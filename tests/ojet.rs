//! `OJet<N>`, the octo-double jet, and `OSeries<N>`, its parameter arithmetic: the coefficients against exact
//! arithmetic (`exact::Dy`) to octo-double accuracy (a polynomial in the series variable, the series of 1/(c + h), the
//! residual of a quotient, a rational function, products of series and a quotient formed in the parameter
//! arithmetic), against the quad-double jet to quad-double accuracy on the same code, bit for bit against the
//! quad-double jet where the arithmetic is exact, against `OV` through every `Lane` method at order 0, and bit for bit
//! against its own scalar parameter arithmetic, its truncations and the quotient recurrence with `/`.
//!
//! Controls: the convolution's index shifted, a quotient recurrence with the wrong sign, the quad-double jet on the
//! octo-double checks, a computation whose quad-double rounding differs, and (feature `mutate`) a convolution term
//! dropped, an octo-double division and accumulator broken.
//!
//! Every check runs on a thread with a 64 MiB stack (`common::big_stack`).
#![allow(clippy::needless_range_loop)]
mod common;
use common::{big_stack, Rng};
use multidouble::dd::DD;
use multidouble::dual::{Counted, Lane, Param};
use multidouble::dv::DV;
use multidouble::exact::Dy;
use multidouble::jet::{OSeries, QSeries};
use multidouble::native::{Jet, OJet, QJet, Qu, OV, QV};
use multidouble::od::{OdAcc, OD};
use multidouble::ov::ODotAcc;
use multidouble::qd::QD;
use multidouble::simd::Native;

type Dv = DV<Native>;

/// octo-double accuracy, about 700 units of 2^-418
const OD_TOL: f64 = 1e-123;
/// quad-double accuracy, about 800 units of 2^-209
const QD_TOL: f64 = 1e-60;

fn dv(v: &[DD; 8]) -> Dv {
    let hi: Vec<f64> = v.iter().map(|d| d.hi).collect();
    let lo: Vec<f64> = v.iter().map(|d| d.lo).collect();
    DV::load(&hi, &lo)
}

/// h (1 + O(2^-53)) with all eight parts in use
fn od_of(r: &mut Rng, h: f64) -> OD {
    let mut x = [0.0; 8];
    x[0] = h;
    for i in 1..8 {
        x[i] = x[i - 1] * 2f64.powi(-53) * r.sym();
    }
    OD::new(x)
}

/// an octo-double lo + w u, u uniform in [0, 1), with all eight parts in use
fn od_u(r: &mut Rng, lo: f64, w: f64) -> OD {
    let h = lo + w * r.unit();
    od_of(r, h)
}

/// an octo-double w u, u uniform in [-1, 1), with all eight parts in use
fn od_s(r: &mut Rng, w: f64) -> OD {
    let h = w * r.sym();
    od_of(r, h)
}

fn pow(x: &Dy, k: usize) -> Dy {
    (0..k).fold(Dy::from_f64(1.0), |p, _| p.mul(x))
}

fn binom(n: usize, k: usize) -> f64 {
    (0..k).fold(1.0, |b, i| b * (n - i) as f64 / (i + 1) as f64)
}

/// |got - want| / scale, exactly up to the f64 of the ratio; an exact zero is required where the scale is zero
fn err(got: &Dy, want: &Dy, scale: &Dy) -> f64 {
    let d = got.sub(want).abs();
    if scale.is_zero() {
        if d.is_zero() {
            0.0
        } else {
            f64::INFINITY
        }
    } else {
        d.ratio(scale)
    }
}

/// the bits of every part of every lane
fn obits(v: OV) -> Vec<u64> {
    v.lanes().iter().flat_map(|d| d.x.map(f64::to_bits)).collect()
}

/// the bits of every coefficient
fn jbits<const N: usize>(j: OJet<N>) -> Vec<u64> {
    j.c.iter().flat_map(|&v| obits(v)).collect()
}

fn qbits(q: QV) -> Vec<u64> {
    q.lanes().iter().flat_map(|d| d.x.map(f64::to_bits)).collect()
}

// ---------------------------------------------------------------------------------------------------------------
// against exact arithmetic
// ---------------------------------------------------------------------------------------------------------------

const DEG: usize = 5;

/// the inputs of `poly_error`: the values c of the series variable c + h and the polynomial's coefficients a_i
fn poly_inputs(r: &mut Rng) -> ([OD; 8], [[OD; 8]; DEG + 1]) {
    let c: [OD; 8] = std::array::from_fn(|_| od_u(r, 0.5, 1.0));
    let a: [[OD; 8]; DEG + 1] = std::array::from_fn(|_| std::array::from_fn(|_| od_s(r, 1.0)));
    (c, a)
}

/// the worst error of coefficients p(k, j) of p(c + h) = sum_i a_i (c + h)^i against the binomial expansion
/// sum_i a_i C(i, k) c^(i-k) in exact arithmetic, relative to the sum of the terms' magnitudes
fn poly_worst(c: &[OD; 8], a: &[[OD; 8]; DEG + 1], n: usize, p: impl Fn(usize, usize) -> Dy) -> f64 {
    let mut worst = 0.0f64;
    for j in 0..8 {
        let cj = c[j].exact();
        for k in 0..n {
            let (mut want, mut scale) = (Dy::zero(), Dy::zero());
            for i in k..=DEG {
                let t = a[i][j].exact().mul(&Dy::from_f64(binom(i, k))).mul(&pow(&cj, i - k));
                want = want.add(&t);
                scale = scale.add(&t.abs());
            }
            worst = worst.max(err(&p(k, j), &want, &scale));
        }
    }
    worst
}

/// worst error of the coefficients of p(c + h), by Horner with the product `mul` on octo-double c and a_i (past the
/// degree the coefficients must be exactly zero)
fn poly_error<const N: usize>(rounds: usize, mul: impl Fn(OJet<N>, OJet<N>) -> OJet<N>) -> f64 {
    let mut r = Rng(81);
    let mut worst = 0.0f64;
    for _ in 0..rounds {
        let (c, a) = poly_inputs(&mut r);
        let x = OJet::<N>::var_lanes(&c);
        let mut p = OJet::<N>::zero();
        p.set_coef_od(0, OV::from_lanes(&a[DEG]));
        for i in (0..DEG).rev() {
            let mut ai = OJet::<N>::zero();
            ai.set_coef_od(0, OV::from_lanes(&a[i]));
            p = mul(p, x) + ai;
        }
        worst = worst.max(poly_worst(&c, &a, N, |k, j| p.c[k].lane(j).exact()));
    }
    worst
}

/// the same polynomial on `QJet<8>` with c and a_i rounded to quad-double, against the exact expansion at the
/// octo-double c and a_i
fn poly_qjet_error(rounds: usize) -> f64 {
    let mut r = Rng(81);
    let mut worst = 0.0f64;
    for _ in 0..rounds {
        let (c, a) = poly_inputs(&mut r);
        let q = |v: &[OD; 8]| QV::from_lanes(&v.map(|x| x.to_qd()));
        let x = QJet::<8>::var_lanes(&c.map(|x| x.to_qd()));
        let mut p = QJet::<8>::zero();
        p.set_coef_qd(0, q(&a[DEG]));
        for i in (0..DEG).rev() {
            let mut ai = QJet::<8>::zero();
            ai.set_coef_qd(0, q(&a[i]));
            p = p * x + ai;
        }
        worst = worst.max(poly_worst(&c, &a, 8, |k, j| p.c[k].lane(j).exact()));
    }
    worst
}

/// p(c + h) on `OJet<8>` and `OJet<3>` within OD_TOL of the exact binomial expansion; the quad-double jet on the same
/// check errs by quad-double rounding (the control that the bound tells the two apart)
#[test]
fn polynomial_coefficients_match_exact_arithmetic() {
    big_stack(|| {
        let e = poly_error::<8>(30, |x, y| x * y);
        println!("OJet<8> on a degree-{DEG} polynomial: worst relative error {e:.1e}");
        assert!(e < OD_TOL, "{e:e}");
        let e = poly_error::<3>(30, |x, y| x * y);
        assert!(e < OD_TOL, "{e:e}");
        let eq = poly_qjet_error(10);
        println!("QJet<8> on the octo-double check: {eq:.1e}");
        assert!(
            eq > 1e3 * OD_TOL && eq < 1e-58,
            "control: the quad-double jet's error {eq:e}"
        );
    })
}

/// Control: a Cauchy product with its index shifted by one is caught.
#[test]
fn control_shifted_convolution_is_caught() {
    big_stack(|| {
        fn shifted(x: OJet<8>, y: OJet<8>) -> OJet<8> {
            let mut c = [OV::zero(); 8];
            c[0] = x.c[0] * y.c[0];
            for k in 1..8 {
                for i in 0..k {
                    c[k] = c[k] + x.c[i] * y.c[k - i - 1];
                }
            }
            OJet::from_coeffs(c)
        }
        let e = poly_error::<8>(4, shifted);
        assert!(e > 1e-3, "control: {e:e}");
    })
}

/// worst relative error of the coefficients q(k, j) of 1/(c + h) against (-1)^k c^(-k-1), exactly:
/// |q_k (-1)^k c^(k+1) - 1|
fn recip_error(c: &[Dy; 8], n: usize, q: impl Fn(usize, usize) -> Dy) -> f64 {
    let one = Dy::from_f64(1.0);
    let mut worst = 0.0f64;
    for j in 0..8 {
        for k in 0..n {
            let s = q(k, j).mul(&pow(&c[j], k + 1));
            let s = if k % 2 == 1 { s.neg() } else { s };
            worst = worst.max(err(&s, &one, &one));
        }
    }
    worst
}

fn recip_ojet_error(rounds: usize) -> f64 {
    let mut r = Rng(82);
    let mut worst = 0.0f64;
    for _ in 0..rounds {
        let c: [OD; 8] = std::array::from_fn(|_| od_u(&mut r, 0.5, 1.0));
        let q = OJet::<12>::splat(DD::ONE) / OJet::<12>::var_lanes(&c);
        let ce: [Dy; 8] = std::array::from_fn(|j| c[j].exact());
        worst = worst.max(recip_error(&ce, 12, |k, j| q.c[k].lane(j).exact()));
    }
    worst
}

/// 1/(c + h) = sum_k (-1)^k c^(-k-1) h^k to octo-double accuracy; the quad-double jet on the same check errs by
/// quad-double rounding (the control that the bound tells the two apart)
#[test]
fn quotients_match_the_series_of_the_reciprocal() {
    big_stack(|| {
        let e = recip_ojet_error(20);
        println!("OJet<12> 1/(c + h): worst relative error {e:.1e}");
        assert!(e < OD_TOL, "{e:e}");
        let mut r = Rng(83);
        let c: [OD; 8] = std::array::from_fn(|_| od_u(&mut r, 0.5, 1.0).to_qd()).map(OD::from_qd);
        let q = QJet::<12>::splat(DD::ONE) / QJet::<12>::var_lanes(&c.map(|x| x.to_qd()));
        let ce: [Dy; 8] = std::array::from_fn(|j| c[j].exact());
        let e = recip_error(&ce, 12, |k, j| q.c[k].lane(j).exact());
        assert!(
            e > 1e3 * OD_TOL && e < QD_TOL,
            "control: the quad-double jet's error {e:e}"
        );
    })
}

/// Control: the quotient recurrence with the sign of the sum flipped fails the reciprocal's series.
#[test]
fn control_wrong_quotient_sign_is_caught() {
    big_stack(|| {
        let mut r = Rng(84);
        let c: [OD; 8] = std::array::from_fn(|_| od_u(&mut r, 0.5, 1.0));
        let y = OJet::<6>::var_lanes(&c);
        let mut q = [OV::zero(); 6];
        q[0] = OV::splat(OD::ONE) / y.c[0];
        for k in 1..6 {
            let mut a = ODotAcc::zero();
            for i in 1..=k {
                a = a.add_prod(y.c[i], q[k - i]);
            }
            q[k] = a.finish() / y.c[0]; // the sign of the sum flipped
        }
        let ce: [Dy; 8] = std::array::from_fn(|j| c[j].exact());
        assert!(recip_error(&ce, 6, |k, j| q[k].lane(j).exact()) > 1e-3);
    })
}

/// random jets of octo-doubles with all parts in use, coefficient 0 in [1, 2) for a divisor
fn ojet<const N: usize>(r: &mut Rng, divisor: bool) -> OJet<N> {
    let mut c: [OV; N] = std::array::from_fn(|_| OV::from_lanes(&std::array::from_fn(|_| od_s(r, 1.0))));
    if divisor {
        c[0] = OV::from_lanes(&std::array::from_fn(|_| od_u(r, 1.0, 1.0)));
    }
    OJet::from_coeffs(c)
}

/// q = a / b on random jets: the residual a_k - sum_{i=0..k} b_i q_{k-i}, exactly, relative to the magnitudes of
/// its terms
#[test]
fn quotient_residuals_are_octo_double() {
    big_stack(|| {
        let mut r = Rng(85);
        let mut worst = 0.0f64;
        for _ in 0..20 {
            let (a, b) = (ojet::<8>(&mut r, false), ojet::<8>(&mut r, true));
            let q = a / b;
            for j in 0..8 {
                for k in 0..8 {
                    let ak = a.c[k].lane(j).exact();
                    let (mut s, mut scale) = (Dy::zero(), ak.abs());
                    for i in 0..=k {
                        let t = b.c[i].lane(j).exact().mul(&q.c[k - i].lane(j).exact());
                        s = s.add(&t);
                        scale = scale.add(&t.abs());
                    }
                    worst = worst.max(err(&s, &ak, &scale));
                }
            }
        }
        println!("OJet<8> quotients: worst relative residual {worst:.1e}");
        assert!(worst < OD_TOL, "{worst:e}");
    })
}

/// f(x, y) = (x^3 + 2 x y) / (x + 3), written over `Lane`
fn f<T: Lane>(x: T, y: T) -> T {
    (x * x * x + (x * y).mulf(2.0)) / x.addc(DV::splat_f(3.0))
}

/// f(c + h, y) on `OJet<6>` against its coefficients in exact arithmetic: f = P - R / (x + 3) with
/// P = x^2 - 3 x + 9 + 2 y and R = 27 + 6 y, so f_k d^(k+1) - P_k d^(k+1) + (-1)^k R = 0 with d = c + 3
#[test]
fn rational_function_matches_exact_arithmetic() {
    big_stack(|| {
        let mut r = Rng(86);
        let mut worst = 0.0f64;
        for _ in 0..20 {
            let c: [OD; 8] = std::array::from_fn(|_| od_u(&mut r, 1.0, 4.0));
            let y: [OD; 8] = std::array::from_fn(|_| od_s(&mut r, 5.0));
            let mut yj = OJet::<6>::zero();
            yj.set_coef_od(0, OV::from_lanes(&y));
            let fj = f(OJet::<6>::var_lanes(&c), yj);
            for j in 0..8 {
                let (cj, yj) = (c[j].exact(), y[j].exact());
                let d = cj.add(&Dy::from_f64(3.0));
                let rr = Dy::from_f64(27.0).add(&Dy::from_f64(6.0).mul(&yj));
                let p = [
                    cj.mul(&cj)
                        .sub(&Dy::from_f64(3.0).mul(&cj))
                        .add(&Dy::from_f64(9.0))
                        .add(&Dy::from_f64(2.0).mul(&yj)),
                    Dy::from_f64(2.0).mul(&cj).sub(&Dy::from_f64(3.0)),
                    Dy::from_f64(1.0),
                ];
                for k in 0..6 {
                    let dk = pow(&d, k + 1);
                    let fk = fj.c[k].lane(j).exact().mul(&dk);
                    let pk = if k < 3 { p[k].mul(&dk) } else { Dy::zero() };
                    let rk = if k % 2 == 1 { rr.neg() } else { rr.clone() };
                    let s = fk.sub(&pk).add(&rk);
                    let scale = fk.abs().add(&pk.abs()).add(&rk.abs());
                    worst = worst.max(err(&s, &Dy::zero(), &scale));
                }
            }
        }
        println!("OJet<6> on (x^3 + 2 x y) / (x + 3): worst relative error {worst:.1e}");
        assert!(worst < OD_TOL, "{worst:e}");
    })
}

/// random scalar series of octo-doubles with all parts in use, coefficient 0 in [1, 2)
fn oseries<const N: usize>(r: &mut Rng) -> OSeries<N> {
    let mut s = OSeries {
        c: std::array::from_fn(|_| od_s(r, 1.0)),
    };
    s.c[0] = od_u(r, 1.0, 1.0);
    s
}

/// `OSeries` against exact truncated power series: a b's coefficient k against sum_{i<=k} a_i b_{k-i} exactly, relative
/// to the sum of the terms' magnitudes; q = a / b by its residual a_k - sum_i b_i q_{k-i}, as for the jets; and
/// w = 1 / (3 + (n - 1) / 2) for n = c + h formed in the parameter arithmetic (`Param::var`, `one`, `from_f64`,
/// `mul_f`), against the series of 1 / (a + h/2), a = (c + 5)/2: w_k (-2)^k a^(k+1) = 1. All within OD_TOL. Control:
/// the double-double series on the last check errs by double-double rounding.
#[test]
fn series_arithmetic_matches_exact_power_series() {
    big_stack(|| {
        let mut r = Rng(87);
        let (mut wp, mut wq, mut wn) = (0.0f64, 0.0f64, 0.0f64);
        for _ in 0..30 {
            let (a, b): (OSeries<10>, OSeries<10>) = (oseries(&mut r), oseries(&mut r));
            let (p, q) = (a * b, a / b);
            for k in 0..10 {
                let (mut s, mut scale) = (Dy::zero(), Dy::zero());
                let (mut t, mut tscale) = (Dy::zero(), a.c[k].exact().abs());
                for i in 0..=k {
                    let x = a.c[i].exact().mul(&b.c[k - i].exact());
                    s = s.add(&x);
                    scale = scale.add(&x.abs());
                    let y = b.c[i].exact().mul(&q.c[k - i].exact());
                    t = t.add(&y);
                    tscale = tscale.add(&y.abs());
                }
                wp = wp.max(err(&p.c[k].exact(), &s, &scale));
                wq = wq.max(err(&t, &a.c[k].exact(), &tscale));
            }
            let c = DD::new(4.0 + 8.0 * r.unit(), r.sym() * 1e-16);
            let n = <OSeries<10> as Param>::var(c);
            let w = OSeries::one() / (OSeries::from_f64(3.0) + (n - OSeries::one()).mul_f(0.5));
            let aa = Dy::sum(&[c.hi, c.lo]).add(&Dy::from_f64(5.0)).mul(&Dy::from_f64(0.5));
            let ce: [Dy; 8] = std::array::from_fn(|_| aa.clone());
            let half = |k: usize| Dy::from_f64(2f64.powi(k as i32));
            wn = wn.max(recip_error(&ce, 10, |k, _| w.c[k].exact().mul(&half(k))));
        }
        println!("OSeries<10>: products {wp:.1e}, quotient residuals {wq:.1e}, 1 / (3 + (n - 1)/2) {wn:.1e}");
        assert!(wp < OD_TOL && wq < OD_TOL && wn < OD_TOL, "{wp:e} {wq:e} {wn:e}");
        let c = DD::new(6.5, 3e-17);
        let n = <multidouble::jet::Series<10> as Param>::var(c);
        let one = multidouble::jet::Series::<10>::one();
        let w = one / (multidouble::jet::Series::from_f64(3.0) + (n - one).mul_f(0.5));
        let aa = Dy::sum(&[c.hi, c.lo]).add(&Dy::from_f64(5.0)).mul(&Dy::from_f64(0.5));
        let e = recip_error(&std::array::from_fn(|_| aa.clone()), 10, |k, _| {
            Dy::sum(&[w.c[k].hi, w.c[k].lo]).mul(&Dy::from_f64(2f64.powi(k as i32)))
        });
        assert!(e > 1e60 * OD_TOL, "control: the double-double series' error {e:e}");
    })
}

/// Controls with the crate's built-in breakage: the octo-double jet's product without its last convolution term
/// (`dual::mutate::OJET_CONV`), the octo-double division without its sixth remainder update and the accumulator
/// without its third level's errors (`od::mutate`) are each caught by the exact checks.
#[cfg(feature = "mutate")]
#[test]
fn control_broken_octo_double_arithmetic_is_caught() {
    big_stack(|| {
        use multidouble::{dual, od};
        dual::mutate::set(dual::mutate::OJET_CONV);
        let c = poly_error::<8>(2, |x, y| x * y);
        dual::mutate::set(0);
        od::mutate::set(od::mutate::DIV_REM);
        let e = recip_ojet_error(2);
        od::mutate::set(od::mutate::ACC_L3);
        let p = poly_error::<8>(2, |x, y| x * y);
        od::mutate::set(0);
        println!(
            "controls: convolution term dropped {c:.1e}, division without a remainder update {e:.1e}, accumulator \
             without its third level {p:.1e}"
        );
        assert!(c > 1e-3, "control: the convolution without its last term, {c:e}");
        assert!(
            e > OD_TOL,
            "control: division without its sixth remainder update, {e:e}"
        );
        assert!(p > OD_TOL, "control: accumulator without its third level, {p:e}");
    })
}

// ---------------------------------------------------------------------------------------------------------------
// against the quad-double jet and OV
// ---------------------------------------------------------------------------------------------------------------

/// a computation over `Lane` with constants formed from a parameter n, as a continuation in n writes them; with n the
/// series variable, the same code on `QJet<N>` and `OJet<N>`
fn g<T: Lane>(x: T, y: T, n: DD) -> T {
    let n = <T::P as Param>::var(n);
    let n1 = n - T::P::one();
    let w = T::P::one() / (T::P::from_f64(3.0) + n1.mul_f(0.5));
    ((x * x).mulp(n1) - y.mulp(w)).addp(n * n) / (x + y.mulp(n)).addc(DV::splat_f(2.0))
}

/// the quad-double and the octo-double jet on the same double-double inputs agree to quad-double accuracy, within
/// 1e-59 of max(1, |coefficient|): a polynomial in the series variable by Horner with `addc`, the rational function,
/// random products and quotients, and the parameter arithmetic through `g`
#[test]
fn coefficients_agree_with_the_quad_double_jet() {
    big_stack(|| {
        let mut r = Rng(88);
        let mut worst = 0.0f64;
        let mut cmp = |o: OJet<8>, q: QJet<8>| {
            for k in 0..8 {
                for l in 0..8 {
                    let (a, b) = (o.c[k].lane(l), OD::from_qd(q.c[k].lane(l)));
                    worst = worst.max((a - b).to_f64().abs() / b.to_f64().abs().max(1.0));
                }
            }
        };
        let rdd = |r: &mut Rng, lo: f64, w: f64| DD::new(lo + w * r.sym(), r.sym() * 1e-17);
        for _ in 0..20 {
            let c: [DD; 8] = std::array::from_fn(|_| DD::new(0.5 + r.unit(), r.sym() * 1e-17));
            let a: [Dv; DEG + 1] = std::array::from_fn(|_| dv(&std::array::from_fn(|_| rdd(&mut r, 0.0, 1.0))));
            let (ox, qx) = (
                OJet::<8>::var_lanes(&c.map(OD::from_dd)),
                QJet::<8>::var_lanes(&c.map(QD::from_dd)),
            );
            let (mut op, mut qp) = (OJet::<8>::cst(a[DEG]), QJet::<8>::cst(a[DEG]));
            for i in (0..DEG).rev() {
                op = (op * ox).addc(a[i]);
                qp = (qp * qx).addc(a[i]);
            }
            cmp(op, qp);
            let y = dv(&std::array::from_fn(|_| rdd(&mut r, 0.0, 5.0)));
            cmp(f(ox, OJet::cst(y)), f(qx, QJet::cst(y)));
            let u: [Dv; 8] = std::array::from_fn(|_| dv(&std::array::from_fn(|_| rdd(&mut r, 0.0, 1.0))));
            let mut v: [Dv; 8] = std::array::from_fn(|_| dv(&std::array::from_fn(|_| rdd(&mut r, 0.0, 1.0))));
            v[0] = dv(&std::array::from_fn(|_| rdd(&mut r, 1.5, 0.5)));
            let (ou, ov) = (
                OJet::<8>::from_coeffs(u.map(OV::from_dv)),
                OJet::<8>::from_coeffs(v.map(OV::from_dv)),
            );
            let (qu, qv) = (
                QJet::<8>::from_coeffs(u.map(QV::from_dv)),
                QJet::<8>::from_coeffs(v.map(QV::from_dv)),
            );
            cmp(ou * ov, qu * qv);
            cmp(ou / ov, qu / qv);
            let n = DD::new(4.0 + 8.0 * r.unit(), r.sym() * 1e-16);
            cmp(g(OJet::cst(y), ou, n), g(QJet::cst(y), qu, n));
        }
        println!("OJet<8> against QJet<8>: worst difference {worst:.1e}");
        assert!(worst < 1e-59, "{worst:e}");
    })
}

/// a jet of n coefficients, each lane a small dyadic (an integer in [-8, 8] over 4) plus, where `two`, another times
/// 2^-60, so that sums and products of a few stay exact in quad-double
fn dyadic_coefs(r: &mut Rng, n: usize, two: bool) -> Vec<[QD; 8]> {
    let small = |r: &mut Rng| ((r.next_u64() % 17) as f64 - 8.0) / 4.0;
    (0..n)
        .map(|_| {
            std::array::from_fn(|_| {
                let a = small(r);
                let b = if two { small(r) * 2f64.powi(-60) } else { 0.0 };
                QD::new(a, b, 0.0, 0.0)
            })
        })
        .collect()
}

/// The same computation on `OJet<4>` and `QJet<4>` from inputs exactly representable in quad-double (small dyadics,
/// one and two parts) where every operation is exact in both: the octo-double coefficients rounded to quad-double
/// (`coef_qd`) are the quad-double jet's bit for bit, through the product, the sums, `mulp` and `addp` with series of
/// such values, `mulf`, `mul_pwr2`, `mulc`, `addc`, `bcast`, the accumulator and a quotient by a power of two.
/// Control: x y - z with z the quad-double jet's x y, zero there and the product's rounding error here, differs.
#[test]
fn exact_computations_match_the_quad_double_jet_bit_for_bit() {
    big_stack(|| {
        let mut r = Rng(89);
        for round in 0..40 {
            let two = round % 2 == 1;
            let jets = |r: &mut Rng| -> (OJet<4>, QJet<4>) {
                let c = dyadic_coefs(r, 4, two);
                (
                    OJet::from_coeffs(std::array::from_fn(|k| OV::from_qv(QV::from_lanes(&c[k])))),
                    QJet::from_coeffs(std::array::from_fn(|k| QV::from_lanes(&c[k]))),
                )
            };
            let ((ox, qx), (oy, qy), (oz, qz)) = (jets(&mut r), jets(&mut r), jets(&mut r));
            let ps = dyadic_coefs(&mut r, 4, two);
            let (op, qp) = (
                OSeries::<4> {
                    c: std::array::from_fn(|k| OD::from_qd(ps[k][0])),
                },
                QSeries::<4> {
                    c: std::array::from_fn(|k| ps[k][0]),
                },
            );
            let cd = dv(&std::array::from_fn(|j| DD::from_f64(((j as f64) - 3.5) / 2.0)));
            let two_c = OJet::<4>::splat(DD::from_f64(2.0));
            let (o, q) = (
                ((ox * oy - oz).mulp(op).addp(op) + ox.mulf(3.0).mul_pwr2(0.25))
                    .mulc(cd)
                    .addc(cd)
                    / two_c,
                ((qx * qy - qz).mulp(qp).addp(qp) + qx.mulf(3.0).mul_pwr2(0.25))
                    .mulc(cd)
                    .addc(cd)
                    / QJet::<4>::splat(DD::from_f64(2.0)),
            );
            let oa = OJet::<4>::fin(OJet::<4>::acc1(
                OJet::<4>::accc(OJet::<4>::acc(OJet::<4>::acc0(), ox, oy), oz, cd),
                -ox,
            ));
            let qa = QJet::<4>::fin(QJet::<4>::acc1(
                QJet::<4>::accc(QJet::<4>::acc(QJet::<4>::acc0(), qx, qy), qz, cd),
                -qx,
            ));
            for k in 0..4 {
                assert_eq!(qbits(o.coef_qd(k)), qbits(q.c[k]), "round {round}: order {k}");
                assert_eq!(
                    qbits(oa.coef_qd(k)),
                    qbits(qa.c[k]),
                    "round {round}: accumulator order {k}"
                );
                assert_eq!(
                    qbits(o.bcast(3).coef_qd(k)),
                    qbits(q.bcast(3).c[k]),
                    "round {round}: bcast order {k}"
                );
            }
        }
        // the control: products of quad-doubles with all parts in use, less their quad-double product
        let mut r = Rng(90);
        let full = |r: &mut Rng| {
            QV::from_lanes(&std::array::from_fn(|_| {
                QD::new(1.0 + r.unit(), r.sym() * 1e-17, r.sym() * 1e-34, r.sym() * 1e-51)
            }))
        };
        let (x, y) = (QJet::<4>::from_coeffs(std::array::from_fn(|_| full(&mut r))), {
            QJet::<4>::from_coeffs(std::array::from_fn(|_| full(&mut r)))
        });
        let z = x * y;
        let to_o = |q: QJet<4>| OJet::<4>::from_coeffs(q.c.map(OV::from_qv));
        let (o, q) = (to_o(x) * to_o(y) - to_o(z), x * y - z);
        assert!(
            (0..4).any(|k| qbits(o.coef_qd(k)) != qbits(q.c[k])),
            "control: the rounding of the quad-double product not seen"
        );
    })
}

/// h(x, y, c) = ((c x - s y)(x/2) + x y + c x - (y + c)) / (x_0 + 3), written once over `Lane` through every one
/// of its methods (the product sum by the accumulator, x_0 by `bcast`)
fn every<T: Lane>(x: T, y: T, c: DV<T::S>, s: DD) -> T {
    let a = x.mulc(c) - y.muls(s);
    let p = T::fin(T::acc1(T::accc(T::acc(T::acc0(), x, y), x, c), -y.addc(c)));
    T::zero() + (a * x.mulf(0.5) + p) / (x.bcast(0) + T::splat(DD::from_f64(3.0)))
}

/// `OJet` truncated to its first coefficient is `OV` arithmetic: bit for bit for the operations that are the same
/// (sums, `mulc`, `mulf`, `mul_pwr2`, `addc`, `bcast`, the quotient through the shared divisor, the accumulator,
/// `val`, `coef`, `coef_qd`), its products, which go through the accumulator where `OV`'s `*` renormalizes once,
/// within 2^-416 of `OV`'s, and `every` within OD_TOL; `OJet<5>`'s order 0 is `OJet<1>`'s bit for bit.
#[test]
fn ojet_order_zero_is_ov() {
    big_stack(|| {
        let mut r = Rng(91);
        let s = DD::ONE / DD::from_f64(3.0);
        let (mut worst_mul, mut worst_every) = (0.0f64, 0.0f64);
        for _ in 0..50 {
            let xs: [OD; 8] = std::array::from_fn(|_| od_s(&mut r, 2.0));
            let ys: [OD; 8] = std::array::from_fn(|_| od_u(&mut r, 1.0, 1.0));
            let c = dv(&std::array::from_fn(|_| DD::new(1.0 + r.unit(), r.sym() * 1e-16)));
            let (x, y) = (OV::from_lanes(&xs), OV::from_lanes(&ys));
            let (jx, jy) = (OJet::<1>::from_coeffs([x]), OJet::<1>::from_coeffs([y]));
            for (name, j, v) in [
                ("+", jx + jy, x + y),
                ("-", jx - jy, x - y),
                ("neg", -jx, -x),
                ("/", jx / jy, x / y),
                ("mulc", jx.mulc(c), x.mulc(c)),
                ("mulf", jx.mulf(0.375), x.mulf(0.375)),
                ("mul_pwr2", jx.mul_pwr2(0.25), Lane::mul_pwr2(x, 0.25)),
                ("addc", jx.addc(c), x.addc(c)),
                ("bcast", jx.bcast(6), Lane::bcast(x, 6)),
                ("cst", OJet::<1>::cst(c), <OV as Lane>::cst(c)),
                (
                    "acc",
                    OJet::<1>::fin(OJet::<1>::acc1(
                        OJet::<1>::accc(OJet::<1>::acc(OJet::<1>::acc0(), jx, jy), jy, c),
                        jx,
                    )),
                    { OV::fin(OV::acc1(OV::accc(OV::acc(OV::acc0(), x, y), y, c), x)) },
                ),
            ] {
                assert_eq!(obits(j.c[0]), obits(v), "{name}");
            }
            for l in 0..8 {
                assert_eq!(jx.val().lane(l), x.val().lane(l), "val");
                assert_eq!(jx.coef(0).lane(l), x.coef(0).lane(l), "coef");
                assert_eq!(jx.coef_qd(0).lane(l).x, x.coef_qd(0).lane(l).x, "coef_qd");
            }
            let rel = |a: OV, b: OV| -> f64 {
                (0..8)
                    .map(|l| (a.lane(l) - b.lane(l)).to_f64().abs() / b.lane(l).to_f64().abs())
                    .fold(0.0, f64::max)
            };
            let p = OSeries::<1>::from_dd(s);
            worst_mul = worst_mul
                .max(rel((jx * jy).c[0], x * y))
                .max(rel(jx.mulp(p).c[0], x.mulp(s)));
            let (e1, ev) = (every(jx, jy, c, s), every(x, y, c, s));
            worst_every = worst_every.max(rel(e1.c[0], ev));
            let e5 = every(
                OJet::<5>::from_vt(x.val(), DV::splat_f(1.0)),
                OJet::<5>::from_vt(y.val(), DV::zero()),
                c,
                s,
            );
            let e1d = every(
                OJet::<1>::from_vt(x.val(), DV::splat_f(1.0)),
                OJet::<1>::from_vt(y.val(), DV::zero()),
                c,
                s,
            );
            assert_eq!(obits(e5.c[0]), obits(e1d.c[0]), "OJet<5> order 0");
        }
        println!("OJet<1> against OV: products {worst_mul:.1e}, every Lane method {worst_every:.1e}");
        assert!(worst_mul < 2f64.powi(-416), "{worst_mul:e}");
        assert!(worst_every < OD_TOL, "{worst_every:e}");
    })
}

// ---------------------------------------------------------------------------------------------------------------
// bit for bit: OSeries, truncation, the shared divisor, accessors
// ---------------------------------------------------------------------------------------------------------------

fn as_ojet(s: OSeries<8>) -> OJet<8> {
    OJet::from_coeffs(s.c.map(OV::splat))
}

/// `OSeries` arithmetic is the jet's on every lane bit for bit, and `mulp` and `addp` are the product and sum with
/// the series as a jet bit for bit
#[test]
fn oseries_matches_jets_and_mulp_is_the_product_bit_for_bit() {
    big_stack(|| {
        let mut r = Rng(92);
        for _ in 0..30 {
            let (a, b) = (oseries::<8>(&mut r), oseries::<8>(&mut r));
            for (name, s, j) in [
                ("+", a + b, as_ojet(a) + as_ojet(b)),
                ("-", a - b, as_ojet(a) - as_ojet(b)),
                ("neg", -a, -as_ojet(a)),
                ("*", a * b, as_ojet(a) * as_ojet(b)),
                ("/", a / b, as_ojet(a) / as_ojet(b)),
                ("mul_f", a.mul_f(0.375), as_ojet(a).mulf(0.375)),
            ] {
                assert_eq!(jbits(as_ojet(s)), jbits(j), "OSeries {name}");
            }
            let x = ojet::<8>(&mut r, false);
            assert_eq!(jbits(x.mulp(a)), jbits(x * as_ojet(a)), "mulp");
            assert_eq!(jbits(x.addp(a)), jbits(x + as_ojet(a)), "addp");
        }
        let v = OSeries::<3>::var(DD::new(2.5, 1e-17));
        assert_eq!(v.c, [OD::from_dd(DD::new(2.5, 1e-17)), OD::ONE, OD::ZERO]);
        assert_eq!(OSeries::<2>::one().c, [OD::ONE, OD::ZERO]);
        assert_eq!(OSeries::<2>::from_f64(3.0).mul_f(0.5).c, [OD::from_f64(1.5), OD::ZERO]);
        // the quad-double series of the same values rounds what the octo-double one keeps
        let (a, b) = (QSeries::<2>::from_f64(1.0), QSeries::<2>::from_f64(3.0));
        let (oa, ob) = (OSeries::<2>::from_f64(1.0), OSeries::<2>::from_f64(3.0));
        assert_ne!(
            OD::from_qd((a / b).c[0]),
            (oa / ob).c[0],
            "control: 1/3 the same in both"
        );
    })
}

/// truncation keeps the low orders bit for bit, the quotient through the shared divisor is the recurrence with `/`
/// bit for bit, and the accumulator's product is `*`'s
#[test]
fn truncation_and_the_shared_divisor_are_bit_for_bit() {
    big_stack(|| {
        let mut r = Rng(93);
        for _ in 0..20 {
            let (a, b) = (ojet::<8>(&mut r, false), ojet::<8>(&mut r, true));
            let low = |j: OJet<8>| OJet::<4>::from_coeffs(std::array::from_fn(|k| j.c[k]));
            for (name, p8, p4) in [
                ("*", a * b, low(a) * low(b)),
                ("/", a / b, low(a) / low(b)),
                ("acc", OJet::<8>::fin(OJet::<8>::acc(OJet::<8>::acc0(), a, b)), {
                    OJet::<4>::fin(OJet::<4>::acc(OJet::<4>::acc0(), low(a), low(b)))
                }),
            ] {
                for k in 0..4 {
                    assert_eq!(obits(p8.c[k]), obits(p4.c[k]), "{name} order {k}");
                }
            }
            let mut q = [OV::zero(); 8];
            q[0] = a.c[0] / b.c[0];
            for k in 1..8 {
                let mut s = ODotAcc::zero();
                for i in 1..=k {
                    s = s.add_prod(b.c[i], q[k - i]);
                }
                q[k] = (a.c[k] - s.finish()) / b.c[0];
            }
            assert_eq!(
                jbits(a / b),
                jbits(OJet::from_coeffs(q)),
                "the quotient against the recurrence with /"
            );
            assert_eq!(
                jbits(a * b),
                jbits(OJet::<8>::fin(OJet::<8>::acc(OJet::<8>::acc0(), a, b))),
                "acc"
            );
        }
    })
}

/// the flags, `var`, `from_vt`, the coefficient accessors (rounded to double-double and quad-double, and in
/// octo-double), `mul_pwr2`, `bcast` and `Counted`; and `coef_od` and `set_coef_od` on the other lane types: exact on
/// `DV`, `QV`, `OV` and `Qu`, rounded once to quad-double on `QJet` and to double-double on `Jet`
#[test]
fn accessors_flags_and_counted() {
    big_stack(|| {
        fn flags<T: Lane>() -> (bool, bool, bool, usize) {
            (T::TANGENT, T::VAL_QD, T::VAL_OD, T::NJ)
        }
        assert_eq!(flags::<OJet<5>>(), (true, false, true, 5));
        assert_eq!(flags::<Counted<OJet<5>>>(), (true, false, true, 5));
        let c = DD::new(1.25, 3e-17);
        let v = OJet::<5>::var(c);
        assert_eq!(obits(v.c[0]), obits(OV::splat(OD::from_dd(c))));
        assert_eq!(obits(v.c[1]), obits(OV::splat(OD::ONE)));
        for k in 2..5 {
            assert_eq!(obits(v.c[k]), obits(OV::zero()));
        }
        let mut r = Rng(94);
        for _ in 0..30 {
            let mut j = ojet::<4>(&mut r, false);
            let x = j.c[2];
            assert_eq!(obits(j.coef_od(2)), obits(x), "coef_od");
            assert_eq!(obits(Counted(j).coef_od(2)), obits(x), "Counted coef_od");
            assert_eq!(qbits(j.coef_qd(2)), qbits(x.to_qv()), "coef_qd rounds");
            assert_eq!(
                obits(OV::from_dv(j.coef(2))),
                obits(OV::from_dv(x.to_dv())),
                "coef rounds"
            );
            assert_eq!(
                obits(OV::from_dv(j.tan())),
                obits(OV::from_dv(j.c[1].to_dv())),
                "tan rounds"
            );
            assert_eq!(
                obits(OV::from_dv(j.val())),
                obits(OV::from_dv(j.c[0].to_dv())),
                "val rounds"
            );
            assert_eq!(obits(j.coef_od(4)), obits(OV::zero()), "coef_od past the truncation");
            assert_eq!(qbits(j.coef_qd(9)), qbits(QV::zero()), "coef_qd past the truncation");
            let y = j.c[3];
            j.set_coef_od(1, y);
            assert_eq!(obits(j.c[1]), obits(y), "set_coef_od");
            let q = y.to_qv();
            j.set_coef_qd(1, q);
            assert_eq!(obits(j.c[1]), obits(OV::from_qv(q)), "set_coef_qd");
            let d = y.to_dv();
            j.set_coef(1, d);
            assert_eq!(obits(j.c[1]), obits(OV::from_dv(d)), "set_coef");
            let mut cj = Counted(j);
            cj.set_coef_od(0, y);
            assert_eq!(obits(cj.0.c[0]), obits(y), "Counted set_coef_od");
            let s = OJet::<4>::from_vt(d, x.to_dv());
            assert_eq!(obits(s.c[1]), obits(OV::from_dv(x.to_dv())), "from_vt");
            assert_eq!(obits(s.c[2]), obits(OV::zero()), "from_vt order 2");
            let p = 2f64.powi((r.next_u64() % 401) as i32 - 200);
            assert_eq!(jbits(j.mul_pwr2(p)), jbits(j.mulf(p)), "mul_pwr2");
            assert_eq!(jbits(j.mul_pwr2(p).mul_pwr2(1.0 / p)), jbits(j), "mul_pwr2 round trip");
            let b = j.bcast(5);
            assert_eq!(obits(b.c[3]), obits(OV::splat(j.c[3].lane(5))), "bcast");

            // the other lane types
            let qv = QV::from_lanes(&std::array::from_fn(|_| {
                QD::new(r.sym(), r.sym() * 1e-17, r.sym() * 1e-34, 0.0)
            }));
            let dd = qv.to_dv();
            assert_eq!(obits(Lane::coef_od(dd, 0)), obits(OV::from_dv(dd)), "DV coef_od");
            assert_eq!(obits(Lane::coef_od(qv, 0)), obits(OV::from_qv(qv)), "QV coef_od");
            assert_eq!(obits(Lane::coef_od(qv, 1)), obits(OV::zero()), "QV coef_od(1)");
            assert_eq!(obits(Lane::coef_od(y, 0)), obits(y), "OV coef_od");
            assert_eq!(obits(Lane::coef_od(y, 1)), obits(OV::zero()), "OV coef_od(1)");
            let u = Qu { v: qv, d: -qv };
            assert_eq!(obits(u.coef_od(1)), obits(OV::from_qv(-qv)), "Qu coef_od");
            let mut qj = QJet::<3>::zero();
            qj.set_coef_od(2, y);
            assert_eq!(qbits(qj.c[2]), qbits(y.to_qv()), "QJet set_coef_od");
            assert_eq!(obits(qj.coef_od(2)), obits(OV::from_qv(y.to_qv())), "QJet coef_od");
            let mut dj = Jet::<3>::zero();
            dj.set_coef_od(2, y);
            let (a, b) = (dj.c[2], y.to_dv());
            assert!(
                (0..8).all(|l| a.lane(l) == b.lane(l)),
                "Jet set_coef_od: rounded once to double-double"
            );
        }
    })
}

/// FNV-1a
fn fold_bits(h: u64, w: &[u64]) -> u64 {
    w.iter().fold(h, |h, &w| (h ^ w).wrapping_mul(0x0000_0100_0000_01b3))
}

/// The jets' outputs pinned bit for bit on fixed inputs, against hashes recorded with the first implementation:
/// the product, the quotient, `mulp` and `addp` with a series, the accumulator, and `OSeries`' product and quotient.
/// Every backend gives these bits (tests/lanes.rs checks the lanes against `OSeries`).
#[test]
fn ojet_outputs_are_pinned() {
    big_stack(|| {
        let mut r = Rng(97);
        let fnv = 0xcbf2_9ce4_8422_2325u64;
        let mut h = [fnv; 4];
        for _ in 0..10 {
            let (a, b) = (ojet::<6>(&mut r, false), ojet::<6>(&mut r, true));
            let p: OSeries<6> = oseries(&mut r);
            h[0] = fold_bits(h[0], &[jbits(a * b), jbits(a / b)].concat());
            h[1] = fold_bits(h[1], &[jbits(a.mulp(p)), jbits(a.addp(p))].concat());
            let acc = OJet::<6>::fin(OJet::<6>::acc1(OJet::<6>::acc(OJet::<6>::acc0(), a, b), b));
            h[2] = fold_bits(h[2], &jbits(acc));
            let q: OSeries<6> = oseries(&mut r);
            let s = [p * q, p / q];
            h[3] = fold_bits(
                h[3],
                &s.iter()
                    .flat_map(|s| s.c.iter().flat_map(|x| x.x.map(f64::to_bits)))
                    .collect::<Vec<_>>(),
            );
        }
        let want: [u64; 4] = [
            0x8af3_0c4b_8626_2f4d,
            0x6d88_f266_8996_7c14,
            0x4a2e_8ba0_8c25_f2f1,
            0x610c_8464_ad7e_14e6,
        ];
        let names = ["product and quotient", "mulp and addp", "accumulator", "OSeries"];
        let bad: Vec<String> = (0..4)
            .filter(|&i| h[i] != want[i])
            .map(|i| format!("{}: {:#018x} pinned {:#018x}", names[i], h[i], want[i]))
            .collect();
        assert!(bad.is_empty(), "{bad:?}");
        let _ = OdAcc::zero();
    })
}
