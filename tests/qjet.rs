//! `QJet<N>`, the quad-double jet: its coefficients against exact arithmetic (`exact::Dy`) to quad-double accuracy
//! (a polynomial in the series variable, the series of 1/(c + h), the residual of a quotient, a rational function),
//! against the double-double jet to double-double accuracy on the same code, against `Qu` through every `Lane`
//! method, and bit for bit against its own scalar parameter arithmetic `QSeries<N>`, its truncations and the quotient
//! recurrence with `/`. Controls: the convolution's index shifted, a quotient recurrence with the wrong sign, the
//! double-double jet on the quad-double checks, and (feature `mutate`) a quad-double division and accumulator broken.
#![allow(clippy::needless_range_loop)]
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::dual::{Counted, Lane, Param};
use multidouble::dv::DV;
use multidouble::exact::Dy;
use multidouble::jet::{QSeries, Series};
use multidouble::native::{Jet, QJet, Qu, QV};
use multidouble::qd::QD;
use multidouble::qv::QDotAcc;
use multidouble::simd::Native;

type Dv = DV<Native>;

/// quad-double accuracy, about 800 units of 2^-209
const QD_TOL: f64 = 1e-60;

fn dv(v: &[DD; 8]) -> Dv {
    let hi: Vec<f64> = v.iter().map(|d| d.hi).collect();
    let lo: Vec<f64> = v.iter().map(|d| d.lo).collect();
    DV::load(&hi, &lo)
}

/// a quad-double lo + w u, u uniform in [0, 1), with all four parts in use
fn qd_u(r: &mut Rng, lo: f64, w: f64) -> QD {
    let h = lo + w * r.unit();
    qd_of(r, h)
}

/// a quad-double w u, u uniform in [-1, 1), with all four parts in use
fn qd_s(r: &mut Rng, w: f64) -> QD {
    let h = w * r.sym();
    qd_of(r, h)
}

/// h (1 + O(2^-53)) with all four parts in use
fn qd_of(r: &mut Rng, h: f64) -> QD {
    let a = h.abs();
    QD::from_dd(DD::new(h, r.sym() * a * 2f64.powi(-53)))
        .add_dd(DD::new(r.sym() * a * 2f64.powi(-106), r.sym() * a * 2f64.powi(-159)))
}

fn dd_dy(d: DD) -> Dy {
    Dy::sum(&[d.hi, d.lo])
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

fn qbits(q: QV) -> Vec<u64> {
    q.lanes().iter().flat_map(|d| d.x.map(f64::to_bits)).collect()
}

fn jbits<const N: usize>(j: QJet<N>) -> Vec<u64> {
    j.c.iter().flat_map(|&q| qbits(q)).collect()
}

// ---------------------------------------------------------------------------------------------------------------
// against exact arithmetic
// ---------------------------------------------------------------------------------------------------------------

const DEG: usize = 5;

/// worst error of the coefficients of p(c + h) = sum_i a_i (c + h)^i, by Horner with the product `mul` and
/// quad-double c and a_i, against the binomial expansion sum_i a_i C(i, k) c^(i-k) in exact arithmetic, relative to
/// the sum of the terms' magnitudes (past the degree the coefficients must be exactly zero)
fn poly_error<const N: usize>(mul: impl Fn(QJet<N>, QJet<N>) -> QJet<N>) -> f64 {
    let mut r = Rng(81);
    let mut worst = 0.0f64;
    for _ in 0..40 {
        let c: [QD; 8] = std::array::from_fn(|_| qd_u(&mut r, 0.5, 1.0));
        let a: [[QD; 8]; DEG + 1] = std::array::from_fn(|_| std::array::from_fn(|_| qd_s(&mut r, 1.0)));
        let x = QJet::<N>::var_lanes(&c);
        let mut p = QJet::<N>::zero();
        p.set_coef_qd(0, QV::from_lanes(&a[DEG]));
        for i in (0..DEG).rev() {
            let mut ai = QJet::<N>::zero();
            ai.set_coef_qd(0, QV::from_lanes(&a[i]));
            p = mul(p, x) + ai;
        }
        for j in 0..8 {
            let cj = c[j].exact();
            for k in 0..N {
                let (mut want, mut scale) = (Dy::zero(), Dy::zero());
                for i in k..=DEG {
                    let t = a[i][j].exact().mul(&Dy::from_f64(binom(i, k))).mul(&pow(&cj, i - k));
                    want = want.add(&t);
                    scale = scale.add(&t.abs());
                }
                worst = worst.max(err(&p.c[k].lane(j).exact(), &want, &scale));
            }
        }
    }
    worst
}

#[test]
fn polynomial_coefficients_match_exact_arithmetic() {
    let e = poly_error::<8>(|x, y| x * y);
    println!("QJet<8> on a degree-{DEG} polynomial: worst relative error {e:.1e}");
    assert!(e < QD_TOL, "{e:e}");
    let e = poly_error::<3>(|x, y| x * y);
    assert!(e < QD_TOL, "{e:e}");
}

/// Control: a Cauchy product with its index shifted by one is caught.
#[test]
fn control_shifted_convolution_is_caught() {
    fn shifted(x: QJet<8>, y: QJet<8>) -> QJet<8> {
        let mut c = [QV::zero(); 8];
        c[0] = x.c[0] * y.c[0];
        for k in 1..8 {
            for i in 0..k {
                c[k] = c[k] + x.c[i] * y.c[k - i - 1];
            }
        }
        QJet::from_coeffs(c)
    }
    let e = poly_error::<8>(shifted);
    assert!(e > 1e-3, "control: {e:e}");
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

fn recip_qjet_error(rounds: usize) -> f64 {
    let mut r = Rng(82);
    let mut worst = 0.0f64;
    for _ in 0..rounds {
        let c: [QD; 8] = std::array::from_fn(|_| qd_u(&mut r, 0.5, 1.0));
        let q = QJet::<12>::splat(DD::ONE) / QJet::<12>::var_lanes(&c);
        let ce: [Dy; 8] = std::array::from_fn(|j| c[j].exact());
        worst = worst.max(recip_error(&ce, 12, |k, j| q.c[k].lane(j).exact()));
    }
    worst
}

/// 1/(c + h) = sum_k (-1)^k c^(-k-1) h^k to quad-double accuracy; the double-double jet on the same check errs by
/// double-double rounding (the control that the bound tells the two apart)
#[test]
fn quotients_match_the_series_of_the_reciprocal() {
    let e = recip_qjet_error(40);
    println!("QJet<12> 1/(c + h): worst relative error {e:.1e}");
    assert!(e < QD_TOL, "{e:e}");
    let mut r = Rng(83);
    let c: [DD; 8] = std::array::from_fn(|_| DD::new(0.5 + r.unit(), r.sym() * 1e-17));
    let q = Jet::<12>::splat(DD::ONE) / Jet::<12>::var_lanes(&c);
    let ce: [Dy; 8] = std::array::from_fn(|j| dd_dy(c[j]));
    let e = recip_error(&ce, 12, |k, j| dd_dy(q.c[k].lane(j)));
    assert!(
        e > 1e3 * QD_TOL && e < 1e-29,
        "control: the double-double jet's error {e:e}"
    );
}

/// Control: the quotient recurrence with the sign of the sum flipped fails the reciprocal's series.
#[test]
fn control_wrong_quotient_sign_is_caught() {
    let mut r = Rng(84);
    let c: [QD; 8] = std::array::from_fn(|_| qd_u(&mut r, 0.5, 1.0));
    let y = QJet::<6>::var_lanes(&c);
    let mut q = [QV::zero(); 6];
    q[0] = QV::splat(QD::ONE) / y.c[0];
    for k in 1..6 {
        let mut a = QDotAcc::zero();
        for i in 1..=k {
            a = a.add_prod(y.c[i], q[k - i]);
        }
        q[k] = a.finish() / y.c[0]; // the sign of the sum flipped
    }
    let ce: [Dy; 8] = std::array::from_fn(|j| c[j].exact());
    assert!(recip_error(&ce, 6, |k, j| q[k].lane(j).exact()) > 1e-3);
}

/// random jets of quad-doubles with all parts in use, coefficient 0 in [1, 2) for a divisor
fn qjet<const N: usize>(r: &mut Rng, divisor: bool) -> QJet<N> {
    let mut c: [QV; N] = std::array::from_fn(|_| QV::from_lanes(&std::array::from_fn(|_| qd_s(r, 1.0))));
    if divisor {
        c[0] = QV::from_lanes(&std::array::from_fn(|_| qd_u(r, 1.0, 1.0)));
    }
    QJet::from_coeffs(c)
}

/// q = a / b on random jets: the residual a_k - sum_{i=0..k} b_i q_{k-i}, exactly, relative to the magnitudes of
/// its terms
#[test]
fn quotient_residuals_are_quad_double() {
    let mut r = Rng(85);
    let mut worst = 0.0f64;
    for _ in 0..40 {
        let (a, b) = (qjet::<8>(&mut r, false), qjet::<8>(&mut r, true));
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
    println!("QJet<8> quotients: worst relative residual {worst:.1e}");
    assert!(worst < QD_TOL, "{worst:e}");
}

/// f(x, y) = (x^3 + 2 x y) / (x + 3), written over `Lane`
fn f<T: Lane>(x: T, y: T) -> T {
    (x * x * x + (x * y).mulf(2.0)) / x.addc(DV::splat_f(3.0))
}

/// f(c + h, y) on `QJet<6>` against its coefficients in exact arithmetic: f = P - R / (x + 3) with
/// P = x^2 - 3 x + 9 + 2 y and R = 27 + 6 y, so f_k d^(k+1) - P_k d^(k+1) + (-1)^k R = 0 with d = c + 3
#[test]
fn rational_function_matches_exact_arithmetic() {
    let mut r = Rng(86);
    let mut worst = 0.0f64;
    for _ in 0..40 {
        let c: [QD; 8] = std::array::from_fn(|_| qd_u(&mut r, 1.0, 4.0));
        let y: [QD; 8] = std::array::from_fn(|_| qd_s(&mut r, 5.0));
        let mut yj = QJet::<6>::zero();
        yj.set_coef_qd(0, QV::from_lanes(&y));
        let fj = f(QJet::<6>::var_lanes(&c), yj);
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
    println!("QJet<6> on (x^3 + 2 x y) / (x + 3): worst relative error {worst:.1e}");
    assert!(worst < QD_TOL, "{worst:e}");
}

/// Controls with the crate's built-in breakage: the quad-double division without its third remainder, and the
/// accumulator without its third level's per-term errors, are each caught by the exact checks.
#[cfg(feature = "mutate")]
#[test]
fn control_broken_quad_double_arithmetic_is_caught() {
    use multidouble::qd::mutate;
    mutate::set(mutate::DIV_R3);
    let e = recip_qjet_error(4);
    mutate::set(mutate::ACC_L3);
    let p = poly_error::<8>(|x, y| x * y);
    mutate::set(0);
    println!("controls: division without its third remainder {e:.1e}, accumulator without its third level {p:.1e}");
    assert!(e > QD_TOL, "control: division without its third remainder, {e:e}");
    assert!(p > QD_TOL, "control: accumulator without its third level, {p:e}");
}

// ---------------------------------------------------------------------------------------------------------------
// against the double-double jet and Qu
// ---------------------------------------------------------------------------------------------------------------

/// a computation over `Lane` with constants formed from a parameter n, as a continuation in n writes them; with n the
/// series variable, the same code on `Jet<N>` and `QJet<N>`
fn g<T: Lane>(x: T, y: T, n: DD) -> T {
    let n = <T::P as Param>::var(n);
    let n1 = n - T::P::one();
    let w = T::P::one() / (T::P::from_f64(3.0) + n1.mul_f(0.5));
    ((x * x).mulp(n1) - y.mulp(w)).addp(n * n) / (x + y.mulp(n)).addc(DV::splat_f(2.0))
}

/// the double-double and the quad-double jet on the same double-double inputs agree to double-double accuracy:
/// a polynomial in the series variable by Horner with `addc`, the rational function, random products and quotients,
/// and the parameter arithmetic through `g`
#[test]
fn coefficients_agree_with_the_double_double_jet() {
    let mut r = Rng(87);
    let mut worst = 0.0f64;
    let mut cmp = |q: QJet<8>, d: Jet<8>| {
        for k in 0..8 {
            for l in 0..8 {
                let (a, b) = (q.coef(k).lane(l), d.c[k].lane(l));
                worst = worst.max((a - b).to_f64().abs() / b.to_f64().abs().max(1.0));
            }
        }
    };
    for _ in 0..100 {
        let c: [DD; 8] = std::array::from_fn(|_| DD::new(0.5 + r.unit(), r.sym() * 1e-17));
        let a: [Dv; DEG + 1] = std::array::from_fn(|_| dv(&std::array::from_fn(|_| DD::new(r.sym(), r.sym() * 1e-17))));
        let (qx, dx) = (QJet::<8>::var_lanes(&c.map(QD::from_dd)), Jet::<8>::var_lanes(&c));
        let (mut qp, mut dp) = (QJet::<8>::cst(a[DEG]), Jet::<8>::cst(a[DEG]));
        for i in (0..DEG).rev() {
            qp = (qp * qx).addc(a[i]);
            dp = (dp * dx).addc(a[i]);
        }
        cmp(qp, dp);
        let y = dv(&std::array::from_fn(|_| DD::new(5.0 * r.sym(), r.sym() * 1e-17)));
        cmp(f(qx, QJet::cst(y)), f(dx, Jet::cst(y)));
        let u: [[DD; 8]; 8] = std::array::from_fn(|_| std::array::from_fn(|_| DD::new(r.sym(), r.sym() * 1e-17)));
        let mut v: [[DD; 8]; 8] = std::array::from_fn(|_| std::array::from_fn(|_| DD::new(r.sym(), r.sym() * 1e-17)));
        v[0] = std::array::from_fn(|_| DD::new(1.0 + r.unit(), r.sym() * 1e-17));
        let (qu, qv) = (
            QJet::<8>::from_coeffs(std::array::from_fn(|k| QV::from_dv(dv(&u[k])))),
            QJet::<8>::from_coeffs(std::array::from_fn(|k| QV::from_dv(dv(&v[k])))),
        );
        let (du, dv_) = (
            Jet::<8>::from_coeffs(std::array::from_fn(|k| dv(&u[k]))),
            Jet::<8>::from_coeffs(std::array::from_fn(|k| dv(&v[k]))),
        );
        cmp(qu * qv, du * dv_);
        cmp(qu / qv, du / dv_);
        let n = DD::new(4.0 + 8.0 * r.unit(), r.sym() * 1e-16);
        cmp(g(QJet::cst(y), qu, n), g(Jet::cst(y), du, n));
    }
    println!("QJet<8> against Jet<8>: worst difference {worst:.1e}");
    assert!(worst < 1e-29, "{worst:e}");
}

/// h(x, y, c) = ((c x - s y)(x/2) + x y + c x - (y + c)) / (x_0 + 3), written once over `Lane` through every one
/// of its methods (the product sum by the accumulator, x_0 by `bcast`)
fn every<T: Lane>(x: T, y: T, c: DV<T::S>, s: DD) -> T {
    let a = x.mulc(c) - y.muls(s);
    let p = T::fin(T::acc1(T::accc(T::acc(T::acc0(), x, y), x, c), -y.addc(c)));
    T::zero() + (a * x.mulf(0.5) + p) / (x.bcast(0) + T::splat(DD::from_f64(3.0)))
}

/// `QJet<2>` is `Qu` to quad-double rounding through every `Lane` method, and `QJet<5>`'s orders 0 and 1 are
/// `QJet<2>`'s bit for bit
#[test]
fn qjet_two_is_qu_through_every_lane_method() {
    let mut r = Rng(88);
    let s = DD::ONE / DD::from_f64(3.0);
    let (one, zero) = (DV::splat_f(1.0), DV::zero());
    let mut worst = 0.0f64;
    for _ in 0..100 {
        let x = dv(&std::array::from_fn(|_| DD::new(2.0 + r.unit(), r.sym() * 1e-16)));
        let y = dv(&std::array::from_fn(|_| DD::new(1.0 + r.unit(), r.sym() * 1e-16)));
        let c = dv(&std::array::from_fn(|_| DD::new(1.0 + r.unit(), r.sym() * 1e-16)));
        let u = every(Qu::from_vt(x, one), Qu::from_vt(y, zero), c, s);
        let j2 = every(QJet::<2>::from_vt(x, one), QJet::<2>::from_vt(y, zero), c, s);
        let j5 = every(QJet::<5>::from_vt(x, one), QJet::<5>::from_vt(y, zero), c, s);
        for (k, want) in [(0, u.v), (1, u.d)] {
            for l in 0..8 {
                let (a, b) = (j2.coef_qd(k).lane(l).exact(), want.lane(l).exact());
                worst = worst.max(err(&a, &b, &b.abs()));
            }
            assert_eq!(qbits(j5.c[k]), qbits(j2.c[k]), "QJet<5> order {k}");
        }
    }
    println!("QJet<2> against Qu: worst relative difference {worst:.1e}");
    assert!(worst < QD_TOL, "{worst:e}");
}

// ---------------------------------------------------------------------------------------------------------------
// bit for bit: QSeries, truncation, the shared divisor, accessors
// ---------------------------------------------------------------------------------------------------------------

fn qseries(r: &mut Rng) -> QSeries<8> {
    let mut s = QSeries {
        c: std::array::from_fn(|_| qd_s(r, 1.0)),
    };
    s.c[0] = qd_u(r, 1.0, 1.0);
    s
}

fn as_qjet(s: QSeries<8>) -> QJet<8> {
    QJet::from_coeffs(s.c.map(QV::splat))
}

/// `QSeries` arithmetic is the jet's on every lane bit for bit, and `mulp` and `addp` are the product and sum with
/// the series as a jet bit for bit
#[test]
fn qseries_matches_jets_and_mulp_is_the_product_bit_for_bit() {
    let mut r = Rng(89);
    for _ in 0..100 {
        let (a, b) = (qseries(&mut r), qseries(&mut r));
        for (name, s, j) in [
            ("+", a + b, as_qjet(a) + as_qjet(b)),
            ("-", a - b, as_qjet(a) - as_qjet(b)),
            ("neg", -a, -as_qjet(a)),
            ("*", a * b, as_qjet(a) * as_qjet(b)),
            ("/", a / b, as_qjet(a) / as_qjet(b)),
            ("mul_f", a.mul_f(0.375), as_qjet(a).mulf(0.375)),
        ] {
            assert_eq!(jbits(as_qjet(s)), jbits(j), "QSeries {name}");
        }
        let x = qjet::<8>(&mut r, false);
        assert_eq!(jbits(x.mulp(a)), jbits(x * as_qjet(a)), "mulp");
        assert_eq!(jbits(x.addp(a)), jbits(x + as_qjet(a)), "addp");
    }
    let v = QSeries::<3>::var(DD::new(2.5, 1e-17));
    assert_eq!(v.c, [QD::from_dd(DD::new(2.5, 1e-17)), QD::ONE, QD::ZERO]);
    assert_eq!(QSeries::<2>::one().c, [QD::ONE, QD::ZERO]);
    assert_eq!(QSeries::<2>::from_f64(3.0).mul_f(0.5).c, [QD::from_f64(1.5), QD::ZERO]);
    // the double-double series of the same values rounds what the quad-double one keeps
    let (a, b) = (Series::<2>::from_f64(1.0), Series::<2>::from_f64(3.0));
    let (qa, qb) = (QSeries::<2>::from_f64(1.0), QSeries::<2>::from_f64(3.0));
    assert_ne!(
        QD::from_dd((a / b).c[0]),
        (qa / qb).c[0],
        "control: 1/3 the same in both"
    );
}

/// truncation keeps the low orders bit for bit, and the quotient through the shared divisor is the recurrence with
/// `/` bit for bit
#[test]
fn truncation_and_the_shared_divisor_are_bit_for_bit() {
    let mut r = Rng(90);
    for _ in 0..50 {
        let (a, b) = (qjet::<8>(&mut r, false), qjet::<8>(&mut r, true));
        let low = |j: QJet<8>| QJet::<4>::from_coeffs(std::array::from_fn(|k| j.c[k]));
        for (name, p8, p4) in [
            ("*", a * b, low(a) * low(b)),
            ("/", a / b, low(a) / low(b)),
            ("acc", QJet::<8>::fin(QJet::<8>::acc(QJet::<8>::acc0(), a, b)), {
                QJet::<4>::fin(QJet::<4>::acc(QJet::<4>::acc0(), low(a), low(b)))
            }),
        ] {
            for k in 0..4 {
                assert_eq!(qbits(p8.c[k]), qbits(p4.c[k]), "{name} order {k}");
            }
        }
        let mut q = [QV::zero(); 8];
        q[0] = a.c[0] / b.c[0];
        for k in 1..8 {
            let mut s = QDotAcc::zero();
            for i in 1..=k {
                s = s.add_prod(b.c[i], q[k - i]);
            }
            q[k] = (a.c[k] - s.finish()) / b.c[0];
        }
        assert_eq!(
            jbits(a / b),
            jbits(QJet::from_coeffs(q)),
            "the quotient against the recurrence with /"
        );
        assert_eq!(
            jbits(a * b),
            jbits(QJet::<8>::fin(QJet::<8>::acc(QJet::<8>::acc0(), a, b))),
            "acc"
        );
    }
}

/// the flags, `var`, `from_vt`, the coefficient accessors (rounded and quad-double), `mul_pwr2` and `Counted`
#[test]
fn accessors_flags_and_counted() {
    fn flags<T: Lane>() -> (bool, bool, usize) {
        (T::TANGENT, T::VAL_QD, T::NJ)
    }
    assert_eq!(flags::<QJet<5>>(), (true, true, 5));
    assert_eq!(flags::<Counted<QJet<5>>>(), (true, true, 5));
    let c = DD::new(1.25, 3e-17);
    let v = QJet::<5>::var(c);
    assert_eq!(qbits(v.c[0]), qbits(QV::splat(QD::from_dd(c))));
    assert_eq!(qbits(v.c[1]), qbits(QV::splat(QD::ONE)));
    for k in 2..5 {
        assert_eq!(qbits(v.c[k]), qbits(QV::zero()));
    }
    let mut r = Rng(91);
    for _ in 0..50 {
        let mut j = qjet::<4>(&mut r, false);
        let x = j.c[2];
        assert_eq!(qbits(j.coef_qd(2)), qbits(x), "coef_qd");
        assert_eq!(qbits(Counted(j).coef_qd(2)), qbits(x), "Counted coef_qd");
        assert_eq!(
            qbits(QV::from_dv(j.coef(2))),
            qbits(QV::from_dv(x.to_dv())),
            "coef rounds"
        );
        assert_eq!(
            qbits(QV::from_dv(j.tan())),
            qbits(QV::from_dv(j.c[1].to_dv())),
            "tan rounds"
        );
        assert_eq!(
            qbits(QV::from_dv(j.val())),
            qbits(QV::from_dv(j.c[0].to_dv())),
            "val rounds"
        );
        assert_eq!(qbits(j.coef_qd(4)), qbits(QV::zero()), "coef_qd past the truncation");
        assert_eq!(
            qbits(QV::from_dv(j.coef(9))),
            qbits(QV::zero()),
            "coef past the truncation"
        );
        let y = j.c[3];
        j.set_coef_qd(1, y);
        assert_eq!(qbits(j.c[1]), qbits(y), "set_coef_qd");
        let d = y.to_dv();
        j.set_coef(1, d);
        assert_eq!(qbits(j.c[1]), qbits(QV::from_dv(d)), "set_coef");
        let mut cj = Counted(j);
        cj.set_coef_qd(0, y);
        assert_eq!(qbits(cj.0.c[0]), qbits(y), "Counted set_coef_qd");
        let s = QJet::<4>::from_vt(d, x.to_dv());
        assert_eq!(qbits(s.c[1]), qbits(QV::from_dv(x.to_dv())), "from_vt");
        assert_eq!(qbits(s.c[2]), qbits(QV::zero()), "from_vt order 2");
        let p = 2f64.powi((r.next_u64() % 401) as i32 - 200);
        assert_eq!(jbits(j.mul_pwr2(p)), jbits(j.mulf(p)), "mul_pwr2");
        assert_eq!(jbits(j.mul_pwr2(p).mul_pwr2(1.0 / p)), jbits(j), "mul_pwr2 round trip");
        let b = j.bcast(5);
        assert_eq!(qbits(b.c[3]), qbits(QV::splat(j.c[3].lane(5))), "bcast");
    }
}
