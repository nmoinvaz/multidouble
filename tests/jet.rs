//! `Jet<N>`: a polynomial in the series variable against its binomial expansion in scalar double-double, quotients
//! against 1/(c + h)'s coefficients and against the product that undoes them, truncation bit for bit, `var` on every
//! lane type, `Jet<2>` against `Du`, and controls: the convolution's index shifted, and a quotient recurrence with the
//! wrong sign.
#![allow(clippy::needless_range_loop)]
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::dual::Lane;
use multidouble::dv::DV;
use multidouble::native::{Dc, Dtn, Du, Fu, Fun, Jet, Qu, F8, QV};
use multidouble::simd::Native;

type Dv = DV<Native>;

fn dv(v: &[DD; 8]) -> Dv {
    let hi: Vec<f64> = v.iter().map(|d| d.hi).collect();
    let lo: Vec<f64> = v.iter().map(|d| d.lo).collect();
    DV::load(&hi, &lo)
}

/// |a - b| / scale
fn err(a: DD, b: DD, scale: f64) -> f64 {
    (a - b).to_f64().abs() / scale
}

fn binom(n: usize, k: usize) -> f64 {
    (0..k).fold(1.0, |b, i| b * (n - i) as f64 / (i + 1) as f64)
}

const DEG: usize = 5;

/// p(x) = sum_i a_i x^i by Horner, with the product supplied (the jet's own, or a wrong one in the control)
fn horner<const N: usize>(a: &[Dv; DEG + 1], x: Jet<N>, mul: impl Fn(Jet<N>, Jet<N>) -> Jet<N>) -> Jet<N> {
    let mut p = Jet::<N>::cst(a[DEG]);
    for i in (0..DEG).rev() {
        p = mul(p, x).addc(a[i]);
    }
    p
}

/// worst error of the coefficients of p(c + h) from `mul` against the binomial expansion, coefficient k of order k
/// being sum_i a_i C(i, k) c^(i-k) in scalar double-double, relative to the sum of the terms' magnitudes
fn poly_error<const N: usize>(mul: impl Fn(Jet<N>, Jet<N>) -> Jet<N>) -> f64 {
    let mut r = Rng(61);
    let mut worst = 0.0f64;
    for _ in 0..200 {
        let c: [DD; 8] = std::array::from_fn(|_| DD::new(0.5 + r.unit(), r.sym() * 1e-17));
        let a: [[DD; 8]; DEG + 1] = std::array::from_fn(|_| std::array::from_fn(|_| DD::new(r.sym(), r.sym() * 1e-17)));
        let ad: [Dv; DEG + 1] = std::array::from_fn(|i| dv(&a[i]));
        let p = horner(&ad, Jet::<N>::var_lanes(&c), &mul);
        for j in 0..8 {
            for k in 0..N {
                let mut want = DD::ZERO;
                let mut scale = 0.0f64;
                for i in k..=DEG {
                    let t = a[i][j] * DD::from_f64(binom(i, k)) * pow(c[j], i - k);
                    want = want + t;
                    scale += t.to_f64().abs();
                }
                worst = worst.max(err(p.c[k].lane(j), want, scale.max(1e-3)));
            }
        }
    }
    worst
}

fn pow(c: DD, k: usize) -> DD {
    (0..k).fold(DD::ONE, |p, _| p * c)
}

#[test]
fn polynomial_coefficients_match_the_binomial_expansion() {
    let e = poly_error::<8>(|x, y| x * y);
    println!("Jet<8> on a degree-{DEG} polynomial: worst relative error {e:.1e}");
    assert!(e < 1e-30, "{e:e}");
    // truncation below the degree: the low orders unchanged
    let e = poly_error::<3>(|x, y| x * y);
    assert!(e < 1e-30, "{e:e}");
}

/// Control: a Cauchy product with its index shifted by one (coefficient k from orders i and k - i - 1) is caught.
#[test]
fn control_shifted_convolution_is_caught() {
    fn shifted(x: Jet<8>, y: Jet<8>) -> Jet<8> {
        let mut c = [DV::zero(); 8];
        c[0] = x.c[0] * y.c[0];
        for k in 1..8 {
            for i in 0..k {
                c[k] = c[k] + x.c[i] * y.c[k - i - 1];
            }
        }
        Jet::from_coeffs(c)
    }
    let e = poly_error::<8>(shifted);
    assert!(e > 1e-3, "control: {e:e}");
}

/// 1/(c + h) = sum_k (-1)^k c^(-k-1) h^k, and (x / y) y = x on random jets
#[test]
fn quotients_match_the_series_of_the_reciprocal() {
    let mut r = Rng(62);
    let mut worst = 0.0f64;
    for _ in 0..200 {
        let c: [DD; 8] = std::array::from_fn(|_| DD::new(0.5 + r.unit(), r.sym() * 1e-17));
        let x = Jet::<12>::var_lanes(&c);
        let q = Jet::<12>::splat(DD::ONE) / x;
        for j in 0..8 {
            let mut want = DD::ONE / c[j];
            for k in 0..12 {
                worst = worst.max(err(q.c[k].lane(j), want, want.to_f64().abs()));
                want = -want / c[j];
            }
        }
        let a: [[DD; 8]; 12] = std::array::from_fn(|_| std::array::from_fn(|_| DD::new(r.sym(), r.sym() * 1e-17)));
        let mut b: [[DD; 8]; 12] = std::array::from_fn(|_| std::array::from_fn(|_| DD::new(r.sym(), r.sym() * 1e-17)));
        b[0] = std::array::from_fn(|_| DD::new(1.0 + r.unit(), r.sym() * 1e-17));
        let (ja, jb) = (
            Jet::<12>::from_coeffs(std::array::from_fn(|k| dv(&a[k]))),
            Jet::<12>::from_coeffs(std::array::from_fn(|k| dv(&b[k]))),
        );
        let back = (ja / jb) * jb;
        for j in 0..8 {
            for k in 0..12 {
                worst = worst.max(err(back.c[k].lane(j), a[k][j], 1.0));
            }
        }
    }
    println!("Jet<12> quotients: worst error {worst:.1e}");
    assert!(worst < 1e-29, "{worst:e}");
}

/// Control: the quotient recurrence with the sign of the sum flipped fails the reciprocal's series.
#[test]
fn control_wrong_quotient_sign_is_caught() {
    let c: [DD; 8] = std::array::from_fn(|j| DD::from_f64(0.75 + 0.1 * j as f64));
    let y = Jet::<6>::var_lanes(&c);
    let mut q = [DV::zero(); 6];
    q[0] = DV::splat(DD::ONE) / y.c[0];
    for k in 1..6 {
        let mut s = DV::zero();
        for i in 1..=k {
            s = s + y.c[i] * q[k - i];
        }
        q[k] = s / y.c[0]; // the sign of the sum flipped
    }
    let right = Jet::<6>::splat(DD::ONE) / y;
    let caught = (0..8).any(|j| err(q[1].lane(j), right.c[1].lane(j), 1.0) > 1e-3);
    assert!(caught);
}

/// Truncation: `Jet<4>`'s product is the first four coefficients of `Jet<8>`'s, bit for bit
#[test]
fn truncation_keeps_the_low_orders_bit_for_bit() {
    let mut r = Rng(63);
    for _ in 0..200 {
        let a: [[DD; 8]; 8] = std::array::from_fn(|_| std::array::from_fn(|_| r.dd(4)));
        let b: [[DD; 8]; 8] = std::array::from_fn(|_| std::array::from_fn(|_| r.dd(4)));
        let p8 = Jet::<8>::from_coeffs(std::array::from_fn(|k| dv(&a[k])))
            * Jet::<8>::from_coeffs(std::array::from_fn(|k| dv(&b[k])));
        let p4 = Jet::<4>::from_coeffs(std::array::from_fn(|k| dv(&a[k])))
            * Jet::<4>::from_coeffs(std::array::from_fn(|k| dv(&b[k])));
        for k in 0..4 {
            for j in 0..8 {
                let (x, y) = (p8.c[k].lane(j), p4.c[k].lane(j));
                assert!(
                    x.hi.to_bits() == y.hi.to_bits() && x.lo.to_bits() == y.lo.to_bits(),
                    "order {k} lane {j}"
                );
            }
        }
    }
}

/// `var`: the series variable on a jet (value c, coefficient 1 one, the rest zero), `splat(c)` on every other lane
#[test]
fn var_is_the_series_variable_on_jets_and_a_constant_elsewhere() {
    let c = DD::new(1.25, 3e-17);
    let j = Jet::<5>::var(c);
    for l in 0..8 {
        assert_eq!(j.c[0].lane(l), c);
        assert_eq!(j.c[1].lane(l), DD::ONE);
        for k in 2..5 {
            assert_eq!(j.c[k].lane(l), DD::ZERO);
        }
    }
    assert_eq!(Jet::<1>::var(c).c[0].lane(3), c);
    fn constant<T: Lane>(c: DD) -> bool {
        let v = T::var(c);
        let plain = T::VAL_F64;
        let val_ok = (0..8).all(|l| v.val().lane(l) == if plain { DD::from_f64(c.hi) } else { c });
        let tan_ok = if T::TAN_F64 {
            (0..T::NT).all(|k| v.tan64(k).to_array() == [0.0; 8])
        } else if T::TANGENT {
            (0..8).all(|l| v.tan().lane(l) == DD::ZERO)
        } else {
            true
        };
        val_ok && tan_ok && T::NJ == 0
    }
    assert!(constant::<Dv>(c), "DV");
    assert!(constant::<Du>(c), "Du");
    assert!(constant::<Dc>(c), "Dc");
    assert!(constant::<F8>(c), "F8");
    assert!(constant::<Fu>(c), "Fu");
    assert!(constant::<Dtn<2>>(c), "Dtn<2>");
    assert!(constant::<Fun<2>>(c), "Fun<2>");
    assert!(constant::<QV>(c), "QV");
    assert!(constant::<Qu>(c), "Qu");
    assert_eq!(Jet::<5>::NJ, 5);
}

/// f(x, y) = (x^3 + 2 x y) / (x + 3) over `Lane`: `Jet<2>` with the seed on x gives `Du`'s value and tangent to
/// rounding, and `Jet<4>`'s coefficients 2 and 3 are the second and third derivatives over 2! and 3! by hand.
/// Control: the hand formula for f'' / 2 with the sign of its remainder term flipped is caught by the same comparison.
#[test]
fn jet_two_is_a_dual_and_the_higher_orders_are_the_derivatives() {
    fn f<T: Lane>(x: T, y: T) -> T {
        let two = T::splat(DD::from_f64(2.0));
        let three = T::splat(DD::from_f64(3.0));
        (x * x * x + two * x * y) / (x + three)
    }
    let mut r = Rng(64);
    let mut worst = 0.0f64;
    let mut control = 0.0f64;
    for _ in 0..300 {
        let x: [DD; 8] = std::array::from_fn(|_| DD::new(1.0 + 4.0 * r.unit(), r.sym() * 1e-17));
        let y: [DD; 8] = std::array::from_fn(|_| DD::new(r.sym() * 5.0, r.sym() * 1e-17));
        let one = DV::splat(DD::ONE);
        let du = f(Du::from_vt(dv(&x), one), Du::cst(dv(&y)));
        let j2 = f(Jet::<2>::var_lanes(&x), Jet::<2>::cst(dv(&y)));
        let j4 = f(Jet::<4>::var_lanes(&x), Jet::<4>::cst(dv(&y)));
        for l in 0..8 {
            worst = worst.max(err(j2.c[0].lane(l), du.v.lane(l), du.v.lane(l).to_f64().abs().max(1.0)));
            worst = worst.max(err(j2.c[1].lane(l), du.d.lane(l), du.d.lane(l).to_f64().abs().max(1.0)));
            // f = x^2 - 3 x + 9 + 2 y - (27 + 6 y) / (x + 3) by polynomial division: f'' / 2 = 1 - (27 + 6 y) / (x + 3)^3,
            // f''' / 6 = (27 + 6 y) / (x + 3)^4
            let d = x[l] + DD::from_f64(3.0);
            let rem = DD::from_f64(27.0) + DD::from_f64(6.0) * y[l];
            let c2 = DD::ONE - rem / (d * d * d);
            let c3 = rem / (d * d * d * d);
            worst = worst.max(err(j4.c[2].lane(l), c2, c2.to_f64().abs().max(1.0)));
            worst = worst.max(err(j4.c[3].lane(l), c3, c3.to_f64().abs().max(1.0)));
            let c2_wrong = DD::ONE + rem / (d * d * d);
            control = control.max(err(j4.c[2].lane(l), c2_wrong, c2_wrong.to_f64().abs().max(1.0)));
        }
    }
    println!("Jet against Du and the hand derivatives: worst error {worst:.1e}");
    assert!(worst < 1e-29, "{worst:e}");
    assert!(control > 1e-3, "control: {control:e}");
}

/// `coef` past the truncation is zero, `from_vt` seeds coefficient 1, and the accumulator is the product
#[test]
fn accumulator_matches_the_product() {
    let mut r = Rng(65);
    for _ in 0..100 {
        let a: [[DD; 8]; 6] = std::array::from_fn(|_| std::array::from_fn(|_| r.dd(4)));
        let b: [[DD; 8]; 6] = std::array::from_fn(|_| std::array::from_fn(|_| r.dd(4)));
        let (ja, jb) = (
            Jet::<6>::from_coeffs(std::array::from_fn(|k| dv(&a[k]))),
            Jet::<6>::from_coeffs(std::array::from_fn(|k| dv(&b[k]))),
        );
        let p = ja * jb;
        let q = Jet::<6>::fin(Jet::<6>::acc(Jet::<6>::acc0(), ja, jb));
        for k in 0..6 {
            for l in 0..8 {
                let (x, y) = (p.c[k].lane(l), q.c[k].lane(l));
                assert!(x.hi.to_bits() == y.hi.to_bits() && x.lo.to_bits() == y.lo.to_bits());
            }
        }
        assert_eq!(p.coef(6).lane(0), DD::ZERO);
        let s = Jet::<6>::from_vt(ja.c[0], jb.c[0]);
        assert_eq!(s.tan().lane(2), jb.c[0].lane(2));
        assert_eq!(s.coef(2).lane(2), DD::ZERO);
    }
}

// ---------------------------------------------------------------------------------------------------------------
// the parameter arithmetic: Series<N>, mulp, addp, coef
// ---------------------------------------------------------------------------------------------------------------

use multidouble::dual::Param;
use multidouble::jet::Series;

fn series(r: &mut Rng) -> Series<8> {
    let mut s = Series {
        c: std::array::from_fn(|_| DD::new(r.sym(), r.sym() * 1e-17)),
    };
    s.c[0] = DD::new(1.0 + r.unit(), r.sym() * 1e-17);
    s
}

/// the series as a jet, every lane the same
fn as_jet(s: Series<8>) -> Jet<8> {
    Jet::from_coeffs(s.c.map(DV::splat))
}

/// `Series` products and quotients against the jet's, and the jet's `mulp` and `addp` against the product and sum
/// with the series as a jet, bit for bit (the same accumulations)
#[test]
fn series_matches_jets_and_mulp_is_the_product_bit_for_bit() {
    let mut r = Rng(66);
    let mut worst = 0.0f64;
    for _ in 0..200 {
        let (a, b) = (series(&mut r), series(&mut r));
        for (s, j) in [
            (a * b, as_jet(a) * as_jet(b)),
            (a / b, as_jet(a) / as_jet(b)),
            (a - b, as_jet(a) - as_jet(b)),
        ] {
            for k in 0..8 {
                worst = worst.max(err(s.c[k], j.c[k].lane(0), j.c[k].lane(0).to_f64().abs().max(1.0)));
            }
        }
        let x = Jet::<8>::from_coeffs(std::array::from_fn(|_| dv(&std::array::from_fn(|_| r.dd(4)))));
        let (p, q) = (x.mulp(a), x * as_jet(a));
        let (s, t) = (x.addp(a), x + as_jet(a));
        for k in 0..8 {
            for l in 0..8 {
                assert!(bits(p.c[k].lane(l)) == bits(q.c[k].lane(l)), "mulp order {k} lane {l}");
                assert!(bits(s.c[k].lane(l)) == bits(t.c[k].lane(l)), "addp order {k} lane {l}");
            }
        }
    }
    println!("Series against Jet: worst error {worst:.1e}");
    assert!(worst < 1e-29, "{worst:e}");
    let v = Series::<3>::var(DD::from_f64(2.5));
    assert_eq!(v.c, [DD::from_f64(2.5), DD::ONE, DD::ZERO]);
    assert_eq!(<DD as Param>::var(DD::from_f64(2.5)), DD::from_f64(2.5));
    assert_eq!(Series::<2>::one().c, [DD::ONE, DD::ZERO]);
    assert_eq!(Series::<2>::from_f64(3.0).mul_f(0.5).c, [DD::from_f64(1.5), DD::ZERO]);
}

fn bits(x: DD) -> (u64, u64) {
    (x.hi.to_bits(), x.lo.to_bits())
}

/// Control: a `Series` product with its index shifted disagrees with the jet's.
#[test]
fn control_shifted_series_product_is_caught() {
    let mut r = Rng(67);
    let (a, b) = (series(&mut r), series(&mut r));
    let mut c = [DD::ZERO; 8];
    c[0] = a.c[0] * b.c[0];
    for k in 1..8 {
        for i in 0..k {
            c[k] = c[k] + a.c[i] * b.c[k - i - 1];
        }
    }
    let j = as_jet(a) * as_jet(b);
    let caught = (1..8).any(|k| err(c[k], j.c[k].lane(0), j.c[k].lane(0).to_f64().abs().max(1.0)) > 1e-3);
    assert!(caught);
}

/// every part of a lane, value and tangents, as bits
fn parts<T: Lane>(x: T) -> Vec<u64> {
    let mut out = Vec::new();
    let mut push = |v: multidouble::v8::V8<T::S>| {
        let mut a = [0.0; 8];
        v.store(&mut a);
        out.extend(a.iter().map(|f| f.to_bits()));
    };
    let v = x.val();
    push(v.hi);
    push(v.lo);
    if T::TAN_F64 {
        for k in 0..T::NT {
            push(x.tan64(k));
        }
    } else if T::TANGENT {
        let t = x.tan();
        push(t.hi);
        push(t.lo);
    }
    out
}

/// on every lane that is not a jet, `mulp` is `muls` and `addp` is `addc` of the splat constant, bit for bit, and
/// `coef` reads the value and the tangent; `set_coef` on a jet round-trips
#[test]
fn parameter_methods_on_every_lane_type() {
    fn check<T: Lane<P = DD>>(name: &str) {
        let mut r = Rng(68);
        for _ in 0..200 {
            let v: [DD; 8] = std::array::from_fn(|_| r.dd(8));
            let t: [DD; 8] = std::array::from_fn(|_| r.dd(8));
            let mut x = T::from_vt(dv_s::<T::S>(&v), dv_s::<T::S>(&t));
            if T::TAN_F64 {
                for k in 0..T::NT {
                    let a: [f64; 8] = std::array::from_fn(|_| r.dd(8).hi);
                    x.set_tan64(k, multidouble::v8::V8::load(&a));
                }
            }
            let p = r.dd(4);
            assert_eq!(parts(x.mulp(p)), parts(x.muls(p)), "{name}: mulp");
            assert_eq!(parts(x.addp(p)), parts(x.addc(DV::splat(p))), "{name}: addp");
            assert_eq!(parts(T::cst(x.coef(0))), parts(T::cst(x.val())), "{name}: coef 0");
            if T::TANGENT {
                assert_eq!(parts(T::cst(x.coef(1))), parts(T::cst(x.tan())), "{name}: coef 1");
            }
            assert_eq!(parts(T::cst(x.coef(2))), parts(T::zero()), "{name}: coef 2");
        }
    }
    check::<Dv>("DV");
    check::<Du>("Du");
    check::<Dc>("Dc");
    check::<F8>("F8");
    check::<Fu>("Fu");
    check::<Dtn<3>>("Dtn<3>");
    check::<Fun<3>>("Fun<3>");
    check::<QV>("QV");
    check::<Qu>("Qu");
    let mut r = Rng(69);
    let mut j = Jet::<4>::zero();
    let c = dv(&std::array::from_fn(|_| r.dd(4)));
    j.set_coef(2, c);
    assert_eq!(bits(j.coef(2).lane(5)), bits(c.lane(5)));
    assert_eq!(bits(j.coef(3).lane(5)), bits(DD::ZERO));
    assert_eq!(bits(j.coef(9).lane(5)), bits(DD::ZERO));
}

fn dv_s<S: multidouble::simd::Simd>(v: &[DD; 8]) -> DV<S> {
    let hi: Vec<f64> = v.iter().map(|d| d.hi).collect();
    let lo: Vec<f64> = v.iter().map(|d| d.lo).collect();
    DV::load(&hi, &lo)
}
