//! Scalar double-double against exact dyadic arithmetic (`multidouble::exact`, no shared code with the algorithms):
//! the error-free transformations must be exact, and the operations must stay inside their error bounds, measured
//! relative to the exact result in units of u^2 = 2^-106.
#![allow(clippy::needless_range_loop)]
mod common;
use common::{Rng, U2};
use multidouble::dd::{is_pwr2, pow2_near, quick_two_sum, two_prod, two_sum, DD};
use multidouble::exact::Dy;

const N: usize = 20_000;

fn exact(x: DD) -> Dy {
    Dy::from_f64(x.hi).add(&Dy::from_f64(x.lo))
}

/// |got - want| / |want| in units of u^2
fn rel_err(got: DD, want: &Dy) -> f64 {
    if want.is_zero() {
        return if got.hi == 0.0 && got.lo == 0.0 {
            0.0
        } else {
            f64::INFINITY
        };
    }
    exact(got).sub(want).ratio(want).abs() / U2
}

fn normalized(x: DD) -> bool {
    x.hi + x.lo == x.hi
}

#[test]
fn error_free_transformations_are_exact() {
    let mut r = Rng(1);
    for _ in 0..N {
        let (a, b) = (r.dd(30).hi, r.dd(30).hi);
        let (s, e) = two_sum(a, b);
        assert!(
            Dy::sum(&[s, e]).sub(&Dy::sum(&[a, b])).is_zero(),
            "two_sum({a:e}, {b:e})"
        );
        let (p, e) = two_prod(a, b);
        assert!(
            Dy::sum(&[p, e]).sub(&Dy::from_f64(a).mul(&Dy::from_f64(b))).is_zero(),
            "two_prod({a:e}, {b:e})"
        );
        // quick_two_sum needs |a| >= |b|
        let (x, y) = if a.abs() >= b.abs() { (a, b) } else { (b, a) };
        let (s, e) = quick_two_sum(x, y);
        assert!(
            Dy::sum(&[s, e]).sub(&Dy::sum(&[x, y])).is_zero(),
            "quick_two_sum({x:e}, {y:e})"
        );
    }
}

#[test]
fn add_and_sub_within_bounds() {
    let mut r = Rng(2);
    let mut worst: f64 = 0.0;
    for i in 0..N {
        let a = r.dd(20);
        // every fourth pair nearly cancels, the hard case for the relative bound
        let b = if i % 4 == 0 {
            DD::new(-a.hi, r.sym() * a.hi.abs() * 2f64.powi(-60))
        } else {
            r.dd(20)
        };
        for (got, want) in [(a + b, exact(a).add(&exact(b))), (a - b, exact(a).sub(&exact(b)))] {
            assert!(normalized(got));
            let e = rel_err(got, &want);
            worst = worst.max(e);
            assert!(e <= 3.0, "{a:?} +- {b:?}: {e} u^2");
        }
    }
    println!("add/sub: worst {worst:.3} u^2 (bound 3 u^2, Joldes, Muller and Popescu 2017)");
}

#[test]
fn mul_within_bound() {
    let mut r = Rng(3);
    let mut worst: f64 = 0.0;
    for _ in 0..N {
        let (a, b) = (r.dd(20), r.dd(20));
        let got = a * b;
        assert!(normalized(got));
        let e = rel_err(got, &exact(a).mul(&exact(b)));
        worst = worst.max(e);
        assert!(e <= 5.0, "{a:?} * {b:?}: {e} u^2");
        let got = a.mul_f(b.hi);
        let e = rel_err(got, &exact(a).mul(&Dy::from_f64(b.hi)));
        assert!(e <= 3.0, "{a:?} * {:e}: {e} u^2", b.hi);
    }
    println!("mul: worst {worst:.3} u^2");
}

#[test]
fn div_within_bound() {
    let mut r = Rng(4);
    let mut worst: f64 = 0.0;
    for _ in 0..N {
        let (a, b) = (r.dd(20), r.dd(20));
        let q = a / b;
        assert!(normalized(q));
        // q b - a, exactly, relative to a: the quotient's relative error to first order
        let res = exact(q).mul(&exact(b)).sub(&exact(a));
        let e = res.ratio(&exact(a)).abs() / U2;
        worst = worst.max(e);
        assert!(e <= 8.0, "{a:?} / {b:?}: {e} u^2");
    }
    println!("div: worst {worst:.3} u^2");
}

#[test]
fn small_identities() {
    let one = DD::ONE;
    let three = DD::from_f64(3.0);
    let third = one / three;
    assert!(((third * three) - one).to_f64().abs() < 2.0 * U2);
    assert_eq!((DD::from_f64(-2.5)).abs(), DD::from_f64(2.5));
    assert_eq!(DD::from_f64(4.0).recip(), DD::from_f64(0.25));
    assert_eq!(-(-third), third);
    // 2 pi to double-double: hi + lo against the 34-digit decimal value
    let tp: multidouble::qd::QD = "6.283185307179586476925286766559005768394".parse().unwrap();
    assert!((tp - multidouble::qd::QD::from_dd(DD::TWO_PI)).to_f64().abs() < 1e-31);
}

/// The checks above can fail: a double-double add that drops the low parts, and a multiply without the cross terms,
/// both break their bounds on these inputs.
#[test]
fn controls_fire() {
    let mut r = Rng(5);
    let (mut add_caught, mut mul_caught) = (false, false);
    for _ in 0..1000 {
        let (a, b) = (r.dd(20), r.dd(20));
        let (s, e) = two_sum(a.hi, b.hi);
        let broken_add = DD::new(s, e);
        add_caught |= rel_err(broken_add, &exact(a).add(&exact(b))) > 3.0;
        let (p, e) = two_prod(a.hi, b.hi);
        let broken_mul = DD::new(p, e);
        mul_caught |= rel_err(broken_mul, &exact(a).mul(&exact(b))) > 5.0;
    }
    assert!(add_caught && mul_caught);
}

/// `pow2_near` returns a normal power of two within half an octave of x, x itself for a power of two, and the
/// neighbour on the other side when x crosses the geometric midpoint (sqrt 2 times a power of two)
#[test]
fn pow2_near_is_the_nearest_power_of_two() {
    let mut r = Rng(91);
    for _ in 0..N {
        let x = r.dd(300).hi.abs();
        let p = pow2_near(x);
        assert!(is_pwr2(p) && (x / p).log2().abs() <= 0.5, "{x} -> {p}");
    }
    assert_eq!(pow2_near(0.25), 0.25);
    assert_eq!(pow2_near(1e-3), 2f64.powi(-10));
    assert_eq!(pow2_near(3.0), 4.0);
    assert_eq!(pow2_near(2.8), 2.0);
    assert_eq!(pow2_near(1.5 * 2f64.powi(100)), 2f64.powi(101));
    assert!(!is_pwr2(1.5 * pow2_near(2.8)), "control");
}
