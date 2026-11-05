//! Scalar double-double against exact dyadic arithmetic (`multidouble::exact`, no shared code with the algorithms):
//! the error-free transformations must be exact, and the operations must stay inside their error bounds, measured
//! relative to the exact result in units of u^2 = 2^-106. Also the slice conversions of double-double and quad-double
//! arrays (`dd::split`, `dd::join`, `qd::to_parts`, `qd::from_parts`), bit for bit.
#![allow(clippy::needless_range_loop)]
mod common;
use common::{Rng, U2};
use multidouble::dd::{is_pwr2, join, pow2_near, quick_two_sum, split, two_prod, two_sum, DD};
use multidouble::exact::Dy;
use multidouble::native::QV;
use multidouble::qd::{from_parts, to_parts, QD};

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
    // the ends of the range: the smallest and the largest normal powers of two
    assert_eq!(pow2_near(f64::MIN_POSITIVE), f64::MIN_POSITIVE);
    assert_eq!(pow2_near(1.4 * f64::MIN_POSITIVE), f64::MIN_POSITIVE);
    assert_eq!(pow2_near(2f64.powi(1023)), 2f64.powi(1023));
    assert_eq!(pow2_near(1.4 * 2f64.powi(1023)), 2f64.powi(1023));
}

/// in debug builds, an x whose nearest power of two is subnormal (or infinite) is refused
#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "outside the normal range")]
fn pow2_near_refuses_a_subnormal_result_in_debug() {
    pow2_near(1e-320);
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "outside the normal range")]
fn pow2_near_refuses_an_infinite_result_in_debug() {
    pow2_near(f64::MAX);
}

// ---------------------------------------------------------------------------------------------------------------
// slice conversions
// ---------------------------------------------------------------------------------------------------------------

fn bits(v: &[f64]) -> Vec<u64> {
    v.iter().map(|x| x.to_bits()).collect()
}

/// `split` and `join` are the loops they replace (the parts collected one array at a time, and `DD { hi, lo }` from
/// the zipped arrays) bit for bit, and each undoes the other, also for parts that overlap (which `join` keeps as
/// they are, where `DD::new` would renormalize them) and for empty arrays. Controls: a join with the lo parts dropped
/// or the parts swapped does not give the double-doubles back.
#[test]
fn split_and_join_are_the_loops_and_inverses() {
    let mut r = Rng(91);
    let v: Vec<DD> = (0..37).map(|_| r.dd(20)).collect();
    let (h, l) = split(&v);
    let (hh, ll): (Vec<f64>, Vec<f64>) = (v.iter().map(|d| d.hi).collect(), v.iter().map(|d| d.lo).collect());
    assert!(bits(&h) == bits(&hh) && bits(&l) == bits(&ll));
    let w = join(&h, &l);
    let hand: Vec<DD> = h.iter().zip(&l).map(|(&a, &c)| DD { hi: a, lo: c }).collect();
    let same = |a: &[DD], b: &[DD]| {
        a.len() == b.len()
            && a.iter()
                .zip(b)
                .all(|(x, y)| x.hi.to_bits() == y.hi.to_bits() && x.lo.to_bits() == y.lo.to_bits())
    };
    assert!(same(&w, &hand) && same(&w, &v));
    // overlapping parts, each about 2^-20 of its hi
    let (oh, ol): (Vec<f64>, Vec<f64>) = (0..37).map(|_| (r.sym(), r.sym() * 2f64.powi(-20))).unzip();
    let (h2, l2) = split(&join(&oh, &ol));
    assert!(bits(&h2) == bits(&oh) && bits(&l2) == bits(&ol));
    assert!(
        oh.iter()
            .zip(&ol)
            .any(|(&a, &b)| DD::new(a, b).hi.to_bits() != a.to_bits()),
        "control: no overlap"
    );
    assert!(split(&[]) == (vec![], vec![]) && join(&[], &[]).is_empty());
    assert!(!same(&join(&h, &vec![0.0; h.len()]), &v), "control: lo dropped");
    assert!(!same(&join(&l, &h), &v), "control: parts swapped");
}

#[test]
#[should_panic(expected = "join: 3 hi parts and 2 lo parts")]
fn join_refuses_arrays_of_different_lengths() {
    join(&[1.0, 2.0, 3.0], &[0.0, 0.0]);
}

/// `to_parts` and `from_parts` are the loops they replace (part k of every value collected into array k, and
/// `QD { x }` from part k of each array at index i) bit for bit, each undoes the other for parts that overlap (not
/// renormalized, as `QD::new` would), and `from_parts` reads the four arrays as `QV::load` does, value i at lane i.
/// Controls: two parts swapped, or the last part dropped, do not give the quad-doubles back.
#[test]
fn to_parts_and_from_parts_are_the_loops_and_inverses() {
    let mut r = Rng(92);
    let n = 40;
    // overlapping parts, each about 2^-20 of the one before
    let c: [Vec<f64>; 4] = std::array::from_fn(|k| (0..n).map(|_| r.sym() * 2f64.powi(-20 * k as i32)).collect());
    let q = from_parts([&c[0], &c[1], &c[2], &c[3]]);
    let hand: Vec<QD> = (0..n)
        .map(|i| QD {
            x: std::array::from_fn(|k| c[k][i]),
        })
        .collect();
    let same = |a: &[QD], b: &[QD]| {
        a.len() == b.len()
            && a.iter()
                .zip(b)
                .all(|(x, y)| x.x.iter().zip(y.x.iter()).all(|(p, s)| p.to_bits() == s.to_bits()))
    };
    assert!(same(&q, &hand));
    let back = to_parts(&q);
    let loops: [Vec<f64>; 4] = std::array::from_fn(|k| q.iter().map(|v| v.x[k]).collect());
    for k in 0..4 {
        assert!(
            bits(&back[k]) == bits(&c[k]) && bits(&loops[k]) == bits(&c[k]),
            "part {k}"
        );
    }
    for b in 0..n / 8 {
        let o = 8 * b;
        let v = QV::load(&c[0][o..o + 8], &c[1][o..o + 8], &c[2][o..o + 8], &c[3][o..o + 8]);
        assert!(same(&v.lanes(), &q[o..o + 8]), "lane vector {b}");
    }
    assert!(
        (0..4).any(|k| QD::new(c[0][0], c[1][0], c[2][0], c[3][0]).x[k].to_bits() != c[k][0].to_bits()),
        "control: no overlap"
    );
    assert!(to_parts(&[]).iter().all(|p| p.is_empty()) && from_parts([&[], &[], &[], &[]]).is_empty());
    assert!(
        !same(&from_parts([&c[1], &c[0], &c[2], &c[3]]), &q),
        "control: parts swapped"
    );
    assert!(
        !same(&from_parts([&c[0], &c[1], &c[2], &vec![0.0; n]]), &q),
        "control: last part dropped"
    );
}

#[test]
#[should_panic(expected = "from_parts: the four arrays must have one length")]
fn from_parts_refuses_arrays_of_different_lengths() {
    from_parts([&[1.0, 2.0], &[0.0, 0.0], &[0.0], &[0.0, 0.0]]);
}
