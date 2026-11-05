//! `QD::from_sum` and `qv::renorm4_any`: four parts given in any order, summed exactly and renormalized. Checked
//! against exact dyadic arithmetic (`exact::Dy`), bitwise `QD::new` on normalized parts, and the 8 lanes bitwise the
//! scalar on every backend this CPU runs. Control: `QD::new` itself, which assumes ordered parts, must fail the
//! exactness check on unordered ones.
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::exact::Dy;
use multidouble::qd::{renorm4_any, QD};
use multidouble::qv;
use multidouble::simd::{self, Kernel, Simd};
use multidouble::v8::V8;
use std::cmp::Ordering;

const N: usize = 40000;

/// CodeRabbit's case on PR #32: two cancelling pairs, out of order, whose sum is zero
const CANCEL: [f64; 4] = [1.0, 1e16, -1.0, -1e16];

fn ulp(x: f64) -> Dy {
    let e = ((x.to_bits() >> 52) & 0x7ff) as i64;
    Dy::from_f64(1.0).ldexp(if e == 0 { -1074 } else { e - 1075 })
}

/// r sums exactly to c and is normalized: zero parts only after the nonzero ones, each part at most the ulp of the one
/// before
fn exact_and_normalized(c: [f64; 4], r: [f64; 4]) -> bool {
    if !Dy::sum(&c).sub(&Dy::sum(&r)).is_zero() {
        return false;
    }
    (0..3).all(|k| {
        if r[k] == 0.0 {
            r[k + 1..].iter().all(|&x| x == 0.0)
        } else {
            Dy::from_f64(r[k + 1]).cmp_abs(&ulp(r[k])) != Ordering::Greater
        }
    })
}

fn sign(r: &mut Rng) -> f64 {
    if r.next_u64() & 1 == 0 {
        1.0
    } else {
        -1.0
    }
}

/// a double with a random sign and an exponent in [lo, hi], zero one time in eight
fn double(r: &mut Rng, lo: i32, hi: i32) -> f64 {
    if r.next_u64().is_multiple_of(8) {
        return 0.0;
    }
    let e = lo + (r.next_u64() % (hi - lo + 1) as u64) as i32;
    (1.0 + r.unit()) * 2f64.powi(e) * sign(r)
}

/// the parts of a normalized quad-double from quad-double arithmetic
fn normalized(r: &mut Rng) -> [f64; 4] {
    let (a, b) = (r.dd(30), r.dd(30));
    QD::from_dd(a)
        .add_dd(DD::new(b.hi * 2f64.powi(-106), b.lo * 2f64.powi(-106)))
        .x
}

fn permuted(r: &mut Rng, mut x: [f64; 4]) -> [f64; 4] {
    for i in (1..4).rev() {
        x.swap(i, (r.next_u64() % (i as u64 + 1)) as usize);
    }
    x
}

/// unordered parts: a normalized quad-double's parts permuted, cancelling pairs, four independent doubles over a wide
/// range of exponents, and four in nearby binades (carries between parts)
fn unordered(r: &mut Rng, i: usize) -> [f64; 4] {
    match i % 4 {
        0 => {
            let x = normalized(r);
            permuted(r, x)
        }
        1 => {
            let (x, y) = (double(r, -60, 60), double(r, -60, 60));
            let z = if r.next_u64() & 1 == 0 { -y } else { y * 2f64.powi(-70) };
            permuted(r, [x, y, -x, z])
        }
        2 => std::array::from_fn(|_| double(r, -120, 120)),
        _ => {
            let e = (r.next_u64() % 41) as i32 - 20;
            std::array::from_fn(|_| double(r, e, e + 3))
        }
    }
}

#[test]
fn from_sum_is_exact_in_any_order() {
    let z = QD::from_sum(CANCEL[0], CANCEL[1], CANCEL[2], CANCEL[3]);
    assert!(z.x.iter().all(|&x| x == 0.0), "{:?}", z.x);
    let mut r = Rng(17);
    let bad: Vec<[f64; 4]> = (0..N)
        .map(|i| unordered(&mut r, i))
        .filter(|&c| !exact_and_normalized(c, renorm4_any(c[0], c[1], c[2], c[3])))
        .collect();
    assert!(
        bad.is_empty(),
        "{} of {N} not exact or not normalized, e.g. {:?}",
        bad.len(),
        &bad[..bad.len().min(3)]
    );
}

/// parts on which QD::new's quick two-sums are exact, normalized ones among them, keep its bits
#[test]
fn from_sum_is_new_on_normalized_parts() {
    let mut r = Rng(19);
    for i in 0..N {
        let c = match i % 4 {
            0 => normalized(&mut r),
            3 => {
                // the parts the pinned systems of src/linalg.rs and the Python tests give QD::new
                let d = r.dd(30);
                [d.hi, d.lo, d.lo * 3.1e-17, d.hi * 7.3e-49]
            }
            1 => {
                let d = r.dd(300);
                [d.hi, d.lo, 0.0, 0.0]
            }
            _ => [double(&mut r, -1000, 1000), 0.0, 0.0, 0.0],
        };
        let (a, b) = (QD::from_sum(c[0], c[1], c[2], c[3]), QD::new(c[0], c[1], c[2], c[3]));
        assert!(
            a.x.iter().zip(b.x).all(|(p, q)| p.to_bits() == q.to_bits()),
            "{c:?}: {:?} against {:?}",
            a.x,
            b.x
        );
    }
}

/// the check can fail: `QD::new` gives 1 for CANCEL, and misses on a share of the other unordered parts
#[test]
fn new_fails_the_check_on_unordered_parts() {
    let z = QD::new(CANCEL[0], CANCEL[1], CANCEL[2], CANCEL[3]);
    assert!(!exact_and_normalized(CANCEL, z.x), "{:?}", z.x);
    let mut r = Rng(17);
    let missed = (0..N)
        .map(|i| unordered(&mut r, i))
        .filter(|&c| !exact_and_normalized(c, QD::new(c[0], c[1], c[2], c[3]).x))
        .count();
    println!("QD::new misses {missed} of {N} unordered cases");
    assert!(missed >= N / 10, "QD::new missed only {missed} of {N}");
}

#[derive(Clone)]
struct LanesMatchScalar;

impl Kernel for LanesMatchScalar {
    type Output = ();
    #[inline(always)]
    fn run<S: Simd>(self) {
        let mut r = Rng(23);
        for round in 0..N / 8 {
            // lanes mixing normalized and unordered parts, and non-finite ones, which keep renorm4
            let c: [[f64; 4]; 8] = std::array::from_fn(|j| match (round + j) % 5 {
                0 => normalized(&mut r),
                4 if j == 7 => [f64::INFINITY, 1.0, f64::NAN, 2.0],
                k => unordered(&mut r, k),
            });
            let part = |k: usize| V8::<S>::load(&std::array::from_fn::<f64, 8, _>(|j| c[j][k]));
            let v = qv::renorm4_any(part(0), part(1), part(2), part(3));
            let mut out = [[0.0f64; 8]; 4];
            for k in 0..4 {
                v[k].store(&mut out[k]);
            }
            for j in 0..8 {
                let want = renorm4_any(c[j][0], c[j][1], c[j][2], c[j][3]);
                for k in 0..4 {
                    let (a, b) = (out[k][j], want[k]);
                    assert!(
                        a.to_bits() == b.to_bits() || (a.is_nan() && b.is_nan()),
                        "{:?}: lane {:?}",
                        c[j],
                        a
                    );
                }
            }
        }
    }
}

#[test]
fn renorm4_any_lanes_match_scalar() {
    let ran: Vec<&str> = simd::for_each_available(LanesMatchScalar)
        .into_iter()
        .map(|r| r.0)
        .collect();
    assert_eq!(ran, simd::available());
    println!("checked on {ran:?}");
}
