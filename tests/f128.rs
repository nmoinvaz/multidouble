//! The f128 conversions of `DD` and `QD` against exact dyadic arithmetic (`multidouble::exact`, no shared code with
//! the conversions): f128 to the greedy round-to-nearest parts (exactly, for `QD`), and the parts to f128 correctly
//! rounded. The reference rounding to f128 is itself checked against the platform's f128 addition and multiplication.
#![feature(f128)]
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::exact::Dy;
use multidouble::qd::QD;

const N: usize = 20_000;

/// a finite f128 with a random sign, a full-width fraction and an exponent in [-emax, emax]
fn f128_in(r: &mut Rng, emax: i64) -> f128 {
    let e = (r.next_u64() % (2 * emax as u64 + 1)) as i64 - emax;
    let fr = (r.next_u64() as u128) << 64 | r.next_u64() as u128;
    let sign = (r.next_u64() & 1) as u128;
    f128::from_bits(sign << 127 | ((e + 16383) as u128) << 112 | (fr & ((1 << 112) - 1)))
}

/// bitwise equal (either zero matches the other: the exact reference has no signed zero)
fn same(a: f128, b: f128) -> bool {
    a.to_bits() == b.to_bits() || (a == 0.0 && b == 0.0)
}

fn exponent(x: f64) -> i32 {
    ((x.to_bits() >> 52) & 0x7ff) as i32 - 1023
}

/// double-doubles, half with a gap below hi so that hi + lo spans more than 113 bits
fn dds(r: &mut Rng) -> Vec<DD> {
    (0..N)
        .map(|i| {
            let a = r.dd(300);
            if i % 2 == 0 {
                a
            } else {
                DD::new(
                    a.hi,
                    r.sym() * a.hi.abs() * 2f64.powi(-53 - (r.next_u64() % 200) as i32),
                )
            }
        })
        .collect()
}

/// quad-doubles of four kinds
fn qds(r: &mut Rng) -> Vec<QD> {
    (0..N)
        .map(|i| {
            let x0 = r.dd(300).hi;
            let e0 = exponent(x0);
            match i % 4 {
                // dense: each part a full-width fraction of the previous one's ulp
                0 => {
                    let x1 = r.sym() * x0.abs() * 2f64.powi(-53);
                    let x2 = r.sym() * x1.abs() * 2f64.powi(-53);
                    QD::new(x0, x1, x2, r.sym() * x2.abs() * 2f64.powi(-53))
                }
                // gaps between the parts
                1 => {
                    let mut x = [x0, 0.0, 0.0, 0.0];
                    for k in 1..4 {
                        x[k] = r.sym() * x[k - 1].abs() * 2f64.powi(-53 - (r.next_u64() % 100) as i32);
                    }
                    QD::new(x[0], x[1], x[2], x[3])
                }
                // ties: x0 + x1 exact in f128, x2 half an f128 ulp of it, x3 deciding the tie or zero
                2 => {
                    let x1 = r.dd(0).hi * 2f64.powi(e0 - 54);
                    let s = x0 as f128 + x1 as f128;
                    let es = ((s.to_bits() >> 112) & 0x7fff) as i32 - 16383;
                    let x2 = 2f64.powi(es - 113) * if r.next_u64() & 1 == 0 { 1.0 } else { -1.0 };
                    let x3 = if r.next_u64().is_multiple_of(3) {
                        0.0
                    } else {
                        r.sym() * x2.abs() * 2f64.powi(-60)
                    };
                    QD { x: [x0, x1, x2, x3] }
                }
                // unnormalized parts of any order (the fields are public)
                _ => {
                    let mut part = || r.sym() * x0.abs() * 2f64.powi((r.next_u64() % 121) as i32 - 60);
                    QD {
                        x: [x0, part(), part(), part()],
                    }
                }
            }
        })
        .collect()
}

/// how many double-doubles `to` converts to other than their exact value rounded once
fn dd_misses(ds: &[DD], to: impl Fn(DD) -> f128) -> usize {
    ds.iter()
        .filter(|d| !same(to(**d), Dy::sum(&[d.hi, d.lo]).to_f128()))
        .count()
}

/// how many quad-doubles `to` converts to other than their exact value rounded once
fn qd_misses(qs: &[QD], to: impl Fn(QD) -> f128) -> usize {
    qs.iter().filter(|q| !same(to(**q), Dy::sum(&q.x).to_f128())).count()
}

/// how many f128 values `from` splits into other than their first n greedy round-to-nearest parts
fn split_misses(xs: &[f128], n: usize, from: impl Fn(f128) -> [f64; 4]) -> usize {
    xs.iter()
        .filter(|&&x| {
            let (got, want) = (from(x), Dy::from_f128(x).greedy4());
            (0..n).any(|k| got[k].to_bits() != want[k].to_bits())
        })
        .count()
}

/// f128 values whose every bit is in f64's range, so that the quad-double split is exact
fn f128s(r: &mut Rng) -> Vec<f128> {
    (0..N).map(|_| f128_in(r, 900)).collect()
}

fn dd_parts(d: DD) -> [f64; 4] {
    [d.hi, d.lo, 0.0, 0.0]
}

#[test]
fn reference_rounding_matches_f128_arithmetic() {
    let mut r = Rng(1);
    let mut misses = 0;
    for _ in 0..N {
        let (a, b) = (f128_in(&mut r, 60), f128_in(&mut r, 60));
        let (da, db) = (Dy::from_f128(a), Dy::from_f128(b));
        misses += !same(da.add(&db).to_f128(), a + b) as usize;
        misses += !same(da.mul(&db).to_f128(), a * b) as usize;
    }
    assert_eq!(misses, 0, "Dy::to_f128 against f128 + and *");
}

#[test]
fn dd_to_f128_is_correctly_rounded() {
    let ds = dds(&mut Rng(2));
    assert_eq!(dd_misses(&ds, DD::to_f128), 0);
}

#[test]
fn qd_to_f128_is_correctly_rounded() {
    let qs = qds(&mut Rng(3));
    assert_eq!(qd_misses(&qs, QD::to_f128), 0);
}

#[test]
fn f128_to_dd_gives_the_greedy_parts() {
    let xs = f128s(&mut Rng(4));
    assert_eq!(split_misses(&xs, 2, |x| dd_parts(DD::from_f128(x))), 0);
}

#[test]
fn f128_to_qd_is_exact_and_round_trips() {
    let xs = f128s(&mut Rng(5));
    assert_eq!(split_misses(&xs, 4, |x| QD::from_f128(x).x), 0);
    for &x in &xs {
        let q = QD::from_f128(x);
        assert!(Dy::sum(&q.x).sub(&Dy::from_f128(x)).is_zero(), "{x:?} -> {q:?}");
        assert!(same(q.to_f128(), x), "{x:?} -> {q:?} -> {:?}", q.to_f128());
    }
}

#[test]
fn non_finite_and_zero() {
    for x in [f128::INFINITY, f128::NEG_INFINITY, f64::MAX as f128 * 2.0] {
        assert_eq!(DD::from_f128(x).hi, x as f64);
        assert_eq!(DD::from_f128(x).lo, 0.0);
        assert_eq!(QD::from_f128(x).x, [x as f64, 0.0, 0.0, 0.0]);
        assert_eq!(QD::from_f128(x).to_f128(), x as f64 as f128);
    }
    assert!(DD::from_f128(f128::NAN).hi.is_nan() && QD::from_f128(f128::NAN).x[0].is_nan());
    assert!(QD::from_f64(f64::INFINITY).to_f128() == f128::INFINITY);
    assert!(QD {
        x: [f64::INFINITY, -f64::INFINITY, 0.0, 0.0]
    }
    .to_f128()
    .is_nan());
    let neg0 = QD { x: [-0.0; 4] }.to_f128();
    assert!(neg0 == 0.0 && neg0.is_sign_negative());
    let cancel = QD {
        x: [1.0, -1.0, -0.0, -0.0],
    }
    .to_f128();
    assert!(cancel == 0.0 && cancel.is_sign_positive());
}

/// Controls: plausible wrong conversions fed to the same checks are caught. Rounding the double-double to f64 first,
/// summing the quad-double parts in f128 (double rounding at the ties), narrowing lo through f32, and stopping the
/// quad-double split at two parts.
#[test]
fn controls_fire() {
    let ds = dds(&mut Rng(2));
    assert!(dd_misses(&ds, |d| (d.hi + d.lo) as f128) > 0);
    let qs = qds(&mut Rng(3));
    assert!(
        qd_misses(&qs, |q| ((q.x[0] as f128 + q.x[1] as f128) + q.x[2] as f128)
            + q.x[3] as f128)
            > 0
    );
    let xs = f128s(&mut Rng(4));
    assert!(
        split_misses(&xs, 2, |x| {
            let hi = x as f64;
            [hi, ((x - hi as f128) as f32) as f64, 0.0, 0.0]
        }) > 0
    );
    assert!(
        split_misses(&xs, 4, |x| {
            let d = DD::from_f128(x);
            [d.hi, d.lo, 0.0, 0.0]
        }) > 0
    );
    // the reference check against the platform's arithmetic, given additions rounded to f64 first
    let mut r = Rng(1);
    let caught = (0..100).any(|_| {
        let (a, b) = (f128_in(&mut r, 60), f128_in(&mut r, 60));
        !same(
            Dy::from_f128(a).add(&Dy::from_f128(b)).to_f128(),
            (a as f64 + b as f64) as f128,
        )
    });
    assert!(caught);
}
