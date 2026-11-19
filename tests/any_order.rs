//! The constructors `DD::new`, `QD::new`, `OD::new` and `OV::new` on parts in any order. Each result is the exact sum
//! of the parts (`exact::Dy`), with zero parts only after the nonzero ones and each part at most the ulp of the one
//! before, for parts in random order with cancelling pairs, zeros between nonzero parts, huge and tiny parts, signed
//! zeros, subnormals and parts that overlap in one binade. Parts with a NaN or an infinity give a first part that is
//! not finite, and the lanes give the scalar bits on every backend. Controls (feature `mutate`): the constructors
//! as they were (`any_order::mutate::AS_GIVEN`), without their fallback (`NO_FALLBACK`), without the fallback's retry
//! after an overflow (`NO_BALANCE`), and lanes that keep an overflow (`LANES_KEEP_OVERFLOW`) fail these checks.
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::exact::Dy;
use multidouble::od::OD;
use multidouble::ov::OV;
use multidouble::qd::QD;
use multidouble::simd::{self, Kernel, Simd};
use multidouble::v8::V8;
use std::cmp::Ordering;

/// cases per type, fewer in the unoptimized coverage build
fn cases() -> usize {
    if cfg!(debug_assertions) {
        20000
    } else {
        60000
    }
}

/// the unit in the last place of a finite x (the subnormal spacing for zero and subnormal x), exactly
fn ulp(x: f64) -> Dy {
    let e = ((x.to_bits() >> 52) & 0x7ff) as i64;
    Dy::from_f64(1.0).ldexp(if e == 0 { -1074 } else { e - 1075 })
}

/// how r fails the constructors' contract for the parts c: "value" if its sum is not c's, "ladder" if a zero part
/// precedes a nonzero one or a part exceeds the ulp of the one before
fn faults(c: &[f64], r: &[f64]) -> (bool, bool) {
    // a part that is not finite (a partial sum that overflowed) is a wrong value
    if !r.iter().all(|x| x.is_finite()) {
        return (true, false);
    }
    let value = !Dy::sum(c).sub(&Dy::sum(r)).is_zero();
    let ladder = (0..r.len() - 1).any(|k| {
        if r[k] == 0.0 {
            r[k + 1] != 0.0
        } else {
            Dy::from_f64(r[k + 1]).cmp_abs(&ulp(r[k])) == Ordering::Greater
        }
    });
    (value, ladder)
}

/// the largest |r_(k+1)| / ulp(r_k) over r's nonzero parts
fn worst_ratio(r: &[f64]) -> f64 {
    (0..r.len() - 1)
        .filter(|&k| r[k] != 0.0)
        .map(|k| Dy::from_f64(r[k + 1]).ratio(&ulp(r[k])))
        .fold(0.0, f64::max)
}

/// +1 or -1 with equal odds
fn sign(r: &mut Rng) -> f64 {
    if r.next_u64() & 1 == 0 {
        1.0
    } else {
        -1.0
    }
}

/// an integer in [lo, hi]
fn int(r: &mut Rng, lo: i32, hi: i32) -> i32 {
    lo + (r.next_u64() % (hi - lo + 1) as u64) as i32
}

/// a double with a random sign and an exponent in [lo, hi], a zero of either sign one time in eight
fn double(r: &mut Rng, lo: i32, hi: i32) -> f64 {
    if r.next_u64().is_multiple_of(8) {
        return 0.0 * sign(r);
    }
    (1.0 + r.unit()) * 2f64.powi(int(r, lo, hi)) * sign(r)
}

/// m 2^e with m in 1..15 and e in [lo, hi], zero one time in six: few significant bits, so that sums are often exact
/// and ties common
fn sparse(r: &mut Rng, lo: i32, hi: i32) -> f64 {
    if r.next_u64().is_multiple_of(6) {
        return 0.0;
    }
    (1 + r.next_u64() % 15) as f64 * 2f64.powi(int(r, lo, hi)) * sign(r)
}

/// x in a random order (Fisher-Yates)
fn permuted<const N: usize>(r: &mut Rng, mut x: [f64; N]) -> [f64; N] {
    for i in (1..N).rev() {
        x.swap(i, (r.next_u64() % (i as u64 + 1)) as usize);
    }
    x
}

/// the parts of a value from the N-part arithmetic, largest first
fn normalized<const N: usize>(r: &mut Rng) -> [f64; N] {
    let (a, b, c) = (r.dd(30), r.dd(30), r.dd(30));
    let p: Vec<f64> = match N {
        2 => vec![(a * b + c).hi, (a * b + c).lo],
        4 => (QD::from_dd(a) * QD::from_dd(b) + QD::from_dd(c)).x.to_vec(),
        _ => (OD::from_qd(QD::from_dd(a) * QD::from_dd(b)) * OD::from_dd(c) + OD::from_dd(r.dd(30)))
            .x
            .to_vec(),
    };
    std::array::from_fn(|i| p[i])
}

/// the families of inputs, by i
const FAMILIES: usize = 12;

/// the ulp of a finite x, 2^-1074 for zero and subnormal x
fn ulp_f64(x: f64) -> f64 {
    f64::from_bits(x.to_bits() & 0x7ff0_0000_0000_0000).max(f64::MIN_POSITIVE) * f64::EPSILON
}

/// parts of family i % FAMILIES: a normalized value's parts permuted; cancelling pairs among other parts;
/// independent parts over 240 binades; parts in four nearby binades; few-bit parts over 60 binades; few-bit parts in
/// seven binades; a huge cancelling pair with tiny parts (the shape of the report on PR #89); parts over the whole
/// exponent range with subnormals; positive parts in one binade (whose sorted renormalization can come out off the
/// ladder); signed zeros among few-bit parts; parts already on the ladder, each up to a whole ulp of the one before
/// and the first down to the subnormals (the constructors' path that renormalizes them as given); two parts of one
/// sign, cancelled by two smaller ones of the other sign whose sum overflows, among smaller parts
fn inputs<const N: usize>(r: &mut Rng, i: usize) -> [f64; N] {
    match i % FAMILIES {
        0 => {
            let x = normalized(r);
            permuted(r, x)
        }
        1 => {
            let mut x: [f64; N] = std::array::from_fn(|_| double(r, -60, 60));
            for p in 0..1 + (r.next_u64() % (N as u64 / 2)) as usize {
                let y = x[2 * p];
                x[2 * p + 1] = match r.next_u64() % 3 {
                    0 => -y,
                    1 => -y * (1.0 + f64::EPSILON * (r.next_u64() % 8) as f64),
                    _ => y * 2f64.powi(-int(r, 0, 200)),
                };
            }
            permuted(r, x)
        }
        2 => std::array::from_fn(|_| double(r, -120, 120)),
        3 => {
            let e = int(r, -20, 20);
            std::array::from_fn(|_| double(r, e, e + 3))
        }
        4 => {
            let e = int(r, -20, 20);
            std::array::from_fn(|_| sparse(r, e - 60, e + 3))
        }
        5 => {
            let e = int(r, -5, 5);
            std::array::from_fn(|_| sparse(r, e - 3, e + 3))
        }
        6 => {
            let mut x: [f64; N] = std::array::from_fn(|_| sparse(r, -300, 2));
            let h = sparse(r, 40, 120);
            (x[0], x[1]) = (h, -h);
            permuted(r, x)
        }
        7 => {
            // below 2^1018, so that no partial sum of eight parts overflows
            let mut x: [f64; N] = std::array::from_fn(|_| double(r, -1074, 1018));
            x[0] = f64::from_bits(r.next_u64() % (1 << 52)) * sign(r);
            permuted(r, x)
        }
        8 => {
            let e = int(r, -4, 4);
            std::array::from_fn(|_| (1.0 + r.unit()) * 2f64.powi(e))
        }
        9 => std::array::from_fn(|_| {
            if r.next_u64() & 1 == 0 {
                0.0 * sign(r)
            } else {
                sparse(r, -10, 10)
            }
        }),
        11 => {
            // a, b in [1.5, 1.75) 2^1023 and c, d in [1.25, 1.5) 2^1023 of the other sign: sorted, c + d overflows
            // first, and the sum lies in (-2^1023, 2^1023)
            let mut x: [f64; N] = std::array::from_fn(|_| double(r, -100, 1000));
            let s = sign(r);
            let mut big = |lo: f64| (lo + 0.25 * r.unit()) * 2f64.powi(1023);
            let (a, b, c, d) = (big(1.5) * s, big(1.5) * s, -big(1.25) * s, -big(1.25) * s);
            if N >= 4 {
                (x[0], x[1], x[2], x[3]) = (a, b, c, d);
            } else {
                (x[0], x[1]) = (a, c);
            }
            permuted(r, x)
        }
        _ => {
            let mut x = [0.0; N];
            x[0] = (1.0 + r.unit()) * 2f64.powi(int(r, -1022, 1000)) * sign(r);
            // the parts after a random one zeroed one time in four
            let end = if r.next_u64().is_multiple_of(4) {
                1 + (r.next_u64() % N as u64) as usize
            } else {
                N
            };
            for k in 1..end {
                let u = ulp_f64(x[k - 1]);
                let m = if r.next_u64().is_multiple_of(8) { 1.0 } else { r.unit() };
                x[k] = if x[k - 1] == 0.0 { 0.0 } else { m * u * sign(r) };
            }
            x
        }
    }
}

/// the scalar constructor of N parts
fn construct<const N: usize>(x: [f64; N]) -> [f64; N] {
    let p: Vec<f64> = match N {
        2 => {
            let d = DD::new(x[0], x[1]);
            vec![d.hi, d.lo]
        }
        4 => QD::new(x[0], x[1], x[2], x[3]).x.to_vec(),
        _ => OD::new(std::array::from_fn(|i| x[i])).x.to_vec(),
    };
    std::array::from_fn(|i| p[i])
}

/// a constructor's faults on `cases()` unordered inputs
struct Tally {
    /// results whose sum is not the parts'
    value: usize,
    /// results off the ladder
    ladder: usize,
    /// the largest |x_(k+1)| / ulp(x_k) of the results
    worst: f64,
    /// the parts of a faulty case
    example: Option<Vec<f64>>,
}

/// The constructor of N parts on `cases()` unordered inputs from the seed
fn run<const N: usize>(seed: u64) -> Tally {
    let mut r = Rng(seed);
    let mut t = Tally {
        value: 0,
        ladder: 0,
        worst: 0.0,
        example: None,
    };
    for i in 0..cases() {
        let c: [f64; N] = inputs(&mut r, i);
        let x = construct(c);
        let (v, l) = faults(&c, &x);
        t.value += v as usize;
        t.ladder += l as usize;
        if (v || l) && t.example.is_none() {
            t.example = Some(c.to_vec());
        }
        if x.iter().all(|p| p.is_finite()) {
            t.worst = t.worst.max(worst_ratio(&x));
        }
    }
    t
}

/// the three constructors' tallies, on the same inputs whatever the mutation
fn tallies() -> [(&'static str, Tally); 3] {
    [
        ("DD::new", run::<2>(1)),
        ("QD::new", run::<4>(2)),
        ("OD::new", run::<8>(3)),
    ]
}

/// the constructors' results are the exact sums of the parts, on the ladder, for every family
#[test]
fn constructors_sum_exactly_onto_the_ladder() {
    for (name, t) in tallies() {
        println!("{name}: {} cases, worst |x_(k+1)| / ulp(x_k) {:.4}", cases(), t.worst);
        assert!(
            t.value == 0 && t.ladder == 0,
            "{name}: {} wrong values, {} off the ladder, e.g. {:?}",
            t.value,
            t.ladder,
            t.example
        );
    }
}

/// A NaN or an infinity among the parts, in any position, gives a first part that is not finite. Control: the same
/// parts with a zero in its place give a finite one.
#[test]
fn non_finite_parts_give_a_non_finite_result() {
    let mut r = Rng(4);
    let specials = [f64::NAN, f64::INFINITY, f64::NEG_INFINITY];
    let not_finite = |x: &[f64]| !x[0].is_finite();
    // the overflow family's parts, one replaced by zero, can sum past the largest double
    for i in (0..300).filter(|i| i % FAMILIES != 11) {
        let s = specials[i % 3];
        let mut c2: [f64; 2] = inputs(&mut r, i);
        let mut c4: [f64; 4] = inputs(&mut r, i);
        let mut c8: [f64; 8] = inputs(&mut r, i);
        let (k2, k4, k8) = (
            (r.next_u64() % 2) as usize,
            (r.next_u64() % 4) as usize,
            (r.next_u64() % 8) as usize,
        );
        (c2[k2], c4[k4], c8[k8]) = (0.0, 0.0, 0.0);
        for (c, x) in [
            (c2.to_vec(), construct(c2).to_vec()),
            (c4.to_vec(), construct(c4).to_vec()),
            (c8.to_vec(), construct(c8).to_vec()),
        ] {
            assert!(!not_finite(&x), "control: {c:?} gives {x:?}");
        }
        (c2[k2], c4[k4], c8[k8]) = (s, s, s);
        for (c, x) in [
            (c2.to_vec(), construct(c2).to_vec()),
            (c4.to_vec(), construct(c4).to_vec()),
            (c8.to_vec(), construct(c8).to_vec()),
        ] {
            assert!(not_finite(&x), "{c:?} gives {x:?}");
        }
    }
}

/// The report of PR #89 and the two like it: `DD::new(2^-60, 1)` gave 1, `QD::new(2^-213, 2^54, 1, -2^54)` gave
/// 2^-213, and `OD::new` of the same with 2^-270 gave the parts [2^-213, 1, 2^-270], whose reciprocal was NaN and whose
/// cosine was 1. Parts near the overflow threshold whose sorted sum overflows give their finite sum.
#[test]
fn reported_cases() {
    let p = |e: i32| 2f64.powi(e);
    let d = DD::new(p(-60), 1.0);
    assert_eq!((d.hi, d.lo), (1.0, p(-60)));
    let q = QD::new(p(-213), p(54), 1.0, -p(54));
    assert_eq!(q.x, [1.0, p(-213), 0.0, 0.0]);
    let o = OD::new([p(-213), p(54), p(-270), 1.0, -p(54), 0.0, 0.0, 0.0]);
    assert_eq!(o.x, [1.0, p(-213), p(-270), 0.0, 0.0, 0.0, 0.0, 0.0]);
    let inv = OD::ONE / o;
    assert!(inv.x.iter().all(|x| x.is_finite()) && inv.to_f64() == 1.0, "{inv:?}");
    // cos 1 = 0.5403023058681398 to f64; the tiny-argument shortcut would give 1
    let c = o.cos().to_f64();
    assert!((c - 1f64.cos()).abs() < 1e-15, "{c}");
    // Greptile's case on this PR: sorted, (-h, -h, p, p) sums p + p first, which overflows, where the sum is -p
    let h = 1.5 * p(1023);
    assert_eq!(QD::new(-h, p(1023), -h, p(1023)).x, [-p(1023), 0.0, 0.0, 0.0]);
    let o = OD::new([-h, p(1023), -h, p(1023), 0.0, 0.0, 0.0, 0.0]);
    assert_eq!(o.x, [-p(1023), 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]);
    // CodeRabbit's case: sorted, (-M, 2^1023, 2^1023) sums 2^1023 + 2^1023 first, which overflows, where the sum is
    // 2^971
    let m = f64::MAX;
    assert_eq!(QD::new(p(1023), p(1023), -m, 0.0).x, [p(971), 0.0, 0.0, 0.0]);
    let o = OD::new([p(1023), p(1023), -m, 0.0, 0.0, 0.0, 0.0, 0.0]);
    assert_eq!(o.x, [p(971), 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]);
}

/// `OV::new` against `OD::new` lane by lane on one backend: the lanes whose parts differ in any bit (NaNs alike)
#[derive(Clone)]
struct OvNewMatchesOdNew;

impl Kernel for OvNewMatchesOdNew {
    type Output = usize;
    /// rounds of 8 lanes: all normalized (the lanes renormalize together), all sorted and in one binade or in the
    /// overflow family (some or all lanes take the fallback), every family mixed, and a NaN or an infinity on one lane
    #[inline(always)]
    fn run<S: Simd>(self) -> usize {
        let mut r = Rng(5);
        let mut bad = 0;
        for round in 0..cases() / 8 {
            let x: [[f64; 8]; 8] = std::array::from_fn(|j| match round % 4 {
                0 => normalized(&mut r),
                1 => {
                    // the overflow family's sorted parts overflow in the lanes' renormalization
                    let mut c: [f64; 8] = inputs(&mut r, if round % 8 == 1 { 8 } else { 11 });
                    c.sort_by(|a, b| b.abs().total_cmp(&a.abs()));
                    c
                }
                2 => inputs(&mut r, round + j),
                _ => {
                    let mut c: [f64; 8] = normalized(&mut r);
                    if j == round / 4 % 8 {
                        c[(r.next_u64() % 8) as usize] = [f64::NAN, f64::INFINITY, f64::NEG_INFINITY][round / 32 % 3];
                    }
                    c
                }
            });
            let v = OV::<S>::new(std::array::from_fn(|k| {
                V8::from_array(std::array::from_fn(|j| x[j][k]))
            }));
            for (j, &xj) in x.iter().enumerate() {
                let (g, w) = (v.lane(j), OD::new(xj));
                let same =
                    g.x.iter()
                        .zip(w.x)
                        .all(|(a, b)| a.to_bits() == b.to_bits() || (a.is_nan() && b.is_nan()));
                bad += !same as usize;
            }
        }
        bad
    }
}

/// `OV::new` gives `OD::new`'s bits on every lane, on every backend this CPU runs
#[test]
fn ov_new_matches_od_new_in_any_order() {
    let ran = simd::for_each_available(OvNewMatchesOdNew);
    assert_eq!(ran.iter().map(|r| r.0).collect::<Vec<_>>(), simd::available());
    assert!(ran.iter().all(|r| r.1 == 0), "lanes that differ: {ran:?}");
    println!("checked on {:?}", simd::available());
}

/// The controls: the constructors as they were fail the checks (`DD::new` and `QD::new` on the value, `QD::new` and
/// `OD::new` on the ladder), without the fallback `QD::new` and `OD::new` leave parts off the ladder and overflow on the
/// overflow family, and without the fallback's retry after an overflow they overflow there. The lanes follow the
/// scalar constructor under each.
#[cfg(feature = "mutate")]
#[test]
fn controls_fail_the_checks() {
    use multidouble::any_order::mutate;
    for id in [mutate::AS_GIVEN, mutate::NO_FALLBACK, mutate::NO_BALANCE] {
        mutate::set(id);
        let rows = tallies();
        let lanes = simd::for_each_available(OvNewMatchesOdNew);
        mutate::set(0);
        for (name, t) in &rows {
            println!(
                "'{}': {name}: {} wrong values, {} off the ladder, worst |x_(k+1)| / ulp(x_k) {:.4}",
                mutate::NAMES[id as usize],
                t.value,
                t.ladder,
                t.worst
            );
        }
        assert!(lanes.iter().all(|r| r.1 == 0), "lanes that differ: {lanes:?}");
        let [dd, qd, od] = rows.map(|(_, t)| (t.value > 0, t.ladder > 0));
        if id == mutate::AS_GIVEN {
            assert!(dd.0 && qd.0 && qd.1 && od.1, "{dd:?} {qd:?} {od:?}");
        } else if id == mutate::NO_FALLBACK {
            assert!(qd.0 && qd.1 && od.0 && od.1, "{qd:?} {od:?}");
        } else {
            assert!(qd.0 && od.0, "{qd:?} {od:?}");
        }
    }
}

/// The lanes' control: `OV::new` keeping the lanes' renormalization when its first part is not finite differs from
/// `OD::new` on the sorted lanes of the overflow family, on every backend this CPU runs
#[cfg(feature = "mutate")]
#[test]
fn lanes_control_fails_the_check() {
    use multidouble::any_order::mutate;
    mutate::set(mutate::LANES_KEEP_OVERFLOW);
    let lanes = simd::for_each_available(OvNewMatchesOdNew);
    mutate::set(0);
    println!(
        "'{}': lanes that differ: {lanes:?}",
        mutate::NAMES[mutate::LANES_KEEP_OVERFLOW as usize]
    );
    assert!(lanes.iter().all(|r| r.1 > 0), "lanes that differ: {lanes:?}");
}
