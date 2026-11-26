//! Correctly rounded ratios of integers (`recip`): every part of `ratio_parts(p, q)` and `recip_parts(k)` against a
//! reference built from exact rationals with `exact`'s big integers and dyadics (each part the round-to-nearest of the
//! exact remainder p/q - r_0 - ... - r_(i-1), found by long division of its dyadic numerator by q), and bit for bit
//! against choptuik-large-d's `recip_parts` and `recip_lane` (hp/src/model.rs, copied below) for every k up to 2^20.
//!
//! Pass, fixed before the first run: every part equal to the reference's, bit for bit, on k = 1..=5000, on 4000 random
//! q < 2^60 with p = 1, and on 4000 random (p, q) with |p| < 2^63, including p > q and negative p, and on p = i64::MIN;
//! the types' `recip_int` and `from_ratio` equal to those prefixes, a double-double's as their two-sum; every
//! double-double constant a double word, hi = RN(hi + lo), of the prefix's value, also at the three k found whose
//! greedy pair is a tie; hp's parts and lane constants equal bit for bit for k = 1..=2^20; and x k times 1/k within
//! 8 u^2, 64 u^4 and 1024 u^8 of x on DD, QD and OD (the bars of `mul_recip_inverts_multiplication`). Controls
//! (feature `mutate`), which must fail: the last part of each type's constant one ulp up (`recip::mutate::LAST_ULP`),
//! and a double-double's parts without the two-sum (`recip::mutate::DD_GREEDY`), at the three ties.
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::exact::{round_to_f64, BigU, Dy};
use multidouble::native::{OV, QV};
use multidouble::od::OD;
use multidouble::qd::QD;
use multidouble::recip::{ratio_parts, recip_parts};

/// the exact signed dyadic numerator p - q (r_0 + ... ), as a Dy
fn numerator(p: i64, q: u64, parts: &[f64]) -> Dy {
    let mut num = Dy {
        neg: p < 0,
        m: BigU::from_u64(p.unsigned_abs()),
        e: 0,
    };
    let qd = Dy {
        neg: false,
        m: BigU::from_u64(q),
        e: 0,
    };
    for &r in parts {
        num = num.sub(&qd.mul(&Dy::from_f64(r)));
    }
    num
}

/// RN(n / q) for a signed dyadic n, by long division of n's mantissa shifted 264 bits (a quotient of 204 bits or
/// more) by q, the remainder's sign as the sticky bit
fn rn_div(n: &Dy, q: u64) -> f64 {
    if n.is_zero() {
        return 0.0;
    }
    let sh = 264u64;
    let (quot, rem) = n.m.shl(sh).divrem_small(q);
    let v = round_to_f64(&quot, n.e - sh as i64, rem != 0);
    if n.neg {
        -v
    } else {
        v
    }
}

/// the reference: eight parts, each RN of the exact remainder
fn reference(p: i64, q: u64) -> [f64; 8] {
    let mut out = [0.0; 8];
    for i in 0..8 {
        let n = numerator(p, q, &out[..i]);
        out[i] = rn_div(&n, q);
        if out[i] == 0.0 {
            break;
        }
    }
    out
}

fn bits(x: &[f64]) -> Vec<u64> {
    x.iter().map(|v| v.to_bits()).collect()
}

/// Knuth's two-sum: RN(a + b) and the exact error
fn two_sum(a: f64, b: f64) -> [f64; 2] {
    let s = a + b;
    let bb = s - a;
    [s, (a - (s - bb)) + (b - bb)]
}

/// the k found below 2^60 whose greedy pair is a tie, its second part half an ulp of an odd first part
const TIES: [u64; 3] = [191516586041457763, 176007846257689259, 383033172082915526];

/// the cases: (p, q) pairs of k = 1..=5000, random q with p = 1, and random (p, q) of both signs
fn cases() -> Vec<(i64, u64)> {
    let mut r = Rng(1099);
    let mut v: Vec<(i64, u64)> = (1..=5000u64).map(|k| (1, k)).collect();
    for _ in 0..4000 {
        let b = 1 + r.next_u64() % 60;
        v.push((1, (r.next_u64() >> (64 - b)).max(1)));
    }
    for _ in 0..4000 {
        let pb = 1 + r.next_u64() % 63;
        let qb = 1 + r.next_u64() % 60;
        let p = (r.next_u64() >> (64 - pb)) as i64 * if r.next_u64() & 1 == 0 { 1 } else { -1 };
        v.push((p, (r.next_u64() >> (64 - qb)).max(1)));
    }
    v.extend([
        (1, (1u64 << 60) - 1),
        (i64::MAX, 3),
        (i64::MIN + 1, (1 << 59) + 1),
        (i64::MIN, 1),
        (i64::MIN, 3),
        (0, 7),
        (6, 3),
        (1, 1 << 40),
    ]);
    v.extend(TIES.map(|k| (1, k)));
    v
}

/// the number of cases whose parts, or the types' prefixes, differ from the reference in any bit
fn mismatches() -> usize {
    let mut bad = 0;
    for (p, q) in cases() {
        let want = reference(p, q);
        let got = if p == 1 { recip_parts(q) } else { ratio_parts(p, q) };
        let dd = if p == 1 { DD::recip_int(q) } else { DD::from_ratio(p, q) };
        let qd = if p == 1 { QD::recip_int(q) } else { QD::from_ratio(p, q) };
        let od = if p == 1 { OD::recip_int(q) } else { OD::from_ratio(p, q) };
        if bits(&got) != bits(&want)
            || bits(&[dd.hi, dd.lo]) != bits(&two_sum(want[0], want[1]))
            || bits(&qd.x) != bits(&want[..4])
            || bits(&od.x) != bits(&want)
        {
            bad += 1;
        }
    }
    bad
}

#[test]
fn ratios_against_exact_rationals() {
    let n = cases().len();
    let bad = mismatches();
    println!("ratio_parts and the types' prefixes against exact rationals: {bad} of {n} cases differ");
    assert_eq!(bad, 0);
    // the reference itself: the parts of an exact ratio end in zeros, and 1/3's first part is RN(1/3)
    assert_eq!(bits(&reference(6, 3)), bits(&[2.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]));
    assert_eq!(reference(1, 3)[0], 1.0 / 3.0);
}

/// the cases whose double-double constant is not a double word, hi = RN(hi + lo), or not of the greedy pair's value
fn dd_not_double_words() -> usize {
    let exact = |a: f64, b: f64| Dy::from_f64(a).add(&Dy::from_f64(b));
    let mut bad = 0;
    for (p, q) in cases() {
        let want = reference(p, q);
        let dd = if p == 1 { DD::recip_int(q) } else { DD::from_ratio(p, q) };
        if dd.hi + dd.lo != dd.hi || !exact(dd.hi, dd.lo).sub(&exact(want[0], want[1])).is_zero() {
            bad += 1;
        }
    }
    bad
}

#[test]
fn dd_constants_are_double_words() {
    // the ties are ties: the greedy pair's sum rounds away from its first part
    for k in TIES {
        let want = reference(1, k);
        assert_ne!(want[0] + want[1], want[0], "k = {k}: the greedy pair is no tie");
    }
    let bad = dd_not_double_words();
    println!(
        "double-double constants: {bad} of {} cases not a double word of the greedy value",
        cases().len()
    );
    assert_eq!(bad, 0);
}

#[cfg(feature = "mutate")]
#[test]
fn dd_double_words_control() {
    use multidouble::recip::mutate;
    mutate::set(mutate::DD_GREEDY);
    let bad = dd_not_double_words();
    mutate::set(0);
    println!("control, a double-double's parts without the two-sum: {bad} cases not a double word (must be the ties)");
    assert_eq!(bad, TIES.len(), "the control did not fire on exactly the ties");
}

#[cfg(feature = "mutate")]
#[test]
fn ratios_control_last_ulp() {
    use multidouble::recip::mutate;
    mutate::set(mutate::LAST_ULP);
    let bad = mismatches();
    mutate::set(0);
    let n = cases().len();
    println!("control, the types' last part one ulp up: {bad} of {n} cases differ (must be all)");
    assert_eq!(bad, n, "the one-ulp control did not fire on every case");
}

/// choptuik-large-d's `recip_parts` (hp/src/model.rs at wip/large-d-form-s 33eeff5c), copied as the reference
fn hp_recip_parts(k: u64) -> [f64; 8] {
    fn pow2(e: i64) -> f64 {
        assert!((-1022..=1023).contains(&e), "pow2: 2^{e} is not a normal f64");
        f64::from_bits(((e + 1023) as u64) << 52)
    }
    assert!((1..1u64 << 60).contains(&k), "recip_parts: k = {k}");
    let d = k as u128;
    let kb = 128 - d.leading_zeros() as i64;
    let mut out = [0.0; 8];
    let (mut n, mut neg, mut e) = (1u128, false, 0i64);
    for r in out.iter_mut() {
        if n == 0 {
            break;
        }
        let mut s = 52 - ((128 - n.leading_zeros() as i64) - kb);
        let mut a = n << s;
        if a / d < 1 << 52 {
            s += 1;
            a <<= 1;
        }
        let q0 = a / d;
        let rem = a - q0 * d;
        let q = q0 + (2 * rem > d || (2 * rem == d && q0 & 1 == 1)) as u128;
        let m = q as f64 * pow2(-(e + s));
        *r = if neg { -m } else { m };
        let rr = a as i128 - (q * d) as i128;
        neg ^= rr < 0;
        n = rr.unsigned_abs();
        e += s;
    }
    out
}

/// hp's `recip_lane` on the quad- and octo-double lanes: the parts' pairs splat as double-doubles and added in the
/// lane's arithmetic
fn hp_recip_lane_qv(r: &[f64; 8]) -> QV {
    let dd = |i: usize| QV::from_dv(multidouble::native::DV::splat(DD { hi: r[i], lo: r[i + 1] }));
    dd(0) + dd(2)
}
fn hp_recip_lane_ov(r: &[f64; 8]) -> OV {
    let dd = |i: usize| OV::from_dv(multidouble::native::DV::splat(DD { hi: r[i], lo: r[i + 1] }));
    ((dd(0) + dd(2)) + dd(4)) + dd(6)
}

#[test]
fn recip_matches_hp_to_2_20() {
    let (mut parts, mut qv, mut ov) = (0, 0, 0);
    for k in 1..=(1u64 << 20) {
        let r = recip_parts(k);
        if bits(&r) != bits(&hp_recip_parts(k)) {
            parts += 1;
        }
        let lane_bits = |c: &[multidouble::native::V8]| -> Vec<u64> {
            c.iter().flat_map(|v| v.to_array().map(f64::to_bits)).collect()
        };
        if lane_bits(&QV::recip_int(k).c) != lane_bits(&hp_recip_lane_qv(&r).c) {
            qv += 1;
        }
        if lane_bits(&OV::recip_int(k).c) != lane_bits(&hp_recip_lane_ov(&r).c) {
            ov += 1;
        }
    }
    println!("k = 1..=2^20 against hp: parts {parts}, QV constants {qv}, OV constants {ov} differ");
    assert_eq!((parts, qv, ov), (0, 0, 0));
}

/// (x k) times 1/k is x to the type's rounding: within 8 u^2, 64 u^4 and 1024 u^8 of |x| (DD, QD, OD) for random x
/// and k < 2^30
#[test]
fn mul_recip_inverts_multiplication() {
    let mut r = Rng(7);
    let mut worst = [0.0f64; 3];
    for _ in 0..3000 {
        let k = 1 + r.next_u64() % (1 << 30);
        let x = r.dd(20);
        let kd = DD::from_f64(k as f64);
        let e = [
            ((x * kd).mul_recip(k) - x).hi.abs() / x.hi.abs(),
            ((QD::from_dd(x) * QD::from_f64(k as f64)).mul_recip(k) - QD::from_dd(x)).x[0].abs() / x.hi.abs(),
            ((OD::from_dd(x) * OD::from_f64(k as f64)).mul_recip(k) - OD::from_dd(x)).x[0].abs() / x.hi.abs(),
        ];
        for i in 0..3 {
            // a NaN would be dropped by max: every error must be finite
            assert!(e[i].is_finite(), "type {i}: k {k}, error {}", e[i]);
            worst[i] = worst[i].max(e[i]);
        }
    }
    let u = [2f64.powi(-106), 2f64.powi(-212), 2f64.powi(-424)];
    let bar = [8.0, 64.0, 1024.0];
    println!(
        "(x k)/k - x relative: DD {:.2e} ({:.2} u^2), QD {:.2e}, OD {:.2e}",
        worst[0],
        worst[0] / u[0],
        worst[1],
        worst[2]
    );
    for i in 0..3 {
        assert!(worst[i] <= bar[i] * u[i], "type {i}: {:.2e}", worst[i]);
    }
}
