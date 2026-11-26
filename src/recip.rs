//! Correctly rounded ratios of integers: p/q as the greedy round-to-nearest expansion of up to eight f64 parts,
//! r_0 = RN(p/q) and r_i = RN(p/q - r_0 - ... - r_(i-1)), each part rounded once from the exact remainder by integer
//! arithmetic in u128 ([`ratio_parts`], [`recip_parts`]). A prefix of P parts is then the expansion of P parts in the
//! form the double-, quad- and octo-double types keep (each part at most half the ulp of the one before, zeros only at
//! the end), so `DD::recip_int(k)`, `QD::recip_int(k)` and `OD::recip_int(k)` are 1/k rounded to their precision, and
//! `from_ratio(p, q)` the same for p/q. The lanes' `recip_int` splat them and `mul_recip(k)` multiplies by them.
//!
//! The quotient in the type's arithmetic is not the same constant. `DD::ONE / DD::from_f64(k as f64)` errs by a few
//! units of 2^-106, and once widened to a quad- or octo-double it keeps that error, 2^-106 relative, far above
//! their rounding: a series whose order k is divided by k in octo-double then carries 1e-32 relative errors. These
//! constants are exact to the last part's rounding in every precision.
use crate::dd::DD;
use crate::dv::DV;
use crate::od::OD;
use crate::ov::OV;
use crate::qd::QD;
use crate::qv::QV;
use crate::simd::Simd;

/// Deliberate breakage of the reciprocals for the controls of the tests (feature `mutate`).
pub mod mutate {
    /// the last part of a type's constant one ulp up (part 1 of a double-double, 3 of a quad-double, 7 of an
    /// octo-double), where `recip_int` and `from_ratio` take their prefix
    pub const LAST_ULP: u32 = 1;
    /// number of ids
    pub const N: u32 = 1;
    /// the mutations' descriptions, by id
    pub const NAMES: [&str; 2] = ["none", "reciprocals: the last part one ulp up"];

    #[cfg(feature = "mutate")]
    thread_local!(static ID: std::cell::Cell<u32> = const { std::cell::Cell::new(0) });

    /// select the mutation for the current thread (0 = none)
    #[cfg(feature = "mutate")]
    pub fn set(id: u32) {
        ID.with(|m| m.set(id));
    }

    /// whether mutation id is selected in the current thread
    #[cfg(feature = "mutate")]
    #[inline(always)]
    pub fn on(id: u32) -> bool {
        ID.with(|m| m.get() == id)
    }

    /// whether mutation id is selected: never, without the feature `mutate`
    #[cfg(not(feature = "mutate"))]
    #[inline(always)]
    pub fn on(_id: u32) -> bool {
        false
    }
}

/// 2^e for e in the normal range, exactly
fn pow2(e: i64) -> f64 {
    assert!((-1022..=1023).contains(&e), "recip: 2^{e} is not a normal f64");
    f64::from_bits(((e + 1023) as u64) << 52)
}

/// p/q in eight parts by greedy round-to-nearest (ties to even), for any p and 1 <= q < 2^60 (it panics otherwise). The
/// value left is (-1)^neg n / (q 2^e) with n an integer; each part is RN(n 2^s / q) 2^-(e + s) for the s that puts n
/// 2^s / q in [2^52, 2^53), formed by one u128 division, and n becomes the exact remainder. After the first part |n| <=
/// q / 2. The parts after an exact ratio are zero.
pub fn ratio_parts(p: i64, q: u64) -> [f64; 8] {
    assert!((1..1u64 << 60).contains(&q), "ratio_parts: q = {q}, not in [1, 2^60)");
    let d = q as u128;
    let qb = 128 - d.leading_zeros() as i64;
    let mut out = [0.0; 8];
    let (mut n, mut neg, mut e) = (p.unsigned_abs() as u128, p < 0, 0i64);
    for r in out.iter_mut() {
        if n == 0 {
            break;
        }
        // n 2^s / q in [2^52, 2^53): for s >= 0 the dividend n 2^s (below 2^114), for s < 0 (a first part above
        // 2^53) the divisor q 2^-s (below 2^71)
        let split = |s: i64| if s >= 0 { (n << s, d) } else { (n, d << -s) };
        let mut s = 52 - ((128 - n.leading_zeros() as i64) - qb);
        let (mut a, mut dv) = split(s);
        if a / dv < 1 << 52 {
            s += 1;
            (a, dv) = split(s);
        }
        let q0 = a / dv;
        let rem = a - q0 * dv;
        let qr = q0 + (2 * rem > dv || (2 * rem == dv && q0 & 1 == 1)) as u128;
        let m = qr as f64 * pow2(-(e + s));
        *r = if neg { -m } else { m };
        // the remainder (a - qr dv) / (q 2^(e + max(s, 0))), of either sign
        let rr = a as i128 - (qr * dv) as i128;
        neg ^= rr < 0;
        n = rr.unsigned_abs();
        e += s.max(0);
    }
    out
}

/// 1/k in eight parts by greedy round-to-nearest (`ratio_parts(1, k)`), for 1 <= k < 2^60 (it panics otherwise)
pub fn recip_parts(k: u64) -> [f64; 8] {
    ratio_parts(1, k)
}

/// the first P parts, the last one ulp up under the control `mutate::LAST_ULP`
#[inline]
fn prefix<const P: usize>(r: [f64; 8]) -> [f64; P] {
    let mut x: [f64; P] = std::array::from_fn(|i| r[i]);
    if mutate::on(mutate::LAST_ULP) {
        x[P - 1] = x[P - 1].next_up();
    }
    x
}

impl DD {
    /// 1/k rounded to the nearest double-double (`recip_parts`'s first two parts)
    ///
    /// # Panics
    ///
    /// Unless 1 <= k < 2^60.
    pub fn recip_int(k: u64) -> DD {
        let [hi, lo] = prefix::<2>(recip_parts(k));
        DD { hi, lo }
    }
    /// p/q rounded to the nearest double-double (`ratio_parts`'s first two parts), for any p
    ///
    /// # Panics
    ///
    /// Unless 1 <= q < 2^60.
    pub fn from_ratio(p: i64, q: u64) -> DD {
        let [hi, lo] = prefix::<2>(ratio_parts(p, q));
        DD { hi, lo }
    }
    /// self times `DD::recip_int(k)`
    pub fn mul_recip(self, k: u64) -> DD {
        self * DD::recip_int(k)
    }
}

impl QD {
    /// 1/k rounded to four parts (`recip_parts`'s first four)
    ///
    /// # Panics
    ///
    /// Unless 1 <= k < 2^60.
    pub fn recip_int(k: u64) -> QD {
        QD {
            x: prefix::<4>(recip_parts(k)),
        }
    }
    /// p/q rounded to four parts (`ratio_parts`'s first four), for any p
    ///
    /// # Panics
    ///
    /// Unless 1 <= q < 2^60.
    pub fn from_ratio(p: i64, q: u64) -> QD {
        QD {
            x: prefix::<4>(ratio_parts(p, q)),
        }
    }
    /// self times `QD::recip_int(k)`
    pub fn mul_recip(self, k: u64) -> QD {
        self * QD::recip_int(k)
    }
}

impl OD {
    /// 1/k rounded to eight parts (`recip_parts`)
    ///
    /// # Panics
    ///
    /// Unless 1 <= k < 2^60.
    pub fn recip_int(k: u64) -> OD {
        OD {
            x: prefix::<8>(recip_parts(k)),
        }
    }
    /// p/q rounded to eight parts (`ratio_parts`), for any p
    ///
    /// # Panics
    ///
    /// Unless 1 <= q < 2^60.
    pub fn from_ratio(p: i64, q: u64) -> OD {
        OD {
            x: prefix::<8>(ratio_parts(p, q)),
        }
    }
    /// self times `OD::recip_int(k)`
    pub fn mul_recip(self, k: u64) -> OD {
        self * OD::recip_int(k)
    }
}

impl<S: Simd> DV<S> {
    /// `DD::recip_int(k)` on every lane
    pub fn recip_int(k: u64) -> Self {
        DV::splat(DD::recip_int(k))
    }
    /// self times `DD::recip_int(k)` on every lane
    pub fn mul_recip(self, k: u64) -> Self {
        self * DV::recip_int(k)
    }
}

impl<S: Simd> QV<S> {
    /// `QD::recip_int(k)` on every lane
    pub fn recip_int(k: u64) -> Self {
        QV::splat(QD::recip_int(k))
    }
    /// self times `QD::recip_int(k)` on every lane
    pub fn mul_recip(self, k: u64) -> Self {
        self * QV::recip_int(k)
    }
}

impl<S: Simd> OV<S> {
    /// `OD::recip_int(k)` on every lane
    pub fn recip_int(k: u64) -> Self {
        OV::splat(OD::recip_int(k))
    }
    /// self times `OD::recip_int(k)` on every lane
    pub fn mul_recip(self, k: u64) -> Self {
        self * OV::recip_int(k)
    }
}
