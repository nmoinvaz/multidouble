//! Sine, cosine and tangent of double-doubles, quad-doubles and octo-doubles (`DD`, `QD`, `OD`): `sin`, `cos`, `tan`
//! and `sin_cos`, written once over the type's arithmetic.
//!
//! * Reduction: x = k pi/2 + r with |r| <= 0.7854 (1 + 2^-52), to pi/2's 1216 fraction bits. k = round(x_0 RN(2/pi)),
//!   and for k = 0 r is x itself.
//!   Otherwise the parts of x are added into a two's-complement fixed-point accumulator of 1280 bits whose unit is
//!   2^-1216 (every finite f64 below 2^53 is a multiple of 2^-1074, so the sum is exact), and k round(pi/2 2^1216) is
//!   subtracted from it. If the remainder's leading part is past 0.7854, which happens only for |x| above 2^31, k is
//!   corrected once from it. The remainder is rounded to n parts greedily (r_0 = RN(rem), r_1 = RN(rem - r_0), ...),
//!   so that r is within u^n |rem| of rem (u = 2^-53) and |r_(i+1)| <= ulp(r_i)/2. The only other error of the
//!   reduction is that of pi/2's 1216 fraction bits, at most |k| 2^-1217, below 2^-1165 for |x| <= 2^52. So r is
//!   accurate relative to itself also next to the multiples of pi/2, wherever the result has full precision.
//! * Evaluation: Taylor series of sin r and cos r in z = r^2 by Horner's scheme, with the type's own products and
//!   sums, as sin r = r + r (z P(z)) and cos r = 1 + z Q(z). The number of terms depends on the binary exponent of
//!   r_0 (the tables in `tables`, from `scripts/trig_tables.py`), so that the series' truncation is at most
//!   2^-10 u^n relative. Below 2^-(53n/2), r and 1 are returned, within u^n/6 and u^n/2.
//! * Recombination by k mod 4, and tan r = sin r / cos r, or -cos r / sin r for odd k.
//!
//! The double-double functions use only double-word algorithms with published error bounds: the product DWTimesDW3,
//! Algorithm 12 of J. Joldes, J.-M. Muller, V. Popescu, "Tight and rigorous error bounds for basic building blocks of
//! double-word arithmetic", ACM Trans. Math. Softw. 44(2), 2017, doi:10.1145/3121432, within (4u^2 + u^3/2)/(1+u)^2
//! by Theorem 2.8 of J.-M. Muller, L. Rideau, ACM Trans. Math. Softw. 48(1), 2022, doi:10.1145/3484514 (`DD`'s `*` is
//! another variant, without a published bound); their AccurateDWPlusDW, `DD`'s `+` (Algorithm 6, 3u^2/(1 - 4u));
//! their DWPlusFP for 1 + t (Algorithm 4, 2u^2); and their DWDivDW2 for the tangent's quotient, `DD::fast_div`
//! (Algorithm 17, 15u^2 + 56u^3). The quad-double functions use QD's operators, and the octo-double ones the
//! octo-double operators, whose bounds the paper proves.
//!
//! Relative errors, for |x_0| <= 2^52 and barring underflow, with an absolute 2^-1163 aside (relative to
//! |sin x cos x| for tan) from pi/2's fraction bits:
//!
//! | | `DD` | `QD` | `OD` |
//! |---|---|---|---|
//! | sin, cos | 7.85 u^2, proven | 32 u^4, tested | 3.17 u^8, proven |
//! | tan | 28.5 u^2, proven | 64 u^4, tested | 6.42 u^8, proven |
//!
//! The proven bounds are those of the paper (paper/expansion-error-bounds.pdf, the appendix on the trigonometric
//! functions, constants from `paper/trig_consts.py`), rounded up; the tests check them against exact arithmetic
//! (`trig_tests`). NaN and the infinities give NaN, a zero gives itself for `sin` and `tan` and one for `cos`, and
//! |x_0| > 2^52 gives NaN: the reduction of larger arguments (M. H. Payne, R. N. Hanek, "Radian reduction for
//! trigonometric functions", ACM SIGNUM Newsletter 18(1), 1983) is not implemented.
//!
//! With the cargo feature `mutate`, `mutate::set(id)` breaks one step on purpose in the current thread, for the
//! controls of the accuracy tests; without it the hooks are compile-time `false`.
use crate::dd::{quick_two_sum, two_prod, two_sum, DD};
use crate::od::OD;
use crate::qd::QD;
use std::ops::Neg;

#[rustfmt::skip]
pub(crate) mod tables;

/// Deliberate breakage for the controls (feature `mutate`; ids below, 0 = none).
pub mod mutate {
    /// reduction: the reduced argument's last part dropped
    pub const REDUCE_TAIL: u32 = 1;
    /// reduction: pi/2 cut to its leading 64 (n + 1) + 1 bits, about what an (n + 1)-part constant holds
    pub const REDUCE_PI_SHORT: u32 = 2;
    /// sin r: two terms fewer than the table's (two at least)
    pub const SIN_SHORT: u32 = 3;
    /// cos r: two terms fewer than the table's (two at least)
    pub const COS_SHORT: u32 = 4;
    /// tan: the divisor's last part dropped
    pub const TAN_DIV_SHORT: u32 = 5;
    /// number of ids
    pub const N: u32 = 5;
    /// the mutations' descriptions, by id
    pub const NAMES: [&str; 6] = [
        "none",
        "reduction: last part of r dropped",
        "reduction: pi/2 cut to 64 (n + 1) + 1 bits",
        "sin r: two terms fewer",
        "cos r: two terms fewer",
        "tan: divisor's last part dropped",
    ];

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

/// |x_0| above this gives NaN
pub const LIMIT: f64 = f64::from_bits((1023 + 52) << 52); // 2^52
/// the reduction corrects k once when |r_0| exceeds this, so that |r| <= 0.7854 (1 + 2^-52): RN(0.7854), above pi/4
#[allow(clippy::approx_constant)]
const R_TH: f64 = 0.7854;
/// limbs of the accumulator: 1280 bits, F = 1216 of them below the binary point
const L: usize = 20;

// ---------------------------------------------------------------------------------------------------------------
// the reduction, in integer arithmetic
// ---------------------------------------------------------------------------------------------------------------

/// A signed fixed-point number, two's complement over L little-endian limbs, of value (limbs) 2^-F.
#[derive(Clone, Copy)]
struct Acc([u64; L]);

impl Acc {
    /// += v 2^(64 w), v < 2^127, modulo 2^(64 L)
    #[inline(always)]
    fn add_at(&mut self, w: usize, v: u128) {
        let mut c = v;
        let mut i = w;
        while c != 0 && i < L {
            let t = self.0[i] as u128 + (c as u64) as u128;
            self.0[i] = t as u64;
            c = (c >> 64) + (t >> 64);
            i += 1;
        }
    }

    /// -= v 2^(64 w), v < 2^127, modulo 2^(64 L)
    #[inline(always)]
    fn sub_at(&mut self, w: usize, v: u128) {
        let mut c = v;
        let mut i = w;
        while c != 0 && i < L {
            let (s, b) = self.0[i].overflowing_sub(c as u64);
            self.0[i] = s;
            c = (c >> 64) + b as u128;
            i += 1;
        }
    }

    /// += x, exactly, for a finite x with |x| < 2^53
    #[inline(always)]
    fn add_f64(&mut self, x: f64) {
        if x == 0.0 {
            return;
        }
        let b = x.to_bits();
        let e = ((b >> 52) & 0x7ff) as i32;
        let frac = b & ((1u64 << 52) - 1);
        // x = m 2^ex with m < 2^53
        let (m, ex) = if e == 0 {
            (frac, -1074)
        } else {
            (frac | (1u64 << 52), e - 1075)
        };
        let pos = (ex + tables::F as i32) as u32;
        let v = (m as u128) << (pos % 64);
        if b >> 63 == 0 {
            self.add_at((pos / 64) as usize, v);
        } else {
            self.sub_at((pos / 64) as usize, v);
        }
    }

    /// -= k P, P = round(pi/2 2^F); |k| < 2^53. `n` parts set the cut of `mutate::REDUCE_PI_SHORT`.
    #[inline(always)]
    fn sub_kp(&mut self, k: i64, n: usize) {
        if k == 0 {
            return;
        }
        let a = k.unsigned_abs() as u128;
        // limbs below `cut` are zero in the mutation: pi/2 to its leading 64 (n + 1) + 1 bits
        let cut = if mutate::on(mutate::REDUCE_PI_SHORT) {
            L - 1 - (n + 1)
        } else {
            0
        };
        let mut mc: u128 = 0;
        let mut bc = false;
        for i in 0..L {
            let p = if i < cut { 0 } else { tables::P[i] };
            let t = a * p as u128 + mc;
            let pl = t as u64;
            mc = t >> 64;
            if k > 0 {
                let (s1, b1) = self.0[i].overflowing_sub(pl);
                let (s2, b2) = s1.overflowing_sub(bc as u64);
                self.0[i] = s2;
                bc = b1 | b2;
            } else {
                let (s1, c1) = self.0[i].overflowing_add(pl);
                let (s2, c2) = s1.overflowing_add(bc as u64);
                self.0[i] = s2;
                bc = c1 | c2;
            }
        }
    }

    /// the value rounded to the nearest f64, ties to even (subnormals included; |value| < 2^54)
    fn round(&self) -> f64 {
        let neg = self.0[L - 1] >> 63 == 1;
        let mut m = self.0;
        if neg {
            // two's complement negation
            let mut c = true;
            for v in m.iter_mut() {
                let (s, o) = (!*v).overflowing_add(c as u64);
                *v = s;
                c = o;
            }
        }
        let Some(top) = m.iter().rposition(|&v| v != 0) else {
            return 0.0;
        };
        // bit index of the leading one, and of the last bit kept: 53 bits, or down to 2^-1074 for a subnormal
        let h = 64 * top + 63 - m[top].leading_zeros() as usize;
        let sub = tables::F as usize - 1074;
        let lsb = if h >= sub + 52 { h - 52 } else { sub };
        // the 54 bits from lsb - 1 up, from two limbs: the 53 kept and the rounding bit; the bits above h are zero
        let (w, s) = ((lsb - 1) / 64, (lsb - 1) % 64);
        let win = if s > 0 && w + 1 < L {
            (m[w] >> s) | (m[w + 1] << (64 - s))
        } else {
            m[w] >> s
        };
        let (mut mant, half) = (win >> 1, win & 1 == 1);
        let sticky = m[w] & ((1u64 << s) - 1) != 0 || m[..w].iter().any(|&v| v != 0);
        if half && (sticky || mant & 1 == 1) {
            mant += 1;
        }
        // value mant 2^(lsb - F); a carry to 2^53 moves the exponent up
        let mut be = lsb as i64 - tables::F as i64 + 1075;
        if mant == 1u64 << 53 {
            mant = 1u64 << 52;
            be += 1;
        }
        let bits = if mant < 1u64 << 52 {
            mant
        } else {
            ((be as u64) << 52) | (mant & ((1u64 << 52) - 1))
        };
        let v = f64::from_bits(bits);
        if neg {
            -v
        } else {
            v
        }
    }

    /// the value rounded greedily to N parts: x_0 = RN(v), x_1 = RN(v - x_0), ...
    fn greedy<const N: usize>(mut self) -> [f64; N] {
        let mut x = [0.0; N];
        for xi in x.iter_mut() {
            let v = self.round();
            if v == 0.0 {
                break;
            }
            *xi = v;
            self.add_f64(-v);
        }
        if mutate::on(mutate::REDUCE_TAIL) {
            x[N - 1] = 0.0;
        }
        x
    }
}

/// x = k pi/2 + r for finite parts x with |x_0| <= 2^52: (k mod 4, r), |r| <= 0.7854 (1 + 2^-52); r = x for k = 0,
/// otherwise N greedy parts
pub(crate) fn reduce<const N: usize>(x: &[f64; N]) -> (u32, [f64; N]) {
    let mut k = (x[0] * tables::TWO_OVER_PI).round();
    if k == 0.0 {
        // |x_0| < 0.78539817: r = x, exactly
        return (0, *x);
    }
    let mut acc = Acc([0; L]);
    for &v in x {
        acc.add_f64(v);
    }
    acc.sub_kp(k as i64, N);
    let r0 = acc.round();
    if r0.abs() > R_TH {
        let k2 = (r0 * tables::TWO_OVER_PI).round();
        acc.sub_kp(k2 as i64, N);
        k += k2;
    }
    ((k as i64).rem_euclid(4) as u32, acc.greedy::<N>())
}

// ---------------------------------------------------------------------------------------------------------------
// the evaluation, once for the three types
// ---------------------------------------------------------------------------------------------------------------

/// the arithmetic the functions need, by type
trait Ext: Copy + Neg<Output = Self> {
    /// 2^-(53 n / 2), n the number of parts: below it sin r = r and cos r = 1 to within u^N/6 and u^N/2
    const TINY: f64;
    /// terms of the sin and cos series by bucket of r_0
    const KS: &'static [u8];
    const KC: &'static [u8];
    fn lead(self) -> f64;
    fn finite(self) -> bool;
    /// the N leading parts of an eight-part table entry
    fn coef(c: &[f64; 8]) -> Self;
    fn one() -> Self;
    fn nan() -> Self;
    fn mul(self, b: Self) -> Self;
    fn add(self, b: Self) -> Self;
    /// 1 + self
    fn one_plus(self) -> Self;
    fn div(self, b: Self) -> Self;
    /// x = k pi/2 + r: (k mod 4, r)
    fn reduce(self) -> (u32, Self);
    /// the last part dropped (`mutate::TAN_DIV_SHORT`)
    fn drop_last(self) -> Self;
}

/// the bucket of |r_0| in [TINY, 0.7854]: j with 2^-(j+1) <= |r_0| < 2^-j (0 for [0.5, 0.7854])
#[inline(always)]
fn bucket(r0: f64) -> usize {
    (1022 - ((r0.to_bits() >> 52) & 0x7ff) as i64) as usize
}

/// the Horner sum c_(k-1) z^(k-2) + ... + c_1 of a table with k >= 2 terms
#[inline(always)]
fn horner<T: Ext>(z: T, c: &[[f64; 8]], k: usize) -> T {
    let mut p = T::coef(&c[k - 1]);
    for i in (1..k - 1).rev() {
        p = z.mul(p).add(T::coef(&c[i]));
    }
    p
}

/// terms for bucket j, two fewer (two at least) with the mutation
#[inline(always)]
fn terms(t: &[u8], j: usize, short: u32) -> usize {
    let k = t[j] as usize;
    if mutate::on(short) {
        k.saturating_sub(2).max(2)
    } else {
        k
    }
}

/// sin r for |r| <= 0.7854 (1 + 2^-52), z = r^2 as computed: r + r (z P(z)), or r when r is tiny
#[inline(always)]
fn sin_r<T: Ext>(r: T, z: T) -> T {
    let r0 = r.lead().abs();
    if r0 < T::TINY {
        return r;
    }
    let k = terms(T::KS, bucket(r0), mutate::SIN_SHORT);
    let p = horner(z, &tables::SIN, k);
    r.add(r.mul(z.mul(p)))
}

/// cos r for |r| <= 0.7854 (1 + 2^-52), z = r^2 as computed: 1 + z Q(z), or 1 when r is tiny
#[inline(always)]
fn cos_r<T: Ext>(r: T, z: T) -> T {
    let r0 = r.lead().abs();
    if r0 < T::TINY {
        return T::one();
    }
    let k = terms(T::KC, bucket(r0), mutate::COS_SHORT);
    let q = horner(z, &tables::COS, k);
    z.mul(q).one_plus()
}

/// what to return before the reduction: NaN for NaN, infinities and |x_0| > 2^52, x itself (sin, tan) or one (cos)
/// below 2^-(53n/2), and None otherwise
#[inline(always)]
fn early<T: Ext>(x: T, cos: bool) -> Option<T> {
    let a = x.lead().abs();
    if !x.finite() || a > LIMIT {
        Some(T::nan())
    } else if a < T::TINY {
        Some(if cos { T::one() } else { x })
    } else {
        None
    }
}

fn sin<T: Ext>(x: T) -> T {
    if let Some(v) = early(x, false) {
        return v;
    }
    let (q, r) = x.reduce();
    let z = r.mul(r);
    match q {
        0 => sin_r(r, z),
        1 => cos_r(r, z),
        2 => -sin_r(r, z),
        _ => -cos_r(r, z),
    }
}

fn cos<T: Ext>(x: T) -> T {
    if let Some(v) = early(x, true) {
        return v;
    }
    let (q, r) = x.reduce();
    let z = r.mul(r);
    match q {
        0 => cos_r(r, z),
        1 => -sin_r(r, z),
        2 => -cos_r(r, z),
        _ => sin_r(r, z),
    }
}

fn sin_cos<T: Ext>(x: T) -> (T, T) {
    if let Some(v) = early(x, false) {
        return (v, early(x, true).unwrap());
    }
    let (q, r) = x.reduce();
    let z = r.mul(r);
    let (s, c) = (sin_r(r, z), cos_r(r, z));
    match q {
        0 => (s, c),
        1 => (c, -s),
        2 => (-s, -c),
        _ => (-c, s),
    }
}

fn tan<T: Ext>(x: T) -> T {
    if let Some(v) = early(x, false) {
        return v;
    }
    let (q, r) = x.reduce();
    let z = r.mul(r);
    let (s, c) = (sin_r(r, z), cos_r(r, z));
    let short = |d: T| {
        if mutate::on(mutate::TAN_DIV_SHORT) {
            d.drop_last()
        } else {
            d
        }
    };
    if q % 2 == 0 {
        s.div(short(c))
    } else {
        -c.div(short(s))
    }
}

// ---------------------------------------------------------------------------------------------------------------
// the three types
// ---------------------------------------------------------------------------------------------------------------

/// DWTimesDW3, Algorithm 12 of Joldes, Muller and Popescu (2017): within (4u^2 + u^3/2)/(1+u)^2 relative (Muller and
/// Rideau 2022, Theorem 2.8)
#[inline(always)]
fn dw_times_dw3(x: DD, y: DD) -> DD {
    let (ch, cl1) = two_prod(x.hi, y.hi);
    let tl0 = x.lo * y.lo;
    let tl1 = x.hi.mul_add(y.lo, tl0);
    let cl2 = x.lo.mul_add(y.hi, tl1);
    let cl3 = cl1 + cl2;
    let (h, l) = quick_two_sum(ch, cl3);
    DD { hi: h, lo: l }
}

/// DWPlusFP, Algorithm 4 of Joldes, Muller and Popescu (2017): within 2u^2 relative (their Theorem 2.2)
#[inline(always)]
fn dw_plus_fp(x: DD, y: f64) -> DD {
    let (sh, sl) = two_sum(x.hi, y);
    let v = x.lo + sl;
    let (h, l) = quick_two_sum(sh, v);
    DD { hi: h, lo: l }
}

impl Ext for DD {
    const TINY: f64 = f64::from_bits((1023 - 53) << 52); // 2^-53
    const KS: &'static [u8] = &tables::KS2;
    const KC: &'static [u8] = &tables::KC2;
    fn lead(self) -> f64 {
        self.hi
    }
    fn finite(self) -> bool {
        self.hi.is_finite() && self.lo.is_finite()
    }
    fn coef(c: &[f64; 8]) -> DD {
        DD { hi: c[0], lo: c[1] }
    }
    fn one() -> DD {
        DD::ONE
    }
    fn nan() -> DD {
        DD::from_f64(f64::NAN)
    }
    fn mul(self, b: DD) -> DD {
        dw_times_dw3(self, b)
    }
    fn add(self, b: DD) -> DD {
        self + b
    }
    fn one_plus(self) -> DD {
        dw_plus_fp(self, 1.0)
    }
    fn div(self, b: DD) -> DD {
        self.fast_div(b)
    }
    fn reduce(self) -> (u32, DD) {
        let (q, r) = reduce(&[self.hi, self.lo]);
        (q, DD { hi: r[0], lo: r[1] })
    }
    fn drop_last(self) -> DD {
        DD::from_f64(self.hi)
    }
}

impl Ext for QD {
    const TINY: f64 = f64::from_bits((1023 - 106) << 52); // 2^-106
    const KS: &'static [u8] = &tables::KS4;
    const KC: &'static [u8] = &tables::KC4;
    fn lead(self) -> f64 {
        self.x[0]
    }
    fn finite(self) -> bool {
        self.x.iter().all(|v| v.is_finite())
    }
    fn coef(c: &[f64; 8]) -> QD {
        QD {
            x: [c[0], c[1], c[2], c[3]],
        }
    }
    fn one() -> QD {
        QD::ONE
    }
    fn nan() -> QD {
        QD::from_f64(f64::NAN)
    }
    fn mul(self, b: QD) -> QD {
        self * b
    }
    fn add(self, b: QD) -> QD {
        self + b
    }
    fn one_plus(self) -> QD {
        self.add_f(1.0)
    }
    fn div(self, b: QD) -> QD {
        self / b
    }
    fn reduce(self) -> (u32, QD) {
        let (q, x) = reduce(&self.x);
        (q, QD { x })
    }
    fn drop_last(self) -> QD {
        QD {
            x: [self.x[0], self.x[1], self.x[2], 0.0],
        }
    }
}

impl Ext for OD {
    const TINY: f64 = f64::from_bits((1023 - 212) << 52); // 2^-212
    const KS: &'static [u8] = &tables::KS8;
    const KC: &'static [u8] = &tables::KC8;
    fn lead(self) -> f64 {
        self.x[0]
    }
    fn finite(self) -> bool {
        self.x.iter().all(|v| v.is_finite())
    }
    fn coef(c: &[f64; 8]) -> OD {
        OD { x: *c }
    }
    fn one() -> OD {
        OD::ONE
    }
    fn nan() -> OD {
        OD::from_f64(f64::NAN)
    }
    fn mul(self, b: OD) -> OD {
        self * b
    }
    fn add(self, b: OD) -> OD {
        self + b
    }
    fn one_plus(self) -> OD {
        self.add_f(1.0)
    }
    fn div(self, b: OD) -> OD {
        self / b
    }
    fn reduce(self) -> (u32, OD) {
        let (q, x) = reduce(&self.x);
        (q, OD { x })
    }
    fn drop_last(self) -> OD {
        let mut x = self.x;
        x[7] = 0.0;
        OD { x }
    }
}

macro_rules! trig_methods {
    ($t:ty, $sc:literal, $tan:literal) => {
        impl $t {
            #[doc = concat!("sin x, within ", $sc, " relative for |x_0| <= 2^52 barring underflow: a reduction ",
                "by pi/2 to 1216 fraction bits in exact integer arithmetic, and a Taylor series (see `trig`). NaN ",
                "for NaN, the infinities and |x_0| > 2^52; a zero gives itself.")]
            pub fn sin(self) -> $t {
                sin(self)
            }
            #[doc = concat!("cos x, within ", $sc, " relative, as `sin`; one for a zero.")]
            pub fn cos(self) -> $t {
                cos(self)
            }
            #[doc = concat!("tan x = sin x / cos x from one reduction, within ", $tan, " relative, as `sin`; a zero ",
                "gives itself.")]
            pub fn tan(self) -> $t {
                tan(self)
            }
            /// (sin x, cos x) from one reduction, bitwise `(self.sin(), self.cos())`
            pub fn sin_cos(self) -> ($t, $t) {
                sin_cos(self)
            }
        }
    };
}

trig_methods!(DD, "7.85 u^2 (u = 2^-53, proven)", "28.5 u^2 (proven)");
trig_methods!(QD, "32 u^4 (u = 2^-53, tested)", "64 u^4 (tested)");
trig_methods!(OD, "3.17 u^8 (u = 2^-53, proven)", "6.42 u^8 (proven)");
