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
//!   2^-10 u^n relative. Below 2^-(53n/2), r and 1 are returned, within u^n/6 and u^n/2. The last two steps of the
//!   sine run on r times 2^(j+1), for r_0 in bucket j (2^-(j+1) <= |r_0| < 2^-j), and are scaled back.
//! * Recombination by k mod 4, and tan r = sin r / cos r, the numerator times 2^(3(j+1)) and the quotient scaled back,
//!   or -cos r / sin r for odd k. The scalings are exact, and keep the products of the run in the normal range for
//!   every reduced argument from 2^-(53n/2) up.
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
//! For x on the ladder (a double-word number for `DD`) with |x_0| <= 2^52, and a run without underflow, the error is
//! at most C |f(x)| + 5 |k| 2^-1217 for sin and cos, and (C_T + 5 |k| 2^-1217 / |sin x cos x|) |tan x| for tan, with
//! k the multiple of pi/2 removed (|k| < 0.64 2^52, so 5 |k| 2^-1217 < 2^-1163) and C, C_T below. With the
//! scalings, the run is without underflow for every reduced argument from 2^-(53n/2) up, checked at eight parts in
//! every binade (the paper's remark on (A2)), unless a part of x lies far below the ladder.
//!
//! | C, C_T | `DD` | `QD` | `OD` |
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
//! The lane types `DV`, `QV` and `OV` have the same four functions, and each lane's result is bitwise the scalar
//! function of its value, so the bounds above hold per lane. The reduction runs on all lanes at once in f64 limbs
//! (`fast_reduce`), and a lane whose greedy parts that one does not decide runs the integer code. The evaluation runs
//! on all lanes at once, each with its own choices: its series and number of terms, its powers of two and its quadrant.
//! Horner's scheme runs the longest series and masks each step per lane, so that a lane with k terms starts at its own
//! leading coefficient and keeps its sum through the steps past its k. The quadrants, the early returns and the
//! unscaled quotients of `tan` are blended per lane. Each lane thus performs the scalar's sequence of roundings. A
//! NaN's sign and payload follow the order of its operands, which the compiler may change, so a lane whose result has a
//! NaN part, possible only for parts off the ladder or not finite, takes the scalar function's result: the bits match,
//! NaNs included.
//!
//! With the cargo feature `mutate`, `mutate::set(id)` breaks one step on purpose in the current thread, for the
//! controls of the accuracy tests; without it the hooks are compile-time `false`.
use crate::dd::{quick_two_sum, DD};
use crate::dv::{self, DV};
use crate::dw;
use crate::od::{alg, OD};
use crate::ov::OV;
use crate::qd::QD;
use crate::qv::QV;
use crate::simd::Simd;
use crate::v8::{M8, V8};
use std::ops::Neg;

#[rustfmt::skip]
pub(crate) mod tables;
pub(crate) mod fast_reduce;

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
    /// lanes only: Horner's steps masked by lane 0's number of terms on every lane
    pub const LANE_TERMS: u32 = 6;
    /// lanes only: lane 0's quadrant on every lane
    pub const LANE_QUADRANT: u32 = 7;
    /// lanes only: the lanes with a NaN part left as the lanes' arithmetic gives them, their NaNs' signs flipped, as
    /// another order of the operands can give them
    pub const LANE_NAN: u32 = 8;
    /// lanes only: lane 0's powers of two on every lane
    pub const LANE_POW2: u32 = 9;
    /// lanes only: the fast reduction's rounding test skipped, so that every lane takes its parts
    pub const REDUCE_FAST_UNCHECKED: u32 = 10;
    /// lanes only: the fast reduction's test with no allowance for its own error (eps = 0)
    pub const REDUCE_FAST_EPS: u32 = 11;
    /// lanes only: the fast reduction's pi/2 without its last two digits (52 bits), its test unchanged
    pub const REDUCE_FAST_PI: u32 = 12;
    /// number of ids
    pub const N: u32 = 12;
    /// the mutations' descriptions, by id
    pub const NAMES: [&str; 13] = [
        "none",
        "reduction: last part of r dropped",
        "reduction: pi/2 cut to 64 (n + 1) + 1 bits",
        "sin r: two terms fewer",
        "cos r: two terms fewer",
        "tan: divisor's last part dropped",
        "lanes: Horner's mask from lane 0's terms",
        "lanes: lane 0's quadrant on every lane",
        "lanes: NaN lanes from the lanes' arithmetic, NaN signs flipped",
        "lanes: lane 0's powers of two on every lane",
        "lanes: fast reduction's test skipped",
        "lanes: fast reduction's test with eps = 0",
        "lanes: fast reduction's pi/2 without its last two digits",
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
#[inline(always)]
pub(crate) fn reduce<const N: usize>(x: &[f64; N]) -> (u32, [f64; N]) {
    let k = (x[0] * tables::TWO_OVER_PI).round();
    if k == 0.0 {
        // |x_0| < 0.78539817: r = x, exactly
        return (0, *x);
    }
    reduce_k(x, k)
}

/// `reduce` for k = round(x_0 RN(2/pi)) != 0, out of line, so that r = x for k = 0 reaches the caller in registers
#[inline(never)]
fn reduce_k<const N: usize>(x: &[f64; N], mut k: f64) -> (u32, [f64; N]) {
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
// the evaluation, once for the three types and their lanes
// ---------------------------------------------------------------------------------------------------------------

/// the arithmetic the functions need, by type, and the choices they make by lane: one lane for the scalar types (`bool`
/// masks, `usize` integers, `f64` scales, `one_lane!`), eight for the lane types (`M8` masks, integers and scales as
/// `V8`, `eight_lanes!`)
pub(crate) trait Ext: Copy + Neg<Output = Self> {
    /// 2^-(53 n / 2), n the number of parts: below it sin r = r and cos r = 1 to within u^N/6 and u^N/2
    const TINY: f64;
    /// terms of the sin and cos series by bucket of r_0
    const KS: &'static [u8];
    const KC: &'static [u8];
    /// a mask, one bit per lane
    type M: Copy;
    /// a small integer per lane: k mod 4, a bucket or a number of terms
    type K: Copy;
    /// an f64 per lane
    type F: Copy;
    fn lead(self) -> Self::F;
    fn finite(self) -> Self::M;
    /// the N leading parts of an eight-part table entry
    fn coef(c: &[f64; 8]) -> Self;
    fn zero() -> Self;
    fn one() -> Self;
    fn nan() -> Self;
    fn mul(self, b: Self) -> Self;
    fn add(self, b: Self) -> Self;
    /// 1 + self
    fn one_plus(self) -> Self;
    fn div(self, b: Self) -> Self;
    /// x = k pi/2 + r: (k mod 4, r)
    fn reduce(self) -> (Self::K, Self);
    /// the last part dropped (`mutate::TAN_DIV_SHORT`)
    fn drop_last(self) -> Self;
    /// times a power of two, every part
    fn scale(self, p: Self::F) -> Self;
    /// per lane a where m is set, b elsewhere
    fn sel(m: Self::M, a: Self, b: Self) -> Self;
    /// (NaN, tiny): the lanes `early` gives NaN, and the others with |x_0| below TINY
    fn early(self) -> (Self::M, Self::M);
    /// (tiny, j): the lanes with |r_0| below TINY, and per lane the bucket of |r_0|, the last bucket where tiny
    fn buckets(self) -> (Self::M, Self::K);
    /// b on every lane
    fn mask(b: bool) -> Self::M;
    fn all(m: Self::M) -> bool;
    fn any(m: Self::M) -> bool;
    fn or(m: Self::M, n: Self::M) -> Self::M;
    /// per lane f(k mod 4)
    fn quadrant(q: Self::K, f: fn(usize) -> bool) -> Self::M;
    /// per lane the terms for bucket j: of the cos series where c is set, of the sin series elsewhere
    fn terms(c: Self::M, j: Self::K) -> Self::K;
    /// the most terms of any lane
    fn kmax(k: Self::K) -> usize;
    /// the lanes whose Horner sum takes step i, those with k >= i + 2 terms
    fn active(k: Self::K, i: usize) -> Self::M;
    /// per lane coefficient k - 1: of the cos table where c is set, of the sin table elsewhere
    fn lead_coef(c: Self::M, k: Self::K) -> Self;
    /// per lane 2^(m (j + 1))
    fn pow2_j(j: Self::K, m: i32) -> Self::F;
    /// per lane 1 where u is set, p elsewhere
    fn unit_where(u: Self::M, p: Self::F) -> Self::F;
}

/// the bucket of |r_0| in [TINY, 0.7854]: j with 2^-(j+1) <= |r_0| < 2^-j (0 for [0.5, 0.7854])
#[inline(always)]
fn bucket(r0: f64) -> usize {
    // parts off the ladder can leave |r_0| >= 1: bucket 0 then, never an index past the tables
    (1022 - ((r0.to_bits() >> 52) & 0x7ff) as i64).max(0) as usize
}

/// 2^k, for -1022 <= k <= 1023
#[inline(always)]
fn pow2(k: i32) -> f64 {
    f64::from_bits(((1023 + k) as u64) << 52)
}

/// the Horner sum c_(k-1) z^(k-2) + ... + c_1 of a table with k >= 2 terms, c(i) = c_i, per lane: each lane starts at
/// its own c_(k-1), `lead`, and keeps its sum through the steps past its own k, so that it rounds as the scalar sum of
/// its k terms
#[inline(always)]
fn horner<T: Ext>(z: T, k: T::K, lead: T, c: impl Fn(usize) -> T) -> T {
    let mut p = lead;
    for i in (1..T::kmax(k) - 1).rev() {
        let m = T::active(k, i);
        // unmasked where every lane takes the step: a select would keep a scalar type's sum in registers, stored and
        // reloaded around each out-of-line product and sum
        if T::all(m) {
            p = z.mul(p).add(c(i));
        } else {
            p = T::sel(m, z.mul(p).add(c(i)), p);
        }
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

/// Per lane sin r where c is clear and cos r where it is set, for |r| <= 0.7854 (1 + 2^-52), z = r^2 as computed, and
/// (tiny, j) = `r.buckets()`.
///
/// sin r = r + r (z P(z)), or r when r is tiny. The last two steps run on r' = 2^(j+1) r, |r'_0| in [1/2, 1) for r_0
/// in bucket j, and the sum is scaled back: r t, about r^3/6, would otherwise have products below the normal range for
/// |r| below about 2^-189 at eight parts. The scalings are exact and change no bit where the unscaled steps stay in the
/// normal range.
///
/// cos r = 1 + z Q(z), or 1 when r is tiny.
#[inline(always)]
fn sin_cos_r<T: Ext>(r: T, z: T, tiny: T::M, j: T::K, c: T::M) -> T {
    let small = T::sel(c, T::one(), r);
    if T::all(tiny) {
        return small;
    }
    // one series on every lane, or each lane's own
    let (all_c, no_c) = (T::all(c), !T::any(c));
    let k = T::terms(c, j);
    let p = horner(z, k, T::lead_coef(c, k), |i| {
        if all_c {
            T::coef(&tables::COS[i])
        } else if no_c {
            T::coef(&tables::SIN[i])
        } else {
            T::sel(c, T::coef(&tables::COS[i]), T::coef(&tables::SIN[i]))
        }
    });
    let zp = z.mul(p);
    let s = if all_c {
        zp
    } else {
        let r1 = r.scale(T::pow2_j(j, 1));
        r1.add(r1.mul(zp)).scale(T::pow2_j(j, -1))
    };
    let v = if no_c { s } else { T::sel(c, zp.one_plus(), s) };
    T::sel(tiny, small, v)
}

/// The lanes that return before the reduction (`skip`), with their sin and tan, and their cos: NaN for NaN, infinities
/// and |x_0| > 2^52, x itself (sin, tan) or one (cos) below 2^-(53n/2). `x` is the reduction's input, zero on them.
struct Early<T: Ext> {
    skip: T::M,
    sin: T,
    cos: T,
    x: T,
}

#[inline(always)]
fn early<T: Ext>(x: T) -> Early<T> {
    let (nan, tiny) = x.early();
    let skip = T::or(nan, tiny);
    Early {
        skip,
        sin: T::sel(nan, T::nan(), x),
        cos: T::sel(nan, T::nan(), T::one()),
        x: T::sel(skip, T::zero(), x),
    }
}

/// k mod 4 odd
#[inline(always)]
fn odd(q: usize) -> bool {
    q % 2 == 1
}

/// k mod 4 is 2 or 3: sin x = -(sin r or cos r)
#[inline(always)]
fn sin_neg(q: usize) -> bool {
    q >= 2
}

/// k mod 4 is 1 or 2: cos x = -(sin r or cos r)
#[inline(always)]
fn cos_neg(q: usize) -> bool {
    q == 1 || q == 2
}

#[inline(always)]
fn sin<T: Ext>(x: T) -> T {
    let e = early(x);
    if T::all(e.skip) {
        return e.sin;
    }
    let (q, r) = e.x.reduce();
    let z = r.mul(r);
    let (tiny, j) = r.buckets();
    // sin r, cos r, -sin r, -cos r by k mod 4
    let v = sin_cos_r(r, z, tiny, j, T::quadrant(q, odd));
    T::sel(e.skip, e.sin, T::sel(T::quadrant(q, sin_neg), -v, v))
}

#[inline(always)]
fn cos<T: Ext>(x: T) -> T {
    let e = early(x);
    if T::all(e.skip) {
        return e.cos;
    }
    let (q, r) = e.x.reduce();
    let z = r.mul(r);
    let (tiny, j) = r.buckets();
    // cos r, -sin r, -cos r, sin r by k mod 4
    let v = sin_cos_r(r, z, tiny, j, T::quadrant(q, |q| !odd(q)));
    T::sel(e.skip, e.cos, T::sel(T::quadrant(q, cos_neg), -v, v))
}

#[inline(always)]
fn sin_cos<T: Ext>(x: T) -> (T, T) {
    let e = early(x);
    if T::all(e.skip) {
        return (e.sin, e.cos);
    }
    let (q, r) = e.x.reduce();
    let z = r.mul(r);
    let (tiny, j) = r.buckets();
    let (s, c) = (
        sin_cos_r(r, z, tiny, j, T::mask(false)),
        sin_cos_r(r, z, tiny, j, T::mask(true)),
    );
    // (s, c), (c, -s), (-s, -c), (-c, s) by k mod 4
    let odd = T::quadrant(q, odd);
    let (a, b) = (T::sel(odd, c, s), T::sel(odd, s, c));
    let a = T::sel(T::quadrant(q, sin_neg), -a, a);
    let b = T::sel(T::quadrant(q, cos_neg), -b, b);
    (T::sel(e.skip, e.sin, a), T::sel(e.skip, e.cos, b))
}

#[inline(always)]
fn tan<T: Ext>(x: T) -> T {
    let e = early(x);
    if T::all(e.skip) {
        return e.sin;
    }
    let (q, r) = e.x.reduce();
    let z = r.mul(r);
    let (tiny, j) = r.buckets();
    let (s, c) = (
        sin_cos_r(r, z, tiny, j, T::mask(false)),
        sin_cos_r(r, z, tiny, j, T::mask(true)),
    );
    let short = |d: T| {
        if mutate::on(mutate::TAN_DIV_SHORT) {
            d.drop_last()
        } else {
            d
        }
    };
    // -cos r / sin r for odd k, sin r / cos r for even k
    let odd = T::quadrant(q, odd);
    let (num, den) = (T::sel(odd, c, s), short(T::sel(odd, s, c)));
    // unscaled for odd k and for tiny r
    let unit = T::or(odd, tiny);
    let t = if T::all(unit) {
        num.div(den)
    } else {
        // sin r / cos r on the numerator times 2^(3(j+1)), a quotient near 2^(2j): cos r = 1 - r^2/2 + ... has its
        // last parts about 2^(-2j-318) at eight parts, and their products with the last quotient terms of an unscaled
        // sin r / cos r leave the normal range for |r| below about 2^-82
        let (up, down) = (T::pow2_j(j, 3), T::pow2_j(j, -3));
        num.scale(T::unit_where(unit, up))
            .div(den)
            .scale(T::unit_where(unit, down))
    };
    T::sel(e.skip, e.sin, T::sel(odd, -t, t))
}

/// the choices of one lane, for the scalar types' `Ext`
macro_rules! one_lane {
    () => {
        type M = bool;
        type K = usize;
        type F = f64;
        #[inline(always)]
        fn sel(m: bool, a: Self, b: Self) -> Self {
            if m {
                a
            } else {
                b
            }
        }
        #[inline(always)]
        fn early(self) -> (bool, bool) {
            let a = self.lead().abs();
            let nan = !self.finite() || a > LIMIT;
            (nan, !nan && a < Self::TINY)
        }
        #[inline(always)]
        fn buckets(self) -> (bool, usize) {
            let a = self.lead().abs();
            if a < Self::TINY {
                (true, Self::KS.len() - 1)
            } else {
                (false, bucket(a))
            }
        }
        #[inline(always)]
        fn mask(b: bool) -> bool {
            b
        }
        #[inline(always)]
        fn all(m: bool) -> bool {
            m
        }
        #[inline(always)]
        fn any(m: bool) -> bool {
            m
        }
        #[inline(always)]
        fn or(m: bool, n: bool) -> bool {
            m || n
        }
        #[inline(always)]
        fn quadrant(q: usize, f: fn(usize) -> bool) -> bool {
            f(q)
        }
        #[inline(always)]
        fn terms(c: bool, j: usize) -> usize {
            if c {
                terms(Self::KC, j, mutate::COS_SHORT)
            } else {
                terms(Self::KS, j, mutate::SIN_SHORT)
            }
        }
        #[inline(always)]
        fn kmax(k: usize) -> usize {
            k
        }
        /// the one lane takes every step, as kmax is its k
        #[inline(always)]
        fn active(_k: usize, _i: usize) -> bool {
            true
        }
        #[inline(always)]
        fn lead_coef(c: bool, k: usize) -> Self {
            Self::coef(if c {
                &tables::COS[k - 1]
            } else {
                &tables::SIN[k - 1]
            })
        }
        #[inline(always)]
        fn pow2_j(j: usize, m: i32) -> f64 {
            pow2(m * (j as i32 + 1))
        }
        #[inline(always)]
        fn unit_where(u: bool, p: f64) -> f64 {
            if u {
                1.0
            } else {
                p
            }
        }
    };
}

/// the choices of eight lanes, for the lane types' `Ext`: integers as exact f64 lanes, each lane's table entries and
/// powers of two from the scalar functions
macro_rules! eight_lanes {
    () => {
        type M = M8<S>;
        type K = V8<S>;
        type F = V8<S>;
        #[inline(always)]
        fn early(self) -> (M8<S>, M8<S>) {
            let a = self.lead().abs();
            let nan = self.finite().not().or(a.gt(V8::splat(LIMIT)));
            (nan, nan.not().and(V8::splat(Self::TINY).gt(a)))
        }
        #[inline(always)]
        fn buckets(self) -> (M8<S>, V8<S>) {
            let a = self.lead().abs();
            let j = a.to_array().map(|v| {
                if v < Self::TINY {
                    (Self::KS.len() - 1) as f64
                } else {
                    bucket(v) as f64
                }
            });
            (V8::splat(Self::TINY).gt(a), V8::from_array(j))
        }
        #[inline(always)]
        fn mask(b: bool) -> M8<S> {
            let z = V8::zero();
            if b {
                z.eq(z)
            } else {
                z.ne(z)
            }
        }
        #[inline(always)]
        fn all(m: M8<S>) -> bool {
            m.bits() == 0xff
        }
        #[inline(always)]
        fn any(m: M8<S>) -> bool {
            m.bits() != 0
        }
        #[inline(always)]
        fn or(m: M8<S>, n: M8<S>) -> M8<S> {
            m.or(n)
        }
        #[inline(always)]
        fn quadrant(q: V8<S>, f: fn(usize) -> bool) -> M8<S> {
            let q = q.to_array();
            let lane0 = mutate::on(mutate::LANE_QUADRANT);
            let set = q.map(|v| {
                let v = if lane0 { q[0] } else { v };
                f(v as usize) as u8 as f64
            });
            V8::from_array(set).eq(V8::splat(1.0))
        }
        #[inline(always)]
        fn terms(c: M8<S>, j: V8<S>) -> V8<S> {
            let (c, j) = (c.bits(), j.to_array());
            V8::from_array(std::array::from_fn(|l| {
                let j = j[l] as usize;
                if c >> l & 1 == 1 {
                    terms(Self::KC, j, mutate::COS_SHORT) as f64
                } else {
                    terms(Self::KS, j, mutate::SIN_SHORT) as f64
                }
            }))
        }
        #[inline(always)]
        fn kmax(k: V8<S>) -> usize {
            k.hmax() as usize
        }
        #[inline(always)]
        fn active(k: V8<S>, i: usize) -> M8<S> {
            let k = if mutate::on(mutate::LANE_TERMS) {
                k.bcast(0)
            } else {
                k
            };
            k.ge(V8::splat((i + 2) as f64))
        }
        #[inline(always)]
        fn lead_coef(c: M8<S>, k: V8<S>) -> Self {
            let (c, k) = (c.bits(), k.to_array());
            Self::rows(std::array::from_fn(|l| {
                let t = if c >> l & 1 == 1 {
                    &tables::COS
                } else {
                    &tables::SIN
                };
                &t[k[l] as usize - 1]
            }))
        }
        #[inline(always)]
        fn pow2_j(j: V8<S>, m: i32) -> V8<S> {
            let j = j.to_array();
            let lane0 = mutate::on(mutate::LANE_POW2);
            V8::from_array(j.map(|v| {
                let v = if lane0 { j[0] } else { v };
                pow2(m * (v as i32 + 1))
            }))
        }
        #[inline(always)]
        fn unit_where(u: M8<S>, p: V8<S>) -> V8<S> {
            u.sel(V8::splat(1.0), p)
        }
    };
}

// ---------------------------------------------------------------------------------------------------------------
// the three types
// ---------------------------------------------------------------------------------------------------------------

impl Ext for DD {
    const TINY: f64 = f64::from_bits((1023 - 53) << 52); // 2^-53
    const KS: &'static [u8] = &tables::KS2;
    const KC: &'static [u8] = &tables::KC2;
    one_lane!();
    fn lead(self) -> f64 {
        self.hi
    }
    fn finite(self) -> bool {
        self.hi.is_finite() && self.lo.is_finite()
    }
    fn coef(c: &[f64; 8]) -> DD {
        DD { hi: c[0], lo: c[1] }
    }
    fn zero() -> DD {
        DD::ZERO
    }
    fn one() -> DD {
        DD::ONE
    }
    fn nan() -> DD {
        DD::from_f64(f64::NAN)
    }
    fn mul(self, b: DD) -> DD {
        let (hi, lo) = dw::dw_times_dw3((self.hi, self.lo), (b.hi, b.lo));
        DD { hi, lo }
    }
    fn add(self, b: DD) -> DD {
        self + b
    }
    fn one_plus(self) -> DD {
        let (hi, lo) = dw::dw_plus_fp((self.hi, self.lo), 1.0);
        DD { hi, lo }
    }
    fn div(self, b: DD) -> DD {
        self.fast_div(b)
    }
    #[inline(always)]
    fn reduce(self) -> (usize, DD) {
        let (q, r) = reduce(&[self.hi, self.lo]);
        // the greedy r can have |r_1| = ulp(r_0)/2 with r_0 odd, a tie that RN(r_0 + r_1) rounds away from r_0; the
        // double-word algorithms' bounds need r_0 = RN(r_0 + r_1)
        let (hi, lo) = quick_two_sum(r[0], r[1]);
        (q as usize, DD { hi, lo })
    }
    fn drop_last(self) -> DD {
        DD::from_f64(self.hi)
    }
    fn scale(self, p: f64) -> DD {
        self.mul_pwr2(p)
    }
}

impl Ext for QD {
    const TINY: f64 = f64::from_bits((1023 - 106) << 52); // 2^-106
    const KS: &'static [u8] = &tables::KS4;
    const KC: &'static [u8] = &tables::KC4;
    one_lane!();
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
    fn zero() -> QD {
        QD::ZERO
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
    #[inline(always)]
    fn reduce(self) -> (usize, QD) {
        let (q, x) = reduce(&self.x);
        (q as usize, QD { x })
    }
    fn drop_last(self) -> QD {
        QD {
            x: [self.x[0], self.x[1], self.x[2], 0.0],
        }
    }
    fn scale(self, p: f64) -> QD {
        self.mul_pwr2(p)
    }
}

impl Ext for OD {
    const TINY: f64 = f64::from_bits((1023 - 212) << 52); // 2^-212
    const KS: &'static [u8] = &tables::KS8;
    const KC: &'static [u8] = &tables::KC8;
    one_lane!();
    fn lead(self) -> f64 {
        self.x[0]
    }
    fn finite(self) -> bool {
        self.x.iter().all(|v| v.is_finite())
    }
    fn coef(c: &[f64; 8]) -> OD {
        OD { x: *c }
    }
    fn zero() -> OD {
        OD::ZERO
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
    #[inline(always)]
    fn reduce(self) -> (usize, OD) {
        let (q, x) = reduce(&self.x);
        (q as usize, OD { x })
    }
    fn drop_last(self) -> OD {
        let mut x = self.x;
        x[7] = 0.0;
        OD { x }
    }
    fn scale(self, p: f64) -> OD {
        self.mul_pwr2(p)
    }
}

macro_rules! trig_methods {
    ($t:ty, $sc:literal, $tan:literal) => {
        impl $t {
            #[doc = concat!("sin x, within ", $sc, " relative and an absolute 5 |k| 2^-1217 < 2^-1163 for x on the ",
                "ladder with |x_0| <= 2^52 (see `trig` for the hypotheses): a reduction by pi/2 to 1216 fraction bits ",
                "in exact integer arithmetic, and a Taylor series. NaN for NaN, the infinities and |x_0| > 2^52; a ",
                "zero gives itself.")]
            pub fn sin(self) -> $t {
                sin(self)
            }
            #[doc = concat!("cos x, within ", $sc, " relative, as `sin`; one for a zero.")]
            pub fn cos(self) -> $t {
                cos(self)
            }
            #[doc = concat!("tan x = sin x / cos x from one reduction, within ", $tan, " and 5 |k| 2^-1217 / ",
                "|sin x cos x| relative, as `sin`; a zero gives itself.")]
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

// ---------------------------------------------------------------------------------------------------------------
// the three lane types
// ---------------------------------------------------------------------------------------------------------------

/// `reduce` on each lane: (k mod 4 as f64, the parts of r), bitwise. Where every lane has |x_0 RN(2/pi)| < 1/2, k = 0
/// and r = x, as `reduce` decides from round(x_0 RN(2/pi)) = 0, with no lane taken apart. Otherwise the lanes with
/// k != 0 take the fast reduction on L limbs (`fast_reduce`), and those whose parts it does not decide take `reduce`.
#[inline(always)]
fn reduce_lanes<S: Simd, const N: usize, const L: usize>(c: &[V8<S>; N]) -> (V8<S>, [V8<S>; N]) {
    let t = c[0].mul(V8::splat(tables::TWO_OVER_PI));
    let k0 = V8::splat(0.5).gt(t.abs());
    if k0.bits() == 0xff {
        return (V8::zero(), *c);
    }
    let k = fast_reduce::round_away(t);
    let (f, ok) = fast_reduce::fast::<V8<S>, N, L>(c, k);
    let mut q = k0.sel(V8::zero(), fast_reduce::mod4(k));
    let mut r = *c;
    for i in 0..N {
        r[i] = k0.sel(c[i], f[i]);
    }
    // every lane with k != 0 under the mutation of `reduce`'s pi/2, which the fast reduction does not follow
    let left = if mutate::on(mutate::REDUCE_PI_SHORT) {
        !k0.bits()
    } else {
        !(ok.bits() | k0.bits())
    };
    if left != 0 {
        exact_lanes(c, left, &mut q, &mut r);
    }
    (q, r)
}

/// the lanes of (q, r) set in m replaced by `reduce` of those of x
#[inline(always)]
fn exact_lanes<S: Simd, const N: usize>(x: &[V8<S>; N], m: u8, q: &mut V8<S>, r: &mut [V8<S>; N]) {
    let a = x.map(|v| v.to_array());
    let mut qa = q.to_array();
    let mut ra = r.map(|v| v.to_array());
    for l in 0..8 {
        if m >> l & 1 == 1 {
            let (ql, rl) = reduce::<N>(&std::array::from_fn(|i| a[i][l]));
            qa[l] = ql as f64;
            for i in 0..N {
                ra[i][l] = rl[i];
            }
        }
    }
    *q = V8::from_array(qa);
    *r = ra.map(V8::from_array);
}

/// |v| < inf on every lane of every part
#[inline(always)]
fn finite_lanes<S: Simd>(c: &[V8<S>]) -> M8<S> {
    let inf = V8::splat(f64::INFINITY);
    let mut m = inf.gt(c[0].abs());
    for v in &c[1..] {
        m = m.and(inf.gt(v.abs()));
    }
    m
}

impl<S: Simd> DV<S> {
    /// lane l the leading two parts of the table entry r\[l\]
    #[inline(always)]
    fn rows(r: [&[f64; 8]; 8]) -> Self {
        DV {
            hi: V8::from_array(r.map(|c| c[0])),
            lo: V8::from_array(r.map(|c| c[1])),
        }
    }
}

impl<S: Simd> Ext for DV<S> {
    const TINY: f64 = <DD as Ext>::TINY;
    const KS: &'static [u8] = <DD as Ext>::KS;
    const KC: &'static [u8] = <DD as Ext>::KC;
    eight_lanes!();
    #[inline(always)]
    fn lead(self) -> V8<S> {
        self.hi
    }
    #[inline(always)]
    fn finite(self) -> M8<S> {
        finite_lanes(&[self.hi, self.lo])
    }
    #[inline(always)]
    fn coef(c: &[f64; 8]) -> Self {
        DV::splat(DD::coef(c))
    }
    #[inline(always)]
    fn zero() -> Self {
        DV::zero()
    }
    #[inline(always)]
    fn one() -> Self {
        DV::splat(DD::one())
    }
    #[inline(always)]
    fn nan() -> Self {
        DV::splat(DD::nan())
    }
    #[inline(always)]
    fn mul(self, b: Self) -> Self {
        let (hi, lo) = dw::dw_times_dw3((self.hi, self.lo), (b.hi, b.lo));
        DV { hi, lo }
    }
    #[inline(always)]
    fn add(self, b: Self) -> Self {
        self + b
    }
    #[inline(always)]
    fn one_plus(self) -> Self {
        let (hi, lo) = dw::dw_plus_fp((self.hi, self.lo), V8::splat(1.0));
        DV { hi, lo }
    }
    #[inline(always)]
    fn div(self, b: Self) -> Self {
        self.fast_div(b)
    }
    #[inline(always)]
    fn reduce(self) -> (V8<S>, Self) {
        let (q, [h, l]) = reduce_lanes::<S, 2, { fast_reduce::limbs(2) }>(&[self.hi, self.lo]);
        // a double-word number, as `DD`'s
        let (hi, lo) = dv::quick_two_sum(h, l);
        (q, DV { hi, lo })
    }
    #[inline(always)]
    fn drop_last(self) -> Self {
        DV {
            hi: self.hi,
            lo: V8::zero(),
        }
    }
    #[inline(always)]
    fn scale(self, p: V8<S>) -> Self {
        DV {
            hi: self.hi.mul(p),
            lo: self.lo.mul(p),
        }
    }
    #[inline(always)]
    fn sel(m: M8<S>, a: Self, b: Self) -> Self {
        DV {
            hi: m.sel(a.hi, b.hi),
            lo: m.sel(a.lo, b.lo),
        }
    }
}

impl<S: Simd> QV<S> {
    /// lane l the leading four parts of the table entry r\[l\]
    #[inline(always)]
    fn rows(r: [&[f64; 8]; 8]) -> Self {
        let mut c = [V8::zero(); 4];
        for i in 0..4 {
            c[i] = V8::from_array(r.map(|c| c[i]));
        }
        QV { c }
    }
}

impl<S: Simd> Ext for QV<S> {
    const TINY: f64 = <QD as Ext>::TINY;
    const KS: &'static [u8] = <QD as Ext>::KS;
    const KC: &'static [u8] = <QD as Ext>::KC;
    eight_lanes!();
    #[inline(always)]
    fn lead(self) -> V8<S> {
        self.c[0]
    }
    #[inline(always)]
    fn finite(self) -> M8<S> {
        finite_lanes(&self.c)
    }
    #[inline(always)]
    fn coef(c: &[f64; 8]) -> Self {
        QV::splat(QD::coef(c))
    }
    #[inline(always)]
    fn zero() -> Self {
        QV::zero()
    }
    #[inline(always)]
    fn one() -> Self {
        QV::splat(QD::one())
    }
    #[inline(always)]
    fn nan() -> Self {
        QV::splat(QD::nan())
    }
    #[inline(always)]
    fn mul(self, b: Self) -> Self {
        self * b
    }
    #[inline(always)]
    fn add(self, b: Self) -> Self {
        self + b
    }
    #[inline(always)]
    fn one_plus(self) -> Self {
        self.add_f(1.0)
    }
    #[inline(always)]
    fn div(self, b: Self) -> Self {
        self / b
    }
    #[inline(always)]
    fn reduce(self) -> (V8<S>, Self) {
        let (q, c) = reduce_lanes::<S, 4, { fast_reduce::limbs(4) }>(&self.c);
        (q, QV { c })
    }
    #[inline(always)]
    fn drop_last(self) -> Self {
        let mut c = self.c;
        c[3] = V8::zero();
        QV { c }
    }
    #[inline(always)]
    fn scale(self, p: V8<S>) -> Self {
        let mut c = self.c;
        for v in c.iter_mut() {
            *v = v.mul(p);
        }
        QV { c }
    }
    #[inline(always)]
    fn sel(m: M8<S>, a: Self, b: Self) -> Self {
        let mut c = b.c;
        for i in 0..4 {
            c[i] = m.sel(a.c[i], b.c[i]);
        }
        QV { c }
    }
}

impl<S: Simd> OV<S> {
    /// lane l the table entry r\[l\]
    #[inline(always)]
    fn rows(r: [&[f64; 8]; 8]) -> Self {
        let mut c = [V8::zero(); 8];
        for i in 0..8 {
            c[i] = V8::from_array(r.map(|c| c[i]));
        }
        OV { c }
    }
}

impl<S: Simd> Ext for OV<S> {
    const TINY: f64 = <OD as Ext>::TINY;
    const KS: &'static [u8] = <OD as Ext>::KS;
    const KC: &'static [u8] = <OD as Ext>::KC;
    eight_lanes!();
    #[inline(always)]
    fn lead(self) -> V8<S> {
        self.c[0]
    }
    #[inline(always)]
    fn finite(self) -> M8<S> {
        finite_lanes(&self.c)
    }
    #[inline(always)]
    fn coef(c: &[f64; 8]) -> Self {
        OV::splat(OD::coef(c))
    }
    #[inline(always)]
    fn zero() -> Self {
        OV::zero()
    }
    #[inline(always)]
    fn one() -> Self {
        OV::splat(OD::one())
    }
    #[inline(always)]
    fn nan() -> Self {
        OV::splat(OD::nan())
    }
    #[inline(always)]
    fn mul(self, b: Self) -> Self {
        self * b
    }
    #[inline(always)]
    fn add(self, b: Self) -> Self {
        self + b
    }
    #[inline(always)]
    fn one_plus(self) -> Self {
        self.add_f(1.0)
    }
    #[inline(always)]
    fn div(self, b: Self) -> Self {
        self / b
    }
    #[inline(always)]
    fn reduce(self) -> (V8<S>, Self) {
        let (q, c) = reduce_lanes::<S, 8, { fast_reduce::limbs(8) }>(&self.c);
        (q, OV { c })
    }
    #[inline(always)]
    fn drop_last(self) -> Self {
        let mut c = self.c;
        c[7] = V8::zero();
        OV { c }
    }
    #[inline(always)]
    fn scale(self, p: V8<S>) -> Self {
        OV {
            c: alg::mul_pwr2(&self.c, p),
        }
    }
    #[inline(always)]
    fn sel(m: M8<S>, a: Self, b: Self) -> Self {
        let mut c = b.c;
        for i in 0..8 {
            c[i] = m.sel(a.c[i], b.c[i]);
        }
        OV { c }
    }
}

/// The lane types' scalar values, for the lanes whose result has a NaN part. Such a result needs parts off the ladder
/// or a NaN or infinite part. Its NaNs' signs and payloads follow the order of the operands, which the compiler may
/// change (LLVM keeps no NaN's sign), so they differ between the lanes' arithmetic and the scalar's, and between
/// backends. A NaN's sign reaches only NaN parts, as the masks treat a NaN alike whatever its sign, so those lanes take
/// the scalar function's result, called out of line, and every other lane is the lanes' own.
trait Scalars: Sized {
    type Scalar: Copy;
    /// the lanes with a NaN part, bit j for lane j
    fn nan_lanes(self) -> u8;
    /// every NaN part's sign flipped (`mutate::LANE_NAN`)
    fn flip_nans(self) -> Self;
    fn lane_of(self, j: usize) -> Self::Scalar;
    /// self with lane j set to v
    fn with_lane(self, j: usize, v: Self::Scalar) -> Self;
}

macro_rules! scalars {
    ($t:ident, $s:ident, $n:literal, $parts:ident, $from:ident, $sparts:ident) => {
        impl<S: Simd> Scalars for $t<S> {
            type Scalar = $s;
            #[inline(always)]
            fn nan_lanes(self) -> u8 {
                let parts = self.$parts();
                let mut m = parts[0].ne(parts[0]);
                for x in &parts[1..] {
                    m = m.or(x.ne(*x));
                }
                m.bits()
            }
            fn flip_nans(self) -> Self {
                $t::$from(self.$parts().map(|x| x.ne(x).sel(x.neg(), x)))
            }
            fn lane_of(self, j: usize) -> $s {
                self.lane(j)
            }
            fn with_lane(self, j: usize, value: $s) -> Self {
                let mut a: [[f64; 8]; $n] = self.$parts().map(|x| x.to_array());
                let w = $sparts(value);
                for i in 0..$n {
                    a[i][j] = w[i];
                }
                $t::$from(a.map(V8::from_array))
            }
        }
    };
}

impl<S: Simd> DV<S> {
    #[inline(always)]
    fn parts_v(self) -> [V8<S>; 2] {
        [self.hi, self.lo]
    }
    fn from_parts_v(c: [V8<S>; 2]) -> Self {
        DV { hi: c[0], lo: c[1] }
    }
}

impl<S: Simd> QV<S> {
    #[inline(always)]
    fn parts_v(self) -> [V8<S>; 4] {
        self.c
    }
    fn from_parts_v(c: [V8<S>; 4]) -> Self {
        QV { c }
    }
}

impl<S: Simd> OV<S> {
    #[inline(always)]
    fn parts_v(self) -> [V8<S>; 8] {
        self.c
    }
    fn from_parts_v(c: [V8<S>; 8]) -> Self {
        OV { c }
    }
}

fn dd_parts(x: DD) -> [f64; 2] {
    [x.hi, x.lo]
}

fn qd_parts(x: QD) -> [f64; 4] {
    x.x
}

fn od_parts(x: OD) -> [f64; 8] {
    x.x
}

scalars!(DV, DD, 2, parts_v, from_parts_v, dd_parts);
scalars!(QV, QD, 4, parts_v, from_parts_v, qd_parts);
scalars!(OV, OD, 8, parts_v, from_parts_v, od_parts);

/// v, with the lanes that have a NaN part set to f of x's lane, f called through a pointer the compiler cannot see, so
/// that it is the scalar function's own code
#[inline(always)]
fn scalar_nans<T: Scalars + Copy>(x: T, v: T, f: fn(T::Scalar) -> T::Scalar) -> T {
    let m = v.nan_lanes();
    if m == 0 {
        return v;
    }
    if mutate::on(mutate::LANE_NAN) {
        return v.flip_nans();
    }
    let f = std::hint::black_box(f);
    let mut v = v;
    for j in 0..8 {
        if m >> j & 1 == 1 {
            v = v.with_lane(j, f(x.lane_of(j)));
        }
    }
    v
}

macro_rules! trig_lane_methods {
    ($t:ident, $s:ident) => {
        impl<S: Simd> $t<S> {
            #[doc = concat!("sin x on every lane, each lane bitwise `", stringify!($s), "::sin` of its value, ",
                        "with its bounds (see `trig`)")]
            #[inline]
            pub fn sin(self) -> Self {
                S::vectorize(
                    #[inline(always)]
                    || scalar_nans(self, sin(self), $s::sin),
                )
            }
            #[doc = concat!("cos x on every lane, each lane bitwise `", stringify!($s), "::cos` of its value")]
            #[inline]
            pub fn cos(self) -> Self {
                S::vectorize(
                    #[inline(always)]
                    || scalar_nans(self, cos(self), $s::cos),
                )
            }
            #[doc = concat!("tan x on every lane, each lane bitwise `", stringify!($s), "::tan` of its value. ",
                        "`x.tan()` on this type is this function; the tangent of `dual::Lane` is `Lane::tan(x)`.")]
            #[inline]
            pub fn tan(self) -> Self {
                S::vectorize(
                    #[inline(always)]
                    || scalar_nans(self, tan(self), $s::tan),
                )
            }
            /// (sin x, cos x) on every lane from one reduction, bitwise `(self.sin(), self.cos())`
            #[inline]
            pub fn sin_cos(self) -> (Self, Self) {
                S::vectorize(
                    #[inline(always)]
                    || {
                        let (s, c) = sin_cos(self);
                        let m = s.nan_lanes() | c.nan_lanes();
                        if m == 0 {
                            return (s, c);
                        }
                        if mutate::on(mutate::LANE_NAN) {
                            return (s.flip_nans(), c.flip_nans());
                        }
                        let f = std::hint::black_box($s::sin_cos as fn($s) -> ($s, $s));
                        let (mut s, mut c) = (s, c);
                        for j in 0..8 {
                            if m >> j & 1 == 1 {
                                let (a, b) = f(self.lane_of(j));
                                s = s.with_lane(j, a);
                                c = c.with_lane(j, b);
                            }
                        }
                        (s, c)
                    },
                )
            }
        }
    };
}

trig_lane_methods!(DV, DD);
trig_lane_methods!(QV, QD);
trig_lane_methods!(OV, OD);
