//! The reduction by pi/2 in f64 arithmetic, written once for one value (`f64`) and eight (`V8`): per lane the multiple
//! of pi/2 and the n greedy parts that the integer reduction (`reduce_exact`) gives, where a test decides them, and a
//! mask of the lanes it decides. The others take the integer reduction.
//!
//! Notation: u = 2^-53, C = P 2^-F (`tables::P`, pi/2 to 1216 fraction bits), c = RN(2/pi), k = round(RN(x_0 c)) != 0
//! as in `reduce_exact`, and v = x_0 + ... + x_(n-1) - k C, which its accumulator holds exactly for |x_i| < 2^53. It
//! subtracts k_2 C more, k_2 = round(RN(RN(v) c)), where |RN(v)| > 0.7854, and returns the greedy parts of the rest.
//!
//! * Limbs: L f64s (8, 12, 20 for n = 2, 4, 8), limb j a multiple of U_j = 2^(-26(j+1)) below 2^53 U_j, so that their
//!   sums are exact. Rounding y to a multiple of 2^e as (y + 1.5 2^(52+e)) - 1.5 2^(52+e) is exact for |y| <= 2^(51+e)
//!   (ties to even), and so is y minus it.
//! * pi/2: c0 = C rounded to a multiple of 2^-26 (27 bits, |C - c0| <= 2^-27), and the balanced digits G_j, |G_j| <=
//!   2^25, of C - c0 rounded to a multiple of U_(L-1): C - c0 = sum G_j U_j + t, |t| <= U_(L-1)/2. With k = k_h + k_l,
//!   k_h = k rounded to a multiple of 2^26, |k_l| <= 2^25, the products k_h c0, k_l c0, (k_h 2^-26) G_(j+1) and k_l
//!   G_j are integers times 2^-26, 2^-26, U_j and U_j below 2^53 of them, so exact; limb j receives the last two.
//! * x_0: t0 = (x_0 - k_h c0) - k_l c0 = x_0 - k c0 exactly. With |x_0 - k/c| <= 1/(2c) + u|x_0| < 1.29 and |c0 - 1/c|
//!   < 2^-27 (1 + 2^-24), |x_0 - k c0| < 1.29 + |k| 2^-27 (1 + 2^-24) < 2^25, a multiple of m = min(ulp(x_0), 2^-26)
//!   below 2^53 m (|x_0| > 0.78 gives ulp(x_0) >= 2^-53, and |k| < 0.64 |x_0| + 1), so representable. If k_h != 0,
//!   |k| > 2^25 and |x_0| > 2^25, and x_0 - k_h c0 = (x_0 - k c0) + k_l c0 is below 2^26 for |x_0| < 2^27 (where |k|
//!   2^-27 < 0.65) and below 2^28 otherwise, a multiple of min(ulp(x_0), 1) >= 2^-27, or >= 2^-25 for |x_0| >= 2^27:
//!   exact as well. t0, a multiple of 2^-53, fills limbs 0 to 2 exactly.
//! * x_1, ..., x_(n-1), each at most 2^20 (larger parts take the integer reduction): rounded to limb 0's multiple, the
//!   rest to limb 1's, and so on, each within U_(L-1)/2 of its limbs. The limbs then hold V with |v - V| <= (|k| + n -
//!   1) U_(L-1)/2, and carries make |D_j| <= U_(j-1)/2 for j >= 1.
//! * k_2: a = RN(D_0 + D_1) is within 2^-49 of RN(v) for |a| < 2.8. So |a| <= 0.7854 - 2^-47 means no correction, and
//!   |a| >= 0.7854 + 2^-47 a correction by round(RN(a c)) = k_2 where |RN(a c)| is 2^-46 or more from 1.5 (and |a| <
//!   2.8). The limbs then take -k_2 c0 and -k_2 G_j (|k_2| <= 2, exact) and their carries again, k is k + k_2, and eps
//!   = (|k| + n - 1) U_(L-1)/2 bounds |v - V| for the corrected v. Lanes within those margins take the integer
//!   reduction.
//! * Rounding: pass 0 sums the limbs from the last up by FastTwoSum (exact: a nonzero D_j has |D_j| >= U_j and the sum
//!   below it at most U_j (1 + 2^-25)/2), giving s_0 and the expansion E_1 = V - s_0 of its errors; pass i sums E_i by
//!   TwoSum likewise into s_i and E_(i+1) = E_i - s_i. Each pass has one term less than the one before.
//! * The test: lane passes if, for every i, B_(i+1) < g(s_i) (1 - 2^-40), with B_n = eps + sum |E_n|, B_i = B_(i+1) +
//!   |s_i|, g(s) = ulp(s)/2, or ulp(s)/4 when |s| is a power of two, and no |x_i| above 2^20.
//!
//! Why the bits are those of `reduce_exact`: by induction on i, the remainder that `reduce_exact` rounds at step i is
//! v - s_0 - ... - s_(i-1) = E_i + (v - V), and E_i = s_i + E_(i+1). So it is within |E_(i+1)| + eps <= B_(i+1) of
//! s_i, an upper bound computed with at most 30 rounded additions of nonnegative terms, which lose less than the factor
//! 1 - 2^-40. It is therefore strictly inside the interval of reals that round to s_i, s_i != 0 is normal (the limbs
//! are multiples of 2^-520), and round-to-nearest of the remainder is s_i, ties or not, the same rounding `Acc::round`
//! performs. No remainder is zero, so its greedy loop runs all n steps, and it corrects k exactly where the fast
//! reduction does, by the same k_2. A lane that fails the test is reduced by `reduce_exact`.
use super::{mutate, tables, R_TH};
use crate::simd::Simd;
use crate::v8::{M8, V8};

/// f64 arithmetic on one value or eight, the operations of the fast reduction
pub(crate) trait Fl: Copy {
    /// a mask, one bit per lane
    type M: Copy;
    fn splat(x: f64) -> Self;
    fn add(self, o: Self) -> Self;
    fn sub(self, o: Self) -> Self;
    fn mul(self, o: Self) -> Self;
    fn abs(self) -> Self;
    fn neg(self) -> Self;
    /// 2^floor(log2 |x|) for normal x, zero for zero and the subnormals
    fn pow2_floor(self) -> Self;
    fn gt(self, o: Self) -> Self::M;
    fn ge(self, o: Self) -> Self::M;
    fn eq(self, o: Self) -> Self::M;
    fn and(m: Self::M, n: Self::M) -> Self::M;
    fn or(m: Self::M, n: Self::M) -> Self::M;
    /// whether m is set on any lane
    fn any(m: Self::M) -> bool;
    /// per lane a where m is set, b elsewhere
    fn sel(m: Self::M, a: Self, b: Self) -> Self;
}

impl Fl for f64 {
    type M = bool;
    #[inline(always)]
    fn splat(x: f64) -> f64 {
        x
    }
    #[inline(always)]
    fn add(self, o: f64) -> f64 {
        self + o
    }
    #[inline(always)]
    fn sub(self, o: f64) -> f64 {
        self - o
    }
    #[inline(always)]
    fn mul(self, o: f64) -> f64 {
        self * o
    }
    #[inline(always)]
    fn abs(self) -> f64 {
        f64::abs(self)
    }
    #[inline(always)]
    fn neg(self) -> f64 {
        -self
    }
    #[inline(always)]
    fn pow2_floor(self) -> f64 {
        f64::from_bits(self.to_bits() & 0x7ff0_0000_0000_0000)
    }
    #[inline(always)]
    fn gt(self, o: f64) -> bool {
        self > o
    }
    #[inline(always)]
    fn ge(self, o: f64) -> bool {
        self >= o
    }
    #[inline(always)]
    fn eq(self, o: f64) -> bool {
        self == o
    }
    #[inline(always)]
    fn and(m: bool, n: bool) -> bool {
        m && n
    }
    #[inline(always)]
    fn or(m: bool, n: bool) -> bool {
        m || n
    }
    #[inline(always)]
    fn any(m: bool) -> bool {
        m
    }
    #[inline(always)]
    fn sel(m: bool, a: f64, b: f64) -> f64 {
        if m {
            a
        } else {
            b
        }
    }
}

impl<S: Simd> Fl for V8<S> {
    type M = M8<S>;
    #[inline(always)]
    fn splat(x: f64) -> Self {
        V8::splat(x)
    }
    #[inline(always)]
    fn add(self, o: Self) -> Self {
        V8::add(self, o)
    }
    #[inline(always)]
    fn sub(self, o: Self) -> Self {
        V8::sub(self, o)
    }
    #[inline(always)]
    fn mul(self, o: Self) -> Self {
        V8::mul(self, o)
    }
    #[inline(always)]
    fn abs(self) -> Self {
        V8::abs(self)
    }
    #[inline(always)]
    fn neg(self) -> Self {
        V8::neg(self)
    }
    #[inline(always)]
    fn pow2_floor(self) -> Self {
        V8::pow2_floor(self)
    }
    #[inline(always)]
    fn gt(self, o: Self) -> M8<S> {
        V8::gt(self, o)
    }
    #[inline(always)]
    fn ge(self, o: Self) -> M8<S> {
        V8::ge(self, o)
    }
    #[inline(always)]
    fn eq(self, o: Self) -> M8<S> {
        V8::eq(self, o)
    }
    #[inline(always)]
    fn and(m: M8<S>, n: M8<S>) -> M8<S> {
        m.and(n)
    }
    #[inline(always)]
    fn or(m: M8<S>, n: M8<S>) -> M8<S> {
        m.or(n)
    }
    #[inline(always)]
    fn any(m: M8<S>) -> bool {
        m.bits() != 0
    }
    #[inline(always)]
    fn sel(m: M8<S>, a: Self, b: Self) -> Self {
        m.sel(a, b)
    }
}

/// 2^e, for -1022 <= e <= 1023
const fn p2(e: i32) -> f64 {
    f64::from_bits(((1023 + e) as u64) << 52)
}

/// bit i of P
const fn pbit(i: usize) -> u64 {
    (tables::P[i / 64] >> (i % 64)) & 1
}

/// bits lo to lo + w - 1 of P, as an integer
const fn pbits(lo: usize, w: usize) -> u64 {
    let mut v = 0;
    let mut b = 0;
    while b < w {
        v |= pbit(lo + b) << b;
        b += 1;
    }
    v
}

/// the bit of P whose unit is 2^-26, and its top: P < 2^(F+1)
const C0_LO: usize = tables::F as usize - 26;
/// c0 = C rounded to a multiple of 2^-26, half up
pub(crate) const C0: f64 = (pbits(C0_LO, 27) + pbit(C0_LO - 1)) as f64 * p2(-26);

/// The digits of C - c0 on a grid of L limbs, as (A, B) with A_j = G_(j+1) U_j and B_j = G_j U_j (G_0 = G_L = 0), so
/// that k (C - c0) = sum (k_h 2^-26 A_j + k_l B_j) to within |k| U_(L-1)/2: G_j the balanced digits, |G_j| <= 2^25, of
/// C - c0 rounded half up to a multiple of U_(L-1). `cut` > 0 zeroes the last `cut` digits (`mutate::REDUCE_FAST_PI`).
const fn digits<const L: usize>(cut: usize) -> ([f64; L], [f64; L]) {
    assert!(L >= 3 && 26 * L < tables::F as usize);
    // G_j's raw bits, and c0's rounding up as a digit -1 at U_0
    let mut d = [0i64; L];
    d[0] = -(pbit(C0_LO - 1) as i64);
    let mut j = 1;
    while j < L {
        d[j] = pbits(tables::F as usize - 26 * (j + 1), 26) as i64;
        j += 1;
    }
    d[L - 1] += pbit(tables::F as usize - 26 * L - 1) as i64;
    // balanced: from the last digit up, a digit of 2^25 or more becomes one 2^26 less and carries one
    let mut j = L - 1;
    while j > 0 {
        if d[j] >= 1 << 25 {
            d[j] -= 1 << 26;
            d[j - 1] += 1;
        }
        j -= 1;
    }
    assert!(d[0] == 0);
    let mut j = L - cut;
    while j < L {
        d[j] = 0;
        j += 1;
    }
    let (mut a, mut b) = ([0.0; L], [0.0; L]);
    let mut j = 0;
    while j < L {
        let u = p2(-26 * (j as i32 + 1));
        b[j] = d[j] as f64 * u;
        if j + 1 < L {
            a[j] = d[j + 1] as f64 * u;
        }
        j += 1;
    }
    (a, b)
}

/// (h, y - h), h = y rounded to a multiple of 2^e, ties to even: exact for |y| <= 2^(51+e)
#[inline(always)]
fn split<T: Fl>(y: T, e: i32) -> (T, T) {
    let s = T::splat(1.5 * p2(52 + e));
    let h = y.add(s).sub(s);
    (h, y.sub(h))
}

/// (s, e) with s = RN(a + b) and a + b = s + e, for a = 0 or |a| >= |b|
#[inline(always)]
fn fast_two_sum<T: Fl>(a: T, b: T) -> (T, T) {
    let s = a.add(b);
    (s, b.sub(s.sub(a)))
}

/// (s, e) with s = RN(a + b) and a + b = s + e
#[inline(always)]
fn two_sum<T: Fl>(a: T, b: T) -> (T, T) {
    let s = a.add(b);
    let bb = s.sub(a);
    (s, a.sub(s.sub(bb)).add(b.sub(bb)))
}

/// round(t), halves away from zero, as `f64::round`, for |t| < 2^52 (a zero's sign aside)
#[inline(always)]
pub(crate) fn round_away<T: Fl>(t: T) -> T {
    let a = t.abs();
    let big = T::splat(p2(52));
    // nearest, ties to even, then a tie rounded down moved up
    let n = a.add(big).sub(big);
    let n = T::sel(n.sub(a).eq(T::splat(-0.5)), n.add(T::splat(1.0)), n);
    T::sel(T::splat(0.0).gt(t), n.neg(), n)
}

/// k mod 4 in [0, 4), for an integer |k| < 2^52
#[inline(always)]
pub(crate) fn mod4<T: Fl>(k: T) -> T {
    let s = T::splat(1.5 * p2(52));
    // the nearest integer to k/4, and k minus four times it, in [-2, 2]
    let f = k.mul(T::splat(0.25)).add(s).sub(s);
    let q = k.sub(f.mul(T::splat(4.0)));
    T::sel(T::splat(0.0).gt(q), q.add(T::splat(4.0)), q)
}

/// 2^-53 (1 - 2^-40) and 2^-54 (1 - 2^-40): the test's bound, times 2^floor(log2 |s|)
const G2: f64 = p2(-53) * (1.0 - p2(-40));
const G4: f64 = p2(-54) * (1.0 - p2(-40));
/// lower parts above this take `reduce`
const X_LOW: f64 = p2(20);

/// The fast reduction of x by k pi/2 for k = round(RN(x_0 RN(2/pi))) != 0 and finite parts with |x_0| <= 2^52, on L
/// limbs: (k', r, ok), where ok is set k' the multiple of pi/2 that `reduce` removes, k or k corrected, and r the n
/// greedy parts it returns (see the module's comment); elsewhere k' and r are to be discarded.
#[inline(always)]
pub(crate) fn fast<T: Fl, const N: usize, const L: usize>(x: &[T; N], k: T) -> (T, [T; N], T::M) {
    let (a, b) = if mutate::on(mutate::REDUCE_FAST_PI) {
        const { digits::<L>(2) }
    } else {
        const { digits::<L>(0) }
    };
    // k = k_h + k_l, and x_0 - k c0 exactly
    let s78 = T::splat(1.5 * p2(78));
    let kh = k.add(s78).sub(s78);
    let kl = k.sub(kh);
    let c0 = T::splat(C0);
    let t0 = x[0].sub(kh.mul(c0)).sub(kl.mul(c0));
    let mut d = [T::splat(0.0); L];
    let (h, y) = split(t0, -26);
    d[0] = h;
    let (h, y) = split(y, -52);
    d[1] = h;
    d[2] = y;
    let mut ok = T::splat(1.0).eq(T::splat(1.0));
    for xi in &x[1..] {
        ok = T::and(ok, T::splat(X_LOW).ge(xi.abs()));
        let mut y = *xi;
        for (j, dj) in d.iter_mut().enumerate() {
            let (h, r) = split(y, -26 * (j as i32 + 1));
            *dj = dj.add(h);
            y = r;
        }
    }
    // -k (C - c0), two exact products per limb
    let khs = kh.mul(T::splat(p2(-26)));
    for j in 0..L {
        d[j] = d[j].sub(khs.mul(T::splat(a[j]))).sub(kl.mul(T::splat(b[j])));
    }
    carries(&mut d);
    // `reduce`'s correction of k where |RN(v)| > 0.7854: a = RN(D_0 + D_1) is within 2^-49 of RN(v) for |a| < 2.8, so
    // a 2^-47 from 0.7854 decides whether it corrects, and round(RN(a c)) is its k_2 where RN(a c) is 2^-46 from 1.5
    let v0 = d[0].add(d[1]);
    let a0 = v0.abs();
    let fix = a0.ge(T::splat(R_TH + p2(-47)));
    let t = v0.mul(T::splat(tables::TWO_OVER_PI));
    let half = t.abs().sub(T::splat(1.5)).abs().ge(T::splat(p2(-46)));
    let corr = T::and(fix, T::and(T::splat(2.8).gt(a0), half));
    ok = T::and(ok, T::or(T::splat(R_TH - p2(-47)).ge(a0), corr));
    let mut k = k;
    if T::any(fix) {
        let k2 = T::sel(corr, round_away(t), T::splat(0.0));
        d[0] = d[0].sub(k2.mul(c0));
        for j in 1..L {
            d[j] = d[j].sub(k2.mul(T::splat(b[j])));
        }
        carries(&mut d);
        k = k.add(k2);
    }
    let eps = if mutate::on(mutate::REDUCE_FAST_EPS) {
        T::splat(0.0)
    } else {
        k.abs()
            .add(T::splat((N - 1) as f64))
            .mul(T::splat(p2(-26 * L as i32 - 1)))
    };
    // pass i: the terms d[i..L] (the limbs for i = 0, then the errors of pass i - 1) summed from the last up into r_i,
    // their errors left in d[i + 1..L]
    let mut r = [T::splat(0.0); N];
    for (i, ri) in r.iter_mut().enumerate() {
        let mut s = d[L - 1];
        for j in (i..L - 1).rev() {
            let (t, e) = if i == 0 {
                fast_two_sum(d[j], s)
            } else {
                two_sum(d[j], s)
            };
            s = t;
            d[j + 1] = e;
        }
        *ri = s;
    }
    // the test, from the last part up: bound >= |E_(i+1)| + eps, as E_i = r_i + E_(i+1)
    if !mutate::on(mutate::REDUCE_FAST_UNCHECKED) {
        let mut bound = eps;
        for e in &d[N..] {
            bound = bound.add(e.abs());
        }
        for ri in r.iter().rev() {
            let p = ri.pow2_floor();
            let g = T::sel(ri.abs().eq(p), p.mul(T::splat(G4)), p.mul(T::splat(G2)));
            ok = T::and(ok, g.gt(bound));
            bound = bound.add(ri.abs());
        }
    }
    if mutate::on(mutate::REDUCE_TAIL) {
        r[N - 1] = T::splat(0.0);
    }
    (k, r, ok)
}

/// the carries of the limbs: |D_j| <= U_(j-1)/2 for j >= 1, exactly, for |D_j| < 2^53 U_j
#[inline(always)]
fn carries<T: Fl, const L: usize>(d: &mut [T; L]) {
    for j in (1..L).rev() {
        let (h, r) = split(d[j], -26 * j as i32);
        d[j] = r;
        d[j - 1] = d[j - 1].add(h);
    }
}

/// limbs of the fast reduction for n parts: 26 L bits below the binary point, about 53 n + 51 + 49 for n = 2 and 4 and
/// 53 n + 51 + 45 for n = 8
pub(crate) const fn limbs(n: usize) -> usize {
    match n {
        2 => 8,
        4 => 12,
        _ => 20,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// c0 and the digits reproduce C to within U_(L-1)/2, checked against P in exact integer arithmetic; control: a
    /// digit one unit off fails
    #[test]
    fn fast_reduce_digits() {
        use crate::exact::{BigU, Dy};
        fn err<const L: usize>(b: &[f64; L]) -> Dy {
            let c = Dy {
                neg: false,
                m: BigU(tables::P.to_vec()),
                e: -(tables::F as i64),
            };
            let mut s = Dy::from_f64(C0);
            for v in b {
                s = s.add(&Dy::from_f64(*v));
            }
            c.sub(&s).abs()
        }
        fn check<const L: usize>() {
            let (a, b) = digits::<L>(0);
            for j in 0..L - 1 {
                assert_eq!(a[j], b[j + 1] * 2f64.powi(26), "A_j = G_(j+1) U_j");
                let g = b[j + 1] * 2f64.powi(26 * (j as i32 + 2));
                assert!(g.abs() <= 2f64.powi(25) && g == g.round(), "digit {}: {g}", j + 1);
            }
            assert_eq!((a[L - 1], b[0]), (0.0, 0.0));
            let half = Dy::from_f64(2f64.powi(-26 * L as i32 - 1));
            assert!(err(&b).cmp_abs(&half) != std::cmp::Ordering::Greater, "L = {L}");
            let mut bad = b;
            bad[L / 2] += 2f64.powi(-26 * (L as i32 / 2 + 1));
            assert!(
                err(&bad).cmp_abs(&half) == std::cmp::Ordering::Greater,
                "control, L = {L}"
            );
        }
        assert!((C0 - std::f64::consts::FRAC_PI_2).abs() <= 2f64.powi(-27));
        assert_eq!(C0, (C0 * 2f64.powi(26)).round() * 2f64.powi(-26));
        check::<8>();
        check::<12>();
        check::<20>();
    }

    /// round_away and mod4 against f64::round and rem_euclid at the halves and around them
    #[test]
    fn fast_reduce_round_mod4() {
        let mut ts = vec![
            0.5,
            1.5,
            2.5,
            0.49999999999999994,
            2f64.powi(51) + 0.5,
            4503599627370495.5,
            0.0,
        ];
        for i in 0..2000 {
            let t = (i as f64 - 1000.0) * 0.25;
            ts.extend([t, t.next_up(), t.next_down()]);
        }
        for t in ts {
            for t in [t, -t] {
                let (want, got) = (t.round(), round_away(t));
                assert!(want == got, "round({t}): {got} for {want}");
                let q = mod4(want);
                assert_eq!(q, (want as i64).rem_euclid(4) as f64, "mod4({want})");
            }
        }
    }
}
