//! Scalar octo-double: an unevaluated sum x0 + x1 + ... + x7 of eight f64, renormalized so that the parts do not
//! overlap (|x_{i+1}| <= ulp(x_i)/2), about 126 significant digits (2^-418 relative, `OD::EPS`). The 8-lane
//! `ov::OV` runs the same algorithms with bitwise the same results.
//!
//! The algorithms are written once over `Limb`, a part position of one value (`f64`) or of eight (`V8`), so the
//! scalar type and the lanes perform the same IEEE operations in the same order. They generalize the quad-double
//! algorithms of the QD library (Y. Hida, X. S. Li, D. H. Bailey, "Algorithms for quad-double precision floating
//! point arithmetic", ARITH-15, 2001) from four parts to eight, with the error-free transformations two-sum and the
//! FMA two-product (`dd`):
//!
//! * Renormalization (`renorm`): QD's two passes. The first runs from the smallest part up with two-sums, so it is
//!   error-free whatever the order of the parts (VecSum: Ogita, Rump, Oishi, "Accurate sum and dot product", SIAM J.
//!   Sci. Comput. 26(6), 2005, 1955-1988, doi:10.1137/030601818; Joldes, Marty, Muller, Popescu, "Arithmetic
//!   algorithms for extended precision using floating-point expansions", IEEE Trans. Comput. 65(4), 2016,
//!   1197-1210, doi:10.1109/TC.2015.2441714). The second runs from the top with quick-two-sums and skips zero
//!   errors, so that an exact partial sum does not leave a gap, and adds what is left into the eighth part.
//! * Addition: the parts pairwise by two-sums, then each error carried down the levels below it, every level but
//!   the last by two-sums (`dep`), and the nine levels renormalized: QD's sloppy add with its error terms kept to
//!   the eighth level. Its error is relative to |a| + |b| (Cray-style), as QD's `+`.
//! * Multiplication: every partial product a_i b_j of order i + j <= 7 by two-product, the products of order 8 by
//!   fused multiply-adds, all deposited by order into nine levels whose first eight sum with two-sums, then
//!   renormalized: QD's accurate multiply, extended to eight parts. The levels carry the product's terms to order 8,
//!   below the eighth part, so its error is that of the renormalization's rounding to eight parts.
//! * Division: long division, nine quotient terms q_k = r_0 / b_0 with the remainder r - b q_k updated in one pass
//!   (QD's accurate divide); the square root by Newton's iteration on 1/sqrt(a), four steps, after scaling by a
//!   power of four (QD's, with this crate's scaling, `qd::QD::sqrt`).
//! * `OdAcc`: sums of products, each product's nine levels added into nine running levels with two-sums (the scalar
//!   twin of `ov::ODotAcc`); `finish` adds the levels with octo-double + f64.
//!
//! The error bounds the tests check are stated per operation where it is defined (`od_tests`), measured against
//! exact arithmetic (`exact`). The algorithms carry no proof here: the bounds are those measured. Full precision
//! needs every part to be a normal f64, |x| above about 2^-600 (424 bits above 2^-1022); below that the lower parts
//! lose bits to underflow, as QD's do below about 2^-800.
//!
//! With the cargo feature `mutate`, `mutate::set(id)` breaks one algorithm on purpose in the current thread, for
//! the controls of the accuracy tests; without it the hooks are compile-time `false`.
use crate::dd::DD;
use crate::exact::Dy;
use crate::qd::QD;
use std::cmp::Ordering;
use std::ops::{Add, Div, Mul, Neg, Sub};

/// Deliberate breakage for the controls (feature `mutate`; ids below, 0 = none).
pub mod mutate {
    /// renormalization: the eighth part dropped
    pub const RENORM_DROP: u32 = 1;
    /// two-sum: its error's second term subtracted instead of added (a wrong sign in an error-free transformation)
    pub const TWO_SUM_SIGN: u32 = 2;
    /// add: the error of a1 + b1 dropped
    pub const ADD_T1: u32 = 3;
    /// mul: the error of a2 b3 (an order-6 term) dropped
    pub const MUL_E23: u32 = 4;
    /// od x f64: the error of a3 b dropped
    pub const MUL_F_E3: u32 = 5;
    /// divide: the remainder update before the sixth quotient term skipped
    pub const DIV_REM: u32 = 6;
    /// sqrt: two Newton iterations instead of four
    pub const SQRT_ITER: u32 = 7;
    /// dot accumulator: the error of the running sum at level 3 dropped
    pub const ACC_L3: u32 = 8;
    /// parse: the last part truncated instead of rounded to nearest
    pub const PARSE_TRUNC: u32 = 9;
    /// 8-lane only: the renormalization's zero test ignored (every error emitted)
    pub const OV_RENORM_MASK: u32 = 10;
    /// 8-lane only, on the backend `simd::Native`: two-product's fused multiply-subtract replaced by a plain product
    /// and a subtraction
    pub const OV_FMA_PLAIN: u32 = 11;
    /// number of ids
    pub const N: u32 = 11;
    /// the mutations' descriptions, by id
    pub const NAMES: [&str; 12] = [
        "none",
        "renorm: eighth part dropped",
        "two-sum: error with a wrong sign",
        "add: error of a1 + b1 dropped",
        "mul: error of a2 b3 dropped",
        "od x f64: error of a3 b dropped",
        "divide: sixth remainder update skipped",
        "sqrt: two Newton iterations instead of four",
        "dot accumulator: level-3 running error dropped",
        "parse: last part truncated",
        "8-lane renorm: zero test ignored",
        "8-lane two-product: FMA as a plain product (native)",
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

// ---------------------------------------------------------------------------------------------------------------
// the arithmetic, once for f64 and for the lanes
// ---------------------------------------------------------------------------------------------------------------

/// One part position of octo-doubles: `f64` for the scalar `OD`, `V8<S>` for the lanes of `ov::OV<S>`. The
/// operations are IEEE round-to-nearest with `fma` and `fms` fused, so each is bitwise the same on both.
pub(crate) trait Limb: Copy {
    /// a per-lane condition: bool for f64, `M8<S>` for the lanes
    type M: Copy;
    fn zero() -> Self;
    fn splat(x: f64) -> Self;
    fn add(self, o: Self) -> Self;
    fn sub(self, o: Self) -> Self;
    fn mul(self, o: Self) -> Self;
    fn div(self, o: Self) -> Self;
    /// self b + c with one rounding
    fn fma(self, b: Self, c: Self) -> Self;
    /// self b - c with one rounding
    fn fms(self, b: Self, c: Self) -> Self;
    /// the sign bit flipped
    fn neg(self) -> Self;
    fn sqrt(self) -> Self;
    /// 2^floor(log2 |x|) for normal x
    fn pow2_floor(self) -> Self;
    /// self == 0
    fn is_zero(self) -> Self::M;
    /// per lane: t where m, f elsewhere
    fn sel(m: Self::M, t: Self, f: Self) -> Self;
    /// the renormalization of N >= 8 parts to eight (the scalar one branches on zero errors, the lanes' masks them)
    fn renorm<const N: usize>(c: [Self; N]) -> [Self; 8];
    /// f, an `#[inline(always)]` closure, run as a function of its own on the lane backends that need no target
    /// features (`Simd::outline`) and inlined elsewhere: the steps of the operations below
    fn outline<T>(f: impl FnOnce() -> T) -> T;
}

impl Limb for f64 {
    type M = bool;
    #[inline(always)]
    fn zero() -> f64 {
        0.0
    }
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
    fn div(self, o: f64) -> f64 {
        self / o
    }
    #[inline(always)]
    fn fma(self, b: f64, c: f64) -> f64 {
        self.mul_add(b, c)
    }
    #[inline(always)]
    fn fms(self, b: f64, c: f64) -> f64 {
        self.mul_add(b, -c)
    }
    #[inline(always)]
    fn neg(self) -> f64 {
        -self
    }
    #[inline(always)]
    fn sqrt(self) -> f64 {
        f64::sqrt(self)
    }
    #[inline(always)]
    fn pow2_floor(self) -> f64 {
        f64::from_bits(self.to_bits() & 0x7ff0_0000_0000_0000)
    }
    #[inline(always)]
    fn is_zero(self) -> bool {
        self == 0.0
    }
    #[inline(always)]
    fn sel(m: bool, t: f64, f: f64) -> f64 {
        if m {
            t
        } else {
            f
        }
    }
    #[inline(always)]
    fn renorm<const N: usize>(c: [f64; N]) -> [f64; 8] {
        renorm_scalar(c)
    }
    #[inline(always)]
    fn outline<T>(f: impl FnOnce() -> T) -> T {
        f()
    }
}

/// (a + b) as (s, e) with s = RN(a + b), error-free (Knuth's two-sum, as `dd::two_sum`)
#[inline(always)]
pub(crate) fn two_sum<L: Limb>(a: L, b: L) -> (L, L) {
    let s = a.add(b);
    let bb = s.sub(a);
    let x = a.sub(s.sub(bb));
    let y = b.sub(bb);
    if mutate::on(mutate::TWO_SUM_SIGN) {
        (s, x.sub(y))
    } else {
        (s, x.add(y))
    }
}

/// (a + b) as (s, e), error-free when |a| >= |b| (Dekker's fast two-sum, as `dd::quick_two_sum`)
#[inline(always)]
pub(crate) fn quick_two_sum<L: Limb>(a: L, b: L) -> (L, L) {
    let s = a.add(b);
    (s, b.sub(s.sub(a)))
}

/// a b as (p, e), error-free barring underflow (the FMA two-product, as `dd::two_prod`)
#[inline(always)]
pub(crate) fn two_prod<L: Limb>(a: L, b: L) -> (L, L) {
    let p = a.mul(b);
    (p, a.fms(b, p))
}

/// t added into level l of the levels s: two-sums at levels l..K-2, each error carried to the next level, and a
/// plain add at the last level K-1. All levels but the last stay error-free.
#[inline(always)]
fn dep<L: Limb, const K: usize>(s: &mut [L; K], l: usize, t: L) {
    let mut e = t;
    for m in l..K - 1 {
        let (x, y) = two_sum(s[m], e);
        s[m] = x;
        e = y;
    }
    s[K - 1] = s[K - 1].add(e);
}

/// The first pass of the renormalization, from the smallest part up: s = c[N-1], then (s, c[i+1]) = two-sum(c[i],
/// s) for i = N-2 down to 0, and c[0] = s. Error-free (VecSum), whatever the order of the parts' magnitudes.
#[inline(always)]
pub(crate) fn vecsum<L: Limb, const N: usize>(c: [L; N]) -> [L; N] {
    let mut c = c;
    let mut s = c[N - 1];
    for i in (0..N - 1).rev() {
        let (t, e) = two_sum(c[i], s);
        s = t;
        c[i + 1] = e;
    }
    c[0] = s;
    c
}

/// The renormalization of N parts to eight, branching on zero errors (`ov` has the masked twin): the two-sum pass
/// from the smallest part up (`vecsum`), then a quick-two-sum pass from the top that emits a part only where the
/// error is nonzero, and once seven parts are out adds the rest into the eighth. An infinite first part returns the
/// first eight parts as they are.
#[inline(always)]
pub(crate) fn renorm_scalar<const N: usize>(c: [f64; N]) -> [f64; 8] {
    if c[0].is_infinite() {
        return std::array::from_fn(|i| if i < N { c[i] } else { 0.0 });
    }
    let c = vecsum(c);
    let mut out = [0.0f64; 8];
    let mut k = 0;
    let mut acc = c[0];
    for &ci in &c[1..] {
        let (t, e) = quick_two_sum(acc, ci);
        if k < 7 && e != 0.0 {
            out[k] = t;
            k += 1;
            acc = e;
        } else {
            acc = t;
        }
    }
    out[k] = acc;
    if mutate::on(mutate::RENORM_DROP) {
        out[7] = 0.0;
    }
    out
}

/// the eight-part arithmetic on part arrays, for `OD` and `ov::OV`
pub(crate) mod alg {
    use super::{dep, mutate, quick_two_sum, two_prod, two_sum, Limb};

    /// a + b (the default `+`): the parts pairwise by two-sums, the errors carried down nine levels, renormalized
    #[inline(always)]
    pub fn add<L: Limb>(a: &[L; 8], b: &[L; 8]) -> [L; 8] {
        L::outline(
            #[inline(always)]
            || {
                let mut s = [L::zero(); 9];
                let mut t = [L::zero(); 8];
                for i in 0..8 {
                    (s[i], t[i]) = two_sum(a[i], b[i]);
                }
                if mutate::on(mutate::ADD_T1) {
                    t[1] = L::zero();
                }
                s[8] = t[7];
                dep(&mut s, 1, t[0]);
                dep(&mut s, 2, t[1]);
                dep(&mut s, 3, t[2]);
                dep(&mut s, 4, t[3]);
                dep(&mut s, 5, t[4]);
                dep(&mut s, 6, t[5]);
                dep(&mut s, 7, t[6]);
                L::renorm(s)
            },
        )
    }

    /// a + b for an exact f64 b: b down the parts by two-sums, renormalized from nine parts
    #[inline(always)]
    pub fn add_f<L: Limb>(a: &[L; 8], b: L) -> [L; 8] {
        L::outline(
            #[inline(always)]
            || {
                let mut s = [L::zero(); 9];
                let mut e = b;
                for i in 0..8 {
                    (s[i], e) = two_sum(a[i], e);
                }
                s[8] = e;
                L::renorm(s)
            },
        )
    }

    /// a b for an exact f64 b: eight two-products, their errors carried down nine levels, renormalized
    #[inline(always)]
    pub fn mul_f<L: Limb>(a: &[L; 8], b: L) -> [L; 8] {
        L::outline(
            #[inline(always)]
            || {
                let mut s = [L::zero(); 9];
                let mut e = [L::zero(); 8];
                for i in 0..8 {
                    (s[i], e[i]) = two_prod(a[i], b);
                }
                if mutate::on(mutate::MUL_F_E3) {
                    e[3] = L::zero();
                }
                s[8] = e[7];
                dep(&mut s, 1, e[0]);
                dep(&mut s, 2, e[1]);
                dep(&mut s, 3, e[2]);
                dep(&mut s, 4, e[3]);
                dep(&mut s, 5, e[4]);
                dep(&mut s, 6, e[5]);
                dep(&mut s, 7, e[6]);
                L::renorm(s)
            },
        )
    }

    /// a b by order: levels 0..7 hold the partial products of their order and the errors carried into them, all
    /// summed with two-sums, and level 8 the products of order 8 (by FMA) and everything below, in plain f64
    #[inline(always)]
    pub fn expand<L: Limb>(a: &[L; 8], b: &[L; 8]) -> [L; 9] {
        L::outline(
            #[inline(always)]
            || {
                let mut s = [L::zero(); 9];
                let mut e = [L::zero(); 8];
                for j in 0..8 {
                    (s[j], e[j]) = two_prod(a[0], b[j]);
                }
                s[8] = a[7].fma(
                    b[1],
                    a[6].fma(
                        b[2],
                        a[5].fma(b[3], a[4].fma(b[4], a[3].fma(b[5], a[2].fma(b[6], a[1].mul(b[7]))))),
                    ),
                );
                dep(&mut s, 1, e[0]);
                dep(&mut s, 2, e[1]);
                dep(&mut s, 3, e[2]);
                dep(&mut s, 4, e[3]);
                dep(&mut s, 5, e[4]);
                dep(&mut s, 6, e[5]);
                dep(&mut s, 7, e[6]);
                dep(&mut s, 8, e[7]);
                // rows 1..7: a_i b_j into level i + j, its error into level i + j + 1
                macro_rules! pp {
                ($(($i:literal, $j:literal)),*) => {
                    $({
                        let (p, e) = two_prod(a[$i], b[$j]);
                        let e = if $i == 2 && $j == 3 && mutate::on(mutate::MUL_E23) { L::zero() } else { e };
                        dep(&mut s, $i + $j, p);
                        dep(&mut s, $i + $j + 1, e);
                    })*
                };
            }
                pp!((1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6));
                pp!((2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5));
                pp!((3, 0), (3, 1), (3, 2), (3, 3), (3, 4));
                pp!((4, 0), (4, 1), (4, 2), (4, 3));
                pp!((5, 0), (5, 1), (5, 2));
                pp!((6, 0), (6, 1));
                pp!((7, 0));
                s
            },
        )
    }

    /// a b (the default `*`): the nine levels of `expand`, renormalized
    #[inline(always)]
    pub fn mul<L: Limb>(a: &[L; 8], b: &[L; 8]) -> [L; 8] {
        L::renorm(expand(a, b))
    }

    /// r - b q for an f64 q in one pass: r_i - RN(b_i q) by two-sums, those errors and the errors of the products
    /// carried down nine levels, renormalized (the remainder of long division)
    #[inline(always)]
    pub fn sub_mul_f<L: Limb>(r: &[L; 8], b: &[L; 8], q: L) -> [L; 8] {
        L::outline(
            #[inline(always)]
            || {
                let mut s = [L::zero(); 9];
                let mut t = [L::zero(); 8];
                let mut e = [L::zero(); 8];
                for i in 0..8 {
                    let (p, pe) = two_prod(b[i], q);
                    (s[i], t[i]) = two_sum(r[i], p.neg());
                    e[i] = pe.neg();
                }
                s[8] = t[7].add(e[7]);
                macro_rules! carry {
                ($($l:literal),*) => {
                    $(
                        dep(&mut s, $l + 1, t[$l]);
                        dep(&mut s, $l + 1, e[$l]);
                    )*
                };
            }
                carry!(0, 1, 2, 3, 4, 5, 6);
                L::renorm(s)
            },
        )
    }

    /// a / b by long division (QD's accurate divide with nine quotient terms), each quotient term q(r_0) = r_0 / b_0
    /// (so that `ov::OV::div_by` can pass a shared divisor)
    #[inline(always)]
    pub fn div<L: Limb>(a: &[L; 8], b: &[L; 8], q: impl Fn(L) -> L) -> [L; 8] {
        let mut qs = [L::zero(); 9];
        let mut r = *a;
        qs[0] = q(r[0]);
        for k in 1..9 {
            if !(k == 5 && mutate::on(mutate::DIV_REM)) {
                r = sub_mul_f(&r, b, qs[k - 1]);
            }
            qs[k] = q(r[0]);
        }
        L::renorm(qs)
    }

    /// times a power of two, every part
    #[inline(always)]
    pub fn mul_pwr2<L: Limb>(a: &[L; 8], s: L) -> [L; 8] {
        a.map(|v| v.mul(s))
    }

    /// -a: the first part's sign bit flipped, the others as -x + 0, so a zero lower part is +0 (as `QD`'s)
    #[inline(always)]
    pub fn neg<L: Limb>(a: &[L; 8]) -> [L; 8] {
        let z = L::zero();
        std::array::from_fn(|i| if i == 0 { a[0].neg() } else { a[i].neg().add(z) })
    }

    /// The square root: Newton's iteration on 1/sqrt(a), four steps from the f64 value (each about doubling the
    /// correct bits, 53 to 424 in three, the fourth for the rounding), then times a, applied to a scaled by an exact
    /// power of four into [1, 4) and the result scaled back (as `QD::sqrt`). A zero gives zero. The products and sums
    /// are the caller's (`mul`, `add`, `add_f`: the type's own operations, so that they are not inlined here sixteen
    /// times over).
    #[inline(always)]
    pub fn sqrt<L: Limb>(
        x: &[L; 8],
        mul: impl Fn(&[L; 8], &[L; 8]) -> [L; 8],
        add: impl Fn(&[L; 8], &[L; 8]) -> [L; 8],
        add_f: impl Fn(&[L; 8], L) -> [L; 8],
    ) -> [L; 8] {
        let z = L::zero();
        let zero = x[0].is_zero();
        let s = x[0].sqrt().pow2_floor();
        let inv = L::splat(1.0).div(s);
        let a = x.map(|v| v.mul(inv).mul(inv));
        let mut r = [z; 8];
        r[0] = L::splat(1.0).div(a[0].sqrt());
        let h = mul_pwr2(&a, L::splat(0.5));
        let n = if mutate::on(mutate::SQRT_ITER) { 2 } else { 4 };
        for _ in 0..n {
            // r + (1/2 - h r^2) r
            let hr2 = mul(&h, &mul(&r, &r));
            let c = add_f(&neg(&hr2), L::splat(0.5));
            r = add(&r, &mul(&c, &r));
        }
        let r = mul(&r, &a);
        r.map(|v| L::sel(zero, z, v.mul(s)))
    }

    /// the levels of `expand` (or a's parts) added into the running levels acc: level l by two-sums into acc[l],
    /// each error carried down to level 8, which sums in plain f64
    #[inline(always)]
    pub fn acc_levels<L: Limb, const K: usize>(acc: &mut [L; 9], t: &[L; K]) {
        L::outline(
            #[inline(always)]
            || {
                for l in 0..K.min(8) {
                    if l == 3 && mutate::on(mutate::ACC_L3) {
                        let (x, _) = two_sum(acc[3], t[3]);
                        acc[3] = x;
                        continue;
                    }
                    dep(acc, l, t[l]);
                }
                if K > 8 {
                    acc[8] = acc[8].add(t[8]);
                }
            },
        )
    }

    /// quick-two-sum of a0 and the sum of the lower parts (a's value to about 2^-106)
    #[inline(always)]
    pub fn to_dd<L: Limb>(a: &[L; 8]) -> (L, L) {
        let t = a[1].add(a[2].add(a[3].add(a[4].add(a[5].add(a[6].add(a[7]))))));
        quick_two_sum(a[0], t)
    }

    /// the four leading parts, the fourth with the sum of the lower four added (renormalized by the caller)
    #[inline(always)]
    pub fn to_qd_parts<L: Limb>(a: &[L; 8]) -> [L; 4] {
        [a[0], a[1], a[2], a[3].add(a[4].add(a[5].add(a[6].add(a[7]))))]
    }

    /// a0 and the sum of the lower parts (a's nearest f64 to within that sum's rounding)
    #[inline(always)]
    pub fn to_f64_parts<L: Limb>(a: &[L; 8]) -> (L, L) {
        (a[0], a[1].add(a[2].add(a[3].add(a[4].add(a[5].add(a[6].add(a[7])))))))
    }
}

// ---------------------------------------------------------------------------------------------------------------
// the scalar type
// ---------------------------------------------------------------------------------------------------------------

/// Octo-double `x[0] + x[1] + ... + x[7]`.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct OD {
    /// the parts, largest first
    pub x: [f64; 8],
}

impl OD {
    /// 0
    pub const ZERO: OD = OD { x: [0.0; 8] };
    /// 1
    pub const ONE: OD = OD {
        x: [1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
    };
    /// 2^-418, the unit of the error bounds (twice the exponent of QD's 2^-209; the parts hold 424 bits)
    pub const EPS: f64 = f64::from_bits((1023 - 418) << 52);

    /// renormalized from eight parts
    #[inline]
    pub fn new(x: [f64; 8]) -> OD {
        OD { x: renorm_scalar(x) }
    }
    /// exact
    #[inline(always)]
    pub fn from_f64(x: f64) -> OD {
        let mut o = OD::ZERO;
        o.x[0] = x;
        o
    }
    /// exact
    #[inline(always)]
    pub fn from_dd(d: DD) -> OD {
        let mut o = OD::ZERO;
        o.x[0] = d.hi;
        o.x[1] = d.lo;
        o
    }
    /// exact
    #[inline(always)]
    pub fn from_qd(q: QD) -> OD {
        let mut o = OD::ZERO;
        o.x[..4].copy_from_slice(&q.x);
        o
    }
    /// nearest f64 (to within the rounding of the seven lower parts' sum); a zero tail leaves the leading part as it
    /// is, so a zero keeps its sign
    #[inline(always)]
    pub fn to_f64(self) -> f64 {
        let (h, t) = alg::to_f64_parts(&self.x);
        if t == 0.0 {
            h
        } else {
            h + t
        }
    }
    /// double-double, to about 2^-106 relative (as `QD::to_dd`)
    #[inline(always)]
    pub fn to_dd(self) -> DD {
        let (hi, lo) = alg::to_dd(&self.x);
        DD { hi, lo }
    }
    /// quad-double, to about 2^-212 relative: the four leading parts with the lower four's sum added to the fourth,
    /// renormalized (`QD::new`)
    #[inline(always)]
    pub fn to_qd(self) -> QD {
        let [a, b, c, d] = alg::to_qd_parts(&self.x);
        QD::new(a, b, c, d)
    }
    /// the leading part is zero (so, renormalized, every part is)
    #[inline(always)]
    pub fn is_zero(self) -> bool {
        self.x[0] == 0.0
    }
    /// |self|: negated where the leading part is negative
    #[inline(always)]
    pub fn abs(self) -> OD {
        if self.x[0] < 0.0 {
            -self
        } else {
            self
        }
    }
    /// times a power of two b (`dd::is_pwr2`): every part scaled, exact barring overflow and underflow
    #[inline(always)]
    pub fn mul_pwr2(self, b: f64) -> OD {
        debug_assert!(crate::dd::is_pwr2(b), "mul_pwr2: {b} is not a power of two");
        OD {
            x: alg::mul_pwr2(&self.x, b),
        }
    }
    /// od + f64
    #[inline]
    pub fn add_f(self, b: f64) -> OD {
        OD {
            x: alg::add_f(&self.x, b),
        }
    }
    /// od x f64
    #[inline]
    pub fn mul_f(self, b: f64) -> OD {
        OD {
            x: alg::mul_f(&self.x, b),
        }
    }
    /// 1 / self
    #[inline]
    pub fn recip(self) -> OD {
        OD::ONE / self
    }
    /// the square root (Newton's iteration on 1/sqrt(a), see the module doc); a negative value gives NaN
    #[inline]
    pub fn sqrt(self) -> OD {
        let w = |x: &[f64; 8]| OD { x: *x };
        OD {
            x: alg::sqrt(
                &self.x,
                |a, b| (w(a) * w(b)).x,
                |a, b| (w(a) + w(b)).x,
                |a, b| w(a).add_f(b).x,
            ),
        }
    }
    /// integer power: binary powering, 1/a^|n| for n < 0 (as `QD::powi`)
    pub fn powi(self, n: i32) -> OD {
        if n == 0 {
            return OD::ONE;
        }
        let mut r = self;
        let mut s = OD::ONE;
        let mut nn = n.unsigned_abs();
        if nn > 1 {
            while nn > 0 {
                if nn % 2 == 1 {
                    s = s * r;
                }
                nn /= 2;
                if nn > 0 {
                    r = r * r;
                }
            }
        } else {
            s = r;
        }
        if n < 0 {
            OD::ONE / s
        } else {
            s
        }
    }

    /// the exact value of the eight-part sum (finite parts)
    pub fn exact(self) -> Dy {
        Dy::sum(&self.x)
    }

    /// Parse a decimal ("-1.234e-5", "3.14159...", "42"): the exact decimal value rounded to eight parts by greedy
    /// round-to-nearest (x0 = RN(v), x1 = RN(v - x0), ...), so |error| <= ulp(x7)/2 <= 2^-424 |v|.
    ///
    /// ```
    /// use multidouble::od::OD;
    /// let x: OD = "1.4142135623730950488016887242096980785696718753769480731766797379907324784621070388503875343276415727"
    ///     .parse()
    ///     .unwrap();
    /// assert!((x * x - OD::from_f64(2.0)).to_f64().abs() < 1e-99);
    /// ```
    pub fn parse(s: &str) -> Result<OD, String> {
        let mut x = crate::qd::parse_parts::<8>(s, mutate::on(mutate::PARSE_TRUNC))?;
        // a lower part that rounded to zero below the subnormals is +0, as everywhere else
        for v in x[1..].iter_mut() {
            *v += 0.0;
        }
        Ok(OD { x })
    }

    /// Scientific notation with `digits` significant digits, correctly rounded (half to even) from the exact value
    /// of the eight-part sum: "-1.2345e-05" style, at least two exponent digits.
    pub fn to_sci(self, digits: usize) -> String {
        crate::qd::sci_parts(&self.x, digits)
    }
}

impl std::fmt::Display for OD {
    /// 128 significant digits (the eight parts carry about 126)
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_sci(f.precision().map(|p| p + 1).unwrap_or(128)))
    }
}

impl std::str::FromStr for OD {
    type Err = String;
    fn from_str(s: &str) -> Result<OD, String> {
        OD::parse(s)
    }
}

/// Lexicographic on the parts, as the QD library orders quad-doubles; None if a part is NaN. For renormalized values
/// (nonoverlapping parts) this is the order of the values, up to ties at the parts' half-ulp bounds.
impl PartialOrd for OD {
    fn partial_cmp(&self, o: &OD) -> Option<Ordering> {
        for i in 0..8 {
            match self.x[i].partial_cmp(&o.x[i])? {
                Ordering::Equal => continue,
                c => return Some(c),
            }
        }
        Some(Ordering::Equal)
    }
}

impl Neg for OD {
    type Output = OD;
    /// every part negated, the lower seven as -x + 0, so that a zero lower part is +0 (as `QD`'s)
    #[inline(always)]
    fn neg(self) -> OD {
        OD { x: alg::neg(&self.x) }
    }
}

impl Add for OD {
    type Output = OD;
    #[inline]
    fn add(self, b: OD) -> OD {
        OD {
            x: alg::add(&self.x, &b.x),
        }
    }
}

impl Sub for OD {
    type Output = OD;
    #[inline]
    fn sub(self, b: OD) -> OD {
        self + (-b)
    }
}

impl Mul for OD {
    type Output = OD;
    #[inline]
    fn mul(self, b: OD) -> OD {
        OD {
            x: alg::mul(&self.x, &b.x),
        }
    }
}

impl Div for OD {
    type Output = OD;
    #[inline]
    fn div(self, b: OD) -> OD {
        let b0 = b.x[0];
        OD {
            x: alg::div(&self.x, &b.x, |r: f64| r / b0),
        }
    }
}

/// the eight parts of octo-doubles as eight arrays, part k of value i at index i of array k (the layout of
/// `OV::load`), the inverse of `from_parts`
pub fn to_parts(v: &[OD]) -> [Vec<f64>; 8] {
    std::array::from_fn(|k| v.iter().map(|q| q.x[k]).collect())
}

/// octo-doubles from the arrays of their eight parts, the parts as they are (`OD { x }`, not renormalized as
/// `OD::new`). Arrays of different lengths panic.
pub fn from_parts(c: [&[f64]; 8]) -> Vec<OD> {
    let n = c[0].len();
    assert!(
        c.iter().all(|p| p.len() == n),
        "from_parts: the eight arrays must have one length"
    );
    (0..n)
        .map(|i| OD {
            x: std::array::from_fn(|k| c[k][i]),
        })
        .collect()
}

/// Scalar sum-of-products accumulator, the twin of `ov::ODotAcc` (same algorithm, bitwise the same per lane): nine
/// running levels, the first eight summed with two-sums and the last in plain f64. Each product's levels (`expand`,
/// its terms to order 8) are added into them with their errors carried down, so the error of a dot product is mostly
/// that of `finish`.
#[derive(Clone, Copy, Debug, Default)]
pub struct OdAcc {
    /// the running levels, the largest first
    pub s: [f64; 9],
}

impl OdAcc {
    /// the empty sum
    pub fn zero() -> OdAcc {
        OdAcc::default()
    }
    /// self + a b
    #[inline]
    pub fn add_prod(self, a: OD, b: OD) -> OdAcc {
        let t = alg::expand(&a.x, &b.x);
        let mut s = self.s;
        alg::acc_levels(&mut s, &t);
        OdAcc { s }
    }
    /// self + a
    #[inline]
    pub fn add(self, a: OD) -> OdAcc {
        let mut s = self.s;
        alg::acc_levels(&mut s, &a.x);
        OdAcc { s }
    }
    /// the sum as an octo-double: the nine levels added in turn with od + f64
    #[inline]
    pub fn finish(self) -> OD {
        let mut r = OD::from_f64(self.s[0]);
        for l in 1..9 {
            r = r.add_f(self.s[l]);
        }
        r
    }
}
