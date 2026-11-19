//! Parts in any order to their exact sum with the parts largest first, for the constructors `QD::new`, `OD::new` and
//! `OV::new`. The result is on the ladder (`on_ladder`): zero parts only after the nonzero ones, and each part at most
//! the ulp of the one before. The constructors take one of three paths (lsb and msb are the exponents of a number's
//! lowest and highest set bits):
//!
//! * Parts already on the ladder, as the arithmetic returns them, are renormalized as given, with the bits the
//!   constructors always gave. Each part is at most 2^-52 of the one before, so each partial sum of VecSum, the first
//!   pass, stays below the next larger part and its quick two-sums are exact. Each error of VecSum is a multiple of
//!   the ulp of the partial sum it rounds and smaller than half the ulp of the partial sum above, so its nonzero
//!   outputs do not overlap, and the second pass below returns them on the ladder.
//! * Other parts are sorted by decreasing magnitude (`by_magnitude`) and renormalized with error-free steps, which is
//!   exact for N parts to N (paper/expansion-error-bounds.pdf, renormalization in any order). The result is kept when
//!   it is on the ladder. Sorting alone does not guarantee that: parts that overlap in one binade can leave the second
//!   part past the ulp of the first (`tests/any_order.rs`, the control without the fallback).
//! * Such a result is replaced by `expansion_sum`, on the ladder for any finite parts. Grow-Expansion (J. R. Shewchuk,
//!   "Adaptive precision floating-point arithmetic and fast robust geometric predicates", Discrete Comput. Geom. 18
//!   (1997) 305-363, doi:10.1007/PL00009321) adds the parts one by one into an expansion whose nonzero components do
//!   not overlap: the msb of each is below the lsb of the next larger one. Every step is a two-sum, so the sum is
//!   exact. Then the renormalization's second pass (the first half of Shewchuk's Compress) runs from the largest
//!   component down.
//!
//! The second pass adds each component w_j into an accumulator A by two-sum, emits the sum t as a part when the error
//! is nonzero, and carries the error on. On components that do not overlap it is exact and on the ladder. A is built
//! from larger components, so it is a multiple of 2^(lsb(w_j) + 1), and lsb(w_j) is the lsb of A + w_j. A step that
//! emits has an inexact A + w_j, whose msb is at least lsb(w_j) + 53, so 2^lsb(w_j) <= ulp(t)/2. The next part rounds
//! the carried error (at most ulp(t)/2) plus components below w_j (together below 2^lsb(w_j)), so it is at most ulp(t).
//!
//! With the cargo feature `mutate`, `mutate::set(id)` breaks the constructors on purpose in the current thread, for
//! the controls of `tests/any_order.rs`; without it the hooks are compile-time `false`.
use crate::dd::two_sum;
use std::cmp::Ordering;

/// Deliberate breakage of the constructors `DD::new`, `QD::new`, `OD::new` and `OV::new` for the controls (feature
/// `mutate`; ids below, 0 = none).
pub mod mutate {
    /// the parts renormalized as given, without the sort and the check: the constructors before they took parts in any
    /// order (`DD::new` by a quick two-sum, `QD::new` by `renorm4`)
    pub const AS_GIVEN: u32 = 1;
    /// the sorted parts' renormalization kept when it is off the ladder (no `expansion_sum`)
    pub const NO_FALLBACK: u32 = 2;
    /// number of ids
    pub const N: u32 = 2;
    /// the mutations' descriptions, by id
    pub const NAMES: [&str; 3] = [
        "none",
        "constructors: parts renormalized as given",
        "constructors: no fallback",
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

/// x sorted by decreasing magnitude, stably: `f64::total_cmp` on `abs`, so that NaN parts come first and infinities
/// next. Parts already in that order are returned as they are, after N - 1 comparisons.
#[inline(always)]
pub(crate) fn by_magnitude<const N: usize>(mut x: [f64; N]) -> [f64; N] {
    if (0..N - 1).all(|k| x[k].abs() >= x[k + 1].abs()) {
        return x;
    }
    for i in 1..N {
        let mut j = i;
        while j > 0 && x[j - 1].abs().total_cmp(&x[j].abs()) == Ordering::Less {
            x.swap(j - 1, j);
            j -= 1;
        }
    }
    x
}

/// ulp(a) exactly for finite a, 2^-1074 for zero and subnormal a, and infinity for infinite or NaN a: the power of two
/// of a's exponent field (at least 2^-1022) times 2^-52
#[inline(always)]
pub(crate) fn ulp(a: f64) -> f64 {
    f64::from_bits(a.to_bits() & 0x7ff0_0000_0000_0000).max(f64::MIN_POSITIVE) * f64::EPSILON
}

/// x is on the ladder: zero parts only after the nonzero ones, and each part at most the ulp of the one before. A
/// quick test without branches, |x_(k+1)| 2^53 <= |x_k| for every k (exact, and so below the ulp), passes most parts
/// from the arithmetic; the others are compared with the ulp.
#[inline(always)]
pub(crate) fn on_ladder<const N: usize>(x: &[f64; N]) -> bool {
    let quick = (0..N - 1).fold(true, |m, k| m & (x[k + 1].abs() * 2f64.powi(53) <= x[k].abs()));
    quick || (0..N - 1).all(|k| x[k + 1] == 0.0 || (x[k] != 0.0 && x[k + 1].abs() <= ulp(x[k])))
}

/// The exact sum of N finite parts in any order as N parts on the ladder (see the module doc): Grow-Expansion, then the
/// pass from the largest component down. Each of the N - 1 steps emits at most one part, so none is lost.
#[cold]
#[inline(never)]
pub(crate) fn expansion_sum<const N: usize>(x: [f64; N]) -> [f64; N] {
    // e[..=m] nonoverlapping, increasing in magnitude, zeros allowed
    let mut e = [0.0f64; N];
    for m in 0..N {
        let mut q = x[m];
        for c in e.iter_mut().take(m) {
            let (s, h) = two_sum(q, *c);
            *c = h;
            q = s;
        }
        e[m] = q;
    }
    let mut out = [0.0f64; N];
    let mut k = 0;
    let mut acc = e[N - 1];
    for i in (0..N - 1).rev() {
        let (t, err) = two_sum(acc, e[i]);
        if err != 0.0 {
            out[k] = t;
            k += 1;
            acc = err;
        } else {
            acc = t;
        }
    }
    out[k] = acc;
    out
}

/// The constructors' paths (see the module doc): `renorm`, the renormalization as the arithmetic runs it, for parts on
/// the ladder; otherwise the parts sorted and renormalized by `renorm_exact` (exact for N parts to N), kept when on the
/// ladder or not finite, and `expansion_sum` of the sorted parts when not.
#[inline(always)]
pub(crate) fn exact_sum<const N: usize>(
    x: [f64; N],
    renorm: impl FnOnce([f64; N]) -> [f64; N],
    renorm_exact: impl FnOnce([f64; N]) -> [f64; N],
) -> [f64; N] {
    if on_ladder(&x) {
        return renorm(x);
    }
    let c = by_magnitude(x);
    let r = renorm_exact(c);
    if !r[0].is_finite() || on_ladder(&r) || mutate::on(mutate::NO_FALLBACK) {
        r
    } else {
        expansion_sum(c)
    }
}

