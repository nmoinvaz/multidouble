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

#[cfg(test)]
mod tests {
    use crate::dd::{quick_two_sum, DD};
    use crate::exact::Dy;
    use crate::od::{renorm_scalar, OD};
    use crate::qd::{renorm4, QD};

    /// splitmix64
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        }
        /// a double-double with a random sign, an exponent in [-e, e] and a full low part
        fn dd(&mut self, e: i32) -> DD {
            let x = 2f64.powi((self.next() % (2 * e as u64 + 1)) as i32 - e)
                * (1.0 + (self.next() >> 11) as f64 / 2f64.powi(53));
            let s = if self.next() & 1 == 0 { 1.0 } else { -1.0 };
            let lo = ((self.next() >> 11) as f64 / 2f64.powi(53) - 0.5) * x * f64::EPSILON;
            DD::new(s * x, lo)
        }
    }

    /// the parts as bits
    fn bits<const N: usize>(x: [f64; N]) -> [u64; N] {
        x.map(f64::to_bits)
    }

    /// parts on the ladder: the first over the exponent range down to the subnormals, each next one a random fraction
    /// of the ulp of the one before (the whole ulp one time in eight), signs at random
    fn laddered<const N: usize>(r: &mut Rng) -> [f64; N] {
        let mut x = [0.0; N];
        x[0] = 2f64.powi((r.next() % 2023) as i32 - 1022) * (1.0 + (r.next() >> 11) as f64 / 2f64.powi(53));
        for k in 1..N {
            let m = if r.next().is_multiple_of(8) {
                1.0
            } else {
                (r.next() >> 11) as f64 / 2f64.powi(53)
            };
            let s = if r.next() & 1 == 0 { 1.0 } else { -1.0 };
            x[k] = if x[k - 1] == 0.0 {
                0.0
            } else {
                s * m * super::ulp(x[k - 1])
            };
        }
        x
    }

    /// r sums exactly to c and is on the ladder, by exact arithmetic
    fn exact_on_ladder(c: &[f64], r: &[f64]) -> bool {
        let ulp = |x: f64| {
            let e = ((x.to_bits() >> 52) & 0x7ff) as i64;
            Dy::from_f64(1.0).ldexp(if e == 0 { -1074 } else { e - 1075 })
        };
        Dy::sum(c).sub(&Dy::sum(r)).is_zero()
            && (0..r.len() - 1).all(|k| {
                if r[k] == 0.0 {
                    r[k + 1] == 0.0
                } else {
                    Dy::from_f64(r[k + 1]).cmp_abs(&ulp(r[k])) != std::cmp::Ordering::Greater
                }
            })
    }

    /// Parts on the ladder take the renormalization as given, whose quick two-sums are then exact and whose result is
    /// on the ladder (the module doc's first path), checked by exact arithmetic. Control: the same parts reversed,
    /// renormalized as given, fail the check.
    #[test]
    fn ladder_parts_renormalize_exactly_onto_the_ladder() {
        let mut r = Rng(2);
        let (mut reversed_fail, n) = (0, 20000);
        for _ in 0..n {
            let q: [f64; 4] = laddered(&mut r);
            assert!(super::on_ladder(&q), "{q:?}");
            let rq = renorm4(q[0], q[1], q[2], q[3]);
            assert!(exact_on_ladder(&q, &rq), "{q:?} gives {rq:?}");
            assert_eq!(bits(QD::new(q[0], q[1], q[2], q[3]).x), bits(rq));
            let o: [f64; 8] = laddered(&mut r);
            assert!(super::on_ladder(&o), "{o:?}");
            let ro = renorm_scalar(o);
            assert!(exact_on_ladder(&o, &ro), "{o:?} gives {ro:?}");
            assert_eq!(bits(OD::new(o).x), bits(ro));
            let p = [q[3], q[2], q[1], q[0]];
            reversed_fail += !exact_on_ladder(&p, &renorm4(p[0], p[1], p[2], p[3])) as usize;
        }
        println!("reversed parts: {reversed_fail} of {n} fail");
        assert!(reversed_fail > n / 10, "control: {reversed_fail} of {n}");
    }

    /// Parts from the arithmetic (largest first, on the ladder, zeros at the end) keep the bits of the constructors
    /// before they took parts in any order: `renorm4`, `renorm_scalar` and the quick two-sum. Control: the same parts
    /// permuted give other bits.
    #[test]
    fn ordered_parts_keep_their_bits() {
        let mut r = Rng(1);
        let (mut permuted_differ, n) = (0, 20000);
        for i in 0..n {
            let (a, b, c) = (r.dd(30), r.dd(30), r.dd(300));
            let d = match i % 3 {
                0 => a * b + c,
                1 => a / b,
                _ => DD::new(a.hi, 0.0),
            };
            // the two-sum's zero low part is +0, where the quick two-sum keeps a -0 low part
            let (h, l) = quick_two_sum(d.hi, d.lo);
            let e = DD::new(d.hi, d.lo);
            assert_eq!(bits([e.hi, e.lo]), bits([h, l + 0.0]), "{d:?}");
            let q = match i % 3 {
                0 => QD::from_dd(a) * QD::from_dd(b) + QD::from_dd(c),
                1 => QD::from_dd(a) / QD::from_dd(b),
                _ => QD::from_dd(a) + QD::from_dd(c),
            };
            let x = q.x;
            assert_eq!(
                bits(QD::new(x[0], x[1], x[2], x[3]).x),
                bits(renorm4(x[0], x[1], x[2], x[3])),
                "{x:?}"
            );
            let o = match i % 3 {
                0 => OD::from_qd(q) * OD::from_dd(c) + OD::from_dd(a),
                1 => OD::from_qd(q) / OD::from_dd(b),
                _ => OD::from_qd(q) - OD::from_dd(a),
            };
            assert_eq!(bits(OD::new(o.x).x), bits(renorm_scalar(o.x)), "{:?}", o.x);
            let p = [o.x[3], o.x[0], o.x[6], o.x[1], o.x[7], o.x[2], o.x[5], o.x[4]];
            permuted_differ += (bits(OD::new(p).x) != bits(renorm_scalar(p))) as usize;
        }
        println!("permuted parts: {permuted_differ} of {n} differ from the renormalization as given");
        assert!(permuted_differ > n / 10, "control: {permuted_differ} of {n}");
    }
}
