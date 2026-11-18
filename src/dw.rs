//! Double-word operations of M. Joldes, J.-M. Muller, V. Popescu, "Tight and rigorous error bounds for basic building
//! blocks of double-word arithmetic", ACM Trans. Math. Softw. 44(2), 2017, doi:10.1145/3121432, written once over the
//! limb type (`f64` for the scalar double-double, `V8` for its lanes), so that the scalar and lane paths perform the same
//! operations. A double-word is (hi, lo), and u = 2^-53.
//!
//! The error-free transformations are this module's own, with no mutation hooks: `od::two_sum` carries one, which
//! would reach `DD::exp`. The two-product's error is `Limb::fms`, as in `dd::two_prod` and `dv::two_prod`.
use crate::od::Limb;

/// a + b as (s, e) with s = RN(a + b), error-free (Knuth's two-sum)
#[inline(always)]
fn two_sum<L: Limb>(a: L, b: L) -> (L, L) {
    let s = a.add(b);
    let bb = s.sub(a);
    (s, a.sub(s.sub(bb)).add(b.sub(bb)))
}

/// a + b as (s, e) for |a| >= |b| or a = 0, error-free (Dekker's fast two-sum)
#[inline(always)]
fn quick_two_sum<L: Limb>(a: L, b: L) -> (L, L) {
    let s = a.add(b);
    (s, b.sub(s.sub(a)))
}

/// a b as (p, e) with p = RN(a b), error-free barring underflow, by one fused multiply-subtract
#[inline(always)]
fn two_prod<L: Limb>(a: L, b: L) -> (L, L) {
    let p = a.mul(b);
    (p, a.fms(b, p))
}

/// a + b for a double-word a and a limb b: DWPlusFP, Algorithm 4 of Joldes, Muller and Popescu (2017), within
/// 2u^2 / (1 - 2u) relative
#[inline(always)]
pub(crate) fn dw_plus_fp<L: Limb>(a: (L, L), b: L) -> (L, L) {
    let (sh, sl) = two_sum(a.0, b);
    let v = a.1.add(sl);
    quick_two_sum(sh, v)
}

/// a b for double-words: DWTimesDW2, Algorithm 11 of Joldes, Muller and Popescu (2017), within 5u^2 / (1 + u)^2
/// relative, the bound J.-M. Muller and L. Rideau proved formally (ACM Trans. Math. Softw. 48(1), 2022,
/// doi:10.1145/3484514). `DD`'s `*` sums its terms in another order, for which no bound is published.
#[inline(always)]
pub(crate) fn dw_times_dw2<L: Limb>(a: (L, L), b: (L, L)) -> (L, L) {
    let (ch, cl1) = two_prod(a.0, b.0);
    let tl = a.0.mul(b.1);
    let cl2 = a.1.fma(b.0, tl);
    quick_two_sum(ch, cl1.add(cl2))
}
