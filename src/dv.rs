//! 8 lanes of double-double: (hi, lo) as two `V8`. The algorithms are the QD library's accurate ("IEEE") add,
//! the FMA two-product multiply and the three-quotient divide, so every operation is accurate to a few units of
//! 2^-104 relative.
//!
//! `DotAcc` accumulates a sum of double-double products as (s, err): each product is formed exactly to ~2^-104,
//! its leading part is added to s with an error-free two-sum and all error terms go into err (Ogita-Rump-Oishi
//! Sum2 style). The result carries ~2^-104 relative to the sum of |terms|, at half the cost of chained DD adds.
use crate::dd::DD;
use crate::simd::Simd;
use crate::v8::V8;
use std::ops::{Add, Div, Mul, Neg, Sub};

#[derive(Clone, Copy, Debug)]
pub struct DV<S: Simd> {
    pub hi: V8<S>,
    pub lo: V8<S>,
}

#[inline(always)]
pub fn two_sum<S: Simd>(a: V8<S>, b: V8<S>) -> (V8<S>, V8<S>) {
    let s = a.add(b);
    let bb = s.sub(a);
    (s, a.sub(s.sub(bb)).add(b.sub(bb)))
}

#[inline(always)]
pub fn quick_two_sum<S: Simd>(a: V8<S>, b: V8<S>) -> (V8<S>, V8<S>) {
    let s = a.add(b);
    (s, b.sub(s.sub(a)))
}

#[inline(always)]
pub fn two_prod<S: Simd>(a: V8<S>, b: V8<S>) -> (V8<S>, V8<S>) {
    let p = a.mul(b);
    (p, a.fms(b, p))
}

impl<S: Simd> DV<S> {
    #[inline(always)]
    pub fn zero() -> Self {
        DV {
            hi: V8::zero(),
            lo: V8::zero(),
        }
    }
    #[inline(always)]
    pub fn splat(x: DD) -> Self {
        DV {
            hi: V8::splat(x.hi),
            lo: V8::splat(x.lo),
        }
    }
    #[inline(always)]
    pub fn splat_f(x: f64) -> Self {
        DV {
            hi: V8::splat(x),
            lo: V8::zero(),
        }
    }
    #[inline(always)]
    pub fn load(hi: &[f64], lo: &[f64]) -> Self {
        DV {
            hi: V8::load(hi),
            lo: V8::load(lo),
        }
    }
    #[inline(always)]
    pub fn store(self, hi: &mut [f64], lo: &mut [f64]) {
        self.hi.store(hi);
        self.lo.store(lo);
    }
    #[inline(always)]
    pub fn lane(self, j: usize) -> DD {
        DD {
            hi: self.hi.to_array()[j],
            lo: self.lo.to_array()[j],
        }
    }
    #[inline(always)]
    pub fn bcast(self, j: usize) -> Self {
        DV {
            hi: self.hi.bcast(j),
            lo: self.lo.bcast(j),
        }
    }
    /// times an exact f64 vector
    #[inline(always)]
    pub fn mul_v(self, b: V8<S>) -> Self {
        let (p, e) = two_prod(self.hi, b);
        let e = self.lo.fma(b, e);
        let (h, l) = quick_two_sum(p, e);
        DV { hi: h, lo: l }
    }
    #[inline(always)]
    pub fn mul_f(self, b: f64) -> Self {
        self.mul_v(V8::splat(b))
    }
    /// times a power of two b, as `DD::mul_pwr2`: both parts scaled, exact barring overflow and underflow
    #[inline(always)]
    pub fn mul_pwr2(self, b: f64) -> Self {
        debug_assert!(crate::dd::is_pwr2(b), "mul_pwr2: {b} is not a power of two");
        let c = V8::splat(b);
        DV {
            hi: self.hi.mul(c),
            lo: self.lo.mul(c),
        }
    }
    #[inline(always)]
    pub fn add_v(self, b: V8<S>) -> Self {
        let (s, e) = two_sum(self.hi, b);
        let e = e.add(self.lo);
        let (h, l) = quick_two_sum(s, e);
        DV { hi: h, lo: l }
    }
    #[inline(always)]
    pub fn abs_hi(self) -> V8<S> {
        self.hi.abs()
    }
}

impl<S: Simd> Add for DV<S> {
    type Output = Self;
    #[inline(always)]
    fn add(self, b: Self) -> Self {
        let (s, e) = two_sum(self.hi, b.hi);
        let (t, f) = two_sum(self.lo, b.lo);
        let e = e.add(t);
        let (s, e) = quick_two_sum(s, e);
        let e = e.add(f);
        let (h, l) = quick_two_sum(s, e);
        DV { hi: h, lo: l }
    }
}

impl<S: Simd> Neg for DV<S> {
    type Output = Self;
    #[inline(always)]
    /// as DD's: the sign bit of hi flipped, lo as -lo + 0 (a zero lo is +0)
    fn neg(self) -> Self {
        DV {
            hi: self.hi.neg(),
            lo: self.lo.neg().add(V8::zero()),
        }
    }
}

impl<S: Simd> Sub for DV<S> {
    type Output = Self;
    #[inline(always)]
    fn sub(self, b: Self) -> Self {
        self + (-b)
    }
}

impl<S: Simd> Mul for DV<S> {
    type Output = Self;
    #[inline(always)]
    fn mul(self, b: Self) -> Self {
        let (p, e) = two_prod(self.hi, b.hi);
        let e = self.hi.fma(b.lo, e);
        let e = self.lo.fma(b.hi, e);
        let (h, l) = quick_two_sum(p, e);
        DV { hi: h, lo: l }
    }
}

impl<S: Simd> Div for DV<S> {
    type Output = Self;
    #[inline(always)]
    fn div(self, b: Self) -> Self {
        let q1 = self.hi.div(b.hi);
        let r = self - b.mul_v(q1);
        let q2 = r.hi.div(b.hi);
        let r = r - b.mul_v(q2);
        let q3 = r.hi.div(b.hi);
        let (q1, q2) = quick_two_sum(q1, q2);
        DV { hi: q1, lo: q2 }.add_v(q3)
    }
}

/// Accumulator for sums of double-double products (see the module doc).
#[derive(Clone, Copy, Debug)]
pub struct DotAcc<S: Simd> {
    pub s: V8<S>,
    pub e: V8<S>,
}

impl<S: Simd> DotAcc<S> {
    #[inline(always)]
    pub fn zero() -> Self {
        DotAcc {
            s: V8::zero(),
            e: V8::zero(),
        }
    }
    /// self + a * b
    #[inline(always)]
    pub fn add_prod(self, a: DV<S>, b: DV<S>) -> Self {
        let (p, pe) = two_prod(a.hi, b.hi);
        let pe = a.hi.fma(b.lo, pe);
        let pe = a.lo.fma(b.hi, pe);
        let (s, t) = two_sum(self.s, p);
        DotAcc {
            s,
            e: self.e.add(t.add(pe)),
        }
    }
    /// self + a
    #[inline(always)]
    pub fn add(self, a: DV<S>) -> Self {
        let (s, t) = two_sum(self.s, a.hi);
        DotAcc {
            s,
            e: self.e.add(t.add(a.lo)),
        }
    }
    #[inline(always)]
    pub fn finish(self) -> DV<S> {
        // s and e may be of comparable size after cancellation: a full two-sum, not the quick one
        let (h, l) = two_sum(self.s, self.e);
        DV { hi: h, lo: l }
    }
}
