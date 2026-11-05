//! 8 lanes of octo-double: eight `V8` registers (structure of arrays, part k of the 8 lanes in `c[k]`), with the
//! algorithms of the scalar `od::OD` and bitwise the same results lane by lane, on every `v8` backend (AVX-512,
//! AVX2, SSE2, NEON, portable).
//!
//! The arithmetic is `od::alg`, written once over `od::Limb` and run here on `V8<S>`: the same IEEE operations in the
//! same order, with the fused multiply-subtract of two-product as `V8::fms` (one fused instruction on AVX-512, AVX2
//! and NEON, `f64::mul_add` per lane on SSE2 and portable), so each lane is the scalar computation bit for bit. The
//! one data-dependent branch, the renormalization's test for a zero error, is run on all lanes with masks: a per-lane
//! slot index k (as f64) says which part an emitted value goes to, every slot is updated by a select where k equals
//! it, and lanes whose error is zero keep accumulating, as `od::renorm_scalar` does with its branch.
//!
//! `ODotAcc` is the 8-lane twin of `od::OdAcc`: each product's nine levels (`od::alg::expand`) added into nine
//! running levels with two-sums, the last level plain, so a dot product errs by little more than its `finish`.
//!
//! The large operations run inside `Simd::vectorize` and are not forced inline (an octo-double product is about a
//! thousand lane operations), so a copy the compiler keeps out of line still runs with the backend's instructions.
use crate::dd::DD;
use crate::dv::DV;
use crate::od::{alg, mutate, quick_two_sum, vecsum, Limb, OD};
use crate::qd::QD;
use crate::qv::QV;
use crate::simd::{Native, Simd};
use crate::v8::{Divisor, M8, V8};
use std::ops::{Add, Div, Mul, Neg, Sub};

/// Eight octo-doubles, part k of lane j at `c[k]` lane j.
#[derive(Clone, Copy, Debug)]
pub struct OV<S: Simd> {
    pub c: [V8<S>; 8],
}

impl<S: Simd> Limb for V8<S> {
    type M = M8<S>;
    #[inline(always)]
    fn zero() -> Self {
        V8::zero()
    }
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
    fn div(self, o: Self) -> Self {
        V8::div(self, o)
    }
    #[inline(always)]
    fn fma(self, b: Self, c: Self) -> Self {
        V8::fma(self, b, c)
    }
    #[inline(always)]
    fn fms(self, b: Self, c: Self) -> Self {
        if mutate::on(mutate::OV_FMA_PLAIN) && S::NAME == Native::NAME {
            V8::sub(V8::mul(self, b), c)
        } else {
            V8::fms(self, b, c)
        }
    }
    #[inline(always)]
    fn neg(self) -> Self {
        V8::neg(self)
    }
    #[inline(always)]
    fn sqrt(self) -> Self {
        V8::sqrt(self)
    }
    #[inline(always)]
    fn pow2_floor(self) -> Self {
        V8::pow2_floor(self)
    }
    #[inline(always)]
    fn is_zero(self) -> M8<S> {
        self.eq(V8::zero())
    }
    #[inline(always)]
    fn sel(m: M8<S>, t: Self, f: Self) -> Self {
        m.sel(t, f)
    }
    #[inline(always)]
    fn renorm<const N: usize>(c: [Self; N]) -> [Self; 8] {
        S::outline(
            #[inline(always)]
            || renorm_lanes(c),
        )
    }
    #[inline(always)]
    fn outline<T>(f: impl FnOnce() -> T) -> T {
        S::outline(f)
    }
}

/// The renormalization of N parts to eight on all lanes, bitwise `od::renorm_scalar` per lane (see the module doc):
/// the slot index k held as f64, each emitted value stored where k equals the slot.
#[inline(always)]
fn renorm_lanes<S: Simd, const N: usize>(c: [V8<S>; N]) -> [V8<S>; 8] {
    let z = V8::<S>::zero();
    let one = V8::splat(1.0);
    let seven = V8::splat(7.0);
    let inf = c[0].abs().eq(V8::splat(f64::INFINITY));
    let orig = c;
    let c = vecsum(c);
    let mut out = [z; 8];
    let mut k = z;
    let mut acc = c[0];
    for i in 1..N {
        let (t, e) = quick_two_sum(acc, c[i]);
        // k < 7 and a nonzero error: t goes to slot k, k advances, e carries on
        let room = seven.gt(k);
        let emit = if mutate::on(mutate::OV_RENORM_MASK) {
            room
        } else {
            room.and_ne(e, z)
        };
        // before this step k <= i - 1, and an emitting lane has k <= 6
        for m in 0..i.min(7) {
            out[m] = emit.and_eq(k, V8::splat(m as f64)).sel(t, out[m]);
        }
        acc = emit.sel(e, t);
        k = k.add_where(emit, one);
    }
    for m in 0..N.min(8) {
        out[m] = k.eq(V8::splat(m as f64)).sel(acc, out[m]);
    }
    if mutate::on(mutate::RENORM_DROP) {
        out[7] = z;
    }
    std::array::from_fn(|m| inf.sel(if m < N { orig[m] } else { z }, out[m]))
}

impl<S: Simd> OV<S> {
    #[inline(always)]
    pub fn zero() -> Self {
        OV { c: [V8::zero(); 8] }
    }
    #[inline(always)]
    pub fn splat(x: OD) -> Self {
        OV { c: x.x.map(V8::splat) }
    }
    #[inline(always)]
    pub fn splat_f(x: f64) -> Self {
        OV::splat(OD::from_f64(x))
    }
    #[inline(always)]
    pub fn splat_dd(x: DD) -> Self {
        OV::splat(OD::from_dd(x))
    }
    #[inline(always)]
    pub fn splat_qd(x: QD) -> Self {
        OV::splat(OD::from_qd(x))
    }
    /// exact
    #[inline(always)]
    pub fn from_v8(x: V8<S>) -> Self {
        let mut c = [V8::zero(); 8];
        c[0] = x;
        OV { c }
    }
    /// exact
    #[inline(always)]
    pub fn from_dv(x: DV<S>) -> Self {
        let mut c = [V8::zero(); 8];
        c[0] = x.hi;
        c[1] = x.lo;
        OV { c }
    }
    /// exact
    #[inline(always)]
    pub fn from_qv(x: QV<S>) -> Self {
        let mut c = [V8::zero(); 8];
        c[..4].copy_from_slice(&x.c);
        OV { c }
    }
    /// double-double, to about 2^-106 relative (as `OD::to_dd`)
    #[inline(always)]
    pub fn to_dv(self) -> DV<S> {
        let (hi, lo) = alg::to_dd(&self.c);
        DV { hi, lo }
    }
    /// quad-double, to about 2^-212 relative (as `OD::to_qd`)
    #[inline(always)]
    pub fn to_qv(self) -> QV<S> {
        let [a, b, c, d] = alg::to_qd_parts(&self.c);
        QV {
            c: crate::qv::renorm4(a, b, c, d),
        }
    }
    /// nearest f64 (as `OD::to_f64`: a zero tail leaves the leading part as it is, so a zero keeps its sign)
    #[inline(always)]
    pub fn to_v8(self) -> V8<S> {
        let (h, t) = alg::to_f64_parts(&self.c);
        t.eq(V8::zero()).sel(h, h.add(t))
    }
    /// from the eight parts' arrays (8 values each)
    #[inline(always)]
    pub fn load(c: [&[f64]; 8]) -> Self {
        OV { c: c.map(V8::load) }
    }
    /// into the eight parts' arrays (8 values each)
    #[inline(always)]
    pub fn store(self, c: [&mut [f64]; 8]) {
        for (v, s) in self.c.iter().zip(c) {
            v.store(s);
        }
    }
    pub fn from_lanes(x: &[OD; 8]) -> Self {
        OV {
            c: std::array::from_fn(|k| V8::from_array(std::array::from_fn(|j| x[j].x[k]))),
        }
    }
    #[inline(always)]
    pub fn lane(self, j: usize) -> OD {
        OD {
            x: self.c.map(|v| v.to_array()[j]),
        }
    }
    pub fn lanes(self) -> [OD; 8] {
        let a = self.c.map(|v| v.to_array());
        std::array::from_fn(|j| OD {
            x: std::array::from_fn(|k| a[k][j]),
        })
    }
    /// all lanes = lane j
    #[inline(always)]
    pub fn bcast(self, j: usize) -> Self {
        OV {
            c: self.c.map(|v| v.bcast(j)),
        }
    }
    /// |leading part|
    #[inline(always)]
    pub fn abs_hi(self) -> V8<S> {
        self.c[0].abs()
    }
    /// |self|: negated where the leading part is negative (as `OD::abs`)
    #[inline]
    pub fn abs(self) -> Self {
        S::vectorize(
            #[inline(always)]
            || {
                let neg = V8::zero().gt(self.c[0]);
                let n = -self;
                OV {
                    c: std::array::from_fn(|k| neg.sel(n.c[k], self.c[k])),
                }
            },
        )
    }
    /// times a power of two b (`dd::is_pwr2`): every part scaled, exact barring overflow and underflow
    #[inline(always)]
    pub fn mul_pwr2(self, b: f64) -> Self {
        debug_assert!(crate::dd::is_pwr2(b), "mul_pwr2: {b} is not a power of two");
        OV {
            c: alg::mul_pwr2(&self.c, V8::splat(b)),
        }
    }
    /// od + exact f64 vector, as `OD::add_f`
    #[inline]
    pub fn add_v(self, b: V8<S>) -> Self {
        S::vectorize(
            #[inline(always)]
            || OV {
                c: alg::add_f(&self.c, b),
            },
        )
    }
    #[inline]
    pub fn add_f(self, b: f64) -> Self {
        self.add_v(V8::splat(b))
    }
    /// times an exact f64 vector, as `OD::mul_f`
    #[inline]
    pub fn mul_v(self, b: V8<S>) -> Self {
        S::vectorize(
            #[inline(always)]
            || OV {
                c: alg::mul_f(&self.c, b),
            },
        )
    }
    #[inline]
    pub fn mul_f(self, b: f64) -> Self {
        self.mul_v(V8::splat(b))
    }
    /// self / b for r = b.c\[0\].divisor(), bitwise the same as `/`. Its nine quotients by b.c\[0\] go through r, so
    /// several divisions by one b share it (on AVX-512 its reciprocal).
    #[inline]
    pub fn div_by(self, b: Self, r: Divisor<S>) -> Self {
        S::vectorize(
            #[inline(always)]
            || OV {
                c: alg::div(&self.c, &b.c, |x: V8<S>| x.div_by(r)),
            },
        )
    }
    #[inline]
    pub fn recip(self) -> Self {
        OV::splat_f(1.0) / self
    }
    /// the square root, as `OD::sqrt` (zero lanes give zero)
    #[inline]
    pub fn sqrt(self) -> Self {
        S::vectorize(
            #[inline(always)]
            || {
                let w = |c: &[V8<S>; 8]| OV { c: *c };
                OV {
                    c: alg::sqrt(
                        &self.c,
                        |a, b| (w(a) * w(b)).c,
                        |a, b| (w(a) + w(b)).c,
                        |a, b| w(a).add_v(b).c,
                    ),
                }
            },
        )
    }
    /// per lane self < o, lexicographic on the parts (as `OD`'s `PartialOrd`)
    #[inline]
    pub fn lt(self, o: Self) -> M8<S> {
        let mut r = self.c[7].gt(self.c[7]); // all false
        let mut eq = self.c[0].eq(self.c[0]).or(self.c[0].ne(self.c[0])); // all true
        for k in 0..8 {
            r = r.or(eq.and(o.c[k].gt(self.c[k])));
            eq = eq.and_eq(self.c[k], o.c[k]);
        }
        r
    }
    /// per lane self > o
    #[inline]
    pub fn gt(self, o: Self) -> M8<S> {
        o.lt(self)
    }
    /// per lane every part equal (so -0 equals +0, and a NaN part is unequal)
    #[inline]
    pub fn eq(self, o: Self) -> M8<S> {
        let mut eq = self.c[0].eq(o.c[0]);
        for k in 1..8 {
            eq = eq.and_eq(self.c[k], o.c[k]);
        }
        eq
    }
    /// per lane self <= o (no part NaN)
    #[inline]
    pub fn le(self, o: Self) -> M8<S> {
        self.lt(o).or(self.eq(o))
    }
    /// per lane self >= o (no part NaN)
    #[inline]
    pub fn ge(self, o: Self) -> M8<S> {
        o.le(self)
    }
}

impl<S: Simd> Neg for OV<S> {
    type Output = Self;
    /// as `OD`'s: the leading part's sign bit flipped, the lower seven as -x + 0 (a zero lower part is +0)
    #[inline(always)]
    fn neg(self) -> Self {
        OV { c: alg::neg(&self.c) }
    }
}

impl<S: Simd> Add for OV<S> {
    type Output = Self;
    #[inline]
    fn add(self, b: Self) -> Self {
        S::vectorize(
            #[inline(always)]
            || OV {
                c: alg::add(&self.c, &b.c),
            },
        )
    }
}

impl<S: Simd> Sub for OV<S> {
    type Output = Self;
    #[inline]
    fn sub(self, b: Self) -> Self {
        self + (-b)
    }
}

impl<S: Simd> Mul for OV<S> {
    type Output = Self;
    #[inline]
    fn mul(self, b: Self) -> Self {
        S::vectorize(
            #[inline(always)]
            || OV {
                c: alg::mul(&self.c, &b.c),
            },
        )
    }
}

impl<S: Simd> Div for OV<S> {
    type Output = Self;
    #[inline]
    fn div(self, b: Self) -> Self {
        S::vectorize(
            #[inline(always)]
            || OV {
                c: alg::div(&self.c, &b.c, |x: V8<S>| x.div(b.c[0])),
            },
        )
    }
}

/// Accumulator for sums of octo-double products (see the module doc); the 8-lane twin of `od::OdAcc`.
#[derive(Clone, Copy, Debug)]
pub struct ODotAcc<S: Simd> {
    pub s: [V8<S>; 9],
}

impl<S: Simd> ODotAcc<S> {
    #[inline(always)]
    pub fn zero() -> Self {
        ODotAcc { s: [V8::zero(); 9] }
    }
    /// self + a b
    #[inline]
    pub fn add_prod(self, a: OV<S>, b: OV<S>) -> Self {
        S::vectorize(
            #[inline(always)]
            || {
                let t = alg::expand(&a.c, &b.c);
                let mut s = self.s;
                alg::acc_levels(&mut s, &t);
                ODotAcc { s }
            },
        )
    }
    /// self + a
    #[inline]
    pub fn add(self, a: OV<S>) -> Self {
        S::vectorize(
            #[inline(always)]
            || {
                let mut s = self.s;
                alg::acc_levels(&mut s, &a.c);
                ODotAcc { s }
            },
        )
    }
    /// the sum as octo-doubles: the nine levels added in turn with od + f64 (as `OdAcc::finish`)
    #[inline]
    pub fn finish(self) -> OV<S> {
        S::vectorize(
            #[inline(always)]
            || {
                let mut r = OV::from_v8(self.s[0]);
                for l in 1..9 {
                    r = OV {
                        c: alg::add_f(&r.c, self.s[l]),
                    };
                }
                r
            },
        )
    }
}
