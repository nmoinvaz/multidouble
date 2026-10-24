//! Lane types for code that is written once and run in several arithmetics, with or without derivatives: the trait
//! [`Lane`] is 8 values of a computation (8 grid points, 8 independent problems, ...), and its implementations are
//!
//! * `DV`: values (double-double).
//! * `Du`: value + one forward-mode tangent (v + d eps, eps^2 = 0), both double-double. One evaluation with a
//!   unit tangent on one unknown gives one exact Jacobian column.
//! * `F8`, `Fu`: the same in plain f64 (one `V8` per value / tangent), for the mixed-precision Newton's f64 Jacobian.
//!   Constants and inputs, which the trait passes as double-double, enter as their hi parts.
//! * `Dtn<N>`: a double-double value with N plain-f64 tangents: N Jacobian columns from one evaluation, the base
//!   trajectory computed once (and to double-double accuracy) for all of them.
//!
//! Each lane type is generic over the backend (`crate::simd`), which `Lane::S` names, so that code generic over
//! `Lane` runs on the instruction set [`crate::simd::dispatch`] picks.
use crate::dd::DD;
use crate::dv::{DotAcc, DV};
use crate::simd::Simd;
use crate::v8::V8;
use std::ops::{Add, Div, Mul, Neg, Sub};

pub trait Lane:
    Copy
    + Send
    + Sync
    + 'static
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
    + Neg<Output = Self>
{
    /// the backend the lanes run on
    type S: Simd;
    type Acc: Copy;
    const TANGENT: bool;
    /// values in plain f64 (`F8`, `Fu`): double-double constants and inputs enter rounded to their hi parts
    const VAL_F64: bool = false;
    /// tangents in plain f64 (`Fu`, `Dtn`)
    const TAN_F64: bool = false;
    /// number of f64 tangents (`tan64`; 0 unless TAN_F64)
    const NT: usize = 0;
    fn zero() -> Self;
    /// a constant (zero tangent)
    fn cst(c: DV<Self::S>) -> Self;
    #[inline(always)]
    fn splat(x: DD) -> Self {
        Self::cst(DV::splat(x))
    }
    /// times a constant lane vector
    fn mulc(self, c: DV<Self::S>) -> Self;
    /// times a scalar constant
    #[inline(always)]
    fn muls(self, s: DD) -> Self {
        self.mulc(DV::splat(s))
    }
    /// times an exact f64 (small integers, 1/2)
    fn mulf(self, s: f64) -> Self;
    /// times a power of two s (`dd::is_pwr2`): every part, value and tangents, scaled exactly (barring overflow and
    /// underflow), so bitwise `mulf(s)`; for computing in a variable rescaled by 2^k, e.g. a power series in x / 2^k
    /// whose coefficients would overflow in x
    fn mul_pwr2(self, s: f64) -> Self;
    /// plus a constant lane vector
    fn addc(self, c: DV<Self::S>) -> Self;
    /// all 8 lanes = lane j
    fn bcast(self, j: usize) -> Self;
    fn val(self) -> DV<Self::S>;
    fn tan(self) -> DV<Self::S>;
    fn from_vt(v: DV<Self::S>, t: DV<Self::S>) -> Self;
    fn acc0() -> Self::Acc;
    /// a + x y
    fn acc(a: Self::Acc, x: Self, y: Self) -> Self::Acc;
    /// a + x c, c constant
    fn accc(a: Self::Acc, x: Self, c: DV<Self::S>) -> Self::Acc;
    /// a + x
    fn acc1(a: Self::Acc, x: Self) -> Self::Acc;
    fn fin(a: Self::Acc) -> Self;
    /// f64 tangent k < NT (TAN_F64 lanes)
    #[inline(always)]
    fn tan64(self, _k: usize) -> V8<Self::S> {
        unreachable!("no f64 tangents")
    }
    /// set f64 tangent k < NT (TAN_F64 lanes)
    #[inline(always)]
    fn set_tan64(&mut self, _k: usize, _t: V8<Self::S>) {
        unreachable!("no f64 tangents")
    }
}

impl<S: Simd> Lane for DV<S> {
    type S = S;
    type Acc = DotAcc<S>;
    const TANGENT: bool = false;
    #[inline(always)]
    fn zero() -> Self {
        DV::zero()
    }
    #[inline(always)]
    fn cst(c: DV<S>) -> Self {
        c
    }
    #[inline(always)]
    fn mulc(self, c: DV<S>) -> Self {
        self * c
    }
    #[inline(always)]
    fn mulf(self, s: f64) -> Self {
        self.mul_f(s)
    }
    #[inline(always)]
    fn mul_pwr2(self, s: f64) -> Self {
        DV::mul_pwr2(self, s)
    }
    #[inline(always)]
    fn addc(self, c: DV<S>) -> Self {
        self + c
    }
    #[inline(always)]
    fn bcast(self, j: usize) -> Self {
        DV::bcast(self, j)
    }
    #[inline(always)]
    fn val(self) -> DV<S> {
        self
    }
    #[inline(always)]
    fn tan(self) -> DV<S> {
        DV::zero()
    }
    #[inline(always)]
    fn from_vt(v: DV<S>, _t: DV<S>) -> Self {
        v
    }
    #[inline(always)]
    fn acc0() -> DotAcc<S> {
        DotAcc::zero()
    }
    #[inline(always)]
    fn acc(a: DotAcc<S>, x: Self, y: Self) -> DotAcc<S> {
        a.add_prod(x, y)
    }
    #[inline(always)]
    fn accc(a: DotAcc<S>, x: Self, c: DV<S>) -> DotAcc<S> {
        a.add_prod(x, c)
    }
    #[inline(always)]
    fn acc1(a: DotAcc<S>, x: Self) -> DotAcc<S> {
        a.add(x)
    }
    #[inline(always)]
    fn fin(a: DotAcc<S>) -> Self {
        a.finish()
    }
}

/// Forward-mode dual number over double-double lanes.
#[derive(Clone, Copy, Debug)]
pub struct Du<S: Simd> {
    pub v: DV<S>,
    pub d: DV<S>,
}

impl<S: Simd> Add for Du<S> {
    type Output = Self;
    #[inline(always)]
    fn add(self, o: Du<S>) -> Du<S> {
        Du {
            v: self.v + o.v,
            d: self.d + o.d,
        }
    }
}
impl<S: Simd> Sub for Du<S> {
    type Output = Self;
    #[inline(always)]
    fn sub(self, o: Du<S>) -> Du<S> {
        Du {
            v: self.v - o.v,
            d: self.d - o.d,
        }
    }
}
impl<S: Simd> Neg for Du<S> {
    type Output = Self;
    #[inline(always)]
    fn neg(self) -> Du<S> {
        Du { v: -self.v, d: -self.d }
    }
}
impl<S: Simd> Mul for Du<S> {
    type Output = Self;
    #[inline(always)]
    fn mul(self, o: Du<S>) -> Du<S> {
        let d = DotAcc::zero().add_prod(self.v, o.d).add_prod(self.d, o.v).finish();
        Du { v: self.v * o.v, d }
    }
}
impl<S: Simd> Div for Du<S> {
    type Output = Self;
    #[inline(always)]
    fn div(self, o: Du<S>) -> Du<S> {
        let q = self.v / o.v;
        Du {
            v: q,
            d: (self.d - q * o.d) / o.v,
        }
    }
}

impl<S: Simd> Lane for Du<S> {
    type S = S;
    type Acc = (DotAcc<S>, DotAcc<S>);
    const TANGENT: bool = true;
    #[inline(always)]
    fn zero() -> Self {
        Du {
            v: DV::zero(),
            d: DV::zero(),
        }
    }
    #[inline(always)]
    fn cst(c: DV<S>) -> Self {
        Du { v: c, d: DV::zero() }
    }
    #[inline(always)]
    fn mulc(self, c: DV<S>) -> Self {
        Du {
            v: self.v * c,
            d: self.d * c,
        }
    }
    #[inline(always)]
    fn mulf(self, s: f64) -> Self {
        Du {
            v: self.v.mul_f(s),
            d: self.d.mul_f(s),
        }
    }
    #[inline(always)]
    fn mul_pwr2(self, s: f64) -> Self {
        Du {
            v: self.v.mul_pwr2(s),
            d: self.d.mul_pwr2(s),
        }
    }
    #[inline(always)]
    fn addc(self, c: DV<S>) -> Self {
        Du {
            v: self.v + c,
            d: self.d,
        }
    }
    #[inline(always)]
    fn bcast(self, j: usize) -> Self {
        Du {
            v: self.v.bcast(j),
            d: self.d.bcast(j),
        }
    }
    #[inline(always)]
    fn val(self) -> DV<S> {
        self.v
    }
    #[inline(always)]
    fn tan(self) -> DV<S> {
        self.d
    }
    #[inline(always)]
    fn from_vt(v: DV<S>, t: DV<S>) -> Self {
        Du { v, d: t }
    }
    #[inline(always)]
    fn acc0() -> Self::Acc {
        (DotAcc::zero(), DotAcc::zero())
    }
    #[inline(always)]
    fn acc(a: Self::Acc, x: Self, y: Self) -> Self::Acc {
        (a.0.add_prod(x.v, y.v), a.1.add_prod(x.v, y.d).add_prod(x.d, y.v))
    }
    #[inline(always)]
    fn accc(a: Self::Acc, x: Self, c: DV<S>) -> Self::Acc {
        (a.0.add_prod(x.v, c), a.1.add_prod(x.d, c))
    }
    #[inline(always)]
    fn acc1(a: Self::Acc, x: Self) -> Self::Acc {
        (a.0.add(x.v), a.1.add(x.d))
    }
    #[inline(always)]
    fn fin(a: Self::Acc) -> Self {
        Du {
            v: a.0.finish(),
            d: a.1.finish(),
        }
    }
}

// ---------------------------------------------------------------------------------------------------------------
// plain f64 lanes
// ---------------------------------------------------------------------------------------------------------------

/// 8 lanes of plain f64 (values).
#[derive(Clone, Copy, Debug)]
pub struct F8<S: Simd>(pub V8<S>);

impl<S: Simd> Add for F8<S> {
    type Output = Self;
    #[inline(always)]
    fn add(self, o: F8<S>) -> F8<S> {
        F8(self.0.add(o.0))
    }
}
impl<S: Simd> Sub for F8<S> {
    type Output = Self;
    #[inline(always)]
    fn sub(self, o: F8<S>) -> F8<S> {
        F8(self.0.sub(o.0))
    }
}
impl<S: Simd> Neg for F8<S> {
    type Output = Self;
    #[inline(always)]
    fn neg(self) -> F8<S> {
        F8(V8::zero().sub(self.0))
    }
}
impl<S: Simd> Mul for F8<S> {
    type Output = Self;
    #[inline(always)]
    fn mul(self, o: F8<S>) -> F8<S> {
        F8(self.0.mul(o.0))
    }
}
impl<S: Simd> Div for F8<S> {
    type Output = Self;
    #[inline(always)]
    fn div(self, o: F8<S>) -> F8<S> {
        F8(self.0.div(o.0))
    }
}

impl<S: Simd> Lane for F8<S> {
    type S = S;
    type Acc = V8<S>;
    const TANGENT: bool = false;
    const VAL_F64: bool = true;
    #[inline(always)]
    fn zero() -> Self {
        F8(V8::zero())
    }
    #[inline(always)]
    fn cst(c: DV<S>) -> Self {
        F8(c.hi)
    }
    #[inline(always)]
    fn splat(x: DD) -> Self {
        F8(V8::splat(x.hi))
    }
    #[inline(always)]
    fn mulc(self, c: DV<S>) -> Self {
        F8(self.0.mul(c.hi))
    }
    #[inline(always)]
    fn muls(self, s: DD) -> Self {
        F8(self.0.mul(V8::splat(s.hi)))
    }
    #[inline(always)]
    fn mulf(self, s: f64) -> Self {
        F8(self.0.mul(V8::splat(s)))
    }
    #[inline(always)]
    fn mul_pwr2(self, s: f64) -> Self {
        debug_assert!(crate::dd::is_pwr2(s), "mul_pwr2: {s} is not a power of two");
        F8(self.0.mul(V8::splat(s)))
    }
    #[inline(always)]
    fn addc(self, c: DV<S>) -> Self {
        F8(self.0.add(c.hi))
    }
    #[inline(always)]
    fn bcast(self, j: usize) -> Self {
        F8(self.0.bcast(j))
    }
    #[inline(always)]
    fn val(self) -> DV<S> {
        DV {
            hi: self.0,
            lo: V8::zero(),
        }
    }
    #[inline(always)]
    fn tan(self) -> DV<S> {
        DV::zero()
    }
    #[inline(always)]
    fn from_vt(v: DV<S>, _t: DV<S>) -> Self {
        F8(v.hi)
    }
    #[inline(always)]
    fn acc0() -> V8<S> {
        V8::zero()
    }
    #[inline(always)]
    fn acc(a: V8<S>, x: Self, y: Self) -> V8<S> {
        x.0.fma(y.0, a)
    }
    #[inline(always)]
    fn accc(a: V8<S>, x: Self, c: DV<S>) -> V8<S> {
        x.0.fma(c.hi, a)
    }
    #[inline(always)]
    fn acc1(a: V8<S>, x: Self) -> V8<S> {
        a.add(x.0)
    }
    #[inline(always)]
    fn fin(a: V8<S>) -> Self {
        F8(a)
    }
}

/// Forward-mode dual number over plain f64 lanes.
#[derive(Clone, Copy, Debug)]
pub struct Fu<S: Simd> {
    pub v: V8<S>,
    pub d: V8<S>,
}

impl<S: Simd> Add for Fu<S> {
    type Output = Self;
    #[inline(always)]
    fn add(self, o: Fu<S>) -> Fu<S> {
        Fu {
            v: self.v.add(o.v),
            d: self.d.add(o.d),
        }
    }
}
impl<S: Simd> Sub for Fu<S> {
    type Output = Self;
    #[inline(always)]
    fn sub(self, o: Fu<S>) -> Fu<S> {
        Fu {
            v: self.v.sub(o.v),
            d: self.d.sub(o.d),
        }
    }
}
impl<S: Simd> Neg for Fu<S> {
    type Output = Self;
    #[inline(always)]
    fn neg(self) -> Fu<S> {
        let z = V8::zero();
        Fu {
            v: z.sub(self.v),
            d: z.sub(self.d),
        }
    }
}
impl<S: Simd> Mul for Fu<S> {
    type Output = Self;
    #[inline(always)]
    fn mul(self, o: Fu<S>) -> Fu<S> {
        Fu {
            v: self.v.mul(o.v),
            d: self.v.fma(o.d, self.d.mul(o.v)),
        }
    }
}
impl<S: Simd> Div for Fu<S> {
    type Output = Self;
    #[inline(always)]
    fn div(self, o: Fu<S>) -> Fu<S> {
        // (d - q o.d) / o.v, with d - q o.d as one fused operation (negated q o.d - d)
        // both divisions by o.v share its divisor (on AVX-512 its reciprocal)
        let r = o.v.divisor();
        let q = self.v.div_by(r);
        Fu {
            v: q,
            d: V8::zero().sub(q.fms(o.d, self.d)).div_by(r),
        }
    }
}

impl<S: Simd> Lane for Fu<S> {
    type S = S;
    type Acc = (V8<S>, V8<S>);
    const TANGENT: bool = true;
    const VAL_F64: bool = true;
    const TAN_F64: bool = true;
    const NT: usize = 1;
    #[inline(always)]
    fn tan64(self, _k: usize) -> V8<S> {
        self.d
    }
    #[inline(always)]
    fn set_tan64(&mut self, _k: usize, t: V8<S>) {
        self.d = t;
    }
    #[inline(always)]
    fn zero() -> Self {
        Fu {
            v: V8::zero(),
            d: V8::zero(),
        }
    }
    #[inline(always)]
    fn cst(c: DV<S>) -> Self {
        Fu { v: c.hi, d: V8::zero() }
    }
    #[inline(always)]
    fn splat(x: DD) -> Self {
        Fu {
            v: V8::splat(x.hi),
            d: V8::zero(),
        }
    }
    #[inline(always)]
    fn mulc(self, c: DV<S>) -> Self {
        Fu {
            v: self.v.mul(c.hi),
            d: self.d.mul(c.hi),
        }
    }
    #[inline(always)]
    fn muls(self, s: DD) -> Self {
        let c = V8::splat(s.hi);
        Fu {
            v: self.v.mul(c),
            d: self.d.mul(c),
        }
    }
    #[inline(always)]
    fn mulf(self, s: f64) -> Self {
        let c = V8::splat(s);
        Fu {
            v: self.v.mul(c),
            d: self.d.mul(c),
        }
    }
    #[inline(always)]
    fn mul_pwr2(self, s: f64) -> Self {
        debug_assert!(crate::dd::is_pwr2(s), "mul_pwr2: {s} is not a power of two");
        let c = V8::splat(s);
        Fu {
            v: self.v.mul(c),
            d: self.d.mul(c),
        }
    }
    #[inline(always)]
    fn addc(self, c: DV<S>) -> Self {
        Fu {
            v: self.v.add(c.hi),
            d: self.d,
        }
    }
    #[inline(always)]
    fn bcast(self, j: usize) -> Self {
        Fu {
            v: self.v.bcast(j),
            d: self.d.bcast(j),
        }
    }
    #[inline(always)]
    fn val(self) -> DV<S> {
        DV {
            hi: self.v,
            lo: V8::zero(),
        }
    }
    #[inline(always)]
    fn tan(self) -> DV<S> {
        DV {
            hi: self.d,
            lo: V8::zero(),
        }
    }
    #[inline(always)]
    fn from_vt(v: DV<S>, t: DV<S>) -> Self {
        Fu { v: v.hi, d: t.hi }
    }
    #[inline(always)]
    fn acc0() -> Self::Acc {
        (V8::zero(), V8::zero())
    }
    #[inline(always)]
    fn acc(a: Self::Acc, x: Self, y: Self) -> Self::Acc {
        (x.v.fma(y.v, a.0), x.d.fma(y.v, x.v.fma(y.d, a.1)))
    }
    #[inline(always)]
    fn accc(a: Self::Acc, x: Self, c: DV<S>) -> Self::Acc {
        (x.v.fma(c.hi, a.0), x.d.fma(c.hi, a.1))
    }
    #[inline(always)]
    fn acc1(a: Self::Acc, x: Self) -> Self::Acc {
        (a.0.add(x.v), a.1.add(x.d))
    }
    #[inline(always)]
    fn fin(a: Self::Acc) -> Self {
        Fu { v: a.0, d: a.1 }
    }
}

/// Dual number with a double-double value and N plain-f64 tangents: the base trajectory to double-double accuracy,
/// computed once for N Jacobian columns.
#[derive(Clone, Copy, Debug)]
pub struct Dtn<S: Simd, const N: usize> {
    pub v: DV<S>,
    pub d: [V8<S>; N],
}

impl<S: Simd, const N: usize> Add for Dtn<S, N> {
    type Output = Self;
    #[inline(always)]
    fn add(self, o: Self) -> Self {
        let mut d = self.d;
        for i in 0..N {
            d[i] = self.d[i].add(o.d[i]);
        }
        Dtn { v: self.v + o.v, d }
    }
}
impl<S: Simd, const N: usize> Sub for Dtn<S, N> {
    type Output = Self;
    #[inline(always)]
    fn sub(self, o: Self) -> Self {
        let mut d = self.d;
        for i in 0..N {
            d[i] = self.d[i].sub(o.d[i]);
        }
        Dtn { v: self.v - o.v, d }
    }
}
impl<S: Simd, const N: usize> Neg for Dtn<S, N> {
    type Output = Self;
    #[inline(always)]
    fn neg(self) -> Self {
        let mut d = self.d;
        for i in 0..N {
            d[i] = V8::zero().sub(self.d[i]);
        }
        Dtn { v: -self.v, d }
    }
}
impl<S: Simd, const N: usize> Mul for Dtn<S, N> {
    type Output = Self;
    #[inline(always)]
    fn mul(self, o: Self) -> Self {
        let mut d = self.d;
        for i in 0..N {
            d[i] = self.v.hi.fma(o.d[i], self.d[i].mul(o.v.hi));
        }
        Dtn { v: self.v * o.v, d }
    }
}
impl<S: Simd, const N: usize> Div for Dtn<S, N> {
    type Output = Self;
    #[inline(always)]
    fn div(self, o: Self) -> Self {
        // d_i = (d_i - q o.d_i) / o.v, as in Fu
        let q = self.v / o.v;
        let mut d = self.d;
        for i in 0..N {
            d[i] = V8::zero().sub(q.hi.fms(o.d[i], self.d[i])).div(o.v.hi);
        }
        Dtn { v: q, d }
    }
}

impl<S: Simd, const N: usize> Lane for Dtn<S, N> {
    type S = S;
    type Acc = (DotAcc<S>, [V8<S>; N]);
    const TANGENT: bool = true;
    const TAN_F64: bool = true;
    const NT: usize = N;
    #[inline(always)]
    fn zero() -> Self {
        Dtn {
            v: DV::zero(),
            d: [V8::zero(); N],
        }
    }
    #[inline(always)]
    fn cst(c: DV<S>) -> Self {
        Dtn {
            v: c,
            d: [V8::zero(); N],
        }
    }
    #[inline(always)]
    fn mulc(self, c: DV<S>) -> Self {
        Dtn {
            v: self.v * c,
            d: self.d.map(|x| x.mul(c.hi)),
        }
    }
    #[inline(always)]
    fn mulf(self, s: f64) -> Self {
        let c = V8::splat(s);
        Dtn {
            v: self.v.mul_f(s),
            d: self.d.map(|x| x.mul(c)),
        }
    }
    #[inline(always)]
    fn mul_pwr2(self, s: f64) -> Self {
        let c = V8::splat(s);
        Dtn {
            v: self.v.mul_pwr2(s),
            d: self.d.map(|x| x.mul(c)),
        }
    }
    #[inline(always)]
    fn addc(self, c: DV<S>) -> Self {
        Dtn {
            v: self.v + c,
            d: self.d,
        }
    }
    #[inline(always)]
    fn bcast(self, j: usize) -> Self {
        Dtn {
            v: self.v.bcast(j),
            d: self.d.map(|x| x.bcast(j)),
        }
    }
    #[inline(always)]
    fn val(self) -> DV<S> {
        self.v
    }
    /// the first tangent
    #[inline(always)]
    fn tan(self) -> DV<S> {
        DV {
            hi: self.d[0],
            lo: V8::zero(),
        }
    }
    /// value v, first tangent t, the others zero
    #[inline(always)]
    fn from_vt(v: DV<S>, t: DV<S>) -> Self {
        let mut d = [V8::zero(); N];
        d[0] = t.hi;
        Dtn { v, d }
    }
    #[inline(always)]
    fn acc0() -> Self::Acc {
        (DotAcc::zero(), [V8::zero(); N])
    }
    #[inline(always)]
    fn acc(a: Self::Acc, x: Self, y: Self) -> Self::Acc {
        let mut d = a.1;
        for i in 0..N {
            d[i] = x.v.hi.fma(y.d[i], x.d[i].fma(y.v.hi, a.1[i]));
        }
        (a.0.add_prod(x.v, y.v), d)
    }
    #[inline(always)]
    fn accc(a: Self::Acc, x: Self, c: DV<S>) -> Self::Acc {
        let mut d = a.1;
        for i in 0..N {
            d[i] = x.d[i].fma(c.hi, a.1[i]);
        }
        (a.0.add_prod(x.v, c), d)
    }
    #[inline(always)]
    fn acc1(a: Self::Acc, x: Self) -> Self::Acc {
        let mut d = a.1;
        for i in 0..N {
            d[i] = a.1[i].add(x.d[i]);
        }
        (a.0.add(x.v), d)
    }
    #[inline(always)]
    fn fin(a: Self::Acc) -> Self {
        Dtn {
            v: a.0.finish(),
            d: a.1,
        }
    }
    #[inline(always)]
    fn tan64(self, k: usize) -> V8<S> {
        self.d[k]
    }
    #[inline(always)]
    fn set_tan64(&mut self, k: usize, t: V8<S>) {
        self.d[k] = t;
    }
}

/// Dual number with a plain-f64 value and N plain-f64 tangents (Fu with N columns per evaluation).
#[derive(Clone, Copy, Debug)]
pub struct Fun<S: Simd, const N: usize> {
    pub v: V8<S>,
    pub d: [V8<S>; N],
}

impl<S: Simd, const N: usize> Add for Fun<S, N> {
    type Output = Self;
    #[inline(always)]
    fn add(self, o: Self) -> Self {
        let mut d = self.d;
        for i in 0..N {
            d[i] = self.d[i].add(o.d[i]);
        }
        Fun { v: self.v.add(o.v), d }
    }
}
impl<S: Simd, const N: usize> Sub for Fun<S, N> {
    type Output = Self;
    #[inline(always)]
    fn sub(self, o: Self) -> Self {
        let mut d = self.d;
        for i in 0..N {
            d[i] = self.d[i].sub(o.d[i]);
        }
        Fun { v: self.v.sub(o.v), d }
    }
}
impl<S: Simd, const N: usize> Neg for Fun<S, N> {
    type Output = Self;
    #[inline(always)]
    fn neg(self) -> Self {
        let z = V8::zero();
        Fun {
            v: z.sub(self.v),
            d: self.d.map(|x| z.sub(x)),
        }
    }
}
impl<S: Simd, const N: usize> Mul for Fun<S, N> {
    type Output = Self;
    #[inline(always)]
    fn mul(self, o: Self) -> Self {
        let mut d = self.d;
        for i in 0..N {
            d[i] = self.v.fma(o.d[i], self.d[i].mul(o.v));
        }
        Fun { v: self.v.mul(o.v), d }
    }
}
impl<S: Simd, const N: usize> Div for Fun<S, N> {
    type Output = Self;
    #[inline(always)]
    fn div(self, o: Self) -> Self {
        // the N + 1 divisions by o.v share its divisor (on AVX-512 its reciprocal)
        let r = o.v.divisor();
        let q = self.v.div_by(r);
        let mut d = self.d;
        for i in 0..N {
            d[i] = V8::zero().sub(q.fms(o.d[i], self.d[i])).div_by(r);
        }
        Fun { v: q, d }
    }
}

impl<S: Simd, const N: usize> Lane for Fun<S, N> {
    type S = S;
    type Acc = (V8<S>, [V8<S>; N]);
    const TANGENT: bool = true;
    const VAL_F64: bool = true;
    const TAN_F64: bool = true;
    const NT: usize = N;
    #[inline(always)]
    fn zero() -> Self {
        Fun {
            v: V8::zero(),
            d: [V8::zero(); N],
        }
    }
    #[inline(always)]
    fn cst(c: DV<S>) -> Self {
        Fun {
            v: c.hi,
            d: [V8::zero(); N],
        }
    }
    #[inline(always)]
    fn splat(x: DD) -> Self {
        Fun {
            v: V8::splat(x.hi),
            d: [V8::zero(); N],
        }
    }
    #[inline(always)]
    fn mulc(self, c: DV<S>) -> Self {
        Fun {
            v: self.v.mul(c.hi),
            d: self.d.map(|x| x.mul(c.hi)),
        }
    }
    #[inline(always)]
    fn muls(self, s: DD) -> Self {
        let c = V8::splat(s.hi);
        Fun {
            v: self.v.mul(c),
            d: self.d.map(|x| x.mul(c)),
        }
    }
    #[inline(always)]
    fn mulf(self, s: f64) -> Self {
        let c = V8::splat(s);
        Fun {
            v: self.v.mul(c),
            d: self.d.map(|x| x.mul(c)),
        }
    }
    #[inline(always)]
    fn mul_pwr2(self, s: f64) -> Self {
        debug_assert!(crate::dd::is_pwr2(s), "mul_pwr2: {s} is not a power of two");
        let c = V8::splat(s);
        Fun {
            v: self.v.mul(c),
            d: self.d.map(|x| x.mul(c)),
        }
    }
    #[inline(always)]
    fn addc(self, c: DV<S>) -> Self {
        Fun {
            v: self.v.add(c.hi),
            d: self.d,
        }
    }
    #[inline(always)]
    fn bcast(self, j: usize) -> Self {
        Fun {
            v: self.v.bcast(j),
            d: self.d.map(|x| x.bcast(j)),
        }
    }
    #[inline(always)]
    fn val(self) -> DV<S> {
        DV {
            hi: self.v,
            lo: V8::zero(),
        }
    }
    /// the first tangent
    #[inline(always)]
    fn tan(self) -> DV<S> {
        DV {
            hi: self.d[0],
            lo: V8::zero(),
        }
    }
    /// value v, first tangent t, the others zero
    #[inline(always)]
    fn from_vt(v: DV<S>, t: DV<S>) -> Self {
        let mut d = [V8::zero(); N];
        d[0] = t.hi;
        Fun { v: v.hi, d }
    }
    #[inline(always)]
    fn acc0() -> Self::Acc {
        (V8::zero(), [V8::zero(); N])
    }
    #[inline(always)]
    fn acc(a: Self::Acc, x: Self, y: Self) -> Self::Acc {
        let mut d = a.1;
        for i in 0..N {
            d[i] = x.v.fma(y.d[i], x.d[i].fma(y.v, a.1[i]));
        }
        (x.v.fma(y.v, a.0), d)
    }
    #[inline(always)]
    fn accc(a: Self::Acc, x: Self, c: DV<S>) -> Self::Acc {
        let mut d = a.1;
        for i in 0..N {
            d[i] = x.d[i].fma(c.hi, a.1[i]);
        }
        (x.v.fma(c.hi, a.0), d)
    }
    #[inline(always)]
    fn acc1(a: Self::Acc, x: Self) -> Self::Acc {
        let mut d = a.1;
        for i in 0..N {
            d[i] = a.1[i].add(x.d[i]);
        }
        (a.0.add(x.v), d)
    }
    #[inline(always)]
    fn fin(a: Self::Acc) -> Self {
        Fun { v: a.0, d: a.1 }
    }
    #[inline(always)]
    fn tan64(self, k: usize) -> V8<S> {
        self.d[k]
    }
    #[inline(always)]
    fn set_tan64(&mut self, k: usize, t: V8<S>) {
        self.d[k] = t;
    }
}
