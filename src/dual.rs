//! Lane types for code that is written once and run in several arithmetics, with or without derivatives: the trait
//! [`Lane`] is 8 values of a computation (8 grid points, 8 independent problems, ...), and its implementations are
//!
//! * `DV`: values (double-double).
//! * `Du`: value + one forward-mode tangent (v + d eps, eps^2 = 0), both double-double. One evaluation with a
//!   unit tangent on one unknown gives one exact Jacobian column.
//! * `F8`, `Fu`: the same in plain f64 (one `V8` per value / tangent), for the mixed-precision Newton's f64 Jacobian.
//!   Constants and inputs, which the trait passes as double-double, enter as their hi parts.
//! * `Dtn<N>`: a double-double value with N plain-f64 tangents: N Jacobian columns from one evaluation, the base
//!   trajectory computed once (and to double-double accuracy) for all of them. `Fun<N>` is the same in plain f64.
//! * `Qu`: value + one tangent, both quad-double (`QV`): exact Jacobian columns to quad-double accuracy.
//! * `Ou`: value + one tangent, both octo-double (`crate::ov::OV`): exact Jacobian columns to octo-double accuracy.
//!   `Oun<N>` carries N octo-double tangents, each bit for bit an `Ou` evaluation's.
//! * `crate::ov::OV`: values in octo-double (`VAL_OD`), with double-double constants and inputs, as `QV` is.
//! * `Dc`: a double-double value with a complex tangent (real and imaginary parts, each double-double): the
//!   derivative along a complex direction, e.g. the growth-mode matrix of a real background at a complex rate.
//! * `jet::Jet<N>`: a truncated power series, N double-double coefficients in one variable: the computation's own
//!   Taylor coefficients in a parameter entered as `Lane::var` or, for the constants formed from the parameter,
//!   through [`Param`] (`Lane::P`: `DD` on every other lane, `jet::Series<N>` on a jet).
//! * `jet::QJet<N>`: the same with N quad-double coefficients (`Lane::P` is `jet::QSeries<N>`), read and set in
//!   quad-double through `Lane::coef_qd` and `set_coef_qd`.
//! * `jet::OJet<N>`: the same with N octo-double coefficients (`Lane::P` is `jet::OSeries<N>`), read and set in
//!   octo-double through `Lane::coef_od` and `set_coef_od`.
//!
//! `Counted<L>` wraps any of them and counts every operation by kind (`take_counts`), for operation counts of the
//! generic code.
//!
//! Each lane type is generic over the backend (`crate::simd`), which `Lane::S` names, so that code generic over
//! `Lane` runs on the instruction set [`crate::simd::dispatch`] picks.
use crate::dd::DD;
use crate::dv::{DotAcc, DV};
use crate::ov::{ODotAcc, OV};
use crate::qv::{QDotAcc, QV};
use crate::simd::Simd;
use crate::v8::V8;
use std::ops::{Add, Div, Mul, Neg, Sub};

/// Deliberate breakage of the octo-double jet and dual lanes for the controls of their tests (feature `mutate`; ids below, 0 =
/// none), as `crate::od::mutate` breaks the octo-double arithmetic: `set(id)` selects one in the current thread, and
/// without the feature the hooks are compile-time `false`.
pub mod mutate {
    /// `crate::jet::OJet`'s product: the last term of each convolution, x_k y_0, dropped (orders k >= 1)
    pub const OJET_CONV: u32 = 1;
    /// `crate::field::FieldSolve::solve_lanes_jet_refine_od`: each refinement residual formed at the iterate rounded
    /// to quad-double
    pub const OJET_REFINE_QD: u32 = 2;
    /// `crate::dual::Ou`'s product: the tangent's term d o.v dropped
    pub const OU_TAN: u32 = 3;
    /// `crate::field::cs_range_at_par`'s and `cs_w_at_par`'s split sums: the last lane vector's coefficient k moved by
    /// one ulp of the leading part of its lane 0
    pub const CS_AT_SPLIT: u32 = 4;
    /// `crate::dual::Lane::mulf_upto` on the jets: coefficient k left unweighted, so that a weighted order-k sum
    /// (`crate::field::cs_w_at`) takes the products of order k with x_k unweighted
    pub const MULF_UPTO: u32 = 5;
    /// number of ids
    pub const N: u32 = 5;
    /// the mutations' descriptions, by id
    pub const NAMES: [&str; 6] = [
        "none",
        "octo-double jet product: last convolution term dropped",
        "octo-double jet solve: residual at the iterate rounded to quad-double",
        "octo-double dual product: tangent term d o.v dropped",
        "split order-k Cauchy sum: last lane vector moved by an ulp",
        "jet times an f64 to order k: coefficient k left unweighted",
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

/// The arithmetic of a parameter a computation over [`Lane`] is continued in ([`Lane::P`]): the scalar double-double
/// on every lane that is not a jet, where a constant formed from the parameter is bit for bit the scalar operations
/// it was, and a scalar truncated power series (`crate::jet::Series<N>`, `crate::jet::QSeries<N>` in quad-double,
/// `crate::jet::OSeries<N>` in octo-double) on a jet lane, whose constants then carry their own Taylor coefficients in
/// the parameter.
pub trait Param:
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
    fn one() -> Self;
    fn from_f64(x: f64) -> Self;
    fn from_dd(x: DD) -> Self;
    /// times an exact f64
    fn mul_f(self, s: f64) -> Self;
    /// the parameter itself: c, and c + h on a series
    fn var(c: DD) -> Self;
}

impl Param for DD {
    #[inline(always)]
    fn one() -> Self {
        DD::ONE
    }
    #[inline(always)]
    fn from_f64(x: f64) -> Self {
        DD::from_f64(x)
    }
    #[inline(always)]
    fn from_dd(x: DD) -> Self {
        x
    }
    #[inline(always)]
    fn mul_f(self, s: f64) -> Self {
        DD::mul_f(self, s)
    }
    #[inline(always)]
    fn var(c: DD) -> Self {
        c
    }
}

/// the parameter arithmetic of a lane that is not a jet: double-double scalars, `mulp` the lane's own `muls`
macro_rules! dd_param {
    () => {
        type P = DD;
        #[inline(always)]
        fn mulp(self, p: DD) -> Self {
            self.muls(p)
        }
        #[inline(always)]
        fn addp(self, p: DD) -> Self {
            self.addc(DV::splat(p))
        }
    };
}
pub(crate) use dd_param;

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
    /// values in plain f64 (`F8`, `Fu`, `Fun`): double-double constants and inputs enter rounded to their hi parts
    const VAL_F64: bool = false;
    /// tangents in plain f64 (`Fu`, `Fun`, `Dtn`)
    const TAN_F64: bool = false;
    /// number of f64 tangents (`tan64`; 0 unless TAN_F64)
    const NT: usize = 0;
    /// values in quad-double (`QV`, `Qu`, `crate::jet::QJet<N>`): a solve with a double-double LU is refined for such
    /// a lane with the residual formed in its arithmetic (`crate::field::FieldSolve::solve_lanes_refine`; a jet's
    /// solve goes order by order, `NJ`)
    const VAL_QD: bool = false;
    /// values in octo-double (`crate::ov::OV`, `Ou`, `Oun`, `crate::jet::OJet<N>`): as for `VAL_QD`, a solve with a
    /// double-double LU is refined for such a lane with the residual formed in its arithmetic, with about twice the
    /// steps, as each gains about cond(A) 2^-104 (a jet's solve goes order by order,
    /// `crate::field::FieldSolve::solve_lanes_jet_refine_od`). Lanes that set it leave `VAL_QD` unset, so code that
    /// refines quad-double lanes a fixed number of steps does not apply that count to them.
    const VAL_OD: bool = false;
    /// number of coefficients of a jet (`crate::jet::Jet<N>`, `crate::jet::QJet<N>`, `crate::jet::OJet<N>`), 0 for
    /// every other lane: code with a branch for jets, such as an order-by-order solve, tests it
    const NJ: usize = 0;
    /// the parameter arithmetic: `DD` on every lane that is not a jet, `crate::jet::Series<N>` on `Jet<N>`,
    /// `crate::jet::QSeries<N>` on `QJet<N>` and `crate::jet::OSeries<N>` on `OJet<N>`
    type P: Param;
    /// times a parameter constant (`muls` on every lane that is not a jet)
    fn mulp(self, p: Self::P) -> Self;
    /// plus a parameter constant (`addc` of the splat constant on every lane that is not a jet)
    fn addp(self, p: Self::P) -> Self;
    /// coefficient k of a jet; on every other lane the value (k = 0), the tangent (k = 1, tangent lanes) and zero
    #[inline(always)]
    fn coef(self, k: usize) -> DV<Self::S> {
        match k {
            0 => self.val(),
            1 if Self::TANGENT => self.tan(),
            _ => DV::zero(),
        }
    }
    /// set coefficient k of a jet
    #[inline(always)]
    fn set_coef(&mut self, _k: usize, _c: DV<Self::S>) {
        unreachable!("no jet coefficients")
    }
    /// coefficient k in quad-double, for code generic over `Lane` that reads a quad-double jet's coefficients without
    /// rounding them to double-double (`coef` does): the jet's own on `crate::jet::QJet<N>`, the quad-double value and
    /// tangent on `QV` and `Qu`, and `coef(k)`, exactly, on every other lane
    #[inline(always)]
    fn coef_qd(self, k: usize) -> QV<Self::S> {
        QV::from_dv(self.coef(k))
    }
    /// set coefficient k of a jet from quad-double: exactly on `crate::jet::QJet<N>`, rounded to double-double
    /// (`QV::to_dv`) on `crate::jet::Jet<N>`
    #[inline(always)]
    fn set_coef_qd(&mut self, k: usize, c: QV<Self::S>) {
        self.set_coef(k, c.to_dv())
    }
    /// coefficient k in octo-double, for code generic over `Lane` that reads an octo-double jet's coefficients without
    /// rounding them (`coef` and `coef_qd` do): the jet's own on `crate::jet::OJet<N>`, the octo-double value on `OV`,
    /// value and tangents on `Ou` and `Oun`, and `coef_qd(k)`, exactly, on every other lane
    #[inline(always)]
    fn coef_od(self, k: usize) -> OV<Self::S> {
        OV::from_qv(self.coef_qd(k))
    }
    /// set coefficient k of a jet from octo-double: exactly on `crate::jet::OJet<N>`, rounded to quad-double
    /// (`OV::to_qv`) on `crate::jet::QJet<N>` and to double-double (`OV::to_dv`) on `crate::jet::Jet<N>`
    #[inline(always)]
    fn set_coef_od(&mut self, k: usize, c: OV<Self::S>) {
        self.set_coef_qd(k, c.to_qv())
    }
    fn zero() -> Self;
    /// a constant (zero tangent)
    fn cst(c: DV<Self::S>) -> Self;
    #[inline(always)]
    fn splat(x: DD) -> Self {
        Self::cst(DV::splat(x))
    }
    /// a parameter the computation is continued in: `splat(c)` on every lane, the series variable c + h on a jet
    #[inline(always)]
    fn var(c: DD) -> Self {
        Self::splat(c)
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
    /// `mulf(s)`'s coefficients 0..=k on a jet, the others left as they are (a weighted order-k sum reads no others,
    /// `crate::field::cs_w_at`); on every other lane `mulf(s)`
    #[inline(always)]
    fn mulf_upto(self, s: f64, k: usize) -> Self {
        let _ = k;
        self.mulf(s)
    }
    /// times a power of two s (`dd::is_pwr2`): every part, value and tangents, scaled exactly (barring overflow and
    /// underflow), so bitwise `mulf(s)`; for computing in a variable rescaled by 2^k, e.g. a power series in x / 2^k
    /// whose coefficients would overflow in x
    fn mul_pwr2(self, s: f64) -> Self;
    /// plus a constant lane vector
    fn addc(self, c: DV<Self::S>) -> Self;
    /// all 8 lanes = lane j
    fn bcast(self, j: usize) -> Self;
    fn val(self) -> DV<Self::S>;
    /// the tangent (derivative part) rounded to double-double, zero on a lane without one. `DV`, `QV` and `OV` also
    /// have an inherent `tan`, the trigonometric tangent, which a method call on the concrete type resolves to:
    /// write `Lane::tan(x)` for this one there.
    fn tan(self) -> DV<Self::S>;
    fn from_vt(v: DV<Self::S>, t: DV<Self::S>) -> Self;
    fn acc0() -> Self::Acc;
    /// a + x y
    fn acc(a: Self::Acc, x: Self, y: Self) -> Self::Acc;
    /// a + x y into a, with the accumulator and the operands borrowed: bitwise `acc`. Moving them copies the jets'
    /// accumulators and coefficients, several kilobytes each (`[QDotAcc; N]` and N quad-double coefficients for
    /// `crate::jet::QJet<N>`), once per term of a sum. The default is `acc`. The jets, `Dtn` and `Fun` add in place,
    /// `QV` and `Qu` through `QDotAcc::add_prod_mut`, `crate::ov::OV`, `Ou` and `Oun` through
    /// `crate::ov::ODotAcc::add_prod_mut`.
    #[inline(always)]
    fn acc_mut(a: &mut Self::Acc, x: &Self, y: &Self) {
        *a = Self::acc(*a, *x, *y);
    }
    /// a + x c, c constant
    fn accc(a: Self::Acc, x: Self, c: DV<Self::S>) -> Self::Acc;
    /// a + x
    fn acc1(a: Self::Acc, x: Self) -> Self::Acc;
    fn fin(a: Self::Acc) -> Self;
    /// `acc_mut` for the coefficient of order k alone: on a jet the products x_i y_(k-i), i = 0..=k, added into
    /// accumulator k in `acc`'s order, so that `fin_at` gives coefficient k of `fin` bit for bit; the other
    /// accumulators are left as they are. On every other lane, `acc_mut`. The order-k operations (`acc_at`, `fin_at`,
    /// `mul_at`, `div_at`, `mulp_at`) form a series one order at a time, its lower orders kept from the calls before.
    #[inline(always)]
    fn acc_at(a: &mut Self::Acc, x: &Self, y: &Self, k: usize) {
        let _ = k;
        Self::acc_mut(a, x, y)
    }
    /// coefficient k of `fin(a)` into coefficient k of `into`, its other coefficients unchanged (jets); on every other
    /// lane `fin(a)`
    #[inline(always)]
    fn fin_at(a: &Self::Acc, k: usize, into: &mut Self) {
        let _ = k;
        *into = Self::fin(*a)
    }
    /// coefficient k of x y into coefficient k of `into`, bit for bit that of `x * y`, the other coefficients
    /// unchanged (jets); on every other lane `x * y`
    #[inline(always)]
    fn mul_at(x: &Self, y: &Self, k: usize, into: &mut Self) {
        let _ = k;
        *into = *x * *y
    }
    /// coefficient k of x / y into coefficient k of `into`, from the quotient's coefficients 0..k - 1 already in
    /// `into`: bit for bit that of `x / y` when they are its (jets). On every other lane `x / y`.
    #[inline(always)]
    fn div_at(x: &Self, y: &Self, k: usize, into: &mut Self) {
        let _ = k;
        *into = *x / *y
    }
    /// coefficient k of `x.mulp(p)` into coefficient k of `into`, bit for bit, the other coefficients unchanged
    /// (jets); on every other lane `x.mulp(p)`
    #[inline(always)]
    fn mulp_at(x: &Self, p: &Self::P, k: usize, into: &mut Self) {
        let _ = k;
        *into = x.mulp(*p)
    }
    /// coefficient k of `from` into coefficient k of `into`, the others unchanged (jets); on every other lane `from`
    #[inline(always)]
    fn copy_at(from: &Self, k: usize, into: &mut Self) {
        let _ = k;
        *into = *from
    }
    /// number of tangents carried in the value's arithmetic (`tan_k`, `from_vt_n`): one on a dual lane with a
    /// tangent of its value's precision, N on `Oun<N>`, none on every other lane (jets; the f64 tangents of `TAN_F64` lanes
    /// are `NT`'s)
    const NTD: usize = (Self::TANGENT && !Self::TAN_F64 && Self::NJ == 0) as usize;
    /// tangent k < NTD rounded to double-double; by default `tan()` for k = 0
    #[inline(always)]
    fn tan_k(self, k: usize) -> DV<Self::S> {
        debug_assert!(k < Self::NTD.max(1), "tan_k: tangent {k} of {}", Self::NTD);
        self.tan()
    }
    /// value v and the tangents t (NTD of them), exactly; by default `from_vt` with t's first (zero when empty)
    #[inline(always)]
    fn from_vt_n(v: DV<Self::S>, t: &[DV<Self::S>]) -> Self {
        Self::from_vt(v, t.first().copied().unwrap_or_else(DV::zero))
    }
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
    dd_param!();
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
    dd_param!();
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
// double-double value and complex tangent
// ---------------------------------------------------------------------------------------------------------------

/// Forward-mode dual number over double-double lanes with a complex tangent: value `v`, tangent `r + i i`, all
/// `DV`. A real function linearised about a real value is real-linear in the tangent, so the real and the imaginary
/// part obey the real dual rule separately: every operation is `Du`'s applied to `r` and to `i`. It gives the
/// derivative along a complex direction, e.g. the growth-mode matrix of a real background at a complex rate.
/// `tan` is the real part and `from_vt` sets the imaginary part to zero, so code written for `Du` runs unchanged with
/// a real tangent; the imaginary part is read and set through the fields (`crate::field::Fl::tan_im`, `from_vri`).
#[derive(Clone, Copy, Debug)]
pub struct Dc<S: Simd> {
    pub v: DV<S>,
    pub r: DV<S>,
    pub i: DV<S>,
}

impl<S: Simd> Add for Dc<S> {
    type Output = Self;
    #[inline(always)]
    fn add(self, o: Dc<S>) -> Dc<S> {
        Dc {
            v: self.v + o.v,
            r: self.r + o.r,
            i: self.i + o.i,
        }
    }
}
impl<S: Simd> Sub for Dc<S> {
    type Output = Self;
    #[inline(always)]
    fn sub(self, o: Dc<S>) -> Dc<S> {
        Dc {
            v: self.v - o.v,
            r: self.r - o.r,
            i: self.i - o.i,
        }
    }
}
impl<S: Simd> Neg for Dc<S> {
    type Output = Self;
    #[inline(always)]
    fn neg(self) -> Dc<S> {
        Dc {
            v: -self.v,
            r: -self.r,
            i: -self.i,
        }
    }
}
impl<S: Simd> Mul for Dc<S> {
    type Output = Self;
    #[inline(always)]
    fn mul(self, o: Dc<S>) -> Dc<S> {
        let r = DotAcc::zero().add_prod(self.v, o.r).add_prod(self.r, o.v).finish();
        let i = DotAcc::zero().add_prod(self.v, o.i).add_prod(self.i, o.v).finish();
        Dc { v: self.v * o.v, r, i }
    }
}
impl<S: Simd> Div for Dc<S> {
    type Output = Self;
    #[inline(always)]
    fn div(self, o: Dc<S>) -> Dc<S> {
        let q = self.v / o.v;
        Dc {
            v: q,
            r: (self.r - q * o.r) / o.v,
            i: (self.i - q * o.i) / o.v,
        }
    }
}

impl<S: Simd> Lane for Dc<S> {
    type S = S;
    type Acc = (DotAcc<S>, DotAcc<S>, DotAcc<S>);
    dd_param!();
    const TANGENT: bool = true;
    #[inline(always)]
    fn zero() -> Self {
        Dc {
            v: DV::zero(),
            r: DV::zero(),
            i: DV::zero(),
        }
    }
    #[inline(always)]
    fn cst(c: DV<S>) -> Self {
        Dc {
            v: c,
            r: DV::zero(),
            i: DV::zero(),
        }
    }
    #[inline(always)]
    fn mulc(self, c: DV<S>) -> Self {
        Dc {
            v: self.v * c,
            r: self.r * c,
            i: self.i * c,
        }
    }
    #[inline(always)]
    fn mulf(self, s: f64) -> Self {
        Dc {
            v: self.v.mul_f(s),
            r: self.r.mul_f(s),
            i: self.i.mul_f(s),
        }
    }
    #[inline(always)]
    fn mul_pwr2(self, s: f64) -> Self {
        Dc {
            v: self.v.mul_pwr2(s),
            r: self.r.mul_pwr2(s),
            i: self.i.mul_pwr2(s),
        }
    }
    #[inline(always)]
    fn addc(self, c: DV<S>) -> Self {
        Dc {
            v: self.v + c,
            r: self.r,
            i: self.i,
        }
    }
    #[inline(always)]
    fn bcast(self, j: usize) -> Self {
        Dc {
            v: self.v.bcast(j),
            r: self.r.bcast(j),
            i: self.i.bcast(j),
        }
    }
    #[inline(always)]
    fn val(self) -> DV<S> {
        self.v
    }
    /// the real part of the tangent
    #[inline(always)]
    fn tan(self) -> DV<S> {
        self.r
    }
    /// a real tangent (imaginary part zero)
    #[inline(always)]
    fn from_vt(v: DV<S>, t: DV<S>) -> Self {
        Dc { v, r: t, i: DV::zero() }
    }
    #[inline(always)]
    fn acc0() -> Self::Acc {
        (DotAcc::zero(), DotAcc::zero(), DotAcc::zero())
    }
    #[inline(always)]
    fn acc(a: Self::Acc, x: Self, y: Self) -> Self::Acc {
        (
            a.0.add_prod(x.v, y.v),
            a.1.add_prod(x.v, y.r).add_prod(x.r, y.v),
            a.2.add_prod(x.v, y.i).add_prod(x.i, y.v),
        )
    }
    #[inline(always)]
    fn accc(a: Self::Acc, x: Self, c: DV<S>) -> Self::Acc {
        (a.0.add_prod(x.v, c), a.1.add_prod(x.r, c), a.2.add_prod(x.i, c))
    }
    #[inline(always)]
    fn acc1(a: Self::Acc, x: Self) -> Self::Acc {
        (a.0.add(x.v), a.1.add(x.r), a.2.add(x.i))
    }
    #[inline(always)]
    fn fin(a: Self::Acc) -> Self {
        Dc {
            v: a.0.finish(),
            r: a.1.finish(),
            i: a.2.finish(),
        }
    }
}

// ---------------------------------------------------------------------------------------------------------------
// quad-double value and tangent
// ---------------------------------------------------------------------------------------------------------------

/// Forward-mode dual number over quad-double lanes: value `v` and one tangent `d`, both `QV`. The value runs the
/// operations of `QV` as a `Lane`, bitwise, and the tangent their derivatives in quad-double; one evaluation with a
/// unit tangent on one unknown gives one Jacobian column to quad-double accuracy. As for `QV`, the trait passes
/// constants and inputs as double-double (they enter exactly) and `val`, `tan` round back to double-double; a
/// quad-double input is built from its parts, `Qu { v, d }`, and read back from `v` and `d`.
#[derive(Clone, Copy, Debug)]
pub struct Qu<S: Simd> {
    pub v: QV<S>,
    pub d: QV<S>,
}

impl<S: Simd> Add for Qu<S> {
    type Output = Self;
    #[inline(always)]
    fn add(self, o: Qu<S>) -> Qu<S> {
        Qu {
            v: self.v + o.v,
            d: self.d + o.d,
        }
    }
}
impl<S: Simd> Sub for Qu<S> {
    type Output = Self;
    #[inline(always)]
    fn sub(self, o: Qu<S>) -> Qu<S> {
        Qu {
            v: self.v - o.v,
            d: self.d - o.d,
        }
    }
}
impl<S: Simd> Neg for Qu<S> {
    type Output = Self;
    #[inline(always)]
    fn neg(self) -> Qu<S> {
        Qu { v: -self.v, d: -self.d }
    }
}
impl<S: Simd> Mul for Qu<S> {
    type Output = Self;
    #[inline(always)]
    fn mul(self, o: Qu<S>) -> Qu<S> {
        let d = QDotAcc::zero().add_prod(self.v, o.d).add_prod(self.d, o.v).finish();
        Qu { v: self.v * o.v, d }
    }
}
impl<S: Simd> Div for Qu<S> {
    type Output = Self;
    #[inline(always)]
    fn div(self, o: Qu<S>) -> Qu<S> {
        let q = self.v / o.v;
        Qu {
            v: q,
            d: (self.d - q * o.d) / o.v,
        }
    }
}

impl<S: Simd> Lane for Qu<S> {
    type S = S;
    type Acc = (QDotAcc<S>, QDotAcc<S>);
    dd_param!();
    const TANGENT: bool = true;
    const VAL_QD: bool = true;
    #[inline(always)]
    fn zero() -> Self {
        Qu {
            v: QV::zero(),
            d: QV::zero(),
        }
    }
    #[inline(always)]
    fn cst(c: DV<S>) -> Self {
        Qu {
            v: QV::from_dv(c),
            d: QV::zero(),
        }
    }
    #[inline(always)]
    fn mulc(self, c: DV<S>) -> Self {
        let c = QV::from_dv(c);
        Qu {
            v: self.v * c,
            d: self.d * c,
        }
    }
    #[inline(always)]
    fn mulf(self, s: f64) -> Self {
        Qu {
            v: self.v.mul_f(s),
            d: self.d.mul_f(s),
        }
    }
    #[inline(always)]
    fn mul_pwr2(self, s: f64) -> Self {
        Qu {
            v: self.v.mul_pwr2(s),
            d: self.d.mul_pwr2(s),
        }
    }
    #[inline(always)]
    fn addc(self, c: DV<S>) -> Self {
        Qu {
            v: self.v + QV::from_dv(c),
            d: self.d,
        }
    }
    #[inline(always)]
    fn bcast(self, j: usize) -> Self {
        Qu {
            v: self.v.bcast(j),
            d: self.d.bcast(j),
        }
    }
    #[inline(always)]
    fn val(self) -> DV<S> {
        self.v.to_dv()
    }
    #[inline(always)]
    fn tan(self) -> DV<S> {
        self.d.to_dv()
    }
    #[inline(always)]
    fn from_vt(v: DV<S>, t: DV<S>) -> Self {
        Qu {
            v: QV::from_dv(v),
            d: QV::from_dv(t),
        }
    }
    #[inline(always)]
    fn acc0() -> Self::Acc {
        (QDotAcc::zero(), QDotAcc::zero())
    }
    #[inline(always)]
    fn acc(a: Self::Acc, x: Self, y: Self) -> Self::Acc {
        (a.0.add_prod(x.v, y.v), a.1.add_prod(x.v, y.d).add_prod(x.d, y.v))
    }
    /// `acc` in place (`QDotAcc::add_prod_mut`)
    #[inline(always)]
    fn acc_mut(a: &mut Self::Acc, x: &Self, y: &Self) {
        a.0.add_prod_mut(&x.v, &y.v);
        a.1.add_prod_mut(&x.v, &y.d);
        a.1.add_prod_mut(&x.d, &y.v);
    }
    #[inline(always)]
    fn accc(a: Self::Acc, x: Self, c: DV<S>) -> Self::Acc {
        let c = QV::from_dv(c);
        (a.0.add_prod(x.v, c), a.1.add_prod(x.d, c))
    }
    #[inline(always)]
    fn acc1(a: Self::Acc, x: Self) -> Self::Acc {
        (a.0.add(x.v), a.1.add(x.d))
    }
    #[inline(always)]
    fn fin(a: Self::Acc) -> Self {
        Qu {
            v: a.0.finish(),
            d: a.1.finish(),
        }
    }
    /// the quad-double value (k = 0) and tangent (k = 1), zero past them
    #[inline(always)]
    fn coef_qd(self, k: usize) -> QV<S> {
        match k {
            0 => self.v,
            1 => self.d,
            _ => QV::zero(),
        }
    }
}

// ---------------------------------------------------------------------------------------------------------------
// octo-double value and tangent
// ---------------------------------------------------------------------------------------------------------------

/// Forward-mode dual number over octo-double lanes: value `v` and one tangent `d`, both `OV`, as `Qu` is over
/// quad-double. The value runs the operations of `OV` as a `Lane`, bitwise, and the tangent their derivatives in
/// octo-double; one evaluation with a unit tangent on one unknown gives one Jacobian column to octo-double accuracy.
/// As for `OV`, the trait passes constants and inputs as double-double (they enter exactly), and `val`, `tan` round
/// back to double-double, `coef_qd` to quad-double. An octo-double input is built from its parts, `Ou { v, d }`
/// (`crate::field::Fl::from_vt_od` for a field), and read back from `v` and `d`, or `coef_od(0)` and `coef_od(1)`.
/// `VAL_OD` is set and `VAL_QD` is not: a solve with a double-double LU is refined for these lanes with the residual
/// in octo-double (`crate::field::FieldSolve::solve_lanes_refine_t`), with about twice the steps of `Qu`.
#[derive(Clone, Copy, Debug)]
pub struct Ou<S: Simd> {
    /// the value
    pub v: OV<S>,
    /// the tangent
    pub d: OV<S>,
}

impl<S: Simd> Add for Ou<S> {
    type Output = Self;
    /// value and tangent added
    #[inline(always)]
    fn add(self, o: Ou<S>) -> Ou<S> {
        Ou {
            v: self.v + o.v,
            d: self.d + o.d,
        }
    }
}
impl<S: Simd> Sub for Ou<S> {
    type Output = Self;
    /// value and tangent subtracted
    #[inline(always)]
    fn sub(self, o: Ou<S>) -> Ou<S> {
        Ou {
            v: self.v - o.v,
            d: self.d - o.d,
        }
    }
}
impl<S: Simd> Neg for Ou<S> {
    type Output = Self;
    /// value and tangent negated
    #[inline(always)]
    fn neg(self) -> Ou<S> {
        Ou { v: -self.v, d: -self.d }
    }
}
impl<S: Simd> Mul for Ou<S> {
    type Output = Self;
    /// the product, its tangent v o.d + d o.v through the dot accumulator (feature `mutate`:
    /// `mutate::OU_TAN` drops the term d o.v)
    #[inline(always)]
    fn mul(self, o: Ou<S>) -> Ou<S> {
        let mut d = ODotAcc::zero();
        d.add_prod_mut(&self.v, &o.d);
        if !mutate::on(mutate::OU_TAN) {
            d.add_prod_mut(&self.d, &o.v);
        }
        Ou {
            v: self.v * o.v,
            d: d.finish(),
        }
    }
}
impl<S: Simd> Div for Ou<S> {
    type Output = Self;
    /// the quotient q = v / o.v, its tangent (d - q o.d) / o.v
    #[inline(always)]
    fn div(self, o: Ou<S>) -> Ou<S> {
        let q = self.v / o.v;
        Ou {
            v: q,
            d: (self.d - q * o.d) / o.v,
        }
    }
}

impl<S: Simd> Lane for Ou<S> {
    type S = S;
    type Acc = (ODotAcc<S>, ODotAcc<S>);
    dd_param!();
    const TANGENT: bool = true;
    const VAL_OD: bool = true;
    /// zero value and tangent
    #[inline(always)]
    fn zero() -> Self {
        Ou {
            v: OV::zero(),
            d: OV::zero(),
        }
    }
    /// the constant c, exactly, with a zero tangent
    #[inline(always)]
    fn cst(c: DV<S>) -> Self {
        Ou {
            v: OV::from_dv(c),
            d: OV::zero(),
        }
    }
    /// value and tangent times the constant c
    #[inline(always)]
    fn mulc(self, c: DV<S>) -> Self {
        Ou {
            v: self.v.mul_dv(c),
            d: self.d.mul_dv(c),
        }
    }
    /// value and tangent times an exact f64
    #[inline(always)]
    fn mulf(self, s: f64) -> Self {
        Ou {
            v: self.v.mul_f(s),
            d: self.d.mul_f(s),
        }
    }
    /// value and tangent times a power of two, exactly
    #[inline(always)]
    fn mul_pwr2(self, s: f64) -> Self {
        Ou {
            v: self.v.mul_pwr2(s),
            d: self.d.mul_pwr2(s),
        }
    }
    /// the value plus the constant c
    #[inline(always)]
    fn addc(self, c: DV<S>) -> Self {
        Ou {
            v: self.v.add_dv(c),
            d: self.d,
        }
    }
    /// all 8 lanes of value and tangent = lane j
    #[inline(always)]
    fn bcast(self, j: usize) -> Self {
        Ou {
            v: self.v.bcast(j),
            d: self.d.bcast(j),
        }
    }
    /// the value rounded to double-double
    #[inline(always)]
    fn val(self) -> DV<S> {
        self.v.to_dv()
    }
    /// the tangent rounded to double-double
    #[inline(always)]
    fn tan(self) -> DV<S> {
        self.d.to_dv()
    }
    /// value v and tangent t, exactly
    #[inline(always)]
    fn from_vt(v: DV<S>, t: DV<S>) -> Self {
        Ou {
            v: OV::from_dv(v),
            d: OV::from_dv(t),
        }
    }
    /// the empty sums of the value and of the tangent
    #[inline(always)]
    fn acc0() -> Self::Acc {
        (ODotAcc::zero(), ODotAcc::zero())
    }
    /// a + x y: the value's product and the tangent's two
    #[inline(always)]
    fn acc(a: Self::Acc, x: Self, y: Self) -> Self::Acc {
        let mut a = a;
        Self::acc_mut(&mut a, &x, &y);
        a
    }
    /// `acc` in place (`ODotAcc::add_prod_mut`)
    #[inline(always)]
    fn acc_mut(a: &mut Self::Acc, x: &Self, y: &Self) {
        a.0.add_prod_mut(&x.v, &y.v);
        a.1.add_prod_mut(&x.v, &y.d);
        a.1.add_prod_mut(&x.d, &y.v);
    }
    /// a + x c, c a constant lane vector
    #[inline(always)]
    fn accc(a: Self::Acc, x: Self, c: DV<S>) -> Self::Acc {
        let mut a = a;
        a.0.add_prod_dv_mut(&x.v, &c);
        a.1.add_prod_dv_mut(&x.d, &c);
        a
    }
    /// a + x
    #[inline(always)]
    fn acc1(a: Self::Acc, x: Self) -> Self::Acc {
        (a.0.add(x.v), a.1.add(x.d))
    }
    /// the sums of the value and of the tangent
    #[inline(always)]
    fn fin(a: Self::Acc) -> Self {
        Ou {
            v: a.0.finish(),
            d: a.1.finish(),
        }
    }
    /// the value (k = 0) and tangent (k = 1) rounded to quad-double, zero past them
    #[inline(always)]
    fn coef_qd(self, k: usize) -> QV<S> {
        self.coef_od(k).to_qv()
    }
    /// the octo-double value (k = 0) and tangent (k = 1), zero past them
    #[inline(always)]
    fn coef_od(self, k: usize) -> OV<S> {
        match k {
            0 => self.v,
            1 => self.d,
            _ => OV::zero(),
        }
    }
}

/// Forward-mode dual number over octo-double lanes with N tangents: value `v` and tangents `d`, all `OV`, so that one
/// evaluation with a unit tangent on each of N unknowns gives N Jacobian columns, the value's operations done once
/// for all of them. Each tangent runs `Ou`'s operations on its own (`Ou`'s product, quotient and dot accumulators,
/// in the same order), so tangent k is bit for bit the tangent of an `Ou` evaluation seeded as tangent k, and the
/// value bit for bit its value. Constants and inputs enter as double-double as for `Ou`; the octo-double value and
/// tangents are built and read through `Tangents`.
#[derive(Clone, Copy, Debug)]
pub struct Oun<S: Simd, const N: usize> {
    /// the value
    pub v: OV<S>,
    /// the tangents
    pub d: [OV<S>; N],
}

impl<S: Simd, const N: usize> Add for Oun<S, N> {
    type Output = Self;
    /// value and tangents added
    #[inline(always)]
    fn add(self, o: Self) -> Self {
        Oun {
            v: self.v + o.v,
            d: std::array::from_fn(|k| self.d[k] + o.d[k]),
        }
    }
}
impl<S: Simd, const N: usize> Sub for Oun<S, N> {
    type Output = Self;
    /// value and tangents subtracted
    #[inline(always)]
    fn sub(self, o: Self) -> Self {
        Oun {
            v: self.v - o.v,
            d: std::array::from_fn(|k| self.d[k] - o.d[k]),
        }
    }
}
impl<S: Simd, const N: usize> Neg for Oun<S, N> {
    type Output = Self;
    /// value and tangents negated
    #[inline(always)]
    fn neg(self) -> Self {
        Oun {
            v: -self.v,
            d: self.d.map(|x| -x),
        }
    }
}
impl<S: Simd, const N: usize> Mul for Oun<S, N> {
    type Output = Self;
    /// the product, each tangent v o.d + d o.v through the dot accumulator as `Ou`'s (feature `mutate`:
    /// `mutate::OU_TAN` drops the term d o.v)
    #[inline(always)]
    fn mul(self, o: Self) -> Self {
        let d = std::array::from_fn(|k| {
            let mut a = ODotAcc::zero();
            a.add_prod_mut(&self.v, &o.d[k]);
            if !mutate::on(mutate::OU_TAN) {
                a.add_prod_mut(&self.d[k], &o.v);
            }
            a.finish()
        });
        Oun { v: self.v * o.v, d }
    }
}
impl<S: Simd, const N: usize> Div for Oun<S, N> {
    type Output = Self;
    /// the quotient q = v / o.v, each tangent (d - q o.d) / o.v (the quotient rule, whose - and * the lint flags)
    #[inline(always)]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, o: Self) -> Self {
        let q = self.v / o.v;
        Oun {
            v: q,
            d: std::array::from_fn(|k| (self.d[k] - q * o.d[k]) / o.v),
        }
    }
}

impl<S: Simd, const N: usize> Lane for Oun<S, N> {
    type S = S;
    type Acc = (ODotAcc<S>, [ODotAcc<S>; N]);
    dd_param!();
    const TANGENT: bool = true;
    const VAL_OD: bool = true;
    const NTD: usize = N;
    /// zero value and tangents
    #[inline(always)]
    fn zero() -> Self {
        Oun {
            v: OV::zero(),
            d: [OV::zero(); N],
        }
    }
    /// the constant c, exactly, with zero tangents
    #[inline(always)]
    fn cst(c: DV<S>) -> Self {
        Oun {
            v: OV::from_dv(c),
            d: [OV::zero(); N],
        }
    }
    /// value and tangents times the constant c
    #[inline(always)]
    fn mulc(self, c: DV<S>) -> Self {
        Oun {
            v: self.v.mul_dv(c),
            d: self.d.map(|x| x.mul_dv(c)),
        }
    }
    /// value and tangents times an exact f64
    #[inline(always)]
    fn mulf(self, s: f64) -> Self {
        Oun {
            v: self.v.mul_f(s),
            d: self.d.map(|x| x.mul_f(s)),
        }
    }
    /// value and tangents times a power of two, exactly
    #[inline(always)]
    fn mul_pwr2(self, s: f64) -> Self {
        Oun {
            v: self.v.mul_pwr2(s),
            d: self.d.map(|x| x.mul_pwr2(s)),
        }
    }
    /// the value plus the constant c
    #[inline(always)]
    fn addc(self, c: DV<S>) -> Self {
        Oun {
            v: self.v.add_dv(c),
            d: self.d,
        }
    }
    /// all 8 lanes of value and tangents = lane j
    #[inline(always)]
    fn bcast(self, j: usize) -> Self {
        Oun {
            v: self.v.bcast(j),
            d: self.d.map(|x| x.bcast(j)),
        }
    }
    /// the value rounded to double-double
    #[inline(always)]
    fn val(self) -> DV<S> {
        self.v.to_dv()
    }
    /// the first tangent rounded to double-double
    #[inline(always)]
    fn tan(self) -> DV<S> {
        self.tan_k(0)
    }
    /// tangent k rounded to double-double
    #[inline(always)]
    fn tan_k(self, k: usize) -> DV<S> {
        if k < N {
            self.d[k].to_dv()
        } else {
            DV::zero()
        }
    }
    /// value v and first tangent t, exactly, the other tangents zero
    #[inline(always)]
    fn from_vt(v: DV<S>, t: DV<S>) -> Self {
        let mut x = Self::cst(v);
        if N > 0 {
            x.d[0] = OV::from_dv(t);
        }
        x
    }
    /// value v and tangents t, exactly (zero past t)
    #[inline(always)]
    fn from_vt_n(v: DV<S>, t: &[DV<S>]) -> Self {
        Oun {
            v: OV::from_dv(v),
            d: std::array::from_fn(|k| t.get(k).map_or_else(OV::zero, |&x| OV::from_dv(x))),
        }
    }
    /// the empty sums of the value and of the tangents
    #[inline(always)]
    fn acc0() -> Self::Acc {
        (ODotAcc::zero(), [ODotAcc::zero(); N])
    }
    /// a + x y: the value's product and each tangent's two, as `Ou`'s
    #[inline(always)]
    fn acc(a: Self::Acc, x: Self, y: Self) -> Self::Acc {
        let mut a = a;
        Self::acc_mut(&mut a, &x, &y);
        a
    }
    /// `acc` in place
    #[inline(always)]
    fn acc_mut(a: &mut Self::Acc, x: &Self, y: &Self) {
        a.0.add_prod_mut(&x.v, &y.v);
        for k in 0..N {
            a.1[k].add_prod_mut(&x.v, &y.d[k]);
            a.1[k].add_prod_mut(&x.d[k], &y.v);
        }
    }
    /// a + x c, c a constant lane vector
    #[inline(always)]
    fn accc(a: Self::Acc, x: Self, c: DV<S>) -> Self::Acc {
        let mut a = a;
        a.0.add_prod_dv_mut(&x.v, &c);
        for k in 0..N {
            a.1[k].add_prod_dv_mut(&x.d[k], &c);
        }
        a
    }
    /// a + x
    #[inline(always)]
    fn acc1(a: Self::Acc, x: Self) -> Self::Acc {
        (a.0.add(x.v), std::array::from_fn(|k| a.1[k].add(x.d[k])))
    }
    /// the sums of the value and of the tangents
    #[inline(always)]
    fn fin(a: Self::Acc) -> Self {
        Oun {
            v: a.0.finish(),
            d: a.1.map(|x| x.finish()),
        }
    }
    /// the value (k = 0) and tangent k - 1 (k = 1..=N) rounded to quad-double, zero past them
    #[inline(always)]
    fn coef_qd(self, k: usize) -> QV<S> {
        self.coef_od(k).to_qv()
    }
    /// the octo-double value (k = 0) and tangent k - 1 (k = 1..=N), zero past them
    #[inline(always)]
    fn coef_od(self, k: usize) -> OV<S> {
        match k {
            0 => self.v,
            k if k <= N => self.d[k - 1],
            _ => OV::zero(),
        }
    }
}

/// A dual lane whose value and tangents are in one lane type `V` (octo-double for `Ou` and `Oun<N>`): built from them
/// exactly and read back exactly, for code that seeds several tangents at once (a Jacobian's columns)
pub trait Tangents: Lane {
    /// the lane type of the value and of each tangent
    type V: Lane<S = Self::S>;
    /// value v and tangents t (`NTD` of them, zero past t), exactly
    fn from_tangents(v: Self::V, t: &[Self::V]) -> Self;
    /// the value
    fn value(&self) -> Self::V;
    /// tangent k < `NTD`
    fn tangent(&self, k: usize) -> Self::V;
}

impl<S: Simd> Tangents for Ou<S> {
    type V = OV<S>;
    #[inline(always)]
    fn from_tangents(v: OV<S>, t: &[OV<S>]) -> Self {
        Ou {
            v,
            d: t.first().copied().unwrap_or_else(OV::zero),
        }
    }
    #[inline(always)]
    fn value(&self) -> OV<S> {
        self.v
    }
    #[inline(always)]
    fn tangent(&self, k: usize) -> OV<S> {
        debug_assert_eq!(k, 0, "Ou has one tangent");
        self.d
    }
}

impl<S: Simd, const N: usize> Tangents for Oun<S, N> {
    type V = OV<S>;
    #[inline(always)]
    fn from_tangents(v: OV<S>, t: &[OV<S>]) -> Self {
        Oun {
            v,
            d: std::array::from_fn(|k| t.get(k).copied().unwrap_or_else(OV::zero)),
        }
    }
    #[inline(always)]
    fn value(&self) -> OV<S> {
        self.v
    }
    #[inline(always)]
    fn tangent(&self, k: usize) -> OV<S> {
        self.d[k]
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
        F8(self.0.neg())
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
    dd_param!();
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
        Fu {
            v: self.v.neg(),
            d: self.d.neg(),
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
    dd_param!();
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
            d[i] = self.d[i].neg();
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
    dd_param!();
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
    /// `acc` in place: the same operations on each tangent and the value
    #[inline(always)]
    fn acc_mut(a: &mut Self::Acc, x: &Self, y: &Self) {
        for i in 0..N {
            a.1[i] = x.v.hi.fma(y.d[i], x.d[i].fma(y.v.hi, a.1[i]));
        }
        a.0 = a.0.add_prod(x.v, y.v);
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
        Fun {
            v: self.v.neg(),
            d: self.d.map(|x| x.neg()),
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
    dd_param!();
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
    /// `acc` in place: the same operations on each tangent and the value
    #[inline(always)]
    fn acc_mut(a: &mut Self::Acc, x: &Self, y: &Self) {
        for i in 0..N {
            a.1[i] = x.v.fma(y.d[i], x.d[i].fma(y.v, a.1[i]));
        }
        a.0 = x.v.fma(y.v, a.0);
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

// ---------------------------------------------------------------------------------------------------------------
// counting lanes
// ---------------------------------------------------------------------------------------------------------------

/// The kinds of lane operation `Counted` counts; `take_counts()[i]` is the count of `COUNTED_OPS[i]` (`op` names the
/// indices). "x f64" covers `mulf`, `mul_pwr2` and `mulf_upto`, "x const" `mulc`, `muls` and `mulp`, "+ const" `addc`
/// and `addp`; `cst`, `splat`,
/// `bcast`, `val`, `tan`, `from_vt` and the f64 tangent accessors move data and are not counted.
pub const COUNTED_OPS: [&str; 11] = [
    "add/sub", "mul", "div", "neg", "x const", "x f64", "+ const", "acc a b", "acc a c", "acc a", "finish",
];

/// The index of each kind of operation in `take_counts()` and `COUNTED_OPS`.
pub mod op {
    pub const ADD_SUB: usize = 0;
    pub const MUL: usize = 1;
    pub const DIV: usize = 2;
    pub const NEG: usize = 3;
    /// `mulc`, `muls`, `mulp`
    pub const MULC: usize = 4;
    /// `mulf`, `mul_pwr2`, `mulf_upto`
    pub const MULF: usize = 5;
    /// `addc`, `addp`
    pub const ADDC: usize = 6;
    pub const ACC: usize = 7;
    pub const ACCC: usize = 8;
    pub const ACC1: usize = 9;
    pub const FIN: usize = 10;
}

std::thread_local!(static COUNTS: std::cell::RefCell<[u64; 11]> = const { std::cell::RefCell::new([0; 11]) });

#[inline(always)]
fn count(i: usize) {
    COUNTS.with(|c| c.borrow_mut()[i] += 1);
}

/// add n to count i (for operations counted as a whole, as `field::MatLane::dmat_apply` on `Counted`)
#[inline(always)]
pub(crate) fn count_n(i: usize, n: u64) {
    COUNTS.with(|c| c.borrow_mut()[i] += n);
}

/// This thread's operation counts since the last call (in the order of `COUNTED_OPS`), and reset them. The counts
/// are per thread: run the computation to be counted on one thread.
pub fn take_counts() -> [u64; 11] {
    COUNTS.with(|c| std::mem::take(&mut *c.borrow_mut()))
}

/// A lane type L with every arithmetic operation counted (one count per 8-lane operation, by kind: `COUNTED_OPS`),
/// for operation counts of code generic over `Lane`: what a computation would cost in another lane type is the
/// counts times that type's cost per operation. The results are bitwise L's.
#[derive(Clone, Copy, Debug)]
pub struct Counted<L: Lane>(pub L);

macro_rules! counted_binop {
    ($tr:ident, $f:ident, $i:expr) => {
        impl<L: Lane> $tr for Counted<L> {
            type Output = Self;
            #[inline(always)]
            fn $f(self, o: Self) -> Self {
                count($i);
                Counted($tr::$f(self.0, o.0))
            }
        }
    };
}
counted_binop!(Add, add, op::ADD_SUB);
counted_binop!(Sub, sub, op::ADD_SUB);
counted_binop!(Mul, mul, op::MUL);
counted_binop!(Div, div, op::DIV);

impl<L: Lane> Neg for Counted<L> {
    type Output = Self;
    #[inline(always)]
    fn neg(self) -> Self {
        count(op::NEG);
        Counted(-self.0)
    }
}

impl<L: Lane> Lane for Counted<L> {
    type S = L::S;
    type Acc = L::Acc;
    const TANGENT: bool = L::TANGENT;
    const VAL_F64: bool = L::VAL_F64;
    const TAN_F64: bool = L::TAN_F64;
    const NT: usize = L::NT;
    const VAL_QD: bool = L::VAL_QD;
    const VAL_OD: bool = L::VAL_OD;
    const NJ: usize = L::NJ;
    type P = L::P;
    #[inline(always)]
    fn var(c: DD) -> Self {
        Counted(L::var(c))
    }
    #[inline(always)]
    fn mulp(self, p: L::P) -> Self {
        count(op::MULC);
        Counted(self.0.mulp(p))
    }
    #[inline(always)]
    fn addp(self, p: L::P) -> Self {
        count(op::ADDC);
        Counted(self.0.addp(p))
    }
    #[inline(always)]
    fn coef(self, k: usize) -> DV<Self::S> {
        self.0.coef(k)
    }
    #[inline(always)]
    fn set_coef(&mut self, k: usize, c: DV<Self::S>) {
        self.0.set_coef(k, c)
    }
    #[inline(always)]
    fn coef_qd(self, k: usize) -> QV<Self::S> {
        self.0.coef_qd(k)
    }
    #[inline(always)]
    fn set_coef_qd(&mut self, k: usize, c: QV<Self::S>) {
        self.0.set_coef_qd(k, c)
    }
    #[inline(always)]
    fn coef_od(self, k: usize) -> OV<Self::S> {
        self.0.coef_od(k)
    }
    #[inline(always)]
    fn set_coef_od(&mut self, k: usize, c: OV<Self::S>) {
        self.0.set_coef_od(k, c)
    }
    #[inline(always)]
    fn zero() -> Self {
        Counted(L::zero())
    }
    #[inline(always)]
    fn cst(c: DV<Self::S>) -> Self {
        Counted(L::cst(c))
    }
    #[inline(always)]
    fn splat(x: DD) -> Self {
        Counted(L::splat(x))
    }
    #[inline(always)]
    fn mulc(self, c: DV<Self::S>) -> Self {
        count(op::MULC);
        Counted(self.0.mulc(c))
    }
    #[inline(always)]
    fn muls(self, s: DD) -> Self {
        count(op::MULC);
        Counted(self.0.muls(s))
    }
    #[inline(always)]
    fn mulf(self, s: f64) -> Self {
        count(op::MULF);
        Counted(self.0.mulf(s))
    }
    /// counted as `mulf`
    #[inline(always)]
    fn mulf_upto(self, s: f64, k: usize) -> Self {
        count(op::MULF);
        Counted(self.0.mulf_upto(s, k))
    }
    #[inline(always)]
    fn mul_pwr2(self, s: f64) -> Self {
        count(op::MULF);
        Counted(self.0.mul_pwr2(s))
    }
    #[inline(always)]
    fn addc(self, c: DV<Self::S>) -> Self {
        count(op::ADDC);
        Counted(self.0.addc(c))
    }
    #[inline(always)]
    fn bcast(self, j: usize) -> Self {
        Counted(self.0.bcast(j))
    }
    #[inline(always)]
    fn val(self) -> DV<Self::S> {
        self.0.val()
    }
    #[inline(always)]
    fn tan(self) -> DV<Self::S> {
        self.0.tan()
    }
    #[inline(always)]
    fn from_vt(v: DV<Self::S>, t: DV<Self::S>) -> Self {
        Counted(L::from_vt(v, t))
    }
    #[inline(always)]
    fn acc0() -> Self::Acc {
        L::acc0()
    }
    #[inline(always)]
    fn acc(a: Self::Acc, x: Self, y: Self) -> Self::Acc {
        count(op::ACC);
        L::acc(a, x.0, y.0)
    }
    /// counted as `acc`
    #[inline(always)]
    fn acc_mut(a: &mut Self::Acc, x: &Self, y: &Self) {
        count(op::ACC);
        L::acc_mut(a, &x.0, &y.0)
    }
    #[inline(always)]
    fn accc(a: Self::Acc, x: Self, c: DV<Self::S>) -> Self::Acc {
        count(op::ACCC);
        L::accc(a, x.0, c)
    }
    #[inline(always)]
    fn acc1(a: Self::Acc, x: Self) -> Self::Acc {
        count(op::ACC1);
        L::acc1(a, x.0)
    }
    #[inline(always)]
    fn fin(a: Self::Acc) -> Self {
        count(op::FIN);
        Counted(L::fin(a))
    }
    /// counted as `acc`
    #[inline(always)]
    fn acc_at(a: &mut Self::Acc, x: &Self, y: &Self, k: usize) {
        count(op::ACC);
        L::acc_at(a, &x.0, &y.0, k)
    }
    /// counted as `fin`
    #[inline(always)]
    fn fin_at(a: &Self::Acc, k: usize, into: &mut Self) {
        count(op::FIN);
        L::fin_at(a, k, &mut into.0)
    }
    /// counted as `*`
    #[inline(always)]
    fn mul_at(x: &Self, y: &Self, k: usize, into: &mut Self) {
        count(op::MUL);
        L::mul_at(&x.0, &y.0, k, &mut into.0)
    }
    /// counted as `/`
    #[inline(always)]
    fn div_at(x: &Self, y: &Self, k: usize, into: &mut Self) {
        count(op::DIV);
        L::div_at(&x.0, &y.0, k, &mut into.0)
    }
    /// counted as `mulp`
    #[inline(always)]
    fn mulp_at(x: &Self, p: &L::P, k: usize, into: &mut Self) {
        count(op::MULC);
        L::mulp_at(&x.0, p, k, &mut into.0)
    }
    /// not counted, as `coef` and `set_coef`
    #[inline(always)]
    fn copy_at(from: &Self, k: usize, into: &mut Self) {
        L::copy_at(&from.0, k, &mut into.0)
    }
    #[inline(always)]
    fn tan64(self, k: usize) -> V8<Self::S> {
        self.0.tan64(k)
    }
    #[inline(always)]
    fn set_tan64(&mut self, k: usize, t: V8<Self::S>) {
        self.0.set_tan64(k, t)
    }
}
