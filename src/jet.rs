//! `Jet<N>`: a truncated power series in one variable h, N double-double lane vectors c\[0\], …, c\[N − 1\] for the
//! orders 0, …, N − 1 (c\[0\] is the value). Products are Cauchy products truncated at order N − 1 and quotients
//! the series-reciprocal recurrence, so a computation written over [`Lane`] evaluated on jets gives its own Taylor
//! coefficients in h. With a parameter entered as [`Lane::var`] (the jet c + h) the coefficients are those of the
//! computation in that parameter: the right-hand sides of a high-order Taylor continuation of a branch (the
//! asymptotic numerical method, Cochelin, Int. J. Numer. Methods Eng. 37 (1994) 1187, doi:10.1002/nme.1620370706).
//! `Jet<2>` is a dual number (`Du`) with the tangent as c\[1\].
//!
//! [`QJet<N>`] is the same in quad-double, with [`QSeries<N>`] its parameter arithmetic: the coefficients to
//! quad-double accuracy where a cancellation in the computation amplifies double-double rounding past what the
//! continuation needs. [`OJet<N>`] and [`OSeries<N>`] are the same in octo-double, for when that amplification
//! exceeds even quad-double.
#![allow(clippy::needless_range_loop)]
use crate::dd::DD;
use crate::dual::{mutate, Lane, Param};
use crate::dv::{DotAcc, DV};
use crate::od::{OdAcc, OD};
use crate::ov::{ODotAcc, OV};
use crate::qd::{QdAcc, QD};
use crate::qv::{QDotAcc, QV};
use crate::simd::Simd;
use std::ops::{Add, Div, Mul, Neg, Sub};

/// A scalar truncated power series, N double-double coefficients: the parameter arithmetic ([`Lane::P`]) of `Jet<N>`,
/// with `Param::var(c)` the series c + h
#[derive(Clone, Copy, Debug)]
pub struct Series<const N: usize> {
    pub c: [DD; N],
}

impl<const N: usize> Add for Series<N> {
    type Output = Self;
    #[inline(always)]
    fn add(self, o: Self) -> Self {
        let mut c = self.c;
        for k in 0..N {
            c[k] = self.c[k] + o.c[k];
        }
        Series { c }
    }
}
impl<const N: usize> Sub for Series<N> {
    type Output = Self;
    #[inline(always)]
    fn sub(self, o: Self) -> Self {
        let mut c = self.c;
        for k in 0..N {
            c[k] = self.c[k] - o.c[k];
        }
        Series { c }
    }
}
impl<const N: usize> Neg for Series<N> {
    type Output = Self;
    #[inline(always)]
    fn neg(self) -> Self {
        Series { c: self.c.map(|x| -x) }
    }
}
impl<const N: usize> Mul for Series<N> {
    type Output = Self;
    #[inline(always)]
    fn mul(self, o: Self) -> Self {
        let mut c = [DD::ZERO; N];
        for k in 0..N {
            for i in 0..=k {
                c[k] = c[k] + self.c[i] * o.c[k - i];
            }
        }
        Series { c }
    }
}
impl<const N: usize> Div for Series<N> {
    type Output = Self;
    /// q = x / y by q_k = (x_k − Σ_{i=1..k} y_i q_{k−i}) / y_0
    #[inline(always)]
    fn div(self, o: Self) -> Self {
        let mut q = [DD::ZERO; N];
        q[0] = self.c[0] / o.c[0];
        for k in 1..N {
            let mut s = DD::ZERO;
            for i in 1..=k {
                s = s + o.c[i] * q[k - i];
            }
            q[k] = (self.c[k] - s) / o.c[0];
        }
        Series { c: q }
    }
}

impl<const N: usize> Param for Series<N> {
    #[inline(always)]
    fn one() -> Self {
        Self::from_dd(DD::ONE)
    }
    #[inline(always)]
    fn from_f64(x: f64) -> Self {
        Self::from_dd(DD::from_f64(x))
    }
    #[inline(always)]
    fn from_dd(x: DD) -> Self {
        const { assert!(N >= 1, "a series has at least its value") }
        let mut c = [DD::ZERO; N];
        c[0] = x;
        Series { c }
    }
    #[inline(always)]
    fn mul_f(self, s: f64) -> Self {
        Series {
            c: self.c.map(|x| x.mul_f(s)),
        }
    }
    #[inline(always)]
    fn var(c: DD) -> Self {
        let mut s = Self::from_dd(c);
        if N > 1 {
            s.c[1] = DD::ONE;
        }
        s
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Jet<S: Simd, const N: usize> {
    pub c: [DV<S>; N],
}

impl<S: Simd, const N: usize> Jet<S, N> {
    /// the series with the given coefficients
    #[inline(always)]
    pub fn from_coeffs(c: [DV<S>; N]) -> Self {
        const { assert!(N >= 1, "a jet has at least its value") }
        Jet { c }
    }
    /// the series variable with lane j's value c\[j\]: coefficient 0 the values, coefficient 1 one
    pub fn var_lanes(c: &[DD; 8]) -> Self {
        let hi: [f64; 8] = std::array::from_fn(|j| c[j].hi);
        let lo: [f64; 8] = std::array::from_fn(|j| c[j].lo);
        let mut j = Self::cst(DV::load(&hi, &lo));
        if N > 1 {
            j.c[1] = DV::splat(DD::ONE);
        }
        j
    }
    /// coefficient k (order k), zero past the truncation
    #[inline(always)]
    pub fn coef(self, k: usize) -> DV<S> {
        if k < N {
            self.c[k]
        } else {
            DV::zero()
        }
    }
    /// the Cauchy product's coefficient k of x and y, orders 0..=k through the dot accumulator
    #[inline(always)]
    fn conv(x: &[DV<S>; N], y: &[DV<S>; N], k: usize) -> DotAcc<S> {
        let mut a = DotAcc::zero();
        for i in 0..=k {
            a = a.add_prod(x[i], y[k - i]);
        }
        a
    }
}

impl<S: Simd, const N: usize> Add for Jet<S, N> {
    type Output = Self;
    #[inline(always)]
    fn add(self, o: Self) -> Self {
        let mut c = self.c;
        for k in 0..N {
            c[k] = self.c[k] + o.c[k];
        }
        Jet { c }
    }
}
impl<S: Simd, const N: usize> Sub for Jet<S, N> {
    type Output = Self;
    #[inline(always)]
    fn sub(self, o: Self) -> Self {
        let mut c = self.c;
        for k in 0..N {
            c[k] = self.c[k] - o.c[k];
        }
        Jet { c }
    }
}
impl<S: Simd, const N: usize> Neg for Jet<S, N> {
    type Output = Self;
    #[inline(always)]
    fn neg(self) -> Self {
        let mut v = self.c;
        for x in v.iter_mut() {
            *x = -*x;
        }
        Jet { c: v }
    }
}
impl<S: Simd, const N: usize> Mul for Jet<S, N> {
    type Output = Self;
    #[inline(always)]
    fn mul(self, o: Self) -> Self {
        Jet {
            c: std::array::from_fn(|k| Self::conv(&self.c, &o.c, k).finish()),
        }
    }
}
impl<S: Simd, const N: usize> Div for Jet<S, N> {
    type Output = Self;
    /// q = x / y by q_k = (x_k − Σ_{i=1..k} y_i q_{k−i}) / y_0
    #[inline(always)]
    fn div(self, o: Self) -> Self {
        // the 3N quotients by o.c[0].hi share its divisor (on AVX-512 its reciprocal)
        let r = o.c[0].hi.divisor();
        let mut q = self.c;
        q[0] = self.c[0].div_by(o.c[0], r);
        for k in 1..N {
            let mut a = DotAcc::zero();
            for i in 1..=k {
                a = a.add_prod(o.c[i], q[k - i]);
            }
            q[k] = (self.c[k] - a.finish()).div_by(o.c[0], r);
        }
        Jet { c: q }
    }
}

impl<S: Simd, const N: usize> Lane for Jet<S, N> {
    type S = S;
    type Acc = [DotAcc<S>; N];
    type P = Series<N>;
    const TANGENT: bool = true;
    const NJ: usize = N;
    /// the Cauchy product with the scalar series, coefficient k from the orders 0..=k through the dot accumulator
    #[inline(always)]
    fn mulp(self, p: Series<N>) -> Self {
        let mut c = self.c;
        for k in 0..N {
            let mut a = DotAcc::zero();
            for i in 0..=k {
                a = a.add_prod(self.c[i], DV::splat(p.c[k - i]));
            }
            c[k] = a.finish();
        }
        Jet { c }
    }
    #[inline(always)]
    fn addp(self, p: Series<N>) -> Self {
        let mut c = self.c;
        for k in 0..N {
            c[k] = self.c[k] + DV::splat(p.c[k]);
        }
        Jet { c }
    }
    #[inline(always)]
    fn coef(self, k: usize) -> DV<S> {
        Jet::coef(self, k)
    }
    #[inline(always)]
    fn set_coef(&mut self, k: usize, c: DV<S>) {
        self.c[k] = c;
    }
    /// set coefficient k from octo-double, rounded to double-double once (`OV::to_dv`)
    #[inline(always)]
    fn set_coef_od(&mut self, k: usize, c: OV<S>) {
        self.c[k] = c.to_dv();
    }
    #[inline(always)]
    fn zero() -> Self {
        Self::from_coeffs([DV::zero(); N])
    }
    #[inline(always)]
    fn cst(c: DV<S>) -> Self {
        let mut j = Self::zero();
        j.c[0] = c;
        j
    }
    /// the series variable itself, c + h
    #[inline(always)]
    fn var(c: DD) -> Self {
        let mut j = Self::splat(c);
        if N > 1 {
            j.c[1] = DV::splat(DD::ONE);
        }
        j
    }
    #[inline(always)]
    fn mulc(self, c: DV<S>) -> Self {
        let mut v = self.c;
        for x in v.iter_mut() {
            *x = *x * c;
        }
        Jet { c: v }
    }
    #[inline(always)]
    fn mulf(self, s: f64) -> Self {
        let mut v = self.c;
        for x in v.iter_mut() {
            *x = x.mul_f(s);
        }
        Jet { c: v }
    }
    #[inline(always)]
    fn mul_pwr2(self, s: f64) -> Self {
        let mut v = self.c;
        for x in v.iter_mut() {
            *x = x.mul_pwr2(s);
        }
        Jet { c: v }
    }
    #[inline(always)]
    fn addc(self, c: DV<S>) -> Self {
        let mut j = self;
        j.c[0] = self.c[0] + c;
        j
    }
    #[inline(always)]
    fn bcast(self, j: usize) -> Self {
        let mut v = self.c;
        for x in v.iter_mut() {
            *x = x.bcast(j);
        }
        Jet { c: v }
    }
    #[inline(always)]
    fn val(self) -> DV<S> {
        self.c[0]
    }
    /// coefficient 1
    #[inline(always)]
    fn tan(self) -> DV<S> {
        self.coef(1)
    }
    /// value v, coefficient 1 t, the others zero
    #[inline(always)]
    fn from_vt(v: DV<S>, t: DV<S>) -> Self {
        let mut j = Self::cst(v);
        if N > 1 {
            j.c[1] = t;
        }
        j
    }
    #[inline(always)]
    fn acc0() -> Self::Acc {
        [DotAcc::zero(); N]
    }
    #[inline(always)]
    fn acc(a: Self::Acc, x: Self, y: Self) -> Self::Acc {
        let mut a = a;
        for k in 0..N {
            for i in 0..=k {
                a[k] = a[k].add_prod(x.c[i], y.c[k - i]);
            }
        }
        a
    }
    /// `acc` in place: the same products in the same order, without moving the N accumulators or the operands
    #[inline(always)]
    fn acc_mut(a: &mut Self::Acc, x: &Self, y: &Self) {
        for k in 0..N {
            let mut s = a[k];
            for i in 0..=k {
                s = s.add_prod(x.c[i], y.c[k - i]);
            }
            a[k] = s;
        }
    }
    #[inline(always)]
    fn accc(a: Self::Acc, x: Self, c: DV<S>) -> Self::Acc {
        let mut a = a;
        for k in 0..N {
            a[k] = a[k].add_prod(x.c[k], c);
        }
        a
    }
    #[inline(always)]
    fn acc1(a: Self::Acc, x: Self) -> Self::Acc {
        let mut a = a;
        for k in 0..N {
            a[k] = a[k].add(x.c[k]);
        }
        a
    }
    /// the sums, order by order, in a plain loop. Through `array::map` AVX2 and AVX-512 keep the
    /// closure out of line, without their target features (`crate::simd::Kernel`)
    #[inline(always)]
    fn fin(a: Self::Acc) -> Self {
        let mut c = [DV::zero(); N];
        for k in 0..N {
            c[k] = a[k].finish();
        }
        Jet { c }
    }
}

// ---------------------------------------------------------------------------------------------------------------
// quad-double jets
// ---------------------------------------------------------------------------------------------------------------

/// A scalar truncated power series, N quad-double coefficients: the parameter arithmetic ([`Lane::P`]) of
/// `QJet<N>`, with `Param::var(c)` the series c + h. Products and quotients sum through the scalar accumulator
/// `QdAcc`, the twin of `QJet`'s `QDotAcc`, so they are bitwise a `QJet<N>`'s with the series on every lane.
#[derive(Clone, Copy, Debug)]
pub struct QSeries<const N: usize> {
    pub c: [QD; N],
}

impl<const N: usize> QSeries<N> {
    /// the Cauchy product's coefficient k of x and y, orders 0..=k through the scalar dot accumulator
    #[inline(always)]
    fn conv(x: &[QD; N], y: &[QD; N], k: usize) -> QdAcc {
        let mut a = QdAcc::zero();
        for i in 0..=k {
            a = a.add_prod(x[i], y[k - i]);
        }
        a
    }
}

impl<const N: usize> Add for QSeries<N> {
    type Output = Self;
    #[inline(always)]
    fn add(self, o: Self) -> Self {
        let mut c = self.c;
        for k in 0..N {
            c[k] = self.c[k] + o.c[k];
        }
        QSeries { c }
    }
}
impl<const N: usize> Sub for QSeries<N> {
    type Output = Self;
    #[inline(always)]
    fn sub(self, o: Self) -> Self {
        let mut c = self.c;
        for k in 0..N {
            c[k] = self.c[k] - o.c[k];
        }
        QSeries { c }
    }
}
impl<const N: usize> Neg for QSeries<N> {
    type Output = Self;
    #[inline(always)]
    fn neg(self) -> Self {
        QSeries { c: self.c.map(|x| -x) }
    }
}
impl<const N: usize> Mul for QSeries<N> {
    type Output = Self;
    #[inline(always)]
    fn mul(self, o: Self) -> Self {
        let mut c = self.c;
        for k in 0..N {
            c[k] = Self::conv(&self.c, &o.c, k).finish();
        }
        QSeries { c }
    }
}
impl<const N: usize> Div for QSeries<N> {
    type Output = Self;
    /// q = x / y by q_k = (x_k − Σ_{i=1..k} y_i q_{k−i}) / y_0
    #[inline(always)]
    fn div(self, o: Self) -> Self {
        let mut q = self.c;
        q[0] = self.c[0] / o.c[0];
        for k in 1..N {
            let mut a = QdAcc::zero();
            for i in 1..=k {
                a = a.add_prod(o.c[i], q[k - i]);
            }
            q[k] = (self.c[k] - a.finish()) / o.c[0];
        }
        QSeries { c: q }
    }
}

impl<const N: usize> Param for QSeries<N> {
    #[inline(always)]
    fn one() -> Self {
        Self::from_dd(DD::ONE)
    }
    #[inline(always)]
    fn from_f64(x: f64) -> Self {
        Self::from_dd(DD::from_f64(x))
    }
    #[inline(always)]
    fn from_dd(x: DD) -> Self {
        const { assert!(N >= 1, "a series has at least its value") }
        let mut c = [QD::ZERO; N];
        c[0] = QD::from_dd(x);
        QSeries { c }
    }
    #[inline(always)]
    fn mul_f(self, s: f64) -> Self {
        QSeries {
            c: self.c.map(|x| x.mul_f(s)),
        }
    }
    #[inline(always)]
    fn var(c: DD) -> Self {
        let mut s = Self::from_dd(c);
        if N > 1 {
            s.c[1] = QD::ONE;
        }
        s
    }
}

/// `QJet<N>`: `Jet<N>` in quad-double, N quad-double lane vectors c\[0\], …, c\[N − 1\] for the orders 0, …, N − 1,
/// with the same operations: Cauchy products through the accumulator `QDotAcc`, quotients by the series-reciprocal
/// recurrence with the 4N quotients by c\[0\]'s leading part through one divisor (`QV::div_by`), and the parameter
/// arithmetic [`QSeries<N>`]. A computation over [`Lane`] evaluated on it gives its Taylor coefficients to quad-double
/// accuracy where `Jet<N>`'s are double-double: through a cancellation (a² − 1 near a = 1, say) the double-double
/// rounding is amplified into every order that depends on it, and here it is the quad-double rounding.
///
/// As for `QV` and `Qu`, the trait passes constants and inputs as double-double (they enter exactly), and `coef`,
/// `val` and `tan` round back to double-double. Quad-double coefficients enter and leave through
/// [`Lane::set_coef_qd`] and [`Lane::coef_qd`], [`QJet::var_lanes`] and the field `c`. `VAL_QD` is set: a solve of
/// a jet goes order by order, which is the caller's, as for `Jet<N>`.
#[derive(Clone, Copy, Debug)]
pub struct QJet<S: Simd, const N: usize> {
    pub c: [QV<S>; N],
}

impl<S: Simd, const N: usize> QJet<S, N> {
    /// the series with the given coefficients
    #[inline(always)]
    pub fn from_coeffs(c: [QV<S>; N]) -> Self {
        const { assert!(N >= 1, "a jet has at least its value") }
        QJet { c }
    }
    /// the series variable with lane j's value c\[j\]: coefficient 0 the values, coefficient 1 one
    pub fn var_lanes(c: &[QD; 8]) -> Self {
        let mut j = Self::from_coeffs([QV::zero(); N]);
        j.c[0] = QV::from_lanes(c);
        if N > 1 {
            j.c[1] = QV::splat(QD::ONE);
        }
        j
    }
    /// the Cauchy product's coefficient k of x and y, orders 0..=k through the dot accumulator
    #[inline(always)]
    fn conv(x: &[QV<S>; N], y: &[QV<S>; N], k: usize) -> QDotAcc<S> {
        let mut a = QDotAcc::zero();
        for i in 0..=k {
            a = a.add_prod(x[i], y[k - i]);
        }
        a
    }
}

impl<S: Simd, const N: usize> Add for QJet<S, N> {
    type Output = Self;
    #[inline(always)]
    fn add(self, o: Self) -> Self {
        let mut c = self.c;
        for k in 0..N {
            c[k] = self.c[k] + o.c[k];
        }
        QJet { c }
    }
}
impl<S: Simd, const N: usize> Sub for QJet<S, N> {
    type Output = Self;
    #[inline(always)]
    fn sub(self, o: Self) -> Self {
        let mut c = self.c;
        for k in 0..N {
            c[k] = self.c[k] - o.c[k];
        }
        QJet { c }
    }
}
impl<S: Simd, const N: usize> Neg for QJet<S, N> {
    type Output = Self;
    #[inline(always)]
    fn neg(self) -> Self {
        let mut v = self.c;
        for x in v.iter_mut() {
            *x = -*x;
        }
        QJet { c: v }
    }
}
impl<S: Simd, const N: usize> Mul for QJet<S, N> {
    type Output = Self;
    #[inline(always)]
    fn mul(self, o: Self) -> Self {
        let mut c = self.c;
        for k in 0..N {
            c[k] = Self::conv(&self.c, &o.c, k).finish();
        }
        QJet { c }
    }
}
impl<S: Simd, const N: usize> Div for QJet<S, N> {
    type Output = Self;
    /// q = x / y by q_k = (x_k − Σ_{i=1..k} y_i q_{k−i}) / y_0
    #[inline(always)]
    fn div(self, o: Self) -> Self {
        // the 4N quotients by o.c[0].c[0] share its divisor (on AVX-512 its reciprocal)
        let r = o.c[0].c[0].divisor();
        let mut q = self.c;
        q[0] = self.c[0].div_by(o.c[0], r);
        for k in 1..N {
            let mut a = QDotAcc::zero();
            for i in 1..=k {
                a = a.add_prod(o.c[i], q[k - i]);
            }
            q[k] = (self.c[k] - a.finish()).div_by(o.c[0], r);
        }
        QJet { c: q }
    }
}

impl<S: Simd, const N: usize> Lane for QJet<S, N> {
    type S = S;
    type Acc = [QDotAcc<S>; N];
    type P = QSeries<N>;
    const TANGENT: bool = true;
    const VAL_QD: bool = true;
    const NJ: usize = N;
    /// the Cauchy product with the scalar series, coefficient k from the orders 0..=k through the dot accumulator
    #[inline(always)]
    fn mulp(self, p: QSeries<N>) -> Self {
        let mut c = self.c;
        for k in 0..N {
            let mut a = QDotAcc::zero();
            for i in 0..=k {
                a = a.add_prod(self.c[i], QV::splat(p.c[k - i]));
            }
            c[k] = a.finish();
        }
        QJet { c }
    }
    #[inline(always)]
    fn addp(self, p: QSeries<N>) -> Self {
        let mut c = self.c;
        for k in 0..N {
            c[k] = self.c[k] + QV::splat(p.c[k]);
        }
        QJet { c }
    }
    /// coefficient k rounded to double-double, zero past the truncation
    #[inline(always)]
    fn coef(self, k: usize) -> DV<S> {
        self.coef_qd(k).to_dv()
    }
    #[inline(always)]
    fn set_coef(&mut self, k: usize, c: DV<S>) {
        self.c[k] = QV::from_dv(c);
    }
    /// coefficient k, zero past the truncation
    #[inline(always)]
    fn coef_qd(self, k: usize) -> QV<S> {
        if k < N {
            self.c[k]
        } else {
            QV::zero()
        }
    }
    #[inline(always)]
    fn set_coef_qd(&mut self, k: usize, c: QV<S>) {
        self.c[k] = c;
    }
    #[inline(always)]
    fn zero() -> Self {
        Self::from_coeffs([QV::zero(); N])
    }
    #[inline(always)]
    fn cst(c: DV<S>) -> Self {
        let mut j = Self::zero();
        j.c[0] = QV::from_dv(c);
        j
    }
    /// the series variable itself, c + h
    #[inline(always)]
    fn var(c: DD) -> Self {
        let mut j = Self::splat(c);
        if N > 1 {
            j.c[1] = QV::splat(QD::ONE);
        }
        j
    }
    #[inline(always)]
    fn mulc(self, c: DV<S>) -> Self {
        let c = QV::from_dv(c);
        let mut v = self.c;
        for x in v.iter_mut() {
            *x = *x * c;
        }
        QJet { c: v }
    }
    #[inline(always)]
    fn mulf(self, s: f64) -> Self {
        let mut v = self.c;
        for x in v.iter_mut() {
            *x = x.mul_f(s);
        }
        QJet { c: v }
    }
    #[inline(always)]
    fn mul_pwr2(self, s: f64) -> Self {
        let mut v = self.c;
        for x in v.iter_mut() {
            *x = x.mul_pwr2(s);
        }
        QJet { c: v }
    }
    #[inline(always)]
    fn addc(self, c: DV<S>) -> Self {
        let mut j = self;
        j.c[0] = self.c[0] + QV::from_dv(c);
        j
    }
    #[inline(always)]
    fn bcast(self, j: usize) -> Self {
        let mut v = self.c;
        for x in v.iter_mut() {
            *x = x.bcast(j);
        }
        QJet { c: v }
    }
    #[inline(always)]
    fn val(self) -> DV<S> {
        self.c[0].to_dv()
    }
    /// coefficient 1, rounded to double-double
    #[inline(always)]
    fn tan(self) -> DV<S> {
        self.coef(1)
    }
    /// value v, coefficient 1 t, the others zero
    #[inline(always)]
    fn from_vt(v: DV<S>, t: DV<S>) -> Self {
        let mut j = Self::cst(v);
        if N > 1 {
            j.c[1] = QV::from_dv(t);
        }
        j
    }
    #[inline(always)]
    fn acc0() -> Self::Acc {
        [QDotAcc::zero(); N]
    }
    #[inline(always)]
    fn acc(a: Self::Acc, x: Self, y: Self) -> Self::Acc {
        let mut a = a;
        for k in 0..N {
            for i in 0..=k {
                a[k] = a[k].add_prod(x.c[i], y.c[k - i]);
            }
        }
        a
    }
    /// `acc` in place: the same products in the same order, without moving the N accumulators or the operands. The
    /// convolution is one `Simd::hot` step with each product's step inlined in it, so that where the compiler keeps
    /// the step out of line (NEON, SSE2, portable) one call per term remains, not one per product.
    #[inline(always)]
    fn acc_mut(a: &mut Self::Acc, x: &Self, y: &Self) {
        S::hot(
            #[inline(always)]
            || {
                for k in 0..N {
                    let mut s = a[k];
                    for i in 0..=k {
                        s = s.plus_prod(&x.c[i], &y.c[k - i]);
                    }
                    a[k] = s;
                }
            },
        )
    }
    #[inline(always)]
    fn accc(a: Self::Acc, x: Self, c: DV<S>) -> Self::Acc {
        let c = QV::from_dv(c);
        let mut a = a;
        for k in 0..N {
            a[k] = a[k].add_prod(x.c[k], c);
        }
        a
    }
    #[inline(always)]
    fn acc1(a: Self::Acc, x: Self) -> Self::Acc {
        let mut a = a;
        for k in 0..N {
            a[k] = a[k].add(x.c[k]);
        }
        a
    }
    /// the sums, order by order, in a plain loop. Through `array::map` AVX2 and AVX-512 keep the
    /// closure out of line, without their target features (`crate::simd::Kernel`)
    #[inline(always)]
    fn fin(a: Self::Acc) -> Self {
        let mut c = [QV::zero(); N];
        for k in 0..N {
            c[k] = a[k].finish();
        }
        QJet { c }
    }
}

// ---------------------------------------------------------------------------------------------------------------
// octo-double jets
// ---------------------------------------------------------------------------------------------------------------

/// A scalar truncated power series, N octo-double coefficients: the parameter arithmetic ([`Lane::P`]) of
/// `OJet<N>`, with `Param::var(c)` the series c + h. Products and quotients sum through the scalar accumulator
/// `OdAcc`, the twin of `OJet`'s `ODotAcc`, so they are bitwise an `OJet<N>`'s with the series on every lane.
#[derive(Clone, Copy, Debug)]
pub struct OSeries<const N: usize> {
    /// the coefficients of the orders 0, ..., N - 1
    pub c: [OD; N],
}

impl<const N: usize> OSeries<N> {
    /// the Cauchy product's coefficient k of x and y, orders 0..=k through the scalar dot accumulator
    #[inline(always)]
    fn conv(x: &[OD; N], y: &[OD; N], k: usize) -> OdAcc {
        let mut a = OdAcc::zero();
        for i in 0..=k {
            a = a.add_prod(x[i], y[k - i]);
        }
        a
    }
}

impl<const N: usize> Add for OSeries<N> {
    type Output = Self;
    /// coefficient by coefficient
    #[inline(always)]
    fn add(self, o: Self) -> Self {
        let mut c = self.c;
        for k in 0..N {
            c[k] = self.c[k] + o.c[k];
        }
        OSeries { c }
    }
}
impl<const N: usize> Sub for OSeries<N> {
    type Output = Self;
    /// coefficient by coefficient
    #[inline(always)]
    fn sub(self, o: Self) -> Self {
        let mut c = self.c;
        for k in 0..N {
            c[k] = self.c[k] - o.c[k];
        }
        OSeries { c }
    }
}
impl<const N: usize> Neg for OSeries<N> {
    type Output = Self;
    /// every coefficient negated
    #[inline(always)]
    fn neg(self) -> Self {
        OSeries { c: self.c.map(|x| -x) }
    }
}
impl<const N: usize> Mul for OSeries<N> {
    type Output = Self;
    /// the Cauchy product truncated at order N - 1
    #[inline(always)]
    fn mul(self, o: Self) -> Self {
        let mut c = self.c;
        for k in 0..N {
            c[k] = Self::conv(&self.c, &o.c, k).finish();
        }
        OSeries { c }
    }
}
impl<const N: usize> Div for OSeries<N> {
    type Output = Self;
    /// q = x / y by q_k = (x_k − Σ_{i=1..k} y_i q_{k−i}) / y_0
    #[inline(always)]
    fn div(self, o: Self) -> Self {
        let mut q = self.c;
        q[0] = self.c[0] / o.c[0];
        for k in 1..N {
            let mut a = OdAcc::zero();
            for i in 1..=k {
                a = a.add_prod(o.c[i], q[k - i]);
            }
            q[k] = (self.c[k] - a.finish()) / o.c[0];
        }
        OSeries { c: q }
    }
}

impl<const N: usize> Param for OSeries<N> {
    /// the constant series 1
    #[inline(always)]
    fn one() -> Self {
        Self::from_dd(DD::ONE)
    }
    /// the constant series x, exactly
    #[inline(always)]
    fn from_f64(x: f64) -> Self {
        Self::from_dd(DD::from_f64(x))
    }
    /// the constant series x, exactly
    #[inline(always)]
    fn from_dd(x: DD) -> Self {
        const { assert!(N >= 1, "a series has at least its value") }
        let mut c = [OD::ZERO; N];
        c[0] = OD::from_dd(x);
        OSeries { c }
    }
    /// every coefficient times an exact f64
    #[inline(always)]
    fn mul_f(self, s: f64) -> Self {
        OSeries {
            c: self.c.map(|x| x.mul_f(s)),
        }
    }
    /// the series c + h
    #[inline(always)]
    fn var(c: DD) -> Self {
        let mut s = Self::from_dd(c);
        if N > 1 {
            s.c[1] = OD::ONE;
        }
        s
    }
}

/// `OJet<N>`: `Jet<N>` in octo-double, N octo-double lane vectors c\[0\], …, c\[N − 1\] for the orders 0, …, N − 1,
/// with the same operations as [`QJet<N>`]: Cauchy products through the accumulator `ODotAcc`, quotients by the
/// series-reciprocal recurrence with the 9N quotients by c\[0\]'s leading part through one divisor (`OV::div_by`), and
/// the parameter arithmetic [`OSeries<N>`]. A computation over [`Lane`] evaluated on it gives its Taylor coefficients
/// to octo-double accuracy, for when a quantity that grows through the computation amplifies even the quad-double
/// rounding of `QJet<N>` past what is needed.
///
/// As for `OV`, the trait passes constants and inputs as double-double (they enter exactly), and `coef`, `val` and
/// `tan` round back to double-double, `coef_qd` to quad-double. Octo-double coefficients enter and leave through
/// [`Lane::set_coef_od`] and [`Lane::coef_od`], [`OJet::var_lanes`] and the field `c`. `VAL_OD` is set and `VAL_QD`
/// is not: a solve of a jet goes order by order, which is the caller's, as for `QJet<N>`.
#[derive(Clone, Copy, Debug)]
pub struct OJet<S: Simd, const N: usize> {
    /// the coefficients of the orders 0, ..., N - 1
    pub c: [OV<S>; N],
}

impl<S: Simd, const N: usize> OJet<S, N> {
    /// the series with the given coefficients
    #[inline(always)]
    pub fn from_coeffs(c: [OV<S>; N]) -> Self {
        const { assert!(N >= 1, "a jet has at least its value") }
        OJet { c }
    }
    /// the series variable with lane j's value c\[j\]: coefficient 0 the values, coefficient 1 one
    pub fn var_lanes(c: &[OD; 8]) -> Self {
        let mut j = Self::from_coeffs([OV::zero(); N]);
        j.c[0] = OV::from_lanes(c);
        if N > 1 {
            j.c[1] = OV::splat(OD::ONE);
        }
        j
    }
    /// the Cauchy product's coefficient k of x and y, orders 0..=k through the dot accumulator (feature `mutate`:
    /// `crate::dual::mutate::OJET_CONV` drops the term x_k y_0)
    #[inline(always)]
    fn conv(x: &[OV<S>; N], y: &[OV<S>; N], k: usize) -> ODotAcc<S> {
        let mut a = ODotAcc::zero();
        let last = if k > 0 && mutate::on(mutate::OJET_CONV) {
            k - 1
        } else {
            k
        };
        for i in 0..=last {
            a.add_prod_mut(&x[i], &y[k - i]);
        }
        a
    }
}

impl<S: Simd, const N: usize> Add for OJet<S, N> {
    type Output = Self;
    /// coefficient by coefficient
    #[inline(always)]
    fn add(self, o: Self) -> Self {
        let mut c = self.c;
        for k in 0..N {
            c[k] = self.c[k] + o.c[k];
        }
        OJet { c }
    }
}
impl<S: Simd, const N: usize> Sub for OJet<S, N> {
    type Output = Self;
    /// coefficient by coefficient
    #[inline(always)]
    fn sub(self, o: Self) -> Self {
        let mut c = self.c;
        for k in 0..N {
            c[k] = self.c[k] - o.c[k];
        }
        OJet { c }
    }
}
impl<S: Simd, const N: usize> Neg for OJet<S, N> {
    type Output = Self;
    /// every coefficient negated
    #[inline(always)]
    fn neg(self) -> Self {
        let mut v = self.c;
        for x in v.iter_mut() {
            *x = -*x;
        }
        OJet { c: v }
    }
}
impl<S: Simd, const N: usize> Mul for OJet<S, N> {
    type Output = Self;
    /// the Cauchy product truncated at order N - 1
    #[inline(always)]
    fn mul(self, o: Self) -> Self {
        let mut c = self.c;
        for k in 0..N {
            c[k] = Self::conv(&self.c, &o.c, k).finish();
        }
        OJet { c }
    }
}
impl<S: Simd, const N: usize> Div for OJet<S, N> {
    type Output = Self;
    /// q = x / y by q_k = (x_k − Σ_{i=1..k} y_i q_{k−i}) / y_0
    #[inline(always)]
    fn div(self, o: Self) -> Self {
        // the 9N quotients by o.c[0].c[0] share its divisor (on AVX-512 its reciprocal)
        let r = o.c[0].c[0].divisor();
        let mut q = self.c;
        q[0] = self.c[0].div_by(o.c[0], r);
        for k in 1..N {
            let mut a = ODotAcc::zero();
            for i in 1..=k {
                a.add_prod_mut(&o.c[i], &q[k - i]);
            }
            q[k] = (self.c[k] - a.finish()).div_by(o.c[0], r);
        }
        OJet { c: q }
    }
}

impl<S: Simd, const N: usize> Lane for OJet<S, N> {
    type S = S;
    type Acc = [ODotAcc<S>; N];
    type P = OSeries<N>;
    const TANGENT: bool = true;
    const VAL_OD: bool = true;
    const NJ: usize = N;
    /// the Cauchy product with the scalar series, coefficient k from the orders 0..=k through the dot accumulator
    #[inline(always)]
    fn mulp(self, p: OSeries<N>) -> Self {
        let mut c = self.c;
        for k in 0..N {
            let mut a = ODotAcc::zero();
            for i in 0..=k {
                a.add_prod_mut(&self.c[i], &OV::splat(p.c[k - i]));
            }
            c[k] = a.finish();
        }
        OJet { c }
    }
    /// plus the scalar series, coefficient by coefficient
    #[inline(always)]
    fn addp(self, p: OSeries<N>) -> Self {
        let mut c = self.c;
        for k in 0..N {
            c[k] = self.c[k] + OV::splat(p.c[k]);
        }
        OJet { c }
    }
    /// coefficient k rounded to double-double, zero past the truncation
    #[inline(always)]
    fn coef(self, k: usize) -> DV<S> {
        self.coef_od(k).to_dv()
    }
    /// set coefficient k from double-double, exactly
    #[inline(always)]
    fn set_coef(&mut self, k: usize, c: DV<S>) {
        self.c[k] = OV::from_dv(c);
    }
    /// coefficient k rounded to quad-double, zero past the truncation
    #[inline(always)]
    fn coef_qd(self, k: usize) -> QV<S> {
        self.coef_od(k).to_qv()
    }
    /// set coefficient k from quad-double, exactly
    #[inline(always)]
    fn set_coef_qd(&mut self, k: usize, c: QV<S>) {
        self.c[k] = OV::from_qv(c);
    }
    /// coefficient k, zero past the truncation
    #[inline(always)]
    fn coef_od(self, k: usize) -> OV<S> {
        if k < N {
            self.c[k]
        } else {
            OV::zero()
        }
    }
    /// set coefficient k
    #[inline(always)]
    fn set_coef_od(&mut self, k: usize, c: OV<S>) {
        self.c[k] = c;
    }
    /// the zero series
    #[inline(always)]
    fn zero() -> Self {
        Self::from_coeffs([OV::zero(); N])
    }
    /// the constant series c (order 0), exactly
    #[inline(always)]
    fn cst(c: DV<S>) -> Self {
        let mut j = Self::zero();
        j.c[0] = OV::from_dv(c);
        j
    }
    /// the series variable itself, c + h
    #[inline(always)]
    fn var(c: DD) -> Self {
        let mut j = Self::splat(c);
        if N > 1 {
            j.c[1] = OV::splat(OD::ONE);
        }
        j
    }
    /// every coefficient times the constant lane vector c
    #[inline(always)]
    fn mulc(self, c: DV<S>) -> Self {
        let c = OV::from_dv(c);
        let mut v = self.c;
        for x in v.iter_mut() {
            *x = *x * c;
        }
        OJet { c: v }
    }
    /// every coefficient times an exact f64
    #[inline(always)]
    fn mulf(self, s: f64) -> Self {
        let mut v = self.c;
        for x in v.iter_mut() {
            *x = x.mul_f(s);
        }
        OJet { c: v }
    }
    /// every coefficient times a power of two, exactly
    #[inline(always)]
    fn mul_pwr2(self, s: f64) -> Self {
        let mut v = self.c;
        for x in v.iter_mut() {
            *x = x.mul_pwr2(s);
        }
        OJet { c: v }
    }
    /// plus the constant c at order 0
    #[inline(always)]
    fn addc(self, c: DV<S>) -> Self {
        let mut j = self;
        j.c[0] = self.c[0] + OV::from_dv(c);
        j
    }
    /// every coefficient's 8 lanes set to its lane j
    #[inline(always)]
    fn bcast(self, j: usize) -> Self {
        let mut v = self.c;
        for x in v.iter_mut() {
            *x = x.bcast(j);
        }
        OJet { c: v }
    }
    /// the value rounded to double-double
    #[inline(always)]
    fn val(self) -> DV<S> {
        self.c[0].to_dv()
    }
    /// coefficient 1, rounded to double-double
    #[inline(always)]
    fn tan(self) -> DV<S> {
        self.coef(1)
    }
    /// value v, coefficient 1 t, the others zero
    #[inline(always)]
    fn from_vt(v: DV<S>, t: DV<S>) -> Self {
        let mut j = Self::cst(v);
        if N > 1 {
            j.c[1] = OV::from_dv(t);
        }
        j
    }
    /// the empty sum, one accumulator per order
    #[inline(always)]
    fn acc0() -> Self::Acc {
        [ODotAcc::zero(); N]
    }
    /// a + x y, the Cauchy product's terms of order k added into accumulator k
    #[inline(always)]
    fn acc(a: Self::Acc, x: Self, y: Self) -> Self::Acc {
        let mut a = a;
        for k in 0..N {
            for i in 0..=k {
                a[k].add_prod_mut(&x.c[i], &y.c[k - i]);
            }
        }
        a
    }
    /// `acc` in place: the same products in the same order (`ODotAcc::add_prod_mut`), without moving the N
    /// accumulators or the operands
    #[inline(always)]
    fn acc_mut(a: &mut Self::Acc, x: &Self, y: &Self) {
        for k in 0..N {
            for i in 0..=k {
                a[k].add_prod_mut(&x.c[i], &y.c[k - i]);
            }
        }
    }
    /// a + x c, c a constant lane vector
    #[inline(always)]
    fn accc(a: Self::Acc, x: Self, c: DV<S>) -> Self::Acc {
        let c = OV::from_dv(c);
        let mut a = a;
        for k in 0..N {
            a[k].add_prod_mut(&x.c[k], &c);
        }
        a
    }
    /// a + x
    #[inline(always)]
    fn acc1(a: Self::Acc, x: Self) -> Self::Acc {
        let mut a = a;
        for k in 0..N {
            a[k] = a[k].add(x.c[k]);
        }
        a
    }
    /// the sums, order by order, in a plain loop. Through `array::map` AVX2 and AVX-512 keep the
    /// closure out of line, without their target features (`crate::simd::Kernel`)
    #[inline(always)]
    fn fin(a: Self::Acc) -> Self {
        let mut c = [OV::zero(); N];
        for k in 0..N {
            c[k] = a[k].finish();
        }
        OJet { c }
    }
}
