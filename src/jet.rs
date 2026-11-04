//! `Jet<N>`: a truncated power series in one variable h, N double-double lane vectors c\[0\], …, c\[N − 1\] for the
//! orders 0, …, N − 1 (c\[0\] is the value). Products are Cauchy products truncated at order N − 1 and quotients
//! the series-reciprocal recurrence, so a computation written over [`Lane`] evaluated on jets gives its own Taylor
//! coefficients in h. With a parameter entered as [`Lane::var`] (the jet c + h) the coefficients are those of the
//! computation in that parameter: the right-hand sides of a high-order Taylor continuation of a branch (the
//! asymptotic numerical method, Cochelin, Int. J. Numer. Methods Eng. 37 (1994) 1187, doi:10.1002/nme.1620370706).
//! `Jet<2>` is a dual number (`Du`) with the tangent as c\[1\].
#![allow(clippy::needless_range_loop)]
use crate::dd::DD;
use crate::dual::{Lane, Param};
use crate::dv::{DotAcc, DV};
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
        Jet { c: self.c.map(|x| -x) }
    }
}
impl<S: Simd, const N: usize> Mul for Jet<S, N> {
    type Output = Self;
    #[inline(always)]
    fn mul(self, o: Self) -> Self {
        let mut c = self.c;
        for k in 0..N {
            c[k] = Self::conv(&self.c, &o.c, k).finish();
        }
        Jet { c }
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
        Jet {
            c: self.c.map(|x| x * c),
        }
    }
    #[inline(always)]
    fn mulf(self, s: f64) -> Self {
        Jet {
            c: self.c.map(|x| x.mul_f(s)),
        }
    }
    #[inline(always)]
    fn mul_pwr2(self, s: f64) -> Self {
        Jet {
            c: self.c.map(|x| x.mul_pwr2(s)),
        }
    }
    #[inline(always)]
    fn addc(self, c: DV<S>) -> Self {
        let mut j = self;
        j.c[0] = self.c[0] + c;
        j
    }
    #[inline(always)]
    fn bcast(self, j: usize) -> Self {
        Jet {
            c: self.c.map(|x| x.bcast(j)),
        }
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
    #[inline(always)]
    fn fin(a: Self::Acc) -> Self {
        Jet {
            c: a.map(|x| x.finish()),
        }
    }
}
