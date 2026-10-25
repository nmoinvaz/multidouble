//! Fields: N = 8 B values of a lane type as B lane vectors (`Fl<T, B>`; a function on a grid of 8 B points, or 8 B
//! independent problems), with the power-series arithmetic that series methods for ODEs need on them: Cauchy products
//! of coefficient sequences (`cs`, `cs_range`, `cs_w`), Horner evaluation (`horner`), and a constant double-double
//! matrix applied to a field (`DMat`, for instance a spectral derivative). Every operation is the lane type's, so code
//! written over `Fl<T, B>` runs with values, dual numbers or quad-double lanes alike (`dual::Lane`).
//!
//! The products accumulate with the lane type's dot accumulator (`Lane::acc`), in the order of the index; for the f64
//! lanes (`VAL_F64` or `TAN_F64`) the B lane vectors' accumulations are interleaved, since a single f64 chain is
//! latency-bound, and each still sums its terms in index order. A matrix product is `MatLane::dmat_apply`: the
//! double-double columns through the accumulator by default, the columns' f64 copy for the f64 lanes.
use crate::dd::DD;
use crate::dual::{Counted, Dtn, Du, Fu, Fun, Lane, F8};
use crate::dv::{DotAcc, DV};
use crate::linalg::DDLu;
use crate::qv::QV;
use crate::simd::Simd;
use crate::v8::V8;
use std::ops::{Add, Div, Mul, Neg, Sub};

/// 8 B values of the lane type T as B lane vectors: value j is lane j % 8 of vector j / 8.
#[derive(Clone, Copy, Debug)]
pub struct Fl<T: Lane, const B: usize>(pub [T; B]);

/// The lane type's double-double vector (constants and values of `Fl<T, B>` come as these)
type Dv<T> = DV<<T as Lane>::S>;

macro_rules! fl_binop {
    ($tr:ident, $f:ident, $op:tt) => {
        impl<T: Lane, const B: usize> $tr for Fl<T, B> {
            type Output = Fl<T, B>;
            #[inline(always)]
            fn $f(self, o: Fl<T, B>) -> Fl<T, B> {
                let mut r = self.0;
                for b in 0..B {
                    r[b] = self.0[b] $op o.0[b];
                }
                Fl(r)
            }
        }
    };
}
fl_binop!(Add, add, +);
fl_binop!(Sub, sub, -);
fl_binop!(Mul, mul, *);
fl_binop!(Div, div, /);

impl<T: Lane, const B: usize> Neg for Fl<T, B> {
    type Output = Fl<T, B>;
    #[inline(always)]
    fn neg(self) -> Fl<T, B> {
        let mut r = self.0;
        for b in 0..B {
            r[b] = -self.0[b];
        }
        Fl(r)
    }
}

impl<T: Lane, const B: usize> Fl<T, B> {
    #[inline(always)]
    pub fn zero() -> Self {
        Fl([T::zero(); B])
    }
    #[inline(always)]
    pub fn splat(x: DD) -> Self {
        Fl([T::splat(x); B])
    }
    /// a constant field (zero tangents)
    #[inline(always)]
    pub fn cst(c: &Fl<Dv<T>, B>) -> Self {
        let mut r = [T::zero(); B];
        for b in 0..B {
            r[b] = T::cst(c.0[b]);
        }
        Fl(r)
    }
    #[inline(always)]
    pub fn muls(self, s: DD) -> Self {
        let sv = DV::splat(s);
        let mut r = self.0;
        for b in 0..B {
            r[b] = self.0[b].mulc(sv);
        }
        Fl(r)
    }
    #[inline(always)]
    pub fn mulf(self, s: f64) -> Self {
        let mut r = self.0;
        for b in 0..B {
            r[b] = self.0[b].mulf(s);
        }
        Fl(r)
    }
    /// times a power of two, every part exact (`Lane::mul_pwr2`): bitwise `mulf(s)` for such s
    #[inline(always)]
    pub fn mul_pwr2(self, s: f64) -> Self {
        let mut r = self.0;
        for b in 0..B {
            r[b] = self.0[b].mul_pwr2(s);
        }
        Fl(r)
    }
    /// times a lane-constant scalar of the lane type (e.g. a frequency that carries a tangent)
    #[inline(always)]
    pub fn mul_t(self, s: T) -> Self {
        let mut r = self.0;
        for b in 0..B {
            r[b] = self.0[b] * s;
        }
        Fl(r)
    }
    #[inline(always)]
    pub fn adds(self, s: DD) -> Self {
        let sv = DV::splat(s);
        let mut r = self.0;
        for b in 0..B {
            r[b] = self.0[b].addc(sv);
        }
        Fl(r)
    }
    pub fn val(&self) -> Fl<Dv<T>, B> {
        let mut r = [DV::zero(); B];
        for b in 0..B {
            r[b] = self.0[b].val();
        }
        Fl(r)
    }
    pub fn tan(&self) -> Fl<Dv<T>, B> {
        let mut r = [DV::zero(); B];
        for b in 0..B {
            r[b] = self.0[b].tan();
        }
        Fl(r)
    }
    pub fn from_vt(v: &Fl<Dv<T>, B>, t: &Fl<Dv<T>, B>) -> Self {
        let mut r = [T::zero(); B];
        for b in 0..B {
            r[b] = T::from_vt(v.0[b], t.0[b]);
        }
        Fl(r)
    }
}

impl<S: Simd, const B: usize> Fl<DV<S>, B> {
    /// from 8 B values (hi, lo)
    pub fn load(hi: &[f64], lo: &[f64]) -> Self {
        let mut r = [DV::zero(); B];
        for b in 0..B {
            r[b] = DV::load(&hi[8 * b..8 * b + 8], &lo[8 * b..8 * b + 8]);
        }
        Fl(r)
    }
    pub fn store(&self, hi: &mut [f64], lo: &mut [f64]) {
        for b in 0..B {
            self.0[b].store(&mut hi[8 * b..8 * b + 8], &mut lo[8 * b..8 * b + 8]);
        }
    }
    pub fn get(&self, j: usize) -> DD {
        self.0[j / 8].lane(j % 8)
    }
    /// max |hi| over the values
    pub fn amax(&self) -> f64 {
        let mut m = 0.0f64;
        for b in 0..B {
            m = m.max(self.0[b].hi.abs().hmax());
        }
        m
    }
}

/// Cauchy product coefficient `sum_{j=0..k} x[j] y[k-j]`
#[inline(always)]
pub fn cs<T: Lane, const B: usize>(x: &[Fl<T, B>], y: &[Fl<T, B>], k: usize) -> Fl<T, B> {
    if T::VAL_F64 || T::TAN_F64 {
        return cs_il(x, y, k, 0, k, |_| 1.0, false);
    }
    let mut out = [T::zero(); B];
    for b in 0..B {
        let mut a = T::acc0();
        for j in 0..=k {
            a = T::acc(a, x[j].0[b], y[k - j].0[b]);
        }
        out[b] = T::fin(a);
    }
    Fl(out)
}

/// `sum_{j=lo..=hi} x[j] y[k-j]`
#[inline(always)]
pub fn cs_range<T: Lane, const B: usize>(x: &[Fl<T, B>], y: &[Fl<T, B>], k: usize, lo: usize, hi: usize) -> Fl<T, B> {
    if T::VAL_F64 || T::TAN_F64 {
        return cs_il(x, y, k, lo, hi, |_| 1.0, false);
    }
    let mut out = [T::zero(); B];
    for b in 0..B {
        let mut a = T::acc0();
        for j in lo..=hi {
            a = T::acc(a, x[j].0[b], y[k - j].0[b]);
        }
        out[b] = T::fin(a);
    }
    Fl(out)
}

/// `sum_{j=lo..=hi} (w(j) x[j]) y[k-j]` with exact f64 weights w(j) (small integers, as in the coefficients of a
/// derivative)
#[inline(always)]
pub fn cs_w<T: Lane, const B: usize>(
    x: &[Fl<T, B>],
    y: &[Fl<T, B>],
    k: usize,
    lo: usize,
    hi: usize,
    w: impl Fn(usize) -> f64,
) -> Fl<T, B> {
    if T::VAL_F64 || T::TAN_F64 {
        return cs_il(x, y, k, lo, hi, w, true);
    }
    let mut out = [T::zero(); B];
    for b in 0..B {
        let mut a = T::acc0();
        for j in lo..=hi {
            a = T::acc(a, x[j].0[b].mulf(w(j)), y[k - j].0[b]);
        }
        out[b] = T::fin(a);
    }
    Fl(out)
}

/// sum_{j=lo..=hi} (w(j) x[j]) y[k-j] (weights only if weighted) with the B lane vectors' accumulations interleaved,
/// for the f64 lanes, whose single accumulation chains are latency-bound; each lane vector still sums its terms in the
/// order j = lo..=hi.
#[inline(always)]
fn cs_il<T: Lane, const B: usize>(
    x: &[Fl<T, B>],
    y: &[Fl<T, B>],
    k: usize,
    lo: usize,
    hi: usize,
    w: impl Fn(usize) -> f64,
    weighted: bool,
) -> Fl<T, B> {
    let mut a = [T::acc0(); B];
    for j in lo..=hi {
        let (xj, yj) = (&x[j].0, &y[k - j].0);
        if weighted {
            let wj = w(j);
            for b in 0..B {
                a[b] = T::acc(a[b], xj[b].mulf(wj), yj[b]);
            }
        } else {
            for b in 0..B {
                a[b] = T::acc(a[b], xj[b], yj[b]);
            }
        }
    }
    Fl(a.map(T::fin))
}

/// Horner evaluation `sum_k s[k] h^k`
#[inline(always)]
pub fn horner<T: Lane, const B: usize>(s: &[Fl<T, B>], h: DD) -> Fl<T, B> {
    let mut out = Fl::<T, B>::zero();
    for k in (0..s.len()).rev() {
        out = out.muls(h) + s[k];
    }
    out
}

/// A constant (8 B) x (8 B) double-double matrix stored by columns (column j as a field over the rows), with a copy
/// of the columns' hi parts for the f64 lanes.
#[derive(Clone)]
pub struct DMat<S: Simd, const B: usize> {
    pub cols: Vec<Fl<DV<S>, B>>,
    /// `cols64[j][b] = cols[j].0[b].hi`
    pub cols64: Vec<[V8<S>; B]>,
}

impl<S: Simd, const B: usize> DMat<S, B> {
    /// from row-major (8 B, 8 B) hi / lo arrays
    pub fn from_rows(hi: &[f64], lo: &[f64]) -> Self {
        let m = 8 * B;
        let mut cols = Vec::with_capacity(m);
        for j in 0..m {
            let ch: Vec<f64> = (0..m).map(|i| hi[i * m + j]).collect();
            let cl: Vec<f64> = (0..m).map(|i| lo[i * m + j]).collect();
            cols.push(Fl::<DV<S>, B>::load(&ch, &cl));
        }
        let cols64 = cols.iter().map(|c| c.0.map(|v| v.hi)).collect();
        DMat { cols, cols64 }
    }

    /// D f in the lane type's precision (`MatLane::dmat_apply`)
    #[inline(always)]
    pub fn apply<T: MatLane<S = S>>(&self, f: &Fl<T, B>) -> Fl<T, B> {
        T::dmat_apply(self, f)
    }

    /// D f with the double-double columns, accumulated by `Lane::accc` (column j's contribution in the order j)
    #[inline(always)]
    pub fn apply_dd<T: Lane<S = S>>(&self, f: &Fl<T, B>) -> Fl<T, B> {
        let mut acc = [T::acc0(); B];
        for jb in 0..B {
            for jl in 0..8 {
                let s = f.0[jb].bcast(jl);
                let col = &self.cols[8 * jb + jl];
                for b in 0..B {
                    acc[b] = T::accc(acc[b], s, col.0[b]);
                }
            }
        }
        let mut out = [T::zero(); B];
        for b in 0..B {
            out[b] = T::fin(acc[b]);
        }
        Fl(out)
    }
}

/// A lane type with the product of a constant matrix: `DMat::apply_dd` by default (the double-double columns through
/// the dot accumulator); the f64 lanes multiply by the columns' f64 copy with fused multiply-adds, `Dtn<N>` its value
/// by the double-double columns and its tangents by the f64 copy.
pub trait MatLane: Lane {
    #[inline(always)]
    fn dmat_apply<const B: usize>(d: &DMat<Self::S, B>, f: &Fl<Self, B>) -> Fl<Self, B> {
        d.apply_dd(f)
    }
}

impl<S: Simd> MatLane for DV<S> {}
impl<S: Simd> MatLane for Du<S> {}
impl<S: Simd> MatLane for QV<S> {}

impl<S: Simd> MatLane for F8<S> {
    #[inline(always)]
    fn dmat_apply<const B: usize>(d: &DMat<S, B>, f: &Fl<Self, B>) -> Fl<Self, B> {
        let mut acc = [V8::zero(); B];
        for jb in 0..B {
            for jl in 0..8 {
                let s = f.0[jb].0.bcast(jl);
                let col = &d.cols64[8 * jb + jl];
                for b in 0..B {
                    acc[b] = s.fma(col[b], acc[b]);
                }
            }
        }
        Fl(acc.map(F8))
    }
}

impl<S: Simd> MatLane for Fu<S> {
    #[inline(always)]
    fn dmat_apply<const B: usize>(d: &DMat<S, B>, f: &Fl<Self, B>) -> Fl<Self, B> {
        let mut av = [V8::zero(); B];
        let mut ad = [V8::zero(); B];
        for jb in 0..B {
            for jl in 0..8 {
                let sv = f.0[jb].v.bcast(jl);
                let sd = f.0[jb].d.bcast(jl);
                let col = &d.cols64[8 * jb + jl];
                for b in 0..B {
                    av[b] = sv.fma(col[b], av[b]);
                    ad[b] = sd.fma(col[b], ad[b]);
                }
            }
        }
        let mut out = [Fu::zero(); B];
        for b in 0..B {
            out[b] = Fu { v: av[b], d: ad[b] };
        }
        Fl(out)
    }
}

impl<S: Simd, const N: usize> MatLane for Dtn<S, N> {
    #[inline(always)]
    fn dmat_apply<const B: usize>(dm: &DMat<S, B>, f: &Fl<Self, B>) -> Fl<Self, B> {
        let mut av = [DotAcc::zero(); B];
        let mut ad = [[V8::zero(); N]; B];
        for jb in 0..B {
            for jl in 0..8 {
                let sv = f.0[jb].v.bcast(jl);
                let sd = f.0[jb].d.map(|x| x.bcast(jl));
                let col = &dm.cols[8 * jb + jl];
                let col64 = &dm.cols64[8 * jb + jl];
                for b in 0..B {
                    av[b] = av[b].add_prod(sv, col.0[b]);
                    for i in 0..N {
                        ad[b][i] = sd[i].fma(col64[b], ad[b][i]);
                    }
                }
            }
        }
        let mut out = [Self::zero(); B];
        for b in 0..B {
            out[b] = Dtn {
                v: av[b].finish(),
                d: ad[b],
            };
        }
        Fl(out)
    }
}

impl<S: Simd, const N: usize> MatLane for Fun<S, N> {
    #[inline(always)]
    fn dmat_apply<const B: usize>(dm: &DMat<S, B>, f: &Fl<Self, B>) -> Fl<Self, B> {
        let mut av = [V8::zero(); B];
        let mut ad = [[V8::zero(); N]; B];
        for jb in 0..B {
            for jl in 0..8 {
                let sv = f.0[jb].v.bcast(jl);
                let sd = f.0[jb].d.map(|x| x.bcast(jl));
                let col64 = &dm.cols64[8 * jb + jl];
                for b in 0..B {
                    av[b] = sv.fma(col64[b], av[b]);
                    for i in 0..N {
                        ad[b][i] = sd[i].fma(col64[b], ad[b][i]);
                    }
                }
            }
        }
        let mut out = [Self::zero(); B];
        for b in 0..B {
            out[b] = Fun { v: av[b], d: ad[b] };
        }
        Fl(out)
    }
}

/// The wrapped type's product, bitwise; counted as the default product would be (8 B x B `accc` and B `fin`).
impl<L: MatLane> MatLane for Counted<L> {
    #[inline(always)]
    fn dmat_apply<const B: usize>(d: &DMat<Self::S, B>, f: &Fl<Self, B>) -> Fl<Self, B> {
        crate::dual::count_n(crate::dual::op::ACCC, (8 * B * B) as u64);
        crate::dual::count_n(crate::dual::op::FIN, B as u64);
        Fl(L::dmat_apply(d, &Fl(f.0.map(|x| x.0))).0.map(Counted))
    }
}

/// Solves of a `DDLu` of order 8 B for a field: `solve_lanes` in double-double, `solve_lanes_hi` in plain f64 with
/// the hi parts of the factors (`DDLu::solve_hi`; the lo parts out zero). Both panic if the order is not 8 B.
pub trait FieldSolve {
    fn solve_lanes<S: Simd, const B: usize>(&self, f: &Fl<DV<S>, B>) -> Fl<DV<S>, B>;
    fn solve_lanes_hi<S: Simd, const B: usize>(&self, f: &Fl<DV<S>, B>) -> Fl<DV<S>, B>;
}

impl FieldSolve for DDLu {
    fn solve_lanes<S: Simd, const B: usize>(&self, f: &Fl<DV<S>, B>) -> Fl<DV<S>, B> {
        let m = 8 * B;
        assert_eq!(
            self.n, m,
            "FieldSolve: a DDLu of order {} for a field of {m} values",
            self.n
        );
        let mut h = vec![0.0; m];
        let mut l = vec![0.0; m];
        f.store(&mut h, &mut l);
        let mut b: Vec<DD> = (0..m).map(|i| DD { hi: h[i], lo: l[i] }).collect();
        self.solve(&mut b);
        for i in 0..m {
            h[i] = b[i].hi;
            l[i] = b[i].lo;
        }
        Fl::<DV<S>, B>::load(&h, &l)
    }

    fn solve_lanes_hi<S: Simd, const B: usize>(&self, f: &Fl<DV<S>, B>) -> Fl<DV<S>, B> {
        let m = 8 * B;
        assert_eq!(
            self.n, m,
            "FieldSolve: a DDLu of order {} for a field of {m} values",
            self.n
        );
        let mut h = vec![0.0; m];
        let mut l = vec![0.0; m];
        f.store(&mut h, &mut l);
        self.solve_hi(&mut h);
        l.iter_mut().for_each(|v| *v = 0.0);
        Fl::<DV<S>, B>::load(&h, &l)
    }
}
