//! The types and operations of one multi-double precision behind one trait, so that code is written once over
//! quad-double ([`Quad`]) and octo-double ([`Octo`]).
//!
//! The two precisions have the same kinds of types (scalar, 8-lane vector, forward-mode dual, power series, dense LU
//! and sum-of-products accumulator) with methods that differ in name or arity: `QD::new(a, b, c, d)` against
//! `OD::new([..; 8])`, `Fl::load_parts` against `Fl::load_parts_od`, `coef_qd` against `coef_od`, `QDLu::factor` of
//! four parts against `ODLu::factor` of eight. [`Precision`] names each kind once and delegates to those methods, so a
//! generic function gives bitwise the results of the code written for one precision.
//!
//! ```
//! use multidouble::precision::{Octo, Precision, Quad};
//! use multidouble::simd::Native;
//!
//! // the same generic code in both precisions: a sum of products, accumulated with one rounding at the end
//! fn norm2<P: Precision<Native>>(x: &[f64]) -> f64 {
//!     let v: Vec<P::Scalar> = x.iter().map(|&a| P::new(&[a])).collect();
//!     P::to_dd(P::dot(v.iter().map(|&a| (a, a)))).hi
//! }
//! assert_eq!(norm2::<Quad>(&[3.0, 4.0]), 25.0);
//! assert_eq!(norm2::<Octo>(&[3.0, 4.0]), 25.0);
//! ```
use crate::dd::DD;
use crate::dual::{Lane, Ou, Qu};
use crate::field::{Fl, MatLane};
use crate::jet::{OJet, QJet};
use crate::linalg::{ODLu, QDLu};
use crate::od::{OdAcc, OD};
use crate::ov::OV;
use crate::qd::{QdAcc, QD};
use crate::qv::QV;
use crate::simd::Simd;
use std::fmt::Debug;
use std::ops::{Add, Mul, Neg, Sub};

/// One multi-double precision on the backend `S`: its types, and the operations whose names differ between
/// precisions. Every method delegates to the precision's own method and returns its result bit for bit.
pub trait Precision<S: Simd>: Copy + Send + Sync + 'static {
    /// the number of f64 parts of a scalar: 4 for quad-double, 8 for octo-double
    const PARTS: usize;
    /// the scalar: `QD`, `OD`
    type Scalar: Copy
        + Send
        + Sync
        + Debug
        + PartialEq
        + Add<Output = Self::Scalar>
        + Sub<Output = Self::Scalar>
        + Mul<Output = Self::Scalar>
        + Neg<Output = Self::Scalar>;
    /// 8 scalars in lanes: `QV`, `OV`
    type V: MatLane<S = S>;
    /// forward-mode dual, value and one tangent in this precision: `Qu`, `Ou`
    type U: MatLane<S = S>;
    /// truncated power series with N coefficients in this precision: `QJet<N>`, `OJet<N>`
    type J<const N: usize>: MatLane<S = S>;
    /// dense LU with partial pivoting in this precision: `QDLu`, `ODLu`
    type Lu: Send + Sync;

    /// zero and one
    const ZERO: Self::Scalar;
    const ONE: Self::Scalar;

    /// a scalar from up to PARTS parts, the missing ones zero, renormalized (`QD::new`, `OD::new`)
    fn new(p: &[f64]) -> Self::Scalar;
    /// a scalar from exactly PARTS parts as they are, not renormalized (the struct literal `QD { x }`, `OD { x }`)
    fn from_raw(p: &[f64]) -> Self::Scalar;
    /// part q of a scalar
    fn part(x: Self::Scalar, q: usize) -> f64;
    /// from double-double, exactly
    fn from_dd(d: DD) -> Self::Scalar;
    /// rounded to double-double
    fn to_dd(x: Self::Scalar) -> DD;
    /// sum of the products a b over the pairs, in this precision's accumulator (`QdAcc`, `OdAcc`): `add_prod` per
    /// pair, `finish` at the end
    fn dot(pairs: impl Iterator<Item = (Self::Scalar, Self::Scalar)>) -> Self::Scalar;

    /// the scalar in every lane (`QV::splat`, `OV::splat`)
    fn splat(x: Self::Scalar) -> Self::V;
    /// a dual from its value and tangent lanes
    fn dual(v: Self::V, d: Self::V) -> Self::U;
    /// coefficient k of a lane in this precision (`Lane::coef_qd`, `Lane::coef_od`)
    fn coef<L: Lane<S = S>>(l: L, k: usize) -> Self::V;
    /// set coefficient k of a lane from this precision (`Lane::set_coef_qd`, `Lane::set_coef_od`)
    fn set_coef<L: Lane<S = S>>(l: &mut L, k: usize, c: Self::V);

    /// a field of 8 B values from PARTS part arrays of at least 8 B values each (`Fl::load_parts`,
    /// `Fl::load_parts_od`)
    fn load_field<const B: usize>(parts: &[&[f64]]) -> Fl<Self::V, B>;
    /// value j of a field (`Fl::get`)
    fn field_get<const B: usize>(f: &Fl<Self::V, B>, j: usize) -> Self::Scalar;
    /// coefficient k of a field in this precision (`Fl::coef_qd`, `Fl::coef_od`)
    fn field_coef<L: Lane<S = S>, const B: usize>(f: &Fl<L, B>, k: usize) -> Fl<Self::V, B>;
    /// set coefficient k of a field from this precision (`Fl::set_coef_qd`, `Fl::set_coef_od`)
    fn field_set_coef<L: Lane<S = S>, const B: usize>(f: &mut Fl<L, B>, k: usize, c: &Fl<Self::V, B>);
    /// a dual field from its values and tangents, exactly (`Fl::from_vt_qd`, `Fl::from_vt_od`)
    fn field_dual<const B: usize>(v: &Fl<Self::V, B>, t: &Fl<Self::V, B>) -> Fl<Self::U, B>;

    /// factor the n x n matrix of PARTS column-major part arrays with leading dimension ld (`QDLu::factor`,
    /// `ODLu::factor`)
    fn lu_factor(n: usize, ld: usize, c: Vec<Vec<f64>>, par: bool) -> Result<Self::Lu, String>;
    /// solve in place with the factored matrix (`QDLu::solve`, `ODLu::solve`)
    fn lu_solve(lu: &Self::Lu, b: &mut [Self::Scalar]);
}

/// Quad-double: `QD`, `QV`, `Qu`, `QJet<N>`, `QDLu`, `QdAcc`
#[derive(Clone, Copy, Debug)]
pub struct Quad;

/// Octo-double: `OD`, `OV`, `Ou`, `OJet<N>`, `ODLu`, `OdAcc`
#[derive(Clone, Copy, Debug)]
pub struct Octo;

fn parts_of<const P: usize>(p: &[f64], what: &str) -> [f64; P] {
    assert!(p.len() <= P, "{what}: at most {P} parts, not {}", p.len());
    std::array::from_fn(|q| if q < p.len() { p[q] } else { 0.0 })
}

impl<S: Simd> Precision<S> for Quad {
    const PARTS: usize = 4;
    type Scalar = QD;
    type V = QV<S>;
    type U = Qu<S>;
    type J<const N: usize> = QJet<S, N>;
    type Lu = QDLu;
    const ZERO: QD = QD::ZERO;
    const ONE: QD = QD::ONE;

    #[inline]
    fn new(p: &[f64]) -> QD {
        let x: [f64; 4] = parts_of(p, "Quad::new");
        QD::new(x[0], x[1], x[2], x[3])
    }
    #[inline]
    fn from_raw(p: &[f64]) -> QD {
        assert_eq!(p.len(), 4, "Quad::from_raw: 4 parts");
        QD {
            x: [p[0], p[1], p[2], p[3]],
        }
    }
    #[inline]
    fn part(x: QD, q: usize) -> f64 {
        x.x[q]
    }
    #[inline]
    fn from_dd(d: DD) -> QD {
        QD::from_dd(d)
    }
    #[inline]
    fn to_dd(x: QD) -> DD {
        x.to_dd()
    }
    fn dot(pairs: impl Iterator<Item = (QD, QD)>) -> QD {
        let mut acc = QdAcc::zero();
        for (a, b) in pairs {
            acc = acc.add_prod(a, b);
        }
        acc.finish()
    }
    #[inline]
    fn splat(x: QD) -> QV<S> {
        QV::splat(x)
    }
    #[inline]
    fn dual(v: QV<S>, d: QV<S>) -> Qu<S> {
        Qu { v, d }
    }
    #[inline]
    fn coef<L: Lane<S = S>>(l: L, k: usize) -> QV<S> {
        l.coef_qd(k)
    }
    #[inline]
    fn set_coef<L: Lane<S = S>>(l: &mut L, k: usize, c: QV<S>) {
        l.set_coef_qd(k, c)
    }
    fn load_field<const B: usize>(parts: &[&[f64]]) -> Fl<QV<S>, B> {
        assert_eq!(parts.len(), 4, "Quad::load_field: 4 parts");
        Fl::load_parts(parts[0], parts[1], parts[2], parts[3])
    }
    #[inline]
    fn field_get<const B: usize>(f: &Fl<QV<S>, B>, j: usize) -> QD {
        f.get(j)
    }
    #[inline]
    fn field_coef<L: Lane<S = S>, const B: usize>(f: &Fl<L, B>, k: usize) -> Fl<QV<S>, B> {
        f.coef_qd(k)
    }
    #[inline]
    fn field_set_coef<L: Lane<S = S>, const B: usize>(f: &mut Fl<L, B>, k: usize, c: &Fl<QV<S>, B>) {
        f.set_coef_qd(k, c)
    }
    #[inline]
    fn field_dual<const B: usize>(v: &Fl<QV<S>, B>, t: &Fl<QV<S>, B>) -> Fl<Qu<S>, B> {
        Fl::<Qu<S>, B>::from_vt_qd(v, t)
    }
    fn lu_factor(n: usize, ld: usize, c: Vec<Vec<f64>>, par: bool) -> Result<QDLu, String> {
        let c: [Vec<f64>; 4] = c
            .try_into()
            .map_err(|c: Vec<Vec<f64>>| format!("Quad::lu_factor: 4 parts, not {}", c.len()))?;
        QDLu::factor(n, ld, c, par)
    }
    #[inline]
    fn lu_solve(lu: &QDLu, b: &mut [QD]) {
        lu.solve(b)
    }
}

impl<S: Simd> Precision<S> for Octo {
    const PARTS: usize = 8;
    type Scalar = OD;
    type V = OV<S>;
    type U = Ou<S>;
    type J<const N: usize> = OJet<S, N>;
    type Lu = ODLu;
    const ZERO: OD = OD::ZERO;
    const ONE: OD = OD::ONE;

    #[inline]
    fn new(p: &[f64]) -> OD {
        OD::new(parts_of(p, "Octo::new"))
    }
    #[inline]
    fn from_raw(p: &[f64]) -> OD {
        assert_eq!(p.len(), 8, "Octo::from_raw: 8 parts");
        OD {
            x: std::array::from_fn(|q| p[q]),
        }
    }
    #[inline]
    fn part(x: OD, q: usize) -> f64 {
        x.x[q]
    }
    #[inline]
    fn from_dd(d: DD) -> OD {
        OD::from_dd(d)
    }
    #[inline]
    fn to_dd(x: OD) -> DD {
        x.to_dd()
    }
    fn dot(pairs: impl Iterator<Item = (OD, OD)>) -> OD {
        let mut acc = OdAcc::zero();
        for (a, b) in pairs {
            acc = acc.add_prod(a, b);
        }
        acc.finish()
    }
    #[inline]
    fn splat(x: OD) -> OV<S> {
        OV::splat(x)
    }
    #[inline]
    fn dual(v: OV<S>, d: OV<S>) -> Ou<S> {
        Ou { v, d }
    }
    #[inline]
    fn coef<L: Lane<S = S>>(l: L, k: usize) -> OV<S> {
        l.coef_od(k)
    }
    #[inline]
    fn set_coef<L: Lane<S = S>>(l: &mut L, k: usize, c: OV<S>) {
        l.set_coef_od(k, c)
    }
    fn load_field<const B: usize>(parts: &[&[f64]]) -> Fl<OV<S>, B> {
        assert_eq!(parts.len(), 8, "Octo::load_field: 8 parts");
        Fl::load_parts_od(std::array::from_fn(|q| parts[q]))
    }
    #[inline]
    fn field_get<const B: usize>(f: &Fl<OV<S>, B>, j: usize) -> OD {
        f.get(j)
    }
    #[inline]
    fn field_coef<L: Lane<S = S>, const B: usize>(f: &Fl<L, B>, k: usize) -> Fl<OV<S>, B> {
        f.coef_od(k)
    }
    #[inline]
    fn field_set_coef<L: Lane<S = S>, const B: usize>(f: &mut Fl<L, B>, k: usize, c: &Fl<OV<S>, B>) {
        f.set_coef_od(k, c)
    }
    #[inline]
    fn field_dual<const B: usize>(v: &Fl<OV<S>, B>, t: &Fl<OV<S>, B>) -> Fl<Ou<S>, B> {
        Fl::<Ou<S>, B>::from_vt_od(v, t)
    }
    fn lu_factor(n: usize, ld: usize, c: Vec<Vec<f64>>, par: bool) -> Result<ODLu, String> {
        let c: [Vec<f64>; 8] = c
            .try_into()
            .map_err(|c: Vec<Vec<f64>>| format!("Octo::lu_factor: 8 parts, not {}", c.len()))?;
        ODLu::factor(n, ld, c, par)
    }
    #[inline]
    fn lu_solve(lu: &ODLu, b: &mut [OD]) {
        lu.solve(b)
    }
}

#[cfg(test)]
mod tests {
    //! Each method of `Quad` and `Octo` against the precision's own method on the same inputs, bit for bit. The
    //! control `mutated` swaps two parts on input and must differ.
    use super::*;
    use crate::simd::Native;

    type N = Native;

    fn qd_parts(seed: u64) -> [f64; 4] {
        let a = 1.0 + (seed as f64) / 7.0;
        let x = QD::from_dd(DD::from_f64(a)) / QD::from_dd(DD::from_f64(3.0 + seed as f64));
        x.x
    }

    fn od_parts(seed: u64) -> [f64; 8] {
        let a = 1.0 + (seed as f64) / 7.0;
        let x = OD::from_dd(DD::from_f64(a)) / OD::from_dd(DD::from_f64(3.0 + seed as f64));
        x.x
    }

    #[test]
    fn precision_scalars_match_their_types() {
        for s in 0..20 {
            let p = qd_parts(s);
            assert_eq!(<Quad as Precision<N>>::new(&p), QD::new(p[0], p[1], p[2], p[3]));
            assert_eq!(<Quad as Precision<N>>::new(&p[..2]), QD::new(p[0], p[1], 0.0, 0.0));
            assert_eq!(<Quad as Precision<N>>::from_raw(&p).x, p);
            let o = od_parts(s);
            assert_eq!(<Octo as Precision<N>>::new(&o), OD::new(o));
            let mut half = o;
            half[4..].fill(0.0);
            assert_eq!(<Octo as Precision<N>>::new(&o[..4]), OD::new(half));
            assert_eq!(<Octo as Precision<N>>::from_raw(&o).x, o);
            for q in 0..8 {
                assert_eq!(<Octo as Precision<N>>::part(OD { x: o }, q), o[q]);
            }
        }
    }

    #[test]
    fn precision_dot_matches_accumulators() {
        let xs: Vec<QD> = (0..13).map(|s| QD { x: qd_parts(s) }).collect();
        let mut acc = QdAcc::zero();
        for w in xs.windows(2) {
            acc = acc.add_prod(w[0], w[1]);
        }
        assert_eq!(
            <Quad as Precision<N>>::dot(xs.windows(2).map(|w| (w[0], w[1]))),
            acc.finish()
        );
        let os: Vec<OD> = (0..13).map(|s| OD { x: od_parts(s) }).collect();
        let mut acc = OdAcc::zero();
        for w in os.windows(2) {
            acc = acc.add_prod(w[0], w[1]);
        }
        assert_eq!(
            <Octo as Precision<N>>::dot(os.windows(2).map(|w| (w[0], w[1]))),
            acc.finish()
        );
    }

    /// the field loads, reads, coefficient access and dual seeds against the precision's own methods
    #[test]
    fn precision_fields_match_their_types() {
        const B: usize = 2;
        let cols: Vec<Vec<f64>> = (0..8)
            .map(|q| (0..8 * B).map(|i| od_parts(i as u64)[q]).collect())
            .collect();
        let refs: Vec<&[f64]> = cols.iter().map(|c| c.as_slice()).collect();
        let fq = <Quad as Precision<N>>::load_field::<B>(&refs[..4]);
        let gq = Fl::<QV<N>, B>::load_parts(refs[0], refs[1], refs[2], refs[3]);
        let fo = <Octo as Precision<N>>::load_field::<B>(&refs);
        let go = Fl::<OV<N>, B>::load_parts_od(std::array::from_fn(|q| refs[q]));
        let unit_q = Fl::<QV<N>, B>::unit(5);
        let unit_o = Fl::<OV<N>, B>::unit(5);
        let dq = <Quad as Precision<N>>::field_dual(&fq, &unit_q);
        let doo = <Octo as Precision<N>>::field_dual(&fo, &unit_o);
        for j in 0..8 * B {
            assert_eq!(<Quad as Precision<N>>::field_get(&fq, j), gq.get(j));
            assert_eq!(<Octo as Precision<N>>::field_get(&fo, j), go.get(j));
            assert_eq!(
                <Quad as Precision<N>>::field_coef(&dq, 1).get(j),
                Fl::<Qu<N>, B>::from_vt_qd(&gq, &unit_q).coef_qd(1).get(j)
            );
            assert_eq!(<Octo as Precision<N>>::field_coef(&doo, 0).get(j), go.get(j));
            assert_eq!(
                <Octo as Precision<N>>::field_coef(&doo, 1).get(j),
                if j == 5 { OD::ONE } else { OD::ZERO }
            );
        }
        let mut jq = Fl::<QJet<N, 4>, B>::zero();
        <Quad as Precision<N>>::field_set_coef(&mut jq, 2, &gq);
        let mut jo = Fl::<OJet<N, 4>, B>::zero();
        <Octo as Precision<N>>::field_set_coef(&mut jo, 2, &go);
        for j in 0..8 * B {
            assert_eq!(<Quad as Precision<N>>::field_coef(&jq, 2).get(j), gq.get(j));
            assert_eq!(<Octo as Precision<N>>::field_coef(&jo, 2).get(j), go.get(j));
        }
    }

    #[test]
    fn precision_lu_matches_its_type() {
        let n = 5;
        let ld = 8; // a multiple of 8, as the LUs need
        let mat = |p: usize, s: u64| -> Vec<Vec<f64>> {
            (0..p)
                .map(|q| {
                    (0..ld * n)
                        .map(|i| {
                            if q == 0 {
                                ((i * 7 + 3) % 11) as f64 - 5.0 + if i % ld == i / ld { 9.0 } else { 0.0 }
                            } else {
                                od_parts(s + i as u64)[q] * 1e-20
                            }
                        })
                        .collect()
                })
                .collect()
        };
        let cq = mat(4, 1);
        let mut bq: Vec<QD> = (0..n).map(|i| QD { x: qd_parts(i as u64) }).collect();
        let mut bq2 = bq.clone();
        let lu = <Quad as Precision<N>>::lu_factor(n, ld, cq.clone(), false).unwrap();
        <Quad as Precision<N>>::lu_solve(&lu, &mut bq);
        QDLu::factor(n, ld, cq.try_into().unwrap(), false)
            .unwrap()
            .solve(&mut bq2);
        assert_eq!(bq, bq2);
        let co = mat(8, 2);
        let mut bo: Vec<OD> = (0..n).map(|i| OD { x: od_parts(i as u64) }).collect();
        let mut bo2 = bo.clone();
        let lu = <Octo as Precision<N>>::lu_factor(n, ld, co.clone(), false).unwrap();
        <Octo as Precision<N>>::lu_solve(&lu, &mut bo);
        ODLu::factor(n, ld, co.try_into().unwrap(), false)
            .unwrap()
            .solve(&mut bo2);
        assert_eq!(bo, bo2);
        assert!(<Quad as Precision<N>>::lu_factor(n, ld, mat(8, 1), false).is_err());
    }

    /// the control: the same comparison with two parts swapped on input must fail
    #[test]
    fn precision_mutated_differs() {
        let p = qd_parts(3);
        let swapped = [p[1], p[0], p[2], p[3]];
        assert_ne!(<Quad as Precision<N>>::from_raw(&swapped), QD { x: p });
        let o = od_parts(3);
        let mut so = o;
        so.swap(0, 1);
        assert_ne!(<Octo as Precision<N>>::from_raw(&so), OD { x: o });
    }
}
