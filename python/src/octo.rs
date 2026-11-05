//! The octo-double LU solve: `od_solve` and the class `ODLu`, with A and b as eight float64 part arrays each; and
//! octo-double arrays as eight part arrays, plus a double-double one (`od_add_dd`) or a multiple of another
//! (`od_axpy`).
use multidouble::dd::DD;
use multidouble::dv::DV;
use multidouble::linalg::{ld_for, ODLu};
use multidouble::od::OD;
use multidouble::ov::{axpy_parts, OV};
use multidouble::simd::{self, Kernel, Simd};
use multidouble::v8::V8;
use numpy::ndarray::{ArrayD, Dimension};
use numpy::{
    IntoPyArray, IxDyn, PyArray1, PyArrayDyn, PyReadonlyArray, PyReadonlyArray1, PyReadonlyArray2, PyReadonlyArrayDyn,
    PyUntypedArrayMethods,
};
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;

type Part<'py> = Bound<'py, PyArrayDyn<f64>>;
type Parts8<'py> = (
    Part<'py>,
    Part<'py>,
    Part<'py>,
    Part<'py>,
    Part<'py>,
    Part<'py>,
    Part<'py>,
    Part<'py>,
);

/// an array's elements in row-major order; a Fortran-ordered array, which `as_slice` would give in column-major
/// order, is refused
fn rows<'a, D: Dimension>(a: &'a PyReadonlyArray<'_, f64, D>, name: &str) -> PyResult<&'a [f64]> {
    let err = || PyValueError::new_err(format!("{name} must be C-contiguous"));
    if !a.is_c_contiguous() {
        return Err(err());
    }
    a.as_slice().map_err(|_| err())
}

/// A in the layout of `ODLu::factor`: eight (n, n) row-major part arrays, each entry renormalized (`OD::new`) and
/// stored column-major with leading dimension `ld_for(n)`, the padding rows zero. Returns (n, ld, parts). Raises
/// ValueError for unequal or non-square shapes and for an entry that is not finite.
fn od_matrix(a: &[PyReadonlyArray2<'_, f64>; 8]) -> PyResult<(usize, usize, [Vec<f64>; 8])> {
    let n = a[0].shape()[0];
    if a.iter().any(|p| p.shape() != [n, n]) {
        return Err(PyValueError::new_err("A must be (n, n), the same in all eight parts"));
    }
    let mut s: [&[f64]; 8] = [&[]; 8];
    for (q, p) in a.iter().enumerate() {
        s[q] = rows(p, &format!("a{q}"))?;
    }
    let ld = ld_for(n);
    let mut c: [Vec<f64>; 8] = std::array::from_fn(|_| vec![0.0; ld * n]);
    for i in 0..n {
        for j in 0..n {
            let k = i * n + j;
            let v = OD::new(std::array::from_fn(|q| s[q][k]));
            if !v.x.iter().all(|x| x.is_finite()) {
                return Err(PyValueError::new_err(format!("A has a non-finite entry at ({i}, {j})")));
            }
            for (q, part) in c.iter_mut().enumerate() {
                part[j * ld + i] = v.x[q];
            }
        }
    }
    Ok((n, ld, c))
}

/// b as k columns of n octo-doubles, each entry renormalized (`OD::new`): eight part arrays of shape (n,) (k = 1) or
/// (n, k), row-major. Returns b's shape and the columns. Raises ValueError for another shape, unequal shapes or an
/// entry that is not finite.
fn od_rhs(b: &[PyReadonlyArrayDyn<'_, f64>; 8], n: usize) -> PyResult<(Vec<usize>, Vec<Vec<OD>>)> {
    let shape = b[0].shape().to_vec();
    let k = match shape[..] {
        [r] if r == n => 1,
        [r, k] if r == n => k,
        _ => {
            return Err(PyValueError::new_err(format!(
                "b must be of shape (n,) or (n, k), n = {n} the order of A"
            )))
        }
    };
    if b.iter().any(|p| p.shape() != shape) {
        return Err(PyValueError::new_err("b0, ..., b7 must have the same shape"));
    }
    let mut s: [&[f64]; 8] = [&[]; 8];
    for (q, p) in b.iter().enumerate() {
        s[q] = rows(p, &format!("b{q}"))?;
    }
    let mut cols = vec![vec![OD::ZERO; n]; k];
    for i in 0..n {
        for (j, col) in cols.iter_mut().enumerate() {
            let o = i * k + j;
            let v = OD::new(std::array::from_fn(|q| s[q][o]));
            if !v.x.iter().all(|x| x.is_finite()) {
                return Err(PyValueError::new_err(if shape.len() == 1 {
                    format!("b has a non-finite entry at {i}")
                } else {
                    format!("b has a non-finite entry at ({i}, {j})")
                }));
            }
            col[i] = v;
        }
    }
    Ok((shape, cols))
}

/// the columns of an octo-double solution as eight part arrays of b's shape
fn od_parts<'py>(py: Python<'py>, shape: &[usize], cols: &[Vec<OD>]) -> PyResult<Parts8<'py>> {
    let (n, k) = (shape[0], cols.len());
    let part = |q: usize| -> PyResult<Part<'py>> {
        let mut v = vec![0.0; n * k];
        for (j, col) in cols.iter().enumerate() {
            for (i, x) in col.iter().enumerate() {
                v[i * k + j] = x.x[q];
            }
        }
        let a = ArrayD::from_shape_vec(IxDyn(shape), v).map_err(|e| PyValueError::new_err(e.to_string()))?;
        Ok(a.into_pyarray(py))
    };
    Ok((
        part(0)?,
        part(1)?,
        part(2)?,
        part(3)?,
        part(4)?,
        part(5)?,
        part(6)?,
        part(7)?,
    ))
}

/// each column solved in place with the factors (A x = b, or A^T x = b when transpose), with the GIL released
fn solve_cols(py: Python<'_>, lu: &ODLu, cols: &mut [Vec<OD>], transpose: bool) {
    py.detach(|| {
        for x in cols.iter_mut() {
            if transpose {
                lu.solve_t(x);
            } else {
                lu.solve(x);
            }
        }
    });
}

/// x with A x = b in octo-double, by LU with partial pivoting (the crate's `ODLu`): A as eight (n, n) row-major part
/// arrays, b as eight part arrays of shape (n,) or (n, k) (k right-hand sides, the columns of b), each entry
/// renormalized first. Returns the eight parts of x, of b's shape. Raises ValueError if A is singular, if A or b has a
/// non-finite entry, or for mismatched shapes.
#[pyfunction]
#[pyo3(signature = (a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3, b4, b5, b6, b7))]
#[allow(clippy::too_many_arguments)]
fn od_solve<'py>(
    py: Python<'py>,
    a0: PyReadonlyArray2<'py, f64>,
    a1: PyReadonlyArray2<'py, f64>,
    a2: PyReadonlyArray2<'py, f64>,
    a3: PyReadonlyArray2<'py, f64>,
    a4: PyReadonlyArray2<'py, f64>,
    a5: PyReadonlyArray2<'py, f64>,
    a6: PyReadonlyArray2<'py, f64>,
    a7: PyReadonlyArray2<'py, f64>,
    b0: PyReadonlyArrayDyn<'py, f64>,
    b1: PyReadonlyArrayDyn<'py, f64>,
    b2: PyReadonlyArrayDyn<'py, f64>,
    b3: PyReadonlyArrayDyn<'py, f64>,
    b4: PyReadonlyArrayDyn<'py, f64>,
    b5: PyReadonlyArrayDyn<'py, f64>,
    b6: PyReadonlyArrayDyn<'py, f64>,
    b7: PyReadonlyArrayDyn<'py, f64>,
) -> PyResult<Parts8<'py>> {
    let (n, ld, c) = od_matrix(&[a0, a1, a2, a3, a4, a5, a6, a7])?;
    // b is read and checked before the factorization, which costs n^3 / 3 octo-double updates
    let (shape, mut cols) = od_rhs(&[b0, b1, b2, b3, b4, b5, b6, b7], n)?;
    let lu = py
        .detach(|| ODLu::factor(n, ld, c, false))
        .map_err(PyValueError::new_err)?;
    solve_cols(py, &lu, &mut cols, false);
    od_parts(py, &shape, &cols)
}

/// The octo-double LU of A with partial pivoting (the crate's `ODLu`), factored once for several solves: ODLu(a0, ...,
/// a7) with A as eight (n, n) row-major part arrays, each entry renormalized first. Raises ValueError if A is singular
/// or has a non-finite entry.
#[pyclass(name = "ODLu", module = "multidouble._multidouble", frozen)]
struct PyOdLu {
    lu: ODLu,
}

#[pymethods]
impl PyOdLu {
    /// factor A, given as eight (n, n) row-major part arrays
    #[new]
    #[pyo3(signature = (a0, a1, a2, a3, a4, a5, a6, a7))]
    #[allow(clippy::too_many_arguments)]
    fn new(
        py: Python<'_>,
        a0: PyReadonlyArray2<'_, f64>,
        a1: PyReadonlyArray2<'_, f64>,
        a2: PyReadonlyArray2<'_, f64>,
        a3: PyReadonlyArray2<'_, f64>,
        a4: PyReadonlyArray2<'_, f64>,
        a5: PyReadonlyArray2<'_, f64>,
        a6: PyReadonlyArray2<'_, f64>,
        a7: PyReadonlyArray2<'_, f64>,
    ) -> PyResult<Self> {
        let (n, ld, c) = od_matrix(&[a0, a1, a2, a3, a4, a5, a6, a7])?;
        let lu = py
            .detach(|| ODLu::factor(n, ld, c, false))
            .map_err(PyValueError::new_err)?;
        Ok(PyOdLu { lu })
    }

    /// the order n of A
    #[getter]
    fn n(&self) -> usize {
        self.lu.n
    }

    /// x with A x = b (A^T x = b when transpose) in octo-double: b as eight part arrays of shape (n,) or (n, k), each
    /// entry renormalized first. Returns the eight parts of x, of b's shape; with transpose false, bitwise those of
    /// od_solve. Raises ValueError if b has a non-finite entry or the wrong shape.
    #[pyo3(signature = (b0, b1, b2, b3, b4, b5, b6, b7, transpose = false))]
    #[allow(clippy::too_many_arguments)]
    fn solve<'py>(
        &self,
        py: Python<'py>,
        b0: PyReadonlyArrayDyn<'py, f64>,
        b1: PyReadonlyArrayDyn<'py, f64>,
        b2: PyReadonlyArrayDyn<'py, f64>,
        b3: PyReadonlyArrayDyn<'py, f64>,
        b4: PyReadonlyArrayDyn<'py, f64>,
        b5: PyReadonlyArrayDyn<'py, f64>,
        b6: PyReadonlyArrayDyn<'py, f64>,
        b7: PyReadonlyArrayDyn<'py, f64>,
        transpose: bool,
    ) -> PyResult<Parts8<'py>> {
        let (shape, mut cols) = od_rhs(&[b0, b1, b2, b3, b4, b5, b6, b7], self.lu.n)?;
        solve_cols(py, &self.lu, &mut cols, transpose);
        od_parts(py, &shape, &cols)
    }
}

/// the eight parts of an octo-double array, one 1-D array each
type Parts8x1<'py> = (A1<'py>, A1<'py>, A1<'py>, A1<'py>, A1<'py>, A1<'py>, A1<'py>, A1<'py>);
type A1<'py> = Bound<'py, PyArray1<f64>>;

/// eight part arrays to Python
fn parts1(py: Python<'_>, v: [Vec<f64>; 8]) -> Parts8x1<'_> {
    let [a, b, c, d, e, f, g, h] = v.map(|p| p.into_pyarray(py));
    (a, b, c, d, e, f, g, h)
}

/// the eight contiguous slices of z0..z7, named z0..z7 (x0.., y0.. likewise) in the errors
fn slices8<'a>(z: &'a [PyReadonlyArray1<'_, f64>; 8], name: &str) -> PyResult<[&'a [f64]; 8]> {
    let mut s: [&[f64]; 8] = [&[]; 8];
    for (q, p) in z.iter().enumerate() {
        s[q] = super::slice(p, &format!("{name}{q}"))?;
    }
    Ok(s)
}

/// z + d elementwise for an octo-double z (eight parts, renormalized first, `OD::new`) and a double-double d
/// (`OD::from_dd`, then `+`): 8 lanes at a time on the backend S (`OV::new`), the remainder in scalar octo-double
/// (bitwise the same per element)
struct OdAddDd<'a> {
    z: [&'a [f64]; 8],
    d: (&'a [f64], &'a [f64]),
    out: [&'a mut [f64]; 8],
}

impl Kernel for OdAddDd<'_> {
    type Output = ();
    /// the lanes, then the scalar tail
    #[inline(always)]
    fn run<S: Simd>(self) {
        let n = self.d.0.len();
        let full = n / 8 * 8;
        let z = self.z;
        let mut out = self.out;
        for i in (0..full).step_by(8) {
            let q = OV::<S>::new(z.map(|p| V8::load(&p[i..i + 8])));
            let r = q + OV::from_dv(DV::<S>::load(&self.d.0[i..i + 8], &self.d.1[i..i + 8]));
            for (k, o) in out.iter_mut().enumerate() {
                r.c[k].store(&mut o[i..i + 8]);
            }
        }
        for i in full..n {
            let r = OD::new(z.map(|p| p[i]))
                + OD::from_dd(DD {
                    hi: self.d.0[i],
                    lo: self.d.1[i],
                });
            for (k, o) in out.iter_mut().enumerate() {
                o[i] = r.x[k];
            }
        }
    }
}

/// (z0 + ... + z7) + (dh + dl) elementwise in octo-double: an octo-double array (eight float64 arrays, renormalized
/// first as od_solve takes its entries) plus a double-double one, e.g. a Newton step applied to a state kept in
/// octo-double. Returns the eight parts of the result, renormalized.
#[pyfunction]
#[pyo3(signature = (z0, z1, z2, z3, z4, z5, z6, z7, dh, dl))]
#[allow(clippy::too_many_arguments)]
fn od_add_dd<'py>(
    py: Python<'py>,
    z0: PyReadonlyArray1<'py, f64>,
    z1: PyReadonlyArray1<'py, f64>,
    z2: PyReadonlyArray1<'py, f64>,
    z3: PyReadonlyArray1<'py, f64>,
    z4: PyReadonlyArray1<'py, f64>,
    z5: PyReadonlyArray1<'py, f64>,
    z6: PyReadonlyArray1<'py, f64>,
    z7: PyReadonlyArray1<'py, f64>,
    dh: PyReadonlyArray1<'py, f64>,
    dl: PyReadonlyArray1<'py, f64>,
) -> PyResult<Parts8x1<'py>> {
    let zs = [z0, z1, z2, z3, z4, z5, z6, z7];
    let z = slices8(&zs, "z")?;
    let d = (super::slice(&dh, "dh")?, super::slice(&dl, "dl")?);
    let n = d.0.len();
    if d.1.len() != n || z.iter().any(|p| p.len() != n) {
        return Err(PyValueError::new_err(
            "z0, ..., z7, dh and dl must have the same length",
        ));
    }
    let mut out: [Vec<f64>; 8] = std::array::from_fn(|_| vec![0.0; n]);
    let [o0, o1, o2, o3, o4, o5, o6, o7] = &mut out;
    // with the GIL held: the slices borrow the input arrays, which another thread could change while it is released
    simd::dispatch(OdAddDd {
        z,
        d,
        out: [o0, o1, o2, o3, o4, o5, o6, o7].map(|o| &mut o[..]),
    });
    Ok(parts1(py, out))
}

/// y + a x elementwise in octo-double for octo-double arrays x and y (eight float64 arrays each, the parts normalized
/// as an octo-double keeps them, e.g. the output of od_add_dd) and a float a: each element times a and the sum in
/// octo-double (the crate's `ov::axpy_parts`), 8 at a time on the best SIMD backend, bitwise the same on every
/// backend. Returns the eight parts of the result.
#[pyfunction]
#[pyo3(signature = (a, x0, x1, x2, x3, x4, x5, x6, x7, y0, y1, y2, y3, y4, y5, y6, y7))]
#[allow(clippy::too_many_arguments)]
fn od_axpy<'py>(
    py: Python<'py>,
    a: f64,
    x0: PyReadonlyArray1<'py, f64>,
    x1: PyReadonlyArray1<'py, f64>,
    x2: PyReadonlyArray1<'py, f64>,
    x3: PyReadonlyArray1<'py, f64>,
    x4: PyReadonlyArray1<'py, f64>,
    x5: PyReadonlyArray1<'py, f64>,
    x6: PyReadonlyArray1<'py, f64>,
    x7: PyReadonlyArray1<'py, f64>,
    y0: PyReadonlyArray1<'py, f64>,
    y1: PyReadonlyArray1<'py, f64>,
    y2: PyReadonlyArray1<'py, f64>,
    y3: PyReadonlyArray1<'py, f64>,
    y4: PyReadonlyArray1<'py, f64>,
    y5: PyReadonlyArray1<'py, f64>,
    y6: PyReadonlyArray1<'py, f64>,
    y7: PyReadonlyArray1<'py, f64>,
) -> PyResult<Parts8x1<'py>> {
    let (xs, ys) = ([x0, x1, x2, x3, x4, x5, x6, x7], [y0, y1, y2, y3, y4, y5, y6, y7]);
    let (x, y) = (slices8(&xs, "x")?, slices8(&ys, "y")?);
    let n = y[0].len();
    if x.iter().chain(y.iter()).any(|p| p.len() != n) {
        return Err(PyValueError::new_err(
            "x0, ..., x7 and y0, ..., y7 must have the same length",
        ));
    }
    // with the GIL held, as in od_add_dd
    Ok(parts1(py, axpy_parts(a, x, y)))
}

/// od_solve, ODLu, od_add_dd and od_axpy added to the module
pub fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(od_solve, m)?)?;
    m.add_class::<PyOdLu>()?;
    m.add_function(wrap_pyfunction!(od_add_dd, m)?)?;
    m.add_function(wrap_pyfunction!(od_axpy, m)?)?;
    Ok(())
}
