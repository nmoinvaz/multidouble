//! The octo-double LU solve: `od_solve` and the class `ODLu`, with A and b as eight float64 part arrays each.
use multidouble::linalg::{ld_for, ODLu};
use multidouble::od::OD;
use numpy::ndarray::{ArrayD, Dimension};
use numpy::{
    IntoPyArray, IxDyn, PyArrayDyn, PyReadonlyArray, PyReadonlyArray2, PyReadonlyArrayDyn, PyUntypedArrayMethods,
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

/// od_solve and ODLu added to the module
pub fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(od_solve, m)?)?;
    m.add_class::<PyOdLu>()?;
    Ok(())
}
