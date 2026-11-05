//! Python bindings of multidouble: double-double numbers as pairs of float64 numpy arrays (hi, lo), elementwise
//! arithmetic, dot products, matrix-vector products and the Horner sum of a power series on them on the best SIMD
//! backend the CPU has, quad-double arrays (four parts) plus a double-double one or plus a multiple of another, and
//! dense LU solves in double-double and in quad-double.
use multidouble::dd::{self, DD};
use multidouble::dv::{self, DotAcc, DV};
use multidouble::linalg::{ld_for, DDLu, QDLu};
use multidouble::qd::QD;
use multidouble::qv::{axpy_parts, renorm4, QV};
use multidouble::simd::{self, Kernel, Simd};
use multidouble::v8::V8;
use numpy::ndarray::{ArrayD, Dimension};
use numpy::{
    IntoPyArray, IxDyn, PyArray1, PyArrayDyn, PyReadonlyArray, PyReadonlyArray1, PyReadonlyArray2, PyReadonlyArrayDyn,
    PyUntypedArrayMethods,
};

type Parts<'py> = (
    Bound<'py, PyArray1<f64>>,
    Bound<'py, PyArray1<f64>>,
    Bound<'py, PyArray1<f64>>,
    Bound<'py, PyArray1<f64>>,
);
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;

mod octo;

type Pair<'py> = (Bound<'py, PyArray1<f64>>, Bound<'py, PyArray1<f64>>);

const ADD: u8 = 0;
const MUL: u8 = 1;
const DIV: u8 = 2;
const SUB: u8 = 3;

fn slice<'a>(a: &'a PyReadonlyArray1<f64>, name: &str) -> PyResult<&'a [f64]> {
    a.as_slice()
        .map_err(|_| PyValueError::new_err(format!("{name} must be a contiguous float64 array")))
}

/// an array's elements in row-major order. `as_slice` also takes a Fortran-ordered array, whose elements it gives in
/// column-major order, so that is refused here.
fn rows<'a, D: Dimension>(a: &'a PyReadonlyArray<'_, f64, D>, name: &str) -> PyResult<&'a [f64]> {
    let err = || PyValueError::new_err(format!("{name} must be C-contiguous"));
    if !a.is_c_contiguous() {
        return Err(err());
    }
    a.as_slice().map_err(|_| err())
}

/// out = a op b elementwise: 8 lanes at a time on the backend S, the remainder in scalar double-double (each lane is
/// bitwise the scalar result, so the split does not show in the output)
struct Elementwise<'a> {
    op: u8,
    a: (&'a [f64], &'a [f64]),
    b: (&'a [f64], &'a [f64]),
    out: (&'a mut [f64], &'a mut [f64]),
}

impl Kernel for Elementwise<'_> {
    type Output = ();
    #[inline(always)]
    fn run<S: Simd>(self) {
        let n = self.a.0.len();
        let full = n / 8 * 8;
        let (oh, ol) = self.out;
        for i in (0..full).step_by(8) {
            let x = DV::<S>::load(&self.a.0[i..i + 8], &self.a.1[i..i + 8]);
            let y = DV::<S>::load(&self.b.0[i..i + 8], &self.b.1[i..i + 8]);
            let r = match self.op {
                ADD => x + y,
                MUL => x * y,
                DIV => x / y,
                _ => x - y,
            };
            r.store(&mut oh[i..i + 8], &mut ol[i..i + 8]);
        }
        for i in full..n {
            let x = DD {
                hi: self.a.0[i],
                lo: self.a.1[i],
            };
            let y = DD {
                hi: self.b.0[i],
                lo: self.b.1[i],
            };
            let r = match self.op {
                ADD => x + y,
                MUL => x * y,
                DIV => x / y,
                _ => x - y,
            };
            oh[i] = r.hi;
            ol[i] = r.lo;
        }
    }
}

fn elementwise<'py>(
    py: Python<'py>,
    op: u8,
    ah: PyReadonlyArray1<'py, f64>,
    al: PyReadonlyArray1<'py, f64>,
    bh: PyReadonlyArray1<'py, f64>,
    bl: PyReadonlyArray1<'py, f64>,
) -> PyResult<Pair<'py>> {
    if op > SUB {
        return Err(PyValueError::new_err(format!(
            "op must be 0 (add), 1 (mul), 2 (div) or 3 (sub), not {op}"
        )));
    }
    let (a0, a1, b0, b1) = (
        slice(&ah, "ah")?,
        slice(&al, "al")?,
        slice(&bh, "bh")?,
        slice(&bl, "bl")?,
    );
    let n = a0.len();
    if a1.len() != n || b0.len() != n || b1.len() != n {
        return Err(PyValueError::new_err("ah, al, bh and bl must have the same length"));
    }
    let mut oh = vec![0.0; n];
    let mut ol = vec![0.0; n];
    // with the GIL held: the slices borrow the input arrays, which another thread could change or reallocate
    // (ndarray.resize with refcheck=False) while it is released; the operation is a single pass over memory
    simd::dispatch(Elementwise {
        op,
        a: (a0, a1),
        b: (b0, b1),
        out: (&mut oh, &mut ol),
    });
    Ok((oh.into_pyarray(py), ol.into_pyarray(py)))
}

/// (ah + al) op (bh + bl) elementwise in double-double, any length: op 0 add, 1 mul, 2 div, 3 sub.
/// Returns the (hi, lo) arrays of the result.
#[pyfunction]
fn dd_op<'py>(
    py: Python<'py>,
    op: u8,
    ah: PyReadonlyArray1<'py, f64>,
    al: PyReadonlyArray1<'py, f64>,
    bh: PyReadonlyArray1<'py, f64>,
    bl: PyReadonlyArray1<'py, f64>,
) -> PyResult<Pair<'py>> {
    elementwise(py, op, ah, al, bh, bl)
}

/// a + b in double-double, elementwise: (hi, lo)
#[pyfunction]
fn add<'py>(
    py: Python<'py>,
    ah: PyReadonlyArray1<'py, f64>,
    al: PyReadonlyArray1<'py, f64>,
    bh: PyReadonlyArray1<'py, f64>,
    bl: PyReadonlyArray1<'py, f64>,
) -> PyResult<Pair<'py>> {
    elementwise(py, ADD, ah, al, bh, bl)
}

/// a - b in double-double, elementwise: (hi, lo)
#[pyfunction]
fn sub<'py>(
    py: Python<'py>,
    ah: PyReadonlyArray1<'py, f64>,
    al: PyReadonlyArray1<'py, f64>,
    bh: PyReadonlyArray1<'py, f64>,
    bl: PyReadonlyArray1<'py, f64>,
) -> PyResult<Pair<'py>> {
    elementwise(py, SUB, ah, al, bh, bl)
}

/// a b in double-double, elementwise: (hi, lo)
#[pyfunction]
fn mul<'py>(
    py: Python<'py>,
    ah: PyReadonlyArray1<'py, f64>,
    al: PyReadonlyArray1<'py, f64>,
    bh: PyReadonlyArray1<'py, f64>,
    bl: PyReadonlyArray1<'py, f64>,
) -> PyResult<Pair<'py>> {
    elementwise(py, MUL, ah, al, bh, bl)
}

/// a / b in double-double, elementwise: (hi, lo)
#[pyfunction]
fn div<'py>(
    py: Python<'py>,
    ah: PyReadonlyArray1<'py, f64>,
    al: PyReadonlyArray1<'py, f64>,
    bh: PyReadonlyArray1<'py, f64>,
    bl: PyReadonlyArray1<'py, f64>,
) -> PyResult<Pair<'py>> {
    elementwise(py, DIV, ah, al, bh, bl)
}

/// z + d elementwise for a quad-double z (four parts, renormalized first as `QD::new` does) and a double-double d
/// (`QD::add_dd`): 8 lanes at a time on the backend S, the remainder in scalar quad-double (bitwise the same per
/// element)
struct QdAddDd<'a> {
    z: [&'a [f64]; 4],
    d: (&'a [f64], &'a [f64]),
    out: [&'a mut [f64]; 4],
}

impl Kernel for QdAddDd<'_> {
    type Output = ();
    #[inline(always)]
    fn run<S: Simd>(self) {
        let n = self.d.0.len();
        let full = n / 8 * 8;
        let z = self.z;
        let [o0, o1, o2, o3] = self.out;
        for i in (0..full).step_by(8) {
            let q = QV::<S>::load(&z[0][i..i + 8], &z[1][i..i + 8], &z[2][i..i + 8], &z[3][i..i + 8]);
            let q = QV {
                c: renorm4(q.c[0], q.c[1], q.c[2], q.c[3]),
            };
            let r = q.add_dv(DV::<S>::load(&self.d.0[i..i + 8], &self.d.1[i..i + 8]));
            r.store(
                &mut o0[i..i + 8],
                &mut o1[i..i + 8],
                &mut o2[i..i + 8],
                &mut o3[i..i + 8],
            );
        }
        for i in full..n {
            let r = QD::new(z[0][i], z[1][i], z[2][i], z[3][i]).add_dd(DD {
                hi: self.d.0[i],
                lo: self.d.1[i],
            });
            o0[i] = r.x[0];
            o1[i] = r.x[1];
            o2[i] = r.x[2];
            o3[i] = r.x[3];
        }
    }
}

/// (z0 + z1 + z2 + z3) + (dh + dl) elementwise in quad-double: a quad-double array (four float64 arrays, renormalized
/// first, so any four parts summing to the value will do) plus a double-double one, e.g. a Newton step applied to a
/// state kept in quad-double. Returns the four parts of the result, renormalized.
#[pyfunction]
fn qd_add_dd<'py>(
    py: Python<'py>,
    z0: PyReadonlyArray1<'py, f64>,
    z1: PyReadonlyArray1<'py, f64>,
    z2: PyReadonlyArray1<'py, f64>,
    z3: PyReadonlyArray1<'py, f64>,
    dh: PyReadonlyArray1<'py, f64>,
    dl: PyReadonlyArray1<'py, f64>,
) -> PyResult<Parts<'py>> {
    let z = [
        slice(&z0, "z0")?,
        slice(&z1, "z1")?,
        slice(&z2, "z2")?,
        slice(&z3, "z3")?,
    ];
    let d = (slice(&dh, "dh")?, slice(&dl, "dl")?);
    let n = d.0.len();
    if d.1.len() != n || z.iter().any(|p| p.len() != n) {
        return Err(PyValueError::new_err(
            "z0, z1, z2, z3, dh and dl must have the same length",
        ));
    }
    let (mut o0, mut o1, mut o2, mut o3) = (vec![0.0; n], vec![0.0; n], vec![0.0; n], vec![0.0; n]);
    // with the GIL held, as in elementwise
    simd::dispatch(QdAddDd {
        z,
        d,
        out: [&mut o0, &mut o1, &mut o2, &mut o3],
    });
    Ok((
        o0.into_pyarray(py),
        o1.into_pyarray(py),
        o2.into_pyarray(py),
        o3.into_pyarray(py),
    ))
}

/// sum_i x_i y_i in double-double: 8 lanes at a time with `DotAcc` on the backend S (the last block padded with
/// zeros, whose products add nothing), then the 8 lane sums added in double-double in lane order, so the result is
/// bitwise the same on every backend
struct Dot<'a> {
    x: (&'a [f64], &'a [f64]),
    y: (&'a [f64], &'a [f64]),
}

/// the dot product of `Dot` on the backend S
#[inline(always)]
fn dot_on<S: Simd>(x: (&[f64], &[f64]), y: (&[f64], &[f64])) -> DD {
    let n = x.0.len();
    let full = n / 8 * 8;
    let mut acc = DotAcc::<S>::zero();
    for i in (0..full).step_by(8) {
        let xv = DV::<S>::load(&x.0[i..i + 8], &x.1[i..i + 8]);
        let yv = DV::<S>::load(&y.0[i..i + 8], &y.1[i..i + 8]);
        acc = acc.add_prod(xv, yv);
    }
    if full < n {
        let pad = |a: &[f64]| -> [f64; 8] { std::array::from_fn(|r| a.get(full + r).copied().unwrap_or(0.0)) };
        let xv = DV::<S>::load(&pad(x.0), &pad(x.1));
        let yv = DV::<S>::load(&pad(y.0), &pad(y.1));
        acc = acc.add_prod(xv, yv);
    }
    let v = acc.finish();
    let mut sum = DD::ZERO;
    for j in 0..8 {
        sum = sum + v.lane(j);
    }
    sum
}

impl Kernel for Dot<'_> {
    type Output = DD;
    #[inline(always)]
    fn run<S: Simd>(self) -> DD {
        dot_on::<S>(self.x, self.y)
    }
}

/// y_i = sum_j a_ij v_j, each row the dot product of `Dot` (A row-major, n rows of m)
struct MatVec<'a> {
    m: usize,
    a: (&'a [f64], &'a [f64]),
    v: (&'a [f64], &'a [f64]),
    out: (&'a mut [f64], &'a mut [f64]),
}

impl Kernel for MatVec<'_> {
    type Output = ();
    #[inline(always)]
    fn run<S: Simd>(self) {
        let m = self.m;
        for i in 0..self.out.0.len() {
            let row = (&self.a.0[i * m..(i + 1) * m], &self.a.1[i * m..(i + 1) * m]);
            let d = dot_on::<S>(row, self.v);
            self.out.0[i] = d.hi;
            self.out.1[i] = d.lo;
        }
    }
}

/// sum_i (xh + xl)_i (yh + yl)_i in double-double, 8 lanes at a time on the best SIMD backend: each lane sums its
/// products with an error-free sum of their leading parts and the rest in float64, then the 8 lane sums are added
/// in double-double. Within about (n / 8 + 12) u^2 of sum |x_i y_i|, u^2 = 2^-106, and bitwise the same on every
/// backend. Returns (hi, lo) as floats.
#[pyfunction]
fn dd_dot(
    xh: PyReadonlyArray1<'_, f64>,
    xl: PyReadonlyArray1<'_, f64>,
    yh: PyReadonlyArray1<'_, f64>,
    yl: PyReadonlyArray1<'_, f64>,
) -> PyResult<(f64, f64)> {
    let (x0, x1, y0, y1) = (
        slice(&xh, "xh")?,
        slice(&xl, "xl")?,
        slice(&yh, "yh")?,
        slice(&yl, "yl")?,
    );
    let n = x0.len();
    if x1.len() != n || y0.len() != n || y1.len() != n {
        return Err(PyValueError::new_err("xh, xl, yh and yl must have the same length"));
    }
    // with the GIL held, as the elementwise functions: the slices borrow the input arrays
    let d = simd::dispatch(Dot {
        x: (x0, x1),
        y: (y0, y1),
    });
    Ok((d.hi, d.lo))
}

/// A v in double-double: A as (n, m) row-major hi and lo arrays, v as hi and lo arrays of length m; each row of the
/// result is the dot product of `dd_dot` (8 lanes at a time, then the lane sums), so within about (m / 8 + 12) u^2
/// of sum_j |a_ij v_j|, u^2 = 2^-106, and bitwise the same on every backend. Returns the (hi, lo) arrays of A v.
#[pyfunction]
fn dd_matvec<'py>(
    py: Python<'py>,
    ah: PyReadonlyArray2<'py, f64>,
    al: PyReadonlyArray2<'py, f64>,
    vh: PyReadonlyArray1<'py, f64>,
    vl: PyReadonlyArray1<'py, f64>,
) -> PyResult<Pair<'py>> {
    let [n, m] = ah.shape() else {
        return Err(PyValueError::new_err("A must be two-dimensional"));
    };
    let (n, m) = (*n, *m);
    if al.shape() != [n, m] || vh.len() != m || vl.len() != m {
        return Err(PyValueError::new_err(
            "A must be (n, m) in both parts and v of length m in both parts",
        ));
    }
    let (ahs, als) = (rows(&ah, "ah")?, rows(&al, "al")?);
    let (v0, v1) = (slice(&vh, "vh")?, slice(&vl, "vl")?);
    let mut oh = vec![0.0; n];
    let mut ol = vec![0.0; n];
    // with the GIL held, as the elementwise functions: the slices borrow the input arrays
    simd::dispatch(MatVec {
        m,
        a: (ahs, als),
        v: (v0, v1),
        out: (&mut oh, &mut ol),
    });
    Ok((oh.into_pyarray(py), ol.into_pyarray(py)))
}

/// y + a x elementwise in quad-double for quad-double arrays x and y (four float64 arrays each, the parts
/// normalized as a quad-double keeps them, e.g. the output of `qd_add_dd`) and a float a: each element times a and
/// the sum in quad-double, 8 at a time on the best SIMD backend, bitwise the same on every backend. Returns the four
/// parts of the result.
#[pyfunction]
#[allow(clippy::too_many_arguments)]
fn qd_axpy<'py>(
    py: Python<'py>,
    a: f64,
    x0: PyReadonlyArray1<'py, f64>,
    x1: PyReadonlyArray1<'py, f64>,
    x2: PyReadonlyArray1<'py, f64>,
    x3: PyReadonlyArray1<'py, f64>,
    y0: PyReadonlyArray1<'py, f64>,
    y1: PyReadonlyArray1<'py, f64>,
    y2: PyReadonlyArray1<'py, f64>,
    y3: PyReadonlyArray1<'py, f64>,
) -> PyResult<Parts<'py>> {
    let x = [
        slice(&x0, "x0")?,
        slice(&x1, "x1")?,
        slice(&x2, "x2")?,
        slice(&x3, "x3")?,
    ];
    let y = [
        slice(&y0, "y0")?,
        slice(&y1, "y1")?,
        slice(&y2, "y2")?,
        slice(&y3, "y3")?,
    ];
    let n = y[0].len();
    if x.iter().chain(y.iter()).any(|p| p.len() != n) {
        return Err(PyValueError::new_err(
            "x0, x1, x2, x3, y0, y1, y2 and y3 must have the same length",
        ));
    }
    // with the GIL held, as in elementwise
    let [o0, o1, o2, o3] = axpy_parts(a, x, y);
    Ok((
        o0.into_pyarray(py),
        o1.into_pyarray(py),
        o2.into_pyarray(py),
        o3.into_pyarray(py),
    ))
}

/// x with A x = b in double-double, by LU with partial pivoting: A as (n, n) row-major hi and lo arrays, b as hi
/// and lo arrays of length n. Returns the (hi, lo) arrays of x. Raises ValueError if A is singular.
#[pyfunction]
fn dd_solve<'py>(
    py: Python<'py>,
    ah: PyReadonlyArray2<'py, f64>,
    al: PyReadonlyArray2<'py, f64>,
    bh: PyReadonlyArray1<'py, f64>,
    bl: PyReadonlyArray1<'py, f64>,
) -> PyResult<Pair<'py>> {
    let n = bh.len();
    if ah.shape() != [n, n] || al.shape() != [n, n] || bl.len() != n {
        return Err(PyValueError::new_err(
            "A must be (n, n) and b of length n, in both parts",
        ));
    }
    let (ahs, als) = (rows(&ah, "ah")?, rows(&al, "al")?);
    let (b0, b1) = (slice(&bh, "bh")?, slice(&bl, "bl")?);
    let ld = ld_for(n);
    let mut h = vec![0.0; ld * n];
    let mut l = vec![0.0; ld * n];
    // column-major with leading dimension ld, as DDLu stores it
    for r in 0..n {
        for c in 0..n {
            h[c * ld + r] = ahs[r * n + c];
            l[c * ld + r] = als[r * n + c];
        }
    }
    let mut b: Vec<DD> = b0.iter().zip(b1).map(|(&hi, &lo)| DD { hi, lo }).collect();
    py.detach(|| -> Result<(), String> {
        let lu = DDLu::factor(n, ld, h, l, false)?;
        lu.solve(&mut b);
        Ok(())
    })
    .map_err(PyValueError::new_err)?;
    Ok((
        b.iter().map(|v| v.hi).collect::<Vec<_>>().into_pyarray(py),
        b.iter().map(|v| v.lo).collect::<Vec<_>>().into_pyarray(py),
    ))
}

type DynParts<'py> = (
    Bound<'py, PyArrayDyn<f64>>,
    Bound<'py, PyArrayDyn<f64>>,
    Bound<'py, PyArrayDyn<f64>>,
    Bound<'py, PyArrayDyn<f64>>,
);

/// A in the layout of `QDLu::factor`: four (n, n) row-major part arrays, each entry renormalized (`QD::new`) and
/// stored column-major with leading dimension `ld_for(n)`, the padding rows zero. Returns (n, ld, parts). Raises
/// ValueError for unequal or non-square shapes and for an entry that is not finite.
fn qd_matrix(a: [&PyReadonlyArray2<'_, f64>; 4]) -> PyResult<(usize, usize, [Vec<f64>; 4])> {
    let n = a[0].shape()[0];
    if a.iter().any(|p| p.shape() != [n, n]) {
        return Err(PyValueError::new_err("A must be (n, n), the same in all four parts"));
    }
    let s = [
        rows(a[0], "a0")?,
        rows(a[1], "a1")?,
        rows(a[2], "a2")?,
        rows(a[3], "a3")?,
    ];
    let ld = ld_for(n);
    let mut c: [Vec<f64>; 4] = std::array::from_fn(|_| vec![0.0; ld * n]);
    for i in 0..n {
        for j in 0..n {
            let k = i * n + j;
            let v = QD::new(s[0][k], s[1][k], s[2][k], s[3][k]);
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

/// b as k columns of n quad-doubles, each entry renormalized (`QD::new`): four part arrays of shape (n,) (k = 1) or
/// (n, k), row-major. Returns b's shape and the columns. Raises ValueError for another shape, unequal shapes or an
/// entry that is not finite.
fn qd_rhs(b: [&PyReadonlyArrayDyn<'_, f64>; 4], n: usize) -> PyResult<(Vec<usize>, Vec<Vec<QD>>)> {
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
        return Err(PyValueError::new_err("b0, b1, b2 and b3 must have the same shape"));
    }
    let s = [
        rows(b[0], "b0")?,
        rows(b[1], "b1")?,
        rows(b[2], "b2")?,
        rows(b[3], "b3")?,
    ];
    let mut cols = vec![vec![QD::ZERO; n]; k];
    for i in 0..n {
        for (j, col) in cols.iter_mut().enumerate() {
            let o = i * k + j;
            let v = QD::new(s[0][o], s[1][o], s[2][o], s[3][o]);
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

/// the columns of a quad-double solution as four part arrays of b's shape
fn qd_parts<'py>(py: Python<'py>, shape: &[usize], cols: &[Vec<QD>]) -> PyResult<DynParts<'py>> {
    let (n, k) = (shape[0], cols.len());
    let part = |q: usize| -> PyResult<Bound<'py, PyArrayDyn<f64>>> {
        let mut v = vec![0.0; n * k];
        for (j, col) in cols.iter().enumerate() {
            for (i, x) in col.iter().enumerate() {
                v[i * k + j] = x.x[q];
            }
        }
        let a = ArrayD::from_shape_vec(IxDyn(shape), v).map_err(|e| PyValueError::new_err(e.to_string()))?;
        Ok(a.into_pyarray(py))
    };
    Ok((part(0)?, part(1)?, part(2)?, part(3)?))
}

/// each column solved in place with the factors (A x = b, or A^T x = b when transpose), with the GIL released
fn solve_cols(py: Python<'_>, lu: &QDLu, cols: &mut [Vec<QD>], transpose: bool) {
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

/// x with A x = b in quad-double, by LU with partial pivoting (the crate's `QDLu`): A as four (n, n) row-major part
/// arrays, b as four part arrays of shape (n,) or (n, k) (k right-hand sides, the columns of b), each entry
/// renormalized first. Returns the four parts of x, of b's shape. Raises ValueError if A is singular, if A or b has a
/// non-finite entry, or for mismatched shapes.
#[pyfunction]
#[allow(clippy::too_many_arguments)]
fn qd_solve<'py>(
    py: Python<'py>,
    a0: PyReadonlyArray2<'py, f64>,
    a1: PyReadonlyArray2<'py, f64>,
    a2: PyReadonlyArray2<'py, f64>,
    a3: PyReadonlyArray2<'py, f64>,
    b0: PyReadonlyArrayDyn<'py, f64>,
    b1: PyReadonlyArrayDyn<'py, f64>,
    b2: PyReadonlyArrayDyn<'py, f64>,
    b3: PyReadonlyArrayDyn<'py, f64>,
) -> PyResult<DynParts<'py>> {
    let (n, ld, c) = qd_matrix([&a0, &a1, &a2, &a3])?;
    // b is read and checked before the factorization, which costs n^3 / 3 quad-double updates
    let (shape, mut cols) = qd_rhs([&b0, &b1, &b2, &b3], n)?;
    let lu = py
        .detach(|| QDLu::factor(n, ld, c, false))
        .map_err(PyValueError::new_err)?;
    solve_cols(py, &lu, &mut cols, false);
    qd_parts(py, &shape, &cols)
}

/// The quad-double LU of A with partial pivoting (the crate's `QDLu`), factored once for several solves: QDLu(a0, a1,
/// a2, a3) with A as four (n, n) row-major part arrays, each entry renormalized first. Raises ValueError if A is
/// singular or has a non-finite entry.
#[pyclass(name = "QDLu", module = "multidouble._multidouble", frozen)]
struct PyQdLu {
    lu: QDLu,
}

#[pymethods]
impl PyQdLu {
    #[new]
    fn new(
        py: Python<'_>,
        a0: PyReadonlyArray2<'_, f64>,
        a1: PyReadonlyArray2<'_, f64>,
        a2: PyReadonlyArray2<'_, f64>,
        a3: PyReadonlyArray2<'_, f64>,
    ) -> PyResult<Self> {
        let (n, ld, c) = qd_matrix([&a0, &a1, &a2, &a3])?;
        let lu = py
            .detach(|| QDLu::factor(n, ld, c, false))
            .map_err(PyValueError::new_err)?;
        Ok(PyQdLu { lu })
    }

    /// the order n of A
    #[getter]
    fn n(&self) -> usize {
        self.lu.n
    }

    /// x with A x = b (A^T x = b when transpose) in quad-double: b as four part arrays of shape (n,) or (n, k), each
    /// entry renormalized first. Returns the four parts of x, of b's shape; with transpose false, bitwise those of
    /// qd_solve. Raises ValueError if b has a non-finite entry or the wrong shape.
    #[pyo3(signature = (b0, b1, b2, b3, transpose = false))]
    fn solve<'py>(
        &self,
        py: Python<'py>,
        b0: PyReadonlyArrayDyn<'py, f64>,
        b1: PyReadonlyArrayDyn<'py, f64>,
        b2: PyReadonlyArrayDyn<'py, f64>,
        b3: PyReadonlyArrayDyn<'py, f64>,
        transpose: bool,
    ) -> PyResult<DynParts<'py>> {
        let (shape, mut cols) = qd_rhs([&b0, &b1, &b2, &b3], self.lu.n)?;
        solve_cols(py, &self.lu, &mut cols, transpose);
        qd_parts(py, &shape, &cols)
    }
}

/// a x in double-double for an f64 a, as the numpy `dd_scale` forms it: the two-product of a and x.hi (exact, so
/// bitwise Dekker's product there), then a x.lo added to its error unfused (`DD::mul_f` fuses it), then the quick
/// two-sum
#[inline(always)]
fn scale_dd(x: DD, a: f64) -> DD {
    let (p, e) = dd::two_prod(a, x.hi);
    let e = e + a * x.lo;
    let (h, l) = dd::quick_two_sum(p, e);
    DD { hi: h, lo: l }
}

/// `scale_dd` on 8 lanes
#[inline(always)]
fn scale_dv<S: Simd>(x: DV<S>, a: V8<S>) -> DV<S> {
    let (p, e) = dv::two_prod(a, x.hi);
    let e = e.add(a.mul(x.lo));
    let (h, l) = dv::quick_two_sum(p, e);
    DV { hi: h, lo: l }
}

/// sum_k c_k a^k by Horner's rule: p = c_N, then p = c_k + `scale_dd`(p, a) for k = N - 1, ..., 0, which is the
/// numpy `dd_add(c_k, dd_scale(p, a))` bit for bit. The coefficients are the rows of (N + 1) n row-major arrays. 8
/// values at a time on the backend S, the remainder in scalar double-double with the same operations (bitwise the
/// same per value).
struct Horner<'a> {
    n: usize,
    c: (&'a [f64], &'a [f64]),
    a: f64,
    out: (&'a mut [f64], &'a mut [f64]),
}

/// coefficient k of values i..i + 8
#[inline(always)]
fn row_dv<S: Simd>(c: (&[f64], &[f64]), n: usize, k: usize, i: usize) -> DV<S> {
    let o = k * n + i;
    DV::<S>::load(&c.0[o..o + 8], &c.1[o..o + 8])
}

impl Kernel for Horner<'_> {
    type Output = ();
    #[inline(always)]
    fn run<S: Simd>(self) {
        let (n, c) = (self.n, self.c);
        let nc = c.0.len() / n;
        let full = n / 8 * 8;
        let (oh, ol) = self.out;
        let a = V8::<S>::splat(self.a);
        for i in (0..full).step_by(8) {
            let mut p = row_dv::<S>(c, n, nc - 1, i);
            for k in (0..nc - 1).rev() {
                p = row_dv::<S>(c, n, k, i) + scale_dv(p, a);
            }
            p.store(&mut oh[i..i + 8], &mut ol[i..i + 8]);
        }
        for i in full..n {
            let mut p = DD {
                hi: c.0[(nc - 1) * n + i],
                lo: c.1[(nc - 1) * n + i],
            };
            for k in (0..nc - 1).rev() {
                let ck = DD {
                    hi: c.0[k * n + i],
                    lo: c.1[k * n + i],
                };
                p = ck + scale_dd(p, self.a);
            }
            oh[i] = p.hi;
            ol[i] = p.lo;
        }
    }
}

/// sum_k (ch + cl)_k a^k by Horner's rule in double-double at a float a: the coefficients c_0, ..., c_N as (N + 1, n)
/// row-major hi and lo arrays, coefficient k in row k. From p = c_N, each step p = c_k + a p is the numpy
/// `dd_add(c_k, dd_scale(p, a))` bit for bit, 8 values at a time on the best SIMD backend, bitwise the same on every
/// backend. Returns the (hi, lo) arrays of the n sums. Raises ValueError for no coefficients or unequal shapes.
#[pyfunction]
fn dd_horner<'py>(
    py: Python<'py>,
    ch: PyReadonlyArray2<'py, f64>,
    cl: PyReadonlyArray2<'py, f64>,
    a: f64,
) -> PyResult<Pair<'py>> {
    let [nc, n] = ch.shape() else {
        return Err(PyValueError::new_err("ch must be two-dimensional, (N + 1, n)"));
    };
    let (nc, n) = (*nc, *n);
    if cl.shape() != [nc, n] {
        return Err(PyValueError::new_err("ch and cl must have one shape, (N + 1, n)"));
    }
    if nc == 0 {
        return Err(PyValueError::new_err("a series needs at least one coefficient"));
    }
    let (chs, cls) = (rows(&ch, "ch")?, rows(&cl, "cl")?);
    let mut oh = vec![0.0; n];
    let mut ol = vec![0.0; n];
    if n > 0 {
        // with the GIL held, as the elementwise functions: the slices borrow the input arrays
        simd::dispatch(Horner {
            n,
            c: (chs, cls),
            a,
            out: (&mut oh, &mut ol),
        });
    }
    Ok((oh.into_pyarray(py), ol.into_pyarray(py)))
}

/// the SIMD backend the elementwise functions run on (avx512, avx2, sse2, neon or portable), detected at run time
#[pyfunction]
fn isa() -> &'static str {
    simd::isa()
}

#[pymodule]
fn _multidouble(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(dd_op, m)?)?;
    m.add_function(wrap_pyfunction!(add, m)?)?;
    m.add_function(wrap_pyfunction!(sub, m)?)?;
    m.add_function(wrap_pyfunction!(mul, m)?)?;
    m.add_function(wrap_pyfunction!(div, m)?)?;
    m.add_function(wrap_pyfunction!(dd_dot, m)?)?;
    m.add_function(wrap_pyfunction!(dd_matvec, m)?)?;
    m.add_function(wrap_pyfunction!(dd_horner, m)?)?;
    m.add_function(wrap_pyfunction!(dd_solve, m)?)?;
    m.add_function(wrap_pyfunction!(qd_solve, m)?)?;
    m.add_class::<PyQdLu>()?;
    m.add_function(wrap_pyfunction!(qd_add_dd, m)?)?;
    m.add_function(wrap_pyfunction!(qd_axpy, m)?)?;
    m.add_function(wrap_pyfunction!(isa, m)?)?;
    octo::register(m)?;
    Ok(())
}
