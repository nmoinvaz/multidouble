//! Python bindings of multidouble: double-double numbers as pairs of float64 numpy arrays (hi, lo), elementwise
//! arithmetic, dot products and matrix-vector products on them on the best SIMD backend the CPU has, quad-double
//! arrays (four parts) plus a double-double one or plus a multiple of another, and a dense double-double LU solve.
use multidouble::dd::DD;
use multidouble::dv::{DotAcc, DV};
use multidouble::linalg::{ld_for, DDLu};
use multidouble::qd::QD;
use multidouble::qv::{axpy_parts, renorm4, QV};
use multidouble::simd::{self, Kernel, Simd};
use numpy::{IntoPyArray, PyArray1, PyReadonlyArray1, PyReadonlyArray2, PyUntypedArrayMethods};

type Parts<'py> = (
    Bound<'py, PyArray1<f64>>,
    Bound<'py, PyArray1<f64>>,
    Bound<'py, PyArray1<f64>>,
    Bound<'py, PyArray1<f64>>,
);
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;

type Pair<'py> = (Bound<'py, PyArray1<f64>>, Bound<'py, PyArray1<f64>>);

const ADD: u8 = 0;
const MUL: u8 = 1;
const DIV: u8 = 2;
const SUB: u8 = 3;

fn slice<'a>(a: &'a PyReadonlyArray1<f64>, name: &str) -> PyResult<&'a [f64]> {
    a.as_slice()
        .map_err(|_| PyValueError::new_err(format!("{name} must be a contiguous float64 array")))
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
    let ahs = ah
        .as_slice()
        .map_err(|_| PyValueError::new_err("ah must be C-contiguous"))?;
    let als = al
        .as_slice()
        .map_err(|_| PyValueError::new_err("al must be C-contiguous"))?;
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
    let ahs = ah
        .as_slice()
        .map_err(|_| PyValueError::new_err("ah must be C-contiguous"))?;
    let als = al
        .as_slice()
        .map_err(|_| PyValueError::new_err("al must be C-contiguous"))?;
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
    m.add_function(wrap_pyfunction!(dd_solve, m)?)?;
    m.add_function(wrap_pyfunction!(qd_add_dd, m)?)?;
    m.add_function(wrap_pyfunction!(qd_axpy, m)?)?;
    m.add_function(wrap_pyfunction!(isa, m)?)?;
    Ok(())
}
