//! Python bindings of multidouble: double-double numbers as pairs of float64 numpy arrays (hi, lo), elementwise
//! arithmetic on them on the best SIMD backend the CPU has, and a dense double-double LU solve.
use multidouble::dd::DD;
use multidouble::dv::DV;
use multidouble::linalg::{ld_for, DDLu};
use multidouble::simd::{self, Kernel, Simd};
use numpy::{IntoPyArray, PyArray1, PyReadonlyArray1, PyReadonlyArray2, PyUntypedArrayMethods};
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
    m.add_function(wrap_pyfunction!(dd_solve, m)?)?;
    m.add_function(wrap_pyfunction!(isa, m)?)?;
    Ok(())
}
