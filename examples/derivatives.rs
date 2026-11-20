//! The derivative of f(x) = (x⁵ - 3x + 1) / (x² + 2) at x = 0.7 (the f64 nearest), by central differences
//! (f(x + h) - f(x - h)) / 2h with h = 2⁻ᵏ in f64, double-double, quad-double and octo-double, and by the dual numbers
//! `Fu`, `Du`, `Qu` and `Ou`, which carry the derivative through the same operations. Prints the run's settings, then
//! one JSON object per step and one for the duals, each estimate as its parts, the input of
//! `scripts/derivative_graph.py`, which measures them against the exact derivative:
//!
//! ```sh
//! cargo run --release --example derivatives > docs/derivatives.jsonl
//! ```

use std::ops::{Add, Div, Mul, Sub};

use multidouble::dd::DD;
use multidouble::dual::{Du, Fu, Ou, Qu};
use multidouble::dv::DV;
use multidouble::od::OD;
use multidouble::ov::OV;
use multidouble::qd::QD;
use multidouble::qv::QV;
use multidouble::simd::Native;
use multidouble::v8::V8;

/// the point, 0.7 rounded to f64, exact in every type
const X: f64 = 0.7;
/// the steps 2⁻ᵏ for k = 0, STEP, ..., KMAX
const KMAX: i32 = 280;
const STEP: usize = 2;

/// the arithmetic f needs, and its integer constants
trait Num: Copy + Add<Output = Self> + Sub<Output = Self> + Mul<Output = Self> + Div<Output = Self> {
    fn c(v: f64) -> Self;
}

impl Num for f64 {
    fn c(v: f64) -> Self {
        v
    }
}

impl Num for DD {
    fn c(v: f64) -> Self {
        DD::from_f64(v)
    }
}

impl Num for QD {
    fn c(v: f64) -> Self {
        QD::from_f64(v)
    }
}

impl Num for OD {
    fn c(v: f64) -> Self {
        OD::from_f64(v)
    }
}

impl Num for Fu<Native> {
    fn c(v: f64) -> Self {
        Fu {
            v: V8::splat(v),
            d: V8::zero(),
        }
    }
}

impl Num for Du<Native> {
    fn c(v: f64) -> Self {
        Du {
            v: DV::splat(DD::from_f64(v)),
            d: DV::splat(DD::ZERO),
        }
    }
}

impl Num for Qu<Native> {
    fn c(v: f64) -> Self {
        Qu {
            v: QV::splat(QD::from_f64(v)),
            d: QV::splat(QD::ZERO),
        }
    }
}

impl Num for Ou<Native> {
    fn c(v: f64) -> Self {
        Ou {
            v: OV::splat(OD::from_f64(v)),
            d: OV::splat(OD::ZERO),
        }
    }
}

/// (x⁵ - 3x + 1) / (x² + 2)
fn f<T: Num>(x: T) -> T {
    let x2 = x * x;
    (x2 * x2 * x - T::c(3.0) * x + T::c(1.0)) / (x2 + T::c(2.0))
}

/// the central difference with step 2⁻ᵏ, x ± h formed in T
fn central<T: Num>(k: i32) -> T {
    let (x, h) = (T::c(X), T::c(2f64.powi(-k)));
    (f(x + h) - f(x - h)) * T::c(2f64.powi(k - 1))
}

/// parts as a JSON array, each printed so that it reads back exactly
fn parts(p: &[f64]) -> String {
    let s: Vec<String> = p.iter().map(|v| format!("{v:e}")).collect();
    format!("[{}]", s.join(", "))
}

fn main() {
    println!(
        r#"{{"x": {X:e}, "kmax": {KMAX}, "version": "{}"}}"#,
        env!("CARGO_PKG_VERSION")
    );
    for k in (0..=KMAX).step_by(STEP) {
        let (dd, qd, od) = (central::<DD>(k), central::<QD>(k), central::<OD>(k));
        println!(
            r#"{{"k": {k}, "f64": {}, "dd": {}, "qd": {}, "od": {}}}"#,
            parts(&[central::<f64>(k)]),
            parts(&[dd.hi, dd.lo]),
            parts(&qd.x),
            parts(&od.x)
        );
    }
    // the duals: the variable x with tangent 1, the derivative in lane 0 of the result's tangent
    let fu = f(Fu::<Native> {
        v: V8::splat(X),
        d: V8::splat(1.0),
    });
    let du = f(Du::<Native> {
        v: DV::splat(DD::from_f64(X)),
        d: DV::splat(DD::ONE),
    });
    let qu = f(Qu::<Native> {
        v: QV::splat(QD::from_f64(X)),
        d: QV::splat(QD::ONE),
    });
    let ou = f(Ou::<Native> {
        v: OV::splat(OD::from_f64(X)),
        d: OV::splat(OD::ONE),
    });
    let d = du.d.lane(0);
    println!(
        r#"{{"dual": true, "f64": {}, "dd": {}, "qd": {}, "od": {}}}"#,
        parts(&[fu.d.to_array()[0]]),
        parts(&[d.hi, d.lo]),
        parts(&qu.d.lane(0).x),
        parts(&ou.d.lane(0).x)
    );
}
