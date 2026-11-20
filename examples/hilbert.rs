//! Hilbert systems H x = b, Hᵢⱼ = 1/(i + j + 1), with b the row sums so that x is all ones, solved by LU with partial
//! pivoting in f64, double-double (`DDLu`), quad-double (`QDLu`) and octo-double (`ODLu`) for n = 2 to `NMAX`. H and b
//! are formed in octo-double and rounded to each type, so each solve sees its own type's nearest data. Prints the run's
//! settings, then one JSON object per n with each solve's largest error max |xᵢ - 1| (null where the factorization
//! failed), the input of `scripts/hilbert_graph.py`:
//!
//! ```sh
//! cargo run --release --example hilbert > docs/hilbert.jsonl
//! ```

use multidouble::dd::DD;
use multidouble::linalg::{DDLu, ODLu, QDLu};
use multidouble::od::OD;
use multidouble::qd::QD;

const NMAX: usize = 100;

/// LU with partial pivoting in f64, column-major with leading dimension n, solving in place
fn solve_f64(n: usize, mut a: Vec<f64>, b: &mut [f64]) -> Option<()> {
    for k in 0..n {
        let p = (k..n).max_by(|&i, &j| a[k * n + i].abs().total_cmp(&a[k * n + j].abs()))?;
        if a[k * n + p] == 0.0 {
            return None;
        }
        for j in 0..n {
            a.swap(j * n + k, j * n + p);
        }
        b.swap(k, p);
        for i in k + 1..n {
            let l = a[k * n + i] / a[k * n + k];
            a[k * n + i] = l;
            for j in k + 1..n {
                a[j * n + i] -= l * a[j * n + k];
            }
            b[i] -= l * b[k];
        }
    }
    for k in (0..n).rev() {
        let s: f64 = (k + 1..n).map(|j| a[j * n + k] * b[j]).sum();
        b[k] = (b[k] - s) / a[k * n + k];
    }
    Some(())
}

/// max |xᵢ - 1| in octo-double, each xᵢ given exactly as an octo-double
fn max_err(x: impl Iterator<Item = OD>) -> f64 {
    x.map(|v| (v - OD::ONE).abs().to_f64()).fold(0.0, f64::max)
}

fn json(e: Option<f64>) -> String {
    e.filter(|v| v.is_finite())
        .map_or("null".to_string(), |v| format!("{v:e}"))
}

fn main() {
    println!(r#"{{"nmax": {NMAX}, "version": "{}"}}"#, env!("CARGO_PKG_VERSION"));
    for n in 2..=NMAX {
        let ld = n.div_ceil(8) * 8;
        // H and b in octo-double: entry (i, j) at j * ld + i, padding rows zero
        let mut h = vec![OD::ZERO; ld * n];
        for j in 0..n {
            for i in 0..n {
                h[j * ld + i] = OD::ONE / OD::from_f64((i + j + 1) as f64);
            }
        }
        let b: Vec<OD> = (0..n)
            .map(|i| (0..n).fold(OD::ZERO, |s, j| s + h[j * ld + i]))
            .collect();
        let parts = |q: usize, m: usize| -> Vec<f64> {
            h.iter()
                .map(|v| match m {
                    2 => [v.to_dd().hi, v.to_dd().lo][q],
                    4 => v.to_qd().x[q],
                    _ => v.x[q],
                })
                .collect()
        };

        let e64 = {
            let a: Vec<f64> = (0..n)
                .flat_map(|j| (0..n).map(move |i| (j, i)))
                .map(|(j, i)| h[j * ld + i].to_f64())
                .collect();
            let mut x: Vec<f64> = b.iter().map(|v| v.to_f64()).collect();
            solve_f64(n, a, &mut x).map(|()| max_err(x.into_iter().map(OD::from_f64)))
        };
        let edd = DDLu::factor(n, ld, parts(0, 2), parts(1, 2), false).ok().map(|lu| {
            let mut x: Vec<DD> = b.iter().map(|v| v.to_dd()).collect();
            lu.solve(&mut x);
            max_err(x.into_iter().map(OD::from_dd))
        });
        let eqd = QDLu::factor(n, ld, std::array::from_fn(|q| parts(q, 4)), false)
            .ok()
            .map(|lu| {
                let mut x: Vec<QD> = b.iter().map(|v| v.to_qd()).collect();
                lu.solve(&mut x);
                max_err(x.into_iter().map(OD::from_qd))
            });
        let eod = ODLu::factor(n, ld, std::array::from_fn(|q| parts(q, 8)), false)
            .ok()
            .map(|lu| {
                let mut x = b.clone();
                lu.solve(&mut x);
                max_err(x.into_iter())
            });
        println!(
            r#"{{"n": {n}, "f64": {}, "dd": {}, "qd": {}, "od": {}}}"#,
            json(e64),
            json(edd),
            json(eqd),
            json(eod)
        );
    }
}
