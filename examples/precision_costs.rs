//! Time per value of add, multiply and divide in each precision, f64, double-double, quad-double and octo-double, on
//! the scalar types and on their 8-lane twins on `simd::Native`, over the same inputs. Each row is the fastest of
//! `RUNS` passes over `N` values, scalar and lane passes alternating so that both see the same load. Prints the run's
//! settings, then one JSON object per row, the input of `scripts/cost_graph.py`:
//!
//! ```sh
//! cargo run --release --example precision_costs > docs/precision-costs.jsonl
//! ```

use std::hint::black_box;
use std::ops::{Add, Div, Mul};
use std::time::Instant;

use multidouble::dd::DD;
use multidouble::dv::DV;
use multidouble::od::OD;
use multidouble::ov::OV;
use multidouble::qd::QD;
use multidouble::qv::QV;
use multidouble::simd::Native;
use multidouble::v8::V8;

const N: usize = 4096;
const RUNS: usize = 101;
/// 2^-53
const U: f64 = 1.0 / 9007199254740992.0;

/// xorshift64
struct Rng(u64);

impl Rng {
    fn u(&mut self) -> f64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 >> 11) as f64 / (1u64 << 53) as f64
    }
    fn s(&mut self) -> f64 {
        2.0 * self.u() - 1.0
    }
}

/// ns per value of one pass
fn pass<F: FnMut() -> f64>(f: &mut F) -> f64 {
    let t = Instant::now();
    black_box(f());
    t.elapsed().as_nanos() as f64 / N as f64
}

/// the fastest of `RUNS` passes of each, scalar and lanes alternating
fn time2<F: FnMut() -> f64, G: FnMut() -> f64>(mut f: F, mut g: G) -> (f64, f64) {
    let (mut a, mut b) = (f64::INFINITY, f64::INFINITY);
    for _ in 0..RUNS {
        a = a.min(pass(&mut f));
        b = b.min(pass(&mut g));
    }
    (a, b)
}

/// the parts of n values in [1, 2) with random lower parts, each at most 2⁻⁵³ of the part above, as arrays of parts
fn inputs(parts: usize, r: &mut Rng) -> Vec<Vec<f64>> {
    let mut c = vec![Vec::with_capacity(N); parts];
    for _ in 0..N {
        let mut p = 1.0 + r.u();
        for q in c.iter_mut() {
            q.push(p);
            p *= U * r.s();
        }
    }
    c
}

/// one precision: the scalar and lane operands from the parts, then add, multiply and divide timed on both
macro_rules! precision {
    ($name:literal, $parts:expr, $scalar:expr, $lanes:expr, $first:expr, $vfirst:expr) => {{
        let mut r = Rng(0x2545_f491_4f6c_dd1d);
        let (ca, cb) = (inputs($parts, &mut r), inputs($parts, &mut r));
        let (xa, xb) = ($scalar(&ca), $scalar(&cb));
        let (va, vb) = ($lanes(&ca), $lanes(&cb));
        for op in ["add", "mul", "div"] {
            let (s, l) = time2(
                || {
                    let mut acc = 0.0;
                    for (&a, &b) in xa.iter().zip(&xb) {
                        let (a, b) = (black_box(a), black_box(b));
                        // the whole result kept, so that no part of it can be left uncomputed
                        acc += $first(black_box(match op {
                            "add" => a.add(b),
                            "mul" => a.mul(b),
                            _ => a.div(b),
                        }));
                    }
                    acc
                },
                || {
                    let mut acc = 0.0;
                    for (&a, &b) in va.iter().zip(&vb) {
                        let (a, b) = (black_box(a), black_box(b));
                        // every lane and part kept, so that none can be left uncomputed
                        acc += $vfirst(black_box(match op {
                            "add" => a.add(b),
                            "mul" => a.mul(b),
                            _ => a.div(b),
                        }));
                    }
                    acc
                },
            );
            println!(
                r#"{{"type": "{}", "op": "{op}", "scalar_ns": {s:.3}, "lanes_ns": {l:.3}}}"#,
                $name
            );
        }
    }};
}

/// today's UTC date as yyyy-mm-dd, from the days since 1970-01-01 (Hinnant's civil_from_days)
fn utc_date() -> String {
    let secs = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_secs());
    let z = (secs / 86400) as i64 + 719468;
    let era = z.div_euclid(146097);
    let doe = z - era * 146097;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = yoe + era * 400 + i64::from(m <= 2);
    format!("{y:04}-{m:02}-{d:02}")
}

/// the machine the timings run on, for the graph's footnote: the CPU's name (sysctl on macOS, /proc/cpuinfo on Linux)
/// and the OS, the OS alone where the CPU's name cannot be read
fn machine() -> String {
    let cpu = if cfg!(target_os = "macos") {
        std::process::Command::new("sysctl")
            .args(["-n", "machdep.cpu.brand_string"])
            .output()
            .ok()
            .and_then(|o| String::from_utf8(o.stdout).ok())
    } else {
        std::fs::read_to_string("/proc/cpuinfo").ok().and_then(|s| {
            s.lines()
                .find(|l| l.starts_with("model name"))
                .and_then(|l| l.split_once(':'))
                .map(|(_, v)| v.to_string())
        })
    };
    let os = match std::env::consts::OS {
        "macos" => "macOS",
        "linux" => "Linux",
        "windows" => "Windows",
        other => other,
    };
    // the name goes into a JSON string, so without quotes or backslashes
    match cpu.map(|c| c.trim().replace(['"', '\\'], "")) {
        Some(c) if !c.is_empty() => format!("{c}, {os}"),
        _ => os.to_string(),
    }
}

fn main() {
    // the run's settings first, for the graph's subtitle and footnote: a commit hash would not survive a rebase merge,
    // so the crate's version and the date name what was measured, the backend is Native's, fixed at build time, and
    // the machine is the one the timings ran on
    println!(
        r#"{{"isa": "{}", "values": {N}, "runs": {RUNS}, "version": "{}", "date": "{}", "machine": "{}"}}"#,
        V8::<Native>::ISA,
        env!("CARGO_PKG_VERSION"),
        utc_date(),
        machine()
    );
    precision!(
        "f64",
        1,
        |c: &[Vec<f64>]| c[0].clone(),
        |c: &[Vec<f64>]| c[0]
            .as_chunks::<8>()
            .0
            .iter()
            .map(|w| V8::<Native>::load(w))
            .collect::<Vec<_>>(),
        |y: f64| y,
        |v: V8<Native>| v.to_array()[0]
    );
    precision!(
        "double-double",
        2,
        |c: &[Vec<f64>]| c[0].iter().zip(&c[1]).map(|(&h, &l)| DD::new(h, l)).collect::<Vec<_>>(),
        |c: &[Vec<f64>]| (0..N / 8)
            .map(|k| DV::<Native>::load(&c[0][8 * k..], &c[1][8 * k..]))
            .collect::<Vec<_>>(),
        |y: DD| y.hi,
        |v: DV<Native>| v.lane(0).hi
    );
    precision!(
        "quad-double",
        4,
        |c: &[Vec<f64>]| (0..N)
            .map(|i| QD::new(c[0][i], c[1][i], c[2][i], c[3][i]))
            .collect::<Vec<_>>(),
        |c: &[Vec<f64>]| {
            (0..N / 8)
                .map(|k| QV::<Native>::load(&c[0][8 * k..], &c[1][8 * k..], &c[2][8 * k..], &c[3][8 * k..]))
                .collect::<Vec<_>>()
        },
        |y: QD| y.x[0],
        |v: QV<Native>| v.lane(0).x[0]
    );
    precision!(
        "octo-double",
        8,
        |c: &[Vec<f64>]| (0..N)
            .map(|i| OD::new(std::array::from_fn(|q| c[q][i])))
            .collect::<Vec<_>>(),
        |c: &[Vec<f64>]| {
            (0..N / 8)
                .map(|k| OV::<Native>::load(std::array::from_fn(|q| &c[q][8 * k..])))
                .collect::<Vec<_>>()
        },
        |y: OD| y.x[0],
        |v: OV<Native>| v.lane(0).x[0]
    );
}
