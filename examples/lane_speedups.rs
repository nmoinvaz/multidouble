//! Time per value of each elementary function, the scalar types against their 8-lane twins on `simd::Native`, on the
//! same inputs: exp, ln, and sin, cos, tan and sin_cos for 1/4 <= |x| < 1 and 1 <= |x| < 1024. Each row is the
//! fastest of `RUNS` passes over `N` values, scalar and lane passes alternating so that both see the same load.
//! Prints the run's settings, then one JSON object per row, the input of `scripts/lane_graphs.py`:
//!
//! ```sh
//! cargo run --release --example lane_speedups > docs/lane-speedups.jsonl
//! ```

use std::hint::black_box;
use std::time::Instant;

use multidouble::dd::DD;
use multidouble::dv::DV;
use multidouble::od::OD;
use multidouble::ov::OV;
use multidouble::qd::QD;
use multidouble::qv::QV;
use multidouble::simd::Native;

const N: usize = 1024;
const RUNS: usize = 15;
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

/// the leading parts of the inputs of one argument kind
fn heads(kind: &str, r: &mut Rng) -> Vec<f64> {
    let sign = |r: &mut Rng| if r.u() < 0.5 { 1.0 } else { -1.0 };
    (0..N)
        .map(|_| match kind {
            "exp" => 40.0 * r.u() - 20.0,
            "ln" => 10f64.powf(60.0 * r.u() - 30.0),
            "trig_small" => (0.25 + 0.75 * r.u()) * sign(r),
            _ => (1.0 + 1023.0 * r.u()) * sign(r),
        })
        .collect()
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

/// the argument kinds, the range each names, and the functions timed on it
const KINDS: [(&str, &str, &[&str]); 4] = [
    ("exp", "", &["exp"]),
    ("ln", "", &["ln"]),
    ("trig_small", "1/4 <= |x| < 1", &["sin", "cos", "tan", "sin_cos"]),
    ("trig_big", "1 <= |x| < 1024", &["sin", "cos", "tan", "sin_cos"]),
];

macro_rules! family {
    ($name:literal, $sc:ty, $vt:ty, $make:expr, $pack:expr, $first:expr, $vfirst:expr) => {{
        for (kind, range, funcs) in KINDS {
            let mut r = Rng(0x2545_f491_4f6c_dd1d);
            let xs: Vec<$sc> = heads(kind, &mut r).into_iter().map(|h| $make(h, &mut r)).collect();
            let vs: Vec<$vt> = xs.chunks_exact(8).map($pack).collect();
            for &f in funcs {
                let (s, l) = time2(
                    || {
                        let mut acc = 0.0;
                        for &x in &xs {
                            let x = black_box(x);
                            acc += match f {
                                "exp" => $first(x.exp()),
                                "ln" => $first(x.ln()),
                                "sin" => $first(x.sin()),
                                "cos" => $first(x.cos()),
                                "tan" => $first(x.tan()),
                                _ => $first(x.sin_cos().0),
                            };
                        }
                        acc
                    },
                    || {
                        let mut acc = 0.0;
                        for &v in &vs {
                            let v = black_box(v);
                            acc += match f {
                                "exp" => $vfirst(v.exp()),
                                "ln" => $vfirst(v.ln()),
                                "sin" => $vfirst(v.sin()),
                                "cos" => $vfirst(v.cos()),
                                "tan" => $vfirst(v.tan()),
                                _ => $vfirst(v.sin_cos().0),
                            };
                        }
                        acc
                    },
                );
                println!(
                    r#"{{"type": "{}", "func": "{f}", "range": "{range}", "scalar_ns": {s:.2}, "lanes_ns": {l:.2}}}"#,
                    $name
                );
            }
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

fn main() {
    // the run's settings first, for the graph's subtitle and footnote: a commit hash would not survive a rebase merge,
    // so the crate's version and the date name what was measured
    println!(
        r#"{{"isa": "{}", "values": {N}, "runs": {RUNS}, "version": "{}", "date": "{}"}}"#,
        multidouble::simd::isa(),
        env!("CARGO_PKG_VERSION"),
        utc_date()
    );
    family!(
        "double-double",
        DD,
        DV<Native>,
        |h: f64, r: &mut Rng| DD::new(h, h * U * r.s()),
        |c: &[DD]| {
            let hi: Vec<f64> = c.iter().map(|d| d.hi).collect();
            let lo: Vec<f64> = c.iter().map(|d| d.lo).collect();
            DV::<Native>::load(&hi, &lo)
        },
        |y: DD| y.hi,
        |v: DV<Native>| v.lane(0).hi
    );
    family!(
        "quad-double",
        QD,
        QV<Native>,
        |h: f64, r: &mut Rng| {
            let b = h * U * r.s();
            let c = b * U * r.s();
            QD::new(h, b, c, c * U * r.s())
        },
        |c: &[QD]| QV::<Native>::from_lanes(c.try_into().unwrap()),
        |y: QD| y.x[0],
        |v: QV<Native>| v.lane(0).x[0]
    );
    family!(
        "octo-double",
        OD,
        OV<Native>,
        |h: f64, r: &mut Rng| {
            let mut p = [h; 8];
            for i in 1..8 {
                p[i] = p[i - 1] * U * r.s();
            }
            OD::new(p)
        },
        |c: &[OD]| OV::<Native>::from_lanes(c.try_into().unwrap()),
        |y: OD| y.x[0],
        |v: OV<Native>| v.lane(0).x[0]
    );
}
