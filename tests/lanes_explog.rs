//! `exp` and `ln` of the 8-lane types `DV`, `QV` and `OV` against the scalar functions of `DD`, `QD` and `OD`, bit for
//! bit in every lane, on every backend this CPU runs. A NaN that arithmetic makes matches any NaN, as in
//! tests/lanes.rs, since Rust leaves its sign and payload unspecified; the special values' results, a NaN x_0's exp
//! (x_0 itself) and ln's NaN among them, are made without arithmetic and must match bit for bit. Most vectors mix
//! kinds of argument, so that their lanes take different reductions k, squaring counts, Taylor degrees, branches of ln
//! and special values in one call; every fourth takes one kind in all lanes. The kinds: for exp, random over the range,
//! near 0 (subnormal included), near k ln 2 and (k + 1/2) ln 2, within 3 ulps of ln f64::MAX with tails near half an
//! ulp, near underflow, subnormal, moderate, and the special values with NaN payloads; for ln, random over the range,
//! near 1, near sqrt(2) 2^k, subnormal, within 3 ulps of f64::MAX with tails near half an ulp (the start's x/2 branch),
//! powers of 2, moderate, and the special values. Lower parts are absent, on the ladder with gaps, or at the top of the
//! ladder. Every eighth vector checks each lane's own powers of two in the exact scalings: lane 0 takes e^0 or ln 1,
//! which scale by 1, and the other lanes take arguments whose results' last parts lie near the bottom of the range,
//! where a scaling by another lane's power of two changes them (exp of one part near 2^-197, ln of 1 and one or two
//! parts near 2^-330).
//!
//! Control (feature `mutate`): with `explog::mutate::LANE_STEP`, each lane skipping the first step of its Horner sum,
//! the check fails for every type and function; with `LANE_POW2_POLY`, `LANE_POW2_FT` and `LANE_POW2_SERIES`, every
//! lane taking lane 0's powers of two in one scaling, the octo-double check fails for the function that scales (the
//! double-double and quad-double results end above the subnormals, so a wrong power of two cannot show there); with
//! each of the scalar functions' mutations, which the lanes share, it still passes.
//!
//! ```text
//! cargo test --release --test lanes_explog
//! cargo test --release --test lanes_explog --features mutate
//! ```
#![allow(clippy::needless_range_loop)]
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::dv::DV;
use multidouble::od::OD;
use multidouble::ov::OV;
use multidouble::qd::QD;
use multidouble::qv::QV;
use multidouble::simd::{self, Kernel, Simd};

/// vectors per function in a release build: double-double, quad-double, octo-double (a debug build runs an eighth)
const COUNT: [usize; 3] = [16000, 8000, 2400];

fn same(a: f64, b: f64) -> bool {
    a.to_bits() == b.to_bits() || (a.is_nan() && b.is_nan())
}

/// 2^e for -1074 <= e <= 1023, from its bits
fn pow2i(e: i32) -> f64 {
    if e >= -1022 {
        f64::from_bits(((e + 1023) as u64) << 52)
    } else {
        f64::from_bits(1 << (e + 1074))
    }
}

/// the gap below |h| to the next f64, for an |h| that is not a power of two
fn ulp(h: f64) -> f64 {
    h.abs() - f64::from_bits(h.abs().to_bits() - 1)
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum F {
    Exp,
    Ln,
}

/// the kinds of argument of each function drawn at random; the last is the special values
const KINDS: u64 = 9;
const SPECIAL: u64 = KINDS - 1;
/// lane 0 of the scaling vectors: e^0 or ln 1, whose powers of two in the scalings are 1
const COMPANION: u64 = KINDS;
/// the other lanes of the scaling vectors (see the module doc)
const SCALING: u64 = KINDS + 1;

/// exp's special values and range ends
const EXP_SPECIAL: [f64; 13] = [
    f64::NAN,
    f64::from_bits(0x7ff8_0000_0000_1234),
    f64::from_bits(0xfff8_0000_0000_0001),
    f64::INFINITY,
    f64::NEG_INFINITY,
    0.0,
    -0.0,
    709.8,
    -745.3,
    709.79,
    -745.2,
    f64::MAX,
    -f64::MAX,
];
/// ln's special values, and 1
const LN_SPECIAL: [f64; 11] = [
    f64::NAN,
    f64::from_bits(0x7ff8_0000_0000_1234),
    f64::from_bits(0xfff8_0000_0000_0001),
    -1.0,
    -0.0,
    0.0,
    f64::INFINITY,
    f64::NEG_INFINITY,
    -f64::from_bits(1),
    -f64::MAX,
    1.0,
];

/// one value's n parts of kind `kind` (see the module doc)
fn arg(r: &mut Rng, f: F, kind: u64, n: usize) -> [f64; 8] {
    let mut p = [0.0; 8];
    let sign = |r: &mut Rng| if r.next_u64() & 1 == 0 { 1.0 } else { -1.0 };
    // a leading part near the top of the range, with a second part near half its ulp
    let edge = |r: &mut Rng, x0: f64, p: &mut [f64; 8]| {
        p[0] = f64::from_bits(x0.to_bits() - r.next_u64() % 4);
        p[1] = ulp(p[0]) / 2.0
            * match r.next_u64() % 3 {
                0 => -1.0,
                1 => 1.0 - r.unit() * pow2i(-40),
                _ => 1.0,
            };
        if n > 2 && r.next_u64() & 1 == 0 {
            p[2] = r.sym() * ulp(p[0]) * pow2i(-60 - (r.next_u64() % 40) as i32);
        }
    };
    let x0 = match (f, kind) {
        (_, SPECIAL) => {
            let s = if f == F::Exp { &EXP_SPECIAL[..] } else { &LN_SPECIAL[..] };
            p[0] = s[(r.next_u64() % s.len() as u64) as usize];
            return p;
        }
        (F::Exp, COMPANION) => return p,
        (F::Ln, COMPANION) => {
            p[0] = 1.0;
            return p;
        }
        (F::Exp, SCALING) => {
            // 1 + x + x^2/2 + ... in eight parts ends near 2^-1022
            p[0] = sign(r) * (1.0 + r.unit()) * pow2i(-195 - (r.next_u64() % 4) as i32);
            return p;
        }
        (F::Ln, SCALING) => {
            // ln(1 + e) = e - e^2/2 + ... has parts near 2^-330 k, so its later parts are subnormal
            let e = -320 - (r.next_u64() % 22) as i32;
            (p[0], p[1]) = (1.0, sign(r) * (1.0 + r.unit()) * pow2i(e));
            if r.next_u64() & 1 == 0 {
                p[2] = sign(r) * (1.0 + r.unit()) * pow2i(e - 53 - (r.next_u64() % 30) as i32);
            }
            return p;
        }
        (F::Exp, 0) => -745.0 + 1455.0 * r.unit(),
        (F::Exp, 1) => sign(r) * (1.0 + r.unit()) * pow2i(-((r.next_u64() % 1075) as i32)),
        (F::Exp, 2 | 3) => {
            let k = (r.next_u64() % 2048) as f64 - 1075.0 + 0.5 * (kind - 2) as f64;
            k * std::f64::consts::LN_2 * (1.0 + r.sym() * pow2i(-30 - (r.next_u64() % 23) as i32))
        }
        (F::Exp, 4) => {
            edge(r, f64::from_bits(709.782712893384f64.to_bits() + 2), &mut p);
            return p;
        }
        (F::Exp, 5) => -708.0 - 37.5 * r.unit(),
        (F::Exp, 6) => sign(r) * f64::from_bits(1 + r.next_u64() % (1 << 52)),
        (F::Exp, _) => r.sym() * pow2i(3 - (r.next_u64() % 16) as i32),
        (F::Ln, 0) => (1.0 + r.unit()) * pow2i((r.next_u64() % 2045) as i32 - 1022),
        (F::Ln, 1) => {
            // 1 itself in a quarter, with the lower parts alone
            let d = r.sym() * pow2i(-((r.next_u64() % 60) as i32) - 1);
            1.0 + if r.next_u64().is_multiple_of(4) { 0.0 } else { d }
        }
        (F::Ln, 2) => {
            let k = (r.next_u64() % 2000) as i32 - 1000;
            std::f64::consts::SQRT_2 * pow2i(k) * (1.0 + r.sym() * pow2i(-40))
        }
        (F::Ln, 3) => f64::from_bits(1 + r.next_u64() % (1 << 52)),
        (F::Ln, 4) => {
            edge(r, f64::MAX, &mut p);
            return p;
        }
        (F::Ln, 5) => {
            p[0] = pow2i((r.next_u64() % 2098) as i32 - 1074);
            return p;
        }
        (F::Ln, _) => (r.sym() * 30.0).exp(),
    };
    p[0] = x0;
    if x0.abs() < pow2i(-900) {
        return p;
    }
    match r.next_u64() % 4 {
        // no lower parts
        0 => {}
        // at the top of the ladder, |x_i| in ((2u)^i / 2, (2u)^i] |x_0|, overlapping by a bit
        1 if n > 2 => {
            for i in 1..n {
                p[i] = sign(r) * (0.5 + 0.5 * r.unit()) * x0.abs() * pow2i(-52 * i as i32);
            }
        }
        // on the ladder with gaps
        _ => {
            for i in 1..n {
                if r.next_u64().is_multiple_of(3) {
                    continue;
                }
                p[i] = r.sym() * x0.abs() * pow2i(-53 * i as i32 - (r.next_u64() % 60) as i32);
            }
        }
    }
    if n == 2 {
        // a double-word
        let d = DD::new(p[0], p[1]);
        (p[0], p[1]) = (d.hi, d.lo);
    }
    p
}

/// count vectors of n parts for f, each lane's kind with it; all scaling vectors if `scaling`
fn vectors(r: &mut Rng, f: F, n: usize, count: usize, scaling: bool) -> Vec<([[f64; 8]; 8], [u64; 8])> {
    (0..count)
        .map(|i| {
            let k0 = r.next_u64() % KINDS;
            let kinds: [u64; 8] = std::array::from_fn(|j| match (scaling || i % 8 == 5, j) {
                (true, 0) => COMPANION,
                (true, _) => SCALING,
                _ if i % 4 == 3 => k0,
                _ => r.next_u64() % KINDS,
            });
            (std::array::from_fn(|j| arg(r, f, kinds[j], n)), kinds)
        })
        .collect()
}

/// a lane type with its scalar functions, through the lanes' parts
trait Lanes<S: Simd>: Copy {
    const NAME: &'static str;
    /// parts per value
    const N: usize;
    /// index into COUNT
    const IX: usize;
    fn load(x: &[[f64; 8]; 8]) -> Self;
    fn parts(self) -> [[f64; 8]; 8];
    fn exp(self) -> Self;
    fn ln(self) -> Self;
    /// the scalar function f of one value's parts
    fn scalar(f: F, x: &[f64; 8]) -> [f64; 8];
}

impl<S: Simd> Lanes<S> for DV<S> {
    const NAME: &'static str = "dv";
    const N: usize = 2;
    const IX: usize = 0;
    fn load(x: &[[f64; 8]; 8]) -> Self {
        let (hi, lo): (Vec<f64>, Vec<f64>) = x.iter().map(|p| (p[0], p[1])).unzip();
        DV::load(&hi, &lo)
    }
    fn parts(self) -> [[f64; 8]; 8] {
        let (hi, lo) = (self.hi.to_array(), self.lo.to_array());
        std::array::from_fn(|j| [hi[j], lo[j], 0.0, 0.0, 0.0, 0.0, 0.0, 0.0])
    }
    fn exp(self) -> Self {
        DV::exp(self)
    }
    fn ln(self) -> Self {
        DV::ln(self)
    }
    fn scalar(f: F, x: &[f64; 8]) -> [f64; 8] {
        let x = DD { hi: x[0], lo: x[1] };
        let y = if f == F::Exp { x.exp() } else { x.ln() };
        [y.hi, y.lo, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]
    }
}

impl<S: Simd> Lanes<S> for QV<S> {
    const NAME: &'static str = "qv";
    const N: usize = 4;
    const IX: usize = 1;
    fn load(x: &[[f64; 8]; 8]) -> Self {
        QV::from_lanes(&std::array::from_fn(|j| QD {
            x: [x[j][0], x[j][1], x[j][2], x[j][3]],
        }))
    }
    fn parts(self) -> [[f64; 8]; 8] {
        self.lanes()
            .map(|q| [q.x[0], q.x[1], q.x[2], q.x[3], 0.0, 0.0, 0.0, 0.0])
    }
    fn exp(self) -> Self {
        QV::exp(self)
    }
    fn ln(self) -> Self {
        QV::ln(self)
    }
    fn scalar(f: F, x: &[f64; 8]) -> [f64; 8] {
        let x = QD {
            x: [x[0], x[1], x[2], x[3]],
        };
        let y = if f == F::Exp { x.exp() } else { x.ln() };
        [y.x[0], y.x[1], y.x[2], y.x[3], 0.0, 0.0, 0.0, 0.0]
    }
}

impl<S: Simd> Lanes<S> for OV<S> {
    const NAME: &'static str = "ov";
    const N: usize = 8;
    const IX: usize = 2;
    fn load(x: &[[f64; 8]; 8]) -> Self {
        OV::from_lanes(&std::array::from_fn(|j| OD { x: x[j] }))
    }
    fn parts(self) -> [[f64; 8]; 8] {
        self.lanes().map(|o| o.x)
    }
    fn exp(self) -> Self {
        OV::exp(self)
    }
    fn ln(self) -> Self {
        OV::ln(self)
    }
    fn scalar(f: F, x: &[f64; 8]) -> [f64; 8] {
        let x = OD { x: *x };
        (if f == F::Exp { x.exp() } else { x.ln() }).x
    }
}

/// one type and function on one backend
#[derive(Debug)]
struct Row {
    what: String,
    lanes: usize,
    /// lanes that differ from the scalar function
    misses: usize,
    /// vectors with special and other lanes
    mixed: usize,
    first: Vec<String>,
}

/// V's exp and ln against the scalar functions, on COUNT[V::IX] / div vectors each, all scaling vectors if `scaling`
fn rows<S: Simd, V: Lanes<S>>(div: usize, scaling: bool) -> Vec<Row> {
    let div = if cfg!(debug_assertions) { 8 * div } else { div };
    let mut out = Vec::new();
    for (s, f) in [F::Exp, F::Ln].into_iter().enumerate() {
        let mut r = Rng(100 + 10 * V::IX as u64 + s as u64);
        let mut row = Row {
            what: format!("{} {f:?}", V::NAME),
            lanes: 0,
            misses: 0,
            mixed: 0,
            first: Vec::new(),
        };
        for (x, kinds) in vectors(&mut r, f, V::N, (COUNT[V::IX] / div).max(8), scaling) {
            let v = V::load(&x);
            let y = if f == F::Exp { v.exp() } else { v.ln() }.parts();
            let special = kinds.iter().filter(|&&k| k == SPECIAL).count();
            row.mixed += (special > 0 && special < 8) as usize;
            for j in 0..8 {
                let want = V::scalar(f, &x[j]);
                row.lanes += 1;
                // a special value's result is made without arithmetic, so a NaN there has defined bits too
                let strict = kinds[j] == SPECIAL;
                if !(0..V::N).all(|i| same(y[j][i], want[i]) && (!strict || y[j][i].to_bits() == want[i].to_bits())) {
                    row.misses += 1;
                    if row.first.len() < 3 {
                        row.first.push(format!(
                            "lane {j} kind {} of {kinds:?}: x {:?} lanes {:?} scalar {:?}",
                            kinds[j],
                            &x[j][..V::N],
                            &y[j][..V::N],
                            &want[..V::N]
                        ));
                    }
                }
            }
        }
        out.push(row);
    }
    out
}

/// the three types' rows on one backend, each type on 1/div of its vectors, all scaling vectors if `scaling`
#[derive(Clone)]
struct LanesVsScalar {
    div: usize,
    scaling: bool,
}

impl Kernel for LanesVsScalar {
    type Output = Vec<Row>;
    #[inline(always)]
    fn run<S: Simd>(self) -> Vec<Row> {
        let mut rows_ = rows::<S, DV<S>>(self.div, self.scaling);
        rows_.extend(rows::<S, QV<S>>(self.div, self.scaling));
        rows_.extend(rows::<S, OV<S>>(self.div, self.scaling));
        rows_
    }
}

/// every backend's rows, each named with its backend
fn every_backend(div: usize, scaling: bool) -> Vec<(&'static str, Row)> {
    let ran = simd::for_each_available(LanesVsScalar { div, scaling });
    assert_eq!(ran.iter().map(|r| r.0).collect::<Vec<_>>(), simd::available());
    ran.into_iter()
        .flat_map(|(isa, rows)| rows.into_iter().map(move |r| (isa, r)))
        .collect()
}

#[test]
fn lanes_match_scalar_bit_for_bit() {
    common::big_stack(|| {
        let rows = every_backend(1, false);
        for (isa, r) in &rows {
            println!(
                "{isa:<8} {:<7} {:>6} lanes, {:>5} vectors mixing special and other lanes, {} differ",
                r.what, r.lanes, r.mixed, r.misses
            );
        }
        let bad: Vec<_> = rows.iter().filter(|(_, r)| r.misses > 0).collect();
        assert!(bad.is_empty(), "{bad:#?}");
        // a fair share of the vectors mixes special values with other lanes in one call
        assert!(rows.iter().all(|(_, r)| r.mixed * 4 >= r.lanes / 8), "{rows:#?}");
    });
}

/// The controls (feature `mutate`): the lanes' own breaks fail the check on every backend, the skipped Horner step for
/// every type and function and lane 0's powers of two for the octo-double function that scales, and the scalar
/// functions' breaks, which the lanes take alike, leave it passing.
#[cfg(feature = "mutate")]
#[test]
fn control_fires() {
    common::big_stack(|| {
        use multidouble::explog::mutate;
        for id in 1..=mutate::N {
            mutate::set(id);
            let rows = every_backend(4, false);
            mutate::set(0);
            let bad: Vec<_> = rows.iter().filter(|(_, r)| r.misses > 0).collect();
            assert!(bad.is_empty(), "under '{}': {bad:#?}", mutate::NAMES[id as usize]);
        }
        mutate::set(mutate::LANE_STEP);
        let rows = every_backend(4, false);
        mutate::set(0);
        for (isa, r) in &rows {
            println!(
                "control '{}': {isa:<8} {:<7} {} of {} lanes differ",
                mutate::NAMES[mutate::LANE_STEP as usize],
                r.what,
                r.misses,
                r.lanes
            );
        }
        let silent: Vec<_> = rows.iter().filter(|(_, r)| r.misses == 0).collect();
        assert!(silent.is_empty(), "the control did not fire: {silent:#?}");
        for (id, row) in [
            (mutate::LANE_POW2_POLY, "ov Exp"),
            (mutate::LANE_POW2_FT, "ov Ln"),
            (mutate::LANE_POW2_SERIES, "ov Ln"),
        ] {
            mutate::set(id);
            let rows = every_backend(4, true);
            mutate::set(0);
            let fired: Vec<_> = rows.iter().filter(|(_, r)| r.what == row).collect();
            assert_eq!(fired.len(), simd::available().len());
            for (isa, r) in &fired {
                println!(
                    "control '{}': {isa:<8} {:<7} {} of {} lanes differ",
                    mutate::NAMES[id as usize],
                    r.what,
                    r.misses,
                    r.lanes
                );
            }
            let silent: Vec<_> = fired.iter().filter(|(_, r)| r.misses == 0).collect();
            assert!(silent.is_empty(), "the control did not fire: {silent:#?}");
        }
    });
}
