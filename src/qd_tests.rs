//! Tests of the quad-double arithmetic (`qd`, `qv`) against exact dyadic arithmetic (`exact`), which shares no code
//! with the algorithms under test: the inputs are built from exact random values by greedy rounding, not by
//! quad-double arithmetic, and every reference result is exact.
//!
//! ```text
//! cargo test --release --lib qd_                                   accuracy, scalar/8-lane agreement, decimal I/O
//! cargo test --release --lib --features mutate qd_controls      every deliberate breakage must fail a check
//! QD_DUMP=DIR cargo test --release --lib qd_dump -- --ignored      inputs and results for hp/qd_check.py (mpmath)
//! cargo test --release --lib bench_qd -- --ignored --nocapture     throughput per lane: f64, dd, qd
//! cargo test --release --lib qd_diag -- --ignored --nocapture      the two exceedances of the first runs:
//!     QD's accurate add against `QD::ieee_add` by cancellation depth, and the accumulator's error by source
//! ```
//! QD_N sets the samples per operation and input category (default 4000), QD_SEED the seed (default 1), QD_REPORT=1
//! prints the tables. RUSTFLAGS selects the `v8` backend: "-C target-cpu=native" (AVX-512 here), "-C
//! target-feature=+avx2,+fma" (AVX2), none (portable). The digest line of qd_accuracy hashes every scalar result; it
//! is the same on every backend, and the 8-lane results equal the scalar ones bit for bit.
use crate::dd::DD;
use crate::dv::{DotAcc, DV};
use crate::exact::{BigU, Dy};
#[cfg(feature = "mutate")]
use crate::qd::mutate;
use crate::qd::{QdAcc, QD};
use crate::qv::{QDotAcc, QV};
use crate::v8::V8;
use std::cmp::Ordering;

/// 2^-209, the unit of the error tables
fn unit() -> f64 {
    2f64.powi(-209)
}

fn env_usize(k: &str, d: usize) -> usize {
    std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d)
}

fn report() -> bool {
    std::env::var("QD_REPORT").map(|v| v == "1").unwrap_or(false)
}

fn set_mutation(id: u32) {
    #[cfg(feature = "mutate")]
    mutate::set(id);
    #[cfg(not(feature = "mutate"))]
    assert_eq!(id, 0, "mutations need the mutate feature");
}

// -------------------------------------------------------------------------------------------------------------
// random exact inputs
// -------------------------------------------------------------------------------------------------------------

pub(crate) struct Rng(u64);

impl Rng {
    pub(crate) fn new(seed: u64) -> Rng {
        Rng(seed.wrapping_mul(0x2545F4914F6CDD1D) ^ 0x9E3779B97F4A7C15)
    }
    /// splitmix64
    pub(crate) fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    pub(crate) fn int(&mut self, lo: i64, hi: i64) -> i64 {
        lo + (self.next() % ((hi - lo + 1) as u64)) as i64
    }
    fn coin(&mut self) -> bool {
        self.next() & 1 == 1
    }
}

/// exact random value ±(1 + f)·2^e, f a random 255-bit fraction
pub(crate) fn rand_dy(r: &mut Rng, e: i64) -> Dy {
    let m = BigU(vec![r.next(), r.next(), r.next(), r.next() | (1u64 << 63)]);
    Dy {
        neg: r.coin(),
        m,
        e: e - 255,
    }
}

/// rand_dy with the binade drawn from lo..=hi
pub(crate) fn rde(r: &mut Rng, lo: i64, hi: i64) -> Dy {
    let e = r.int(lo, hi);
    rand_dy(r, e)
}

/// sum of 1-4 small integers k_i 2^(e - g_i) with random gaps (exact sums and zero error terms are common)
fn sparse_dy(r: &mut Rng, e: i64) -> Dy {
    let n = r.int(1, 4);
    let mut v = Dy::zero();
    let mut g = 0;
    for i in 0..n {
        let k = r.int(1, 2000) * if r.coin() { 1 } else { -1 };
        if i > 0 {
            g += r.int(0, 120);
        }
        v = v.add(&Dy::from_f64(k as f64).ldexp(e - g));
    }
    if v.is_zero() {
        Dy::from_f64(1.0).ldexp(e)
    } else {
        v
    }
}

/// 2^k (1 + s 2^-j f), j in a set around the part boundaries (j = 0: exactly 2^k)
fn near_pow2(r: &mut Rng, k: i64) -> Dy {
    const J: [i64; 12] = [0, 1, 52, 53, 54, 105, 106, 107, 158, 159, 211, 212];
    let j = if r.coin() {
        J[r.int(0, 11) as usize]
    } else {
        r.int(1, 250)
    };
    let p = Dy::from_f64(1.0).ldexp(k);
    if j == 0 {
        return if r.coin() { p } else { p.neg() };
    }
    let mut d = rand_dy(r, k - j);
    if r.coin() {
        d = d.ldexp(-1);
    }
    let v = p.add(&d);
    if r.coin() {
        v
    } else {
        v.neg()
    }
}

fn qd_of(d: &Dy) -> QD {
    QD { x: d.greedy4() }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Add,
    Mul,
    Sqr,
    Div,
    Sqrt,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Cat {
    Wide,
    Cancel,
    Overflow,
    Underflow,
    Pow2,
    Sparse,
    Computed,
}

const CATS: [Cat; 7] = [
    Cat::Wide,
    Cat::Cancel,
    Cat::Overflow,
    Cat::Underflow,
    Cat::Pow2,
    Cat::Sparse,
    Cat::Computed,
];

fn cat_name(c: Cat) -> &'static str {
    match c {
        Cat::Wide => "wide",
        Cat::Cancel => "cancel",
        Cat::Overflow => "overflow",
        Cat::Underflow => "underflow",
        Cat::Pow2 => "pow2",
        Cat::Sparse => "sparse",
        Cat::Computed => "computed",
    }
}

/// one input pair (a, b) for an operation of the given kind (b unused by sqrt)
fn gen(r: &mut Rng, kind: Kind, cat: Cat) -> (QD, QD) {
    use Cat::*;
    use Kind::*;
    let one = Dy::from_f64(1.0);
    if cat == Computed {
        // operands produced by quad-double arithmetic (QD-renormalized parts, not greedy ones): x y (1/y); for the
        // adds b = -(x y (1/y)) or b = -(a + d) (sloppy add, |d| = 2^-k |a|), so a + b is small with misaligned
        // parts, as in a residual's subtraction of two nearly equal values computed along different routes
        let route = |r: &mut Rng, x: QD| -> QD {
            let y = qd_of(&rde(r, -2, 2));
            (x * y) * (QD::ONE / y)
        };
        let a = qd_of(&rde(r, -20, 20));
        return match kind {
            Add => {
                if r.coin() {
                    (a, -route(r, a))
                } else {
                    let k = r.int(1, 230);
                    let d = qd_of(&rand_dy(r, -k)) * a;
                    (a, -(a + d))
                }
            }
            Sqrt => (route(r, a).abs(), QD::ONE),
            _ => {
                let b = qd_of(&rde(r, -20, 20));
                (route(r, a), route(r, b))
            }
        };
    }
    let (a, b): (Dy, Dy) = match (cat, kind) {
        (Wide, Sqrt) => (rde(r, -800, 800).abs(), one),
        (Wide, Sqr) => (rde(r, -400, 400), one),
        (Wide, _) => (rde(r, -400, 400), rde(r, -400, 400)),
        // a + b small: b = -a + d with |d| = 2^-k |a|
        (Cancel, Add) => {
            let e = r.int(-50, 50);
            let a = rand_dy(r, e);
            let d = rde(r, e - 260, e - 1);
            let b = a.neg().add(&d);
            (a, b)
        }
        // products near 1: (1 + d1)(1 - d2)
        (Cancel, Mul) => {
            let d1 = rde(r, -230, -1).abs();
            let d2 = rde(r, -230, -1).abs();
            (one.add(&d1), one.sub(&d2))
        }
        // quotients near 1: b = a (1 + d)
        (Cancel, Div) => {
            let a = rde(r, -50, 50);
            let d = rde(r, -230, -1);
            let b = a.add(&a.mul(&d));
            (a, b)
        }
        (Cancel, Sqrt) => (one.add(&rde(r, -230, -1)), one),
        (Cancel, Sqr) => (one.add(&rde(r, -230, -1)), one),
        (Overflow, Sqr) => (rde(r, 490, 510), one),
        (Underflow, Sqr) => (rde(r, -510, -430), one),
        (Overflow, Add) => (rde(r, 1000, 1021), rde(r, 900, 1021)),
        (Overflow, Mul) => {
            let t = r.int(990, 1020);
            let ea = r.int(0, 1020);
            (rand_dy(r, ea), rand_dy(r, t - ea))
        }
        (Overflow, Div) => {
            if r.coin() {
                (rde(r, 990, 1020), rde(r, -1, 0))
            } else {
                (rde(r, 990, 1021), rde(r, 990, 1021))
            }
        }
        (Overflow, Sqrt) => (rde(r, 990, 1022).abs(), one),
        (Underflow, Add) => (rde(r, -1020, -860), rde(r, -1020, -860)),
        (Underflow, Mul) => {
            let t = r.int(-1020, -860);
            let ea = r.int(-600, -300);
            (rand_dy(r, ea), rand_dy(r, t - ea))
        }
        (Underflow, Div) => {
            let t = r.int(-1020, -860);
            let eb = r.int(-50, 100);
            (rand_dy(r, t + eb), rand_dy(r, eb))
        }
        (Underflow, Sqrt) => (rde(r, -1070, -860).abs(), one),
        (Pow2, Sqrt) => {
            let k = r.int(-40, 40);
            (near_pow2(r, k).abs(), one)
        }
        (Pow2, _) => {
            let k = r.int(-20, 20);
            (rde(r, -20, 20), near_pow2(r, k))
        }
        (Sparse, Sqrt) => {
            let e = r.int(-30, 30);
            (sparse_dy(r, e).abs(), one)
        }
        (Sparse, Add) => {
            let e = r.int(-30, 30);
            let f = e + r.int(-60, 60);
            (sparse_dy(r, e), sparse_dy(r, f))
        }
        (Sparse, _) => {
            let (e, f) = (r.int(-30, 30), r.int(-30, 30));
            (sparse_dy(r, e), sparse_dy(r, f))
        }
        (Computed, _) => unreachable!(),
    };
    (qd_of(&a), qd_of(&b))
}

// -------------------------------------------------------------------------------------------------------------
// operations, their references and thresholds
// -------------------------------------------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Op {
    SloppyAdd,
    IeeeAdd,
    AddF,
    AddDd,
    SloppyMul,
    AccurateMul,
    MulF,
    MulDd,
    Sqr,
    SloppyDiv,
    AccurateDiv,
    Sqrt,
}

const OPS: [Op; 12] = [
    Op::SloppyAdd,
    Op::IeeeAdd,
    Op::AddF,
    Op::AddDd,
    Op::SloppyMul,
    Op::AccurateMul,
    Op::MulF,
    Op::MulDd,
    Op::Sqr,
    Op::SloppyDiv,
    Op::AccurateDiv,
    Op::Sqrt,
];

fn op_name(op: Op) -> &'static str {
    match op {
        Op::SloppyAdd => "sloppy add",
        Op::IeeeAdd => "accurate add",
        Op::AddF => "qd + f64",
        Op::AddDd => "qd + dd",
        Op::SloppyMul => "sloppy mul",
        Op::AccurateMul => "accurate mul",
        Op::MulF => "qd x f64",
        Op::MulDd => "qd x dd",
        Op::Sqr => "sqr",
        Op::SloppyDiv => "sloppy div",
        Op::AccurateDiv => "accurate div",
        Op::Sqrt => "sqrt",
    }
}

fn op_kind(op: Op) -> Kind {
    match op {
        Op::SloppyAdd | Op::IeeeAdd | Op::AddF | Op::AddDd => Kind::Add,
        Op::SloppyMul | Op::AccurateMul | Op::MulF | Op::MulDd => Kind::Mul,
        Op::Sqr => Kind::Sqr,
        Op::SloppyDiv | Op::AccurateDiv => Kind::Div,
        Op::Sqrt => Kind::Sqrt,
    }
}

/// Cray-style measure |error| / (|a| + |b|) instead of the relative error
fn op_cray(op: Op) -> bool {
    matches!(op, Op::SloppyAdd | Op::AddF | Op::AddDd)
}

/// pass threshold in units of 2^-209 (docs/QUAD_DOUBLE.md, fixed before the runs)
fn op_thr(op: Op) -> f64 {
    match op {
        Op::IeeeAdd => 1.0,
        Op::SloppyAdd | Op::AddF | Op::AddDd => 1.0,
        Op::SloppyMul | Op::MulDd => 2.0,
        Op::AccurateMul | Op::MulF => 1.0,
        Op::Sqr => 2.0,
        Op::SloppyDiv => 4.0,
        Op::AccurateDiv => 2.0,
        Op::Sqrt => 4.0,
    }
}

fn dd_of(b: QD) -> DD {
    DD { hi: b.x[0], lo: b.x[1] }
}

fn apply_s(op: Op, a: QD, b: QD) -> QD {
    match op {
        Op::SloppyAdd => a.sloppy_add(b),
        Op::IeeeAdd => a.ieee_add(b),
        Op::AddF => a.add_f(b.x[0]),
        Op::AddDd => a.add_dd(dd_of(b)),
        Op::SloppyMul => a.sloppy_mul(b),
        Op::AccurateMul => a.accurate_mul(b),
        Op::MulF => a.mul_f(b.x[0]),
        Op::MulDd => a.mul_dd(dd_of(b)),
        Op::Sqr => a.sqr(),
        Op::SloppyDiv => a.sloppy_div(b),
        Op::AccurateDiv => a.accurate_div(b),
        Op::Sqrt => a.sqrt(),
    }
}

fn apply_v(op: Op, a: QV, b: QV) -> QV {
    match op {
        Op::SloppyAdd => a.sloppy_add(b),
        Op::IeeeAdd => a.ieee_add(b),
        Op::AddF => a.add_v(b.c[0]),
        Op::AddDd => a.add_dv(DV { hi: b.c[0], lo: b.c[1] }),
        Op::SloppyMul => a.sloppy_mul(b),
        Op::AccurateMul => a.accurate_mul(b),
        Op::MulF => a.mul_v(b.c[0]),
        Op::MulDd => a.mul_dv(DV { hi: b.c[0], lo: b.c[1] }),
        Op::Sqr => a.sqr(),
        Op::SloppyDiv => a.sloppy_div(b),
        Op::AccurateDiv => a.accurate_div(b),
        Op::Sqrt => a.sqrt(),
    }
}

/// the second operand as the operation sees it
fn b_exact(op: Op, b: QD) -> Dy {
    match op {
        Op::AddF | Op::MulF => Dy::from_f64(b.x[0]),
        Op::AddDd | Op::MulDd => Dy::sum(&b.x[..2]),
        _ => b.exact(),
    }
}

/// (err, scale, rel, allow): the check is err <= thr·u·scale + allow, the reported value err / scale; rel is the
/// relative error of the result (= err / scale except for the Cray-style measure). In the near-underflow inputs allow
/// is 16·2^-1074 on the result (its parts cannot go below 2^-1074), carried to err: 16·2^-1074 for add and mul,
/// 16·2^-1074 |b| for div (err = |r b - a|), 32·2^-1074 |r| for sqrt (err = |r^2 - a|); div and sqrt add
/// 16·2^-1074 more for their remainders, which are formed at the scale of a.
fn exact_err(op: Op, a: QD, b: QD, r: QD, under: bool) -> (Dy, Dy, f64, Dy) {
    let (ae, be, re) = (a.exact(), b_exact(op, b), r.exact());
    let tiny = Dy::from_f64(16.0).ldexp(-1074);
    let allow = if !under {
        Dy::zero()
    } else {
        match op_kind(op) {
            Kind::Div => tiny.add(&tiny.mul(&be.abs())),
            Kind::Sqrt => tiny.add(&tiny.mul(&re.abs()).ldexp(1)),
            _ => tiny,
        }
    };
    match op_kind(op) {
        Kind::Add => {
            let x = ae.add(&be);
            let err = re.sub(&x).abs();
            let rel = err.ratio(&x);
            let scale = if op_cray(op) { ae.abs().add(&be.abs()) } else { x.abs() };
            (err, scale, rel, allow)
        }
        Kind::Mul | Kind::Sqr => {
            let x = if op == Op::Sqr { ae.mul(&ae) } else { ae.mul(&be) };
            let err = re.sub(&x).abs();
            let rel = err.ratio(&x);
            (err, x.abs(), rel, allow)
        }
        Kind::Div => {
            // |r - a/b| / |a/b| = |r b - a| / |a|
            let err = re.mul(&be).sub(&ae).abs();
            let rel = err.ratio(&ae);
            (err, ae.abs(), rel, allow)
        }
        Kind::Sqrt => {
            // r = sqrt(a)(1 + d): r^2 - a = a (2d + d^2)
            let err = re.mul(&re).sub(&ae).abs();
            let scale = ae.abs().ldexp(1);
            let rel = err.ratio(&scale);
            (err, scale, rel, allow)
        }
    }
}

fn within(err: &Dy, scale: &Dy, thr: f64, allow: &Dy) -> bool {
    let lim = scale.mul(&Dy::from_f64(thr * unit())).add(allow);
    err.cmp_abs(&lim) != Ordering::Greater
}

fn same(a: QD, b: QD) -> bool {
    a.x.iter()
        .zip(b.x.iter())
        .all(|(x, y)| x.to_bits() == y.to_bits() || (x.is_nan() && y.is_nan()))
}

fn fnv(h: &mut u64, x: QD) {
    for v in x.x {
        let v = if v.is_nan() { f64::NAN } else { v };
        for byte in v.to_bits().to_le_bytes() {
            *h ^= byte as u64;
            *h = h.wrapping_mul(0x100000001b3);
        }
    }
}

/// One line of the results.
#[derive(Clone, Debug)]
pub(crate) struct Res {
    pub what: String,
    pub cat: &'static str,
    pub n: usize,
    /// max and 99.9th percentile of the check's measure, in units of 2^-209
    pub max: f64,
    pub p999: f64,
    /// max of the relative error (= the measure except for the Cray-style adds), in units of 2^-209
    pub rel_max: f64,
    pub thr: f64,
    /// samples outside the bound
    pub fails: usize,
    /// lanes whose 8-lane result differs from the scalar one in any bit
    pub mism: usize,
    pub digest: u64,
}

impl Res {
    fn ok(&self) -> bool {
        self.fails == 0 && self.mism == 0
    }
}

fn pct(v: &mut [f64], q: f64) -> f64 {
    if v.is_empty() {
        return 0.0;
    }
    v.sort_by(|a, b| a.partial_cmp(b).unwrap_or(Ordering::Equal));
    v[((v.len() - 1) as f64 * q).floor() as usize]
}

fn fmt_u(x: f64) -> String {
    if x == 0.0 {
        "0".into()
    } else if x.is_infinite() {
        "inf".into()
    } else if (0.01..1000.0).contains(&x) {
        format!("{x:.3}")
    } else {
        format!("{x:.2e}")
    }
}

fn print_table(title: &str, rs: &[Res]) {
    println!("{title}");
    println!(
        "  {:<14} {:<10} {:>6} {:>10} {:>10} {:>10} {:>6} {:>6} {:>6}",
        "operation", "inputs", "n", "max", "99.9%", "max rel", "thr", "fails", "lanes"
    );
    for r in rs {
        println!(
            "  {:<14} {:<10} {:>6} {:>10} {:>10} {:>10} {:>6} {:>6} {:>6}",
            r.what,
            r.cat,
            r.n,
            fmt_u(r.max),
            fmt_u(r.p999),
            fmt_u(r.rel_max),
            fmt_u(r.thr),
            r.fails,
            r.mism
        );
    }
}

/// inputs of one operation and category (generated with no mutation active)
fn inputs(op: Op, cat: Cat, n: usize, seed: u64) -> Vec<(QD, QD)> {
    let mut r = Rng::new(seed ^ ((op as u64) << 32) ^ ((cat as u64) << 40));
    (0..n).map(|_| gen(&mut r, op_kind(op), cat)).collect()
}

/// scalar and 8-lane results of one operation on the inputs
fn results(op: Op, inp: &[(QD, QD)]) -> (Vec<QD>, Vec<QD>) {
    let rs: Vec<QD> = inp.iter().map(|&(a, b)| apply_s(op, a, b)).collect();
    let mut rv = Vec::with_capacity(inp.len());
    for c in inp.chunks(8) {
        let mut la = [QD::ZERO; 8];
        let mut lb = [QD::ONE; 8];
        for (j, &(a, b)) in c.iter().enumerate() {
            la[j] = a;
            lb[j] = b;
        }
        let out = apply_v(op, QV::from_lanes(&la), QV::from_lanes(&lb)).lanes();
        rv.extend_from_slice(&out[..c.len()]);
    }
    (rs, rv)
}

/// accuracy and agreement of every operation in every category, with mutation `id` active during the arithmetic
pub(crate) fn run_ops(n: usize, seed: u64, id: u32) -> Vec<Res> {
    let mut out = Vec::new();
    for op in OPS {
        for cat in CATS {
            let inp = inputs(op, cat, n, seed);
            set_mutation(id);
            let (rs, rv) = results(op, &inp);
            set_mutation(0);
            let under = cat == Cat::Underflow;
            let (mut ms, mut fails, mut mism, mut rel_max) = (Vec::with_capacity(n), 0, 0, 0f64);
            let mut digest = 0xcbf29ce484222325u64;
            for (k, &(a, b)) in inp.iter().enumerate() {
                let r = rs[k];
                fnv(&mut digest, r);
                if !same(r, rv[k]) {
                    mism += 1;
                }
                if !r.x.iter().all(|v| v.is_finite()) {
                    fails += 1;
                    ms.push(f64::INFINITY);
                    continue;
                }
                let (err, scale, rel, allow) = exact_err(op, a, b, r, under);
                if !within(&err, &scale, op_thr(op), &allow) {
                    fails += 1;
                }
                ms.push(err.ratio(&scale) / unit());
                rel_max = rel_max.max(rel / unit());
            }
            let max = ms.iter().cloned().fold(0.0, f64::max);
            let p999 = pct(&mut ms, 0.999);
            out.push(Res {
                what: op_name(op).into(),
                cat: cat_name(cat),
                n,
                max,
                p999,
                rel_max,
                thr: op_thr(op),
                fails,
                mism,
                digest,
            });
        }
    }
    out
}

// -------------------------------------------------------------------------------------------------------------
// the dot accumulator
// -------------------------------------------------------------------------------------------------------------

const ACC_CATS: [&str; 4] = ["random", "cancel", "wide", "mixed"];

/// accuracy of QDotAcc / QdAcc on dot products of length len (8 per sample, one per lane): |error| / sum |a_i b_i|
pub(crate) fn run_acc(n: usize, seed: u64, id: u32) -> Vec<Res> {
    let mut out = Vec::new();
    for len in [1usize, 4, 16, 64, 128] {
        for (ci, cat) in ACC_CATS.iter().enumerate() {
            let mut r = Rng::new(seed ^ ((len as u64) << 20) ^ ((ci as u64) << 30) ^ 0xacc);
            let thr = (8.0 + len as f64) / 8.0;
            let (mut ms, mut fails, mut mism, mut rel_max) = (Vec::new(), 0, 0, 0f64);
            let mut digest = 0xcbf29ce484222325u64;
            let nsamp = (n / 8).max(1) * 8 / len.clamp(1, 16);
            let nsamp = nsamp.max(8) / 8 * 8;
            for _ in 0..nsamp / 8 {
                // 8 lanes x len terms
                let mut a = vec![[QD::ZERO; 8]; len];
                let mut b = vec![[QD::ZERO; 8]; len];
                for lane in 0..8 {
                    for i in 0..len {
                        let (x, y) = match *cat {
                            "wide" => (rde(&mut r, -100, 100), rde(&mut r, -100, 100)),
                            "cancel" if i >= len / 2 && len > 1 => {
                                // a_i b_i = -(a_k b_k)(1 + d): pairs that nearly cancel
                                let k = i - len / 2;
                                let ak = a[k][lane].exact();
                                let d = rde(&mut r, -200, -1);
                                (ak.neg().add(&ak.mul(&d)), b[k][lane].exact())
                            }
                            _ => (rde(&mut r, -3, 3), rde(&mut r, -3, 3)),
                        };
                        a[i][lane] = qd_of(&x);
                        b[i][lane] = qd_of(&y);
                    }
                }
                let plain = |i: usize| *cat == "mixed" && i % 4 == 3;
                set_mutation(id);
                let mut acc = QDotAcc::zero();
                for i in 0..len {
                    acc = if plain(i) {
                        acc.add(QV::from_lanes(&a[i]))
                    } else {
                        acc.add_prod(QV::from_lanes(&a[i]), QV::from_lanes(&b[i]))
                    };
                }
                let rv = acc.finish().lanes();
                let rs: Vec<QD> = (0..8)
                    .map(|lane| {
                        let mut s = QdAcc::zero();
                        for i in 0..len {
                            s = if plain(i) {
                                s.add(a[i][lane])
                            } else {
                                s.add_prod(a[i][lane], b[i][lane])
                            };
                        }
                        s.finish()
                    })
                    .collect();
                set_mutation(0);
                for lane in 0..8 {
                    fnv(&mut digest, rs[lane]);
                    if !same(rs[lane], rv[lane]) {
                        mism += 1;
                    }
                    let (mut x, mut s) = (Dy::zero(), Dy::zero());
                    for i in 0..len {
                        let t = if plain(i) {
                            a[i][lane].exact()
                        } else {
                            a[i][lane].exact().mul(&b[i][lane].exact())
                        };
                        s = s.add(&t.abs());
                        x = x.add(&t);
                    }
                    let err = rs[lane].exact().sub(&x).abs();
                    if !within(&err, &s, thr, &Dy::zero()) {
                        fails += 1;
                    }
                    ms.push(err.ratio(&s) / unit());
                    rel_max = rel_max.max(err.ratio(&x) / unit());
                }
            }
            let max = ms.iter().cloned().fold(0.0, f64::max);
            let p999 = pct(&mut ms, 0.999);
            out.push(Res {
                what: format!("dot n={len}"),
                cat,
                n: ms.len(),
                max,
                p999,
                rel_max,
                thr,
                fails,
                mism,
                digest,
            });
        }
    }
    out
}

// -------------------------------------------------------------------------------------------------------------
// conversions and decimal input/output
// -------------------------------------------------------------------------------------------------------------

/// (negative, digits as integer, exponent of the last digit, number of digits) of "-d.ddde±xx"
fn split_sci(s: &str) -> (bool, BigU, i64, usize) {
    let (neg, s) = if let Some(t) = s.strip_prefix('-') {
        (true, t)
    } else {
        (false, s)
    };
    let p = s.find('e').unwrap();
    let (m, e) = (&s[..p], s[p + 1..].parse::<i64>().unwrap());
    let frac = m.find('.').map(|q| m.len() - q - 1).unwrap_or(0);
    let digits: String = m.chars().filter(|c| *c != '.').collect();
    (neg, BigU::from_dec(&digits), e - frac as i64, digits.len())
}

/// value of a decimal n·10^e times 10^s (s >= -e so the result is an integer): exact Dy
fn dec_scaled(neg: bool, n: &BigU, e: i64, s: i64) -> Dy {
    assert!(e + s >= 0);
    let m = n.mul(&BigU::pow_small(10, (e + s) as u64));
    Dy {
        neg: neg && !m.is_zero(),
        m,
        e: 0,
    }
}

/// ulp of a finite nonzero f64
fn ulp(x: f64) -> Dy {
    let e = ((x.to_bits() >> 52) & 0x7ff) as i64;
    Dy::from_f64(1.0).ldexp(if e == 0 { -1074 } else { e - 1075 })
}

pub(crate) fn run_io(n: usize, seed: u64, id: u32) -> Vec<Res> {
    let mut out = Vec::new();
    let mut r = Rng::new(seed ^ 0x10);
    // parsing: random decimals, 1-90 digits, exponents -250..300
    let (mut ms, mut fails, mut greedy_fails) = (Vec::new(), 0, 0);
    for _ in 0..n {
        let nd = r.int(1, 90) as usize;
        let mut d = String::new();
        d.push((b'1' + (r.next() % 9) as u8) as char);
        for _ in 1..nd {
            d.push((b'0' + (r.next() % 10) as u8) as char);
        }
        let e10 = r.int(-250 - nd as i64, 300 - nd as i64);
        let neg = r.coin();
        let s = format!("{}{}e{}", if neg { "-" } else { "" }, d, e10);
        set_mutation(id);
        let q = QD::parse(&s).unwrap();
        set_mutation(0);
        // |q - v| relative, exactly: scale both by 10^max(0, -e10)
        let sh = (-e10).max(0);
        let v = dec_scaled(neg, &BigU::from_dec(&d), e10, sh);
        let qs = q.exact().mul(&Dy {
            neg: false,
            m: BigU::pow_small(10, sh as u64),
            e: 0,
        });
        let err = qs.sub(&v).abs();
        let rel = err.ratio(&v) / unit();
        ms.push(rel);
        if rel > 0.25 {
            fails += 1;
        }
        // greedy round-to-nearest: |q - v| <= ulp(x3)/2 (zero if x3 is zero), scaled the same way
        let last = q.x.iter().rposition(|c| *c != 0.0).unwrap();
        let half = ulp(q.x[last]).ldexp(-1).mul(&Dy {
            neg: false,
            m: BigU::pow_small(10, sh as u64),
            e: 0,
        });
        let bound = if last == 3 { half } else { Dy::zero() };
        if err.cmp_abs(&bound) == Ordering::Greater {
            greedy_fails += 1;
        }
    }
    let max = ms.iter().cloned().fold(0.0, f64::max);
    let p999 = pct(&mut ms, 0.999);
    out.push(Res {
        what: "parse".into(),
        cat: "decimal",
        n,
        max,
        p999,
        rel_max: max,
        thr: 0.25,
        fails,
        mism: 0,
        digest: 0,
    });
    out.push(Res {
        what: "parse".into(),
        cat: "greedy RN",
        n,
        max: greedy_fails as f64,
        p999: 0.0,
        rel_max: 0.0,
        thr: 0.0,
        fails: greedy_fails,
        mism: 0,
        digest: 0,
    });

    // printing: correctly rounded to the digits asked for (half to even), exactly checked
    let mut print_fails = 0;
    let mut np = 0;
    for _ in 0..n / 4 {
        let x = qd_of(&rde(&mut r, -1000, 1000));
        for digits in [1usize, 2, 16, 17, 33, 64, 66, 70, 100] {
            np += 1;
            let s = x.to_sci(digits);
            let (neg, m, e, nd) = split_sci(&s);
            let xv = x.exact();
            // |x - m 10^e| <= 5·10^(e-1), all scaled by 10^(1-e) when e < 1
            let sh = (1 - e).max(0);
            let xs = xv.mul(&Dy {
                neg: false,
                m: BigU::pow_small(10, sh as u64),
                e: 0,
            });
            let ds = dec_scaled(neg, &m, e, sh);
            let half = dec_scaled(false, &BigU::from_u64(5), e - 1, sh);
            let c = xs.sub(&ds).abs().cmp_abs(&half);
            let even = m.divrem_small(2).1 == 0;
            let lead_ok = m.to_dec().len() == digits && nd == digits;
            if c == Ordering::Greater || (c == Ordering::Equal && !even) || !lead_ok || neg != xv.neg {
                print_fails += 1;
            }
        }
    }
    out.push(Res {
        what: "print".into(),
        cat: "rounding",
        n: np,
        max: print_fails as f64,
        p999: 0.0,
        rel_max: 0.0,
        thr: 0.0,
        fails: print_fails,
        mism: 0,
        digest: 0,
    });

    // round trips: all exact digits, and 70 digits, back to the same four parts
    let (mut rt_exact, mut rt70) = (0, 0);
    for _ in 0..n / 4 {
        let x = qd_of(&rde(&mut r, -280, 280));
        let (_, dm, _) = x.exact().to_decimal();
        let all = dm.to_dec().trim_end_matches('0').len().max(1);
        set_mutation(id);
        let y = QD::parse(&x.to_sci(all)).unwrap();
        let y70 = QD::parse(&x.to_sci(70)).unwrap();
        set_mutation(0);
        rt_exact += !same(x, y) as usize;
        rt70 += !same(x, y70) as usize;
    }
    out.push(Res {
        what: "round trip".into(),
        cat: "exact",
        n: n / 4,
        max: rt_exact as f64,
        p999: 0.0,
        rel_max: 0.0,
        thr: 0.0,
        fails: rt_exact,
        mism: 0,
        digest: 0,
    });
    out.push(Res {
        what: "round trip".into(),
        cat: "70 digits",
        n: n / 4,
        max: rt70 as f64,
        p999: 0.0,
        rel_max: 0.0,
        thr: 0.0,
        fails: rt70,
        mism: 0,
        digest: 0,
    });

    // conversions: to_dd within 2^-105 relative, to_f64 within one ulp (and how often not the nearest)
    let (mut dd_fails, mut f_fails, mut f_not_nearest, mut conv_mism) = (0, 0, 0, 0);
    let mut lanes = Vec::new();
    for _ in 0..n {
        let x = qd_of(&rde(&mut r, -900, 900));
        let xv = x.exact();
        let d = x.to_dd();
        let f = x.to_f64();
        if Dy::sum(&[d.hi, d.lo]).sub(&xv).abs().cmp_abs(&xv.abs().ldexp(-105)) == Ordering::Greater {
            dd_fails += 1;
        }
        let ef = Dy::from_f64(f).sub(&xv).abs();
        if ef.cmp_abs(&ulp(f)) == Ordering::Greater {
            f_fails += 1;
        }
        if ef.cmp_abs(&ulp(f).ldexp(-1)) == Ordering::Greater {
            f_not_nearest += 1;
        }
        if QD::from_dd(d).x != [d.hi, d.lo, 0.0, 0.0] {
            dd_fails += 1;
        }
        lanes.push((x, d, f));
    }
    for c in lanes.chunks(8) {
        if c.len() < 8 {
            break;
        }
        let xs: [QD; 8] = std::array::from_fn(|j| c[j].0);
        let v = QV::from_lanes(&xs);
        let (dv, fv) = (v.to_dv(), v.to_v8().to_array());
        for j in 0..8 {
            let dj = dv.lane(j);
            if dj.hi.to_bits() != c[j].1.hi.to_bits()
                || dj.lo.to_bits() != c[j].1.lo.to_bits()
                || fv[j].to_bits() != c[j].2.to_bits()
            {
                conv_mism += 1;
            }
        }
    }
    out.push(Res {
        what: "to_dd".into(),
        cat: "random",
        n,
        max: dd_fails as f64,
        p999: 0.0,
        rel_max: 0.0,
        thr: 0.0,
        fails: dd_fails,
        mism: conv_mism,
        digest: 0,
    });
    out.push(Res {
        what: "to_f64".into(),
        cat: "random",
        n,
        max: f_not_nearest as f64,
        p999: 0.0,
        rel_max: 0.0,
        thr: 0.0,
        fails: f_fails,
        mism: conv_mism,
        digest: 0,
    });
    out
}

fn print_io(rs: &[Res]) {
    println!("decimal input/output and conversions");
    for r in rs {
        match (r.what.as_str(), r.cat) {
            ("parse", "decimal") => println!(
                "  parse: n {} relative error max {} u, 99.9% {} u (threshold 0.25 u); outside: {}",
                r.n,
                fmt_u(r.max),
                fmt_u(r.p999),
                r.fails
            ),
            ("parse", _) => println!("  parse: greedy round-to-nearest violated in {} of {}", r.fails, r.n),
            ("print", _) => println!(
                "  print: not correctly rounded (or misformatted) in {} of {} strings",
                r.fails, r.n
            ),
            ("round trip", c) => println!("  round trip ({c}): {} of {} differ", r.fails, r.n),
            ("to_dd", _) => println!(
                "  to_dd: {} of {} beyond 2^-105 relative; 8-lane mismatches {}",
                r.fails, r.n, r.mism
            ),
            ("to_f64", _) => println!(
                "  to_f64: {} of {} beyond one ulp, {} not the nearest; 8-lane mismatches {}",
                r.fails, r.n, r.max as usize, r.mism
            ),
            _ => {}
        }
    }
}

// -------------------------------------------------------------------------------------------------------------
// the tests
// -------------------------------------------------------------------------------------------------------------

#[test]
fn qd_constants() {
    let pi = "3.14159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798";
    assert!(same(QD::parse(pi).unwrap(), QD::PI));
    let tau = "6.28318530717958647692528676655900576839433879875021164194988918461563281257241799725606965068423413596";
    assert!(same(QD::parse(tau).unwrap(), QD::TWO_PI));
    assert_eq!(QD::EPS, unit());
    // QD::PI is 5.7e-66 below pi: its 66-digit value (from mpmath on its four parts) ends in ...230
    assert_eq!(
        QD::PI.to_sci(66),
        "3.14159265358979323846264338327950288419716939937510582097494459230e+00"
    );
    assert_eq!(
        format!("{:.59}", QD::ONE / QD::from_f64(3.0)),
        format!("3.{}e-01", "3".repeat(59))
    );
    assert_eq!(QD::from_f64(-0.0).to_sci(3), "-0.00e+00");
    assert_eq!(QD::parse("1e400").unwrap().x[0], f64::INFINITY);
    assert!(same(QD::parse("-0").unwrap(), QD::from_f64(-0.0)));
    // powi and recip agree with repeated products to rounding
    let x = QD::parse("1.0000001234567890123456789").unwrap();
    let p = x.powi(5);
    let q = x * x * x * x * x;
    assert!((p - q).abs().to_f64() < 1e-62, "{}", (p - q).to_f64());
    assert!(((x.powi(-3) * x.powi(3)) - QD::ONE).abs().to_f64() < 1e-62);
}

#[test]
fn qd_accuracy() {
    let n = env_usize("QD_N", 4000) / 8 * 8;
    let seed = env_usize("QD_SEED", 1) as u64;
    let rs = run_ops(n, seed, 0);
    let mut digest = 0xcbf29ce484222325u64;
    for r in &rs {
        digest ^= r.digest;
        digest = digest.wrapping_mul(0x100000001b3);
    }
    if report() {
        print_table(
            &format!("quad-double accuracy (units of 2^-209; n per row; isa {})", V8::ISA),
            &rs,
        );
    }
    println!("qd digest {digest:016x} (n {n}, seed {seed}, isa {})", V8::ISA);
    let bad: Vec<&Res> = rs.iter().filter(|r| !r.ok()).collect();
    assert!(bad.is_empty(), "{} rows fail: {:?}", bad.len(), bad);
}

/// Near-cancelling sums where QD's accurate add drops v when all parts are read with three emitted (up to 86 u), and
/// where the first repair here (u + v rounded to one double) still left up to 11 u. They were found by checking the
/// upstream C++ library (github.com/BL-highprecision/qd) against mpmath with a = round(x), b = round(-x + d), x and d
/// random with 424 bits, |d| ~ 2^-k |x|, k = 1..30, which this file's random categories had missed. Each sum must be
/// within 1 u of the exact one, the 8-lane add must agree with the scalar one bit for bit, and QD's literal algorithm
/// must miss by more than 1 u on at least one of them (the control).
#[test]
fn qd_ieee_add_regression() {
    let cases: [([u64; 4], [u64; 4]); 11] = [
        // QD 86.5 u, u + v 0 u
        (
            [
                0x3ef951721a089dac,
                0x3b9bfd25b612531b,
                0x3828ccb5c92981ca,
                0x34bfdb48ac690c3e,
            ],
            [
                0xbef9516c2de75542,
                0xbb9ef9cf9d9adc96,
                0x3837d7f1c298e636,
                0x347fff9515590769,
            ],
        ),
        // QD 36.3 u, u + v 0 u
        (
            [
                0x402b19c6d75a4d6e,
                0xbcc2b2893130a8b5,
                0xb92d8f0b92099d05,
                0x35c3a15c7a42b826,
            ],
            [
                0xc02b19d4f23da799,
                0x3ccc5a00064e2d90,
                0xb93f649c2d5adb67,
                0x35afff4fc9a005eb,
            ],
        ),
        // QD 24.4 u, u + v 0 u
        (
            [
                0x40e8e8f019860773,
                0x3d7c0b7495f54327,
                0xba1ea4cb65a1dde9,
                0x36b3d1ab6bbfea7f,
            ],
            [
                0xc0e8e997f59382e5,
                0x3d7f337fa392d224,
                0x39f81c33a8bef873,
                0x369fffff555aa4e9,
            ],
        ),
        // QD 11 u, u + v 0 u
        (
            [
                0x3fab4917aa6521c1,
                0xbc431751b90eebbc,
                0x38e457fd5ceb2937,
                0xb581c291b33ec99a,
            ],
            [
                0xbfab47a3a55cf42d,
                0x3c4acce345ad26ad,
                0x38c1dd9152e35abb,
                0xb55ffc8c15aa0bd5,
            ],
        ),
        // QD 5.51 u, u + v 0 u
        (
            [
                0x3f233bff86a76a84,
                0xbbbfbb82ff3b21df,
                0xb845a1132e342815,
                0xb4b5a63ed5712530,
            ],
            [
                0xbf233c2df82cb8d4,
                0x3ba33f9553bbd4bf,
                0x380904ba0a4aa555,
                0xb49fe9840028655d,
            ],
        ),
        // QD 4.11 u, u + v 0 u
        (
            [
                0x3f6bf05cb9fdf68b,
                0xbc03bfd56bc70ef5,
                0x38a0ef38ec9dbbf0,
                0xb52639a5fc7c012f,
            ],
            [
                0xbf6bef63a3889911,
                0x3bf199494adfff9d,
                0xb88e8aca38c58a94,
                0xb4fffa11888c72cd,
            ],
        ),
        // QD 3.91 u, u + v 3.91 u
        (
            [
                0x404498cf8495391b,
                0x3c9ff868cd9f016b,
                0xb93581fb16ee53c6,
                0xb598823c55a81995,
            ],
            [
                0xc044987d9f7f6628,
                0x3cb7f325473af245,
                0xb95c81ecfbadb115,
                0xb5d296c70e5ffc27,
            ],
        ),
        // QD 3.46 u, u + v 0 u
        (
            [
                0x3f7b8dcd4ea99299,
                0xbc074e4764154a57,
                0x38abd826ee7e9024,
                0xb50ffc0f5ae41f2b,
            ],
            [
                0xbf7b8ef5a4d1abbe,
                0x3c18613829fefd70,
                0x38a5ad4d22961835,
                0xb537c5c293313478,
            ],
        ),
        // QD 1.68 u, u + v 0 u
        (
            [
                0x3f1fe8334ab9d3a3,
                0xbbae4cb4c1d13471,
                0xb84c14a49ca1a931,
                0x347fd1b0bdfa9d37,
            ],
            [
                0xbf1fe7e70851524c,
                0x3bac8b41c2227b93,
                0x38344b4bce56d5e4,
                0x34dd29a97e190def,
            ],
        ),
        // QD 1.32 u, u + v 1.32 u
        (
            [
                0x40f9516d7b423272,
                0xbd77b4d4c47d3b4f,
                0xb9ea5903e5652218,
                0xb6850a737a3acaa9,
            ],
            [
                0xc0f950ac0f3312f0,
                0x3d4ff0595728ab83,
                0xb9ea80293fdb0e41,
                0xb661f5c78597f551,
            ],
        ),
        // QD 10.8 u, u + v 10.8 u
        (
            [
                0x4118c13ebd58c314,
                0xbd9ffa669caed1c3,
                0xba3b0a1f7341752a,
                0x36cbed49380a1951,
            ],
            [
                0xc118bfc27fb8259d,
                0xbda01b0f65212978,
                0x3a4a40bbd55040e7,
                0xb6e16e495cfa947e,
            ],
        ),
    ];
    let f = |p: [u64; 4]| QD {
        x: p.map(f64::from_bits),
    };
    let mut worst = 0f64;
    let mut literal_worst = 0f64;
    for chunk in cases.chunks(8) {
        let mut la = [QD { x: [0.0; 4] }; 8];
        let mut lb = [QD { x: [0.0; 4] }; 8];
        for (m, (a, b)) in chunk.iter().enumerate() {
            la[m] = f(*a);
            lb[m] = f(*b);
        }
        let lanes = QV::from_lanes(&la).ieee_add(QV::from_lanes(&lb)).lanes();
        for m in 0..chunk.len() {
            let (qa, qb) = (la[m], lb[m]);
            let x = qa.exact().add(&qb.exact());
            let r = qa.ieee_add(qb);
            assert_eq!(
                r.x.map(f64::to_bits),
                lanes[m].x.map(f64::to_bits),
                "case {m}: scalar and 8-lane differ"
            );
            worst = worst.max(r.exact().sub(&x).abs().ratio(&x) / unit());
            literal_worst = literal_worst.max(ieee_add_qd_literal(qa, qb).exact().sub(&x).abs().ratio(&x) / unit());
        }
    }
    if report() {
        println!(
            "accurate add, {} regression sums: max error {worst:.3} u (QD's literal algorithm: {literal_worst:.3} u)",
            cases.len()
        );
    }
    assert!(worst <= 1.0, "accurate add misses by {worst} u");
    assert!(
        literal_worst > 1.0,
        "control: QD's literal algorithm should miss these ({literal_worst} u)"
    );
}

#[test]
fn qd_accumulator() {
    let n = env_usize("QD_N", 4000) / 8 * 8;
    let seed = env_usize("QD_SEED", 1) as u64;
    let rs = run_acc(n / 4, seed, 0);
    if report() {
        print_table(
            "dot accumulator: |error| / sum |a_i b_i| (units of 2^-209); threshold (8 + n)/8",
            &rs,
        );
    }
    let bad: Vec<&Res> = rs.iter().filter(|r| !r.ok()).collect();
    assert!(bad.is_empty(), "{bad:?}");
}

#[test]
fn qd_decimal_io() {
    let n = env_usize("QD_N", 4000);
    let seed = env_usize("QD_SEED", 1) as u64;
    let rs = run_io(n, seed, 0);
    if report() {
        print_io(&rs);
    }
    let bad: Vec<&Res> = rs.iter().filter(|r| !r.ok()).collect();
    assert!(bad.is_empty(), "{bad:?}");
}

/// Every deliberate breakage (qd::mutate) must make at least one check fail.
#[cfg(feature = "mutate")]
#[test]
fn qd_controls() {
    let n = env_usize("QD_N", 1000) / 8 * 8;
    let mut silent = Vec::new();
    for id in 1..=mutate::N {
        let mut rs = run_ops(n, 7, id);
        rs.extend(run_acc(n / 4, 7, id));
        rs.extend(run_io(n / 2, 7, id));
        let failed: Vec<&Res> = rs.iter().filter(|r| !r.ok()).collect();
        let worst = failed.iter().map(|r| r.max).fold(0.0, f64::max);
        let lanes: usize = failed.iter().map(|r| r.mism).sum();
        let rows: Vec<String> = failed.iter().take(6).map(|r| format!("{}/{}", r.what, r.cat)).collect();
        println!(
            "control {id:2} {:<50} fires: {:>3} rows fail, worst {} u, {} lane mismatches; e.g. {}",
            mutate::NAMES[id as usize],
            failed.len(),
            fmt_u(worst),
            lanes,
            rows.join(", ")
        );
        if failed.is_empty() {
            silent.push(id);
        }
    }
    assert!(silent.is_empty(), "controls that did not fire: {silent:?}");
}

/// Inputs and results for hp/qd_check.py: QD_DUMP=DIR writes ops.bin (rows of 12 f64: a, b, scalar result) with
/// index ops.txt, and io.txt (parse and print cases).
#[test]
#[ignore]
fn qd_dump() {
    use std::io::Write;
    let dir = std::env::var("QD_DUMP").expect("QD_DUMP=directory");
    let n = env_usize("QD_N", 2000) / 8 * 8;
    let seed = env_usize("QD_SEED", 1) as u64;
    // QD_MUTATE=id (feature mutate): break one algorithm during the arithmetic, for the control of qd_check.py
    let id = env_usize("QD_MUTATE", 0) as u32;
    std::fs::create_dir_all(&dir).unwrap();
    let mut bin = std::io::BufWriter::new(std::fs::File::create(format!("{dir}/ops.bin")).unwrap());
    let mut idx = std::fs::File::create(format!("{dir}/ops.txt")).unwrap();
    for op in OPS {
        for cat in CATS {
            let inp = inputs(op, cat, n, seed);
            set_mutation(id);
            let (rs, _) = results(op, &inp);
            set_mutation(0);
            writeln!(idx, "{}\t{}\t{}\t{}", op_name(op), cat_name(cat), n, op_thr(op)).unwrap();
            for (k, &(a, b)) in inp.iter().enumerate() {
                for v in a.x.iter().chain(b.x.iter()).chain(rs[k].x.iter()) {
                    bin.write_all(&v.to_le_bytes()).unwrap();
                }
            }
        }
    }
    // dot accumulator: 8 lanes of length-16 sums, rows a(4) b(4) per term, then the 8 results
    let mut r = Rng::new(seed ^ 0xd07);
    let len = 16;
    writeln!(idx, "dot\t{}\t{}\t{}", len, n / 8, (8.0 + len as f64) / 8.0).unwrap();
    for _ in 0..n / 8 {
        let a: Vec<[QD; 8]> = (0..len)
            .map(|_| std::array::from_fn(|_| qd_of(&rde(&mut r, -3, 3))))
            .collect();
        let b: Vec<[QD; 8]> = (0..len)
            .map(|_| std::array::from_fn(|_| qd_of(&rde(&mut r, -3, 3))))
            .collect();
        set_mutation(id);
        let mut acc = QDotAcc::zero();
        for i in 0..len {
            acc = acc.add_prod(QV::from_lanes(&a[i]), QV::from_lanes(&b[i]));
        }
        let res = acc.finish().lanes();
        set_mutation(0);
        for i in 0..len {
            for lane in 0..8 {
                for v in a[i][lane].x.iter().chain(b[i][lane].x.iter()) {
                    bin.write_all(&v.to_le_bytes()).unwrap();
                }
            }
        }
        for q in res {
            for v in q.x {
                bin.write_all(&v.to_le_bytes()).unwrap();
            }
        }
    }
    // decimal: parse lines "P <string> <4 parts as hex bits>" and print lines "S <4 parts> <digits> <string>"
    let mut io = std::io::BufWriter::new(std::fs::File::create(format!("{dir}/io.txt")).unwrap());
    for _ in 0..n {
        let nd = r.int(1, 90) as usize;
        let mut d = String::new();
        d.push((b'1' + (r.next() % 9) as u8) as char);
        for _ in 1..nd {
            d.push((b'0' + (r.next() % 10) as u8) as char);
        }
        let s = format!(
            "{}{}e{}",
            if r.coin() { "-" } else { "" },
            d,
            r.int(-250 - nd as i64, 300 - nd as i64)
        );
        set_mutation(id);
        let q = QD::parse(&s).unwrap();
        set_mutation(0);
        writeln!(io, "P {s} {}", q.x.map(|v| format!("{:016x}", v.to_bits())).join(" ")).unwrap();
        let x = qd_of(&rde(&mut r, -1000, 1000));
        let digits = [1usize, 17, 33, 64, 66, 70, 100][r.int(0, 6) as usize];
        writeln!(
            io,
            "S {} {digits} {}",
            x.x.map(|v| format!("{:016x}", v.to_bits())).join(" "),
            x.to_sci(digits)
        )
        .unwrap();
    }
    println!("wrote {dir}/ops.bin, ops.txt, io.txt (n {n}, seed {seed}, mutation {id})");
}

// -------------------------------------------------------------------------------------------------------------
// throughput
// -------------------------------------------------------------------------------------------------------------

/// cargo test --release --lib bench_qd -- --ignored --nocapture: nanoseconds per lane and operation, one thread,
/// 16 independent vectors per pass (throughput, not latency); each row the minimum of 5 timings
#[test]
#[ignore]
fn bench_qd() {
    use std::hint::black_box;
    use std::time::Instant;
    const NV: usize = 16;
    let reps = env_usize("QD_BENCH_REPS", 20000);
    let mut r = Rng::new(3);
    let near1 = |r: &mut Rng| qd_of(&Dy::from_f64(1.0).add(&rde(r, -30, -20)));
    let rq = |r: &mut Rng| qd_of(&rde(r, -2, 2));
    let lanes = |r: &mut Rng, f: &dyn Fn(&mut Rng) -> QD| -> QV { QV::from_lanes(&std::array::from_fn(|_| f(r))) };
    let qa: Vec<QV> = (0..NV).map(|_| lanes(&mut r, &rq)).collect();
    let qy: Vec<QV> = (0..NV).map(|_| lanes(&mut r, &near1)).collect();
    let qz: Vec<QV> = (0..NV).map(|_| lanes(&mut r, &rq)).collect();
    let da: Vec<DV> = qa.iter().map(|q| q.to_dv()).collect();
    let dy: Vec<DV> = qy.iter().map(|q| q.to_dv()).collect();
    let dz: Vec<DV> = qz.iter().map(|q| q.to_dv()).collect();
    let fa: Vec<V8> = qa.iter().map(|q| q.c[0]).collect();
    let fy: Vec<V8> = qy.iter().map(|q| q.c[0]).collect();
    let fz: Vec<V8> = qz.iter().map(|q| q.c[0]).collect();
    let per = (reps * NV * 8) as f64;
    // x[i] = body(x[i], i) over NV independent chains, reps passes
    macro_rules! time {
        ($x:expr, $body:expr) => {{
            let mut best = f64::INFINITY;
            for _ in 0..5 {
                let mut x = $x.clone();
                let t0 = Instant::now();
                for _ in 0..reps {
                    for i in 0..NV {
                        x[i] = ($body)(x[i], i);
                    }
                    black_box(&mut x);
                }
                best = best.min(t0.elapsed().as_secs_f64() * 1e9 / per);
                black_box(&x);
            }
            best
        }};
    }
    // 16-term sums of products through an accumulator, finished: ns per lane and term
    macro_rules! dot {
        ($a:expr, $b:expr, $zero:expr) => {{
            let mut best = f64::INFINITY;
            for _ in 0..5 {
                let t0 = Instant::now();
                for _ in 0..reps {
                    for i in 0..NV {
                        let mut acc = $zero;
                        for k in 0..16 {
                            acc = acc.add_prod($a[(i + k) % NV], $b[k]);
                        }
                        black_box(acc.finish());
                    }
                }
                best = best.min(t0.elapsed().as_secs_f64() * 1e9 / (per * 16.0));
            }
            best
        }};
    }
    let half = V8::splat(0.5);
    println!(
        "isa {}, ns per lane and operation (one thread, {NV} independent vectors, min of 5)",
        V8::ISA
    );
    let f_add = time!(fa, |x: V8, i: usize| x.add(fz[i]));
    let f_mul = time!(fa, |x: V8, i: usize| x.mul(fy[i]));
    let f_div = time!(fa, |x: V8, i: usize| x.div(fy[i]));
    let f_fma = time!(fa, |x: V8, i: usize| x.fma(half, fz[i]));
    let f_sqrt = time!(fa, |x: V8, i: usize| x.abs().sqrt().add(fz[i].abs()));
    let f_dot = {
        let mut best = f64::INFINITY;
        for _ in 0..5 {
            let t0 = Instant::now();
            for _ in 0..reps {
                for i in 0..NV {
                    let mut acc = V8::zero();
                    for k in 0..16 {
                        acc = fa[(i + k) % NV].fma(fy[k], acc);
                    }
                    black_box(acc);
                }
            }
            best = best.min(t0.elapsed().as_secs_f64() * 1e9 / (per * 16.0));
        }
        best
    };
    let d_add = time!(da, |x: DV, i: usize| (x + dz[i]).mul_f(0.5));
    let d_mul = time!(da, |x: DV, i: usize| x * dy[i]);
    let d_div = time!(da, |x: DV, i: usize| x / dy[i]);
    let d_fma = time!(da, |x: DV, i: usize| x.mul_f(0.5) * dy[i] + dz[i]);
    let d_dot = dot!(da, dy, DotAcc::zero());
    let q_add = time!(qa, |x: QV, i: usize| (x + qz[i]).mul_pwr2(0.5));
    let q_iadd = time!(qa, |x: QV, i: usize| x.ieee_add(qz[i]).mul_pwr2(0.5));
    let q_mul = time!(qa, |x: QV, i: usize| x * qy[i]);
    let q_amul = time!(qa, |x: QV, i: usize| x.accurate_mul(qy[i]));
    let q_mulf = time!(qa, |x: QV, i: usize| x.mul_v(fy[i]));
    let q_div = time!(qa, |x: QV, i: usize| x / qy[i]);
    let q_adiv = time!(qa, |x: QV, i: usize| x.accurate_div(qy[i]));
    let q_sqrt = time!(qa, |x: QV, i: usize| x.abs().sqrt() + qz[i].abs());
    let q_fma = time!(qa, |x: QV, i: usize| x.mul_pwr2(0.5) * qy[i] + qz[i]);
    let q_dot = dot!(qa, qy, QDotAcc::zero());
    let q_pow2 = time!(qa, |x: QV, _i: usize| x.mul_pwr2(0.5));
    let d_mulf = time!(da, |x: DV, _i: usize| x.mul_f(0.5));
    let row = |name: &str, f: f64, d: f64, q: f64| {
        println!(
            "  {name:<34} f64 {f:7.3}  dd {d:7.3}  qd {q:8.3}   qd/dd {:6.1}  dd/f64 {:5.1}",
            q / d,
            d / f
        )
    };
    row(
        "add (dd, qd: (a + b)/2 less the halving)",
        f_add,
        d_add - d_mulf,
        q_add - q_pow2,
    );
    row("mul", f_mul, d_mul, q_mul);
    row("div", f_div, d_div, q_div);
    row("a b + c, mul then add", f_fma, d_fma - d_mulf, q_fma - q_pow2);
    row("dot term (16-term sums, finished)", f_dot, d_dot, q_dot);
    println!("  qd only: accurate add {:.3}, accurate mul {q_amul:.3}, qd x f64 {q_mulf:.3}, accurate div {q_adiv:.3}, sqrt {:.3} (f64 sqrt {f_sqrt:.3})", q_iadd - q_pow2, q_sqrt - (q_add - q_pow2));
}

// -------------------------------------------------------------------------------------------------------------
// diagnostics of the two exceedances of the pre-registered thresholds (docs/QUAD_DOUBLE.md, section 3)
// -------------------------------------------------------------------------------------------------------------

/// QD's accurate add exactly as in QD 2.3 (qd_inline.h, ieee_add), for comparison with `QD::ieee_add`, which keeps
/// u + v where this keeps u when all parts are read with three emitted
fn ieee_add_qd_literal(a: QD, b: QD) -> QD {
    use crate::dd::quick_two_sum;
    use crate::qd::renorm4;
    let (a, b) = (a.x, b.x);
    let (mut i, mut j, mut k) = (0usize, 0usize, 0usize);
    let mut x = [0.0f64; 4];
    let (mut u, mut v);
    if a[i].abs() > b[j].abs() {
        u = a[i];
        i += 1;
    } else {
        u = b[j];
        j += 1;
    }
    if a[i].abs() > b[j].abs() {
        v = a[i];
        i += 1;
    } else {
        v = b[j];
        j += 1;
    }
    (u, v) = quick_two_sum(u, v);
    while k < 4 {
        if i >= 4 && j >= 4 {
            x[k] = u;
            if k < 3 {
                k += 1;
                x[k] = v;
            }
            break;
        }
        let t;
        if i >= 4 {
            t = b[j];
            j += 1;
        } else if j >= 4 || a[i].abs() > b[j].abs() {
            t = a[i];
            i += 1;
        } else {
            t = b[j];
            j += 1;
        }
        let (s, bb) = crate::dd::two_sum(v, t);
        let (s, aa) = crate::dd::two_sum(u, s);
        if aa != 0.0 && bb != 0.0 {
            u = aa;
            v = bb;
            x[k] = s;
            k += 1;
        } else if bb == 0.0 {
            v = aa;
            u = s;
        } else {
            u = s;
            v = bb;
        }
    }
    for kk in i..4 {
        x[3] += a[kk];
    }
    for kk in j..4 {
        x[3] += b[kk];
    }
    QD {
        x: renorm4(x[0], x[1], x[2], x[3]),
    }
}

/// QD_N samples (default 200000) of near-cancelling a + b (a + b = 2^-k a): the accurate add's relative error by
/// depth k, QD's algorithm as published and `QD::ieee_add`
#[test]
#[ignore]
fn qd_diag_accurate_add() {
    let n = env_usize("QD_N", 200000);
    let mut r = Rng::new(11);
    let bins = [1i64, 8, 16, 24, 32, 53, 106, 160, 261];
    let mut worst = vec![(0f64, 0f64, 0usize, 0usize); bins.len() - 1];
    for _ in 0..n {
        let e = r.int(-50, 50);
        let k = r.int(1, 260);
        let a = rand_dy(&mut r, e);
        let d = rand_dy(&mut r, e - k);
        let (qa, qb) = (qd_of(&a), qd_of(&a.neg().add(&d)));
        let x = qa.exact().add(&qb.exact());
        let e1 = ieee_add_qd_literal(qa, qb).exact().sub(&x).abs().ratio(&x) / unit();
        let e2 = qa.ieee_add(qb).exact().sub(&x).abs().ratio(&x) / unit();
        let bi = bins.iter().rposition(|&b| b <= k).unwrap().min(bins.len() - 2);
        let w = &mut worst[bi];
        w.0 = w.0.max(e1);
        w.1 = w.1.max(e2);
        w.2 += (e1 > 1.0) as usize;
        w.3 += 1;
    }
    println!("accurate add, a + b = 2^-k a ({n} samples): max relative error in units of 2^-209");
    for (i, w) in worst.iter().enumerate() {
        println!(
            "  k {:>3}..{:<3} n {:>6}: QD 2.3 {:>8}  ({} above 1 u);  QD::ieee_add {:>8}",
            bins[i],
            bins[i + 1] - 1,
            w.3,
            fmt_u(w.0),
            w.2,
            fmt_u(w.1)
        );
    }
}

/// The dot accumulator's error split: as built; its levels summed exactly (no finish); and with levels 3-4 replaced
/// by the exact sum of the level-3 increments (recomputed by a scalar copy of QdAcc::add_prod), which leaves only
/// the products' truncation; |error| / sum |a_i b_i| in units of 2^-209
#[test]
#[ignore]
fn qd_diag_accumulator() {
    use crate::dd::{two_prod, two_sum};
    let nsamp = env_usize("QD_N", 4000);
    for len in [16usize, 128, 512] {
        for cat in ["random", "wide"] {
            let mut r = Rng::new(5 + len as u64);
            let (mut m1, mut m2, mut m3, mut m4, mut m5, mut v1) = (0f64, 0f64, 0f64, 0f64, 0f64, Vec::new());
            for _ in 0..nsamp * 16 / len {
                let mut acc = QdAcc::zero();
                let mut lvl3 = Dy::zero();
                let (mut x, mut s) = (Dy::zero(), Dy::zero());
                for _ in 0..len {
                    let (ea, eb) = if cat == "wide" {
                        (r.int(-100, 100), r.int(-100, 100))
                    } else {
                        (r.int(-3, 3), r.int(-3, 3))
                    };
                    let (da, db) = (rand_dy(&mut r, ea), rand_dy(&mut r, eb));
                    let (qa, qb) = (qd_of(&da), qd_of(&db));
                    let t = qa.exact().mul(&qb.exact());
                    x = x.add(&t);
                    s = s.add(&t.abs());
                    // the level-3 increment of QdAcc::add_prod, recomputed (same operations)
                    let (a, b) = (qa.x, qb.x);
                    let (p00, e00) = two_prod(a[0], b[0]);
                    let (p01, e01) = two_prod(a[0], b[1]);
                    let (p10, e10) = two_prod(a[1], b[0]);
                    let (p02, e02) = two_prod(a[0], b[2]);
                    let (p11, e11) = two_prod(a[1], b[1]);
                    let (p20, e20) = two_prod(a[2], b[0]);
                    let r3 = a[3].mul_add(b[0], a[2].mul_add(b[1], a[1].mul_add(b[2], a[0] * b[3])));
                    let (_, t0) = two_sum(acc.s[0], p00);
                    let (x1, y1) = two_sum(p01, p10);
                    let (x2, y2) = two_sum(e00, t0);
                    let (x3, y3) = two_sum(x1, x2);
                    let (_, y4) = two_sum(acc.s[1], x3);
                    let (z1, w1) = two_sum(p02, p20);
                    let (z2, w2) = two_sum(p11, e01);
                    let (z3, w3) = two_sum(e10, y1);
                    let (z4, w4) = two_sum(y2, y3);
                    let (z5, w5) = two_sum(z1, z2);
                    let (z6, w6) = two_sum(z3, z4);
                    let (z7, w7) = two_sum(z5, z6);
                    let (z8, w8) = two_sum(z7, y4);
                    let (_, w9) = two_sum(acc.s[2], z8);
                    lvl3 = lvl3.add(&Dy::sum(&[w1, w2, w3, w4, w5, w6, w7, w8, w9, r3, e02, e11, e20]));
                    acc = acc.add_prod(qa, qb);
                }
                let e_built = acc.finish().exact().sub(&x).abs().ratio(&s) / unit();
                // levels 0-2 as built, level 3 exact, summed exactly: the error left is the products' truncation
                let ex = Dy::sum(&acc.s[..3]).add(&lvl3);
                let e_exact3 = ex.sub(&x).abs().ratio(&s) / unit();
                // the four levels as built, summed exactly (no finish): the error left is level 3's rounding
                let e_nofin = Dy::sum(&acc.s).sub(&x).abs().ratio(&s) / unit();
                m3 = m3.max(e_nofin);
                m4 = m4.max(Dy::from_f64(acc.s[3]).ratio(&s) / unit());
                m5 = m5.max(Dy::from_f64(acc.s[4]).ratio(&s) / unit());
                m1 = m1.max(e_built);
                m2 = m2.max(e_exact3);
                v1.push(e_built);
            }
            let p = pct(&mut v1, 0.999);
            println!(
                "dot n={len:<4} {cat:<6}: as built max {} (99.9% {}) u; levels summed exactly, no finish {} u; levels 3-4 exact, no finish {} u; max |s3| {} u, |s4| {} u; threshold (8 + n)/8 = {}",
                fmt_u(m1),
                fmt_u(p),
                fmt_u(m3),
                fmt_u(m2),
                fmt_u(m4),
                fmt_u(m5),
                (8 + len) as f64 / 8.0
            );
        }
    }
}
