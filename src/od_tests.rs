//! Tests of the octo-double arithmetic (`od`, `ov`) against exact dyadic arithmetic (`exact`), which shares no code
//! with the algorithms under test: the inputs are built from exact random values by greedy rounding to eight parts,
//! not by octo-double arithmetic, and every reference result is exact.
//!
//! ```text
//! cargo test --release --lib od_                                  accuracy, scalar/8-lane agreement, decimal I/O
//! cargo test --release --lib --features mutate od_controls        every deliberate breakage must fail a check
//! ```
//! OD_N sets the samples per operation and input category (default 2000), OD_SEED the seed (default 1),
//! OD_REPORT=1 prints the tables. The thresholds, in units of 2^-418 (`OD::EPS`), were fixed before the first run:
//! 1 for the adds (relative to |a| + |b|, Cray-style, as QD's `+`), the multiply and od x f64, 2 for the divide and
//! the square root, and (8 + n)/8 relative to sum |a_i b_i| for dot products of n terms: the quad-double tests'
//! (`qd_tests`) thresholds of the accurate operations.
use crate::dd::DD;
use crate::exact::{BigU, Dy};
use crate::native::{ODotAcc, OV, V8};
#[cfg(feature = "mutate")]
use crate::od::mutate;
use crate::od::{OdAcc, OD};
use crate::qd::QD;
use crate::qd_tests::Rng;
use std::cmp::Ordering;

/// 2^-418, the unit of the error tables
fn unit() -> f64 {
    OD::EPS
}

/// the environment variable k as a number, or d
fn env_usize(k: &str, d: usize) -> usize {
    std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d)
}

/// OD_REPORT=1: print the tables
fn report() -> bool {
    std::env::var("OD_REPORT").map(|v| v == "1").unwrap_or(false)
}

/// select mutation id (0 = none) for the current thread
fn set_mutation(id: u32) {
    #[cfg(feature = "mutate")]
    mutate::set(id);
    #[cfg(not(feature = "mutate"))]
    assert_eq!(id, 0, "mutations need the mutate feature");
}

/// a random bit
fn coin(r: &mut Rng) -> bool {
    r.next() & 1 == 1
}

// -------------------------------------------------------------------------------------------------------------
// random exact inputs
// -------------------------------------------------------------------------------------------------------------

/// exact random value ±(1 + f)·2^e, f a random 511-bit fraction (more bits than eight parts hold)
fn rand_dy(r: &mut Rng, e: i64) -> Dy {
    let mut m: Vec<u64> = (0..8).map(|_| r.next()).collect();
    m[7] |= 1u64 << 63;
    Dy {
        neg: coin(r),
        m: BigU(m),
        e: e - 511,
    }
}

/// rand_dy with the binade drawn from lo..=hi
fn rde(r: &mut Rng, lo: i64, hi: i64) -> Dy {
    let e = r.int(lo, hi);
    rand_dy(r, e)
}

/// sum of 1-8 small integers k_i 2^(e - g_i) with random gaps (exact sums and zero error terms are common)
fn sparse_dy(r: &mut Rng, e: i64) -> Dy {
    let n = r.int(1, 8);
    let mut v = Dy::zero();
    let mut g = 0;
    for i in 0..n {
        let k = r.int(1, 2000) * if coin(r) { 1 } else { -1 };
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
    const J: [i64; 16] = [0, 1, 52, 53, 54, 105, 106, 159, 212, 265, 318, 371, 423, 424, 425, 430];
    let j = if coin(r) {
        J[r.int(0, 15) as usize]
    } else {
        r.int(1, 440)
    };
    let p = Dy::from_f64(1.0).ldexp(k);
    if j == 0 {
        return if coin(r) { p } else { p.neg() };
    }
    let mut d = rand_dy(r, k - j);
    if coin(r) {
        d = d.ldexp(-1);
    }
    let v = p.add(&d);
    if coin(r) {
        v
    } else {
        v.neg()
    }
}

/// eight parts by greedy round-to-nearest (x0 = RN(v), x1 = RN(v - x0), ...): a normalized octo-double built
/// without any octo-double arithmetic (a lower part that rounds to zero is +0 and ends the parts)
fn greedy8(d: &Dy) -> [f64; 8] {
    let mut r = d.clone();
    let mut x = [0.0; 8];
    for (i, xi) in x.iter_mut().enumerate() {
        let c = r.to_f64();
        if c == 0.0 || !c.is_finite() {
            if i == 0 {
                *xi = c;
            }
            break;
        }
        *xi = c;
        r = r.sub(&Dy::from_f64(c));
    }
    x
}

/// a dyadic as eight greedy parts
fn od_of(d: &Dy) -> OD {
    OD { x: greedy8(d) }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Add,
    Mul,
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

/// the category's name in the tables
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
fn gen(r: &mut Rng, kind: Kind, cat: Cat) -> (OD, OD) {
    use Cat::*;
    use Kind::*;
    let one = Dy::from_f64(1.0);
    if cat == Computed {
        // operands produced by octo-double arithmetic (renormalized parts, not greedy ones): x y (1/y); for the adds
        // b = -(x y (1/y)) or b = -(a + d) (|d| = 2^-k |a|), so a + b is small with misaligned parts, as in a
        // residual's subtraction of two nearly equal values computed along different routes
        let route = |r: &mut Rng, x: OD| -> OD {
            let y = od_of(&rde(r, -2, 2));
            (x * y) * (OD::ONE / y)
        };
        let a = od_of(&rde(r, -20, 20));
        return match kind {
            Add => {
                if coin(r) {
                    (a, -route(r, a))
                } else {
                    let k = r.int(1, 440);
                    let d = od_of(&rand_dy(r, -k)) * a;
                    (a, -(a + d))
                }
            }
            Sqrt => (route(r, a).abs(), OD::ONE),
            _ => {
                let b = od_of(&rde(r, -20, 20));
                (route(r, a), route(r, b))
            }
        };
    }
    let (a, b): (Dy, Dy) = match (cat, kind) {
        (Wide, Sqrt) => (rde(r, -800, 800).abs(), one),
        (Wide, Add) => (rde(r, -400, 400), rde(r, -400, 400)),
        // products and quotients within 2^-600..2^600, where all eight parts of the result are normal
        (Wide, _) => (rde(r, -300, 300), rde(r, -300, 300)),
        // a + b small: b = -a + d with |d| = 2^-k |a|
        (Cancel, Add) => {
            let e = r.int(-50, 50);
            let a = rand_dy(r, e);
            let d = rde(r, e - 460, e - 1);
            let b = a.neg().add(&d);
            (a, b)
        }
        // products near 1: (1 + d1)(1 - d2)
        (Cancel, Mul) => {
            let d1 = rde(r, -440, -1).abs();
            let d2 = rde(r, -440, -1).abs();
            (one.add(&d1), one.sub(&d2))
        }
        // quotients near 1: b = a (1 + d)
        (Cancel, Div) => {
            let a = rde(r, -50, 50);
            let d = rde(r, -440, -1);
            let b = a.add(&a.mul(&d));
            (a, b)
        }
        (Cancel, Sqrt) => (one.add(&rde(r, -440, -1)), one),
        (Overflow, Add) => (rde(r, 1000, 1021), rde(r, 900, 1021)),
        (Overflow, Mul) => {
            let t = r.int(990, 1020);
            let ea = r.int(0, 1020);
            (rand_dy(r, ea), rand_dy(r, t - ea))
        }
        (Overflow, Div) => {
            if coin(r) {
                (rde(r, 990, 1020), rde(r, -1, 0))
            } else {
                (rde(r, 990, 1021), rde(r, 990, 1021))
            }
        }
        (Overflow, Sqrt) => (rde(r, 990, 1022).abs(), one),
        // the parts reach the subnormals: the eighth part is near 2^-1074 well before the first is
        (Underflow, Add) => (rde(r, -1020, -620), rde(r, -1020, -620)),
        (Underflow, Mul) => {
            let t = r.int(-1020, -620);
            let ea = r.int(-500, -300);
            (rand_dy(r, ea), rand_dy(r, t - ea))
        }
        (Underflow, Div) => {
            let t = r.int(-1020, -620);
            let eb = r.int(-50, 100);
            (rand_dy(r, t + eb), rand_dy(r, eb))
        }
        (Underflow, Sqrt) => (rde(r, -1070, -620).abs(), one),
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
    (od_of(&a), od_of(&b))
}

// -------------------------------------------------------------------------------------------------------------
// operations, their references and thresholds
// -------------------------------------------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Op {
    Add,
    AddF,
    Mul,
    MulF,
    Div,
    Sqrt,
}

const OPS: [Op; 6] = [Op::Add, Op::AddF, Op::Mul, Op::MulF, Op::Div, Op::Sqrt];

/// the operation's name in the tables
fn op_name(op: Op) -> &'static str {
    match op {
        Op::Add => "add",
        Op::AddF => "od + f64",
        Op::Mul => "mul",
        Op::MulF => "od x f64",
        Op::Div => "div",
        Op::Sqrt => "sqrt",
    }
}

/// the kind of exact reference the operation is checked against
fn op_kind(op: Op) -> Kind {
    match op {
        Op::Add | Op::AddF => Kind::Add,
        Op::Mul | Op::MulF => Kind::Mul,
        Op::Div => Kind::Div,
        Op::Sqrt => Kind::Sqrt,
    }
}

/// Cray-style measure |error| / (|a| + |b|) instead of the relative error
fn op_cray(op: Op) -> bool {
    matches!(op, Op::Add | Op::AddF)
}

/// pass threshold in units of 2^-418 (fixed before the runs)
fn op_thr(op: Op) -> f64 {
    match op {
        Op::Add | Op::AddF | Op::Mul | Op::MulF => 1.0,
        Op::Div | Op::Sqrt => 2.0,
    }
}

/// the scalar operation
fn apply_s(op: Op, a: OD, b: OD) -> OD {
    match op {
        Op::Add => a + b,
        Op::AddF => a.add_f(b.x[0]),
        Op::Mul => a * b,
        Op::MulF => a.mul_f(b.x[0]),
        Op::Div => a / b,
        Op::Sqrt => a.sqrt(),
    }
}

/// the 8-lane operation
fn apply_v(op: Op, a: OV, b: OV) -> OV {
    match op {
        Op::Add => a + b,
        Op::AddF => a.add_v(b.c[0]),
        Op::Mul => a * b,
        Op::MulF => a.mul_v(b.c[0]),
        Op::Div => a / b,
        Op::Sqrt => a.sqrt(),
    }
}

/// the second operand as the operation sees it
fn b_exact(op: Op, b: OD) -> Dy {
    match op {
        Op::AddF | Op::MulF => Dy::from_f64(b.x[0]),
        _ => b.exact(),
    }
}

/// (err, scale, rel, allow): the check is err <= thr·u·scale + allow, the reported value err / scale; rel is the
/// relative error of the result (= err / scale except for the Cray-style measure). In the near-underflow inputs
/// allow is 16·2^-1074 on the result (its parts cannot go below 2^-1074), carried to err as in `qd_tests`.
fn exact_err(op: Op, a: OD, b: OD, r: OD, under: bool) -> (Dy, Dy, f64, Dy) {
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
        Kind::Mul => {
            let x = ae.mul(&be);
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

/// err <= thr 2^-418 scale + allow, exactly
fn within(err: &Dy, scale: &Dy, thr: f64, allow: &Dy) -> bool {
    let lim = scale.mul(&Dy::from_f64(thr * unit())).add(allow);
    err.cmp_abs(&lim) != Ordering::Greater
}

/// every part the same bits (any NaN equal to any NaN)
fn same(a: OD, b: OD) -> bool {
    a.x.iter()
        .zip(b.x.iter())
        .all(|(x, y)| x.to_bits() == y.to_bits() || (x.is_nan() && y.is_nan()))
}

/// FNV-1a over the bits of the parts
fn fnv(h: &mut u64, x: OD) {
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
struct Res {
    what: String,
    cat: &'static str,
    n: usize,
    /// max and 99.9th percentile of the check's measure, in units of 2^-418
    max: f64,
    p999: f64,
    /// max of the relative error (= the measure except for the Cray-style adds), in units of 2^-418
    rel_max: f64,
    thr: f64,
    /// samples outside the bound
    fails: usize,
    /// lanes whose 8-lane result differs from the scalar one in any bit
    mism: usize,
    digest: u64,
}

impl Res {
    /// no sample outside the bound and no lane different from the scalar result
    fn ok(&self) -> bool {
        self.fails == 0 && self.mism == 0
    }
}

/// the q-quantile of v (sorted in place)
fn pct(v: &mut [f64], q: f64) -> f64 {
    if v.is_empty() {
        return 0.0;
    }
    v.sort_by(|a, b| a.partial_cmp(b).unwrap_or(Ordering::Equal));
    v[((v.len() - 1) as f64 * q).floor() as usize]
}

/// a number for the tables
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

/// print the rows of an accuracy table
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
fn inputs(op: Op, cat: Cat, n: usize, seed: u64) -> Vec<(OD, OD)> {
    let mut r = Rng::new(seed ^ ((op as u64) << 32) ^ ((cat as u64) << 40) ^ 0x0c70);
    (0..n).map(|_| gen(&mut r, op_kind(op), cat)).collect()
}

/// scalar and 8-lane results of one operation on the inputs
fn results(op: Op, inp: &[(OD, OD)]) -> (Vec<OD>, Vec<OD>) {
    let rs: Vec<OD> = inp.iter().map(|&(a, b)| apply_s(op, a, b)).collect();
    let mut rv = Vec::with_capacity(inp.len());
    for c in inp.chunks(8) {
        let mut la = [OD::ZERO; 8];
        let mut lb = [OD::ONE; 8];
        for (j, &(a, b)) in c.iter().enumerate() {
            la[j] = a;
            lb[j] = b;
        }
        let out = apply_v(op, OV::from_lanes(&la), OV::from_lanes(&lb)).lanes();
        rv.extend_from_slice(&out[..c.len()]);
    }
    (rs, rv)
}

/// accuracy and agreement of every operation in every category, with mutation `id` active during the arithmetic
fn run_ops(n: usize, seed: u64, id: u32) -> Vec<Res> {
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

/// accuracy of ODotAcc / OdAcc on dot products of length len (8 per sample, one per lane): |error| / sum |a_i b_i|
fn run_acc(n: usize, seed: u64, id: u32) -> Vec<Res> {
    let mut out = Vec::new();
    for len in [1usize, 4, 16, 64] {
        for (ci, cat) in ACC_CATS.iter().enumerate() {
            let mut r = Rng::new(seed ^ ((len as u64) << 20) ^ ((ci as u64) << 30) ^ 0x0acc);
            let thr = (8.0 + len as f64) / 8.0;
            let (mut ms, mut fails, mut mism, mut rel_max) = (Vec::new(), 0, 0, 0f64);
            let mut digest = 0xcbf29ce484222325u64;
            let nsamp = ((n / len.clamp(1, 16)).max(8)) / 8 * 8;
            for _ in 0..nsamp / 8 {
                let mut a = vec![[OD::ZERO; 8]; len];
                let mut b = vec![[OD::ZERO; 8]; len];
                for lane in 0..8 {
                    for i in 0..len {
                        let (x, y) = match *cat {
                            "wide" => (rde(&mut r, -100, 100), rde(&mut r, -100, 100)),
                            "cancel" if i >= len / 2 && len > 1 => {
                                // a_i b_i = -(a_k b_k)(1 + d): pairs that nearly cancel
                                let k = i - len / 2;
                                let ak = a[k][lane].exact();
                                let d = rde(&mut r, -400, -1);
                                (ak.neg().add(&ak.mul(&d)), b[k][lane].exact())
                            }
                            _ => (rde(&mut r, -3, 3), rde(&mut r, -3, 3)),
                        };
                        a[i][lane] = od_of(&x);
                        b[i][lane] = od_of(&y);
                    }
                }
                let plain = |i: usize| *cat == "mixed" && i % 4 == 3;
                set_mutation(id);
                let mut acc = ODotAcc::zero();
                for i in 0..len {
                    acc = if plain(i) {
                        acc.add(OV::from_lanes(&a[i]))
                    } else {
                        acc.add_prod(OV::from_lanes(&a[i]), OV::from_lanes(&b[i]))
                    };
                }
                let rv = acc.finish().lanes();
                let rs: Vec<OD> = (0..8)
                    .map(|lane| {
                        let mut s = OdAcc::zero();
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
// conversions, comparisons and decimal input/output
// -------------------------------------------------------------------------------------------------------------

/// ulp of a finite nonzero f64
fn ulp(x: f64) -> Dy {
    let e = ((x.to_bits() >> 52) & 0x7ff) as i64;
    Dy::from_f64(1.0).ldexp(if e == 0 { -1074 } else { e - 1075 })
}

/// a decimal digit string's value times 10^(e10 + sh) as an exact integer Dy (e10 + sh >= 0)
fn dec_scaled(neg: bool, digits: &str, e10: i64, sh: i64) -> Dy {
    assert!(e10 + sh >= 0);
    let m = BigU::from_dec(digits).mul(&BigU::pow_small(10, (e10 + sh) as u64));
    Dy {
        neg: neg && !m.is_zero(),
        m,
        e: 0,
    }
}

/// 10^k, exactly
fn pow10(k: i64) -> Dy {
    Dy {
        neg: false,
        m: BigU::pow_small(10, k as u64),
        e: 0,
    }
}

/// a one-row result
fn row(what: &str, cat: &'static str, n: usize, fails: usize, mism: usize) -> Res {
    Res {
        what: what.into(),
        cat,
        n,
        max: fails as f64,
        p999: 0.0,
        rel_max: 0.0,
        thr: 0.0,
        fails,
        mism,
        digest: 0,
    }
}

/// decimal parsing and printing, round trips, the conversions to DD, QD and f64, and the order, against exact arithmetic, with mutation id active
fn run_io(n: usize, seed: u64, id: u32) -> Vec<Res> {
    let mut out = Vec::new();
    let mut r = Rng::new(seed ^ 0x0d10);
    // parsing: random decimals of 1-160 digits, exponents -250..300, greedy round-to-nearest checked exactly
    let mut greedy_fails = 0;
    for _ in 0..n {
        let nd = r.int(1, 160) as usize;
        let mut d = String::new();
        d.push((b'1' + (r.next() % 9) as u8) as char);
        for _ in 1..nd {
            d.push((b'0' + (r.next() % 10) as u8) as char);
        }
        let e10 = r.int(-250 - nd as i64, 300 - nd as i64);
        let neg = coin(&mut r);
        let s = format!("{}{}e{}", if neg { "-" } else { "" }, d, e10);
        set_mutation(id);
        let q = OD::parse(&s).unwrap();
        set_mutation(0);
        let sh = (-e10).max(0);
        let v = dec_scaled(neg, &d, e10, sh);
        let err = q.exact().mul(&pow10(sh)).sub(&v).abs();
        // |q - v| <= ulp(x7)/2 when all eight parts are used, else at most half the least subnormal (a remainder
        // that rounds to zero ends the parts); a zero lower part is +0
        let last = q.x.iter().rposition(|c| *c != 0.0).unwrap();
        let sub = Dy::from_f64(1.0).ldexp(-1075);
        let bound = if last == 7 { ulp(q.x[7]).ldexp(-1) } else { sub }.mul(&pow10(sh));
        if err.cmp_abs(&bound) == Ordering::Greater || q.x[1..].iter().any(|v| v.to_bits() == (-0.0f64).to_bits()) {
            greedy_fails += 1;
        }
    }
    out.push(row("parse", "greedy RN", n, greedy_fails, 0));

    // printing: correctly rounded, exactly checked; round trips through all the exact digits and through 140
    // (424 bits and the gaps between the parts' bits, about 7 on average), where every part is normal
    let (mut print_fails, mut np, mut rt_exact, mut rt140) = (0, 0, 0, 0);
    for _ in 0..n / 4 {
        let x = od_of(&rde(&mut r, -1000, 1000));
        for digits in [1usize, 17, 64, 126, 128, 130, 150] {
            np += 1;
            let s = x.to_sci(digits);
            let (neg, rest) = match s.strip_prefix('-') {
                Some(t) => (true, t),
                None => (false, s.as_str()),
            };
            let p = rest.find('e').unwrap();
            let e: i64 = rest[p + 1..].parse().unwrap();
            let m: String = rest[..p].chars().filter(|c| *c != '.').collect();
            let e = e - (m.len() as i64 - 1);
            let sh = (1 - e).max(0);
            let xs = x.exact().mul(&pow10(sh));
            let ds = dec_scaled(neg, &m, e, sh);
            let half = dec_scaled(false, "5", e - 1, sh);
            let c = xs.sub(&ds).abs().cmp_abs(&half);
            let even = BigU::from_dec(&m).divrem_small(2).1 == 0;
            if c == Ordering::Greater || (c == Ordering::Equal && !even) || m.len() != digits || neg != x.exact().neg {
                print_fails += 1;
            }
        }
        let x = od_of(&rde(&mut r, -500, 500));
        let (_, dm, _) = x.exact().to_decimal();
        let all = dm.to_dec().trim_end_matches('0').len().max(1);
        set_mutation(id);
        let y = OD::parse(&x.to_sci(all)).unwrap();
        let y140 = OD::parse(&x.to_sci(140)).unwrap();
        set_mutation(0);
        rt_exact += !same(x, y) as usize;
        rt140 += !same(x, y140) as usize;
    }
    out.push(row("print", "rounding", np, print_fails, 0));
    out.push(row("round trip", "exact", n / 4, rt_exact, 0));
    out.push(row("round trip", "140 digits", n / 4, rt140, 0));

    // conversions: to_dd within 2^-105 relative, to_qd within 2^-210, to_f64 within one ulp; the lanes bit for bit
    let (mut fails, mut conv_mism) = (0, 0);
    let mut lanes = Vec::new();
    for _ in 0..n {
        let x = od_of(&rde(&mut r, -900, 900));
        let xv = x.exact();
        let (d, q, f) = (x.to_dd(), x.to_qd(), x.to_f64());
        let tol = |k| xv.abs().ldexp(k);
        if Dy::sum(&[d.hi, d.lo]).sub(&xv).abs().cmp_abs(&tol(-105)) == Ordering::Greater {
            fails += 1;
        }
        if q.exact().sub(&xv).abs().cmp_abs(&tol(-210)) == Ordering::Greater {
            fails += 1;
        }
        if Dy::from_f64(f).sub(&xv).abs().cmp_abs(&ulp(f)) == Ordering::Greater {
            fails += 1;
        }
        if OD::from_dd(d).x[..2] != [d.hi, d.lo] || OD::from_qd(q).x[..4] != q.x || OD::from_qd(q).x[4..] != [0.0; 4] {
            fails += 1;
        }
        lanes.push((x, d, q, f));
    }
    for c in lanes.as_chunks::<8>().0 {
        let v = OV::from_lanes(&std::array::from_fn(|j| c[j].0));
        let (dv, qv, fv) = (v.to_dv(), v.to_qv(), v.to_v8().to_array());
        for j in 0..8 {
            let (dj, qj) = (dv.lane(j), qv.lane(j));
            if dj.hi.to_bits() != c[j].1.hi.to_bits()
                || dj.lo.to_bits() != c[j].1.lo.to_bits()
                || qj.x.map(f64::to_bits) != c[j].2.x.map(f64::to_bits)
                || fv[j].to_bits() != c[j].3.to_bits()
            {
                conv_mism += 1;
            }
        }
    }
    out.push(row("to_dd, to_qd, to_f64", "random", n, fails, conv_mism));

    // comparisons: the lexicographic order against the exact one, on pairs that differ in one part (often a low
    // one), scalar and lanes
    let (mut cmp_fails, mut cmp_mism) = (0, 0);
    let mut pairs = Vec::new();
    for _ in 0..n {
        let a = od_of(&rde(&mut r, -50, 50));
        let b = match r.int(0, 3) {
            0 => od_of(&rde(&mut r, -50, 50)),
            1 => a,
            _ => {
                let k = r.int(0, 7) as usize;
                let mut b = a;
                b.x[k] = f64::from_bits(if coin(&mut r) {
                    b.x[k].to_bits() + 1
                } else {
                    b.x[k].to_bits() - 1
                });
                OD::new(b.x)
            }
        };
        let want = a.exact().sub(&b.exact());
        let ord = if want.is_zero() {
            Ordering::Equal
        } else if want.neg {
            Ordering::Less
        } else {
            Ordering::Greater
        };
        if a.partial_cmp(&b) != Some(ord) {
            cmp_fails += 1;
        }
        pairs.push((a, b));
    }
    for c in pairs.as_chunks::<8>().0 {
        let va = OV::from_lanes(&std::array::from_fn(|j| c[j].0));
        let vb = OV::from_lanes(&std::array::from_fn(|j| c[j].1));
        let m = [va.lt(vb), va.le(vb), va.gt(vb), va.ge(vb), va.eq(vb)].map(|m| m.bits());
        for j in 0..8 {
            let (a, b) = c[j];
            let want = [a < b, a <= b, a > b, a >= b, a == b];
            for (mk, w) in m.iter().zip(want) {
                if (mk >> j & 1 == 1) != w {
                    cmp_mism += 1;
                }
            }
        }
    }
    out.push(row("compare", "exact order", n, cmp_fails, cmp_mism));
    out
}

/// print the rows of the decimal, conversion and order checks
fn print_rows(title: &str, rs: &[Res]) {
    println!("{title}");
    for r in rs {
        println!(
            "  {} ({}): {} of {} fail, {} lane mismatches",
            r.what, r.cat, r.fails, r.n, r.mism
        );
    }
}

// -------------------------------------------------------------------------------------------------------------
// the tests
// -------------------------------------------------------------------------------------------------------------

/// constants, decimal digits of pi, powers, special values, the power-of-two scaling and the conversions
#[test]
fn od_constants_and_special_values() {
    assert_eq!(OD::EPS, 2f64.powi(-418));
    assert_eq!(
        format!("{:.124}", OD::ONE / OD::from_f64(3.0)),
        format!("3.{}e-01", "3".repeat(124))
    );
    // 140 digits of pi parse to parts whose first four are QD's pi (both greedy), and print back
    let pi = "3.14159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798\
              21480865132823066470938446095505822317253594";
    let p = OD::parse(pi).unwrap();
    assert_eq!(&p.x[..4], &QD::PI.x);
    assert_eq!(p.to_sci(126), format!("{}e+00", &pi[..127]));
    assert_eq!(OD::from_f64(-0.0).to_sci(3), "-0.00e+00");
    assert_eq!(OD::parse("1e400").unwrap().x[0], f64::INFINITY);
    assert!(same(OD::parse("-0").unwrap(), OD::from_f64(-0.0)));
    // powi and recip against repeated products, sqrt against its square
    let x = OD::parse("1.0000001234567890123456789").unwrap();
    let q = x * x * x * x * x;
    assert!((x.powi(5) - q).abs().to_f64() < 1e-123, "{}", (x.powi(5) - q).to_f64());
    assert!(((x.powi(-3) * x.powi(3)) - OD::ONE).abs().to_f64() < 1e-123);
    let two = OD::from_f64(2.0);
    assert!((two.sqrt() * two.sqrt() - two).abs().to_f64() < 1e-124);
    assert_eq!(two.recip().x, OD::from_f64(0.5).x);
    // zeros, negatives, infinities
    assert!(same(OD::ZERO.sqrt(), OD::ZERO));
    assert!((-two).sqrt().x.iter().any(|v| v.is_nan()));
    assert!((OD::from_f64(f64::INFINITY) + two).x[0].is_infinite());
    assert!(same(-OD::ZERO, OD::from_f64(-0.0)));
    assert!((-OD::ONE).x[1..].iter().all(|v| v.to_bits() == 0));
    // mul_pwr2 is exact and bitwise mul_f by the power of two
    let y = od_of(
        &Dy::from_f64(1.0)
            .add(&Dy::from_f64(1.0).ldexp(-300))
            .add(&Dy::from_f64(3.0).ldexp(-400)),
    );
    assert!(same(y.mul_pwr2(0.25), y.mul_f(0.25)));
    assert!(same(y.mul_pwr2(2f64.powi(-600)).mul_pwr2(2f64.powi(600)), y));
    // conversions back and forth
    let d = DD::new(1.0, 2f64.powi(-60));
    assert_eq!(OD::from_dd(d).to_dd(), d);
    assert_eq!(OD::from_qd(QD::PI).to_qd().x, QD::PI.x);
    assert_eq!(p.to_f64(), std::f64::consts::PI);
    // the parts of slices round trip
    let v = vec![p, x, y];
    let parts = crate::od::to_parts(&v);
    let back = crate::od::from_parts(std::array::from_fn(|k| &parts[k][..]));
    assert!(v.iter().zip(&back).all(|(a, b)| same(*a, *b)));
}

/// every operation in every input category against exact arithmetic, and the lanes against the scalar type
#[test]
fn od_accuracy() {
    let n = env_usize("OD_N", 2000) / 8 * 8;
    let seed = env_usize("OD_SEED", 1) as u64;
    let rs = run_ops(n, seed, 0);
    let mut digest = 0xcbf29ce484222325u64;
    for r in &rs {
        digest ^= r.digest;
        digest = digest.wrapping_mul(0x100000001b3);
    }
    if report() {
        print_table(
            &format!("octo-double accuracy (units of 2^-418; n per row; isa {})", V8::ISA),
            &rs,
        );
    }
    println!("od digest {digest:016x} (n {n}, seed {seed}, isa {})", V8::ISA);
    let bad: Vec<&Res> = rs.iter().filter(|r| !r.ok()).collect();
    assert!(bad.is_empty(), "{} rows fail: {:?}", bad.len(), bad);
}

/// the dot accumulators against exact sums, 1 to 64 terms
#[test]
fn od_accumulator() {
    let n = env_usize("OD_N", 2000) / 8 * 8;
    let seed = env_usize("OD_SEED", 1) as u64;
    let rs = run_acc(n / 4, seed, 0);
    if report() {
        print_table(
            "dot accumulator: |error| / sum |a_i b_i| (units of 2^-418); threshold (8 + n)/8",
            &rs,
        );
    }
    let bad: Vec<&Res> = rs.iter().filter(|r| !r.ok()).collect();
    assert!(bad.is_empty(), "{bad:?}");
}

/// decimal input and output, the conversions and the order, exactly
#[test]
fn od_decimal_io_conversions_and_order() {
    let n = env_usize("OD_N", 2000);
    let seed = env_usize("OD_SEED", 1) as u64;
    let rs = run_io(n, seed, 0);
    if report() {
        print_rows("decimal input/output, conversions and comparisons", &rs);
    }
    let bad: Vec<&Res> = rs.iter().filter(|r| !r.ok()).collect();
    assert!(bad.is_empty(), "{bad:?}");
}

/// Every deliberate breakage (od::mutate) must make at least one check fail.
#[cfg(feature = "mutate")]
#[test]
fn od_controls() {
    let n = env_usize("OD_N", 400) / 8 * 8;
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
            "control {id:2} {:<52} fires: {:>3} rows fail, worst {} u, {} lane mismatches; e.g. {}",
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
