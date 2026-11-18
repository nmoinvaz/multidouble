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
//! the square root: the quad-double tests' (`qd_tests`) thresholds of the accurate operations. Dot products of n
//! terms are checked against the accumulator's proven bound, (|Z| + c_n W) u^8 with W = sum |a_i b_i| (`acc_thr`).
//!
//! The adds, the multiply and od x f64 have a proven bound, u^8 (1 + 2^-14) with u = 2^-53, which is 1/64 unit and
//! holds for operands on the ladder |a_i| <= 2^(-52 i) |a_0| without underflow (`proven`). Every input within those
//! hypotheses is checked against it too (`PROVEN_THR`), and `od_worst_case_inputs` reaches it. Random inputs stay
//! near 10^-4 units, the ladder category's inputs included, because the error is set by the result's parts.
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
    Gap,
    Ladder,
}

/// the categories whose results' bits `OD_DIGEST` pins and whose results' parts do not overlap
const CATS: [Cat; 7] = [
    Cat::Wide,
    Cat::Cancel,
    Cat::Overflow,
    Cat::Underflow,
    Cat::Pow2,
    Cat::Sparse,
    Cat::Computed,
];

/// every category of the accuracy checks: `CATS`, and the gap and ladder categories, whose results' bits `GAP_DIGEST`
/// and `LADDER_DIGEST` pin
const ALL_CATS: [Cat; 9] = [
    Cat::Wide,
    Cat::Cancel,
    Cat::Overflow,
    Cat::Underflow,
    Cat::Pow2,
    Cat::Sparse,
    Cat::Computed,
    Cat::Gap,
    Cat::Ladder,
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
        Cat::Gap => "gap",
        Cat::Ladder => "ladder",
    }
}

/// a value with a part far below the one above it: x0 + x1 with x1 2^-60 to 2^-400 below x0, or greedy parts with
/// those below the first zeroed at random (zero parts between nonzero ones)
fn gapped(r: &mut Rng) -> OD {
    let e = r.int(-20, 20);
    let mut x = greedy8(&rand_dy(r, e));
    if coin(r) {
        let g = r.int(60, 400);
        x = [x[0], rand_dy(r, e - g).to_f64(), 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
    } else {
        for xi in x.iter_mut().skip(1) {
            if coin(r) {
                *xi = 0.0;
            }
        }
    }
    OD { x }
}

/// A value whose parts sit near the top of the ladder that the proven bounds allow, |x_i| from 1/2 to 1 ulp of the
/// part above, signs at random. Greedy parts sit about 2^-8 lower over eight parts, so their products' order-8
/// terms are far below u^8 |ab|, where this value's are a few u^8 |ab|, as in the worst case.
fn topped(r: &mut Rng) -> OD {
    let mut x = [0.0; 8];
    let e = r.int(-20, 20);
    x[0] = rand_dy(r, e).to_f64();
    for i in 1..8 {
        // m in [1/2, 1) with 53 bits, or 1 (a part of a whole ulp) one time in eight
        let m = if r.int(0, 7) == 0 {
            1.0
        } else {
            0.5 + (r.next() >> 12) as f64 * 2f64.powi(-53)
        };
        let s = if coin(r) { -m } else { m };
        x[i] = s * ulp(x[i - 1]).to_f64();
    }
    OD { x }
}

/// one input pair (a, b) for an operation of the given kind (b unused by sqrt)
fn gen(r: &mut Rng, kind: Kind, cat: Cat) -> (OD, OD) {
    use Cat::*;
    use Kind::*;
    let one = Dy::from_f64(1.0);
    if cat == Ladder {
        let a = topped(r);
        return match kind {
            Sqrt => (a.abs(), OD::ONE),
            _ => (a, topped(r)),
        };
    }
    if cat == Gap {
        // a product of a gapped value sends the levels to the renormalization out of magnitude order; a (1/a)
        // nearly cancels them (the square root's last Newton step forms such a product)
        let a = gapped(r);
        return match kind {
            Add => (a, gapped(r)),
            Sqrt => (a.abs(), OD::ONE),
            Mul => {
                if coin(r) {
                    (a, OD::ONE / a)
                } else {
                    (a, gapped(r))
                }
            }
            Div => (gapped(r), a),
        };
    }
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
        (Computed, _) | (Gap, _) | (Ladder, _) => unreachable!(),
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

/// The proven bound of add, od + f64, mul and od x f64, in units of 2^-418: u^8 (1 + 2^-14) with u = 2^-53, relative
/// to |ab| for the products and to |a| + |b| for the adds. It holds for operands within `proven`'s hypotheses.
const PROVEN_THR: f64 = (1.0 + 1.0 / 16384.0) / 64.0;

/// exponent of the last bit of a finite nonzero x
fn lsb(x: f64) -> i64 {
    let e = ((x.to_bits() >> 52) & 0x7ff) as i64;
    if e == 0 {
        -1074
    } else {
        e - 1075
    }
}

/// |a_i| <= 2^(-52 i) |a_0| for every part, exactly: the ladder that every ulp-nonoverlapping value has
fn ladder(a: &OD) -> bool {
    let a0 = Dy::from_f64(a.x[0]);
    (1..8).all(|i| Dy::from_f64(a.x[i]).cmp_abs(&a0.ldexp(-52 * i as i64)) != Ordering::Greater)
}

/// every product of parts that the operation forms is a multiple of 2^-1074, so that a rounding below 2^-1022 is
/// exact and two-product is error-free (|e_a + e_b| >= -970 in exponents)
fn products_fit(a: &[f64], b: &[f64], max_order: usize) -> bool {
    a.iter().enumerate().all(|(i, &x)| {
        b.iter()
            .enumerate()
            .all(|(j, &y)| i + j > max_order || x == 0.0 || y == 0.0 || lsb(x) + lsb(y) >= -1074)
    })
}

/// The operands are within the hypotheses of the proven bound: finite, both octo-double operands on the ladder, every
/// rounding either normal or exact, and the leading parts well below overflow. Only the operation's inputs are
/// read, so the runs of division and the square root, whose intermediate quotients these do not bound, are left out.
fn proven(op: Op, a: OD, b: OD) -> bool {
    let fin = |x: &OD| x.x.iter().all(|v| v.is_finite());
    let big = |x: f64| x.abs() >= 2f64.powi(500);
    if !fin(&a) || !fin(&b) || !ladder(&a) {
        return false;
    }
    match op {
        Op::Add => ladder(&b) && !big(a.x[0]) && !big(b.x[0]),
        Op::AddF => !big(a.x[0]) && !big(b.x[0]),
        Op::Mul => ladder(&b) && products_fit(&a.x, &b.x, 8) && !big(a.x[0]) && !big(b.x[0]),
        Op::MulF => products_fit(&a.x, &b.x[..1], 7) && !big(a.x[0]) && !big(b.x[0]),
        Op::Div | Op::Sqrt => false,
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
    /// the samples within the proven bound's hypotheses, checked against `PROVEN_THR`
    proven: Proven,
}

/// samples within the proven bound's hypotheses: their number, the worst measure in units of 2^-418, those outside
#[derive(Clone, Debug, Default)]
struct Proven {
    n: usize,
    max: f64,
    fails: usize,
}

impl Res {
    /// no sample outside the bounds and no lane different from the scalar result
    fn ok(&self) -> bool {
        self.fails == 0 && self.proven.fails == 0 && self.mism == 0
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
        "  {:<14} {:<10} {:>6} {:>10} {:>10} {:>10} {:>6} {:>6} {:>6} {:>7} {:>10} {:>7}",
        "operation", "inputs", "n", "max", "99.9%", "max rel", "thr", "fails", "lanes", "proven", "max", "fails"
    );
    for r in rs {
        println!(
            "  {:<14} {:<10} {:>6} {:>10} {:>10} {:>10} {:>6} {:>6} {:>6} {:>7} {:>10} {:>7}",
            r.what,
            r.cat,
            r.n,
            fmt_u(r.max),
            fmt_u(r.p999),
            fmt_u(r.rel_max),
            fmt_u(r.thr),
            r.fails,
            r.mism,
            r.proven.n,
            fmt_u(r.proven.max),
            r.proven.fails
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
        for cat in ALL_CATS {
            let inp = inputs(op, cat, n, seed);
            set_mutation(id);
            let (rs, rv) = results(op, &inp);
            set_mutation(0);
            let under = cat == Cat::Underflow;
            let (mut ms, mut fails, mut mism, mut rel_max) = (Vec::with_capacity(n), 0, 0, 0f64);
            let mut digest = 0xcbf29ce484222325u64;
            let mut pr = Proven::default();
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
                if proven(op, a, b) {
                    pr.n += 1;
                    pr.max = pr.max.max(err.ratio(&scale) / unit());
                    if !within(&err, &scale, PROVEN_THR, &Dy::zero()) {
                        pr.fails += 1;
                    }
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
                proven: pr,
            });
        }
    }
    out
}

// -------------------------------------------------------------------------------------------------------------
// the dot accumulator
// -------------------------------------------------------------------------------------------------------------

const ACC_CATS: [&str; 4] = ["random", "cancel", "wide", "mixed"];

/// The accumulator's proven bound for len products of operands on the ladder |a_i| <= 2^(-52 i) |a_0|, in units of
/// 2^-418 relative to W = sum |a_i b_i|: |Z - x| <= (|Z| + c W) u^8 <= (1 + c) W / 64 units. c is the second term's
/// constant, rounded up, for len = 1, 4, 16 and 64 at n = 8, p = 53, theta = 2 (2^-14.92, 2^-14.28, 2^-10.55,
/// 2^2.68). The paper's W sums the leading parts' |a_0 b_0|, within a factor 1 + 5u of the W here, which the rounding
/// up absorbs. c grows like len^9 u, so the bound stays near u^8 W only up to about 50 products, and a sum of 2048
/// constructed terms reaches 2^23.8 u^8 |Z|. The proof is the paper's section on sums of products
/// (paper/expansion-error-bounds-accumulator.tex), and paper/accumulator/ computes the constants.
fn acc_thr(len: usize) -> f64 {
    let c = match len {
        1 => 3.3e-5,
        4 => 5.1e-5,
        16 => 6.7e-4,
        64 => 6.43,
        _ => panic!("acc_thr: no constant for {len} terms"),
    };
    (1.0 + c) / 64.0
}

/// accuracy of ODotAcc / OdAcc on dot products of length len (8 per sample, one per lane): |error| / sum |a_i b_i|
fn run_acc(n: usize, seed: u64, id: u32) -> Vec<Res> {
    let mut out = Vec::new();
    for len in [1usize, 4, 16, 64] {
        for (ci, cat) in ACC_CATS.iter().enumerate() {
            let mut r = Rng::new(seed ^ ((len as u64) << 20) ^ ((ci as u64) << 30) ^ 0x0acc);
            let thr = acc_thr(len);
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
                proven: Proven::default(),
            });
        }
    }
    out
}

// -------------------------------------------------------------------------------------------------------------
// a double-double operand: od x dd, od + dd and the accumulator's od x dd against the promoted operations
// -------------------------------------------------------------------------------------------------------------

/// the operations with a double-double operand, each checked bit for bit against `*`, `+` or `add_prod` with the
/// operand promoted (`OD::from_dd`, `OV::from_dv`)
const DD_OPS: [&str; 3] = ["od x dd", "od + dd", "dot x dd"];

/// every bit the same, a NaN equal to any NaN: Rust leaves the sign and payload of a NaN result unspecified, and the
/// lanes and the scalar type already give NaNs of different signs on one input (as `same`)
fn bits_eq(a: &[f64], b: &[f64]) -> bool {
    a.len() == b.len()
        && a.iter()
            .zip(b)
            .all(|(x, y)| x.to_bits() == y.to_bits() || (x.is_nan() && y.is_nan()))
}

/// a double-double operand from b's two leading parts, a quarter of them with the low part +0 or -0 (an f64 constant)
fn dd_from(r: &mut Rng, b: OD) -> DD {
    match r.int(0, 7) {
        0 => DD { hi: b.x[0], lo: 0.0 },
        1 => DD { hi: b.x[0], lo: -0.0 },
        _ => DD { hi: b.x[0], lo: b.x[1] },
    }
}

/// the scalar result of a double-double operation (`DD_OPS[op]`) and its promoted reference, as their parts or the
/// accumulator's nine levels then its sum; the accumulator starts from start
fn dd_scalar(op: usize, a: OD, c: DD, start: OdAcc) -> (Vec<f64>, Vec<f64>) {
    let p = OD::from_dd(c);
    match op {
        0 => (a.mul_dd(c).x.to_vec(), (a * p).x.to_vec()),
        1 => (a.add_dd(c).x.to_vec(), (a + p).x.to_vec()),
        _ => {
            let (n, r) = (start.add_prod_dd(a, c), start.add_prod(a, p));
            let cat = |s: OdAcc| [&s.s[..], &s.finish().x[..]].concat();
            (cat(n), cat(r))
        }
    }
}

/// `dd_scalar` on 8 lanes, by lane
fn dd_lanes(op: usize, a: &[OD; 8], c: &[DD; 8], start: &[OdAcc; 8]) -> (Vec<Vec<f64>>, Vec<Vec<f64>>) {
    let av = OV::from_lanes(a);
    let cv = crate::dv::DV::<crate::simd::Native>::load(&c.map(|d| d.hi), &c.map(|d| d.lo));
    let p = OV::from_dv(cv);
    let lanes = |v: OV| -> Vec<Vec<f64>> { v.lanes().iter().map(|x| x.x.to_vec()).collect() };
    match op {
        0 => (lanes(av.mul_dv(cv)), lanes(av * p)),
        1 => (lanes(av.add_dv(cv)), lanes(av + p)),
        _ => {
            let mut s0 = ODotAcc::zero();
            for l in 0..9 {
                s0.s[l] = V8::load(&start.map(|a| a.s[l]));
            }
            let mut n = s0;
            n.add_prod_dv_mut(&av, &cv);
            let n2 = s0.add_prod_dv(av, cv);
            let r = s0.add_prod(av, p);
            let cat = |s: ODotAcc| -> Vec<Vec<f64>> {
                let f = s.finish().lanes();
                (0..8)
                    .map(|j| {
                        let mut v: Vec<f64> = s.s.iter().map(|l| l.to_array()[j]).collect();
                        v.extend_from_slice(&f[j].x);
                        v
                    })
                    .collect()
            };
            // the by-value and in-place forms are one operation
            let (nv, n2v) = (cat(n), cat(n2));
            assert!(
                nv.iter().zip(&n2v).all(|(x, y)| bits_eq(x, y)),
                "add_prod_dv_mut vs add_prod_dv"
            );
            (nv, cat(r))
        }
    }
}

/// Every operation of `DD_OPS` in every input category, with mutation id active in the new operations only: per row,
/// fails counts the results (scalar or lanes, levels and sums for the accumulator) that differ in any bit from the
/// promoted operation run with no mutation, and mism the lanes that differ from the scalar result. The accumulator
/// starts empty on even samples and from the previous sample's product on odd ones.
fn run_dd(n: usize, seed: u64, id: u32) -> Vec<Res> {
    let mut out = Vec::new();
    for (op, name) in DD_OPS.iter().enumerate() {
        for cat in ALL_CATS {
            let base = if op == 1 { Op::Add } else { Op::Mul };
            let inp = inputs(base, cat, n, seed);
            let mut r = Rng::new(seed ^ ((op as u64) << 24) ^ ((cat as u64) << 40) ^ 0x0ddc);
            let cs: Vec<DD> = inp.iter().map(|&(_, b)| dd_from(&mut r, b)).collect();
            let starts: Vec<OdAcc> = (0..inp.len())
                .map(|k| {
                    if k.is_multiple_of(2) {
                        OdAcc::zero()
                    } else {
                        OdAcc::zero().add_prod(inp[k - 1].0, inp[k - 1].1)
                    }
                })
                .collect();
            let (mut fails, mut mism) = (0, 0);
            for (c8, k0) in inp.chunks(8).zip((0..).step_by(8)) {
                let m = c8.len();
                let a: [OD; 8] = std::array::from_fn(|j| if j < m { c8[j].0 } else { OD::ONE });
                let c: [DD; 8] = std::array::from_fn(|j| if j < m { cs[k0 + j] } else { DD::ONE });
                let st: [OdAcc; 8] = std::array::from_fn(|j| if j < m { starts[k0 + j] } else { OdAcc::zero() });
                set_mutation(id);
                let news: Vec<Vec<f64>> = (0..m).map(|j| dd_scalar(op, a[j], c[j], st[j]).0).collect();
                let (newv, _) = dd_lanes(op, &a, &c, &st);
                set_mutation(0);
                let (_, refv) = dd_lanes(op, &a, &c, &st);
                for j in 0..m {
                    let refs = dd_scalar(op, a[j], c[j], st[j]).1;
                    fails += !bits_eq(&news[j], &refs) as usize + !bits_eq(&newv[j], &refv[j]) as usize;
                    mism += !bits_eq(&news[j], &newv[j]) as usize;
                }
            }
            out.push(row(name, cat_name(cat), n, fails, mism));
        }
    }
    out
}

/// Edge operands: zeros of either sign in any part, zero parts between nonzero ones, exact integers, values whose
/// lower parts underflow or are subnormal, values near overflow, infinities and NaNs (one with a payload).
fn od_edges() -> Vec<OD> {
    let u = 2f64.powi(-53);
    let nan_p = f64::from_bits(0x7ff8_0000_0000_1234);
    let mut v = vec![
        OD::ZERO,
        OD::from_f64(-0.0),
        OD { x: [-0.0; 8] },
        OD {
            x: [0.0, -0.0, 0.0, -0.0, 0.0, -0.0, 0.0, -0.0],
        },
        OD::ONE,
        OD::from_f64(-1.0),
        OD::from_f64(3.0),
        OD::from_f64(-7.0),
        OD::from_f64(4503599627370497.0),
        OD {
            x: [1.0, -0.0, -0.0, -0.0, -0.0, -0.0, -0.0, -0.0],
        },
        OD {
            x: [-1.0, 0.0, -0.0, 0.0, -0.0, 0.0, -0.0, 0.0],
        },
        OD {
            x: [1.0, 0.0, u.powi(3), 0.0, 0.0, -u.powi(6), 0.0, 0.0],
        },
        OD {
            x: [-1.5, u, 0.0, 0.0, 0.0, 0.0, 0.0, u.powi(8)],
        },
        OD {
            x: [1.0, u, u * u, u.powi(3), u.powi(4), u.powi(5), u.powi(6), u.powi(7)],
        },
        OD {
            x: [1e-300, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
        },
        OD {
            x: [-1e-300, 1e-317, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
        },
        OD {
            x: [2f64.powi(-1022), -5e-324, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
        },
        OD::from_f64(5e-324),
        OD::from_f64(-1e-310),
        OD {
            x: [1e250, 1e233, -1e216, 0.0, 0.0, 0.0, 0.0, 0.0],
        },
        OD::from_f64(1e300),
        OD::from_f64(-f64::MAX),
        OD::from_f64(f64::INFINITY),
        OD::from_f64(f64::NEG_INFINITY),
        OD::from_f64(f64::NAN),
        OD::from_f64(nan_p),
        OD {
            x: [1.0, nan_p, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
        },
        OD {
            x: [1.0, 0.0, 0.0, f64::INFINITY, 0.0, 0.0, 0.0, 0.0],
        },
    ];
    // a non-finite value or a -0 in each part: the skipped products are then not all zeros
    let full = [-1.25, u, -u * u, u.powi(3), -u.powi(4), u.powi(5), -u.powi(6), u.powi(7)];
    for i in 0..8 {
        for s in [f64::INFINITY, f64::NEG_INFINITY, f64::NAN, -0.0] {
            let mut x = full;
            x[i] = s;
            v.push(OD { x });
        }
    }
    let mut r = Rng::new(0xed9e);
    for _ in 0..12 {
        let e = r.int(-30, 30);
        v.push(od_of(&rand_dy(&mut r, e)));
    }
    for _ in 0..4 {
        v.push(od_of(&rde(&mut r, -1060, -900)));
        v.push(od_of(&rde(&mut r, 900, 1020)));
    }
    v
}

/// edge double-double operands, the same kinds as `od_edges`, the low part of either sign or zero
fn dd_edges() -> Vec<DD> {
    let d = |hi: f64, lo: f64| DD { hi, lo };
    let u = 2f64.powi(-53);
    vec![
        d(0.0, 0.0),
        d(0.0, 1.0),
        d(-0.0, -u),
        d(u, 1.0),
        d(1.0, f64::INFINITY),
        d(-0.0, 0.0),
        d(0.0, -0.0),
        d(-0.0, -0.0),
        d(1.0, 0.0),
        d(1.0, -0.0),
        d(-1.0, 0.0),
        d(-1.0, -0.0),
        d(3.0, -u * 1.5),
        d(-7.0, u),
        d(0.1, -5.551115123125783e-18),
        d(1.0, u),
        d(1.0, -u / 2.0),
        d(2f64.powi(-1022), 0.0),
        d(5e-324, 0.0),
        d(-1e-300, 1e-317),
        d(1e300, -1e283),
        d(f64::MAX, 0.0),
        d(f64::INFINITY, 0.0),
        d(f64::NEG_INFINITY, -0.0),
        d(f64::NAN, 0.0),
        d(1.0, f64::NAN),
    ]
}

/// The edge pairs (`od_edges` x `dd_edges`): the new operations' levels (`alg::expand_dd` against `alg::expand`) and
/// results against the promoted ones, scalar and lanes, every bit. Returns the mismatches as (operation, a, c) and
/// the number of comparisons.
fn dd_edge_mismatches() -> (Vec<String>, usize) {
    let (ods, dds) = (od_edges(), dd_edges());
    let pairs: Vec<(OD, DD, OdAcc)> = ods
        .iter()
        .flat_map(|&a| dds.iter().map(move |&c| (a, c)))
        .enumerate()
        .map(|(k, (a, c))| {
            let start = if k.is_multiple_of(3) {
                OdAcc::zero()
            } else {
                OdAcc::zero().add_prod(ods[k % ods.len()], ods[(k / 7) % ods.len()])
            };
            (a, c, start)
        })
        .collect();
    let (mut bad, mut n) = (Vec::new(), 0);
    for &(a, c, start) in &pairs {
        let lv = crate::od::alg::expand_dd(&a.x, c.hi, c.lo);
        let lr = crate::od::alg::expand(&a.x, &OD::from_dd(c).x);
        n += 1;
        if !bits_eq(&lv, &lr) {
            bad.push(format!("levels {:?} x {:?}: {lv:?} vs {lr:?}", a.x, c));
        }
        for op in 0..3 {
            let (x, y) = dd_scalar(op, a, c, start);
            n += 1;
            if !bits_eq(&x, &y) {
                bad.push(format!("{} {:?} {:?}: {x:?} vs {y:?}", DD_OPS[op], a.x, c));
            }
        }
    }
    for ch in pairs.chunks(8) {
        let m = ch.len();
        let a: [OD; 8] = std::array::from_fn(|j| ch[j.min(m - 1)].0);
        let c: [DD; 8] = std::array::from_fn(|j| ch[j.min(m - 1)].1);
        let st: [OdAcc; 8] = std::array::from_fn(|j| ch[j.min(m - 1)].2);
        let cv = crate::dv::DV::<crate::simd::Native>::load(&c.map(|d| d.hi), &c.map(|d| d.lo));
        let av = OV::from_lanes(&a);
        let lv = crate::od::alg::expand_dd(&av.c, cv.hi, cv.lo);
        let lr = crate::od::alg::expand(&av.c, &OV::from_dv(cv).c);
        for j in 0..m {
            n += 1;
            let (x, y): (Vec<f64>, Vec<f64>) = (
                lv.iter().map(|l| l.to_array()[j]).collect(),
                lr.iter().map(|l| l.to_array()[j]).collect(),
            );
            if !bits_eq(&x, &y) {
                bad.push(format!("lanes: levels {:?} x {:?}", a[j].x, c[j]));
            }
        }
        for op in 0..3 {
            let (x, y) = dd_lanes(op, &a, &c, &st);
            for j in 0..m {
                n += 2;
                if !bits_eq(&x[j], &y[j]) {
                    bad.push(format!(
                        "lanes: {} {:?} {:?}: {:?} vs {:?}",
                        DD_OPS[op], a[j].x, c[j], x[j], y[j]
                    ));
                }
                // the lanes are the scalar operation
                if !bits_eq(&x[j], &dd_scalar(op, a[j], c[j], st[j]).0) {
                    bad.push(format!("lanes vs scalar: {} {:?} {:?}", DD_OPS[op], a[j].x, c[j]));
                }
            }
        }
    }
    (bad, n)
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
        proven: Proven::default(),
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
    let digest = digest(&rs);
    if report() {
        print_table(
            &format!("octo-double accuracy (units of 2^-418; n per row; isa {})", V8::ISA),
            &rs,
        );
    }
    println!("od digest {digest:016x} (n {n}, seed {seed}, isa {})", V8::ISA);
    let bad: Vec<&Res> = rs.iter().filter(|r| !r.ok()).collect();
    assert!(bad.is_empty(), "{} rows fail: {:?}", bad.len(), bad);
    // the proven bound is checked on most inputs of the four operations it covers, not on a few
    for op in [Op::Add, Op::AddF, Op::Mul, Op::MulF] {
        let covered: usize = rs.iter().filter(|r| r.what == op_name(op)).map(|r| r.proven.n).sum();
        assert!(
            covered >= 5 * n,
            "{}: {covered} inputs within the proven bound's hypotheses",
            op_name(op)
        );
    }
    if (n, seed) == (2000, 1) {
        let gap = digest_cat(&rs, "gap");
        let ladder = digest_cat(&rs, "ladder");
        println!("od gap digest {gap:016x}, ladder digest {ladder:016x}");
        assert!(
            digest == OD_DIGEST && gap == GAP_DIGEST && ladder == LADDER_DIGEST,
            "the results' bits changed: digests {digest:#018x}, {gap:#018x}, {ladder:#018x}, pinned {:#018x}, {:#018x}, \
             {:#018x}",
            OD_DIGEST,
            GAP_DIGEST,
            LADDER_DIGEST
        );
    }
}

/// the digest of the results (`Res::digest`) of every row in `CATS`, in order
fn digest(rs: &[Res]) -> u64 {
    fold_digest(rs.iter().filter(|r| CATS.iter().any(|&c| cat_name(c) == r.cat)))
}

/// the digest of the results of one category's rows, in order
fn digest_cat(rs: &[Res], cat: &str) -> u64 {
    fold_digest(rs.iter().filter(|r| r.cat == cat))
}

fn fold_digest<'a>(rs: impl Iterator<Item = &'a Res>) -> u64 {
    rs.fold(0xcbf29ce484222325u64, |h, r| (h ^ r.digest).wrapping_mul(0x100000001b3))
}

/// The digest of `od_accuracy`'s results at its default size and seed (2000, 1), recorded with
/// 4.1.1: every operation's bits in every category, pinned, and the lanes' with them, which must
/// be the scalar ones. Every backend gives these bits.
const OD_DIGEST: u64 = 0x6ff0_7dec_6a4e_4e28;

/// The digest of the gap category's results at the same size and seed, recorded with 4.8.1, whose renormalization's
/// second pass by two-sums made them correct.
const GAP_DIGEST: u64 = 0xd7a7_6d83_c65e_67d7;

/// The digest of the ladder category's results at the same size and seed, recorded with 4.8.2.
const LADDER_DIGEST: u64 = 0xcfaf_1ebd_dc50_f177;

/// Control for the pinned digest: with the order-6 term a2 b3 of the product dropped
/// (`mutate::MUL_E23`), the results' digest is not the pinned one.
#[cfg(feature = "mutate")]
#[test]
fn od_digest_control() {
    assert!(digest(&run_ops(2000, 1, mutate::MUL_E23)) != OD_DIGEST);
}

/// the dot accumulators against exact sums, 1 to 64 terms
#[test]
fn od_accumulator() {
    let n = env_usize("OD_N", 2000) / 8 * 8;
    let seed = env_usize("OD_SEED", 1) as u64;
    let rs = run_acc(n / 4, seed, 0);
    if report() {
        print_table(
            "dot accumulator: |error| / sum |a_i b_i| (units of 2^-418); threshold the proven bound (acc_thr)",
            &rs,
        );
    }
    let bad: Vec<&Res> = rs.iter().filter(|r| !r.ok()).collect();
    assert!(bad.is_empty(), "{bad:?}");
}

/// Pass: od x dd (`OD::mul_dd`, `OV::mul_dv`), od + dd (`add_dd`, `add_dv`) and the accumulators' od x dd
/// (`OdAcc::add_prod_dd`, `ODotAcc::add_prod_dv` and `add_prod_dv_mut`) are bit for bit the operations with the
/// operand promoted to octo-double, levels included, on every input category (OD_N per row) and on the edge pairs,
/// whose zeros' signs, infinities and NaNs must match too (`bits_eq`). Control: `od_dd_control`.
#[test]
fn od_dd_operand_is_the_promoted_operation() {
    let n = env_usize("OD_N", 2000) / 8 * 8;
    let seed = env_usize("OD_SEED", 1) as u64;
    let rs = run_dd(n, seed, 0);
    if report() {
        print_rows(
            "a double-double operand: results differing from the promoted operation (fails)",
            &rs,
        );
    }
    let bad: Vec<&Res> = rs.iter().filter(|r| !r.ok()).collect();
    assert!(bad.is_empty(), "{bad:?}");
    let (bad, count) = dd_edge_mismatches();
    println!("edge pairs: {count} comparisons, {} mismatches", bad.len());
    assert!(
        bad.is_empty(),
        "{} of {count}: {:?}",
        bad.len(),
        &bad[..bad.len().min(8)]
    );
}

/// Control for `od_dd_operand_is_the_promoted_operation`: with the second level of od x dd and od + dd one ulp up
/// (`mutate::DD_ULP`; a subnormal or zero level stays), every operation fails in every input category, and the edge
/// pairs fail.
#[cfg(feature = "mutate")]
#[test]
fn od_dd_control() {
    let rs = run_dd(400, 3, mutate::DD_ULP);
    for r in &rs {
        println!("{:<9} {:<10} {} of {} results differ", r.what, r.cat, r.fails, 2 * r.n);
    }
    let quiet: Vec<String> = rs
        .iter()
        .filter(|r| r.fails == 0)
        .map(|r| format!("{}/{}", r.what, r.cat))
        .collect();
    assert!(quiet.is_empty(), "rows where no result changed: {quiet:?}");
    set_mutation(mutate::DD_ULP);
    let (bad, count) = dd_edge_mismatches();
    set_mutation(0);
    println!("edge pairs under the control: {} of {count} differ", bad.len());
    assert!(!bad.is_empty());
}

/// the largest |x_(i+1)| / ulp(x_i) over x's nonzero parts and their successors, infinite when a nonzero part follows a
/// zero one, zero for a non-finite value: at most 1/2 for parts that do not overlap, at most 1 for ulp-nonoverlapping
/// ones
fn overlap(x: OD) -> f64 {
    if x.x.iter().any(|p| !p.is_finite()) {
        return 0.0;
    }
    let mut w = 0.0f64;
    for i in 0..7 {
        if x.x[i] == 0.0 {
            return if x.x[i + 1..].iter().all(|&p| p == 0.0) {
                w
            } else {
                f64::INFINITY
            };
        }
        w = w.max(Dy::from_f64(x.x[i + 1]).abs().ratio(&ulp(x.x[i])));
    }
    w
}

/// Pass, set after a first run against `od`'s earlier statement (every part at most half the ulp of the one above it
/// for every operation), which the adds miss after cancellation: on `od_accuracy`'s inputs (OD_N per operation and
/// category, scalar and lanes), every finite result of the multiply, od x f64, the divide and the square root has
/// |x_(i+1)| <= ulp(x_i)/2, and of the adds (od + od, od + f64) |x_(i+1)| <= ulp(x_i), with no nonzero part after a
/// zero one. Controls: a value whose second part is twice the first's ulp fails both, one whose second part is a
/// whole ulp fails the half-ulp bound only, and one with a nonzero part after a zero one fails both.
#[test]
fn od_results_do_not_overlap() {
    let n = env_usize("OD_N", 2000) / 8 * 8;
    let seed = env_usize("OD_SEED", 1) as u64;
    let mut bad = Vec::new();
    for op in OPS {
        let bound = if op_cray(op) { 1.0 } else { 0.5 };
        let (mut worst, mut past_half, mut count) = (0.0f64, 0usize, 0usize);
        for cat in CATS {
            let (rs, rv) = results(op, &inputs(op, cat, n, seed));
            for x in rs.iter().chain(&rv) {
                let w = overlap(*x);
                count += 1;
                past_half += (w > 0.5) as usize;
                worst = worst.max(w);
            }
        }
        println!(
            "{}: worst |x_(i+1)| / ulp(x_i) {worst:.4}, {past_half} of {count} past 1/2 (bound {bound})",
            op_name(op)
        );
        if worst > bound {
            bad.push((op_name(op), worst));
        }
    }
    let part = |x1: f64, x2: f64| {
        let mut x = [0.0; 8];
        (x[0], x[1], x[2]) = (1.0, x1, x2);
        overlap(OD { x })
    };
    let controls = [part(2.0 * f64::EPSILON, 0.0), part(f64::EPSILON, 0.0), part(0.0, 1e-40)];
    println!("controls (twice the ulp, a whole ulp, a gap): {controls:?}");
    assert!(bad.is_empty(), "results past their bound: {bad:?}");
    assert!(
        controls[0] > 1.0 && controls[1] > 0.5 && controls[1] <= 1.0 && controls[2] > 1.0,
        "{controls:?}"
    );
}

/// Inputs on which the add, od + f64, mul, od x f64 and the divide reach their proven bounds, u^8 times the measure to
/// within a factor 1 - O(u). The products and quotients come out as (1, u, ..., u^7) up to sign, and the order-8 term
/// that the renormalization drops is the error. For od x f64, 3 g = 2^53 + 1 makes a_0 b = 1 + u. Pass: each
/// measure between 0.99 u^8 and its bound, scalar and lanes alike, and the four operations' operands within
/// `proven`'s hypotheses.
#[test]
fn od_worst_case_inputs() {
    let u = 2f64.powi(-53);
    let ladder_to = |k: usize| -> OD {
        let mut x = [0.0; 8];
        for (i, p) in x.iter_mut().enumerate().take(k) {
            *p = u.powi(i as i32);
        }
        OD { x }
    };
    let mut b_mul = [0.0; 8];
    b_mul[0] = 1.0;
    b_mul[7] = u.powi(7);
    let mut c = [0.0; 8];
    c[0] = u.powi(8);
    let mut a_mulf = [0.0; 8];
    for i in [0, 2, 4, 6] {
        a_mulf[i] = 1.5 * u.powi(i as i32);
    }
    a_mulf[7] = 1.5 * u.powi(8);
    let g = 3002399751580331.0 * 2f64.powi(-52);
    let mut d = [0.0; 8];
    d[0] = -1.0;
    d[1] = u;
    // the divide's runs are within the hypotheses too: its remainders are (u^k, 0, ...) and its quotient terms -u^k,
    // so every product is exact; its bound is u^8 (1 + 2^-25) relative
    let div_thr = (1.0 + 2f64.powi(-25)) / 64.0;
    let cases = [
        (Op::Mul, ladder_to(7), OD { x: b_mul }, PROVEN_THR),
        (Op::Add, ladder_to(8), OD { x: c }, PROVEN_THR),
        (Op::AddF, ladder_to(8), OD::from_f64(u.powi(8)), PROVEN_THR),
        (Op::MulF, OD { x: a_mulf }, OD::from_f64(g), PROVEN_THR),
        (Op::Div, OD::ONE, OD { x: d }, div_thr),
    ];
    assert_eq!(3 * 3002399751580331u64, (1u64 << 53) + 1);
    for (op, a, b, thr) in cases {
        assert!(
            op == Op::Div || proven(op, a, b),
            "{}: operands outside the hypotheses",
            op_name(op)
        );
        let (rs, rv) = results(op, &[(a, b)]);
        assert!(
            same(rs[0], rv[0]),
            "{}: lanes differ from the scalar result",
            op_name(op)
        );
        let (err, scale, _, _) = exact_err(op, a, b, rs[0], false);
        let m = err.ratio(&scale) / unit();
        println!("{:<9} error {m:.10} units of 2^-418, bound {thr:.10}", op_name(op));
        assert!(
            within(&err, &scale, thr, &Dy::zero()),
            "{}: {m} units, past the proven bound",
            op_name(op)
        );
        assert!(m >= 0.99 / 64.0, "{}: {m} units, below 0.99 u^8", op_name(op));
    }
}

/// The proven bound catches what the 1-unit thresholds miss: with the products of order 8 dropped, an error of a few
/// u^8 |ab| on the ladder category's inputs. Pass, set after a first run (2 of 400 past 1 unit, 348 past the
/// proven bound): the proven bound fails more than half of the ladder row's samples and more than ten times as many as
/// the thresholds.
#[cfg(feature = "mutate")]
#[test]
fn od_proven_bound_control() {
    let n = env_usize("OD_N", 400) / 8 * 8;
    let rs = run_ops(n, 7, mutate::MUL_L8);
    let row = rs
        .iter()
        .find(|r| r.what == op_name(Op::Mul) && r.cat == "ladder")
        .unwrap();
    println!(
        "mul without order 8, ladder inputs: {} of {n} past 1 unit, {} past the proven bound, worst {:.4} units",
        row.fails, row.proven.fails, row.proven.max
    );
    assert!(row.proven.fails * 2 > n && row.proven.fails > 10 * row.fails, "{row:?}");
}

/// Inputs whose results missed their bounds by 1e10 to 1e28 units when the renormalization's second pass was by
/// quick-two-sums: the square root of a two-part value with a gap and its product with its reciprocal, and two
/// quotients of values with zero parts. Pass: each within its operation's threshold, scalar and lanes alike.
#[test]
fn od_gap_regressions() {
    let bad: Vec<(&str, f64)> = gap_cases()
        .iter()
        .filter_map(|&(name, op, a, b)| {
            let (r, rv) = results(op, &[(a, b)]);
            let (err, scale, _, allow) = exact_err(op, a, b, r[0], false);
            let ok = within(&err, &scale, op_thr(op), &allow) && same(r[0], rv[0]);
            (!ok).then(|| (name, err.ratio(&scale) / unit()))
        })
        .collect();
    assert!(bad.is_empty(), "{bad:?}");
}

/// Control: with the second pass by quick-two-sums (`mutate::RENORM_FAST`), every case misses its bound.
#[cfg(feature = "mutate")]
#[test]
fn od_gap_regressions_control() {
    for (name, op, a, b) in gap_cases() {
        set_mutation(mutate::RENORM_FAST);
        let r = apply_s(op, a, b);
        set_mutation(0);
        let (err, scale, _, allow) = exact_err(op, a, b, r, false);
        assert!(!within(&err, &scale, op_thr(op), &allow), "{name} within its bound");
    }
}

/// eight to nine values ±(1 + f)·2^e, e in -300..=0, in random magnitude order; half the time one value nearly cancels
/// another, as the levels of a·(1/a) do
fn unordered(r: &mut Rng) -> [f64; 9] {
    let mut c: [f64; 9] = std::array::from_fn(|_| rde(r, -300, 0).to_f64());
    if coin(r) {
        let (i, j) = (r.int(0, 8) as usize, r.int(0, 8) as usize);
        if i != j {
            c[j] = -c[i] * (1.0 + f64::EPSILON * r.int(1, 1 << 20) as f64);
        }
    }
    c
}

/// 4.8.0's renormalization (second pass by quick-two-sums), and whether its every quick-two-sum was exact
fn renorm_fast_pass(c: [f64; 9]) -> ([f64; 8], bool) {
    let c = crate::od::vecsum(c);
    let (mut out, mut k, mut acc, mut exact) = ([0.0f64; 8], 0, c[0], true);
    for &ci in &c[1..] {
        let (t, e) = crate::od::quick_two_sum(acc, ci);
        exact &= (t, e) == crate::od::two_sum(acc, ci);
        if k < 7 && e != 0.0 {
            out[k] = t;
            k += 1;
            acc = e;
        } else {
            acc = t;
        }
    }
    out[k] = acc;
    (out, exact)
}

fn exact_sum(c: &[f64]) -> Dy {
    c.iter().fold(Dy::zero(), |s, &x| s.add(&Dy::from_f64(x)))
}

/// Pass: eight values in any magnitude order renormalize with their exact sum kept (seven emissions at most, so no
/// part is truncated, and every two-sum is exact).
#[test]
fn renorm_of_eight_keeps_the_exact_sum_in_any_order() {
    let mut r = Rng::new(0x5e7e);
    let lost = (0..20000)
        .filter(|_| {
            let c: [f64; 8] = unordered(&mut r)[..8].try_into().unwrap();
            !exact_sum(&crate::od::renorm_scalar(c)).sub(&exact_sum(&c)).is_zero()
        })
        .count();
    assert_eq!(lost, 0, "{lost} of 20000 renormalizations lost part of their sum");
}

/// Control: with the second pass by quick-two-sums (`mutate::RENORM_FAST`), some of the same renormalizations lose
/// part of their sum.
#[cfg(feature = "mutate")]
#[test]
fn renorm_of_eight_keeps_the_exact_sum_control() {
    let mut r = Rng::new(0x5e7e);
    set_mutation(mutate::RENORM_FAST);
    let lost = (0..20000)
        .filter(|_| {
            let c: [f64; 8] = unordered(&mut r)[..8].try_into().unwrap();
            !exact_sum(&crate::od::renorm_scalar(c)).sub(&exact_sum(&c)).is_zero()
        })
        .count();
    set_mutation(0);
    assert!(lost > 0, "the quick-two-sum pass kept every sum");
}

/// Pass: wherever every quick-two-sum of 4.8.0's second pass was exact, the two-sum pass gives its bits; the inputs,
/// half of them in magnitude order, include both kinds (at least 1000 of each in 20000).
#[test]
fn renorm_keeps_the_fast_pass_bits_where_it_was_exact() {
    let (exact, inexact, changed) = fast_pass_comparison(0);
    println!("renorm: {exact} with every quick-two-sum exact ({changed} changed), {inexact} with one inexact");
    assert_eq!(
        changed, 0,
        "{changed} results changed where every quick-two-sum was exact"
    );
    assert!(exact >= 1000 && inexact >= 1000, "{exact} exact, {inexact} inexact");
}

/// Control: with the renormalization's eighth part dropped (`mutate::RENORM_DROP`), results change where every
/// quick-two-sum was exact.
#[cfg(feature = "mutate")]
#[test]
fn renorm_keeps_the_fast_pass_bits_control() {
    assert!(fast_pass_comparison(mutate::RENORM_DROP).2 > 0);
}

/// over 20000 renormalizations, half in magnitude order (as the levels of a product of full values) and half in random
/// order: those whose every quick-two-sum in 4.8.0's pass was exact, those with one inexact, and among the first those
/// whose bits differ from 4.8.0's, with mutation `id` active in `renorm_scalar`
fn fast_pass_comparison(id: u32) -> (usize, usize, usize) {
    let mut r = Rng::new(0xb175);
    let (mut exact, mut inexact, mut changed) = (0, 0, 0);
    for i in 0..20000 {
        let c = if i % 2 == 0 {
            std::array::from_fn(|k| {
                let e = -53 * k as i64 - r.int(0, 3);
                rand_dy(&mut r, e).to_f64()
            })
        } else {
            unordered(&mut r)
        };
        let (old, was_exact) = renorm_fast_pass(c);
        set_mutation(id);
        let new = crate::od::renorm_scalar(c);
        set_mutation(0);
        if was_exact {
            exact += 1;
            changed += (old.map(f64::to_bits) != new.map(f64::to_bits)) as usize;
        } else {
            inexact += 1;
        }
    }
    (exact, inexact, changed)
}

/// the cases of `od_gap_regressions`
fn gap_cases() -> Vec<(&'static str, Op, OD, OD)> {
    let od = |h: [u64; 8]| OD {
        x: h.map(f64::from_bits),
    };
    let a = od([0x3ff97f22dc331771, 0x320e700ef097bbfd, 0, 0, 0, 0, 0, 0]);
    vec![
        ("sqrt", Op::Sqrt, a, OD::ONE),
        ("a (1/a)", Op::Mul, a, OD::ONE / a),
        (
            "quotient 1",
            Op::Div,
            od([
                0x3fdc0b223f8ec38c,
                0xbc6e614a71d2f866,
                0xb590b5eca31e706d,
                0x2ea39cd33f0fce0b,
                0x27bc6d352bcd0000,
                0,
                0,
                0,
            ]),
            od([
                0x3ff04936766afb19,
                0xbc65eb912e2cf5f6,
                0x2b655daf2bc93326,
                0xa7f828724fe44000,
                0,
                0,
                0,
                0,
            ]),
        ),
        (
            "quotient 2",
            Op::Div,
            od([
                0x40081779531a9783,
                0xb929a00ece965c74,
                0xb26660a9a05ed265,
                0x2efe880195dd03a0,
                0x281c44f426214000,
                0,
                0,
                0,
            ]),
            od([
                0x3fb9b4b7d1740212,
                0xbc49003abd38f755,
                0xab2ec2cfd3d8683b,
                0xa78f516e79640000,
                0,
                0,
                0,
                0,
            ]),
        ),
    ]
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
        rs.extend(run_dd(n / 4, 7, id));
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
