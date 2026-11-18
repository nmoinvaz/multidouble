//! `exp` and `ln` of the double-double, quad-double and octo-double types against a reference far more accurate than
//! 2^-424 that shares no code with them (`exp_ref`): e^x for an exact dyadic x, by its Taylor series at x 2^-12 in
//! fixed point with P = 1700 fractional bits, then twelve squarings in floating point with P + 64-bit significands,
//! with a rigorous bound on its error, below 2^-1600 relative. ln is measured through it: for the computed y,
//! |e^y - x| / x = |e^(y - ln x) - 1| is |y - ln x| up to a factor 1 + 2^-400.
//!
//! The reference is checked against planted truth (`reference_is_planted_truth`): e = sum 1/k! in exact integer
//! arithmetic, within 2^-1550, and e^x to 470 of the 700 digits that Python's decimal module gives
//! (scripts/explog_vectors.py, tests/data/explog_vectors.txt); a reference cut to 60 Taylor terms must fail both.
//!
//! The bounds, with u = 2^-53, are checked on every input that meets their hypotheses on x (`covered`; for exp, on
//! every input): the proven ones of the paper's appendix on exp and log (paper/explog_consts.py), `OD::exp` 3.661 u^8
//! e^x + 8 2^-1074 and `OD::ln` 9.926 u^8 |ln x| + 2^-509, `DD::exp` 5.465 u^2 e^x + 2 2^-1074 and `DD::ln` 15.351 u^2
//! |ln x| + 2^-1071, for x on the ladder |x_i| <= (2u)^i |x_0| (for the double-double a double-word) with normal parts;
//! the theorems also ask that no product inside the run underflow, apart from those that only choose k, m, the degree
//! or a branch; an emulator scanning every binade of x finds none (the paper's appendix on exp and log). Where
//! `OD::ln`'s absolute term dominates, near x = 1, it is held to its relative constant as well, a tested threshold. The
//! quad-double, which has no proven bounds, is held to 64 u^4 relative, fixed before the first run. The start of ln,
//! `explog::ln_f64`, is checked against its proven 5.915 u. Inputs, n per category for the double-double, n/2 for the
//! quad-double and n/4 for the octo-double: random over the range, near 0, near the reduction's boundaries (k + 1/2) ln
//! 2 and its multiples k ln 2, near overflow and underflow, near 1 for ln, subnormal, with gaps and zero parts, at the
//! top of the ladder (overlapping by a bit, not greedy, with random signs; not for the double-double, which must be a
//! double-word), and the special values.
//!
//! ```text
//! cargo test --release --test explog                        the checks (EXPLOG_REPORT=1 prints the worst cases)
//! cargo test --release --test explog --features mutate      and their controls (`explog::mutate`)
//! cargo test --release --test explog timing -- --ignored --nocapture
//! ```
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::exact::{BigU, Dy};
use multidouble::od::OD;
use multidouble::qd::QD;

/// the reference's fixed-point fractional bits
const P: u64 = 1700;
/// the reference's squarings: |x| 2^-12 <= 0.182 for |x| <= 745.2
const SQ: u32 = 12;

/// the proven bounds (paper/explog_consts.py), in units of u^n; exp's add n 2^-1074, ln's 2^FLOOR
const OD_EXP: f64 = 3.661;
const OD_LN: f64 = 9.926;
const OD_LN_FLOOR: i32 = -509;
const DD_EXP: f64 = 5.465;
const DD_LN: f64 = 15.351;
const DD_LN_FLOOR: i32 = -1071;
/// tested, not proven: `OD::ln` relative to |ln x| where the proven bound's absolute term dominates
const OD_LN_TESTED: f64 = OD_LN;
/// the start `ln_f64`'s proven bound, in units of u
const LN_F64: f64 = 5.915;
/// arguments of `ln_f64` checked besides the random ones: 0x1.22e14015c154dp+0, near its worst found by a search
const START_PINNED: [u64; 1] = [0x3ff2_2e14_015c_154d];
/// the quad-double thresholds, fixed before the first run
const QD_EXP: f64 = 64.0;
const QD_LN: f64 = 64.0;

// -------------------------------------------------------------------------------------------------------------
// the reference
// -------------------------------------------------------------------------------------------------------------

/// e^x = m 2^e within 2^err2 relative (err2 a log2 bound)
struct Ref {
    m: BigU,
    e: i64,
    err2: f64,
}

impl Ref {
    fn dy(&self) -> Dy {
        Dy {
            neg: false,
            m: self.m.clone(),
            e: self.e,
        }
    }
}

/// the reference's domain: |x| 2^-12 <= 0.182, where its Taylor series converges as its error bound assumes
const REF_MAX: f64 = 745.2;

/// e^x for an exact dyadic x with |x| <= REF_MAX, or None outside it, so that a result far off fails at once instead of
/// running the series where its terms grow. y = x 2^-12, Y = floor(|y| 2^P); the terms T_k = floor(T_(k-1) Y /
/// (2^P k)) of e^(+-Y 2^-P) are each within 2 units below the true ones (T_(k-1) is within 2 units, and Y 2^-P / k <
/// 1), so the K terms' sum S is within 2K + 4 units of e^(Y 2^-P) 2^P counting the tail after the first zero term,
/// and |y - Y 2^-P| < 2^-P adds 2 units. S >= 0.83 2^P. Each squaring doubles the relative error and its truncation
/// to P + 64 bits adds 2^-(P + 63). cut: keep only that many terms (the control); a series cut before its first zero
/// term has no certified bound, err2 = +inf.
fn exp_ref(x: &Dy, cut: Option<usize>) -> Option<Ref> {
    if x.to_f64().abs() > REF_MAX {
        return None;
    }
    let sh = x.e + P as i64 - SQ as i64;
    let y = if sh >= 0 {
        x.m.shl(sh as u64)
    } else {
        x.m.shr((-sh) as u64)
    };
    let one = BigU::from_u64(1).shl(P);
    let (mut pos, mut neg) = (one.clone(), BigU::zero());
    let mut t = one;
    let mut k = 0u64;
    let mut early = false;
    loop {
        k += 1;
        if cut.is_some_and(|c| k as usize >= c) {
            early = true;
            break;
        }
        t = t.mul(&y).shr(P).divrem_small(k).0;
        if t.is_zero() {
            break;
        }
        if x.neg && k % 2 == 1 {
            neg = neg.add(&t);
        } else {
            pos = pos.add(&t);
        }
    }
    let mut m = pos.sub(&neg);
    let mut e = -(P as i64);
    let mut err2 = ((2 * k + 6) as f64 / 0.83).log2() - P as f64;
    for _ in 0..SQ {
        m = m.mul(&m);
        e *= 2;
        let b = m.bits();
        if b > P + 64 {
            m = m.shr(b - P - 64);
            e += (b - P - 64) as i64;
        }
        // 2 eps + eps^2 + 2^-(P + 63) <= 2^(err2 + 1.001) while err2 < -100
        err2 = (err2 + 1.0).max(-(P as f64) - 63.0) + 0.001;
    }
    if early {
        err2 = f64::INFINITY;
    }
    Some(Ref { m, e, err2 })
}

/// the decimal d.ddd...e+NNN as (digits, power of ten)
fn decimal(s: &str) -> (BigU, i64) {
    let (mant, ex) = s.split_once('e').unwrap();
    let digits: String = mant.chars().filter(|c| c.is_ascii_digit()).collect();
    let frac = mant.split_once('.').map_or(0, |(_, f)| f.len()) as i64;
    (BigU::from_dec(&digits), ex.parse::<i64>().unwrap() - frac)
}

/// |m 2^e - d 10^p| / (d 10^p) <= 10^-digits, in integers
fn agrees(r: &Ref, d: &BigU, p: i64, digits: u64) -> bool {
    // compare m 2^e 10^-p with d: scale both to integers
    let (mut a, mut b) = (r.m.clone(), d.clone());
    if r.e >= 0 {
        a = a.shl(r.e as u64);
    } else {
        b = b.shl((-r.e) as u64);
    }
    if p >= 0 {
        b = b.mul(&BigU::pow_small(10, p as u64));
    } else {
        a = a.mul(&BigU::pow_small(10, (-p) as u64));
    }
    let diff = if a.cmp(&b) == std::cmp::Ordering::Less {
        b.sub(&a)
    } else {
        a.sub(&b)
    };
    diff.mul(&BigU::pow_small(10, digits)).cmp(&b) != std::cmp::Ordering::Greater
}

/// e as sum_(k <= 320) 1/k! in integers: e 320! = sum 320!/k! + (a tail below 1), within 2^-1550 relative
fn e_check(r: &Ref) -> bool {
    let n = 320u64;
    let mut f = BigU::from_u64(1);
    for k in 2..=n {
        f = f.mul_small(k);
    }
    let mut s = BigU::zero();
    let mut q = f.clone();
    for k in 0..=n {
        if k > 0 {
            q = q.divrem_small(k).0;
        }
        s = s.add(&q);
    }
    // m 2^e n! against s
    let (mut a, mut b) = (r.m.mul(&f), s);
    if r.e >= 0 {
        a = a.shl(r.e as u64);
    } else {
        b = b.shl((-r.e) as u64);
    }
    let diff = if a.cmp(&b) == std::cmp::Ordering::Less {
        b.sub(&a)
    } else {
        a.sub(&b)
    };
    diff.shl(1550).cmp(&b) != std::cmp::Ordering::Greater
}

fn vectors() -> Vec<(Dy, BigU, i64)> {
    include_str!("data/explog_vectors.txt")
        .lines()
        .map(|l| {
            let (xs, ds) = l.split_once(' ').unwrap();
            let x = xs
                .split(',')
                .map(|h| Dy::from_f64(f64::from_bits(u64::from_str_radix(h, 16).unwrap())))
                .fold(Dy::zero(), |a, b| a.add(&b));
            let (d, p) = decimal(ds);
            (x, d, p)
        })
        .collect()
}

/// whether the reference agrees with e = sum 1/k!, and with each 700-digit decimal value, and |x| of each. The uncut
/// reference must certify its bound below 2^-1600, and no reference may certify a bound that its value misses: a
/// series cut before its first zero term certifies none.
fn planted(cut: Option<usize>) -> (bool, Vec<(bool, f64)>) {
    let e = exp_ref(&Dy::from_f64(1.0), cut).unwrap();
    let e_ok = e_check(&e);
    assert!(e_ok || e.err2 > -1550.0, "e certified within 2^{} and missed", e.err2);
    let vs = vectors()
        .iter()
        .map(|(x, d, p)| {
            let r = exp_ref(x, cut).unwrap();
            if cut.is_none() {
                assert!(r.err2 < -1600.0, "reference error bound 2^{}", r.err2);
            }
            // 10^-470 = 2^-1561, above the reference's bound
            let ok = agrees(&r, d, *p, 470);
            assert!(
                ok || r.err2 > -1561.0,
                "x = {x:?} certified within 2^{} and missed",
                r.err2
            );
            (ok, x.to_f64().abs())
        })
        .collect();
    (e_ok, vs)
}

/// x on H(2) whose f = x - 1, exact, is led by a part below half its value: e_f of the leading part does not bound |f|,
/// while `bound_expo`'s U does, sum |f_i| (1 + 2^-48) < 2^(e + 1); and ln x is within its bound
#[test]
fn leading_part_does_not_bound_the_value() {
    let x = OD {
        x: [
            1.0,
            1.5050180741806962e-71,
            -1.0947644252537633e-47,
            1.0947644252537632e-47,
            -1.6444249949300811e-63,
            -4.130301482114151e-79,
            -1.1985091468012028e-94,
            -1.9639758264985916e-110,
        ],
    };
    assert!(ladder(x));
    let f = x.add_f(-1.0);
    let fd = exact(f);
    assert!(fd.sub(&exact(x).sub(&Dy::from_f64(1.0))).is_zero(), "x - 1 is exact");
    let expo = |h: f64| ((h.to_bits() >> 52) & 0x7ff) as i32 - 1023;
    let lead = Dy::from_f64(pow2i(expo(f.x[0]) + 1));
    assert_eq!(
        fd.cmp_abs(&lead),
        std::cmp::Ordering::Greater,
        "|f| above 2^(e+1) of its leading part"
    );
    let u = f.x.iter().fold(0.0, |a, v| a + v.abs()) * (1.0 + 2f64.powi(-48));
    assert_eq!(
        fd.cmp_abs(&Dy::from_f64(pow2i(expo(u) + 1))),
        std::cmp::Ordering::Less,
        "|f| below U's bound"
    );
    let (e, fl) = ln_err(x, OD_LN_FLOOR);
    assert!(e <= OD_LN + fl && e <= OD_LN_TESTED, "ln x errs by {e} u^8");
}

#[test]
fn reference_is_planted_truth() {
    let (e, vs) = planted(None);
    assert!(e && vs.iter().all(|v| v.0), "e {e}, decimal values {vs:?}");
    // the domain ends at REF_MAX: a wrong ln result such as 800 or 2^600 is refused at once
    assert!(exp_ref(&Dy::from_f64(REF_MAX), None).is_some() && exp_ref(&Dy::from_f64(-REF_MAX), None).is_some());
    assert!(exp_ref(&Dy::from_f64(800.0), None).is_none() && exp_ref(&Dy::from_f64(2f64.powi(600)), None).is_none());
    // control: 60 Taylor terms of e^(x/4096) err by about 2^-990 for |x| near 1, which fails both checks wherever
    // |x| >= 1/4 (smaller x need fewer terms)
    let (e, vs) = planted(Some(60));
    let big: Vec<&(bool, f64)> = vs.iter().filter(|v| v.1 >= 0.25).collect();
    assert!(
        !e && big.len() >= 10 && big.iter().all(|v| !v.0),
        "cut reference: e {e}, {vs:?}"
    );
}

// -------------------------------------------------------------------------------------------------------------
// the types, generically
// -------------------------------------------------------------------------------------------------------------

/// what the checks need of each type
trait Ty: Copy + std::fmt::Debug {
    const N: usize;
    const NAME: &'static str;
    fn parts(self) -> Vec<f64>;
    fn from_parts(p: &[f64]) -> Self;
    fn exp(self) -> Self;
    fn ln(self) -> Self;
}

impl Ty for DD {
    const N: usize = 2;
    const NAME: &'static str = "dd";
    fn parts(self) -> Vec<f64> {
        vec![self.hi, self.lo]
    }
    fn from_parts(p: &[f64]) -> DD {
        DD { hi: p[0], lo: p[1] }
    }
    fn exp(self) -> DD {
        DD::exp(self)
    }
    fn ln(self) -> DD {
        DD::ln(self)
    }
}

impl Ty for QD {
    const N: usize = 4;
    const NAME: &'static str = "qd";
    fn parts(self) -> Vec<f64> {
        self.x.to_vec()
    }
    fn from_parts(p: &[f64]) -> QD {
        QD {
            x: [p[0], p[1], p[2], p[3]],
        }
    }
    fn exp(self) -> QD {
        QD::exp(self)
    }
    fn ln(self) -> QD {
        QD::ln(self)
    }
}

impl Ty for OD {
    const N: usize = 8;
    const NAME: &'static str = "od";
    fn parts(self) -> Vec<f64> {
        self.x.to_vec()
    }
    fn from_parts(p: &[f64]) -> OD {
        OD {
            x: std::array::from_fn(|i| p[i]),
        }
    }
    fn exp(self) -> OD {
        OD::exp(self)
    }
    fn ln(self) -> OD {
        OD::ln(self)
    }
}

fn exact<T: Ty>(x: T) -> Dy {
    Dy::sum(&x.parts())
}

/// the greedy n-part expansion of v: x_0 = RN(v), x_1 = RN(v - x_0), ...
fn greedy<T: Ty>(v: &Dy) -> T {
    let mut r = v.clone();
    let mut p = vec![0.0; T::N];
    for x in p.iter_mut() {
        let c = r.to_f64();
        *x = c;
        if c == 0.0 || !c.is_finite() {
            break;
        }
        r = r.sub(&Dy::from_f64(c));
    }
    T::from_parts(&p)
}

/// 2^e for -1074 <= e <= 1023, from its bits (in a debug build 2f64.powi(-1070) is 0, as 2^1070 overflows first)
fn pow2i(e: i32) -> f64 {
    if e >= -1022 {
        f64::from_bits(((e + 1023) as u64) << 52)
    } else {
        f64::from_bits(1 << (e + 1074))
    }
}

/// the unit u^n
fn un<T: Ty>() -> f64 {
    2f64.powi(-53 * T::N as i32)
}

/// the proven bounds' hypotheses on x: on the ladder |x_i| <= (2u)^i |x_0| (for the double-double, a double-word, x_h
/// = RN(x_h + x_l), as the published bounds ask), with every nonzero part normal, so that no product of a subnormal
/// part leaves (A2)
fn ladder<T: Ty>(x: T) -> bool {
    let p = x.parts();
    let a0 = p[0].abs();
    let shape = if T::N == 2 {
        p[0] + p[1] == p[0]
    } else {
        (1..p.len()).all(|i| p[i].abs() <= a0 * 2f64.powi(-52 * i as i32))
    };
    p.iter().all(|v| *v == 0.0 || v.is_normal()) && shape
}

/// ln 2 to 1700 bits from sum 1/(j 2^j), a value within (P + 1) 2^-P below ln 2: independent of the crate's constants
fn ln2() -> Dy {
    let mut s = BigU::zero();
    for j in 1..=P {
        s = s.add(&BigU::from_u64(1).shl(P - j).divrem_small(j).0);
    }
    Dy {
        neg: false,
        m: s,
        e: -(P as i64),
    }
}

/// a random exact value of 300 random bits times 2^e (sign included)
fn rand_dy(r: &mut Rng, e: i64, neg: bool) -> Dy {
    let mut m = BigU::from_u64(r.next_u64() | 1 << 63);
    for _ in 0..4 {
        m = m.shl(64).add(&BigU::from_u64(r.next_u64()));
    }
    Dy { neg, m, e: e - 319 }
}

/// rand_dy with an exponent uniform in [lo, hi) and, if signed, a random sign
fn rand_in(r: &mut Rng, lo: i64, hi: i64, signed: bool) -> Dy {
    let e = lo + (r.next_u64() % (hi - lo) as u64) as i64;
    let neg = signed && r.next_u64() & 1 == 0;
    rand_dy(r, e, neg)
}

/// an input with gaps: random parts at random depths, some zero, on the ladder
fn gapped<T: Ty>(r: &mut Rng, x0: f64) -> T {
    let mut p = vec![0.0; T::N];
    p[0] = x0;
    for (i, x) in p.iter_mut().enumerate().skip(1) {
        if r.next_u64().is_multiple_of(3) {
            continue;
        }
        let depth = 53 * i as i32 + (r.next_u64() % 120) as i32;
        *x = r.sym() * x0.abs() * 2f64.powi(-depth);
    }
    T::from_parts(&p)
}

/// parts at the top of the ladder, |x_i| in ((2u)^i / 2, (2u)^i] |x_0|, with random signs: overlapping by a bit and
/// not greedy, which H(2) allows and `greedy` and `gapped` never produce (not a double-word: for QD and OD only)
fn top_ladder<T: Ty>(r: &mut Rng, x0: f64) -> T {
    let mut p = vec![0.0; T::N];
    p[0] = x0;
    for (i, x) in p.iter_mut().enumerate().skip(1) {
        let s = if r.next_u64() & 1 == 0 { 1.0 } else { -1.0 };
        *x = s * (0.5 + 0.5 * r.unit()) * x0.abs() * 2f64.powi(-52 * i as i32);
    }
    T::from_parts(&p)
}

// -------------------------------------------------------------------------------------------------------------
// the checks
// -------------------------------------------------------------------------------------------------------------

/// the result of one category's checks
#[derive(Debug, Default)]
struct Row {
    what: String,
    n: usize,
    /// inputs within the bound's hypotheses
    covered: usize,
    fails: usize,
    /// the largest error in units of u^n (relative; for ln relative to |ln x|)
    max: f64,
    worst: String,
}

/// |exp(x) - e^x| / e^x in units of u^n, the share of the absolute term n 2^-1074 (the final scaling's loss to the
/// subnormals) in the same units, whether the result is finite, and whether its leading part leaves room for n normal
/// parts, |y_0| > 2^(-1022 + 53 (n - 1)), where the worst relative error is recorded
fn exp_err<T: Ty>(x: T) -> (f64, f64, bool, bool) {
    let y = x.exp();
    if !y.parts().iter().all(|v| v.is_finite()) {
        return (f64::INFINITY, 0.0, false, false);
    }
    let r = exp_ref(&exact(x), None).expect("exp's inputs lie in the reference's domain");
    let yd = exact(y);
    let e = yd.sub(&r.dy()).ratio(&r.dy()) / un::<T>();
    // n 2^-1074 / e^x / u^n, from its bits: a debug build gives 2f64.powi(-1074) = 0, as 2^1074 overflows first
    let fl = Dy::from_f64(f64::from_bits(T::N as u64)).ratio(&r.dy()) / un::<T>();
    let room = y.parts()[0].abs() > pow2i(-1022 + 53 * (T::N as i32 - 1));
    (e, fl, true, room)
}

/// |ln(x) - ln x| / |ln x| in units of u^n, and the share of an absolute term 2^fl, 2^fl / |ln x| / u^n
fn ln_err<T: Ty>(x: T, fl: i32) -> (f64, f64) {
    let y = x.ln();
    if !y.parts().iter().all(|v| v.is_finite()) {
        return (f64::INFINITY, 0.0);
    }
    let yd = exact(y);
    let xd = exact(x);
    if yd.is_zero() {
        // only ln 1 may be zero
        let one = xd.sub(&Dy::from_f64(1.0)).is_zero();
        return (if one { 0.0 } else { f64::INFINITY }, 0.0);
    }
    // a result outside the reference's domain is far from ln x, |ln x| < 745
    let Some(r) = exp_ref(&yd, None) else {
        return (f64::INFINITY, 0.0);
    };
    let e = r.dy().sub(&xd).ratio(&xd.mul(&yd)) / un::<T>();
    let floor = pow2i(fl) / y.parts()[0].abs() / un::<T>();
    (e, floor)
}

/// exp on n inputs of each category
fn run_exp<T: Ty>(n: usize, seed: u64, bound: f64, proven: bool) -> Vec<Row> {
    let mut r = Rng(seed);
    let l2 = ln2();
    let mut rows = Vec::new();
    let mut cats = vec![
        "random",
        "near 0",
        "(k+1/2) ln 2",
        "k ln 2",
        "overflow",
        "underflow",
        "gaps",
    ];
    if T::N > 2 {
        cats.push("top ladder");
    }
    for cat in cats {
        let mut row = Row {
            what: format!("{} exp {cat}", T::NAME),
            ..Row::default()
        };
        for _ in 0..n {
            let x: T = match cat {
                "random" => {
                    let v = -740.0 + 1445.0 * r.unit();
                    greedy(&Dy::from_f64(v).add(&rand_in(&mut r, -52, -51, true)))
                }
                "near 0" => greedy(&rand_in(&mut r, -1000, 0, true)),
                "(k+1/2) ln 2" | "k ln 2" => {
                    let k = (r.next_u64() % 2048) as i64 - 1074;
                    let h = if cat == "k ln 2" { 0 } else { 1 };
                    let c = l2.mul(&Dy::from_f64((2 * k + h) as f64)).ldexp(-1);
                    let d = rand_in(&mut r, -420, -20, true);
                    greedy(&c.add(&d))
                }
                "overflow" => greedy(&Dy::from_f64(
                    709.782712893384 - 2f64.powi(-((r.next_u64() % 40) as i32)),
                )),
                "underflow" => greedy(&Dy::from_f64(-708.0 - 37.0 * r.unit())),
                "gaps" => {
                    let x0 = -745.0 + 1454.0 * r.unit();
                    gapped(&mut r, x0)
                }
                _ => {
                    // over the range, or near 0
                    let x0 = if r.next_u64() & 1 == 0 {
                        -740.0 + 1445.0 * r.unit()
                    } else {
                        r.sym() * pow2i(-((r.next_u64() % 1000) as i32))
                    };
                    top_ladder(&mut r, x0)
                }
            };
            let (e, fl, finite, room) = exp_err(x);
            row.n += 1;
            // every result is held to C u^n e^x + n 2^-1074 (no input here overflows); `covered` counts those within
            // the proven bound's hypotheses
            let hyp = finite && (!proven || ladder(x));
            row.covered += hyp as usize;
            if !finite || e > bound + fl {
                row.fails += 1;
            }
            // the worst relative error where the result has room for n normal parts
            if hyp && room && e > row.max {
                row.max = e;
                row.worst = format!("{:?}", x.parts());
            }
        }
        rows.push(row);
    }
    rows
}

/// ln on n inputs of each category
fn run_ln<T: Ty>(n: usize, seed: u64, bound: f64, floor: Option<i32>, proven: bool) -> Vec<Row> {
    let mut r = Rng(seed);
    let mut rows = Vec::new();
    let mut cats = vec![
        "random",
        "near 1",
        "sqrt2 2^k",
        "subnormal",
        "near max",
        "gaps",
        "power of 2",
    ];
    if T::N > 2 {
        cats.push("top ladder");
    }
    for cat in cats {
        let mut row = Row {
            what: format!("{} ln {cat}", T::NAME),
            ..Row::default()
        };
        for _ in 0..n {
            let x: T = match cat {
                "random" => greedy(&rand_in(&mut r, -1021, 1024, false)),
                "near 1" => {
                    let d = rand_in(&mut r, -600, 0, true);
                    greedy(&Dy::from_f64(1.0).add(&d))
                }
                "sqrt2 2^k" => {
                    // x near 2^(k + 1/2), where the reduction of exp(-y0) changes k
                    let k = (r.next_u64() % 2000) as i64 - 1000;
                    let s = Dy::from_f64(std::f64::consts::SQRT_2);
                    let d = rand_in(&mut r, -150, -50, true);
                    greedy(&s.add(&d).ldexp(k))
                }
                "subnormal" => greedy(&Dy::from_f64(f64::from_bits(1 + r.next_u64() % (1 << 52)))),
                "near max" => greedy(&Dy::from_f64(f64::MAX * (1.0 - r.unit() * 2f64.powi(-20)))),
                "gaps" => {
                    let x0 = (1.0 + r.unit()) * 2f64.powi((r.next_u64() % 1200) as i32 - 600);
                    gapped(&mut r, x0)
                }
                "top ladder" => {
                    // over the range, near 1, or near sqrt 2
                    let x0 = match r.next_u64() % 3 {
                        0 => (1.0 + r.unit()) * 2f64.powi((r.next_u64() % 1200) as i32 - 600),
                        1 => 1.0 + r.sym() * pow2i(-((r.next_u64() % 52) as i32) - 1),
                        _ => std::f64::consts::SQRT_2 * (1.0 + r.sym() * 2f64.powi(-40)),
                    };
                    top_ladder(&mut r, x0)
                }
                _ => {
                    // 2^k for -1074 <= k <= 1023, subnormal powers included
                    let k = (r.next_u64() % 2098) as i64 - 1074;
                    let b = if k >= -1022 {
                        ((k + 1023) as u64) << 52
                    } else {
                        1u64 << (k + 1074)
                    };
                    greedy(&Dy::from_f64(f64::from_bits(b)))
                }
            };
            let (e, fl) = ln_err(x, floor.unwrap_or(-1074));
            row.n += 1;
            // a single subnormal part is scaled exactly before any operation
            let hyp = !proven || ladder(x) || x.parts()[1..].iter().all(|v| *v == 0.0);
            let lim = bound + if floor.is_some() { fl } else { 0.0 };
            if hyp {
                row.covered += 1;
                // where the absolute term dominates, the octo-double is held to a tested relative threshold too
                if e > lim || (floor == Some(OD_LN_FLOOR) && e > OD_LN_TESTED) {
                    row.fails += 1;
                }
                if e > row.max {
                    row.max = e;
                    row.worst = format!("{:?}", x.parts());
                }
            }
        }
        rows.push(row);
    }
    rows
}

/// the start's bound (paper/explog_consts.py): `ln_f64` within `LN_F64` u of ln h relative (ln_f64(1) = 0 exactly), on
/// random normal and subnormal arguments, near 1, near the boundaries sqrt(2) 2^k of its reduction, at powers of 2 and
/// at `START_PINNED`; the count of misses and the worst error in units of u, with its result times 1 + nudge (the
/// control)
fn start_bound(n: usize, seed: u64, nudge: f64) -> (usize, f64) {
    let mut r = Rng(seed);
    let (mut bad, mut worst) = (0, 0.0f64);
    for i in 0..n + START_PINNED.len() {
        let k = (r.next_u64() % 2046) as i32 - 1022;
        let h = match i % 5 {
            _ if i >= n => f64::from_bits(START_PINNED[i - n]),
            0 => (1.0 + r.unit()) * 2f64.powi(k),
            1 => 1.0 + r.sym() * pow2i(-((r.next_u64() % 53) as i32)),
            2 => f64::from_bits(1 + r.next_u64() % (1 << 52)),
            3 => std::f64::consts::SQRT_2 * (1.0 + r.sym() * pow2i(-((r.next_u64() % 53) as i32))) * 2f64.powi(k),
            _ => pow2i((r.next_u64() % 2098) as i32 - 1074),
        };
        if !(h > 0.0 && h.is_finite()) {
            continue;
        }
        let l = multidouble::explog::ln_f64(h) * (1.0 + nudge);
        if l == 0.0 {
            bad += (h != 1.0) as usize;
            continue;
        }
        // |e^l - h| / (h |l|) = |e^(l - ln h) - 1| / |l| ~ |l - ln h| / |l|
        let Some(rf) = exp_ref(&Dy::from_f64(l), None) else {
            bad += 1;
            continue;
        };
        let e = rf
            .dy()
            .sub(&Dy::from_f64(h))
            .ratio(&Dy::from_f64(h).mul(&Dy::from_f64(l)))
            / 2f64.powi(-53);
        worst = worst.max(e);
        bad += (e > LN_F64) as usize;
    }
    (bad, worst)
}

fn report() -> bool {
    std::env::var("EXPLOG_REPORT").map(|v| v == "1").unwrap_or(false)
}

fn show(rows: &[Row]) {
    for r in rows {
        println!(
            "{:<28} n {:>5} covered {:>5} fails {:>4} worst {:.3e} u^n {}",
            r.what,
            r.n,
            r.covered,
            r.fails,
            r.max,
            if report() { &r.worst } else { "" }
        );
    }
}

fn all_rows(n: usize, seed: u64) -> Vec<Row> {
    let mut rows = run_exp::<DD>(n, seed, DD_EXP, true);
    rows.extend(run_ln::<DD>(n, seed, DD_LN, Some(DD_LN_FLOOR), true));
    rows.extend(run_exp::<QD>(n / 2, seed, QD_EXP, false));
    rows.extend(run_ln::<QD>(n / 2, seed, QD_LN, None, false));
    rows.extend(run_exp::<OD>(n / 4, seed, OD_EXP, true));
    rows.extend(run_ln::<OD>(n / 4, seed, OD_LN, Some(OD_LN_FLOOR), true));
    rows
}

#[test]
fn exp_and_ln_within_bounds() {
    let n = std::env::var("EXPLOG_N")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(400);
    // n / 4 octo-double inputs per category: fewer than 4 would check none
    assert!(
        n >= 4,
        "EXPLOG_N = {n} leaves the octo-double without inputs; use 4 or more"
    );
    let rows = all_rows(n, 1);
    show(&rows);
    let bad: Vec<&Row> = rows.iter().filter(|r| r.fails > 0).collect();
    assert!(bad.is_empty(), "{bad:#?}");
    // the proven bounds are checked on most inputs, not a few
    for r in rows.iter().filter(|r| !r.what.ends_with("underflow")) {
        assert!(
            r.covered * 2 >= r.n,
            "{}: {} of {} inputs within the hypotheses",
            r.what,
            r.covered,
            r.n
        );
    }
    let (bad, worst) = start_bound(4 * n, 2, 0.0);
    println!("ln_f64: {} arguments, worst {worst:.3} u", 4 * n + START_PINNED.len());
    assert_eq!(bad, 0, "ln_f64 beyond {LN_F64} u");
    // control: off by 2^-48 = 32 u relative, it misses wherever ln h is not 0
    assert!(start_bound(64, 2, 2f64.powi(-48)).0 > 48);
}

/// special values, exact cases and the range ends, as f64's exp and ln give them
#[test]
fn special_values() {
    fn check<T: Ty>() {
        let f = |v: f64| T::from_parts(&[v, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0][..T::N]);
        let hi = |x: T| x.parts()[0];
        assert!(hi(f(f64::NAN).exp()).is_nan());
        assert_eq!(hi(f(f64::INFINITY).exp()), f64::INFINITY);
        assert_eq!(hi(f(f64::NEG_INFINITY).exp()).to_bits(), 0);
        assert_eq!(f(0.0).exp().parts(), f(1.0).parts());
        assert_eq!(f(-0.0).exp().parts(), f(1.0).parts());
        assert_eq!(hi(f(709.79).exp()), f64::INFINITY);
        assert_eq!(f(709.8).exp().parts(), f(f64::INFINITY).parts());
        assert!(hi(f(709.78).exp()).is_finite());
        assert_eq!(hi(f(-745.21).exp()).to_bits(), 0);
        assert!(hi(f(-745.0).exp()) > 0.0, "e^-745 rounds to the least subnormal");
        assert!(hi(f(f64::NAN).ln()).is_nan());
        assert!(hi(f(-1.0).ln()).is_nan());
        assert!(hi(f(-f64::MIN_POSITIVE).ln()).is_nan());
        assert_eq!(hi(f(0.0).ln()), f64::NEG_INFINITY);
        assert_eq!(hi(f(-0.0).ln()), f64::NEG_INFINITY);
        assert_eq!(hi(f(f64::INFINITY).ln()), f64::INFINITY);
        assert!(f(1.0).ln().parts().iter().all(|v| *v == 0.0), "ln 1 = 0 exactly");
        // e^(ln 2 + ln 3) = 6, ln(e^x) = x, to the precision
        let six = (f(2.0).ln().parts(), f(3.0).ln().parts());
        let s = exact(T::from_parts(&six.0)).add(&exact(T::from_parts(&six.1)));
        let back = exact(greedy::<T>(&s).exp());
        assert!(back.sub(&Dy::from_f64(6.0)).ratio(&Dy::from_f64(6.0)) < 100.0 * un::<T>());
    }
    check::<DD>();
    check::<QD>();
    check::<OD>();
}

/// The controls (feature `mutate`): each breakage of `explog::mutate` makes the checks of every type fail.
#[cfg(feature = "mutate")]
#[test]
fn controls_fire() {
    use multidouble::explog::mutate;
    let mut silent = Vec::new();
    for id in 1..=mutate::N {
        mutate::set(id);
        let rows = all_rows(64, 3);
        mutate::set(0);
        for t in ["dd", "qd", "od"] {
            let failed: Vec<&str> = rows
                .iter()
                .filter(|r| r.what.starts_with(t) && r.fails > 0)
                .map(|r| r.what.as_str())
                .collect();
            println!(
                "control {id} {:<40} {t}: {} rows fail{}",
                mutate::NAMES[id as usize],
                failed.len(),
                if report() {
                    format!(" {failed:?}")
                } else {
                    String::new()
                }
            );
            let failed = failed.len();
            if failed == 0 {
                silent.push((id, t));
            }
        }
    }
    assert!(silent.is_empty(), "controls that did not fire: {silent:?}");
}

/// time per call of each function, on arguments spread over the range
#[test]
#[ignore]
fn timing() {
    fn time<T: Ty>(xs: &[T], f: fn(T) -> T) -> f64 {
        let reps = 3;
        let mut best = f64::INFINITY;
        for _ in 0..reps {
            let t = std::time::Instant::now();
            let mut acc = 0.0;
            for &x in xs {
                acc += f(std::hint::black_box(x)).parts()[0];
            }
            std::hint::black_box(acc);
            best = best.min(t.elapsed().as_secs_f64() / xs.len() as f64);
        }
        best * 1e9
    }
    fn args<T: Ty>(lo: f64, hi: f64) -> Vec<T> {
        let mut r = Rng(5);
        (0..2000)
            .map(|_| {
                greedy(
                    &rand_dy(&mut r, 0, false)
                        .ldexp(-1)
                        .add(&Dy::from_f64(lo + (hi - lo) * r.unit())),
                )
            })
            .collect()
    }
    fn row<T: Ty>() {
        let e = args::<T>(-700.0, 700.0);
        let l = args::<T>(1e-3, 1e3);
        println!(
            "{}: exp {:.0} ns, ln {:.0} ns",
            T::NAME,
            time(&e, T::exp),
            time(&l, T::ln)
        );
    }
    row::<DD>();
    row::<QD>();
    row::<OD>();
}
