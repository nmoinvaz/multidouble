//! Tests of `trig` (sin, cos, tan of `DD`, `QD`, `OD`) against a reference in fixed-point integer arithmetic with
//! 2200 fraction bits (`Fx`), built from `exact::BigU` and sharing no code or constant with `trig`: its pi comes from
//! Stormer's formula, pi/4 = 44 arctan(1/57) + 7 arctan(1/239) - 12 arctan(1/682) + 24 arctan(1/12943), and its sine
//! and cosine from their Taylor series to the last bit, after reducing x by pi/2 in the same fixed point. The
//! reference errs by less than 2^-2140 absolute for |x| <= 2^52 (pi/2 within 2^-2199, times |k| < 2^52, and each
//! series within 2^-2190), far below u^8 = 2^-424 relative to every result the tests compare (each above 2^-1500),
//! and its planted-truth checks pin it to known values.
//!
//! ```text
//! cargo test --release --lib trig_                                 tables, reference, accuracy, special values
//! cargo test --release --lib --features mutate trig_controls       every deliberate breakage must fail a check
//! cargo test --release --lib trig_timing -- --ignored --nocapture  ns per call
//! cargo test --release --lib trig_lanes_timing -- --ignored --nocapture  the lanes' ns per value against the scalar
//! ```
//! TRIG_N scales the samples per category (default 1), TRIG_REPORT=1 prints the tables. The error is relative to the
//! exact function value, in units of u^n (u = 2^-53, n the parts), with an absolute 2^-1163 allowed for the
//! reduction's pi/2 (5 |k| 2^-1217 with |k| < 0.64 2^52, relative to sin x cos x for tan). The bounds of `DD` and `OD`
//! are the paper's (`paper/trig_consts.py`); those of `QD` were fixed before the first run: 32 u^4 for sin and cos,
//! 64 u^4 for tan.
use crate::dd::DD;
use crate::exact::{BigU, Dy};
use crate::od::OD;
use crate::qd::QD;
use crate::qd_tests::Rng;
#[cfg(feature = "mutate")]
use crate::trig::mutate;
use std::cmp::Ordering;
use std::sync::OnceLock;

/// the reduction's threshold of |r_0|, RN(0.7854) (`trig::R_TH`), written out
#[allow(clippy::approx_constant)]
const R_TH: f64 = 0.7854;

// ---------------------------------------------------------------------------------------------------------------
// the reference
// ---------------------------------------------------------------------------------------------------------------

/// fraction bits of the reference
const FR: u64 = 2200;

/// ±m 2^-FR
#[derive(Clone, Debug)]
struct Fx {
    neg: bool,
    m: BigU,
}

impl Fx {
    /// exact for a dyadic with e >= -FR
    fn from_dy(d: &Dy) -> Fx {
        assert!(d.e + FR as i64 >= 0, "Fx::from_dy: 2^{} below the fixed point", d.e);
        Fx {
            neg: d.neg && !d.m.is_zero(),
            m: d.m.shl((d.e + FR as i64) as u64),
        }
    }
    fn from_f64(x: f64) -> Fx {
        Fx::from_dy(&Dy::from_f64(x))
    }
    fn to_dy(&self) -> Dy {
        Dy {
            neg: self.neg && !self.m.is_zero(),
            m: self.m.clone(),
            e: -(FR as i64),
        }
    }
    fn neg(&self) -> Fx {
        Fx {
            neg: !self.neg && !self.m.is_zero(),
            m: self.m.clone(),
        }
    }
    fn add(&self, o: &Fx) -> Fx {
        if self.neg == o.neg {
            return Fx {
                neg: self.neg,
                m: self.m.add(&o.m),
            };
        }
        match self.m.cmp(&o.m) {
            Ordering::Less => Fx {
                neg: o.neg,
                m: o.m.sub(&self.m),
            },
            _ => {
                let m = self.m.sub(&o.m);
                Fx {
                    neg: self.neg && !m.is_zero(),
                    m,
                }
            }
        }
    }
    fn sub(&self, o: &Fx) -> Fx {
        self.add(&o.neg())
    }
    /// truncated toward zero: within 2^-FR
    fn mul(&self, o: &Fx) -> Fx {
        let m = self.m.mul(&o.m).shr(FR);
        Fx {
            neg: (self.neg != o.neg) && !m.is_zero(),
            m,
        }
    }
    fn mul_small(&self, k: u64) -> Fx {
        Fx {
            neg: self.neg && k != 0,
            m: self.m.mul_small(k),
        }
    }
    /// truncated toward zero: within 2^-FR
    fn div_small(&self, d: u64) -> Fx {
        let m = self.m.divrem_small(d).0;
        Fx {
            neg: self.neg && !m.is_zero(),
            m,
        }
    }
}

/// 2^b arctan(1/m), within (terms + 2) of 2^-0 (a_k = floor(2^b / m^(2k+1)) by repeated division by m^2, each term
/// floor(a_k / (2k+1)), the tail below the last nonzero a_k)
fn arctan_inv(m: u64, b: u64) -> BigU {
    let m2 = m * m;
    let mut a = BigU::from_u64(1).shl(b).divrem_small(m).0;
    let (mut pos, mut neg) = (BigU::zero(), BigU::zero());
    let mut k = 0u64;
    while !a.is_zero() {
        let t = a.divrem_small(2 * k + 1).0;
        if k.is_multiple_of(2) {
            pos = pos.add(&t);
        } else {
            neg = neg.add(&t);
        }
        a = a.divrem_small(m2).0;
        k += 1;
    }
    pos.sub(&neg)
}

/// pi/2 from Stormer's formula at FR + 64 bits, rounded down to FR: within 2^-(FR - 1)
fn half_pi_with(terms: &[(u64, u64)], neg_terms: &[(u64, u64)]) -> Fx {
    let b = FR + 64;
    let mut s = BigU::zero();
    for &(c, m) in terms {
        s = s.add(&arctan_inv(m, b).mul_small(c));
    }
    for &(c, m) in neg_terms {
        s = s.sub(&arctan_inv(m, b).mul_small(c));
    }
    // pi/4 = s 2^-b, so pi/2 = 2 s 2^-b
    Fx {
        neg: false,
        m: s.shl(1).shr(64),
    }
}

fn half_pi() -> &'static Fx {
    static P: OnceLock<Fx> = OnceLock::new();
    P.get_or_init(|| half_pi_with(&[(44, 57), (7, 239), (24, 12943)], &[(12, 682)]))
}

/// sin r and cos r for |r| < 1 by their Taylor series: within (terms + 1) 2^-FR each
fn sin_cos_fx(r: &Fx) -> (Fx, Fx) {
    let z = r.mul(r);
    let (mut s, mut t) = (r.clone(), r.clone());
    let mut i = 1u64;
    loop {
        t = t.mul(&z).div_small((2 * i) * (2 * i + 1));
        if t.m.is_zero() {
            break;
        }
        s = if i % 2 == 1 { s.sub(&t) } else { s.add(&t) };
        i += 1;
    }
    let one = Fx {
        neg: false,
        m: BigU::from_u64(1).shl(FR),
    };
    let (mut c, mut t) = (one.clone(), one);
    let mut i = 1u64;
    loop {
        t = t.mul(&z).div_small((2 * i - 1) * (2 * i));
        if t.m.is_zero() {
            break;
        }
        c = if i % 2 == 1 { c.sub(&t) } else { c.add(&t) };
        i += 1;
    }
    (s, c)
}

/// (sin x, cos x) for an exact x with |x| <= 2^53: x - k pi/2 with |r| <= pi/4, then the series
fn reference(x: &Dy) -> (Fx, Fx) {
    let p = half_pi();
    let xf = Fx::from_dy(x);
    let mut k = (x.to_f64() / std::f64::consts::FRAC_PI_2).round() as i64;
    let mut r = xf.sub(&p.mul_small(k.unsigned_abs()).neg_if(k < 0));
    let half = p.div_small(2);
    while r.m.cmp(&half.m) == Ordering::Greater {
        if r.neg {
            k -= 1;
            r = r.add(p);
        } else {
            k += 1;
            r = r.sub(p);
        }
    }
    let (s, c) = sin_cos_fx(&r);
    match k.rem_euclid(4) {
        0 => (s, c),
        1 => (c, s.neg()),
        2 => (s.neg(), c.neg()),
        _ => (c.neg(), s),
    }
}

impl Fx {
    fn neg_if(self, b: bool) -> Fx {
        if b {
            self.neg()
        } else {
            self
        }
    }
}

// ---------------------------------------------------------------------------------------------------------------
// the reference's planted truths
// ---------------------------------------------------------------------------------------------------------------

/// |a - b| in units of 2^-FR, as f64
fn fx_dist(a: &Fx, b: &Fx) -> f64 {
    let d = a.sub(b);
    let dy = Dy {
        neg: false,
        m: d.m,
        e: 0,
    };
    dy.ratio(&Dy {
        neg: false,
        m: BigU::from_u64(1),
        e: 0,
    })
}

/// the planted-truth discrepancies of the reference with pi/2 = p, in units of 2^-FR: sin(pi/6) = 1/2,
/// cos(pi/3) = 1/2, 2 sin(pi/4)^2 = 1, and sin^2 + cos^2 = 1 and sin 2r = 2 sin r cos r at 16 points
fn planted(p: &Fx) -> Vec<(String, f64)> {
    let half = Fx {
        neg: false,
        m: BigU::from_u64(1).shl(FR - 1),
    };
    let one = half.mul_small(2);
    let mut out = Vec::new();
    let (s6, _) = sin_cos_fx(&p.div_small(3));
    out.push(("sin(pi/6) - 1/2".to_string(), fx_dist(&s6, &half)));
    let (_, c3) = sin_cos_fx(&p.mul_small(2).div_small(3));
    out.push(("cos(pi/3) - 1/2".to_string(), fx_dist(&c3, &half)));
    let (s4, _) = sin_cos_fx(&p.div_small(2));
    out.push((
        "2 sin(pi/4)^2 - 1".to_string(),
        fx_dist(&s4.mul(&s4).mul_small(2), &one),
    ));
    let mut rng = Rng::new(11);
    for i in 0..16 {
        let r = Fx::from_dy(&crate::qd_tests::rand_dy(&mut rng, -1 - (i % 4)));
        let (s, c) = sin_cos_fx(&r);
        out.push((
            format!("sin^2 + cos^2 - 1 at {i}"),
            fx_dist(&s.mul(&s).add(&c.mul(&c)), &one),
        ));
        let (s2, _) = sin_cos_fx(&r.mul_small(2));
        out.push((
            format!("sin 2r - 2 sin r cos r at {i}"),
            fx_dist(&s2, &s.mul(&c).mul_small(2)),
        ));
    }
    out
}

#[test]
fn trig_reference_planted_truth() {
    for (what, d) in planted(half_pi()) {
        assert!(d <= 2048.0, "{what}: {d} units of 2^-{FR}");
    }
    // pi/2 from Machin's formula, an independent derivation, agrees
    assert!(halves_agree(&machin_half_pi(), half_pi()));
}

/// pi/2 from Machin's formula, pi/4 = 4 arctan(1/5) - arctan(1/239)
fn machin_half_pi() -> Fx {
    half_pi_with(&[(4, 5)], &[(1, 239)])
}

/// two values of pi/2 agree to 4 units of 2^-FR
fn halves_agree(a: &Fx, b: &Fx) -> bool {
    fx_dist(a, b) <= 4.0
}

/// Control: with pi/2 off by 2^-2000, every planted truth that involves pi fails
#[test]
fn trig_reference_planted_truth_control() {
    let p = half_pi().add(&Fx {
        neg: false,
        m: BigU::from_u64(1).shl(FR - 2000),
    });
    let bad = planted(&p).iter().filter(|(_, d)| *d > 2048.0).count();
    assert_eq!(bad, 3, "the three checks at multiples of pi must fail");
    // and Machin's pi/2 does not agree with it
    assert!(!halves_agree(&machin_half_pi(), &p));
}

// ---------------------------------------------------------------------------------------------------------------
// the constants
// ---------------------------------------------------------------------------------------------------------------

/// the greedy rounding of a rational num / den to eight parts, checked exactly: each part c_i with
/// |num/den - sum_(j<i) c_j - c_i| < ulp(c_i)/2, so c_i = RN of the remainder (no ties occur)
fn is_greedy(parts: &[f64; 8], num: &Dy, den: &Dy) -> bool {
    let mut rem = num.clone(); // den (num/den - sum), exactly
    for (i, &c) in parts.iter().enumerate() {
        if c == 0.0 {
            // the remainder is exhausted, and every later part is zero
            return rem.is_zero() && parts[i..].iter().all(|&p| p == 0.0);
        }
        rem = rem.sub(&den.mul(&Dy::from_f64(c)));
        // |rem| < den ulp(c)/2
        let half_ulp = Dy::from_f64(f64::from_bits(c.abs().to_bits() & 0x7ff0_0000_0000_0000) * f64::EPSILON / 2.0);
        if rem.cmp_abs(&den.mul(&half_ulp)) != Ordering::Less {
            return false;
        }
    }
    true
}

/// c = RN(2/pi), for c in [1/2, 1): |c pi/2 - 1| < (pi/2) ulp(c)/2, ulp(c) = 2^-53
fn is_rn_two_over_pi(c: f64) -> bool {
    let e = Fx::from_f64(c).mul(half_pi()).sub(&Fx::from_f64(1.0));
    e.to_dy().ratio(&Fx::from_f64(1.0).to_dy()) < std::f64::consts::FRAC_PI_2 * 2f64.powi(-53) / 2.0
}

fn fact(n: u64) -> Dy {
    let mut m = BigU::from_u64(1);
    for i in 2..=n {
        m = m.mul_small(i);
    }
    Dy { neg: false, m, e: 0 }
}

/// the coefficient tables' mismatches: SIN[k] must be the greedy rounding of (-1)^k/(2k+1)!, COS[k] of (-1)^k/(2k)!
fn table_mismatches(sin: &[[f64; 8]], cos: &[[f64; 8]]) -> usize {
    let mut bad = 0;
    for (k, c) in sin.iter().enumerate() {
        let one = Dy::from_f64(if k % 2 == 0 { 1.0 } else { -1.0 });
        bad += !is_greedy(c, &one, &fact(2 * k as u64 + 1)) as usize;
    }
    for (k, c) in cos.iter().enumerate() {
        let one = Dy::from_f64(if k % 2 == 0 { 1.0 } else { -1.0 });
        bad += !is_greedy(c, &one, &fact(2 * k as u64)) as usize;
    }
    bad
}

#[test]
fn trig_constants() {
    use crate::trig::tables as t;
    assert_eq!(table_mismatches(&t::SIN, &t::COS), 0);
    // P = round(pi/2 2^F): within 1/2 + the reference's error of the reference's pi/2
    let p = Fx {
        neg: false,
        m: BigU(t::P.to_vec()).shl(FR - t::F as u64),
    };
    let d = fx_dist(&p, half_pi()) / 2f64.powi((FR - t::F as u64) as i32);
    assert!(d < 0.5 + 1e-9, "P is {d} units of 2^-{} from pi/2", t::F);
    assert!(is_rn_two_over_pi(t::TWO_OVER_PI));
    // the series lengths: the first omitted term R^(2K)/(2K+1)! (sin) or R^(2K)/(2K)! (cos) at most 2^-10 u^n of
    // sin r >= r (1 - R^2/6) or cos r >= 1 - R^2/2, R = 0.78541 or 2^-j (1 + 2^-50), checked exactly
    for (n, ks, kc) in [
        (2, &t::KS2[..], &t::KC2[..]),
        (4, &t::KS4[..], &t::KC4[..]),
        (8, &t::KS8[..], &t::KC8[..]),
    ] {
        assert_eq!(ks.len(), 53 * n / 2);
        assert_eq!(kc.len(), 53 * n / 2);
        for (j, (&k_s, &k_c)) in ks.iter().zip(kc).enumerate() {
            assert!(
                terms_in_tables(k_s as usize) && terms_in_tables(k_c as usize),
                "n = {n}, bucket {j}"
            );
            assert!(
                series_enough(n, j, k_s as u64, true),
                "sin, n = {n}, bucket {j}: {k_s} terms"
            );
            assert!(
                series_enough(n, j, k_c as u64, false),
                "cos, n = {n}, bucket {j}: {k_c} terms"
            );
        }
    }
}

/// a series length the coefficient tables can serve: 2 to their length
fn terms_in_tables(k: usize) -> bool {
    use crate::trig::tables as t;
    (2..=t::SIN.len().min(t::COS.len())).contains(&k)
}

/// R^(2K) 2^(53 n + 10) <= (2K+1)! (1 - R^2/6), or (2K)! (1 - R^2/2) for cos, exactly (R an upper bound of |r| in
/// bucket j, as a dyadic: 0.78541 < 25737/32768 = 0.785430..., and 2^-j (1 + 2^-50))
fn series_enough(n: usize, j: usize, k: u64, sine: bool) -> bool {
    let r = if j == 0 {
        Dy::from_f64(25737.0 / 32768.0)
    } else {
        Dy::from_f64(2f64.powi(-(j as i32)) * (1.0 + 2f64.powi(-50)))
    };
    let r2 = r.mul(&r);
    let mut lhs = Dy::from_f64(2f64.powi(10)).ldexp(53 * n as i64);
    for _ in 0..k {
        lhs = lhs.mul(&r2);
    }
    // (1 - R^2/6) or (1 - R^2/2), times 6 or 2 on both sides
    let (f, c) = if sine {
        (fact(2 * k + 1), 6.0)
    } else {
        (fact(2 * k), 2.0)
    };
    let rhs = f.mul(&Dy::from_f64(c).sub(&r2));
    lhs.mul(&Dy::from_f64(c)).cmp_abs(&rhs) != Ordering::Greater
}

/// Control: a coefficient one ulp off in its last part, a series one term short, and P off by one unit all fail
#[test]
fn trig_constants_control() {
    use crate::trig::tables as t;
    // series lengths past the coefficient tables, or below two
    assert!(!terms_in_tables(t::SIN.len() + 1) && !terms_in_tables(1));
    let mut sin = t::SIN;
    sin[5][7] = f64::from_bits(sin[5][7].to_bits() + 1);
    assert_eq!(table_mismatches(&sin, &t::COS), 1);
    // an exact remainder followed by a nonzero part
    let mut cos = t::COS;
    assert_eq!(cos[1][..2], [-0.5, 0.0]);
    cos[1][2] = 2f64.powi(-54);
    assert_eq!(table_mismatches(&t::SIN, &cos), 1);
    assert!(!is_rn_two_over_pi(f64::from_bits(t::TWO_OVER_PI.to_bits() + 1)));
    assert!(!is_rn_two_over_pi(1.0));
    assert!(!series_enough(8, 0, t::KS8[0] as u64 - 1, true));
    assert!(!series_enough(4, 3, t::KC4[3] as u64 - 1, false));
    let mut pm = t::P.to_vec();
    pm[0] += 1;
    let p = Fx {
        neg: false,
        m: BigU(pm).shl(FR - t::F as u64),
    };
    let d = fx_dist(&p, half_pi()) / 2f64.powi((FR - t::F as u64) as i32);
    assert!(d > 0.5, "P + 1 is {d} units from pi/2");
}

// ---------------------------------------------------------------------------------------------------------------
// the types
// ---------------------------------------------------------------------------------------------------------------

trait Ty: Copy + std::fmt::Debug {
    /// parts
    const N: usize;
    const NAME: &'static str;
    /// the bounds in units of u^n: sin and cos, tan
    const BOUND: [f64; 2];
    fn from_parts(p: &[f64]) -> Self;
    fn parts(&self) -> Vec<f64>;
    fn sin(self) -> Self;
    fn cos(self) -> Self;
    fn tan(self) -> Self;
    fn sin_cos(self) -> (Self, Self);
    /// a b + c in the type's arithmetic: a renormalized value that need not be the greedy rounding
    fn mul_add(self, b: Self, c: Self) -> Self;
}

impl Ty for DD {
    const N: usize = 2;
    const NAME: &'static str = "dd";
    const BOUND: [f64; 2] = DD_BOUND;
    fn from_parts(p: &[f64]) -> DD {
        DD { hi: p[0], lo: p[1] }
    }
    fn parts(&self) -> Vec<f64> {
        vec![self.hi, self.lo]
    }
    fn sin(self) -> DD {
        DD::sin(self)
    }
    fn cos(self) -> DD {
        DD::cos(self)
    }
    fn tan(self) -> DD {
        DD::tan(self)
    }
    fn sin_cos(self) -> (DD, DD) {
        DD::sin_cos(self)
    }
    fn mul_add(self, b: DD, c: DD) -> DD {
        self * b + c
    }
}

impl Ty for QD {
    const N: usize = 4;
    const NAME: &'static str = "qd";
    const BOUND: [f64; 2] = [32.0, 64.0];
    fn from_parts(p: &[f64]) -> QD {
        QD {
            x: [p[0], p[1], p[2], p[3]],
        }
    }
    fn parts(&self) -> Vec<f64> {
        self.x.to_vec()
    }
    fn sin(self) -> QD {
        QD::sin(self)
    }
    fn cos(self) -> QD {
        QD::cos(self)
    }
    fn tan(self) -> QD {
        QD::tan(self)
    }
    fn sin_cos(self) -> (QD, QD) {
        QD::sin_cos(self)
    }
    fn mul_add(self, b: QD, c: QD) -> QD {
        self * b + c
    }
}

impl Ty for OD {
    const N: usize = 8;
    const NAME: &'static str = "od";
    const BOUND: [f64; 2] = OD_BOUND;
    fn from_parts(p: &[f64]) -> OD {
        let mut x = [0.0; 8];
        x.copy_from_slice(p);
        OD { x }
    }
    fn parts(&self) -> Vec<f64> {
        self.x.to_vec()
    }
    fn sin(self) -> OD {
        OD::sin(self)
    }
    fn cos(self) -> OD {
        OD::cos(self)
    }
    fn tan(self) -> OD {
        OD::tan(self)
    }
    fn sin_cos(self) -> (OD, OD) {
        OD::sin_cos(self)
    }
    fn mul_add(self, b: OD, c: OD) -> OD {
        self * b + c
    }
}

/// the proven bounds in units of u^n (`paper/trig_consts.py`), rounded up: sin and cos, tan
const DD_BOUND: [f64; 2] = [7.85, 28.5];
const OD_BOUND: [f64; 2] = [3.17, 6.42];

fn exact<T: Ty>(x: T) -> Dy {
    Dy::sum(&x.parts())
}

/// greedy rounding to N parts
fn greedy<T: Ty>(d: &Dy) -> T {
    let mut rem = d.clone();
    let mut p = vec![0.0; T::N];
    for v in p.iter_mut() {
        let c = rem.to_f64();
        if c == 0.0 {
            break;
        }
        *v = c;
        rem = rem.sub(&Dy::from_f64(c));
    }
    T::from_parts(&p)
}

/// a random exact value ±(1 + f) 2^e with a 255-bit fraction f
fn rand_at(r: &mut Rng, e: i64) -> Dy {
    crate::qd_tests::rand_dy(r, e)
}

/// a random exact value with a random exponent in [lo, hi]
fn rand_r(r: &mut Rng, lo: i64, hi: i64) -> Dy {
    let e = r.int(lo, hi);
    rand_at(r, e)
}

/// uniform in [0, 1)
fn unit(r: &mut Rng) -> f64 {
    (r.next() >> 11) as f64 * 2f64.powi(-53)
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum Cat {
    /// |x| from 2^-8 to 2^20, greedy parts
    Random,
    /// a b + c in the type's arithmetic, |x| up to about 4
    Ops,
    /// |x| from 2^-(53n/2) / 16 to 2^-8: the tiny path and the small buckets
    Small,
    /// the greedy rounding of k pi/2, 1 <= k <= 2^20, and of k pi/2 plus a few ulps of its last part
    NearPi2,
    /// k pi/2 +- 0.7854 (1 +- 2^-30): the reduction's top bucket and its correction of k
    Edge,
    /// |x| from 2^48 to 2^52
    Limit,
}

const CATS: [Cat; 6] = [Cat::Random, Cat::Ops, Cat::Small, Cat::NearPi2, Cat::Edge, Cat::Limit];

/// k pi/2 as an exact dyadic to 2^-FR
fn k_half_pi(k: i64) -> Dy {
    half_pi().mul_small(k.unsigned_abs()).neg_if(k < 0).to_dy()
}

fn inputs<T: Ty>(cat: Cat, n: usize, seed: u64) -> Vec<T> {
    let mut r = Rng::new(seed ^ (cat as u64) << 32 ^ (T::N as u64) << 40);
    let tiny = -(53 * T::N as i64) / 2;
    (0..n)
        .map(|i| match cat {
            Cat::Random => greedy(&rand_r(&mut r, -8, 19)),
            Cat::Ops => {
                let a: T = greedy(&rand_r(&mut r, -2, 1));
                let b: T = greedy(&rand_r(&mut r, -2, 0));
                let c: T = greedy(&rand_r(&mut r, -30, 0));
                a.mul_add(b, c)
            }
            // every eighth sample in the binade just below the early return, where its error is largest
            Cat::Small if i % 8 == 0 => greedy(&rand_at(&mut r, tiny - 1)),
            Cat::Small => greedy(&rand_r(&mut r, tiny - 4, -9)),
            Cat::NearPi2 => {
                let (a, b) = (r.int(0, 19), r.int(0, 1 << 10));
                let k = (1i64 << a) + b;
                let k = if r.next() & 1 == 1 { -k } else { k };
                let x: T = greedy(&k_half_pi(k));
                // a few units of the last part's ulp, or none
                let last = x.parts()[T::N - 1];
                let d =
                    r.int(-3, 3) as f64 * f64::from_bits(last.abs().to_bits() & 0x7ff0_0000_0000_0000) * 2f64.powi(-52);
                greedy(&exact(x).add(&Dy::from_f64(d)))
            }
            Cat::Edge => {
                let e = r.int(1, 50);
                let k = r.int(1, 1 << e);
                let off = R_TH * (1.0 + (2.0 * unit(&mut r) - 1.0) * 2f64.powi(-30));
                let off = if r.next() & 1 == 1 { -off } else { off };
                greedy(&k_half_pi(k).add(&Dy::from_f64(off)))
            }
            Cat::Limit => {
                let x: T = greedy(&rand_r(&mut r, 48, 51));
                x
            }
        })
        .collect()
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum Fun {
    Sin,
    Cos,
    Tan,
}

const FUNS: [Fun; 3] = [Fun::Sin, Fun::Cos, Fun::Tan];

/// the error of f(x) in units of u^n relative to the exact value, after subtracting the reduction's absolute
/// allowance: 2^-1163 for sin and cos, and for tan 2^-1163 |cos x| from |got cos x - sin x|, which allows less than
/// the theorem's 2^-1163 / |sin x cos x| relative
fn err<T: Ty>(f: Fun, x: T, got: T, sc: &(Fx, Fx)) -> f64 {
    let un = 2f64.powi(-53 * T::N as i32);
    let g = Fx::from_dy(&exact(got));
    // tan: |got cos - sin| / |sin|, the relative error of got as sin / cos
    let (num, den) = match f {
        Fun::Sin => (g.sub(&sc.0), sc.0.clone()),
        Fun::Cos => (g.sub(&sc.1), sc.1.clone()),
        Fun::Tan => (g.mul(&sc.1).sub(&sc.0), sc.0.clone()),
    };
    let dd = den.to_dy();
    assert!(
        dd.m.bits() as i64 - FR as i64 > -1500,
        "{} {f:?}({x:?}): exact value below 2^-1500, beyond the reference's accuracy",
        T::NAME
    );
    let a = Dy::from_f64(1.0).ldexp(-1163);
    let a = if f == Fun::Tan { a.mul(&sc.1.to_dy().abs()) } else { a };
    let e = num.to_dy().abs();
    let e = if e.cmp_abs(&a) == Ordering::Greater {
        e.sub(&a)
    } else {
        Dy::zero()
    };
    e.ratio(&dd) / un
}

struct Row {
    cat: Cat,
    fun: Fun,
    n: usize,
    worst: f64,
    fails: usize,
    /// log2 of the least |f(x)|
    least: i64,
}

fn run<T: Ty>(n: usize, seed: u64) -> Vec<Row> {
    let mut rows = Vec::new();
    for cat in CATS {
        let xs: Vec<T> = inputs(cat, n, seed);
        let refs: Vec<(Fx, Fx)> = xs.iter().map(|&x| reference(&exact(x))).collect();
        for fun in FUNS {
            let thr = if fun == Fun::Tan { T::BOUND[1] } else { T::BOUND[0] };
            let mut row = Row {
                cat,
                fun,
                n: xs.len(),
                worst: 0.0,
                fails: 0,
                least: i64::MAX,
            };
            for (&x, sc) in xs.iter().zip(&refs) {
                let got = match fun {
                    Fun::Sin => x.sin(),
                    Fun::Cos => x.cos(),
                    Fun::Tan => x.tan(),
                };
                let e = err(fun, x, got, sc);
                let f = if fun == Fun::Cos { &sc.1 } else { &sc.0 };
                row.least = row.least.min(f.m.bits() as i64 - FR as i64);
                row.worst = row.worst.max(e);
                // a NaN error fails
                row.fails += !matches!(e.partial_cmp(&thr), Some(Ordering::Less | Ordering::Equal)) as usize;
            }
            rows.push(row);
        }
    }
    rows
}

fn report() -> bool {
    std::env::var("TRIG_REPORT").map(|v| v == "1").unwrap_or(false)
}

/// TRIG_N, at least 1 (default 1)
fn scale() -> usize {
    let n = std::env::var("TRIG_N").ok().and_then(|v| v.parse().ok()).unwrap_or(1);
    assert!(n > 0, "TRIG_N must be at least 1");
    n
}

/// n samples times TRIG_N, which must not overflow
fn samples(n: usize) -> usize {
    n.checked_mul(scale()).expect("TRIG_N too large")
}

fn print_rows<T: Ty>(rows: &[Row]) {
    println!(
        "{}: error in u^{} (bounds {} for sin and cos, {} for tan)",
        T::NAME,
        T::N,
        T::BOUND[0],
        T::BOUND[1]
    );
    println!(
        "{:<8} {:<4} {:>6} {:>12} {:>6}",
        "category", "fn", "n", "worst", "fails"
    );
    for r in rows {
        println!(
            "{:<8} {:<4} {:>6} {:>12.4e} {:>6} {:>12}",
            format!("{:?}", r.cat),
            format!("{:?}", r.fun),
            r.n,
            r.worst,
            r.fails,
            format!("2^{}", r.least)
        );
    }
}

fn accuracy<T: Ty>(n: usize) {
    let rows = run::<T>(samples(n), 1);
    if report() {
        print_rows::<T>(&rows);
    }
    let bad: Vec<String> = rows
        .iter()
        .filter(|r| r.fails > 0)
        .map(|r| {
            format!(
                "{} {:?} {:?}: {} of {} past the bound, worst {:.3e} u^n",
                T::NAME,
                r.cat,
                r.fun,
                r.fails,
                r.n,
                r.worst
            )
        })
        .collect();
    assert!(bad.is_empty(), "{bad:#?}");
}

#[test]
fn trig_dd_accuracy() {
    accuracy::<DD>(2000);
}

#[test]
fn trig_qd_accuracy() {
    accuracy::<QD>(1000);
}

#[test]
fn trig_od_accuracy() {
    accuracy::<OD>(500);
}

/// The inputs of the paper's Table 1 for the octo-double sin, cos and tan (paper/table1_inputs.py), with the floors
/// their errors reach in units of u^8: x chosen so that f(x) lies just past 2^E (1 + u + ... + u^7) and the result
/// is 2^E (1, u, ..., u^7) up to sign, the ninth part that the renormalization drops near u^8 2^E.
const OD_TABLE1: [(Fun, [u64; 8], f64); 3] = [
    (
        Fun::Sin,
        [
            0x3ee000000000aaab,
            0x3b75555eeef6eef2,
            0x381729d2975900e8,
            0x348a195a54a29eb4,
            0x3128cc3a41f5cda2,
            0xad6de6f5c4da02df,
            0x29dad523df82f39d,
            0x261efb1a1688e432,
        ],
        0.999999995,
    ),
    (
        Fun::Cos,
        [
            0x3ff941fb6999a8d4,
            0x3c98b0c392810f09,
            0xb93572503683ff67,
            0xb58f05686f022788,
            0xb1ca742cfa0db1ed,
            0x2e6693f13d61b2d3,
            0xab0bccc00c1d973a,
            0xa7a798c3c05b350e,
        ],
        1.00069,
    ),
    (
        Fun::Tan,
        [
            0x3e0000000000000e,
            0x3aaffaaaaaaaaaac,
            0xb748f55222222223,
            0xb3eb04e88ad1ad57,
            0x307dc840ac82561c,
            0x2d0b1f36bfab0d59,
            0x299bd6c73c83ad94,
            0xa5fdb97f61d2dd6c,
        ],
        1.00138,
    ),
];

/// The octo-double sin, cos and tan on the inputs of the paper's Table 1. Pass: each result 2^E (1, u, ..., u^7) up to
/// sign, scalar and lanes alike, and the check, the error between its floor and the proven bound. Controls: the check
/// rejects a wrong result past the bound (the last part 16 2^E u^8 further out) and one far more accurate (the greedy
/// eight parts of the sum of the result's parts and 2^E u^8), and each input with its leading part one ulp up errs by
/// less than its floor.
#[test]
fn trig_od_table1_inputs() {
    use crate::native::OV;
    let u = 2f64.powi(-53);
    let eval = |f: Fun, x: OD| match f {
        Fun::Sin => (x.sin(), OV::splat(x).sin().lane(0)),
        Fun::Cos => (x.cos(), OV::splat(x).cos().lane(0)),
        Fun::Tan => (x.tan(), OV::splat(x).tan().lane(0)),
    };
    for (f, b, floor) in OD_TABLE1 {
        let x = OD {
            x: b.map(f64::from_bits),
        };
        let sc = reference(&exact(x));
        let bound = if f == Fun::Tan { OD_BOUND[1] } else { OD_BOUND[0] };
        // the error of y as f(x) in units of u^8, and whether the check passes it
        let check = |y: OD| -> (f64, bool) {
            let e = err(f, x, y, &sc);
            (e, e >= floor && e <= bound)
        };
        let (got, lane) = eval(f, x);
        let top = got.x[0];
        let pow = f64::from_bits(top.abs().to_bits() & 0x7ff0_0000_0000_0000).copysign(top);
        let ladder = (1..8).all(|k| got.x[k] == pow * u.powi(k as i32));
        assert!(ladder, "{f:?}: the result is not 2^E (1, u, ..., u^7)");
        assert_eq!(got.x, lane.x, "{f:?}: lanes differ from the scalar result");
        let (e, ok) = check(got);
        println!("{f:?}: error {e:.9} u^8, floor {floor}");
        assert!(ok, "{f:?}: error {e} u^8 outside [{floor}, {bound}]");
        let mut hi = got;
        hi.x[7] += 16.0 * pow * u.powi(8);
        let lo: OD = greedy(&exact(got).add(&Dy::from_f64(pow * u.powi(8))));
        let ((eh, okh), (el, okl)) = (check(hi), check(lo));
        let mut y = x;
        y.x[0] = y.x[0].next_up();
        let ey = err(f, y, eval(f, y).0, &reference(&exact(y)));
        println!("  controls: {eh:.3e} and {el:.3e} u^8 for the wrong results, {ey:.3e} u^8 for x one ulp up");
        assert!(!okh && !okl, "{f:?} control: the check passes a wrong result");
        assert!(
            ey < floor,
            "{f:?} control: {ey} u^8, the input one ulp up still reaches the floor"
        );
    }
}

/// crate::trig::reduce on parts of any of the three lengths
fn reduce_parts(x: &[f64]) -> (u32, Vec<f64>) {
    match x.len() {
        2 => {
            let (q, r) = crate::trig::reduce::<2, 8>(&[x[0], x[1]]);
            (q, r.to_vec())
        }
        4 => {
            let (q, r) = crate::trig::reduce::<4, 12>(&[x[0], x[1], x[2], x[3]]);
            (q, r.to_vec())
        }
        _ => {
            let mut a = [0.0; 8];
            a.copy_from_slice(x);
            let (q, r) = crate::trig::reduce::<8, 20>(&a);
            (q, r.to_vec())
        }
    }
}

/// The reduction's failures on xs: r must be x itself when k = 0, and otherwise within u^n |rem| + 2^-1164 of
/// rem = x - k pi/2 for an integer k = q mod 4 with |rem| <= 0.7854 (1 + 2^-52), with greedy parts (|r_(i+1)| <=
/// ulp(r_i)/2). k is the reference's k or one off it, where |rem| is near pi/4.
fn reduction_failures<T: Ty>(xs: &[T]) -> usize {
    let p = half_pi();
    let un = Dy::from_f64(2f64.powi(-53 * T::N as i32));
    let a = Dy::from_f64(1.0).ldexp(-1164);
    let top = Dy::from_f64(R_TH * (1.0 + 2f64.powi(-52)));
    let mut bad = 0;
    for &x in xs {
        let parts = x.parts();
        let (q, r) = reduce_parts(&parts);
        let ex = exact(x);
        let k0 = (ex.to_f64() / std::f64::consts::FRAC_PI_2).round() as i64;
        // the code's own k = 0 test: r is x, exactly
        if (x.parts()[0] * crate::trig::tables::TWO_OVER_PI).round() == 0.0 {
            bad += (q != 0 || r != parts) as usize;
            continue;
        }
        let rd = Dy::sum(&r);
        let ok = (-2..=2).any(|d: i64| {
            let k = k0 + d;
            if k.rem_euclid(4) != q as i64 {
                return false;
            }
            let rem = Fx::from_dy(&ex)
                .sub(&p.mul_small(k.unsigned_abs()).neg_if(k < 0))
                .to_dy();
            let err = rd.sub(&rem).abs();
            rem.cmp_abs(&top) != Ordering::Greater && err.cmp_abs(&un.mul(&rem).add(&a)) != Ordering::Greater
        });
        let greedy = r.windows(2).all(|w| {
            w[1] == 0.0
                || w[1].abs() <= f64::from_bits(w[0].abs().to_bits() & 0x7ff0_0000_0000_0000) * f64::EPSILON / 2.0
        });
        bad += !(ok && greedy) as usize;
    }
    bad
}

#[test]
fn trig_reduction() {
    for cat in CATS {
        let n = samples(200);
        assert_eq!(reduction_failures(&inputs::<DD>(cat, n, 7)), 0, "dd {cat:?}");
        assert_eq!(reduction_failures(&inputs::<QD>(cat, n, 7)), 0, "qd {cat:?}");
        assert_eq!(reduction_failures(&inputs::<OD>(cat, n, 7)), 0, "od {cat:?}");
    }
}

/// sin_cos is bitwise (sin, cos)
fn sin_cos_mismatches<T: Ty>(xs: &[T]) -> usize {
    xs.iter()
        .filter(|&&x| {
            let (s, c) = x.sin_cos();
            let bits = |v: T| v.parts().iter().map(|p| p.to_bits()).collect::<Vec<_>>();
            bits(s) != bits(x.sin()) || bits(c) != bits(x.cos())
        })
        .count()
}

#[test]
fn trig_sin_cos_is_sin_and_cos() {
    for cat in CATS {
        assert_eq!(sin_cos_mismatches(&inputs::<DD>(cat, 200, 3)), 0);
        assert_eq!(sin_cos_mismatches(&inputs::<QD>(cat, 100, 3)), 0);
        assert_eq!(sin_cos_mismatches(&inputs::<OD>(cat, 50, 3)), 0);
    }
}

fn special<T: Ty>() {
    let p = |v: f64| {
        let mut x = vec![0.0; T::N];
        x[0] = v;
        T::from_parts(&x)
    };
    let lead = |v: T| v.parts()[0];
    let bits = |v: T| v.parts().iter().map(|p| p.to_bits()).collect::<Vec<_>>();
    for v in [
        f64::NAN,
        f64::INFINITY,
        f64::NEG_INFINITY,
        2f64.powi(52) * (1.0 + f64::EPSILON),
        -1e300,
    ] {
        let x = p(v);
        assert!(
            lead(x.sin()).is_nan() && lead(x.cos()).is_nan() && lead(x.tan()).is_nan(),
            "{} {v}",
            T::NAME
        );
        let (s, c) = x.sin_cos();
        assert!(lead(s).is_nan() && lead(c).is_nan());
    }
    // a NaN in a lower part
    let mut q = vec![0.0; T::N];
    q[0] = 1.0;
    q[T::N - 1] = f64::NAN;
    assert!(lead(T::from_parts(&q).sin()).is_nan());
    for z in [0.0, -0.0] {
        let x = p(z);
        assert_eq!(bits(x.sin()), bits(x), "{} sin({z})", T::NAME);
        assert_eq!(bits(x.tan()), bits(x), "{} tan({z})", T::NAME);
        assert_eq!(lead(x.cos()), 1.0);
        assert_eq!(bits(x.sin_cos().0), bits(x));
    }
    // tiny arguments return themselves, and 2^52 itself is inside the limit
    for v in [5e-324f64, -2.2250738585072014e-308, 1e-200] {
        if v.abs() < 2f64.powi(-(53 * T::N as i32) / 2) {
            assert_eq!(bits(p(v).sin()), bits(p(v)));
            assert_eq!(lead(p(v).cos()), 1.0);
        }
    }
    assert!(lead(p(2f64.powi(52)).sin()).is_finite());
}

#[test]
fn trig_special_values() {
    special::<DD>();
    special::<QD>();
    special::<OD>();
}

/// Parts off the ladder, (1, 2^60, 0, ...), whose reduction leaves |r_0| above 1: a finite value, no panic
#[test]
fn trig_off_ladder_inputs() {
    fn check<T: Ty>() {
        let mut p = vec![0.0; T::N];
        p[0] = 1.0;
        p[1] = 2f64.powi(60);
        let x = T::from_parts(&p);
        for y in [x.sin(), x.cos(), x.tan()] {
            assert!(y.parts().iter().all(|v| v.is_finite()), "{} {x:?}: {y:?}", T::NAME);
        }
    }
    check::<DD>();
    check::<QD>();
    check::<OD>();
}

/// The reduced argument of a double-double is a double-word number (r_0 = RN(r_0 + r_1)), as the double-word bounds
/// need, on double-word inputs whose greedy reduced argument is a tie, |r_1| = ulp(r_0)/2 with r_0 odd. Control: the
/// greedy reduction itself (`trig::reduce`) gives a pair that is not a double-word number on each of them.
#[test]
fn trig_dd_reduced_is_double_word() {
    use crate::trig::Ext;
    let ties = [
        (0x401a552e8777604b_u64, 0xbc5676733ae8fe48_u64),
        (0x4023731618ccbb6c, 0x3c5e4e5327a28294),
        (0x4034b86901443171, 0xbc64807b3fba9d35),
    ];
    for (h, l) in ties {
        let x = DD {
            hi: f64::from_bits(h),
            lo: f64::from_bits(l),
        };
        assert_eq!(x.hi + x.lo, x.hi, "{x:?} is not a double-word number");
        let (_, g) = crate::trig::reduce_exact::<2>(&[x.hi, x.lo]);
        assert_ne!(
            g[0] + g[1],
            g[0],
            "control: the greedy r of {x:?} is a double-word number"
        );
        let (_, r) = x.reduce();
        assert_eq!(r.hi + r.lo, r.hi, "{x:?}: r = {r:?}");
    }
}

/// Controls: each deliberate breakage must fail the accuracy checks of the functions it touches
#[cfg(feature = "mutate")]
#[test]
fn trig_controls() {
    fn fails<T: Ty>(id: u32, n: usize) -> Vec<(Fun, usize)> {
        mutate::set(id);
        let rows = run::<T>(n, 5);
        mutate::set(0);
        FUNS.iter()
            .map(|&f| (f, rows.iter().filter(|r| r.fun == f).map(|r| r.fails).sum()))
            .collect()
    }
    let want: [(u32, &[Fun]); 5] = [
        (mutate::REDUCE_TAIL, &[Fun::Sin, Fun::Cos, Fun::Tan]),
        (mutate::REDUCE_PI_SHORT, &[Fun::Sin, Fun::Cos, Fun::Tan]),
        (mutate::SIN_SHORT, &[Fun::Sin, Fun::Cos, Fun::Tan]),
        (mutate::COS_SHORT, &[Fun::Sin, Fun::Cos, Fun::Tan]),
        (mutate::TAN_DIV_SHORT, &[Fun::Tan]),
    ];
    let mut missed = Vec::new();
    for (id, funs) in want {
        for (name, got) in [
            ("dd", fails::<DD>(id, 60)),
            ("qd", fails::<QD>(id, 40)),
            ("od", fails::<OD>(id, 30)),
        ] {
            for f in funs {
                let n = got.iter().find(|(g, _)| g == f).unwrap().1;
                if n == 0 {
                    missed.push(format!("{name} {:?} under '{}'", f, mutate::NAMES[id as usize]));
                }
            }
        }
    }
    // the reduction's own check fails under the reduction's mutations
    for id in [mutate::REDUCE_TAIL, mutate::REDUCE_PI_SHORT] {
        mutate::set(id);
        let f = reduction_failures(&inputs::<DD>(Cat::NearPi2, 40, 5))
            + reduction_failures(&inputs::<QD>(Cat::NearPi2, 40, 5))
            + reduction_failures(&inputs::<OD>(Cat::NearPi2, 40, 5));
        mutate::set(0);
        if f == 0 {
            missed.push(format!("reduction check under '{}'", mutate::NAMES[id as usize]));
        }
    }
    assert!(missed.is_empty(), "controls that did not fail: {missed:#?}");
}

// ---------------------------------------------------------------------------------------------------------------
// the fast reduction
// ---------------------------------------------------------------------------------------------------------------

/// k P 2^-F, k times the reduction's pi/2, exactly
fn k_c(k: i64) -> Dy {
    Dy {
        neg: k < 0,
        m: BigU(crate::trig::tables::P.to_vec()).mul_small(k.unsigned_abs()),
        e: -(crate::trig::tables::F as i64),
    }
}

fn sign(r: &mut Rng) -> f64 {
    if r.next() & 1 == 1 {
        -1.0
    } else {
        1.0
    }
}

/// ulp(v) for a normal v
fn ulp(v: f64) -> f64 {
    f64::from_bits(v.abs().to_bits() & 0x7ff0_0000_0000_0000) * f64::EPSILON
}

/// the kinds of argument of the fast reduction's checks
#[derive(Clone, Copy, PartialEq, Debug)]
enum FCat {
    /// greedy parts, |x| from 2^-1 to 2^52, and 2^52 and 2^52 - 1 with a lower part
    Wide,
    /// |x| below 1: k = 0 and k = +-1 side by side, and tiny
    Small,
    /// the greedy rounding of k pi/2 (k up to 2^51), or of k pi/2 plus a few units of its last part (k up to 2^40): the
    /// deepest cancellations
    NearPi2,
    /// k pi/2 + t, k up to 2^40 and t with random bits from 2^-20 to 2^-(53 (n - 1) + 20) down to below the last
    /// part's: the depths where the fast reduction runs out of bits
    Mid,
    /// k pi/2 + t, t's remainder after its part i at or within 2^-27 ulp(t_i) of the tie ulp(t_i)/2
    NearTie,
    /// k pi/2 +- 0.7854 (1 +- 2^-30), k up to 2^50: the correction of k
    Edge,
    /// parts off the ladder: a lower part above 2^20, parts that do not decrease, a subnormal lower part
    Off,
}

const FCATS: [FCat; 7] = [
    FCat::Wide,
    FCat::Small,
    FCat::NearPi2,
    FCat::Mid,
    FCat::NearTie,
    FCat::Edge,
    FCat::Off,
];

/// k C + t, t = t_0 + ... + t_i + ulp(t_i)/2 + d with d = 0 or +-2^-(27 + m) ulp(t_i), m in [0, 40]: the remainder that
/// the greedy rounding meets at step i is within d + ulp(x_(n-1)) of a tie. k <= 2^10 keeps ulp(x_(n-1)) below
/// 2^-21 of the zone, as i <= n - 2 (i = 0 for n = 2).
fn near_tie<T: Ty>(r: &mut Rng) -> T {
    let n = T::N as i64;
    let i = r.int(0, (n - 2).max(0)) as usize;
    let k = (1 + r.int(0, 1 << 10)) * sign(r) as i64;
    let mut t = vec![sign(r) * (0.1 + 0.68 * unit(r))];
    for l in 0..i {
        t.push(sign(r) * (1.0 + unit(r)) * ulp(t[l]) / 4.0);
    }
    let u = ulp(t[i]);
    let d = match r.int(0, 3) {
        0 => 0.0,
        _ => sign(r) * u * 2f64.powi(-27 - r.int(0, 40) as i32),
    };
    let target = k_c(k)
        .add(&Dy::sum(&t))
        .add(&Dy::from_f64(sign(r) * u / 2.0))
        .add(&Dy::from_f64(d));
    greedy(&target)
}

fn fast_input<T: Ty>(r: &mut Rng, cat: FCat) -> T {
    let n = T::N;
    match cat {
        FCat::Wide => match r.int(0, 7) {
            // 2^52 and 2^52 - 1, the largest arguments, with a lower part
            0 => {
                let top = 2f64.powi(52) - r.int(0, 1) as f64;
                greedy(&Dy::from_f64(sign(r) * top).add(&rand_r(r, -60, -2)))
            }
            _ => greedy(&rand_r(r, -1, 51)),
        },
        FCat::Small => match r.int(0, 3) {
            0 => greedy(&rand_r(r, -1000, -4)),
            _ => greedy(&rand_r(r, -3, -1)),
        },
        FCat::NearPi2 => match r.int(0, 1) {
            0 => {
                let k = (1i64 << r.int(0, 50)) + r.int(0, 1 << 20);
                greedy(&k_c(k * sign(r) as i64))
            }
            _ => {
                let k = (1i64 << r.int(0, 40)) + r.int(0, 1 << 10);
                let x: T = greedy(&k_half_pi(k * sign(r) as i64));
                let d = r.int(-3, 3) as f64 * ulp(x.parts()[n - 1]);
                greedy(&exact(x).add(&Dy::from_f64(d)))
            }
        },
        FCat::Mid => {
            let k = (1i64 << r.int(0, 40)) + r.int(0, 1 << 10);
            let e = r.int(20, 53 * (n as i64 - 1) + 20);
            let mut m: Vec<u64> = (0..10).map(|_| r.next()).collect();
            m[9] |= 1 << 63;
            let t = Dy {
                neg: r.next() & 1 == 1,
                m: BigU(m),
                e: -e - 639,
            };
            greedy(&k_c(k * sign(r) as i64).add(&t))
        }
        FCat::NearTie => near_tie(r),
        FCat::Edge => {
            let e = r.int(1, 50);
            let k = r.int(1, 1 << e);
            let off = sign(r) * R_TH * (1.0 + (2.0 * unit(r) - 1.0) * 2f64.powi(-30));
            greedy(&k_half_pi(k * sign(r) as i64).add(&Dy::from_f64(off)))
        }
        FCat::Off => {
            let mut p = vec![0.0; n];
            p[0] = sign(r) * (1.0 + unit(r)) * 2f64.powi(r.int(0, 40) as i32);
            match r.int(0, 2) {
                0 => p[1] = sign(r) * (1.0 + unit(r)) * 2f64.powi(r.int(19, 40) as i32),
                1 => {
                    for v in p.iter_mut().skip(1) {
                        *v = sign(r) * unit(r) * 2f64.powi(-r.int(0, 60) as i32);
                    }
                }
                _ => p[n - 1] = sign(r) * f64::from_bits(1 + r.next() % (1 << 52)),
            }
            T::from_parts(&p)
        }
    }
}

/// vectors of 8 arguments with their kinds: of one kind on every fourth vector, of a kind per lane on the others
fn fast_vectors<T: Ty>(n: usize, seed: u64) -> Vec<[(T, FCat); 8]> {
    let mut r = Rng::new(seed ^ (T::N as u64) << 40);
    (0..n)
        .map(|v| {
            let one = FCATS[r.int(0, 6) as usize];
            std::array::from_fn(|_| {
                let cat = if v % 4 == 0 { one } else { FCATS[r.int(0, 6) as usize] };
                (fast_input(&mut r, cat), cat)
            })
        })
        .collect()
}

fn parts_n<T: Ty, const N: usize>(x: T) -> [f64; N] {
    x.parts().try_into().unwrap()
}

/// the counts of a run of the fast reduction, by kind of argument
#[derive(Clone, Copy, Default, Debug, PartialEq)]
struct FastCount {
    /// lanes with k != 0
    k: usize,
    /// of those, the lanes the fast reduction decides
    decided: usize,
    /// lanes whose `reduce` (scalar) differs from `reduce_exact` in any bit of q or r
    scalar_bad: usize,
}

/// The scalar fast reduction on vectors of arguments: per kind, the lanes with k != 0, those it decides, and the
/// lanes where `reduce` differs from `reduce_exact`
fn fast_counts<T: Ty, const N: usize, const L: usize>(vs: &[[(T, FCat); 8]]) -> Vec<(FCat, FastCount)> {
    let mut c: Vec<(FCat, FastCount)> = FCATS.iter().map(|&f| (f, FastCount::default())).collect();
    for v in vs {
        for &(x, cat) in v {
            let p = parts_n::<T, N>(x);
            let row = &mut c.iter_mut().find(|e| e.0 == cat).unwrap().1;
            let k = (p[0] * crate::trig::tables::TWO_OVER_PI).round();
            if k != 0.0 {
                row.k += 1;
                row.decided += crate::trig::fast_reduce::fast::<f64, N, L>(&p, k).2 as usize;
            }
            let (a, b) = (crate::trig::reduce::<N, L>(&p), crate::trig::reduce_exact::<N>(&p));
            let same = a.0 == b.0 && a.1.iter().zip(&b.1).all(|(u, v)| u.to_bits() == v.to_bits());
            row.scalar_bad += !same as usize;
        }
    }
    c
}

/// by kind: lanes whose q or r differs from `reduce_exact`, lanes whose decision differs from the scalar one
type LaneRows = Vec<(FCat, usize, usize)>;

/// a kernel: the lanes' reduction on the vectors, (lanes whose q or r differs from `reduce_exact` in any bit, lanes
/// whose decision differs from the scalar fast reduction's), by kind
#[derive(Clone)]
struct FastLanes<const N: usize, const L: usize>(Vec<[([f64; N], FCat); 8]>);

impl<const N: usize, const L: usize> crate::simd::Kernel for FastLanes<N, L> {
    type Output = LaneRows;
    #[inline(always)]
    fn run<S: crate::simd::Simd>(self) -> Self::Output {
        use crate::v8::V8;
        let mut out: LaneRows = FCATS.iter().map(|&f| (f, 0, 0)).collect();
        for v in &self.0 {
            let c: [V8<S>; N] = std::array::from_fn(|i| V8::from_array(std::array::from_fn(|l| v[l].0[i])));
            let (q, r) = crate::trig::reduce_lanes::<S, N, L>(&c);
            let (q, r) = (q.to_array(), r.map(|x| x.to_array()));
            let t = c[0].mul(V8::splat(crate::trig::tables::TWO_OVER_PI));
            let k = crate::trig::fast_reduce::round_away(t);
            let ok = crate::trig::fast_reduce::fast::<V8<S>, N, L>(&c, k).2.bits();
            let k = k.to_array();
            for l in 0..8 {
                let (x, cat) = v[l];
                let (qe, re) = crate::trig::reduce_exact::<N>(&x);
                let same = q[l] == qe as f64 && (0..N).all(|i| r[i][l].to_bits() == re[i].to_bits());
                let one = k[l] != 0.0 && crate::trig::fast_reduce::fast::<f64, N, L>(&x, k[l]).2;
                let row = out.iter_mut().find(|e| e.0 == cat).unwrap();
                row.1 += !same as usize;
                row.2 += (k[l] != 0.0 && one != (ok >> l & 1 == 1)) as usize;
            }
        }
        out
    }
}

/// per backend, by kind: lanes that differ from `reduce_exact`, and decisions that differ from the scalar ones
fn fast_lanes<T: Ty, const N: usize, const L: usize>(vs: &[[(T, FCat); 8]]) -> Vec<(&'static str, LaneRows)> {
    let v = vs.iter().map(|v| v.map(|(x, c)| (parts_n::<T, N>(x), c))).collect();
    crate::simd::for_each_available(FastLanes::<N, L>(v))
}

/// The fast reduction, scalar and on the lanes of every backend the CPU runs, against `reduce_exact`, bit for bit, on
/// vectors that mix the kinds of `FCat` lane by lane; and the lanes' decisions are the scalar ones. TRIG_REPORT=1
/// prints the share of the lanes with k != 0 that the fast reduction decides, by kind.
#[test]
fn trig_fast_reduce_bitwise() {
    fn check<T: Ty, const N: usize, const L: usize>(n: usize) {
        let vs = fast_vectors::<T>(samples(n), 17);
        let counts = fast_counts::<T, N, L>(&vs);
        for (cat, c) in &counts {
            if report() {
                println!(
                    "{} {cat:?}: {} of {} lanes with k != 0 decided ({:.4}%)",
                    T::NAME,
                    c.decided,
                    c.k,
                    100.0 * c.decided as f64 / c.k.max(1) as f64
                );
            }
            assert_eq!(
                c.scalar_bad,
                0,
                "{} {cat:?}: scalar `reduce` differs from `reduce_exact`",
                T::NAME
            );
        }
        // the fast reduction decides almost every random argument, and leaves some of the deepest cancellations
        let share = |f: FCat| {
            let c = counts.iter().find(|e| e.0 == f).unwrap().1;
            c.decided as f64 / c.k as f64
        };
        assert!(
            share(FCat::Wide) > 0.999,
            "{} decides {} of Wide",
            T::NAME,
            share(FCat::Wide)
        );
        assert!(
            share(FCat::NearPi2) < 1.0 && share(FCat::Mid) < 1.0 && share(FCat::NearTie) < 1.0,
            "{} decides every near case",
            T::NAME
        );
        for (isa, rows) in fast_lanes::<T, N, L>(&vs) {
            for (cat, bad, decisions) in rows {
                assert_eq!(
                    (bad, decisions),
                    (0, 0),
                    "{} on {isa}, {cat:?}: lanes, decisions that differ",
                    T::NAME
                );
            }
        }
    }
    check::<DD, 2, 8>(400);
    check::<QD, 4, 12>(150);
    check::<OD, 8, 20>(60);
}

/// Controls (feature `mutate`): the fast reduction with its test skipped fails the bitwise check on the near ties and
/// near the multiples of pi/2, with eps = 0 at the depths where its bits run out, and with pi/2 two digits short on
/// the wide arguments, scalar and on the lanes of every backend
#[cfg(feature = "mutate")]
#[test]
fn trig_fast_reduce_controls() {
    fn bad<T: Ty, const N: usize, const L: usize>(id: u32, n: usize, cats: &[FCat]) -> Vec<String> {
        let vs = fast_vectors::<T>(n, 23);
        mutate::set(id);
        let counts = fast_counts::<T, N, L>(&vs);
        let lanes = fast_lanes::<T, N, L>(&vs);
        mutate::set(0);
        let mut missed = Vec::new();
        for &cat in cats {
            let s = counts.iter().find(|e| e.0 == cat).unwrap().1.scalar_bad;
            println!("'{}': {} {cat:?}: scalar {s}", mutate::NAMES[id as usize], T::NAME);
            if s == 0 {
                missed.push(format!(
                    "{} scalar {cat:?} under '{}'",
                    T::NAME,
                    mutate::NAMES[id as usize]
                ));
            }
            for (isa, rows) in &lanes {
                let b = rows.iter().find(|e| e.0 == cat).unwrap().1;
                println!("'{}': {} {cat:?}: {isa} {b}", mutate::NAMES[id as usize], T::NAME);
                if b == 0 {
                    missed.push(format!(
                        "{} {isa} {cat:?} under '{}'",
                        T::NAME,
                        mutate::NAMES[id as usize]
                    ));
                }
            }
        }
        missed
    }
    let mut missed = Vec::new();
    for (id, cats) in [
        (
            mutate::REDUCE_FAST_UNCHECKED,
            &[FCat::NearTie, FCat::NearPi2, FCat::Mid][..],
        ),
        (mutate::REDUCE_FAST_EPS, &[FCat::Mid][..]),
        (mutate::REDUCE_FAST_PI, &[FCat::Wide][..]),
    ] {
        missed.extend(bad::<DD, 2, 8>(id, 400, cats));
        missed.extend(bad::<QD, 4, 12>(id, 300, cats));
        missed.extend(bad::<OD, 8, 20>(id, 300, cats));
    }
    assert!(missed.is_empty(), "controls that did not fail: {missed:#?}");
}

#[test]
#[ignore]
fn trig_timing() {
    fn time<T: Ty, R>(xs: &[T], f: fn(T) -> R) -> f64 {
        let mut best = f64::INFINITY;
        for _ in 0..5 {
            let t = std::time::Instant::now();
            for &x in xs {
                std::hint::black_box(f(std::hint::black_box(x)));
            }
            best = best.min(t.elapsed().as_secs_f64() / xs.len() as f64);
        }
        best * 1e9
    }
    fn row<T: Ty>(what: &str, xs: &[T]) {
        println!(
            "{} {what:<24} sin {:>8.0} ns  cos {:>8.0} ns  tan {:>8.0} ns  sin_cos {:>8.0} ns",
            T::NAME,
            time(xs, |x| x.sin()),
            time(xs, |x| x.cos()),
            time(xs, |x| x.tan()),
            time(xs, |x| x.sin_cos())
        );
    }
    fn rows<T: Ty>(n: usize) {
        let mut r = Rng::new(9);
        let small: Vec<T> = (0..n).map(|_| greedy(&rand_r(&mut r, -2, -1))).collect();
        let mid: Vec<T> = (0..n).map(|_| greedy(&rand_r(&mut r, 0, 9))).collect();
        let big: Vec<T> = (0..n).map(|_| greedy(&rand_r(&mut r, 40, 51))).collect();
        row("|x| in [1/4, 1)", &small);
        row("|x| in [1, 1024)", &mid);
        row("|x| in [2^40, 2^52)", &big);
    }
    rows::<DD>(20000);
    rows::<QD>(4000);
    rows::<OD>(1000);
}

/// ns per value of the lane functions (`DV`, `QV`, `OV` on the compile-time backend) against the scalar ones, and of
/// the reduction: the scalar one, and the lanes' (each lane taken apart, reduced by `reduce` and packed) with its share
/// of the lanes' sin
#[test]
#[ignore]
fn trig_lanes_timing() {
    use crate::dv::DV;
    use crate::ov::OV;
    use crate::qv::QV;
    use crate::simd::Native;
    use crate::trig::Ext;
    use std::hint::black_box;
    /// the best of five runs over xs, ns per value with `per` values an item
    fn time<X: Copy, R>(xs: &[X], per: usize, f: impl Fn(X) -> R) -> f64 {
        let mut best = f64::INFINITY;
        for _ in 0..5 {
            let t = std::time::Instant::now();
            for &x in xs {
                black_box(f(black_box(x)));
            }
            best = best.min(t.elapsed().as_secs_f64() / (xs.len() * per) as f64);
        }
        best * 1e9
    }
    fn rows<T: Ty + Ext, V: Ext + Copy>(
        n: usize,
        lanes: impl Fn(&[T]) -> V,
        scalar: [fn(T) -> T; 4],
        vector: [fn(V) -> V; 4],
    ) {
        let mut r = Rng::new(9);
        for (what, lo, hi) in [("[1/4, 1)", -2, -1), ("[1, 1024)", 0, 9), ("[2^40, 2^52)", 40, 51)] {
            let xs: Vec<T> = (0..n).map(|_| greedy(&rand_r(&mut r, lo, hi))).collect();
            let vs: Vec<V> = xs.as_chunks::<8>().0.iter().map(|c| lanes(c)).collect();
            let mut cells = Vec::new();
            for k in 0..4 {
                let (s, v) = (time(&xs, 1, scalar[k]), time(&vs, 8, vector[k]));
                cells.push(format!("{s:.0} | {v:.0} | {:.2}", s / v));
            }
            let one = time(&xs, 1, |x: T| x.reduce());
            let red = time(&vs, 8, |v: V| v.reduce());
            let sin = time(&vs, 8, vector[0]);
            println!(
                "| {} | {what} | {} | {one:.1} | {red:.1} | {:.0}% |",
                T::NAME,
                cells.join(" | "),
                100.0 * red / sin
            );
        }
    }
    println!(
        "{} lanes: ns per value, scalar | lanes | ratio for sin, cos, tan, sin_cos; the reduction, ns per value, \
         scalar | lanes | the lanes' share of their sin",
        <Native as crate::simd::Simd>::NAME
    );
    println!("| type | \\|x\\| | sin | | | cos | | | tan | | | sin_cos | | | reduction | | share |");
    rows::<DD, DV<Native>>(
        16000,
        |x| {
            DV::load(
                &x.iter().map(|d| d.hi).collect::<Vec<_>>(),
                &x.iter().map(|d| d.lo).collect::<Vec<_>>(),
            )
        },
        [DD::sin, DD::cos, DD::tan, |x| DD::sin_cos(x).0],
        [DV::sin, DV::cos, DV::tan, |x| DV::sin_cos(x).0],
    );
    rows::<QD, QV<Native>>(
        4000,
        |x| QV::from_lanes(&std::array::from_fn(|i| x[i])),
        [QD::sin, QD::cos, QD::tan, |x| QD::sin_cos(x).0],
        [QV::sin, QV::cos, QV::tan, |x| QV::sin_cos(x).0],
    );
    rows::<OD, OV<Native>>(
        800,
        |x| OV::from_lanes(&std::array::from_fn(|i| x[i])),
        [OD::sin, OD::cos, OD::tan, |x| OD::sin_cos(x).0],
        [OV::sin, OV::cos, OV::tan, |x| OV::sin_cos(x).0],
    );
}
