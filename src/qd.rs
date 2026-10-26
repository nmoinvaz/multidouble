//! Scalar quad-double: an unevaluated sum x0 + x1 + x2 + x3 of four f64, renormalized so that the parts do not
//! overlap (|x_{i+1}| <= ulp(x_i)/2), about 64 significant digits (2^-209 relative, the QD library's epsilon).
//! The 8-lane `qv::QV` runs the same algorithms with bitwise the same results.
//!
//! The algorithms are those of the QD library (Y. Hida, X. S. Li, D. H. Bailey, "Algorithms for quad-double
//! precision floating point arithmetic", ARITH-15, 2001; QD 2.3, qd_inline.h): two-sum, the FMA two-product,
//! the renormalization with its zero-skipping branches, the "sloppy" add (Cray-style bound) and the accurate merge
//! add (IEEE-style bound), the sloppy and the accurate multiply (the latter adds the O(eps^4) partial products), the
//! sloppy and the accurate divide (four or five quotient terms), and the square root by Newton's iteration on
//! 1/sqrt(a). The O(eps^3) partial products that QD sums in plain arithmetic are summed here with FMA, in QD's order.
//! The operators use the library's default configuration: `+`, `-` the sloppy add, `*` the sloppy multiply, `/` the
//! sloppy divide; `ieee_add`, `accurate_mul` and `accurate_div` are the others.
//!
//! Two repairs of QD, both found by the tests: the accurate add keeps u + v where
//! QD keeps u alone (when all parts are read with three emitted), and sqrt scales its argument by an exact power of
//! four into [1, 4) (QD's iteration loses accuracy above about 2^860 and below about 2^-860).
//!
//! `QdAcc` is a sum-of-products accumulator (the scalar twin of `qv::QDotAcc`, see there for its error). Decimal
//! parsing and printing are exact (via `exact`): `parse` rounds the decimal value to four parts by greedy
//! round-to-nearest (error <= 2^-212 relative), `to_sci` prints the four-part sum correctly rounded.
//!
//! With the cargo feature `mutate`, `mutate::set(id)` breaks one algorithm on purpose in the current thread, for
//! the controls of the accuracy tests (`qd_tests`); without it the hooks are compile-time `false`.
use crate::dd::{quick_two_sum, two_prod, two_sum, DD};
use crate::exact::{BigU, DecRat, Dy};
use std::ops::{Add, Div, Mul, Neg, Sub};

/// Deliberate breakage for the controls (feature `mutate`; ids below, 0 = none).
pub mod mutate {
    /// renormalization: the last first-pass quick-two-sum (c0 + s) done in plain f64, its error dropped
    pub const RENORM_P1: u32 = 1;
    /// sloppy add: the error of a0 + b0 dropped
    pub const SLOPPY_ADD_T0: u32 = 2;
    /// accurate add: the merge takes the smaller part first
    pub const IEEE_ADD_ORDER: u32 = 3;
    /// sloppy mul: the error of a0 b0 dropped
    pub const SLOPPY_MUL_Q0: u32 = 4;
    /// sloppy mul: the error of a0 b2 (an O(eps^3) term) dropped
    pub const SLOPPY_MUL_Q3: u32 = 5;
    /// accurate mul: the error of a0 b1 dropped
    pub const ACCURATE_MUL_Q1: u32 = 6;
    /// qd x f64: the error of a1 b dropped
    pub const MUL_F_Q1: u32 = 7;
    /// qd x dd: the error of a0 b.lo dropped
    pub const MUL_DD_Q1: u32 = 8;
    /// qd + f64: the error of a0 + b dropped
    pub const ADD_F_E: u32 = 9;
    /// qd + dd: the error of a1 + b.lo dropped
    pub const ADD_DD_T1: u32 = 10;
    /// divide: the third remainder update skipped (q3 from a stale remainder)
    pub const DIV_R3: u32 = 11;
    /// sqrt: one Newton iteration instead of three
    pub const SQRT_ITER: u32 = 12;
    /// dot accumulator: the level-2 two-sum errors not carried to level 3
    pub const ACC_L3: u32 = 13;
    /// parse: the last component truncated (rounded toward zero) instead of rounded to nearest
    pub const PARSE_TRUNC: u32 = 14;
    /// 8-lane only: the renormalization's zero test ignored in the second-pass step for c2
    pub const QV_RENORM_MASK: u32 = 15;
    /// 8-lane only: the accurate add's merge reads the next part of a one position late
    pub const QV_IEEE_HEAD: u32 = 16;
    /// number of ids
    pub const N: u32 = 16;
    pub const NAMES: [&str; 17] = [
        "none",
        "renorm: last first-pass two-sum in plain f64",
        "sloppy add: error of a0 + b0 dropped",
        "accurate add: merge takes the smaller part first",
        "sloppy mul: error of a0 b0 dropped",
        "sloppy mul: error of a0 b2 dropped",
        "accurate mul: error of a0 b1 dropped",
        "qd x f64: error of a1 b dropped",
        "qd x dd: error of a0 b.lo dropped",
        "qd + f64: error of a0 + b dropped",
        "qd + dd: error of a1 + b.lo dropped",
        "divide: third remainder update skipped",
        "sqrt: one Newton iteration instead of three",
        "dot accumulator: level-2 errors dropped",
        "parse: last component truncated",
        "8-lane renorm: zero test ignored (step c2)",
        "8-lane accurate add: next part of a read one late",
    ];

    #[cfg(feature = "mutate")]
    thread_local!(static ID: std::cell::Cell<u32> = const { std::cell::Cell::new(0) });

    /// select the mutation for the current thread (0 = none)
    #[cfg(feature = "mutate")]
    pub fn set(id: u32) {
        ID.with(|m| m.set(id));
    }

    #[cfg(feature = "mutate")]
    #[inline(always)]
    pub fn on(id: u32) -> bool {
        ID.with(|m| m.get() == id)
    }

    #[cfg(not(feature = "mutate"))]
    #[inline(always)]
    pub fn on(_id: u32) -> bool {
        false
    }
}

/// (a + b + c) as (s, e1, e2), error-free (QD's three_sum)
#[inline(always)]
pub fn three_sum(a: f64, b: f64, c: f64) -> (f64, f64, f64) {
    let (t1, t2) = two_sum(a, b);
    let (a, t3) = two_sum(c, t1);
    let (b, c) = two_sum(t2, t3);
    (a, b, c)
}

/// (a + b + c) as (s, e), the last error rounded (QD's three_sum2)
#[inline(always)]
pub fn three_sum2(a: f64, b: f64, c: f64) -> (f64, f64) {
    let (t1, t2) = two_sum(a, b);
    let (a, t3) = two_sum(c, t1);
    (a, t2 + t3)
}

/// QD's renormalization of four parts (no-op if c0 is infinite)
#[inline(always)]
pub fn renorm4(c0: f64, c1: f64, c2: f64, c3: f64) -> [f64; 4] {
    if c0.is_infinite() {
        return [c0, c1, c2, c3];
    }
    let (s, c3) = quick_two_sum(c2, c3);
    let (s, c2) = quick_two_sum(c1, s);
    let (c0, c1) = if mutate::on(mutate::RENORM_P1) {
        (c0 + s, 0.0)
    } else {
        quick_two_sum(c0, s)
    };
    let (mut s0, mut s1, mut s2, mut s3) = (c0, c1, 0.0, 0.0);
    if s1 != 0.0 {
        (s1, s2) = quick_two_sum(s1, c2);
        if s2 != 0.0 {
            (s2, s3) = quick_two_sum(s2, c3);
        } else {
            (s1, s2) = quick_two_sum(s1, c3);
        }
    } else {
        (s0, s1) = quick_two_sum(s0, c2);
        if s1 != 0.0 {
            (s1, s2) = quick_two_sum(s1, c3);
        } else {
            (s0, s1) = quick_two_sum(s0, c3);
        }
    }
    [s0, s1, s2, s3]
}

/// QD's renormalization of five parts to four (no-op if c0 is infinite)
#[inline(always)]
pub fn renorm5(c0: f64, c1: f64, c2: f64, c3: f64, c4: f64) -> [f64; 4] {
    if c0.is_infinite() {
        return [c0, c1, c2, c3];
    }
    let (s, c4) = quick_two_sum(c3, c4);
    let (s, c3) = quick_two_sum(c2, s);
    let (s, c2) = quick_two_sum(c1, s);
    let (c0, c1) = if mutate::on(mutate::RENORM_P1) {
        (c0 + s, 0.0)
    } else {
        quick_two_sum(c0, s)
    };
    let (mut s0, mut s1, mut s2, mut s3) = (c0, c1, 0.0, 0.0);
    if s1 != 0.0 {
        (s1, s2) = quick_two_sum(s1, c2);
        if s2 != 0.0 {
            (s2, s3) = quick_two_sum(s2, c3);
            if s3 != 0.0 {
                s3 += c4;
            } else {
                (s2, s3) = quick_two_sum(s2, c4);
            }
        } else {
            (s1, s2) = quick_two_sum(s1, c3);
            if s2 != 0.0 {
                (s2, s3) = quick_two_sum(s2, c4);
            } else {
                (s1, s2) = quick_two_sum(s1, c4);
            }
        }
    } else {
        (s0, s1) = quick_two_sum(s0, c2);
        if s1 != 0.0 {
            (s1, s2) = quick_two_sum(s1, c3);
            if s2 != 0.0 {
                (s2, s3) = quick_two_sum(s2, c4);
            } else {
                (s1, s2) = quick_two_sum(s1, c4);
            }
        } else {
            (s0, s1) = quick_two_sum(s0, c3);
            if s1 != 0.0 {
                (s1, s2) = quick_two_sum(s1, c4);
            } else {
                (s0, s1) = quick_two_sum(s0, c4);
            }
        }
    }
    [s0, s1, s2, s3]
}

/// QD's quick_three_accum: adds c to the pair (a, b); returns the part that does not fit (0 if it all fits)
#[inline(always)]
fn quick_three_accum(a: &mut f64, b: &mut f64, c: f64) -> f64 {
    let (s, bb) = two_sum(*b, c);
    let (s, aa) = two_sum(*a, s);
    *a = aa;
    *b = bb;
    let za = aa != 0.0;
    let zb = bb != 0.0;
    if za && zb {
        return s;
    }
    if !zb {
        *b = *a;
        *a = s;
    } else {
        *a = s;
    }
    0.0
}

/// Quad-double `x[0] + x[1] + x[2] + x[3]`.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct QD {
    pub x: [f64; 4],
}

impl QD {
    pub const ZERO: QD = QD { x: [0.0; 4] };
    pub const ONE: QD = QD {
        x: [1.0, 0.0, 0.0, 0.0],
    };
    /// pi (greedy round-to-nearest parts)
    pub const PI: QD = QD {
        x: [
            f64::from_bits(0x400921fb54442d18),
            f64::from_bits(0x3ca1a62633145c07),
            f64::from_bits(0xb92f1976b7ed8fbc),
            f64::from_bits(0x35c4cf98e804177d),
        ],
    };
    /// 2 pi
    pub const TWO_PI: QD = QD {
        x: [
            f64::from_bits(0x401921fb54442d18),
            f64::from_bits(0x3cb1a62633145c07),
            f64::from_bits(0xb93f1976b7ed8fbc),
            f64::from_bits(0x35d4cf98e804177d),
        ],
    };
    /// QD's epsilon, 2^-209 (exactly; QD's decimal literal 1.21543267145725e-63 is its 15-digit rounding)
    pub const EPS: f64 = f64::from_bits(0x32e0_0000_0000_0000);

    /// renormalized from four parts
    #[inline(always)]
    pub fn new(x0: f64, x1: f64, x2: f64, x3: f64) -> QD {
        QD {
            x: renorm4(x0, x1, x2, x3),
        }
    }
    #[inline(always)]
    pub fn from_f64(x: f64) -> QD {
        QD { x: [x, 0.0, 0.0, 0.0] }
    }
    /// exact
    #[inline(always)]
    pub fn from_dd(d: DD) -> QD {
        QD {
            x: [d.hi, d.lo, 0.0, 0.0],
        }
    }
    /// nearest f64 (to within the rounding of the three lower parts' sum)
    #[inline(always)]
    pub fn to_f64(self) -> f64 {
        let t = self.x[1] + (self.x[2] + self.x[3]);
        // a zero tail leaves the leading part as it is, so a zero keeps its sign
        if t == 0.0 {
            self.x[0]
        } else {
            self.x[0] + t
        }
    }
    /// double-double, to about 2^-106 relative
    #[inline(always)]
    pub fn to_dd(self) -> DD {
        DD::new(self.x[0], self.x[1] + (self.x[2] + self.x[3]))
    }
    #[inline(always)]
    pub fn is_zero(self) -> bool {
        self.x[0] == 0.0
    }
    #[inline(always)]
    pub fn abs(self) -> QD {
        if self.x[0] < 0.0 {
            -self
        } else {
            self
        }
    }
    /// times a power of two b (`dd::is_pwr2`): every part scaled, exact barring overflow and underflow
    #[inline(always)]
    pub fn mul_pwr2(self, b: f64) -> QD {
        debug_assert!(crate::dd::is_pwr2(b), "mul_pwr2: {b} is not a power of two");
        QD {
            x: self.x.map(|v| v * b),
        }
    }

    // ---------------------------------------------------------------------------------------------------------
    // additions
    // ---------------------------------------------------------------------------------------------------------

    /// QD's sloppy add (the default `+`): Cray-style error bound
    #[inline(always)]
    pub fn sloppy_add(self, b: QD) -> QD {
        let (a, b) = (self.x, b.x);
        let (s0, t0) = two_sum(a[0], b[0]);
        let t0 = if mutate::on(mutate::SLOPPY_ADD_T0) { 0.0 } else { t0 };
        let (s1, t1) = two_sum(a[1], b[1]);
        let (s2, t2) = two_sum(a[2], b[2]);
        let (s3, t3) = two_sum(a[3], b[3]);
        let (s1, t0) = two_sum(s1, t0);
        let (s2, t0, t1) = three_sum(s2, t0, t1);
        let (s3, t0) = three_sum2(s3, t0, t2);
        let t0 = t0 + t1 + t3;
        QD {
            x: renorm5(s0, s1, s2, s3, t0),
        }
    }

    /// QD's accurate add (merge by magnitude, double-length accumulator), IEEE-style error bound, with one change:
    /// when every part has been read with three already emitted, the last part is u + v where QD keeps u alone
    /// (QD's version reached 16.8 u relative error in 2 of 20000 near-cancelling sums, this
    /// one 0.12 u in 200000)
    #[inline]
    // the merge keeps QD's branch order, in which the first and last branches take the same part
    #[allow(clippy::if_same_then_else)]
    pub fn ieee_add(self, b: QD) -> QD {
        let (a, b) = (self.x, b.x);
        let gt = |x: f64, y: f64| {
            if mutate::on(mutate::IEEE_ADD_ORDER) {
                x.abs() < y.abs()
            } else {
                x.abs() > y.abs()
            }
        };
        let (mut i, mut j, mut k) = (0usize, 0usize, 0usize);
        let mut x = [0.0f64; 4];
        let mut u;
        let mut v;
        if gt(a[i], b[j]) {
            u = a[i];
            i += 1;
        } else {
            u = b[j];
            j += 1;
        }
        if gt(a[i], b[j]) {
            v = a[i];
            i += 1;
        } else {
            v = b[j];
            j += 1;
        }
        (u, v) = quick_two_sum(u, v);
        while k < 4 {
            if i >= 4 && j >= 4 {
                if k < 3 {
                    x[k] = u;
                    k += 1;
                    x[k] = v;
                } else {
                    // QD stores u alone here and drops v. After cancellation the parts emitted so far can overlap,
                    // so they hold fewer than 212 bits and v can lie well above the last bit of the result (QD:
                    // up to 86 u; u + v rounded to one double still left up to 11 u, the first repair here). So v
                    // is kept as a fifth term and the five are renormalized; all parts are read, nothing is left.
                    return QD {
                        x: renorm5(x[0], x[1], x[2], u, v),
                    };
                }
                break;
            }
            let t;
            if i >= 4 {
                t = b[j];
                j += 1;
            } else if j >= 4 {
                t = a[i];
                i += 1;
            } else if gt(a[i], b[j]) {
                t = a[i];
                i += 1;
            } else {
                t = b[j];
                j += 1;
            }
            let s = quick_three_accum(&mut u, &mut v, t);
            if s != 0.0 {
                x[k] = s;
                k += 1;
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

    #[inline(always)]
    pub fn ieee_sub(self, b: QD) -> QD {
        self.ieee_add(-b)
    }

    /// qd + f64
    #[inline(always)]
    pub fn add_f(self, b: f64) -> QD {
        let a = self.x;
        let (c0, e) = two_sum(a[0], b);
        let e = if mutate::on(mutate::ADD_F_E) { 0.0 } else { e };
        let (c1, e) = two_sum(a[1], e);
        let (c2, e) = two_sum(a[2], e);
        let (c3, e) = two_sum(a[3], e);
        QD {
            x: renorm5(c0, c1, c2, c3, e),
        }
    }

    /// qd + dd
    #[inline]
    pub fn add_dd(self, b: DD) -> QD {
        let a = self.x;
        let (s0, t0) = two_sum(a[0], b.hi);
        let (s1, t1) = two_sum(a[1], b.lo);
        let t1 = if mutate::on(mutate::ADD_DD_T1) { 0.0 } else { t1 };
        let (s1, t0) = two_sum(s1, t0);
        let (s2, t0, t1) = three_sum(a[2], t0, t1);
        let (s3, t0) = two_sum(t0, a[3]);
        let t0 = t0 + t1;
        QD {
            x: renorm5(s0, s1, s2, s3, t0),
        }
    }

    // ---------------------------------------------------------------------------------------------------------
    // multiplications
    // ---------------------------------------------------------------------------------------------------------

    /// qd x f64
    #[inline(always)]
    pub fn mul_f(self, b: f64) -> QD {
        let a = self.x;
        let (p0, q0) = two_prod(a[0], b);
        let (p1, q1) = two_prod(a[1], b);
        let q1 = if mutate::on(mutate::MUL_F_Q1) { 0.0 } else { q1 };
        let (p2, q2) = two_prod(a[2], b);
        let p3 = a[3] * b;
        let s0 = p0;
        let (s1, s2) = two_sum(q0, p1);
        let (s2, q1, p2) = three_sum(s2, q1, p2);
        let (q1, q2) = three_sum2(q1, q2, p3);
        let s3 = q1;
        let s4 = q2 + p2;
        QD {
            x: renorm5(s0, s1, s2, s3, s4),
        }
    }

    /// qd x dd
    #[inline]
    pub fn mul_dd(self, b: DD) -> QD {
        let a = self.x;
        let (p0, q0) = two_prod(a[0], b.hi);
        let (p1, q1) = two_prod(a[0], b.lo);
        let q1 = if mutate::on(mutate::MUL_DD_Q1) { 0.0 } else { q1 };
        let (p2, q2) = two_prod(a[1], b.hi);
        let (p3, q3) = two_prod(a[1], b.lo);
        let (p4, q4) = two_prod(a[2], b.hi);
        let (p1, p2, q0) = three_sum(p1, p2, q0);
        // five-three sum
        let (p2, p3, p4) = three_sum(p2, p3, p4);
        let (q1, q2) = two_sum(q1, q2);
        let (s0, t0) = two_sum(p2, q1);
        let (s1, t1) = two_sum(p3, q2);
        let (s1, t0) = two_sum(s1, t0);
        let s2 = t0 + t1 + p4;
        let p2 = s0;
        let p3 = a[3].mul_add(b.hi, a[2] * b.lo) + q3 + q4;
        let (p3, q0) = three_sum2(p3, q0, s1);
        let p4 = q0 + s2;
        QD {
            x: renorm5(p0, p1, p2, p3, p4),
        }
    }

    /// QD's sloppy multiply (the default `*`): partial products to O(eps^3)
    #[inline(always)]
    pub fn sloppy_mul(self, b: QD) -> QD {
        let (a, b) = (self.x, b.x);
        let (p0, q0) = two_prod(a[0], b[0]);
        let q0 = if mutate::on(mutate::SLOPPY_MUL_Q0) { 0.0 } else { q0 };
        let (p1, q1) = two_prod(a[0], b[1]);
        let (p2, q2) = two_prod(a[1], b[0]);
        let (p3, q3) = two_prod(a[0], b[2]);
        let q3 = if mutate::on(mutate::SLOPPY_MUL_Q3) { 0.0 } else { q3 };
        let (p4, q4) = two_prod(a[1], b[1]);
        let (p5, q5) = two_prod(a[2], b[0]);
        let (p1, p2, q0) = three_sum(p1, p2, q0);
        // six-three sum of p2, q1, q2, p3, p4, p5
        let (p2, q1, q2) = three_sum(p2, q1, q2);
        let (p3, p4, p5) = three_sum(p3, p4, p5);
        let (s0, t0) = two_sum(p2, p3);
        let (s1, t1) = two_sum(q1, p4);
        let s2 = q2 + p5;
        let (s1, t0) = two_sum(s1, t0);
        let s2 = s2 + (t0 + t1);
        // O(eps^3) terms
        let r = eps3(a, b) + q0 + q3 + q4 + q5;
        let s1 = s1 + r;
        QD {
            x: renorm5(p0, p1, s0, s1, s2),
        }
    }

    /// QD's accurate multiply: partial products to O(eps^4)
    #[inline]
    pub fn accurate_mul(self, b: QD) -> QD {
        let (a, b) = (self.x, b.x);
        let (p0, q0) = two_prod(a[0], b[0]);
        let (p1, q1) = two_prod(a[0], b[1]);
        let q1 = if mutate::on(mutate::ACCURATE_MUL_Q1) { 0.0 } else { q1 };
        let (p2, q2) = two_prod(a[1], b[0]);
        let (p3, q3) = two_prod(a[0], b[2]);
        let (p4, q4) = two_prod(a[1], b[1]);
        let (p5, q5) = two_prod(a[2], b[0]);
        let (p1, p2, q0) = three_sum(p1, p2, q0);
        let (p2, q1, q2) = three_sum(p2, q1, q2);
        let (p3, p4, p5) = three_sum(p3, p4, p5);
        let (s0, t0) = two_sum(p2, p3);
        let (s1, t1) = two_sum(q1, p4);
        let s2 = q2 + p5;
        let (s1, t0) = two_sum(s1, t0);
        let s2 = s2 + (t0 + t1);
        // O(eps^3) terms
        let (p6, q6) = two_prod(a[0], b[3]);
        let (p7, q7) = two_prod(a[1], b[2]);
        let (p8, q8) = two_prod(a[2], b[1]);
        let (p9, q9) = two_prod(a[3], b[0]);
        // nine-two sum of q0, s1, q3, q4, q5, p6, p7, p8, p9
        let (q0, q3) = two_sum(q0, q3);
        let (q4, q5) = two_sum(q4, q5);
        let (p6, p7) = two_sum(p6, p7);
        let (p8, p9) = two_sum(p8, p9);
        let (t0, t1) = two_sum(q0, q4);
        let t1 = t1 + (q3 + q5);
        let (r0, r1) = two_sum(p6, p8);
        let r1 = r1 + (p7 + p9);
        let (q3, q4) = two_sum(t0, r0);
        let q4 = q4 + (t1 + r1);
        let (t0, t1) = two_sum(q3, s1);
        let t1 = t1 + q4;
        // O(eps^4) terms
        let r = eps4(a, b) + q6 + q7 + q8 + q9 + s2;
        let t1 = t1 + r;
        QD {
            x: renorm5(p0, p1, s0, t0, t1),
        }
    }

    /// QD's square
    #[inline]
    pub fn sqr(self) -> QD {
        let a = self.x;
        let (p0, q0) = two_prod(a[0], a[0]);
        let (p1, q1) = two_prod(2.0 * a[0], a[1]);
        let (p2, q2) = two_prod(2.0 * a[0], a[2]);
        let (p3, q3) = two_prod(a[1], a[1]);
        let (p1, q0) = two_sum(q0, p1);
        let (q0, q1) = two_sum(q0, q1);
        let (p2, p3) = two_sum(p2, p3);
        let (s0, t0) = two_sum(q0, p2);
        let (s1, t1) = two_sum(q1, p3);
        let (s1, t0) = two_sum(s1, t0);
        let t0 = t0 + t1;
        let (s1, t0) = quick_two_sum(s1, t0);
        let (p2, t1) = quick_two_sum(s0, s1);
        let (p3, q0) = quick_two_sum(t1, t0);
        let p4 = 2.0 * a[0] * a[3];
        let p5 = 2.0 * a[1] * a[2];
        let (p4, p5) = two_sum(p4, p5);
        let (q2, q3) = two_sum(q2, q3);
        let (t0, t1) = two_sum(p4, q2);
        let t1 = t1 + p5 + q3;
        let (p3, p4) = two_sum(p3, t0);
        let p4 = p4 + q0 + t1;
        QD {
            x: renorm5(p0, p1, p2, p3, p4),
        }
    }

    // ---------------------------------------------------------------------------------------------------------
    // division, square root, powers
    // ---------------------------------------------------------------------------------------------------------

    /// QD's sloppy divide (the default `/`): four quotient terms
    #[inline]
    pub fn sloppy_div(self, b: QD) -> QD {
        let q0 = self.x[0] / b.x[0];
        let r = self - b.mul_f(q0);
        let q1 = r.x[0] / b.x[0];
        let r = r - b.mul_f(q1);
        let q2 = r.x[0] / b.x[0];
        let r = if mutate::on(mutate::DIV_R3) { r } else { r - b.mul_f(q2) };
        let q3 = r.x[0] / b.x[0];
        QD {
            x: renorm4(q0, q1, q2, q3),
        }
    }

    /// QD's accurate divide: five quotient terms
    #[inline]
    pub fn accurate_div(self, b: QD) -> QD {
        let q0 = self.x[0] / b.x[0];
        let r = self - b.mul_f(q0);
        let q1 = r.x[0] / b.x[0];
        let r = r - b.mul_f(q1);
        let q2 = r.x[0] / b.x[0];
        let r = if mutate::on(mutate::DIV_R3) { r } else { r - b.mul_f(q2) };
        let q3 = r.x[0] / b.x[0];
        let r = r - b.mul_f(q3);
        let q4 = r.x[0] / b.x[0];
        QD {
            x: renorm5(q0, q1, q2, q3, q4),
        }
    }

    #[inline(always)]
    pub fn recip(self) -> QD {
        QD::ONE / self
    }

    /// Square root: QD's Newton iteration on 1/sqrt(a) (three steps from the f64 value, then times a), applied to a
    /// scaled by an exact power of four into [1, 4) and the result scaled back. Unscaled, as in QD, the iteration
    /// loses accuracy above about 2^860 (1/a's lower parts underflow) and below about 2^-860 (a/2 drops bits of
    /// subnormal parts); the near-overflow tests found it.
    #[inline]
    pub fn sqrt(self) -> QD {
        if self.is_zero() {
            return QD::ZERO;
        }
        // s = 2^k with 4^k <= a0 < 4^(k+1); 1/s is exact, and a/s^2 is formed in two exact steps
        let s = f64::from_bits(self.x[0].sqrt().to_bits() & 0x7ff0_0000_0000_0000);
        let inv = 1.0 / s;
        let a = self.mul_pwr2(inv).mul_pwr2(inv);
        let mut r = QD::from_f64(1.0 / a.x[0].sqrt());
        let h = a.mul_pwr2(0.5);
        let n = if mutate::on(mutate::SQRT_ITER) { 1 } else { 3 };
        for _ in 0..n {
            r = r + (-(h * r.sqr())).add_f(0.5) * r;
        }
        (r * a).mul_pwr2(s)
    }

    /// integer power (QD's npwr: binary powering by sqr and the sloppy multiply; 1/a^|n| for n < 0)
    pub fn powi(self, n: i32) -> QD {
        if n == 0 {
            return QD::ONE;
        }
        let mut r = self;
        let mut s = QD::ONE;
        let mut nn = n.unsigned_abs();
        if nn > 1 {
            while nn > 0 {
                if nn % 2 == 1 {
                    s = s * r;
                }
                nn /= 2;
                if nn > 0 {
                    r = r.sqr();
                }
            }
        } else {
            s = r;
        }
        if n < 0 {
            QD::ONE / s
        } else {
            s
        }
    }

    // ---------------------------------------------------------------------------------------------------------
    // exact value, decimal input and output
    // ---------------------------------------------------------------------------------------------------------

    /// the exact value of the four-part sum (finite parts)
    pub fn exact(self) -> Dy {
        Dy::sum(&self.x)
    }

    /// Parse a decimal ("-1.234e-5", "3.14159...", "42"): the exact decimal value rounded to four parts by greedy
    /// round-to-nearest (x0 = RN(v), x1 = RN(v - x0), ...), so |error| <= ulp(x3)/2 <= 2^-212 |v|.
    pub fn parse(s: &str) -> Result<QD, String> {
        let t = s.trim();
        let (neg, body) = match t.as_bytes().first() {
            Some(b'-') => (true, &t[1..]),
            Some(b'+') => (false, &t[1..]),
            _ => (false, t),
        };
        let (mant, exp) = match body.find(['e', 'E']) {
            Some(p) => (
                &body[..p],
                body[p + 1..]
                    .parse::<i64>()
                    .map_err(|e| format!("{s}: exponent: {e}"))?,
            ),
            None => (body, 0),
        };
        let (ip, fp) = match mant.find('.') {
            Some(p) => (&mant[..p], &mant[p + 1..]),
            None => (mant, ""),
        };
        if ip.is_empty() && fp.is_empty() || !ip.bytes().chain(fp.bytes()).all(|c| c.is_ascii_digit()) {
            return Err(format!("{s}: not a decimal number"));
        }
        let digits = format!("{ip}{fp}");
        let digits = digits.trim_start_matches('0');
        let n = BigU::from_dec(if digits.is_empty() { "0" } else { digits });
        let e10 = exp - fp.len() as i64;
        let mut r = if e10 >= 0 {
            DecRat {
                neg,
                n: n.mul(&BigU::pow_small(10, e10 as u64)),
                k: 0,
                t: 0,
            }
        } else {
            DecRat {
                neg,
                n,
                k: (-e10) as u64,
                t: 0,
            }
        };
        let mut x = [0.0f64; 4];
        for i in 0..4 {
            let mut c = r.round();
            if i == 3 && mutate::on(mutate::PARSE_TRUNC) && c != 0.0 && r.sub_f64(c).neg != r.neg {
                // rounded away from zero: step one ulp back toward zero
                c = f64::from_bits(c.to_bits() - 1);
            }
            if !c.is_finite() {
                return Ok(QD { x: [c, 0.0, 0.0, 0.0] });
            }
            x[i] = c;
            if c == 0.0 {
                break;
            }
            r = r.sub_f64(c);
        }
        if neg && x[0] == 0.0 {
            x[0] = -0.0;
        }
        Ok(QD { x })
    }

    /// Scientific notation with `digits` significant digits, correctly rounded (half to even) from the exact value
    /// of the four-part sum: "-1.2345e-05" style, at least two exponent digits.
    pub fn to_sci(self, digits: usize) -> String {
        let digits = digits.max(1);
        if !self.x.iter().all(|v| v.is_finite()) {
            return format!("{}", self.x[0] + self.x[1] + self.x[2] + self.x[3]);
        }
        let v = self.exact();
        let sign = if v.neg || (v.is_zero() && self.x[0].is_sign_negative()) {
            "-"
        } else {
            ""
        };
        if v.is_zero() {
            return format!(
                "{sign}{}e+00",
                if digits > 1 {
                    format!("0.{}", "0".repeat(digits - 1))
                } else {
                    "0".into()
                }
            );
        }
        let (_, n, e10) = v.to_decimal();
        let d = n.to_dec();
        // value = 0.d × 10^(len + e10) = d[0].d[1..] × 10^(len - 1 + e10)
        let mut exp10 = d.len() as i64 - 1 + e10;
        let mut out: Vec<u8> = d.bytes().take(digits).collect();
        while out.len() < digits {
            out.push(b'0');
        }
        if d.len() > digits {
            let next = d.as_bytes()[digits];
            let rest = d.as_bytes()[digits + 1..].iter().any(|&c| c != b'0');
            let odd = (out[digits - 1] - b'0') % 2 == 1;
            if next > b'5' || (next == b'5' && (rest || odd)) {
                // round up with carry
                let mut i = digits;
                loop {
                    if i == 0 {
                        out.insert(0, b'1');
                        out.pop();
                        exp10 += 1;
                        break;
                    }
                    i -= 1;
                    if out[i] == b'9' {
                        out[i] = b'0';
                    } else {
                        out[i] += 1;
                        break;
                    }
                }
            }
        }
        let m = String::from_utf8(out).unwrap();
        let mant = if digits > 1 {
            format!("{}.{}", &m[..1], &m[1..])
        } else {
            m
        };
        format!("{sign}{mant}e{}{:02}", if exp10 < 0 { '-' } else { '+' }, exp10.abs())
    }
}

#[cfg(feature = "f128")]
impl QD {
    /// greedy round-to-nearest parts (x0 = RN(x), x1 = RN(x - x0), ...), exact when RN(x) is finite and the last bit
    /// of x is at least 2^-1074: the 113 bits fill at most three parts, and each remainder is exact in f128
    pub fn from_f128(x: f128) -> QD {
        let mut q = QD::ZERO;
        let mut r = x;
        for xi in q.x.iter_mut() {
            *xi = r as f64;
            if !xi.is_finite() {
                break;
            }
            r -= *xi as f128;
        }
        q
    }
    /// correctly rounded, for any four parts: their exact sum in a fixed-point accumulator, rounded once
    pub fn to_f128(self) -> f128 {
        sum_to_f128(self.x)
    }
}

/// Limbs of the fixed-point accumulator, in two's complement: bit p weighs 2^(p - 1074), from the least f64 bit to
/// beyond 2^1026, which bounds a sum of four f64.
#[cfg(feature = "f128")]
const ACC_LIMBS: usize = 33;

/// the exact sum of four f64, rounded to the nearest f128 (ties to even)
#[cfg(feature = "f128")]
fn sum_to_f128(x: [f64; 4]) -> f128 {
    // infinities and NaN as IEEE addition gives them
    if x.iter().any(|v| !v.is_finite()) {
        return x[0] as f128 + x[1] as f128 + x[2] as f128 + x[3] as f128;
    }
    let mut acc = [0u64; ACC_LIMBS];
    for v in x {
        let b = v.to_bits();
        let ex = (b >> 52 & 0x7ff) as usize;
        let m = (b & ((1 << 52) - 1)) | ((ex > 0) as u64) << 52;
        // v = ±m·2^(p - 1074)
        let p = ex.max(1) - 1;
        acc_add(&mut acc, p / 64, (m as u128) << (p % 64), b >> 63 == 1);
    }
    let neg = acc[ACC_LIMBS - 1] >> 63 == 1;
    if neg {
        let mut c = 1;
        for a in acc.iter_mut() {
            let (s, o) = (!*a).overflowing_add(c);
            *a = s;
            c = o as u64;
        }
    }
    let Some(t) = acc.iter().rposition(|&a| a != 0) else {
        // an exact zero is -0 only when every part is -0, as in IEEE addition
        return if x.iter().all(|v| v.is_sign_negative()) {
            -0.0
        } else {
            0.0
        };
    };
    // leading bit l, the 113-bit significand from bit l - 112
    let mut l = 64 * t + 63 - acc[t].leading_zeros() as usize;
    let m = if l < 113 {
        acc_bits(&acc, 0) << (112 - l)
    } else {
        let lo = l - 112;
        let m = acc_bits(&acc, lo);
        let half = acc[(lo - 1) / 64] >> ((lo - 1) % 64) & 1 == 1;
        let up = half && (acc_any_below(&acc, lo - 1) || m & 1 == 1);
        let m = m + up as u128;
        if m >> 113 == 1 {
            l += 1;
            m >> 1
        } else {
            m
        }
    };
    // m·2^(l - 112 - 1074) with m in [2^112, 2^113): always a normal f128
    let biased = (l + 16383 - 1074) as u128;
    f128::from_bits((neg as u128) << 127 | biased << 112 | (m & ((1 << 112) - 1)))
}

/// acc += w·2^(64k), or acc -= w·2^(64k) when neg, carrying or borrowing up to the top limb
#[cfg(feature = "f128")]
fn acc_add(acc: &mut [u64; ACC_LIMBS], k: usize, w: u128, neg: bool) {
    let mut c = 0;
    for j in k..ACC_LIMBS {
        let d = if j < k + 2 { (w >> (64 * (j - k))) as u64 } else { 0 };
        let (s, o1) = if neg {
            acc[j].overflowing_sub(d)
        } else {
            acc[j].overflowing_add(d)
        };
        let (s, o2) = if neg {
            s.overflowing_sub(c)
        } else {
            s.overflowing_add(c)
        };
        acc[j] = s;
        c = (o1 || o2) as u64;
        if j > k && c == 0 {
            break;
        }
    }
}

/// the 128 bits of acc from bit lo up
#[cfg(feature = "f128")]
fn acc_bits(acc: &[u64; ACC_LIMBS], lo: usize) -> u128 {
    let limb = |i: usize| acc.get(i).copied().unwrap_or(0) as u128;
    let (i, s) = (lo / 64, lo % 64);
    let w = limb(i) | limb(i + 1) << 64;
    if s == 0 {
        w
    } else {
        w >> s | limb(i + 2) << (128 - s)
    }
}

/// any bit of acc below bit n
#[cfg(feature = "f128")]
fn acc_any_below(acc: &[u64; ACC_LIMBS], n: usize) -> bool {
    let (i, s) = (n / 64, n % 64);
    acc[..i].iter().any(|&a| a != 0) || (s > 0 && acc[i] & ((1 << s) - 1) != 0)
}

/// a0 b3 + a1 b2 + a2 b1 + a3 b0 (the O(eps^3) partial products), by FMA in QD's order
#[inline(always)]
fn eps3(a: [f64; 4], b: [f64; 4]) -> f64 {
    a[3].mul_add(b[0], a[2].mul_add(b[1], a[1].mul_add(b[2], a[0] * b[3])))
}

/// a1 b3 + a2 b2 + a3 b1 (the O(eps^4) partial products), by FMA in QD's order
#[inline(always)]
fn eps4(a: [f64; 4], b: [f64; 4]) -> f64 {
    a[3].mul_add(b[1], a[2].mul_add(b[2], a[1] * b[3]))
}

impl std::fmt::Display for QD {
    /// 66 significant digits (the four parts carry about 64)
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_sci(f.precision().map(|p| p + 1).unwrap_or(66)))
    }
}

impl std::str::FromStr for QD {
    type Err = String;
    fn from_str(s: &str) -> Result<QD, String> {
        QD::parse(s)
    }
}

impl Neg for QD {
    type Output = QD;
    #[inline(always)]
    /// every part negated, the lower three as -x + 0, so that a zero lower part is +0 (as DD's lo)
    fn neg(self) -> QD {
        let x = self.x;
        QD {
            x: [-x[0], -x[1] + 0.0, -x[2] + 0.0, -x[3] + 0.0],
        }
    }
}

impl Add for QD {
    type Output = QD;
    #[inline(always)]
    fn add(self, b: QD) -> QD {
        self.sloppy_add(b)
    }
}

impl Sub for QD {
    type Output = QD;
    #[inline(always)]
    fn sub(self, b: QD) -> QD {
        self.sloppy_add(-b)
    }
}

impl Mul for QD {
    type Output = QD;
    #[inline(always)]
    fn mul(self, b: QD) -> QD {
        self.sloppy_mul(b)
    }
}

impl Div for QD {
    type Output = QD;
    #[inline(always)]
    fn div(self, b: QD) -> QD {
        self.sloppy_div(b)
    }
}

/// Scalar sum-of-products accumulator, the twin of `qv::QDotAcc` (same algorithm, bitwise the same per lane).
#[derive(Clone, Copy, Debug, Default)]
pub struct QdAcc {
    pub s: [f64; 5],
}

impl QdAcc {
    pub fn zero() -> QdAcc {
        QdAcc::default()
    }
    /// self + a b
    #[inline(always)]
    pub fn add_prod(self, a: QD, b: QD) -> QdAcc {
        let (a, b) = (a.x, b.x);
        let (p00, e00) = two_prod(a[0], b[0]);
        let (p01, e01) = two_prod(a[0], b[1]);
        let (p10, e10) = two_prod(a[1], b[0]);
        let (p02, e02) = two_prod(a[0], b[2]);
        let (p11, e11) = two_prod(a[1], b[1]);
        let (p20, e20) = two_prod(a[2], b[0]);
        let r3 = eps3(a, b);
        // level 0
        let (s0, t0) = two_sum(self.s[0], p00);
        // level 1: t0, e00, p01, p10
        let (x1, y1) = two_sum(p01, p10);
        let (x2, y2) = two_sum(e00, t0);
        let (x3, y3) = two_sum(x1, x2);
        let (s1, y4) = two_sum(self.s[1], x3);
        // level 2: y1..y4, e01, e10, p02, p11, p20
        let (z1, w1) = two_sum(p02, p20);
        let (z2, w2) = two_sum(p11, e01);
        let (z3, w3) = two_sum(e10, y1);
        let (z4, w4) = two_sum(y2, y3);
        let (z5, w5) = two_sum(z1, z2);
        let (z6, w6) = two_sum(z3, z4);
        let (z7, w7) = two_sum(z5, z6);
        let (z8, w8) = two_sum(z7, y4);
        let (s2, w9) = two_sum(self.s[2], z8);
        // level 3: w9, the error of the running level-2 sum, is as large as that sum's ulp and goes in by itself;
        // the per-term errors and O(eps^3) products are summed first
        let (w, w9) = if mutate::on(mutate::ACC_L3) {
            (0.0, 0.0)
        } else {
            (((w1 + w2) + (w3 + w4)) + ((w5 + w6) + (w7 + w8)), w9)
        };
        let r = ((w + r3) + (e02 + e11)) + e20;
        let (s3, x9) = two_sum(self.s[3], w9);
        let (s3, x10) = two_sum(s3, r);
        // level 4
        QdAcc {
            s: [s0, s1, s2, s3, self.s[4] + (x9 + x10)],
        }
    }
    /// self + a
    #[inline(always)]
    pub fn add(self, a: QD) -> QdAcc {
        let a = a.x;
        let (s0, t0) = two_sum(self.s[0], a[0]);
        let (x1, y1) = two_sum(a[1], t0);
        let (s1, y2) = two_sum(self.s[1], x1);
        let (z1, w1) = two_sum(a[2], y1);
        let (z2, w2) = two_sum(z1, y2);
        let (s2, w3) = two_sum(self.s[2], z2);
        let r = (w1 + w2) + a[3];
        let (s3, x3) = two_sum(self.s[3], w3);
        let (s3, x4) = two_sum(s3, r);
        QdAcc {
            s: [s0, s1, s2, s3, self.s[4] + (x3 + x4)],
        }
    }
    /// the sum as a quad-double: the five levels added in turn with qd + f64
    #[inline(always)]
    pub fn finish(self) -> QD {
        QD::from_f64(self.s[0])
            .add_f(self.s[1])
            .add_f(self.s[2])
            .add_f(self.s[3])
            .add_f(self.s[4])
    }
}
