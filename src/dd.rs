//! Scalar double-double (hi + lo, |lo| <= ulp(hi)/2, ~32 significant digits). Used for constants and set-up; the
//! hot loops use the 8-lane `dv::DV` with the same algorithms.
use std::ops::{Add, Div, Mul, Neg, Sub};

#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct DD {
    pub hi: f64,
    pub lo: f64,
}

#[inline(always)]
pub fn two_sum(a: f64, b: f64) -> (f64, f64) {
    let s = a + b;
    let bb = s - a;
    (s, (a - (s - bb)) + (b - bb))
}

#[inline(always)]
pub fn quick_two_sum(a: f64, b: f64) -> (f64, f64) {
    let s = a + b;
    (s, b - (s - a))
}

#[inline(always)]
pub fn two_prod(a: f64, b: f64) -> (f64, f64) {
    let p = a * b;
    (p, a.mul_add(b, -p))
}

/// The power of two nearest to x in the logarithm (within a factor of sqrt 2; x > 0, finite, and inside the range
/// whose nearest power of two is a normal f64, about 2^-1022 to 2^1023, which debug builds check): the scale for
/// computing in a variable rescaled by a power of two (`DD::mul_pwr2`, `crate::dual::Lane::mul_pwr2`), e.g. a
/// power series in x / pow2_near(x0), whose coefficients then stay near the scale of the evaluation radius instead
/// of growing like r^-k. The scaling is exact, so the values agree bit for bit with the unscaled recursion wherever
/// that neither overflows nor underflows.
pub fn pow2_near(x: f64) -> f64 {
    debug_assert!(
        x > 0.0 && x.is_finite(),
        "pow2_near: {x} is not a positive finite number"
    );
    let p = 2f64.powi(x.log2().round() as i32);
    debug_assert!(
        is_pwr2(p),
        "pow2_near: {x} rounds to a power of two outside the normal range ({p})"
    );
    p
}

/// b is a normal power of two (positive or negative): the scales `mul_pwr2` accepts
#[inline(always)]
pub fn is_pwr2(b: f64) -> bool {
    let e = (b.to_bits() >> 52) & 0x7ff;
    b.to_bits() & 0x000f_ffff_ffff_ffff == 0 && e != 0 && e != 0x7ff
}

/// the hi and lo parts of double-doubles as two arrays, the inverse of `join`
pub fn split(v: &[DD]) -> (Vec<f64>, Vec<f64>) {
    (v.iter().map(|d| d.hi).collect(), v.iter().map(|d| d.lo).collect())
}

/// double-doubles from the arrays of their hi and lo parts, the parts as they are (`DD { hi, lo }`, not
/// renormalized). Arrays of different lengths panic.
pub fn join(hi: &[f64], lo: &[f64]) -> Vec<DD> {
    assert_eq!(
        hi.len(),
        lo.len(),
        "join: {} hi parts and {} lo parts",
        hi.len(),
        lo.len()
    );
    hi.iter().zip(lo).map(|(&hi, &lo)| DD { hi, lo }).collect()
}

impl DD {
    pub const ZERO: DD = DD { hi: 0.0, lo: 0.0 };
    pub const ONE: DD = DD { hi: 1.0, lo: 0.0 };
    /// 2 pi
    pub const TWO_PI: DD = DD {
        hi: std::f64::consts::TAU,
        lo: 2.4492935982947064e-16,
    };

    #[inline(always)]
    pub fn new(hi: f64, lo: f64) -> DD {
        let (h, l) = quick_two_sum(hi, lo);
        DD { hi: h, lo: l }
    }
    #[inline(always)]
    pub fn from_f64(x: f64) -> DD {
        DD { hi: x, lo: 0.0 }
    }
    /// hi + lo; a zero lo leaves hi as it is, so a zero keeps its sign (-0 + +0 would round to +0)
    #[inline(always)]
    pub fn to_f64(self) -> f64 {
        if self.lo == 0.0 {
            self.hi
        } else {
            self.hi + self.lo
        }
    }
    #[inline(always)]
    pub fn abs(self) -> DD {
        if self.hi < 0.0 {
            -self
        } else {
            self
        }
    }
    #[inline(always)]
    pub fn recip(self) -> DD {
        DD::ONE / self
    }
    /// self / b with two divisions where `/` has three: DWDivDW2, Algorithm 17 of J. Joldes, J.-M. Muller,
    /// V. Popescu, "Tight and rigorous error bounds for basic building blocks of double-word arithmetic", ACM Trans.
    /// Math. Softw. 44(2), 2017, doi:10.1145/3121432, with their Algorithm 7 for (b.hi + b.lo) th. Its relative error
    /// is at most 15 u^2 + 56 u^3 (their Theorem 7.1), a bound J.-M. Muller and L. Rideau proved formally (ACM Trans.
    /// Math. Softw. 48(1), 2022, doi:10.1145/3484514). `/` is tested to 8 u^2 and
    /// measures about 2 u^2.
    /// Barring underflow and overflow; a zero or non-finite divisor gives whatever its steps give. The low part is
    /// never a negative zero (`Neg`'s canonical form).
    #[inline(always)]
    pub fn fast_div(self, b: DD) -> DD {
        let th = self.hi / b.hi;
        // (rh, rl) ~ (b.hi + b.lo) th
        let (ch, cl1) = two_prod(b.hi, th);
        let (h, tl1) = quick_two_sum(ch, b.lo * th);
        let (rh, rl) = quick_two_sum(h, tl1 + cl1);
        // self.hi - rh is exact (Sterbenz: rh is within (3u + 6u^2) self.hi of self.hi)
        let d = (self.hi - rh) + (self.lo - rl);
        let (h, l) = quick_two_sum(th, d / b.hi);
        DD { hi: h, lo: l + 0.0 }
    }
    /// the square: the two-product of hi, and 2 hi lo by one fused multiply-add, one rounding fewer than `self * self`
    #[inline(always)]
    pub fn sqr(self) -> DD {
        let (p, e) = two_prod(self.hi, self.hi);
        let e = (self.hi + self.hi).mul_add(self.lo, e);
        let (h, l) = quick_two_sum(p, e);
        DD { hi: h, lo: l }
    }
    /// the square root, within 25/8 u^2 = 3.125 u^2 relative (u = 2^-53): Algorithm 8 (SQRTDWtoDW) of V. Lefèvre,
    /// N. Louvet, J.-M. Muller, J. Picot, L. Rideau, "Accurate calculation of Euclidean norms using double-word
    /// arithmetic", ACM Trans. Math. Softw. 49(1), 2023, doi:10.1145/3568672, whose Theorem 3.5 (HAL hal-03482567v1)
    /// proves the bound, asymptotically optimal. Its condition x >= 2^(2k), k >= (emin + p)/2, keeps hi - s^2 exact;
    /// a smaller x is scaled by 2^972 first and the root by 2^-486 after, both exact. Zero, a negative, infinite or
    /// NaN hi gives hi.sqrt() with lo = 0.
    pub fn sqrt(self) -> DD {
        // zero, negative, NaN (unordered) or infinite
        if self.hi.partial_cmp(&0.0) != Some(std::cmp::Ordering::Greater) || self.hi == f64::INFINITY {
            return DD {
                hi: self.hi.sqrt(),
                lo: 0.0,
            };
        }
        // 2^(2k) with k = -484, the least even power of two the theorem allows in binary64
        if self.hi < f64::from_bits((1023 - 968) << 52) {
            return self.mul_pwr2(2f64.powi(972)).sqrt().mul_pwr2(2f64.powi(-486));
        }
        let sh = self.hi.sqrt();
        // exact: the remainder of a correctly rounded square root, by one fused multiply-add
        let rho1 = (-sh).mul_add(sh, self.hi);
        let rho2 = self.lo + rho1;
        let sl = rho2 / (sh + sh);
        let (h, l) = quick_two_sum(sh, sl);
        DD { hi: h, lo: l }
    }
    /// self^n by binary powering (`sqr` and `*`), and the reciprocal for n < 0; self^0 is one
    pub fn powi(self, n: i32) -> DD {
        if n == 0 {
            return DD::ONE;
        }
        let k = n.unsigned_abs();
        if n < 0 && self.hi.abs().log2() * k as f64 > 1023.0 {
            // self^k overflows while self^n may be representable, below 2^-1022 and so with fewer bits: power the
            // reciprocal instead
            return self.recip().powu(k);
        }
        let s = self.powu(k);
        if n < 0 {
            DD::ONE / s
        } else {
            s
        }
    }
    /// self^k, k >= 1, by binary powering
    fn powu(self, mut k: u32) -> DD {
        if k == 1 {
            return self;
        }
        let mut r = self;
        let mut s = DD::ONE;
        while k > 0 {
            if k % 2 == 1 {
                s = s * r;
            }
            k /= 2;
            if k > 0 {
                r = r.sqr();
            }
        }
        s
    }
    #[inline(always)]
    pub fn mul_f(self, b: f64) -> DD {
        let (p, e) = two_prod(self.hi, b);
        let e = self.lo.mul_add(b, e);
        let (h, l) = quick_two_sum(p, e);
        DD { hi: h, lo: l }
    }
    /// times a power of two b (`is_pwr2`): both parts scaled, exact barring overflow and underflow, so `mul_f(b)`
    /// without its rounding steps, bit for bit except a zero lo, which takes the sign of lo b where `mul_f` gives +0;
    /// for computing in a variable rescaled by 2^k
    #[inline(always)]
    pub fn mul_pwr2(self, b: f64) -> DD {
        debug_assert!(is_pwr2(b), "mul_pwr2: {b} is not a power of two");
        DD {
            hi: self.hi * b,
            lo: self.lo * b,
        }
    }
}

#[cfg(feature = "f128")]
impl DD {
    /// hi = RN(x), lo = RN(x - hi): the greedy parts, to about 2^-106 relative (x - hi is exact in f128)
    #[inline(always)]
    pub fn from_f128(x: f128) -> DD {
        let hi = x as f64;
        if !hi.is_finite() {
            return DD::from_f64(hi);
        }
        DD {
            hi,
            lo: (x - hi as f128) as f64,
        }
    }
    /// correctly rounded (hi + lo is rounded once)
    #[inline(always)]
    pub fn to_f128(self) -> f128 {
        self.hi as f128 + self.lo as f128
    }
}

impl Add for DD {
    type Output = DD;
    #[inline(always)]
    fn add(self, b: DD) -> DD {
        let (s, e) = two_sum(self.hi, b.hi);
        let (t, f) = two_sum(self.lo, b.lo);
        let e = e + t;
        let (s, e) = quick_two_sum(s, e);
        let e = e + f;
        let (h, l) = quick_two_sum(s, e);
        DD { hi: h, lo: l }
    }
}

impl Neg for DD {
    type Output = DD;
    #[inline(always)]
    /// -hi, and -lo + 0, which is -lo except that a zero lo is +0: the low part of a negation never carries a
    /// negative zero (the canonical form; the value's sign of zero is hi's)
    fn neg(self) -> DD {
        DD {
            hi: -self.hi,
            lo: -self.lo + 0.0,
        }
    }
}

impl Sub for DD {
    type Output = DD;
    #[inline(always)]
    fn sub(self, b: DD) -> DD {
        self + (-b)
    }
}

impl Mul for DD {
    type Output = DD;
    #[inline(always)]
    fn mul(self, b: DD) -> DD {
        let (p, e) = two_prod(self.hi, b.hi);
        let e = self.hi.mul_add(b.lo, e);
        let e = self.lo.mul_add(b.hi, e);
        let (h, l) = quick_two_sum(p, e);
        DD { hi: h, lo: l }
    }
}

impl Div for DD {
    type Output = DD;
    #[inline(always)]
    fn div(self, b: DD) -> DD {
        let q1 = self.hi / b.hi;
        let r = self - b.mul_f(q1);
        let q2 = r.hi / b.hi;
        let r = r - b.mul_f(q2);
        let q3 = r.hi / b.hi;
        let (q1, q2) = quick_two_sum(q1, q2);
        DD { hi: q1, lo: q2 } + DD::from_f64(q3)
    }
}
