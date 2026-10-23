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
    #[inline(always)]
    pub fn to_f64(self) -> f64 {
        self.hi + self.lo
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
    #[inline(always)]
    pub fn mul_f(self, b: f64) -> DD {
        let (p, e) = two_prod(self.hi, b);
        let e = self.lo.mul_add(b, e);
        let (h, l) = quick_two_sum(p, e);
        DD { hi: h, lo: l }
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
    fn neg(self) -> DD {
        DD {
            hi: -self.hi,
            lo: -self.lo,
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
