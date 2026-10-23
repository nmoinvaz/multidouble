// The NEON backend's body, included twice: on aarch64 with `core::arch::aarch64::*` in scope, and in the x86 test
// build with the pure-Rust model of the same intrinsics in `v8::neon_model`, so its logic is checked bit for bit
// against the scalar operations on every CI runner, not only on ARM.
//
// Four 128-bit registers of two f64 each. NEON's FMLA is fused (one rounding), as the double-double algorithms need.

/// 8 f64 lanes in four NEON registers.
#[derive(Clone, Copy, Debug)]
pub struct V8(pub [float64x2_t; 4]);

macro_rules! four {
    ($f:ident, $a:expr) => {
        unsafe { V8([$f($a.0[0]), $f($a.0[1]), $f($a.0[2]), $f($a.0[3])]) }
    };
    ($f:ident, $a:expr, $b:expr) => {
        unsafe { V8([$f($a.0[0], $b.0[0]), $f($a.0[1], $b.0[1]), $f($a.0[2], $b.0[2]), $f($a.0[3], $b.0[3])]) }
    };
}

macro_rules! four_mask {
    ($f:ident, $a:expr, $b:expr) => {
        unsafe { M8([$f($a.0[0], $b.0[0]), $f($a.0[1], $b.0[1]), $f($a.0[2], $b.0[2]), $f($a.0[3], $b.0[3])]) }
    };
}

#[allow(unused_unsafe)]
impl V8 {
    pub const ISA: &'static str = "neon";
    #[inline(always)]
    pub fn splat(x: f64) -> Self {
        unsafe {
            let v = vdupq_n_f64(x);
            V8([v, v, v, v])
        }
    }
    #[inline(always)]
    pub fn zero() -> Self {
        Self::splat(0.0)
    }
    #[inline(always)]
    pub fn load(s: &[f64]) -> Self {
        assert!(s.len() >= 8);
        let p = s.as_ptr();
        unsafe { V8([vld1q_f64(p), vld1q_f64(p.add(2)), vld1q_f64(p.add(4)), vld1q_f64(p.add(6))]) }
    }
    #[inline(always)]
    pub fn store(self, s: &mut [f64]) {
        assert!(s.len() >= 8);
        let p = s.as_mut_ptr();
        unsafe {
            vst1q_f64(p, self.0[0]);
            vst1q_f64(p.add(2), self.0[1]);
            vst1q_f64(p.add(4), self.0[2]);
            vst1q_f64(p.add(6), self.0[3]);
        }
    }
    #[inline(always)]
    pub fn add(self, o: Self) -> Self {
        four!(vaddq_f64, self, o)
    }
    #[inline(always)]
    pub fn sub(self, o: Self) -> Self {
        four!(vsubq_f64, self, o)
    }
    #[inline(always)]
    pub fn mul(self, o: Self) -> Self {
        four!(vmulq_f64, self, o)
    }
    #[inline(always)]
    pub fn div(self, o: Self) -> Self {
        four!(vdivq_f64, self, o)
    }
    /// self * b + c with one rounding (vfmaq_f64(c, a, b) = c + a b)
    #[inline(always)]
    pub fn fma(self, b: Self, c: Self) -> Self {
        unsafe {
            V8([
                vfmaq_f64(c.0[0], self.0[0], b.0[0]),
                vfmaq_f64(c.0[1], self.0[1], b.0[1]),
                vfmaq_f64(c.0[2], self.0[2], b.0[2]),
                vfmaq_f64(c.0[3], self.0[3], b.0[3]),
            ])
        }
    }
    /// self * b - c with one rounding: -c + a b, the negation being exact
    #[inline(always)]
    pub fn fms(self, b: Self, c: Self) -> Self {
        unsafe {
            V8([
                vfmaq_f64(vnegq_f64(c.0[0]), self.0[0], b.0[0]),
                vfmaq_f64(vnegq_f64(c.0[1]), self.0[1], b.0[1]),
                vfmaq_f64(vnegq_f64(c.0[2]), self.0[2], b.0[2]),
                vfmaq_f64(vnegq_f64(c.0[3]), self.0[3], b.0[3]),
            ])
        }
    }
    #[inline(always)]
    pub fn abs(self) -> Self {
        four!(vabsq_f64, self)
    }
    #[inline(always)]
    pub fn max(self, o: Self) -> Self {
        four!(vmaxq_f64, self, o)
    }
    /// all lanes = lane j
    #[inline(always)]
    pub fn bcast(self, j: usize) -> Self {
        let mut a = [0.0; 8];
        self.store(&mut a);
        Self::splat(a[j])
    }
    #[inline(always)]
    pub fn sqrt(self) -> Self {
        four!(vsqrtq_f64, self)
    }
    /// the exponent bits only: 2^floor(log2 |x|) for normal x
    #[inline(always)]
    pub fn pow2_floor(self) -> Self {
        unsafe {
            let m = vdupq_n_u64(0x7ff0_0000_0000_0000);
            let f = |v: float64x2_t| vreinterpretq_f64_u64(vandq_u64(vreinterpretq_u64_f64(v), m));
            V8([f(self.0[0]), f(self.0[1]), f(self.0[2]), f(self.0[3])])
        }
    }
    /// self != o (true when either is NaN, as C's !=): the complement of the ordered equality
    #[inline(always)]
    pub fn ne(self, o: Self) -> M8 {
        self.eq(o).not()
    }
    /// self == o (false when either is NaN)
    #[inline(always)]
    pub fn eq(self, o: Self) -> M8 {
        four_mask!(vceqq_f64, self, o)
    }
    /// self > o (false when either is NaN)
    #[inline(always)]
    pub fn gt(self, o: Self) -> M8 {
        four_mask!(vcgtq_f64, self, o)
    }
    /// self >= o (false when either is NaN)
    #[inline(always)]
    pub fn ge(self, o: Self) -> M8 {
        four_mask!(vcgeq_f64, self, o)
    }
}

/// 8-lane mask (all-ones / all-zeros 64-bit lanes in four NEON registers).
#[derive(Clone, Copy, Debug)]
pub struct M8(pub [uint64x2_t; 4]);

#[allow(unused_unsafe)]
impl M8 {
    #[inline(always)]
    pub fn and(self, o: Self) -> Self {
        four_mask!(vandq_u64, self, o)
    }
    #[inline(always)]
    pub fn or(self, o: Self) -> Self {
        four_mask!(vorrq_u64, self, o)
    }
    #[inline(always)]
    pub fn not(self) -> Self {
        unsafe {
            let ones = vdupq_n_u64(u64::MAX);
            M8([
                veorq_u64(self.0[0], ones),
                veorq_u64(self.0[1], ones),
                veorq_u64(self.0[2], ones),
                veorq_u64(self.0[3], ones),
            ])
        }
    }
    /// per lane: t where set, f elsewhere
    #[inline(always)]
    pub fn sel(self, t: V8, f: V8) -> V8 {
        unsafe {
            V8([
                vbslq_f64(self.0[0], t.0[0], f.0[0]),
                vbslq_f64(self.0[1], t.0[1], f.0[1]),
                vbslq_f64(self.0[2], t.0[2], f.0[2]),
                vbslq_f64(self.0[3], t.0[3], f.0[3]),
            ])
        }
    }
    /// bit j = lane j
    #[inline(always)]
    pub fn bits(self) -> u8 {
        let mut b = 0u8;
        for k in 0..4 {
            let (lo, hi) = unsafe { (vgetq_lane_u64::<0>(self.0[k]), vgetq_lane_u64::<1>(self.0[k])) };
            b |= ((lo & 1) as u8) << (2 * k) | ((hi & 1) as u8) << (2 * k + 1);
        }
        b
    }
}
