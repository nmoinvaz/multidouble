//! 8-lane f64 vector `V8<S>` on a backend `S` ([`crate::simd`]), chosen at run time by [`crate::simd::dispatch`] or
//! at compile time as [`crate::simd::Native`]:
//!
//! * `avx512`: AVX-512F, one zmm register, every operation one intrinsic;
//! * `avx2`: AVX2 + FMA, two ymm registers;
//! * `sse2`: x86 and x86-64 otherwise (SSE2 is part of the x86-64 baseline), four xmm registers, with the fused
//!   operations per lane through `f64::mul_add` (SSE2 has no FMA instruction);
//! * `neon`: aarch64, four NEON registers, fused multiply-add in hardware;
//! * `portable`: every target, a plain array, `f64::mul_add` for the fused operations, which the double-double
//!   algorithms need to be exact.
//!
//! All operations are IEEE round-to-nearest with no reassociation, as the error-free transformations in `dv`
//! require, so every backend gives bitwise the same results for finite inputs. (`max` follows each instruction set
//! for NaN and for +0 against -0; the arithmetic never depends on it there.) `M8` is an 8-lane mask from the
//! comparisons `ne`, `eq`, `gt`, `ge`, with per-lane select `sel`: the quad-double lanes (`qv`) run QD's
//! data-dependent branches with them.

use crate::simd::{backend, Simd};

#[cfg(target_arch = "x86_64")]
mod avx512 {
    use std::arch::x86_64::*;

    #[derive(Clone, Copy, Debug)]
    #[repr(transparent)]
    pub struct V8(pub __m512d);

    #[allow(unused_unsafe)]
    impl V8 {
        pub const ISA: &'static str = "avx512";
        #[inline(always)]
        pub fn splat(x: f64) -> Self {
            unsafe { V8(_mm512_set1_pd(x)) }
        }
        #[inline(always)]
        pub fn zero() -> Self {
            unsafe { V8(_mm512_setzero_pd()) }
        }
        #[inline(always)]
        pub fn load(s: &[f64]) -> Self {
            assert!(s.len() >= 8);
            unsafe { V8(_mm512_loadu_pd(s.as_ptr())) }
        }
        #[inline(always)]
        pub fn store(self, s: &mut [f64]) {
            assert!(s.len() >= 8);
            unsafe { _mm512_storeu_pd(s.as_mut_ptr(), self.0) }
        }
        #[inline(always)]
        pub fn add(self, o: Self) -> Self {
            unsafe { V8(_mm512_add_pd(self.0, o.0)) }
        }
        #[inline(always)]
        pub fn sub(self, o: Self) -> Self {
            unsafe { V8(_mm512_sub_pd(self.0, o.0)) }
        }
        #[inline(always)]
        pub fn mul(self, o: Self) -> Self {
            unsafe { V8(_mm512_mul_pd(self.0, o.0)) }
        }
        #[inline(always)]
        pub fn div(self, o: Self) -> Self {
            unsafe { V8(_mm512_div_pd(self.0, o.0)) }
        }
        /// self * b + c with one rounding
        #[inline(always)]
        pub fn fma(self, b: Self, c: Self) -> Self {
            unsafe { V8(_mm512_fmadd_pd(self.0, b.0, c.0)) }
        }
        /// self * b - c with one rounding
        #[inline(always)]
        pub fn fms(self, b: Self, c: Self) -> Self {
            unsafe { V8(_mm512_fmsub_pd(self.0, b.0, c.0)) }
        }
        #[inline(always)]
        pub fn abs(self) -> Self {
            unsafe { V8(_mm512_abs_pd(self.0)) }
        }
        #[inline(always)]
        pub fn max(self, o: Self) -> Self {
            unsafe { V8(_mm512_max_pd(self.0, o.0)) }
        }
        /// all lanes = lane j
        #[inline(always)]
        pub fn bcast(self, j: usize) -> Self {
            unsafe { V8(_mm512_permutexvar_pd(_mm512_set1_epi64(j as i64), self.0)) }
        }
        #[inline(always)]
        pub fn sqrt(self) -> Self {
            unsafe { V8(_mm512_sqrt_pd(self.0)) }
        }
        /// the exponent bits only: 2^floor(log2 |x|) for normal x
        #[inline(always)]
        pub fn pow2_floor(self) -> Self {
            unsafe {
                V8(_mm512_castsi512_pd(_mm512_and_si512(
                    _mm512_castpd_si512(self.0),
                    _mm512_set1_epi64(0x7ff0_0000_0000_0000),
                )))
            }
        }
        /// self != o (true when either is NaN, as C's !=)
        #[inline(always)]
        pub fn ne(self, o: Self) -> M8 {
            unsafe { M8(_mm512_cmp_pd_mask::<_CMP_NEQ_UQ>(self.0, o.0)) }
        }
        /// self == o (false when either is NaN)
        #[inline(always)]
        pub fn eq(self, o: Self) -> M8 {
            unsafe { M8(_mm512_cmp_pd_mask::<_CMP_EQ_OQ>(self.0, o.0)) }
        }
        /// self > o (false when either is NaN)
        #[inline(always)]
        pub fn gt(self, o: Self) -> M8 {
            unsafe { M8(_mm512_cmp_pd_mask::<_CMP_GT_OQ>(self.0, o.0)) }
        }
        /// self >= o (false when either is NaN)
        #[inline(always)]
        pub fn ge(self, o: Self) -> M8 {
            unsafe { M8(_mm512_cmp_pd_mask::<_CMP_GE_OQ>(self.0, o.0)) }
        }
        /// self + o where m is set, self elsewhere
        #[inline(always)]
        pub fn add_where(self, m: M8, o: Self) -> Self {
            unsafe { V8(_mm512_mask_add_pd(self.0, m.0, self.0, o.0)) }
        }
        /// self as a divisor, with y = RN(1/self) on the lanes ok, those with |self| in [LO, HI]
        #[inline(always)]
        pub fn divisor(self) -> D {
            unsafe {
                let (b, one) = (self.0, _mm512_set1_pd(1.0));
                let ab = _mm512_abs_pd(b);
                let ok = _mm512_mask_cmp_pd_mask::<_CMP_LE_OQ>(
                    _mm512_cmp_pd_mask::<_CMP_GE_OQ>(ab, _mm512_set1_pd(LO)),
                    ab,
                    _mm512_set1_pd(HI),
                );
                // rcp14 is within 2^-14 relative, and two Newton steps leave y within 0.14 ulp before its rounding, so
                // y is faithful
                let mut y = _mm512_rcp14_pd(b);
                y = _mm512_fmadd_pd(y, _mm512_fnmadd_pd(b, y, one), y);
                y = _mm512_fmadd_pd(y, _mm512_fnmadd_pd(b, y, one), y);
                // a third step from a faithful y, with 1 - b y exact, gives RN(1/b) (Markstein), except for a
                // significand of all ones, where y can stay at the power of two below 1/b and RN(1/b) is that
                // power with its last bit set
                y = _mm512_fmadd_pd(y, _mm512_fnmadd_pd(b, y, one), y);
                let sig = _mm512_set1_epi64(0x000f_ffff_ffff_ffff);
                let ones = _mm512_cmpeq_epi64_mask(_mm512_and_si512(_mm512_castpd_si512(b), sig), sig);
                let y = _mm512_castsi512_pd(_mm512_mask_or_epi64(
                    _mm512_castpd_si512(y),
                    ones,
                    _mm512_castpd_si512(y),
                    _mm512_set1_epi64(1),
                ));
                D { b, y, ok }
            }
        }
        /// self / d.b, correctly rounded, as q = RN(a y) and one correction RN(q + (a - b q) y). When q is within an
        /// ulp of a / b, the remainder is exact and the correction gives RN(a/b) (Markstein). When it is not, a and b
        /// normalized to [1, 2) have a < b, and a / b is at least (2 - a) 2^-54 from every midpoint, while the
        /// corrected value is within 1.75 2^-105 of a / b. It can cross a midpoint only for a within 3.5 ulps of 2,
        /// which the tests check exhaustively. Lanes with |a| or |b| out of [LO, HI] take `div`.
        #[inline(always)]
        pub fn div_by(self, d: D) -> Self {
            unsafe {
                let a = self.0;
                let aa = _mm512_abs_pd(a);
                let fast = _mm512_mask_cmp_pd_mask::<_CMP_LE_OQ>(
                    _mm512_mask_cmp_pd_mask::<_CMP_GE_OQ>(d.ok, aa, _mm512_set1_pd(LO)),
                    aa,
                    _mm512_set1_pd(HI),
                );
                // for a = 0, a y is the zero with the sign of a / b, which the masked correction keeps
                let zero = _mm512_mask_cmp_pd_mask::<_CMP_EQ_OQ>(d.ok, a, _mm512_setzero_pd());
                let q = _mm512_mul_pd(a, d.y);
                let q = _mm512_mask3_fmadd_pd(_mm512_fnmadd_pd(d.b, q, a), d.y, q, fast);
                let slow = !(fast | zero);
                if slow == 0 {
                    V8(q)
                } else {
                    V8(_mm512_mask_div_pd(q, slow, a, d.b))
                }
            }
        }
    }

    /// The range of |a| and |b| where `div_by` takes the reciprocal, so that a / b, 1 / b and the remainders a - b q
    /// stay normal and exact.
    const LO: f64 = f64::from_bits((1023 - 500) << 52);
    const HI: f64 = f64::from_bits((1023 + 500) << 52);

    /// A divisor b with y = RN(1/b) on the lanes ok.
    #[derive(Clone, Copy, Debug)]
    pub struct D {
        b: __m512d,
        y: __m512d,
        ok: __mmask8,
    }

    /// 8-lane mask (one bit per lane).
    #[derive(Clone, Copy, Debug)]
    pub struct M8(pub __mmask8);

    impl M8 {
        /// self and a == b
        #[inline(always)]
        pub fn and_eq(self, a: V8, b: V8) -> Self {
            unsafe { M8(_mm512_mask_cmp_pd_mask::<_CMP_EQ_OQ>(self.0, a.0, b.0)) }
        }
        /// self and a != b
        #[inline(always)]
        pub fn and_ne(self, a: V8, b: V8) -> Self {
            unsafe { M8(_mm512_mask_cmp_pd_mask::<_CMP_NEQ_UQ>(self.0, a.0, b.0)) }
        }
        #[inline(always)]
        pub fn and(self, o: Self) -> Self {
            M8(self.0 & o.0)
        }
        #[inline(always)]
        pub fn or(self, o: Self) -> Self {
            M8(self.0 | o.0)
        }
        #[inline(always)]
        pub fn not(self) -> Self {
            M8(!self.0)
        }
        /// per lane: t where set, f elsewhere
        #[inline(always)]
        pub fn sel(self, t: V8, f: V8) -> V8 {
            unsafe { V8(_mm512_mask_blend_pd(self.0, f.0, t.0)) }
        }
        /// bit j = lane j
        #[inline(always)]
        pub fn bits(self) -> u8 {
            self.0
        }
    }
}

#[cfg(target_arch = "x86_64")]
mod avx2 {
    use std::arch::x86_64::*;

    #[derive(Clone, Copy, Debug)]
    pub struct V8(pub [__m256d; 2]);

    macro_rules! two {
        ($f:ident, $a:expr, $b:expr) => {
            unsafe { V8([$f($a.0[0], $b.0[0]), $f($a.0[1], $b.0[1])]) }
        };
    }

    #[allow(unused_unsafe)]
    impl V8 {
        pub const ISA: &'static str = "avx2";
        #[inline(always)]
        pub fn splat(x: f64) -> Self {
            unsafe { V8([_mm256_set1_pd(x), _mm256_set1_pd(x)]) }
        }
        #[inline(always)]
        pub fn zero() -> Self {
            unsafe { V8([_mm256_setzero_pd(), _mm256_setzero_pd()]) }
        }
        #[inline(always)]
        pub fn load(s: &[f64]) -> Self {
            assert!(s.len() >= 8);
            unsafe { V8([_mm256_loadu_pd(s.as_ptr()), _mm256_loadu_pd(s.as_ptr().add(4))]) }
        }
        #[inline(always)]
        pub fn store(self, s: &mut [f64]) {
            assert!(s.len() >= 8);
            unsafe {
                _mm256_storeu_pd(s.as_mut_ptr(), self.0[0]);
                _mm256_storeu_pd(s.as_mut_ptr().add(4), self.0[1]);
            }
        }
        #[inline(always)]
        pub fn add(self, o: Self) -> Self {
            two!(_mm256_add_pd, self, o)
        }
        #[inline(always)]
        pub fn sub(self, o: Self) -> Self {
            two!(_mm256_sub_pd, self, o)
        }
        #[inline(always)]
        pub fn mul(self, o: Self) -> Self {
            two!(_mm256_mul_pd, self, o)
        }
        #[inline(always)]
        pub fn div(self, o: Self) -> Self {
            two!(_mm256_div_pd, self, o)
        }
        #[inline(always)]
        pub fn fma(self, b: Self, c: Self) -> Self {
            unsafe {
                V8([
                    _mm256_fmadd_pd(self.0[0], b.0[0], c.0[0]),
                    _mm256_fmadd_pd(self.0[1], b.0[1], c.0[1]),
                ])
            }
        }
        #[inline(always)]
        pub fn fms(self, b: Self, c: Self) -> Self {
            unsafe {
                V8([
                    _mm256_fmsub_pd(self.0[0], b.0[0], c.0[0]),
                    _mm256_fmsub_pd(self.0[1], b.0[1], c.0[1]),
                ])
            }
        }
        #[inline(always)]
        pub fn abs(self) -> Self {
            unsafe {
                let m = _mm256_set1_pd(-0.0);
                V8([_mm256_andnot_pd(m, self.0[0]), _mm256_andnot_pd(m, self.0[1])])
            }
        }
        #[inline(always)]
        pub fn max(self, o: Self) -> Self {
            two!(_mm256_max_pd, self, o)
        }
        #[inline(always)]
        pub fn bcast(self, j: usize) -> Self {
            let mut a = [0.0; 8];
            self.store(&mut a);
            Self::splat(a[j])
        }
        #[inline(always)]
        pub fn sqrt(self) -> Self {
            unsafe { V8([_mm256_sqrt_pd(self.0[0]), _mm256_sqrt_pd(self.0[1])]) }
        }
        /// the exponent bits only: 2^floor(log2 |x|) for normal x
        #[inline(always)]
        pub fn pow2_floor(self) -> Self {
            unsafe {
                let m = _mm256_castsi256_pd(_mm256_set1_epi64x(0x7ff0_0000_0000_0000));
                V8([_mm256_and_pd(self.0[0], m), _mm256_and_pd(self.0[1], m)])
            }
        }
        /// self != o (true when either is NaN, as C's !=)
        #[inline(always)]
        pub fn ne(self, o: Self) -> M8 {
            unsafe {
                M8([
                    _mm256_cmp_pd::<_CMP_NEQ_UQ>(self.0[0], o.0[0]),
                    _mm256_cmp_pd::<_CMP_NEQ_UQ>(self.0[1], o.0[1]),
                ])
            }
        }
        /// self == o (false when either is NaN)
        #[inline(always)]
        pub fn eq(self, o: Self) -> M8 {
            unsafe {
                M8([
                    _mm256_cmp_pd::<_CMP_EQ_OQ>(self.0[0], o.0[0]),
                    _mm256_cmp_pd::<_CMP_EQ_OQ>(self.0[1], o.0[1]),
                ])
            }
        }
        /// self > o (false when either is NaN)
        #[inline(always)]
        pub fn gt(self, o: Self) -> M8 {
            unsafe {
                M8([
                    _mm256_cmp_pd::<_CMP_GT_OQ>(self.0[0], o.0[0]),
                    _mm256_cmp_pd::<_CMP_GT_OQ>(self.0[1], o.0[1]),
                ])
            }
        }
        /// self >= o (false when either is NaN)
        #[inline(always)]
        pub fn ge(self, o: Self) -> M8 {
            unsafe {
                M8([
                    _mm256_cmp_pd::<_CMP_GE_OQ>(self.0[0], o.0[0]),
                    _mm256_cmp_pd::<_CMP_GE_OQ>(self.0[1], o.0[1]),
                ])
            }
        }
    }

    /// 8-lane mask (all-ones / all-zeros 64-bit lanes in two ymm registers).
    #[derive(Clone, Copy, Debug)]
    pub struct M8(pub [__m256d; 2]);

    #[allow(unused_unsafe)]
    impl M8 {
        #[inline(always)]
        pub fn and(self, o: Self) -> Self {
            unsafe { M8([_mm256_and_pd(self.0[0], o.0[0]), _mm256_and_pd(self.0[1], o.0[1])]) }
        }
        #[inline(always)]
        pub fn or(self, o: Self) -> Self {
            unsafe { M8([_mm256_or_pd(self.0[0], o.0[0]), _mm256_or_pd(self.0[1], o.0[1])]) }
        }
        #[inline(always)]
        pub fn not(self) -> Self {
            unsafe {
                let ones = _mm256_castsi256_pd(_mm256_set1_epi64x(-1));
                M8([_mm256_xor_pd(self.0[0], ones), _mm256_xor_pd(self.0[1], ones)])
            }
        }
        /// per lane: t where set, f elsewhere
        #[inline(always)]
        pub fn sel(self, t: V8, f: V8) -> V8 {
            unsafe {
                V8([
                    _mm256_blendv_pd(f.0[0], t.0[0], self.0[0]),
                    _mm256_blendv_pd(f.0[1], t.0[1], self.0[1]),
                ])
            }
        }
        /// bit j = lane j
        #[inline(always)]
        pub fn bits(self) -> u8 {
            unsafe { (_mm256_movemask_pd(self.0[0]) | (_mm256_movemask_pd(self.0[1]) << 4)) as u8 }
        }
    }
}

#[cfg(all(any(target_arch = "x86", target_arch = "x86_64"), target_feature = "sse2"))]
mod sse2 {
    #[cfg(target_arch = "x86")]
    use std::arch::x86::*;
    #[cfg(target_arch = "x86_64")]
    use std::arch::x86_64::*;

    /// 8 f64 lanes in four xmm registers.
    #[derive(Clone, Copy, Debug)]
    pub struct V8(pub [__m128d; 4]);

    macro_rules! four {
        ($f:ident, $a:expr) => {
            unsafe { V8([$f($a.0[0]), $f($a.0[1]), $f($a.0[2]), $f($a.0[3])]) }
        };
        ($f:ident, $a:expr, $b:expr) => {
            unsafe {
                V8([
                    $f($a.0[0], $b.0[0]),
                    $f($a.0[1], $b.0[1]),
                    $f($a.0[2], $b.0[2]),
                    $f($a.0[3], $b.0[3]),
                ])
            }
        };
    }

    macro_rules! four_mask {
        ($f:ident, $a:expr, $b:expr) => {
            unsafe {
                M8([
                    $f($a.0[0], $b.0[0]),
                    $f($a.0[1], $b.0[1]),
                    $f($a.0[2], $b.0[2]),
                    $f($a.0[3], $b.0[3]),
                ])
            }
        };
    }

    #[allow(unused_unsafe)]
    impl V8 {
        pub const ISA: &'static str = "sse2";
        #[inline(always)]
        fn to_array(self) -> [f64; 8] {
            let mut a = [0.0; 8];
            self.store(&mut a);
            a
        }
        #[inline(always)]
        fn from_array(a: [f64; 8]) -> Self {
            Self::load(&a)
        }
        #[inline(always)]
        pub fn splat(x: f64) -> Self {
            unsafe {
                let v = _mm_set1_pd(x);
                V8([v, v, v, v])
            }
        }
        #[inline(always)]
        pub fn zero() -> Self {
            unsafe {
                let v = _mm_setzero_pd();
                V8([v, v, v, v])
            }
        }
        #[inline(always)]
        pub fn load(s: &[f64]) -> Self {
            assert!(s.len() >= 8);
            let p = s.as_ptr();
            unsafe {
                V8([
                    _mm_loadu_pd(p),
                    _mm_loadu_pd(p.add(2)),
                    _mm_loadu_pd(p.add(4)),
                    _mm_loadu_pd(p.add(6)),
                ])
            }
        }
        #[inline(always)]
        pub fn store(self, s: &mut [f64]) {
            assert!(s.len() >= 8);
            let p = s.as_mut_ptr();
            unsafe {
                _mm_storeu_pd(p, self.0[0]);
                _mm_storeu_pd(p.add(2), self.0[1]);
                _mm_storeu_pd(p.add(4), self.0[2]);
                _mm_storeu_pd(p.add(6), self.0[3]);
            }
        }
        #[inline(always)]
        pub fn add(self, o: Self) -> Self {
            four!(_mm_add_pd, self, o)
        }
        #[inline(always)]
        pub fn sub(self, o: Self) -> Self {
            four!(_mm_sub_pd, self, o)
        }
        #[inline(always)]
        pub fn mul(self, o: Self) -> Self {
            four!(_mm_mul_pd, self, o)
        }
        #[inline(always)]
        pub fn div(self, o: Self) -> Self {
            four!(_mm_div_pd, self, o)
        }
        /// self * b + c with one rounding, per lane (`f64::mul_add`: SSE2 has no fused multiply-add)
        #[inline(always)]
        pub fn fma(self, b: Self, c: Self) -> Self {
            let (x, y, z) = (self.to_array(), b.to_array(), c.to_array());
            Self::from_array(std::array::from_fn(|i| x[i].mul_add(y[i], z[i])))
        }
        /// self * b - c with one rounding, per lane
        #[inline(always)]
        pub fn fms(self, b: Self, c: Self) -> Self {
            let (x, y, z) = (self.to_array(), b.to_array(), c.to_array());
            Self::from_array(std::array::from_fn(|i| x[i].mul_add(y[i], -z[i])))
        }
        #[inline(always)]
        pub fn abs(self) -> Self {
            unsafe {
                let m = _mm_set1_pd(-0.0);
                V8([
                    _mm_andnot_pd(m, self.0[0]),
                    _mm_andnot_pd(m, self.0[1]),
                    _mm_andnot_pd(m, self.0[2]),
                    _mm_andnot_pd(m, self.0[3]),
                ])
            }
        }
        #[inline(always)]
        pub fn max(self, o: Self) -> Self {
            four!(_mm_max_pd, self, o)
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
            four!(_mm_sqrt_pd, self)
        }
        /// the exponent bits only: 2^floor(log2 |x|) for normal x
        #[inline(always)]
        pub fn pow2_floor(self) -> Self {
            unsafe {
                let m = _mm_castsi128_pd(_mm_set1_epi64x(0x7ff0_0000_0000_0000));
                V8([
                    _mm_and_pd(self.0[0], m),
                    _mm_and_pd(self.0[1], m),
                    _mm_and_pd(self.0[2], m),
                    _mm_and_pd(self.0[3], m),
                ])
            }
        }
        /// self != o (true when either is NaN, as C's !=)
        #[inline(always)]
        pub fn ne(self, o: Self) -> M8 {
            four_mask!(_mm_cmpneq_pd, self, o)
        }
        /// self == o (false when either is NaN)
        #[inline(always)]
        pub fn eq(self, o: Self) -> M8 {
            four_mask!(_mm_cmpeq_pd, self, o)
        }
        /// self > o (false when either is NaN)
        #[inline(always)]
        pub fn gt(self, o: Self) -> M8 {
            four_mask!(_mm_cmpgt_pd, self, o)
        }
        /// self >= o (false when either is NaN)
        #[inline(always)]
        pub fn ge(self, o: Self) -> M8 {
            four_mask!(_mm_cmpge_pd, self, o)
        }
    }

    /// 8-lane mask (all-ones / all-zeros 64-bit lanes in four xmm registers).
    #[derive(Clone, Copy, Debug)]
    pub struct M8(pub [__m128d; 4]);

    #[allow(unused_unsafe)]
    impl M8 {
        #[inline(always)]
        pub fn and(self, o: Self) -> Self {
            four_mask!(_mm_and_pd, self, o)
        }
        #[inline(always)]
        pub fn or(self, o: Self) -> Self {
            four_mask!(_mm_or_pd, self, o)
        }
        #[inline(always)]
        pub fn not(self) -> Self {
            unsafe {
                let ones = _mm_castsi128_pd(_mm_set1_epi64x(-1));
                M8([
                    _mm_xor_pd(self.0[0], ones),
                    _mm_xor_pd(self.0[1], ones),
                    _mm_xor_pd(self.0[2], ones),
                    _mm_xor_pd(self.0[3], ones),
                ])
            }
        }
        /// per lane: t where set, f elsewhere (SSE2 has no blend: (m and t) or (not m and f))
        #[inline(always)]
        pub fn sel(self, t: V8, f: V8) -> V8 {
            unsafe {
                let s = |m: __m128d, a: __m128d, b: __m128d| _mm_or_pd(_mm_and_pd(m, a), _mm_andnot_pd(m, b));
                V8([
                    s(self.0[0], t.0[0], f.0[0]),
                    s(self.0[1], t.0[1], f.0[1]),
                    s(self.0[2], t.0[2], f.0[2]),
                    s(self.0[3], t.0[3], f.0[3]),
                ])
            }
        }
        /// bit j = lane j
        #[inline(always)]
        pub fn bits(self) -> u8 {
            unsafe {
                (_mm_movemask_pd(self.0[0])
                    | _mm_movemask_pd(self.0[1]) << 2
                    | _mm_movemask_pd(self.0[2]) << 4
                    | _mm_movemask_pd(self.0[3]) << 6) as u8
            }
        }
    }
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
mod neon {
    use core::arch::aarch64::*;
    include!("v8_neon.rs");
}

mod portable {
    #[derive(Clone, Copy, Debug)]
    pub struct V8(pub [f64; 8]);

    macro_rules! lanes {
        ($a:expr, $b:expr, $op:tt) => {{
            let mut r = [0.0; 8];
            for i in 0..8 {
                r[i] = $a.0[i] $op $b.0[i];
            }
            V8(r)
        }};
    }

    impl V8 {
        pub const ISA: &'static str = "portable";
        #[inline(always)]
        pub fn splat(x: f64) -> Self {
            V8([x; 8])
        }
        #[inline(always)]
        pub fn zero() -> Self {
            V8([0.0; 8])
        }
        #[inline(always)]
        pub fn load(s: &[f64]) -> Self {
            let mut r = [0.0; 8];
            r.copy_from_slice(&s[..8]);
            V8(r)
        }
        #[inline(always)]
        pub fn store(self, s: &mut [f64]) {
            s[..8].copy_from_slice(&self.0);
        }
        #[inline(always)]
        pub fn add(self, o: Self) -> Self {
            lanes!(self, o, +)
        }
        #[inline(always)]
        pub fn sub(self, o: Self) -> Self {
            lanes!(self, o, -)
        }
        #[inline(always)]
        pub fn mul(self, o: Self) -> Self {
            lanes!(self, o, *)
        }
        #[inline(always)]
        pub fn div(self, o: Self) -> Self {
            lanes!(self, o, /)
        }
        #[inline(always)]
        pub fn fma(self, b: Self, c: Self) -> Self {
            let mut r = [0.0; 8];
            for i in 0..8 {
                r[i] = self.0[i].mul_add(b.0[i], c.0[i]);
            }
            V8(r)
        }
        #[inline(always)]
        pub fn fms(self, b: Self, c: Self) -> Self {
            let mut r = [0.0; 8];
            for i in 0..8 {
                r[i] = self.0[i].mul_add(b.0[i], -c.0[i]);
            }
            V8(r)
        }
        #[inline(always)]
        pub fn abs(self) -> Self {
            V8(self.0.map(f64::abs))
        }
        #[inline(always)]
        pub fn max(self, o: Self) -> Self {
            let mut r = [0.0; 8];
            for i in 0..8 {
                r[i] = self.0[i].max(o.0[i]);
            }
            V8(r)
        }
        #[inline(always)]
        pub fn bcast(self, j: usize) -> Self {
            V8([self.0[j]; 8])
        }
        #[inline(always)]
        pub fn sqrt(self) -> Self {
            V8(self.0.map(f64::sqrt))
        }
        /// the exponent bits only: 2^floor(log2 |x|) for normal x
        #[inline(always)]
        pub fn pow2_floor(self) -> Self {
            V8(self.0.map(|x| f64::from_bits(x.to_bits() & 0x7ff0_0000_0000_0000)))
        }
        #[inline(always)]
        fn cmp(self, o: Self, f: impl Fn(f64, f64) -> bool) -> M8 {
            let mut m = 0u8;
            for i in 0..8 {
                if f(self.0[i], o.0[i]) {
                    m |= 1 << i;
                }
            }
            M8(m)
        }
        /// self != o (true when either is NaN, as C's !=)
        #[inline(always)]
        pub fn ne(self, o: Self) -> M8 {
            self.cmp(o, |a, b| a != b)
        }
        /// self == o (false when either is NaN)
        #[inline(always)]
        pub fn eq(self, o: Self) -> M8 {
            self.cmp(o, |a, b| a == b)
        }
        /// self > o (false when either is NaN)
        #[inline(always)]
        pub fn gt(self, o: Self) -> M8 {
            self.cmp(o, |a, b| a > b)
        }
        /// self >= o (false when either is NaN)
        #[inline(always)]
        pub fn ge(self, o: Self) -> M8 {
            self.cmp(o, |a, b| a >= b)
        }
    }

    /// 8-lane mask (bit j = lane j).
    #[derive(Clone, Copy, Debug)]
    pub struct M8(pub u8);

    impl M8 {
        #[inline(always)]
        pub fn and(self, o: Self) -> Self {
            M8(self.0 & o.0)
        }
        #[inline(always)]
        pub fn or(self, o: Self) -> Self {
            M8(self.0 | o.0)
        }
        #[inline(always)]
        pub fn not(self) -> Self {
            M8(!self.0)
        }
        /// per lane: t where set, f elsewhere
        #[inline(always)]
        pub fn sel(self, t: V8, f: V8) -> V8 {
            let mut r = [0.0; 8];
            for i in 0..8 {
                r[i] = if self.0 >> i & 1 == 1 { t.0[i] } else { f.0[i] };
            }
            V8(r)
        }
        #[inline(always)]
        pub fn bits(self) -> u8 {
            self.0
        }
    }
}

/// `Simd` for a backend type from its module's `V8` and `M8`: whether `hot` forces inlining (`always` or `hint`),
/// the target features its `vectorize` enables, and optionally in braces the divisor (`D`, `divisor`, `div_by`) and
/// the overrides of the trait's default operations. Without them the divisor is b itself.
macro_rules! simd {
    ($b:ty, $m:ident, $hot:ident $(, $feat:literal)?) => {
        simd!($b, $m, $hot $(, $feat)? {
            type D = $m::V8;
            #[inline(always)]
            fn divisor(b: $m::V8) -> $m::V8 {
                b
            }
            #[inline(always)]
            fn div_by(a: $m::V8, b: $m::V8) -> $m::V8 {
                a.div(b)
            }
        });
    };
    ($b:ty, $m:ident, $hot:ident $(, $feat:literal)? { $($extra:item)* }) => {
        impl crate::simd::sealed::Sealed for $b {}
        impl Simd for $b {
            const NAME: &'static str = $m::V8::ISA;
            type R = $m::V8;
            type M = $m::M8;
            #[inline(always)]
            fn splat(x: f64) -> $m::V8 {
                $m::V8::splat(x)
            }
            #[inline(always)]
            fn zero() -> $m::V8 {
                $m::V8::zero()
            }
            #[inline(always)]
            fn load(s: &[f64]) -> $m::V8 {
                $m::V8::load(s)
            }
            #[inline(always)]
            fn store(a: $m::V8, s: &mut [f64]) {
                a.store(s)
            }
            #[inline(always)]
            fn add(a: $m::V8, b: $m::V8) -> $m::V8 {
                a.add(b)
            }
            #[inline(always)]
            fn sub(a: $m::V8, b: $m::V8) -> $m::V8 {
                a.sub(b)
            }
            #[inline(always)]
            fn mul(a: $m::V8, b: $m::V8) -> $m::V8 {
                a.mul(b)
            }
            #[inline(always)]
            fn div(a: $m::V8, b: $m::V8) -> $m::V8 {
                a.div(b)
            }
            #[inline(always)]
            fn fma(a: $m::V8, b: $m::V8, c: $m::V8) -> $m::V8 {
                a.fma(b, c)
            }
            #[inline(always)]
            fn fms(a: $m::V8, b: $m::V8, c: $m::V8) -> $m::V8 {
                a.fms(b, c)
            }
            #[inline(always)]
            fn abs(a: $m::V8) -> $m::V8 {
                a.abs()
            }
            #[inline(always)]
            fn max(a: $m::V8, b: $m::V8) -> $m::V8 {
                a.max(b)
            }
            #[inline(always)]
            fn bcast(a: $m::V8, j: usize) -> $m::V8 {
                a.bcast(j)
            }
            #[inline(always)]
            fn sqrt(a: $m::V8) -> $m::V8 {
                a.sqrt()
            }
            #[inline(always)]
            fn pow2_floor(a: $m::V8) -> $m::V8 {
                a.pow2_floor()
            }
            #[inline(always)]
            fn ne(a: $m::V8, b: $m::V8) -> $m::M8 {
                a.ne(b)
            }
            #[inline(always)]
            fn eq(a: $m::V8, b: $m::V8) -> $m::M8 {
                a.eq(b)
            }
            #[inline(always)]
            fn gt(a: $m::V8, b: $m::V8) -> $m::M8 {
                a.gt(b)
            }
            #[inline(always)]
            fn ge(a: $m::V8, b: $m::V8) -> $m::M8 {
                a.ge(b)
            }
            #[inline(always)]
            fn and(m: $m::M8, n: $m::M8) -> $m::M8 {
                m.and(n)
            }
            #[inline(always)]
            fn or(m: $m::M8, n: $m::M8) -> $m::M8 {
                m.or(n)
            }
            #[inline(always)]
            fn not(m: $m::M8) -> $m::M8 {
                m.not()
            }
            #[inline(always)]
            fn sel(m: $m::M8, t: $m::V8, f: $m::V8) -> $m::V8 {
                m.sel(t, f)
            }
            #[inline(always)]
            fn bits(m: $m::M8) -> u8 {
                m.bits()
            }
            $($extra)*
            simd!(@vectorize $($feat)?);
            simd!(@hot $hot);
        }
    };
    (@hot always) => {
        #[inline(always)]
        fn hot<T>(f: impl FnOnce() -> T) -> T {
            f()
        }
    };
    (@hot hint) => {
        #[inline]
        fn hot<T>(f: impl FnOnce() -> T) -> T {
            f()
        }
    };
    (@vectorize) => {
        #[inline(always)]
        fn vectorize<T>(f: impl FnOnce() -> T) -> T {
            f()
        }
    };
    (@vectorize $feat:literal) => {
        #[inline(always)]
        fn vectorize<T>(f: impl FnOnce() -> T) -> T {
            #[target_feature(enable = $feat)]
            unsafe fn with<T>(f: impl FnOnce() -> T) -> T {
                f()
            }
            // SAFETY: the backend's type reaches code only through dispatch on a CPU that has these features, or as
            // Native, which the build already requires.
            unsafe { with(f) }
        }
    };
}

#[cfg(target_arch = "x86_64")]
simd!(backend::Avx512, avx512, always, "avx512f,avx2,fma" {
    type D = avx512::D;
    #[inline(always)]
    fn divisor(b: avx512::V8) -> avx512::D {
        b.divisor()
    }
    #[inline(always)]
    fn div_by(a: avx512::V8, d: avx512::D) -> avx512::V8 {
        a.div_by(d)
    }
    #[inline(always)]
    fn add_where(m: avx512::M8, a: avx512::V8, b: avx512::V8) -> avx512::V8 {
        a.add_where(m, b)
    }
    #[inline(always)]
    fn and_eq(m: avx512::M8, a: avx512::V8, b: avx512::V8) -> avx512::M8 {
        m.and_eq(a, b)
    }
    #[inline(always)]
    fn and_ne(m: avx512::M8, a: avx512::V8, b: avx512::V8) -> avx512::M8 {
        m.and_ne(a, b)
    }
});
#[cfg(target_arch = "x86_64")]
simd!(backend::Avx2, avx2, always, "avx2,fma");
#[cfg(all(any(target_arch = "x86", target_arch = "x86_64"), target_feature = "sse2"))]
simd!(backend::Sse2, sse2, hint);
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
simd!(backend::Neon, neon, hint);
simd!(backend::Portable, portable, hint);

/// 8 f64 lanes on the backend S.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct V8<S: Simd>(pub S::R);

/// 8-lane mask on the backend S.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct M8<S: Simd>(pub S::M);

/// A divisor for several divisions by it ([`V8::div_by`]), on AVX-512 with its reciprocal.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct Divisor<S: Simd>(pub S::D);

impl<S: Simd> V8<S> {
    pub const ISA: &'static str = S::NAME;
    #[inline(always)]
    pub fn splat(x: f64) -> Self {
        V8(S::splat(x))
    }
    #[inline(always)]
    pub fn zero() -> Self {
        V8(S::zero())
    }
    #[inline(always)]
    pub fn load(s: &[f64]) -> Self {
        V8(S::load(s))
    }
    #[inline(always)]
    pub fn store(self, s: &mut [f64]) {
        S::store(self.0, s)
    }
    #[inline(always)]
    pub fn add(self, o: Self) -> Self {
        V8(S::add(self.0, o.0))
    }
    #[inline(always)]
    pub fn sub(self, o: Self) -> Self {
        V8(S::sub(self.0, o.0))
    }
    #[inline(always)]
    pub fn mul(self, o: Self) -> Self {
        V8(S::mul(self.0, o.0))
    }
    #[inline(always)]
    pub fn div(self, o: Self) -> Self {
        V8(S::div(self.0, o.0))
    }
    /// self as a divisor, for several divisions by it
    #[inline(always)]
    pub fn divisor(self) -> Divisor<S> {
        Divisor(S::divisor(self.0))
    }
    /// self / b for d = b.divisor(), bitwise the same as `div`: on AVX-512 by b's reciprocal and one correction
    #[inline(always)]
    pub fn div_by(self, d: Divisor<S>) -> Self {
        V8(S::div_by(self.0, d.0))
    }
    /// self * b + c with one rounding
    #[inline(always)]
    pub fn fma(self, b: Self, c: Self) -> Self {
        V8(S::fma(self.0, b.0, c.0))
    }
    /// self * b - c with one rounding
    #[inline(always)]
    pub fn fms(self, b: Self, c: Self) -> Self {
        V8(S::fms(self.0, b.0, c.0))
    }
    /// self + o where m is set, self elsewhere
    #[inline(always)]
    pub fn add_where(self, m: M8<S>, o: Self) -> Self {
        V8(S::add_where(m.0, self.0, o.0))
    }
    #[inline(always)]
    pub fn abs(self) -> Self {
        V8(S::abs(self.0))
    }
    #[inline(always)]
    pub fn max(self, o: Self) -> Self {
        V8(S::max(self.0, o.0))
    }
    /// all lanes = lane j
    #[inline(always)]
    pub fn bcast(self, j: usize) -> Self {
        V8(S::bcast(self.0, j))
    }
    #[inline(always)]
    pub fn sqrt(self) -> Self {
        V8(S::sqrt(self.0))
    }
    /// the exponent bits only: 2^floor(log2 |x|) for normal x
    #[inline(always)]
    pub fn pow2_floor(self) -> Self {
        V8(S::pow2_floor(self.0))
    }
    /// self != o (true when either is NaN, as C's !=)
    #[inline(always)]
    pub fn ne(self, o: Self) -> M8<S> {
        M8(S::ne(self.0, o.0))
    }
    /// self == o (false when either is NaN)
    #[inline(always)]
    pub fn eq(self, o: Self) -> M8<S> {
        M8(S::eq(self.0, o.0))
    }
    /// self > o (false when either is NaN)
    #[inline(always)]
    pub fn gt(self, o: Self) -> M8<S> {
        M8(S::gt(self.0, o.0))
    }
    /// self >= o (false when either is NaN)
    #[inline(always)]
    pub fn ge(self, o: Self) -> M8<S> {
        M8(S::ge(self.0, o.0))
    }
    #[inline(always)]
    pub fn to_array(self) -> [f64; 8] {
        let mut a = [0.0; 8];
        self.store(&mut a);
        a
    }
    #[inline(always)]
    pub fn from_array(a: [f64; 8]) -> Self {
        Self::load(&a)
    }
    #[inline(always)]
    pub fn hmax(self) -> f64 {
        self.to_array().iter().fold(f64::NEG_INFINITY, |m, &v| m.max(v))
    }
}

impl<S: Simd> M8<S> {
    #[inline(always)]
    pub fn and(self, o: Self) -> Self {
        M8(S::and(self.0, o.0))
    }
    #[inline(always)]
    pub fn or(self, o: Self) -> Self {
        M8(S::or(self.0, o.0))
    }
    #[inline(always)]
    pub fn not(self) -> Self {
        M8(S::not(self.0))
    }
    /// self and a == b
    #[inline(always)]
    pub fn and_eq(self, a: V8<S>, b: V8<S>) -> Self {
        M8(S::and_eq(self.0, a.0, b.0))
    }
    /// self and a != b
    #[inline(always)]
    pub fn and_ne(self, a: V8<S>, b: V8<S>) -> Self {
        M8(S::and_ne(self.0, a.0, b.0))
    }
    /// per lane: t where set, f elsewhere
    #[inline(always)]
    pub fn sel(self, t: V8<S>, f: V8<S>) -> V8<S> {
        V8(S::sel(self.0, t.0, f.0))
    }
    /// bit j = lane j
    #[inline(always)]
    pub fn bits(self) -> u8 {
        S::bits(self.0)
    }
}

// ---------------------------------------------------------------------------------------------------------------
// The NEON backend checked off ARM: a pure-Rust model of the intrinsics it uses (same names and signatures, the
// architecture's semantics: FMLA fused, FMAX's NaN and signed-zero rules, all-ones/all-zeros compare masks), the
// backend's body compiled against it, and every operation compared bit for bit with the scalar f64 one.
// ---------------------------------------------------------------------------------------------------------------

#[cfg(all(test, not(target_arch = "aarch64")))]
#[allow(non_camel_case_types, clippy::missing_safety_doc)]
mod neon_model {
    #[derive(Clone, Copy, Debug)]
    pub struct float64x2_t(pub [f64; 2]);
    #[derive(Clone, Copy, Debug)]
    pub struct uint64x2_t(pub [u64; 2]);

    fn f1(a: float64x2_t, f: impl Fn(f64) -> f64) -> float64x2_t {
        float64x2_t([f(a.0[0]), f(a.0[1])])
    }
    fn f2(a: float64x2_t, b: float64x2_t, f: impl Fn(f64, f64) -> f64) -> float64x2_t {
        float64x2_t([f(a.0[0], b.0[0]), f(a.0[1], b.0[1])])
    }
    fn u2(a: uint64x2_t, b: uint64x2_t, f: impl Fn(u64, u64) -> u64) -> uint64x2_t {
        uint64x2_t([f(a.0[0], b.0[0]), f(a.0[1], b.0[1])])
    }
    fn cmp(a: float64x2_t, b: float64x2_t, f: impl Fn(f64, f64) -> bool) -> uint64x2_t {
        uint64x2_t([
            if f(a.0[0], b.0[0]) { u64::MAX } else { 0 },
            if f(a.0[1], b.0[1]) { u64::MAX } else { 0 },
        ])
    }

    pub fn vdupq_n_f64(x: f64) -> float64x2_t {
        float64x2_t([x, x])
    }
    pub fn vdupq_n_u64(x: u64) -> uint64x2_t {
        uint64x2_t([x, x])
    }
    pub unsafe fn vld1q_f64(p: *const f64) -> float64x2_t {
        unsafe { float64x2_t([*p, *p.add(1)]) }
    }
    pub unsafe fn vst1q_f64(p: *mut f64, a: float64x2_t) {
        unsafe {
            *p = a.0[0];
            *p.add(1) = a.0[1];
        }
    }
    pub fn vaddq_f64(a: float64x2_t, b: float64x2_t) -> float64x2_t {
        f2(a, b, |x, y| x + y)
    }
    pub fn vsubq_f64(a: float64x2_t, b: float64x2_t) -> float64x2_t {
        f2(a, b, |x, y| x - y)
    }
    pub fn vmulq_f64(a: float64x2_t, b: float64x2_t) -> float64x2_t {
        f2(a, b, |x, y| x * y)
    }
    pub fn vdivq_f64(a: float64x2_t, b: float64x2_t) -> float64x2_t {
        f2(a, b, |x, y| x / y)
    }
    /// a + b c, fused
    pub fn vfmaq_f64(a: float64x2_t, b: float64x2_t, c: float64x2_t) -> float64x2_t {
        float64x2_t([b.0[0].mul_add(c.0[0], a.0[0]), b.0[1].mul_add(c.0[1], a.0[1])])
    }
    pub fn vnegq_f64(a: float64x2_t) -> float64x2_t {
        f1(a, |x| -x)
    }
    pub fn vabsq_f64(a: float64x2_t) -> float64x2_t {
        f1(a, f64::abs)
    }
    pub fn vsqrtq_f64(a: float64x2_t) -> float64x2_t {
        f1(a, f64::sqrt)
    }
    /// FMAX: NaN if either is NaN; +0 is larger than -0
    pub fn vmaxq_f64(a: float64x2_t, b: float64x2_t) -> float64x2_t {
        f2(a, b, |x, y| {
            if x.is_nan() || y.is_nan() {
                f64::NAN
            } else if x == y {
                if x.is_sign_positive() {
                    x
                } else {
                    y
                }
            } else if x > y {
                x
            } else {
                y
            }
        })
    }
    pub fn vreinterpretq_u64_f64(a: float64x2_t) -> uint64x2_t {
        uint64x2_t([a.0[0].to_bits(), a.0[1].to_bits()])
    }
    pub fn vreinterpretq_f64_u64(a: uint64x2_t) -> float64x2_t {
        float64x2_t([f64::from_bits(a.0[0]), f64::from_bits(a.0[1])])
    }
    pub fn vandq_u64(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
        u2(a, b, |x, y| x & y)
    }
    pub fn vorrq_u64(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
        u2(a, b, |x, y| x | y)
    }
    pub fn veorq_u64(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
        u2(a, b, |x, y| x ^ y)
    }
    pub fn vceqq_f64(a: float64x2_t, b: float64x2_t) -> uint64x2_t {
        cmp(a, b, |x, y| x == y)
    }
    pub fn vcgtq_f64(a: float64x2_t, b: float64x2_t) -> uint64x2_t {
        cmp(a, b, |x, y| x > y)
    }
    pub fn vcgeq_f64(a: float64x2_t, b: float64x2_t) -> uint64x2_t {
        cmp(a, b, |x, y| x >= y)
    }
    /// bitwise select: b where the mask bit is set, c elsewhere
    pub fn vbslq_f64(m: uint64x2_t, b: float64x2_t, c: float64x2_t) -> float64x2_t {
        let (b, c) = (vreinterpretq_u64_f64(b), vreinterpretq_u64_f64(c));
        vreinterpretq_f64_u64(uint64x2_t([
            (m.0[0] & b.0[0]) | (!m.0[0] & c.0[0]),
            (m.0[1] & b.0[1]) | (!m.0[1] & c.0[1]),
        ]))
    }
    pub fn vgetq_lane_u64<const LANE: i32>(v: uint64x2_t) -> u64 {
        v.0[LANE as usize]
    }
}

#[cfg(all(test, not(target_arch = "aarch64")))]
mod neon_check {
    use super::neon_model::*;
    include!("v8_neon.rs");

    fn same(a: f64, b: f64) -> bool {
        a.to_bits() == b.to_bits()
    }

    #[test]
    fn neon_backend_matches_scalar() {
        let mut s = 0x0123_4567_89ab_cdefu64;
        let mut next = move || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            let m = 1.0 + (s >> 11) as f64 / (1u64 << 53) as f64;
            let e = ((s >> 3) % 81) as i32 - 40;
            m * 2f64.powi(e) * if s & 1 == 0 { 1.0 } else { -1.0 }
        };
        for _ in 0..20_000 {
            let a: [f64; 8] = std::array::from_fn(|_| next());
            let b: [f64; 8] = std::array::from_fn(|j| if j == 5 { a[5] } else { next() });
            let c: [f64; 8] = std::array::from_fn(|_| next());
            let (va, vb, vc) = (V8::load(&a), V8::load(&b), V8::load(&c));
            let mut out = [0.0; 8];
            let checks: [(V8, &dyn Fn(usize) -> f64); 10] = [
                (va.add(vb), &|j| a[j] + b[j]),
                (va.sub(vb), &|j| a[j] - b[j]),
                (va.mul(vb), &|j| a[j] * b[j]),
                (va.div(vb), &|j| a[j] / b[j]),
                (va.fma(vb, vc), &|j| a[j].mul_add(b[j], c[j])),
                (va.fms(vb, vc), &|j| a[j].mul_add(b[j], -c[j])),
                (va.abs(), &|j| a[j].abs()),
                (va.abs().sqrt(), &|j| a[j].abs().sqrt()),
                (va.max(vb), &|j| a[j].max(b[j])),
                (va.pow2_floor(), &|j| {
                    f64::from_bits(a[j].to_bits() & 0x7ff0_0000_0000_0000)
                }),
            ];
            for (k, (v, f)) in checks.iter().enumerate() {
                v.store(&mut out);
                for j in 0..8 {
                    assert!(same(out[j], f(j)), "op {k} lane {j}: {} vs {}", out[j], f(j));
                }
            }
            let want = |f: &dyn Fn(f64, f64) -> bool| (0..8).fold(0u8, |m, j| m | (f(a[j], b[j]) as u8) << j);
            assert_eq!(va.eq(vb).bits(), want(&|x, y| x == y));
            assert_eq!(va.ne(vb).bits(), want(&|x, y| x != y));
            assert_eq!(va.gt(vb).bits(), want(&|x, y| x > y));
            assert_eq!(va.ge(vb).bits(), want(&|x, y| x >= y));
            let (m1, m2) = (va.gt(vb), vb.ge(vc));
            assert_eq!(m1.and(m2).bits(), m1.bits() & m2.bits());
            assert_eq!(m1.or(m2).bits(), m1.bits() | m2.bits());
            assert_eq!(m1.not().bits(), !m1.bits());
            m1.sel(va, vb).store(&mut out);
            for j in 0..8 {
                assert!(same(out[j], if m1.bits() >> j & 1 == 1 { a[j] } else { b[j] }));
            }
            va.bcast(6).store(&mut out);
            assert!(out.iter().all(|&x| same(x, a[6])));
            V8::zero().store(&mut out);
            assert!(out.iter().all(|&x| same(x, 0.0)));
            assert_eq!(V8::ISA, "neon");
        }
    }

    /// Control: a model whose fused multiply-add rounds twice is caught by the same comparison.
    #[test]
    fn control_unfused_fma_is_caught() {
        let a = 1.0 + 2f64.powi(-30);
        let b = 1.0 - 2f64.powi(-30);
        let c = -1.0;
        // a b = 1 - 2^-60: rounded first to 1, then minus 1 gives 0; fused it gives -2^-60
        assert!(!same(a * b + c, a.mul_add(b, c)));
        let v = V8::splat(a).fma(V8::splat(b), V8::splat(c));
        let mut out = [0.0; 8];
        v.store(&mut out);
        assert!(same(out[0], a.mul_add(b, c)) && !same(out[0], a * b + c));
    }
}
