//! 8-lane f64 vector. With AVX-512F enabled at compile time (`-C target-cpu=native` on such a CPU) it is one zmm
//! register and every operation is one intrinsic; with AVX2 + FMA it is two ymm registers; otherwise a plain array
//! (`f64::mul_add` for the fused operations, which the double-double algorithms need to be exact).
//!
//! All operations are IEEE round-to-nearest with no reassociation, as the error-free transformations in `dv`
//! require. `M8` is an 8-lane mask (a `__mmask8`, two all-ones/all-zeros ymm registers, or a bit set) from the
//! comparisons `ne`, `eq`, `gt`, `ge`, with per-lane select `sel`: the quad-double lanes (`qv`) run QD's data-dependent
//! branches with them.

#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
mod imp {
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
    }

    /// 8-lane mask (one bit per lane).
    #[derive(Clone, Copy, Debug)]
    pub struct M8(pub __mmask8);

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
            unsafe { V8(_mm512_mask_blend_pd(self.0, f.0, t.0)) }
        }
        /// bit j = lane j
        #[inline(always)]
        pub fn bits(self) -> u8 {
            self.0
        }
    }
}

#[cfg(all(
    target_arch = "x86_64",
    not(target_feature = "avx512f"),
    target_feature = "avx2",
    target_feature = "fma"
))]
mod imp {
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

#[cfg(not(any(
    all(target_arch = "x86_64", target_feature = "avx512f"),
    all(target_arch = "x86_64", target_feature = "avx2", target_feature = "fma")
)))]
mod imp {
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

pub use imp::{M8, V8};

impl V8 {
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
