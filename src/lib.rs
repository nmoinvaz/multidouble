//! Double-double and quad-double floating-point arithmetic, scalar and on 8-lane SIMD vectors.
//!
//! A double-double is an unevaluated sum `hi + lo` of two `f64` (about 32 significant digits); a quad-double is a sum
//! of four (about 64 digits). The lane types run the same algorithms on 8 values at once, with **bitwise the same
//! results per lane** as the scalar types, on every backend:
//!
//! * [`v8::V8`]: 8 `f64` in one AVX-512 register, two AVX2 registers, four SSE2 or four NEON registers, or a plain
//!   array, chosen at compile time by the enabled target features (e.g. `RUSTFLAGS="-C target-cpu=native"`; the
//!   cargo feature `portable` forces the plain array), with fused multiply-add throughout.
//! * [`dd::DD`] scalar and [`dv::DV`] 8-lane double-double; [`dv::DotAcc`] a sum-of-products accumulator.
//! * [`qd::QD`] scalar and [`qv::QV`] 8-lane quad-double (the algorithms of Hida, Li and Bailey's QD library, with two
//!   repairs found by this crate's tests), exact decimal parsing and printing;
//!   [`qd::QdAcc`] and [`qv::QDotAcc`] accumulators.
//! * [`exact`]: exact dyadic and decimal arithmetic, the reference the tests compare against.
//! * [`dual`]: forward-mode dual numbers over these lanes ([`dual::Du`] double-double value and tangent,
//!   [`dual::Dtn`] a double-double value with N f64 tangents, and f64 variants), behind the [`dual::Lane`] trait, so
//!   one generic code gives values and exact derivatives.
//! * [`linalg`]: dense LU with partial pivoting in double-double (and blocked in f64 for mixed precision), solves,
//!   transpose solves and Gram matrices.
//!
//! All operations are IEEE round-to-nearest with no reassociation, which the error-free transformations need.
//!
//! The cargo feature `f128` adds conversions between `f128` and [`dd::DD`] and [`qd::QD`]. It needs a nightly
//! compiler, as `f128` is unstable.
//!
//! ```
//! use multidouble::dd::DD;
//! use multidouble::qd::QD;
//!
//! let third = DD::from_f64(1.0) / DD::from_f64(3.0);
//! assert!(((third * DD::from_f64(3.0)) - DD::from_f64(1.0)).to_f64().abs() < 1e-31);
//!
//! let x: QD = "1.41421356237309504880168872420969807856967187537694807317667973799".parse().unwrap();
//! assert!((x * x - QD::from_f64(2.0)).to_f64().abs() < 1e-62);
//! ```
// Numerical kernels index several arrays with one loop variable, and the lane and accumulator types keep inherent
// add/sub/mul/div methods (the std::ops traits are implemented where they apply).
#![allow(clippy::needless_range_loop, clippy::should_implement_trait)]
#![cfg_attr(feature = "f128", feature(f128))]

pub mod dd;
pub mod dual;
pub mod dv;
pub mod exact;
pub mod linalg;
pub mod qd;
pub mod qv;
pub mod simd;
pub mod v8;

/// The lane types on the compile-time backend [`simd::Native`], for code that does not dispatch.
pub mod native {
    use crate::simd::Native;
    pub type V8 = crate::v8::V8<Native>;
    pub type M8 = crate::v8::M8<Native>;
    pub type DV = crate::dv::DV<Native>;
    pub type DotAcc = crate::dv::DotAcc<Native>;
}

#[cfg(test)]
mod qd_tests;

/// The README's examples, compiled and run as doctests.
#[doc = include_str!("../README.md")]
#[cfg(doctest)]
pub struct ReadmeDoctests;
