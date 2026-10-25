//! Runtime choice of the 8-lane backend.
//!
//! The lane types ([`crate::v8::V8`], [`crate::dv::DV`], [`crate::qv::QV`], the dual lanes) are generic over an
//! instruction set `S: Simd`. Code written once over `S` runs on the best one the CPU has through [`dispatch`]:
//! AVX-512F (with AVX2 and FMA), then AVX2 + FMA, then SSE2 on x86-64, NEON on aarch64, a plain array elsewhere.
//! Every backend gives bitwise the same results, so the choice changes only the speed.
//!
//! [`Native`] is the backend the build's target features select at compile time, the one the aliases in
//! [`crate::native`] use. The others can be named only inside [`Kernel::run`], which [`dispatch`] and
//! [`for_each_available`] call only with a backend this CPU supports.
use std::fmt::Debug;
use std::sync::atomic::{AtomicU8, Ordering};

pub(crate) mod sealed {
    pub trait Sealed {}
}

/// An instruction set for 8 f64 lanes: the register types and their operations, which [`crate::v8::V8`] and
/// [`crate::v8::M8`] wrap. Sealed.
pub trait Simd: Copy + Send + Sync + Debug + 'static + sealed::Sealed {
    /// avx512, avx2, sse2, neon or portable
    const NAME: &'static str;
    /// 8 f64 lanes
    type R: Copy + Send + Sync + Debug;
    /// an 8-lane mask
    type M: Copy + Send + Sync + Debug;
    fn splat(x: f64) -> Self::R;
    fn zero() -> Self::R;
    fn load(s: &[f64]) -> Self::R;
    fn store(a: Self::R, s: &mut [f64]);
    fn add(a: Self::R, b: Self::R) -> Self::R;
    fn sub(a: Self::R, b: Self::R) -> Self::R;
    fn mul(a: Self::R, b: Self::R) -> Self::R;
    fn div(a: Self::R, b: Self::R) -> Self::R;
    /// a divisor prepared for several divisions by it ([`Simd::div_by`])
    type D: Copy + Send + Sync + Debug;
    /// b as a divisor, on AVX-512 with its reciprocal and elsewhere b itself
    fn divisor(b: Self::R) -> Self::D;
    /// a / b for d = divisor(b), bitwise the same as `div`
    fn div_by(a: Self::R, d: Self::D) -> Self::R;
    /// a b + c with one rounding
    fn fma(a: Self::R, b: Self::R, c: Self::R) -> Self::R;
    /// a b - c with one rounding
    fn fms(a: Self::R, b: Self::R, c: Self::R) -> Self::R;
    /// -a: the sign bit flipped, so -(+0) = -0 as for f64 (0 - a would give +0)
    fn neg(a: Self::R) -> Self::R;
    fn abs(a: Self::R) -> Self::R;
    fn max(a: Self::R, b: Self::R) -> Self::R;
    /// all lanes = lane j
    fn bcast(a: Self::R, j: usize) -> Self::R;
    fn sqrt(a: Self::R) -> Self::R;
    /// the exponent bits only: 2^floor(log2 |x|) for normal x
    fn pow2_floor(a: Self::R) -> Self::R;
    fn ne(a: Self::R, b: Self::R) -> Self::M;
    fn eq(a: Self::R, b: Self::R) -> Self::M;
    fn gt(a: Self::R, b: Self::R) -> Self::M;
    fn ge(a: Self::R, b: Self::R) -> Self::M;
    fn and(m: Self::M, n: Self::M) -> Self::M;
    fn or(m: Self::M, n: Self::M) -> Self::M;
    fn not(m: Self::M) -> Self::M;
    /// per lane: t where set, f elsewhere
    fn sel(m: Self::M, t: Self::R, f: Self::R) -> Self::R;
    /// per lane: a + b where m is set, a elsewhere (one masked add on AVX-512)
    #[inline(always)]
    fn add_where(m: Self::M, a: Self::R, b: Self::R) -> Self::R {
        Self::sel(m, Self::add(a, b), a)
    }
    /// m and a == b (one masked compare on AVX-512)
    #[inline(always)]
    fn and_eq(m: Self::M, a: Self::R, b: Self::R) -> Self::M {
        Self::and(m, Self::eq(a, b))
    }
    /// m and a != b
    #[inline(always)]
    fn and_ne(m: Self::M, a: Self::R, b: Self::R) -> Self::M {
        Self::and(m, Self::ne(a, b))
    }
    /// bit j = lane j
    fn bits(m: Self::M) -> u8;
    /// f run with this instruction set enabled. f should be an `#[inline(always)]` closure, so that its body is
    /// compiled inside, where the backend's instructions inline.
    fn vectorize<T>(f: impl FnOnce() -> T) -> T;
    /// f, an `#[inline(always)]` closure, inlined into the caller on AVX2 and AVX-512 and left to the compiler on
    /// the other backends: for the large hot operations of `qv`. Forced inlining of those on the plain array made the
    /// test build exceed 3 GB of memory and 17 minutes.
    fn hot<T>(f: impl FnOnce() -> T) -> T;
}

/// The backends, one zero-sized type each. Not exported, so that outside the crate only [`Native`] can be named.
pub(crate) mod backend {
    #[cfg(target_arch = "x86_64")]
    #[derive(Clone, Copy, Debug)]
    pub struct Avx512;
    #[cfg(target_arch = "x86_64")]
    #[derive(Clone, Copy, Debug)]
    pub struct Avx2;
    #[cfg(all(any(target_arch = "x86", target_arch = "x86_64"), target_feature = "sse2"))]
    #[derive(Clone, Copy, Debug)]
    pub struct Sse2;
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    #[derive(Clone, Copy, Debug)]
    pub struct Neon;
    #[derive(Clone, Copy, Debug)]
    pub struct Portable;
}

/// The backend the build's target features select at compile time (the cargo feature `portable` forces the plain
/// array).
#[cfg(all(not(feature = "portable"), target_arch = "x86_64", target_feature = "avx512f"))]
pub type Native = backend::Avx512;
/// The backend the build's target features select at compile time (the cargo feature `portable` forces the plain
/// array).
#[cfg(all(
    not(feature = "portable"),
    target_arch = "x86_64",
    not(target_feature = "avx512f"),
    target_feature = "avx2",
    target_feature = "fma"
))]
pub type Native = backend::Avx2;
/// The backend the build's target features select at compile time (the cargo feature `portable` forces the plain
/// array).
#[cfg(all(
    not(feature = "portable"),
    any(target_arch = "x86", target_arch = "x86_64"),
    target_feature = "sse2",
    not(all(target_arch = "x86_64", target_feature = "avx512f")),
    not(all(target_arch = "x86_64", target_feature = "avx2", target_feature = "fma"))
))]
pub type Native = backend::Sse2;
/// The backend the build's target features select at compile time (the cargo feature `portable` forces the plain
/// array).
#[cfg(all(not(feature = "portable"), target_arch = "aarch64", target_feature = "neon"))]
pub type Native = backend::Neon;
/// The backend the build's target features select at compile time (the cargo feature `portable` forces the plain
/// array).
#[cfg(any(
    feature = "portable",
    not(any(
        all(any(target_arch = "x86", target_arch = "x86_64"), target_feature = "sse2"),
        all(target_arch = "aarch64", target_feature = "neon")
    ))
))]
pub type Native = backend::Portable;

/// Code generic over the backend, run by [`dispatch`] on the best one the CPU has.
///
/// `run` should be `#[inline(always)]`: it is then compiled inside the backend's [`Simd::vectorize`], where its lane
/// operations become the backend's instructions. Closures it hands to other threads (rayon) leave that context and
/// should enter it again with `S::vectorize(#[inline(always)] || ...)`.
///
/// Loops over lanes in `run` should be plain `for` loops. An iterator adapter that takes the loop body as a closure,
/// such as `fold` or `for_each`, runs it inside a std function. The compiler may keep that function out of line,
/// compiled without the backend's target features, and every lane operation in it is then a call (27 times slower
/// for `QV` addition on AVX2).
pub trait Kernel {
    type Output;
    fn run<S: Simd>(self) -> Self::Output;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
enum Level {
    Portable = 1,
    Sse2,
    Neon,
    Avx2,
    Avx512,
}

impl Level {
    fn name(self) -> &'static str {
        match self {
            Level::Portable => "portable",
            Level::Sse2 => "sse2",
            Level::Neon => "neon",
            Level::Avx2 => "avx2",
            Level::Avx512 => "avx512",
        }
    }
}

/// the backends this CPU runs, best first
fn levels() -> Vec<Level> {
    [Level::Avx512, Level::Avx2, Level::Sse2, Level::Neon, Level::Portable]
        .into_iter()
        .filter(|&l| runs(l))
        .collect()
}

/// whether the build has backend l and this CPU runs it (the feature `portable` keeps only the plain array)
fn runs(l: Level) -> bool {
    if cfg!(feature = "portable") {
        return l == Level::Portable;
    }
    match l {
        #[cfg(target_arch = "x86_64")]
        // every feature the backend's `vectorize` enables: a hypervisor can mask AVX2 or FMA under AVX-512F
        Level::Avx512 => {
            std::arch::is_x86_feature_detected!("avx512f")
                && std::arch::is_x86_feature_detected!("avx2")
                && std::arch::is_x86_feature_detected!("fma")
        }
        #[cfg(target_arch = "x86_64")]
        Level::Avx2 => std::arch::is_x86_feature_detected!("avx2") && std::arch::is_x86_feature_detected!("fma"),
        Level::Sse2 => cfg!(all(
            any(target_arch = "x86", target_arch = "x86_64"),
            target_feature = "sse2"
        )),
        Level::Neon => cfg!(all(target_arch = "aarch64", target_feature = "neon")),
        Level::Portable => true,
        #[allow(unreachable_patterns)]
        _ => false,
    }
}

/// 0 until the first dispatch, then the best `Level`
static BEST: AtomicU8 = AtomicU8::new(0);

/// the best backend this CPU has, detected on the first call
fn best() -> Level {
    let all = [Level::Portable, Level::Sse2, Level::Neon, Level::Avx2, Level::Avx512];
    if let Some(&l) = all.iter().find(|l| **l as u8 == BEST.load(Ordering::Relaxed)) {
        return l;
    }
    let l = levels()[0];
    BEST.store(l as u8, Ordering::Relaxed);
    l
}

#[inline(always)]
fn run<S: Simd, K: Kernel>(k: K) -> K::Output {
    S::vectorize(
        #[inline(always)]
        || k.run::<S>(),
    )
}

fn run_on<K: Kernel>(l: Level, k: K) -> K::Output {
    match l {
        #[cfg(target_arch = "x86_64")]
        Level::Avx512 => run::<backend::Avx512, K>(k),
        #[cfg(target_arch = "x86_64")]
        Level::Avx2 => run::<backend::Avx2, K>(k),
        #[cfg(all(any(target_arch = "x86", target_arch = "x86_64"), target_feature = "sse2"))]
        Level::Sse2 => run::<backend::Sse2, K>(k),
        #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
        Level::Neon => run::<backend::Neon, K>(k),
        Level::Portable => run::<backend::Portable, K>(k),
        #[allow(unreachable_patterns)]
        _ => unreachable!("backend {} not built for this target", l.name()),
    }
}

/// k run on the best backend this CPU has, detected once.
pub fn dispatch<K: Kernel>(k: K) -> K::Output {
    run_on(best(), k)
}

/// k run on every backend this CPU has, best first, each result with the backend's name: for checks that the
/// backends agree.
pub fn for_each_available<K: Kernel + Clone>(k: K) -> Vec<(&'static str, K::Output)> {
    levels().into_iter().map(|l| (l.name(), run_on(l, k.clone()))).collect()
}

/// the name of the backend [`dispatch`] runs on
pub fn isa() -> &'static str {
    best().name()
}

/// the names of the backends this CPU has, best first
pub fn available() -> Vec<&'static str> {
    levels().into_iter().map(Level::name).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone)]
    struct Name;

    impl Kernel for Name {
        type Output = &'static str;
        #[inline(always)]
        fn run<S: Simd>(self) -> &'static str {
            S::NAME
        }
    }

    #[test]
    fn dispatch_runs_the_backends_it_names() {
        assert_eq!(dispatch(Name), isa());
        let ran = for_each_available(Name);
        assert_eq!(ran.iter().map(|r| r.0).collect::<Vec<_>>(), available());
        assert!(ran.iter().all(|(name, ran_on)| name == ran_on));
        assert_eq!(ran.last().map(|r| r.0), Some("portable"));
        assert!(available().contains(&Native::NAME));
        println!("simd: {} of {:?}, native {}", isa(), available(), Native::NAME);
    }
}
