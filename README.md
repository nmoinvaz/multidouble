# multidouble

[![Build](https://github.com/nmoinvaz/multidouble/actions/workflows/build.yml/badge.svg)](https://github.com/nmoinvaz/multidouble/actions/workflows/build.yml)
[![Lint](https://github.com/nmoinvaz/multidouble/actions/workflows/lint.yml/badge.svg)](https://github.com/nmoinvaz/multidouble/actions/workflows/lint.yml)
[![codecov](https://codecov.io/gh/nmoinvaz/multidouble/graph/badge.svg)](https://codecov.io/gh/nmoinvaz/multidouble)

Double-double and quad-double floating-point arithmetic for Rust, scalar and on 8-lane SIMD vectors, with **bitwise the
same results on AVX-512, AVX2, SSE2, NEON and portable builds**. It also has forward-mode dual numbers over these lanes and a dense
LU factorization in double-double.

A double-double is an unevaluated sum `hi + lo` of two `f64`, about 32 significant digits. A quad-double is a sum of four,
about 64 digits. Both are built from error-free transformations (two-sum, FMA two-product), so they run at hardware
speed, with no allocation and no arbitrary-precision library.

| Type | What it is |
|---|---|
| `v8::V8` | 8 `f64` in one AVX-512 register, two AVX2 registers, four SSE2 or NEON registers, or a plain array, with fused multiply-add throughout |
| `dd::DD`, `dv::DV` | double-double, scalar and 8-lane; `dv::DotAcc` accumulates sums of products |
| `qd::QD`, `qv::QV` | quad-double, scalar and 8-lane; exact decimal parsing and printing; `QdAcc`, `QDotAcc` accumulators |
| `dual::Du`, `dual::Dtn<N>`, `dual::Fu`, `dual::Fun<N>` | forward-mode dual lanes: a double-double value with a double-double tangent or N f64 tangents, and f64 versions, behind the `dual::Lane` trait |
| `linalg::DDLu` | dense LU with partial pivoting in double-double (and blocked in f64 for mixed precision), solves, transpose solves, many right-hand sides, Gram matrices |
| `exact` | exact dyadic and decimal arithmetic, the reference the tests compare against |

## Usage

```rust
use multidouble::dd::DD;
use multidouble::dv::DV;
use multidouble::qd::QD;

// double-double: about 32 digits
let third = DD::from_f64(1.0) / DD::from_f64(3.0);

// quad-double: about 64 digits, with exact decimal input and output
let sqrt2: QD = "1.414213562373095048801688724209698078569671875376948073176679737990732478"
    .parse()
    .unwrap();
println!("{}", (sqrt2 * sqrt2).to_sci(64));

// 8 double-double values at once, each lane bitwise equal to the scalar result
let x = DV::load(&[1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0], &[0.0; 8]);
let y = x * x + DV::splat(third);
assert_eq!(y.lane(2), DD::from_f64(9.0) + third);
```

The SIMD backend is chosen at compile time by the target and its enabled features:

| Backend | When | Registers |
|---|---|---|
| `avx512` | x86-64 with AVX-512F enabled (`RUSTFLAGS="-C target-cpu=native"` on such a CPU) | one zmm |
| `avx2` | x86-64 with AVX2 and FMA enabled (`-C target-feature=+avx2,+fma`) | two ymm |
| `sse2` | x86 and x86-64 otherwise; SSE2 has no fused multiply-add, so that one operation runs per lane through `f64::mul_add` | four xmm |
| `neon` | aarch64 | four NEON |
| `portable` | every other target, or any target with the cargo feature `portable` | a plain array |

`V8::ISA` reports which one was compiled in. Results are the same on every backend; only the speed changes.

The cargo feature `f128` adds conversions between `f128` and the scalar types. It needs nightly Rust, as `f128` is
unstable. `QD::from_f128` is exact, `DD::from_f128` rounds to the nearest parts, and both `to_f128` are correctly
rounded.

## Accuracy

The tests compare against exact arithmetic (`exact`), which shares no code with the algorithms under test. Errors are
relative to the exact result. Here u = 2⁻⁵³, so u² = 2⁻¹⁰⁶ is the double-double unit.

| Operation | Bound checked | Worst seen (20,000 random inputs) |
|---|---|---|
| double-double add, subtract (including near-cancelling pairs) | 3 u² (Joldes, Muller and Popescu, 2017) | 1.66 u² |
| double-double multiply | 5 u² | 3.12 u² |
| double-double divide (residual of the quotient) | 8 u² | 1.54 u² |
| two-sum, quick-two-sum, two-product | exact | exact |

For the quad-double types, the tests check every operation against exact arithmetic. They also check the scalar and 8-lane
results bit for bit, and decimal input and output round trips. Against exact arithmetic the quad-double operations err by
at most 2.1×2⁻²⁰⁹, about 63 digits. They use the algorithms of the QD library (Hida, Li and Bailey, ARITH-15, 2001), with
two repairs found by these tests:

- **The accurate add.** It lost a term when all parts are read with three emitted.
- **The square root.** It lost accuracy far from 1. It now scales its argument by a power of four first.

Quad-double costs 8–29 times double-double per operation, and 14–17 times in sums of products.

Every check can fail. Two kinds of controls show it:

- **Built-in breakage.** The feature `mutate` breaks the quad-double algorithms one at a time on purpose, and
  `cargo test --release --features mutate` checks that each breakage fails a test.
- **Hand-written controls.** The integration tests contain controls that feed deliberately wrong results to the same
  checks: a double-double add without its low parts, a wrong derivative, a perturbed LU factor, and f128 conversions
  that round twice.

## Testing, coverage and benchmarks

```sh
cargo test --release                                            # SSE2 on x86, NEON on aarch64
cargo test --release --features portable                        # the plain-array backend
RUSTFLAGS="-C target-feature=+avx2,+fma" cargo test --release   # AVX2
RUSTFLAGS="-C target-cpu=native" cargo test --release           # AVX-512 where the CPU has it
cargo test --release --features mutate                          # the mutation controls
cargo +nightly test --release --features f128                   # the f128 conversions
cargo llvm-cov --release --features mutate                      # coverage (cargo-llvm-cov)
cargo bench --bench arith                                       # scalar against lanes; f64, double-double, quad-double
cargo bench --bench linalg                                      # double-double LU against f64 LU
```

`tests/lanes.rs` checks that `V8`, `DV` and `QV` match the scalar types bit for bit. The NEON backend's code is also
compiled on x86 against a pure-Rust model of its intrinsics and checked there (`v8::neon_check`), so it is tested on
every runner, not only on ARM. CI runs the whole suite on:

- the portable, SSE2, AVX2, AVX-512 and NEON backends;
- Linux on x86-64, ARM64, ARMv7, PPC64LE, RISC-V 64 and S390X (big-endian);
- macOS on ARM64;
- Windows on x64 and x86;
- nightly Rust with the feature `f128`, on x86-64 and ARM64 Linux.

It also runs coverage, clippy on each backend, and a library check at the minimum Rust version.

The minimum Rust version is 1.89, where the AVX-512 intrinsics became stable.

## Origin

This code was written for a double-double solver of Choptuik's critical collapse in D dimensions
([choptuik-large-d](https://github.com/nmoinvaz/choptuik-large-d)). That solver needs about 30 digits and an exact
Jacobian at the speed of SIMD f64 code.

## License

[BSD 3-Clause](LICENSE), the license of the QD library whose quad-double algorithms `src/qd.rs` and `src/qv.rs`
follow. QD's own notice is kept in [LICENSE-QD](LICENSE-QD).
