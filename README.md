# multidouble

[![Build](https://github.com/nmoinvaz/multidouble/actions/workflows/build.yml/badge.svg)](https://github.com/nmoinvaz/multidouble/actions/workflows/build.yml)
[![Lint](https://github.com/nmoinvaz/multidouble/actions/workflows/lint.yml/badge.svg)](https://github.com/nmoinvaz/multidouble/actions/workflows/lint.yml)

Double-double and quad-double floating-point arithmetic for Rust, scalar and on 8-lane SIMD vectors, with **bitwise the
same results on AVX-512, AVX2 and portable builds**. It also has forward-mode dual numbers over these lanes and a dense
LU factorization in double-double.

A double-double is an unevaluated sum `hi + lo` of two `f64`, about 32 significant digits. A quad-double is a sum of four,
about 64 digits. Both are built from error-free transformations (two-sum, FMA two-product), so they run at hardware
speed, with no allocation and no arbitrary-precision library.

| Type | What it is |
|---|---|
| `v8::V8` | 8 `f64` in one AVX-512 register, two AVX2 registers, or a plain array, with fused multiply-add throughout |
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

The SIMD backend is chosen at compile time by the enabled target features. Build with
`RUSTFLAGS="-C target-cpu=native"`, or `-C target-feature=+avx2,+fma`, to get the AVX-512 or AVX2 code;
`V8::ISA` reports which one was compiled in. Results are the same on every backend; only the speed changes.

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

[docs/QUAD_DOUBLE.md](docs/QUAD_DOUBLE.md) has the full record. Quad-double costs 8–29 times double-double per
operation, and 14–17 times in sums of products.

Every check can fail. Two kinds of controls show it:

- **Built-in breakage.** The feature `mutate` breaks the quad-double algorithms one at a time on purpose, and
  `cargo test --release --features mutate` checks that each breakage fails a test.
- **Hand-written controls.** The integration tests contain controls that feed deliberately wrong results to the same
  checks: a double-double add without its low parts, a wrong derivative, and a perturbed LU factor.

## Testing, coverage and benchmarks

```sh
cargo test --release                                            # portable backend
RUSTFLAGS="-C target-feature=+avx2,+fma" cargo test --release   # AVX2
RUSTFLAGS="-C target-cpu=native" cargo test --release           # AVX-512 where the CPU has it
cargo test --release --features mutate                          # the mutation controls
cargo llvm-cov --release --all-features                         # coverage (cargo-llvm-cov)
cargo bench --bench arith                                       # scalar against lanes; f64, double-double, quad-double
cargo bench --bench linalg                                      # double-double LU against f64 LU
```

`tests/lanes.rs` checks that `V8`, `DV` and `QV` match the scalar types bit for bit. CI runs the whole suite on:

- the portable, AVX2 and AVX-512 backends;
- Linux on x86-64, ARM64, ARMv7, PPC64LE, RISC-V 64 and S390X (big-endian);
- macOS on ARM64;
- Windows on x64 and x86.

It also runs coverage, clippy on each backend, and a library check at the minimum Rust version.

The minimum Rust version is 1.89, where the AVX-512 intrinsics became stable.

## Origin

This code was written for a double-double solver of Choptuik's critical collapse in D dimensions
([choptuik-large-d](https://github.com/nmoinvaz/choptuik-large-d)). That solver needs about 30 digits and an exact
Jacobian at the speed of SIMD f64 code. The solver itself stays in that repository.

## License

[Zlib](LICENSE.md). The quad-double algorithms follow the QD library, whose license is in [LICENSE-QD](LICENSE-QD).
