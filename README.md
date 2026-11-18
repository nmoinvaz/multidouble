# multidouble

[![Build](https://github.com/nmoinvaz/multidouble/actions/workflows/build.yml/badge.svg)](https://github.com/nmoinvaz/multidouble/actions/workflows/build.yml)
[![Lint](https://github.com/nmoinvaz/multidouble/actions/workflows/lint.yml/badge.svg)](https://github.com/nmoinvaz/multidouble/actions/workflows/lint.yml)
[![codecov](https://codecov.io/gh/nmoinvaz/multidouble/graph/badge.svg)](https://codecov.io/gh/nmoinvaz/multidouble)

Double-double, quad-double and octo-double floating-point arithmetic for Rust, scalar and on 8-lane SIMD vectors, with
**bitwise the same results on AVX-512, AVX2, SSE2, NEON and portable builds**. It also has forward-mode dual numbers,
truncated power series and dense LU factorizations in all three precisions.

A double-double is an unevaluated sum `hi + lo` of two `f64`, about 32 significant digits. A quad-double is a sum of four,
about 64 digits, and an octo-double a sum of eight, about 126 digits. All are built from error-free transformations
(two-sum, FMA two-product), so they run at hardware speed, with no allocation and no arbitrary-precision library.

The octo-double add, multiply, divide and square root have proven error bounds. The paper [Error bounds for quad-double
style arithmetic on floating-point expansions of any length](paper/expansion-error-bounds.pdf) proves them for the same
algorithms at any number of parts, and shows that simple inputs reach the bounds of the add, multiply and divide.

## Types

### Numbers

| Type | What it is |
|---|---|
| `v8::V8` | 8 `f64` lanes: one AVX-512 register, two AVX2 registers, four SSE2 or NEON registers, or a plain array, with fused multiply-add throughout |
| `dd::DD`, `dv::DV` | double-double, scalar and on 8 lanes |
| `qd::QD`, `qv::QV` | quad-double, scalar and on 8 lanes, with exact decimal parsing and printing |
| `od::OD`, `ov::OV` | octo-double, scalar and on 8 lanes, with exact decimal parsing and printing: the quad-double algorithms carried to eight parts and written once for both |
| `dv::DotAcc`, `qd::QdAcc`, `qv::QDotAcc`, `od::OdAcc`, `ov::ODotAcc` | accumulators for sums of products |

The lanes give the scalar type's bits on every backend. The scalar types have `sqrt`, `recip` and `powi`, and every type
has `mul_pwr2`, a scaling by a power of two that is exact barring overflow and underflow. Two operations trade accuracy
for speed. `DD::fast_div` divides with two divisions instead of three, within a proven 15 u² + 56 u³ barring underflow
and overflow, and `OD::sloppy_mul` takes about 1/1.35 of the time of `*` and gives up 7 to 9 of the 424 bits. An
octo-double meets a double-double through `OD::mul_dd`, `OD::add_dd` and `OdAcc::add_prod_dd`, which skip the zero
parts' products and give the promoted operation's bits, a NaN's sign and payload aside. The API documentation lists the
rest, such as division by a shared divisor and conversion to arrays of parts.

### Packed storage

| Type | What it is |
|---|---|
| `pack::PackedDD`, `pack::PackedQD`, `pack::PackedOD` | values packed in 121, 235 and 463 bits instead of 128, 256 and 512, restored bit for bit |

A lower part keeps its sign and fraction but only a 4-bit code for its exponent, which in a renormalized value lies 53
or more binary places below the part above it. Values are stored in blocks of 8, so `get(i)` reads any one of them alone
and `unpack_into` and `dot` decode 8 at a time with SIMD. A value whose parts do not fit the codes, under 0.5% of the
octo-double arithmetic's results in the tests, keeps its lower parts raw in a side table. `words` and `side` give the
storage, and `from_raw` checks and restores it.

![An octo-double, raw and packed](docs/pack-layout.svg)

[docs/pack.md](docs/pack.md) describes the format with diagrams, its size against general compressors, and its speed.

### Derivatives and power series

| Type | What it is |
|---|---|
| `dual::Du`, `dual::Dtn<N>` | a double-double value with a double-double tangent, or with N `f64` tangents |
| `dual::Fu`, `dual::Fun<N>` | the `f64` versions |
| `dual::Qu`, `dual::Ou` | a quad-double value with a quad-double tangent, an octo-double value with an octo-double tangent |
| `dual::Dc` | a double-double value with a complex tangent |
| `jet::Jet<N>`, `jet::QJet<N>`, `jet::OJet<N>` | a truncated power series in one variable, with N coefficients in double-double, quad-double or octo-double |
| `dual::Counted<L>` | any lane type with every operation counted by kind |

All of them, and `OV`, are lanes behind the `dual::Lane` trait. A computation written once over the trait gives values,
derivatives, or its own Taylor coefficients in a parameter entered as `Lane::var`, the right-hand sides of a high-order
Taylor continuation. The quad-double and octo-double jets keep the coefficients accurate where cancellation in the
computation amplifies double-double rounding. `Counted<L>` returns L's results bit for bit and counts every operation on
the thread that runs it (`dual::take_counts`), so counting a whole computation takes running it on one thread.

### Fields and linear algebra

| Type | What it is |
|---|---|
| `field::Fl<T, B>` | 8 B values of a lane type as B lane vectors: the arithmetic of power-series methods, for every lane type |
| `field::cs`, `field::cs_range`, `field::cs_w`, `field::horner` | Cauchy products and Horner evaluation, also in place, one lane vector or one coefficient at a time, and on threads, all with the same bits |
| `field::DMat` | a constant double-double matrix applied to a field |
| `field::FieldSolve` | solves with a `DDLu`, refined in the lane type, and a jet's system order by order |
| `field::TangentTail` | ends a series once its tangent terms have stayed small for a run of orders |
| `linalg::DDLu` | dense LU with partial pivoting in double-double, blocked in `f64`: solves, transpose solves, solves refined to quad-double, Gram matrices and the determinant |
| `linalg::clu_logdet`, `linalg::clu_pivots` | ln\|det\|, arg det and the pivots of a complex double-double matrix |
| `linalg::QDLu`, `linalg::ODLu` | dense LU in quad-double and octo-double on 8-row lanes, for systems too ill-conditioned for the precision below (an `ODLu` solve errs by about cond(A) 2⁻⁴¹⁸) |
| `linalg::lu_rect_f64`, `linalg::StaircaseLu` | the `f64` LU of a block of columns, and of a staircase system with one global parameter, as multiple shooting gives |

### Generic code

| Type | What it is |
|---|---|
| `precision::Precision`, `precision::Double`, `precision::Quad`, `precision::Octo` | one trait over double-double, quad-double and octo-double |
| `exact` | exact dyadic and decimal arithmetic, the reference the tests compare against |

`Precision` gathers one precision's scalar, lane, dual, jet and LU types, and the operations whose names or arity
differ between them (`new`, `load_field`, `coef`, `field_dual`, `lu_factor`, `dot`, ...), each delegating to the
precision's own. Code written once over `Precision` gives bitwise the results of the code written for one precision.

## Installation

Add the crate from [crates.io](https://crates.io/crates/multidouble):

```sh
cargo add multidouble
```

or as a dependency in `Cargo.toml`:

```toml
[dependencies]
multidouble = "4.8"
```

It needs Rust 1.89 or later, the version in which the AVX-512 intrinsics became stable.

## Usage

```rust
use multidouble::dd::DD;
use multidouble::native::DV;
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

The SIMD backend is the best one the CPU has, detected at run time:

| Backend | Chosen when | Registers |
|---|---|---|
| `avx512` | the x86-64 CPU has AVX-512F, AVX2 and FMA | one zmm |
| `avx2` | the x86-64 CPU has AVX2 and FMA | two ymm |
| `sse2` | any other x86 or x86-64 CPU; SSE2 has no fused multiply-add, so that one operation runs per lane through `f64::mul_add` | four xmm |
| `neon` | aarch64 | four NEON |
| `portable` | every other target, or any target with the cargo feature `portable` | a plain array |

`linalg` picks it by itself. Code of your own, written once over the backend `S: Simd`, runs on it through
`simd::dispatch`:

```rust
use multidouble::dd::DD;
use multidouble::dv::{DotAcc, DV};
use multidouble::simd::{self, Kernel, Simd};

/// the sum of squares of the double-doubles (hi, lo), 8 lanes at a time
struct SumSq<'a>(&'a [f64], &'a [f64]);

impl Kernel for SumSq<'_> {
    type Output = DD;
    // inlined into the backend's instruction set, so that the lane operations become its instructions
    #[inline(always)]
    fn run<S: Simd>(self) -> DD {
        let mut acc = DotAcc::<S>::zero();
        for (h, l) in self.0.chunks_exact(8).zip(self.1.chunks_exact(8)) {
            let x = DV::load(h, l);
            acc = acc.add_prod(x, x);
        }
        let v = acc.finish();
        (0..8).fold(DD::ZERO, |s, j| s + v.lane(j))
    }
}

let (hi, lo) = (vec![1.5; 64], vec![0.0; 64]);
assert_eq!(simd::dispatch(SumSq(&hi, &lo)).to_f64(), 144.0);
println!("ran on {}", simd::isa());
```

Inside `run`, loop over lanes with plain `for` loops. An adapter such as `fold` runs the loop body inside a std
function, which the compiler may keep out of line and compile without the backend's instructions, so that every lane
operation becomes a call.

The aliases in `native` (`native::DV`, `native::QV`, ...) are the lane types on the backend the build's target
features select at compile time, for code that does not dispatch (`RUSTFLAGS="-C target-cpu=native"` makes that the
best one too). Results are the same on every backend; only the speed changes.

The cargo feature `f128` adds conversions between `f128` and the scalar types. It needs nightly Rust, as `f128` is
unstable. `QD::from_f128` is exact, `DD::from_f128` rounds to the nearest parts, and both `to_f128` are correctly
rounded.

## Python

[`python/`](python/README.md) is a Python package of the same arithmetic on numpy arrays: elementwise double-double
add, subtract, multiply and divide on (hi, lo) array pairs on the best backend the CPU has, double-double, quad-double
and octo-double LU solves (`od_solve` takes eight part arrays), octo-double arrays plus a double-double one or a
multiple of another (`od_add_dd`, `od_axpy`), and numpy versions of the error-free transformations
(`pip install ./python`, which builds it with maturin).

## Accuracy

Every operation is tested against exact arithmetic (`exact`), which shares no code with the algorithms. With u = 2⁻⁵³,
the parts of an n-part type hold 53n significand bits, and the natural target is an error of uⁿ times the result, the
rounding error of a format with 53n bits. The table gives each operation's error bound in those units, with the bits it
gives up in parentheses.

| Operation | double-double (106 bits) | quad-double (212 bits) | octo-double (424 bits) |
|---|---|---|---|
| add, subtract | 3 u² (1.6), proven | 8 u⁴ (3) | u⁸ (0), proven |
| multiply | 5 u² (2.3) | 16 u⁴ (4) | u⁸ (0), proven |
| divide | 8 u² (3) | 32 u⁴ (5) | u⁸ (0), proven |
| square root | 25/8 u² (1.6), proven | 32 u⁴ (5) | 3 u⁸ (1.6), proven |

A proven bound holds for every input. The double-double add's is Theorem 3.1 of Joldes, Muller and Popescu (2017),
`fast_div`'s is their Theorem 7.1, which Muller and Rideau (2022) proved formally, and the double-double square root's
is Theorem 3.5 of Lefèvre, Louvet, Muller, Picot and Rideau (2023), whose Algorithm 8 it is. The octo-double ones are in
[the paper](paper/expansion-error-bounds.pdf), where each has a second term at most 2⁻¹⁵ of the first. The other bounds
are the thresholds the tests check.

- The double-double add is relative to the result. The quad-double `+` is measured against |a| + |b|, all its algorithm
  promises after cancellation, and so is the small second term of the octo-double add. The double-double divide is
  measured on the residual of its quotient.
- The octo-double add, multiply and divide reach their bounds on the paper's worst-case inputs (`od_worst_case_inputs`),
  and the tests check the proven bounds of the add and multiply on every input that meets the paper's hypotheses.
  Random inputs stay far inside: below 0.01 u⁸ for every octo-double operation, and up to 1.66 u², 3.12 u² and 1.54 u²
  for the double-double add, multiply and divide.
- The quad-double column is for the default operators `+`, `*` and `/`. The more accurate `ieee_add`, `accurate_mul` and
  `accurate_div` keep 8 u⁴, 8 u⁴ and 16 u⁴. The quad-double types use the QD library's algorithms (Hida, Li and Bailey,
  ARITH-15, 2001) with three repairs: the accurate add lost a term when all parts are read with three emitted, and its
  accumulator when four parts are emitted before every part is read, and the square root, which lost accuracy far from
  1, now scales its argument by a power of four.
- The sloppy multiply has no level below the eighth part. Its error is the 64 roundings at that level and the dropped
  products of order above 8, at most 2³¹·⁹³ u⁸|a₀b₀| for operands on the ladder (proved in the paper, Theorem 30, with
  the constant from `paper/sloppy_consts.py`), where `*` errs by u⁸. The bound is a triangle inequality: random
  operands give at most 98 u⁸|a₀b₀| (1.5 units of 2⁻⁴¹⁸) and a hill climb 582 u⁸|a₀b₀| (2⁹·² u⁸).
- Two-sum, quick-two-sum and two-product are exact. Octo-double dot products of n terms are checked against the
  accumulator's bound, (|Z| + cₙ Σ|aᵢbᵢ|) u⁸ with cₙ below 1 up to 50 terms (proved in the paper); the second term grows
  like (nu)⁹ Σ|aᵢbᵢ|, and 2048 constructed terms reach 2²³·⁸ u⁸|Z|. Full precision needs every part to be a normal
  `f64`, so octo-double values above about 2⁻⁶⁰⁰; near underflow the tests allow an absolute 16×2⁻¹⁰⁷⁴.
- `ODLu` solves to about 10⁻¹³³ cond(A) for condition numbers up to 10³⁰, 2⁻²²⁰ times the quad-double LU's error. `OJet`
  coefficients are within 10⁻¹²³ of the sum of their terms' magnitudes, where the quad-double jet errs by 2×10⁻⁶⁴, and
  its order-by-order solve reaches planted solutions within 10⁻¹²⁰ in four refinement steps. `Ou` gives derivatives
  within 10⁻¹²³, and its value is `OV`'s bit for bit.

Every check can fail. The feature `mutate` breaks the quad-double and octo-double algorithms one at a time, and
`cargo test --release --features mutate` checks that each breakage fails a test. The integration tests also feed
deliberately wrong results to the same checks: a double-double add without its low parts, a wrong derivative, a
perturbed LU factor, and f128 conversions that round twice.

## Testing, coverage and benchmarks

```sh
cargo test --release                                            # SSE2 on x86, NEON on aarch64
cargo test --release --features portable                        # the plain-array backend
RUSTFLAGS="-C target-feature=+avx2,+fma" cargo test --release   # AVX2
RUSTFLAGS="-C target-cpu=native" cargo test --release           # AVX-512 where the CPU has it
cargo test --release --features mutate                          # the mutation controls
cargo +nightly test --release --features f128                   # the f128 conversions
cargo llvm-cov --features mutate                                # coverage (cargo-llvm-cov)
cargo bench --bench arith                                       # scalar against lanes; f64, double-double, quad-double, octo-double
cargo bench --bench linalg                                      # double-double LU against f64 LU, and the octo-double LU
cargo bench --bench jet                                         # OJet<24> against QJet<24>: product, sums, the jet solve
cargo test --release --test odlu bench_od_lu -- --ignored --nocapture   # the octo-double LU at n = 64, 256, 800
```

Each precision costs more than the one below it:

| Comparison | Per operation | Sums of products |
|---|---|---|
| quad-double against double-double | 8–29× | 14–17× |
| octo-double against quad-double, NEON lanes | 4–8× (add 3.7, multiply 5.3, divide 7.6) | about 14×, as its accumulator keeps the smallest partial products the quad-double one drops |

On the NEON lanes an `OJet<24>` product costs 7.6 times a `QJet<24>` one, a term of its sums 12 times, and a 24-order
solve on 32 values 8.3 times, with four refinement steps against two.

`tests/lanes.rs` checks that `V8`, `DV`, `QV` and `OV` match the scalar types bit for bit, `OJet` its scalar series
`OSeries` and `Ou` its scalar formulas, on every backend the CPU has. The NEON backend's code is also
compiled on x86 against a pure-Rust model of its intrinsics and checked there (`v8::neon_check`), so it is tested on
every runner, not only on ARM. CI runs the whole suite on:

- the portable, SSE2, AVX2, AVX-512 and NEON backends;
- Linux on x86-64, ARM64, ARMv7, PPC64LE, RISC-V 64 and S390X (big-endian);
- macOS on ARM64;
- Windows on x64 and x86;
- nightly Rust with the feature `f128`, on x86-64 and ARM64 Linux.

It also runs coverage, clippy on each backend, and a library check at the minimum Rust version.

## Origin

This code was written for a double-double solver of Choptuik's critical collapse in D dimensions
([choptuik-large-d](https://github.com/nmoinvaz/choptuik-large-d)). That solver needs about 30 digits and an exact
Jacobian at the speed of SIMD f64 code, and at large D, where rounding is amplified, quad-double and octo-double.

## License

[BSD 3-Clause](LICENSE), the license of the QD library whose quad-double algorithms `src/qd.rs` and `src/qv.rs`
follow, and `src/od.rs` carries to eight parts. QD's own notice is kept in [LICENSE-QD](LICENSE-QD).
