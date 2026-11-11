# multidouble

[![Build](https://github.com/nmoinvaz/multidouble/actions/workflows/build.yml/badge.svg)](https://github.com/nmoinvaz/multidouble/actions/workflows/build.yml)
[![Lint](https://github.com/nmoinvaz/multidouble/actions/workflows/lint.yml/badge.svg)](https://github.com/nmoinvaz/multidouble/actions/workflows/lint.yml)
[![codecov](https://codecov.io/gh/nmoinvaz/multidouble/graph/badge.svg)](https://codecov.io/gh/nmoinvaz/multidouble)

Double-double, quad-double and octo-double floating-point arithmetic for Rust, scalar and on 8-lane SIMD vectors, with
**bitwise the same results on AVX-512, AVX2, SSE2, NEON and portable builds**. It also has forward-mode dual numbers over
these lanes and dense LU factorizations in double-double, quad-double and octo-double.

A double-double is an unevaluated sum `hi + lo` of two `f64`, about 32 significant digits. A quad-double is a sum of four,
about 64 digits, and an octo-double a sum of eight, about 126 digits. All are built from error-free transformations
(two-sum, FMA two-product), so they run at hardware speed, with no allocation and no arbitrary-precision library.

| Type | What it is |
|---|---|
| `v8::V8` | 8 `f64` in one AVX-512 register, two AVX2 registers, four SSE2 or NEON registers, or a plain array, with fused multiply-add throughout; `divisor` and `div_by` for several divisions by one vector, on AVX-512 by its reciprocal (`rcp14`, Newton steps and one correction), bitwise the same as `div` |
| `dd::DD`, `dv::DV` | double-double, scalar and 8-lane; `DV::div_by` for several divisions by one b through `b.hi.divisor()`, bitwise the same as `/`; `dv::DotAcc` accumulates sums of products; `dd::split` and `dd::join` between slices of double-doubles and their hi and lo arrays |
| `qd::QD`, `qv::QV` | quad-double, scalar and 8-lane; exact decimal parsing and printing; `QV::div_by` for several divisions by one b through `b.c[0].divisor()`, bitwise the same as `/`; `QdAcc`, `QDotAcc` accumulators (`QDotAcc::add_prod_mut` adds a product in place); `qv::axpy_parts`, y + a x on quad-double vectors kept as four part arrays; `qd::to_parts` and `qd::from_parts` between slices of quad-doubles and their four part arrays |
| `od::OD`, `ov::OV` | octo-double, scalar and 8-lane: the quad-double algorithms carried to eight parts and written once for both, add, multiply, divide (also by a shared divisor), square root, comparisons, exact decimal parsing and printing; `OdAcc`, `ODotAcc` accumulators; `OV` is a `dual::Lane` (`Lane::VAL_OD`), so code written over the trait runs in octo-double and `solve_lanes_refine` refines a double-double LU's solve to octo-double; `OV::new` renormalizes eight parts on the lanes, and `ov::axpy_parts` is y + a x on octo-double vectors kept as eight part arrays |
| `dual::Du`, `dual::Dtn<N>`, `dual::Fu`, `dual::Fun<N>`, `dual::Qu`, `dual::Ou`, `dual::Dc` | forward-mode dual lanes: a double-double value with a double-double tangent or N f64 tangents, f64 versions, a quad-double value with a quad-double tangent, an octo-double value with an octo-double tangent (`Fl::from_vt_od` seeds a field of them), and a double-double value with a complex tangent, behind the `dual::Lane` trait |
| `jet::Jet<N>` | a truncated power series lane: N double-double coefficients in one variable, Cauchy products and series quotients, so a computation written over `dual::Lane` gives its own Taylor coefficients in a parameter entered as `Lane::var` (the right-hand sides of a high-order Taylor continuation of a branch); `jet::Series<N>` is its scalar parameter arithmetic (`Lane::P`, double-double on every other lane, so constants formed from the parameter stay bit for bit what they were) |
| `jet::QJet<N>` | the same in quad-double, with `jet::QSeries<N>` its parameter arithmetic: Taylor coefficients to quad-double accuracy where cancellation in the computation amplifies double-double rounding; `Lane::coef_qd` and `set_coef_qd` read and set them without rounding to double-double |
| `jet::OJet<N>` | the same in octo-double, with `jet::OSeries<N>` its parameter arithmetic, for when the amplification exceeds even quad-double; `Lane::coef_od` and `set_coef_od` read and set its coefficients in octo-double, and its sums accumulate in place (`ODotAcc::add_prod_mut`) |
| `dual::Counted<L>` | any lane type with every operation counted by kind (`dual::take_counts`, indexed by `dual::op`), the results bitwise L's: operation counts of code written over `dual::Lane` |
| `field::Fl<T, B>`, `field::DMat`, `field::TangentTail` | 8 B values of a lane type as B lane vectors, with f64 tangents set and unit tangents seeded (`set_tan64`, `unit`, `unit_tangent`), quad-double and octo-double values as part arrays (`load_parts`, `store_parts`, `load_parts_od`, `store_parts_od`), Cauchy products (`cs`, `cs_range`, `cs_w`, and bitwise the same in place, `cs_into`, `cs_range_into`, `cs_w_into`, or one lane vector at a time, `cs_lane_into`, `cs_w_lane_into`, through `Lane::acc_mut`, which saves a jet's sums the copy of its kilobytes per term), Horner evaluation, a constant double-double matrix applied to them (`MatLane::dmat_apply`), solves with a `DDLu` (`FieldSolve`, including `solve_lanes_refine`, refined in the lane type: to quad-double for `QV`, and `solve_lanes_refine_t`, value and tangent together, a complex tangent by its real part and a jet refused, and `solve_lanes_jet`, `solve_lanes_jet_refine` and `solve_lanes_jet_refine_od`, a jet's system order by order with the LU at the values, in double-double or each order refined to quad-double or octo-double) and an early end of a series once its tangent terms have stayed below a tolerance, relative to their largest so far, for a run of orders (`TangentTail`): the arithmetic of power-series methods, for every lane type |
| `linalg::DDLu`, `linalg::clu_logdet` | dense LU with partial pivoting in double-double (and blocked in f64 for mixed precision), solves, transpose solves, many right-hand sides, solves refined to quad-double (`solve_refine_qd`, the residual in quad-double), Gram matrices, the determinant; ln\|det\| and arg det of a complex double-double matrix by the same LU (`clu_logdet`) |
| `linalg::QDLu` | dense LU with partial pivoting in quad-double (8-row `QV` lanes, the trailing update in parallel, zero updates skipped), solves and transpose solves in quad-double: for systems too ill-conditioned for double-double |
| `linalg::ODLu` | dense LU with partial pivoting in octo-double (8-row `OV` lanes, the trailing update in parallel, zero updates skipped), solves and transpose solves in octo-double: for systems too ill-conditioned for quad-double, to about cond(A) 2^-418 |
| `linalg::lu_rect_f64` | the f64 partial-pivoting LU of the first columns of a rectangular block, leaving the Schur complement: the step of a block (staircase) LU |
| `linalg::StaircaseLu` | the f64 LU with partial pivoting of a staircase (almost block diagonal) system with one global parameter, as multiple shooting gives, built block by block without the dense matrix; solves and transpose solves in double-double |
| `precision::Precision`, `precision::Double`, `precision::Quad`, `precision::Octo` | one trait over double-double, quad-double and octo-double: the scalar, lane, dual, jet and LU types of one precision, and the operations whose names or arity differ between them (`new`, `load_field`, `coef`, `field_dual`, `lu_factor`, `dot`, ...), each delegating to the precision's own, so code written once over `Precision` gives bitwise the results of the code written for one precision |
| `exact` | exact dyadic and decimal arithmetic, the reference the tests compare against |

Every number and lane type has `mul_pwr2`, an exact scaling by a power of two (every part, tangents included), for
computing in a variable rescaled by 2^k, such as a power series whose coefficients would overflow in the original variable;
`dd::pow2_near` gives the power of two nearest to a scale in the logarithm (within a factor of √2).

## Installation

Add the crate from [crates.io](https://crates.io/crates/multidouble):

```sh
cargo add multidouble
```

or as a dependency in `Cargo.toml`:

```toml
[dependencies]
multidouble = "1.0"
```

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

The octo-double operations are checked the same way, against exact arithmetic on random, cancelling, near-overflow,
near-underflow, near-power-of-two, sparse and computed inputs. In units of 2⁻⁴¹⁸ (relative to |a| + |b| for the adds):

| Operation | Bound checked | Worst seen (2,000 inputs per kind) |
|---|---|---|
| add, subtract, + f64 | 1 | 1.1×10⁻⁴ |
| multiply, × f64 | 1 | 9.5×10⁻⁵ |
| divide | 2 | 1.1×10⁻⁴ |
| square root | 2 | 1.1×10⁻⁴ |
| dot products of 1 to 64 terms (relative to Σ \|aᵢbᵢ\|) | (8 + n)/8 | 9.8×10⁻⁵ |

Octo-double costs 4–8 times quad-double per operation on the NEON lanes (add 3.7, multiply 5.3, divide 7.6) and about 14
times in sums of products, whose quad-double accumulator drops the smallest partial products where this one keeps them.
The worst error, about 2⁻⁴³¹, is the rounding of the result to eight parts. The near-underflow inputs are checked with
an absolute allowance of 16×2⁻¹⁰⁷⁴, as for quad-double: full precision needs every part to be a normal `f64`, so values
above about 2⁻⁶⁰⁰. `ODLu` solves to about 10⁻¹³³ cond(A) against planted solutions, 2⁻²²⁰ times the quad-double LU's
error on the same systems, for condition numbers from 1 to 10³⁰.

The octo-double jet's coefficients are checked against exact arithmetic too (`tests/ojet.rs`). Polynomials,
reciprocals, quotients and a rational function in the series variable, and series formed in the parameter arithmetic,
are within 10⁻¹²³ of the sum of their terms' magnitudes (2.2×10⁻¹²⁸ seen, where the quad-double jet errs by 2×10⁻⁶⁴).
The order-by-order solve reaches planted solutions within 10⁻¹²⁰ in four refinement steps (1.1×10⁻¹³⁰ seen; two steps
leave 2.4×10⁻⁹⁵). On the NEON lanes an `OJet<24>` product costs 7.6 times a `QJet<24>` one, a term of its sums 12
times, and a 24-order solve on 32 values 8.3 times, with four refinement steps against two (`cargo bench --bench jet`).
The octo-double dual `Ou` gives partial derivatives and Jacobian columns within 10⁻¹²³ of the exact ones (3.6×10⁻¹³⁰
seen, where `Qu` errs by 1.9×10⁻⁶⁴), and its value is `OV`'s bit for bit.

Every check can fail. Two kinds of controls show it:

- **Built-in breakage.** The feature `mutate` breaks the quad-double and octo-double algorithms one at a time on
  purpose, and `cargo test --release --features mutate` checks that each breakage fails a test. One of them replaces
  a fused multiply-subtract by a plain product on the compile-time backend only, and the backend check catches it there
  and on no other backend.
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
cargo llvm-cov --features mutate                                # coverage (cargo-llvm-cov)
cargo bench --bench arith                                       # scalar against lanes; f64, double-double, quad-double, octo-double
cargo bench --bench linalg                                      # double-double LU against f64 LU, and the octo-double LU
cargo bench --bench jet                                         # OJet<24> against QJet<24>: product, sums, the jet solve
cargo test --release --test odlu bench_od_lu -- --ignored --nocapture   # the octo-double LU at n = 64, 256, 800
```

`tests/lanes.rs` checks that `V8`, `DV`, `QV` and `OV` match the scalar types bit for bit, `OJet` its scalar series `OSeries` and `Ou` its scalar formulas, on every backend the CPU has. The NEON backend's code is also
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
Jacobian at the speed of SIMD f64 code, and at large D, where rounding is amplified, quad-double and octo-double.

## License

[BSD 3-Clause](LICENSE), the license of the QD library whose quad-double algorithms `src/qd.rs` and `src/qv.rs`
follow, and `src/od.rs` carries to eight parts. QD's own notice is kept in [LICENSE-QD](LICENSE-QD).
