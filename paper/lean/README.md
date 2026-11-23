# Lean proofs of the appendix

The appendix's results proved in Lean 4, for any precision `p ≥ 2`, on
[FloatSpec](https://github.com/Beneficial-AI-Foundation/FloatSpec), a port of Flocq.
The table lists those proved so far.

| File | Contents |
|---|---|
| `ExpansionBounds/Model.lean` | Assumption 6: `F p`, the binary numbers of precision `p` with an unbounded exponent range, `RN p`, rounding to nearest with ties to even, `u` and `ū`, and TwoSum, FastTwoSum and TwoProd |
| `ExpansionBounds/Rounding.lean` | the bounds on `RN p` stated after Assumption 6 |
| `ExpansionBounds/Bridge.lean` | FloatSpec proves TwoSum and FastTwoSum for a format with a least exponent `emin`; on multiples of `2^emin` its rounding is that of `F p`, which carries both to the unbounded model |
| `ExpansionBounds/Facts.lean` | Lemma 8, (a) to (c) |
| `ExpansionBounds/Renorm.lean` | VecSum and `Ren_n`, and Theorem 9 (a), (b), (d) and (e) |
| `ExpansionBounds/RenormSharp.lean` | Theorem 9 (c): on `(1, u, u², …, uⁿ)` the loss is `B_0 = uⁿ` |
| `ExpansionBounds/Levels.lean` | Lemma 11: a run on the levels as a list of assignments, deps and roundings, bounded at every state it passes through |
| `ExpansionBounds/Parts.lean` | Lemma 12: the parts of `Ren_n`, `x_0` from `S` and each `x_i` from `x_{i-1}` and the `v_j` after |
| `ExpansionBounds/OpBounds.lean` | Lemma 13 (a) and (b) from the bounds on an operation's levels, and the bounds of Lemma 11 growing with the inputs' totals |
| `ExpansionBounds/Ops.lean` | ADD, MULF and ADDF and Lemma 13 for each; ADD and MULF share one program of Lemma 11 |
| `ExpansionBounds/MulOps.lean` | MUL and Lemma 13 for it: `T_m = m(m + 1)`, `Q = n² + n - 1`, the inputs within `A_m` and the dropped products within `Δ` |
| `ExpansionBounds/Acc.lean` | the accumulator's lemma (`lem:acc`): `K` deposits into the levels, each within `S_m(k)` at every moment and the rounding errors within `Ē_lev`, with the bounds in the lemma's closed form |
| `ExpansionBounds/Horner.lean` | Lemma 33 (`lem:horner`): Horner's rule on expansions, with Lemma 13's bounds `G_MUL` and `G_ADD` applied in turn |
| `ExpansionBounds/GScale.lean` | Lemma 13's bounds `G_MUL` and `G_ADD` homogeneous of degree one in the operands' part bounds and `Z̄`, nonnegative, and `G_ADDF` for ADDF |
| `ExpansionBounds/Taylor.lean` | the sine and cosine series: for `\|r\| ≤ 1` a partial sum errs by at most its first omitted term, `\|sin r\| ≥ \|r\|(1 - r²/6)` and `cos r ≥ cos₋ r̄` |
| `ExpansionBounds/SinCos.lean` | Lemma 34 (`lem:sincosr`): SINR and COSR within `δ_S\|sin r\|` and `δ_C cos r`, with parts at most `ψ_s\|r\|` and `ψ_c`, for any `K ≥ 2`, scaling `2^e` and `r̄ ≤ 1`, and SINR's `r` and COSR's `1` below `\|r_0\| < u^{n/2}` |
| `ExpansionBounds/FExact.lean` | Lemma 41 (`lem:fexact`): `ADDF(x', -1) = x' - 1` exactly for `x'_0 ∈ [1/2, 2]`, by Sterbenz and Theorem 9 (a); that range, from Lemma 38 (a) and Theorem 42, is the hypothesis |
| `ExpansionBounds/ExpRed.lean` | Lemma 38 (`lem:expred`): EXP's reduction, `\|k\| ≤ 1075`, `\|r_e\| ≤ r̄_max` and `x_0 - kc_h ∈ F`, and `r` within `δ` of `r_e` with parts at most `π^r`, for `p ≥ 14`, `c_r = RN(1/ln 2)` and `c_h` a multiple of `2^{-p-1}`, with `η_0 = 0` as the exponent range is unbounded; and `G_MULF` for MULF |
| `ExpansionBounds/ExpCore.lean` | Lemma 39 (`lem:core`): steps (2) to (4) of EXP, with `U ≥ ∑\|r_i\|`, Horner's rule on the `F_j` of `1/j!`, the last product and sum at `r̂`'s scale and `m` squarings, give `\|t - (e^r - 1)\| ≤ E_m` and `\|t_i\| ≤ ψ_{m,i}` for any `m`, `d' ≥ 1` and `b' < d' + 2`; `n ≤ 31` becomes `(1 + u)^n ≤ 1 + γ`, and `η_0 = 0`. With it the series of `e^x` after `N` terms, within `B^N/(N!(1 - B/(N + 1)))` for `\|x\| ≤ B < N + 1` |
| `ExpansionBounds/Closed.lean` | Theorems 14 and 15 (`thm:t2`, `thm:t3`): on `H(θ)` operands, the closed forms `L_m`, `R_n` and `Δ_n` of the level bounds of MUL, ADD, MULF and ADDF, and `\|Z - x\| ≤ u^n\|Z\| + κu^{n+1}M`, with its forms relative to the result by `(eq:a0)`; for any `θ > 0`, and `2ρ < 1` for the relative forms |
| `ExpansionBounds/Closure.lean` | Theorem 17 (`thm:t5`): the parts of the result of MUL, ADD, MULF and ADDF within `u^i((1 + u)^i\|x_0\| + i u (1 + u)^{n+i-1} Λ M)`, by Theorem 9 (d) and Lemma 12; and for `\|Z\| ≥ ζM` with `ξ > 0`, `\|x_0\| ≥ ξM` and the part inequalities of `H(θ')` (the paper's `H(θ')` also needs `θ'u ≤ 1/4`), with the paper's `ζ` for MUL and MULF, and for ADD and ADDF on leading parts of one sign |
| `ExpansionBounds/ExpThm.lean` | Theorem 40 (`thm:exp`), for a case: with `r` within `δ` of `x - k ln 2`, `a ≤ \|r\| ≤ b` and its sign, EXP's `y = 2^k ADDF(t, 1)` satisfies `\|y - e^x\| ≤ ε e^x` with `ε = (E_m + ε_s)/v + e^δ - 1`; `n 2^{-1074}` is zero with no exponent limits |

From this folder:

```sh
# Mathlib's prebuilt files for the modules FloatSpec imports
lake exe cache get Mathlib.Tactic Mathlib.Analysis.Real.Sqrt Mathlib.Algebra.Order.Floor.Ring \
  Mathlib.Data.Nat.Digits.Defs Mathlib.Data.Nat.Log Mathlib.Algebra.Divisibility.Basic \
  Mathlib.Algebra.Order.Monoid.Unbundled.Pow Mathlib.Data.Real.Basic
lake build   # about 5 minutes the first time, most of it FloatSpec
```

The build treats warnings as errors, so a proof left as `sorry` fails it. Each theorem depends only on Lean's axioms
`propext`, `Classical.choice` and `Quot.sound`, which `#print axioms` shows.

Lean is pinned to v4.34.1, and Mathlib and cslib to their v4.34.1 tags. FloatSpec pins v4.34.0-rc2, whose executables
abort at thread exit on macOS 27 ([lean4#15087](https://github.com/leanprover/lean4/issues/15087)).
