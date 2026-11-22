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
