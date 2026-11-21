# Lean proofs of the appendix

The appendix's results proved in Lean 4, for any precision `p ≥ 2`, on
[FloatSpec](https://github.com/Beneficial-AI-Foundation/FloatSpec), a port of Flocq.
The table lists those proved so far.

| File | Contents |
|---|---|
| `ExpansionBounds/Model.lean` | Assumption 6: `F p`, the binary numbers of precision `p` with an unbounded exponent range, `RN p`, rounding to nearest with ties to even, `u` and `ū`, and TwoSum, FastTwoSum and TwoProd |
| `ExpansionBounds/Rounding.lean` | the bounds on `RN p` stated after Assumption 6 |

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
