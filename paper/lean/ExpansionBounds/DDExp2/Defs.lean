import ExpansionBounds.DDExpEval
import ExpansionBounds.Exp8.Defs
import ExpansionBounds.ExpRed8
import ExpansionBounds.DDExp2.Data

/-!
# Proposition 44, `DD::exp` at `p = 53`: what the kernel evaluates

`DD::exp` is EXP with `s = 1` and `d = 27` on double words: the coefficients `F_k` are the first two parts of
multidouble's table (`Exp8/Data.lean`), `B = 118`, and no exponent of step (2) leaves a squaring. For an interval
`[a, b]` of `|r|` of degree `d'`, `DD2Bin` is what the kernel checks: the bound `ε` of the case on its rational
mirror (`ddExpEpsQ`) is at most `5.465u²` for both signs, with the reduction's `δ*` of `k ≠ 0`, which is above the
`0` of `k = 0`; the mirror's divisor is positive and its numerator nonnegative; and for `d' ≠ 1` the scaled-back `t`
keeps its high part above the floor `2^{-967}`. `DD2Group` is a group of exponents with one degree, its intervals
following each other from the least `|r|` that selects it to the largest.
-/

namespace ExpansionBounds

open Finset

/-- `φ_k = |F_k - 1/k!|` for the first two parts of the table -/
def dd2Phi (k : ℕ) : ℚ := |exp8F k 0 + exp8F k 1 - 1 / (k.factorial : ℚ)|

/-- `η_0 = 2^{-1075}` -/
def dd2Eta : ℚ := 1 / 2 ^ 1075

/-- the floor `2^{-967}` of the scaling back -/
def dd2Floor : ℚ := 1 / 2 ^ 967

/-- step (3)'s degree for the exponent `e`: `min(27, ⌈B/(-e - 1)⌉)` for `e ≥ -1 - B`, and `1` below, `B = 118` -/
def ddDeg (e : ℤ) : ℕ := if e < -119 then 1 else min 27 ((118 + (-e - 1) - 1) / (-e - 1)).toNat

/-- an interval `[a, b]` of `|r|` of degree `d` and one sign: the floor of the scaling back for `d ≠ 1`, the
mirror's divisor positive and numerator nonnegative, and `ε ≤ 5.465u²` -/
def DD2Sign (pos : Bool) (d : ℕ) (a b : ℚ) : Prop :=
  (d ≠ 1 → dd2Floor * (1 + red8U) ≤ a / (1 + a) - ddCoreEQ red8U (ddT0Q pos b) 0 b dd2Phi d) ∧
    0 < (if pos then expLoQ (a - dyQ dd2DeltaS) else expLoQ (-b - dyQ dd2DeltaS)) ∧
    0 ≤ ddCoreEQ red8U (ddT0Q pos b) dd2Eta b dd2Phi d +
      eFQ red8U * ((if pos then expUpQ b else expUpQ (-a)) + ddCoreEQ red8U (ddT0Q pos b) dd2Eta b dd2Phi d) ∧
    ddExpEpsQ red8U dd2Eta pos a b (dyQ dd2DeltaS) dd2Phi d ≤ 5465 / 1000 * red8U ^ 2

instance (pos : Bool) (d : ℕ) (a b : ℚ) : Decidable (DD2Sign pos d a b) := by
  unfold DD2Sign
  infer_instance

/-- an interval `[a, b]` of `|r|` of degree `d`: `0 ≤ a ≤ b`, `b + δ* ≤ 1`, and `DD2Sign` for both signs -/
def DD2Bin (d : ℕ) (a b : ℚ) : Prop :=
  0 ≤ a ∧ a ≤ b ∧ b + dyQ dd2DeltaS ≤ 1 ∧ DD2Sign true d a b ∧ DD2Sign false d a b

instance (d : ℕ) (a b : ℚ) : Decidable (DD2Bin d a b) := by
  unfold DD2Bin
  infer_instance

/-- what the kernel checks for a group `(d', e_lo, e_hi, bins)`: its exponents have the degree `d' ≥ 1`, and its
intervals, at least one, follow each other from `2^{e_lo}(1 - 2^{-46})`, or from `0` for the last group, to
`min(top, 2^{e_hi+1})`, each with `DD2Bin` -/
def DD2Group (last : Bool) (g : ℕ × ℤ × ℤ × List ((ℤ × ℕ) × (ℤ × ℕ))) : Prop :=
  (∀ e : ℤ, g.2.1 ≤ e → e ≤ g.2.2.1 → g.1 = ddDeg e) ∧ 1 ≤ g.1 ∧ g.2.2.2 ≠ [] ∧
    exp8ChainB (if last then 0 else (2 : ℚ) ^ g.2.1 * (1 - 1 / 2 ^ 46))
      (min (dyQ dd2TopS) ((2 : ℚ) ^ (g.2.2.1 + 1))) (g.2.2.2.map fun ab => (dyQ ab.1, dyQ ab.2)) = true ∧
    ∀ ab ∈ g.2.2.2, DD2Bin g.1 (dyQ ab.1) (dyQ ab.2)

instance (last : Bool) (g : ℕ × ℤ × ℤ × List ((ℤ × ℕ) × (ℤ × ℕ))) : Decidable (DD2Group last g) := by
  unfold DD2Group
  infer_instance

end ExpansionBounds
