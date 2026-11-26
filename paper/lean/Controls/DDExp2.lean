import ExpansionBounds.DDExp2

/-!
# Controls of Proposition 44's constant for `DD::exp`

Each claim below is one of the kernel's checks of `DDExp2.lean` with a wrong number, a wrong degree, an
interval or a group left out or a pair that is not a double word, and the kernel proves its negation.
This file is written by `ddexp_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
/-- the worst case's bound is not within `5.464u²` -/
example : ¬ ddExpEpsQ red8U dd2Eta false (dyQ (2310824987954753, 53)) (dyQ (12786308645209148243, 65))
    (dyQ dd2DeltaS) dd2Phi 27 ≤ 5464 / 1000 * red8U ^ 2 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- a group with the wrong degree is not accepted -/
example : ¬ DD2Group false (26, -5, -2, dd2G0.2.2.2) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- a group with an interval left out is not accepted -/
example : ¬ DD2Group false (27, -5, -2, dd2G0.2.2.2.drop 1) := by
  decide +kernel

/-- the groups, the first left out, do not cover `-118 ≤ e ≤ -2` -/
example : ¬ ∀ e : ℤ, -118 ≤ e → e ≤ -2 → ∃ g ∈ dd2Grp.tail, g.2.1 ≤ e ∧ e ≤ g.2.2.1 := by decide +kernel

/-- the bound of `|r|`, which rules out the exponent `-1`, does not rule out `-2` -/
example : ¬ dyQ dd2TopS < (2 : ℚ) ^ (-2 : ℤ) * (1 - 1 / 2 ^ 46) := by decide +kernel

/-- the floor `2^{-100}` of the scaling back is not met at the least `|r|` of degree 2 -/
example : ¬ (1 / 2 ^ 100 : ℚ) * (1 + red8U) ≤ dyQ (70368744177663, 164) / (1 + dyQ (70368744177663, 164)) -
    ddCoreEQ red8U (ddT0Q true (dyQ (1, 59))) 0 (dyQ (1, 59)) dd2Phi 2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the bound of `δ*` one unit lower is not one -/
example : ¬ dd2Delta dd2RMax ≤ dyQ (dd2DeltaS.1 - 1, dd2DeltaS.2) := by decide +kernel

/-- a pair whose low part is three quarters of an ulp of the high part is not a double word -/
example : ¬ rnQ 53 (dyFn [(1, 0), (3, 54)] 0 + dyFn [(1, 0), (3, 54)] 1) = dyFn [(1, 0), (3, 54)] 0 := by
  decide +kernel

end ExpansionBounds
