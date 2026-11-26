import ExpansionBounds.DDLog2

/-!
# Controls of Proposition 44's constants for `DD::ln`

Each claim below is one of the kernel's checks of `DDLog2.lean` with a wrong number, a wrong degree or an
interval or a group left out, and the kernel proves its negation.
This file is written by `ddlog_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
/-- the worst case's ratio is not within `15.350u²` -/
example : ¬ ddlBQ false 27 (dyQ (1710601602911521, 53)) (dyQ ddlLkS) (ddlE (dyQ ddlLkS)) (dyQ (399572145162690497, 60))
    (ddlDelta (dyQ (399572145162690497, 60) + dyQ ddlDStarS)) ≤ 15350 / 1000 * red8U ^ 2 * dyQ ddlLkS := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- `𝓔(0)` is not within `2^{-1072}` -/
example : ¬ ddlBQ true 2 ((2 : ℚ) ^ (-118 : ℤ) * (1 - 1 / 2 ^ 46)) 0 0 0 0 ≤
    1 / 2 ^ 1072 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the worst case's `C` is not within `2^{-42}` -/
example : ¬ ddlCQ false 27 (dyQ (1710601602911521, 53)) (ddlE red8X) (dyQ (399572145162690497, 60))
    (ddlDelta (dyQ (399572145162690497, 60) + dyQ ddlDStarS)) ≤ 1 / 2 ^ 42 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- a group with the wrong degree is not accepted -/
example : ¬ DDL1Group false (26, -5, -2, ddl1G0.2.2.2) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- a group with an interval left out is not accepted -/
example : ¬ DDL1Group false (27, -5, -2, ddl1G0.2.2.2.drop 1) := by
  decide +kernel

/-- the groups of `k = 0` on the linear piece, the first left out, do not cover `-59 ≤ e ≤ -2` -/
example : ¬ ∀ e : ℤ, -59 ≤ e → e ≤ -2 → ∃ g ∈ ddl0Lin.tail, g.2.1 ≤ e ∧ e ≤ g.2.2.1 := by decide +kernel

/-- the groups of `k ≠ 0`, the first left out, do not cover `-118 ≤ e ≤ -2` -/
example : ¬ ∀ e : ℤ, -118 ≤ e → e ≤ -2 → ∃ g ∈ ddl1Grp.tail, g.2.1 ≤ e ∧ e ≤ g.2.2.1 := by decide +kernel

/-- the floor of the scaling back is not met at degree 2 by an interval from `2^{-968}`, below it -/
example : ¬ DDLFloor true 2 (1 / 2 ^ 968) (dyQ ddl0S.2.2.2 + ddlEs (dyQ ddl0S.2.2.2)) := by
  decide +kernel

/-- the group of degree 3 is not on the start's second piece: its `ℓ₂` is above `u(1 - u)/2` -/
example : ¬ dyQ (18446744073709565781, 104) < red8U * (1 - red8U) / 2 := by decide +kernel

/-- the least `ℓ` of a group of `k = 0`, one unit higher, is not below the `ℓ` that select it -/
example : ¬ (1 + ddlE1) * dyQ (18446744073708041268, 123) +
    ddlE0 ≤
    (2 : ℚ) ^ (-59 : ℤ) * (1 - 1 / 2 ^ 46) := by decide +kernel

end ExpansionBounds
