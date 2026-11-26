import ExpansionBounds.Log8.Table

/-!
# Theorem 42 at `n = 8` and `p = 53`: the kernel's checks of the tables

The numbers of the groups of `Log8/Table.lean` (`Log8G0Ok`, `Log8G1Ok`), that the groups cover the exponents
`-436 ≤ e ≤ -2` with the last for `e ≤ -437`, and the constants of the driver: an exponent `e ≥ -1` is not selected,
`|ln x| ≥ ℓ_k^-` for `k ≠ 0`, Lemma 38 applies up to `X = 745.2`, and the bounds of `|r|` and of `∑_{i ≥ 1}|r_i|`
for `k ≠ 0`. The coefficients `F'_k` have at most eight parts, each in `F`.
-/

namespace ExpansionBounds

open Finset

set_option maxHeartbeats 4000000 in
/-- The groups of `k = 0` cover the exponents `-436 ≤ e ≤ -2`, the last is every `e ≤ -437`, and their numbers are
as `Log8G0Ok` asks. -/
theorem log8_grps0 : (∀ g ∈ log8Grp0, Log8G0Ok false g) ∧
    (∀ e : ℤ, -436 ≤ e → e ≤ -2 → ∃ g ∈ log8Grp0, g.elo ≤ e ∧ e ≤ g.ehi) ∧ Log8G0Ok true log8Last0 ∧
    log8Last0.m = 0 ∧ log8Last0.d = 1 ∧ log8Last0.ehi = -437 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- The groups of `k ≠ 0` cover the exponents `-436 ≤ e ≤ -2`, the last is every `e ≤ -437`, and their numbers are
as `Log8G1Ok` asks. -/
theorem log8_grps1 : (∀ g ∈ log8Grp1, Log8G1Ok log8Top1 log8Tail1 false g) ∧
    (∀ e : ℤ, -436 ≤ e → e ≤ -2 → ∃ g ∈ log8Grp1, g.elo ≤ e ∧ e ≤ g.ehi) ∧
    Log8G1Ok log8Top1 log8Tail1 true log8Last1 ∧
    log8Last1.m = 0 ∧ log8Last1.d = 1 ∧ log8Last1.ehi = -437 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- The constants of `k = 0`: `e ≥ -1` is not selected, since `|y_0| ≤ (1 + u)/(2c_r)` there; and `e₁ < 1`. -/
theorem log8_consts0 : log8Top0 < (2 : ℚ) ^ (-1 : ℤ) * (1 - 1 / 2 ^ 46) * (1 - red8U) / (1 + red8U) ∧
    log8E1 < 1 ∧ 0 < log8Top0 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- The constants of `k ≠ 0`: `|ln x| ≥ ℓ_k^-`, since `|y_0| ≥ (1 - u)/(2c_r(1 + u))` there; Lemma 38 applies up
to `X = 745.2`; `r̄_max + δ*` and the sum of `π^r_i`, `i ≥ 1`, at `X` are within the table's bounds; and `e ≥ -1` is
not selected. -/
theorem log8_consts1 : log8Lk * (1 + log8E1) + log8E0 ≤ (1 - red8U) / (2 * cr8 * (1 + red8U)) ∧ 0 ≤ log8Lk ∧
    log8Lk ≤ log8X ∧ (log8X + log8Eq log8X) / (1 - red8U) ≤ 7453 / 10 ∧ log8Alpha log8X 0 < 1 / 2 ∧
    log8RMax log8X + log8DeltaS log8X ≤ log8Top1 ∧ ∑ i ∈ Ico 1 8, log8PiR log8X log8Top1 i ≤ log8Tail1 ∧
    log8Top1 < (2 : ℚ) ^ (-1 : ℤ) * (1 - 1 / 2 ^ 46) - 2 * log8Tail1 ∧ 0 ≤ log8Top1 := by
  decide +kernel

/-- The coefficients `F'_k`: at most eight parts to a coefficient, each in `F`. -/
theorem log8_table : (∀ t ∈ log8Ser, t.length ≤ 8) ∧ ∀ t ∈ log8Ser, ∀ q ∈ t, rnQ 53 (dyQ q) = dyQ q := by
  decide +kernel

end ExpansionBounds
