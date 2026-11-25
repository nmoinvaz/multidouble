import ExpansionBounds.TrigEval
import ExpansionBounds.TrigTan

/-!
# Theorem 35's `C^T` in rational arithmetic

`C^T = ε(max((1 + δ_S)(1 + δ_D)/(1 - δ_C), (1 + δ_C)(1 + δ_D)/(1 - δ_S)) - 1 + εu^n 2r̄/sin₋(2r̄))` grows with `δ_S`,
`δ_C` and `δ_D` when they are nonnegative and the bounds of `δ_S` and `δ_C` are below one, so its value at such bounds
is a bound (`tanCT_le`).
-/

namespace ExpansionBounds

open Finset

/-- `sin₋ t = t - t³/6 + t⁵/120 - t⁷/5040` -/
def sinLoQ (t : ℚ) : ℚ := t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040

theorem cast_sinLo (t : ℚ) : ((sinLoQ t : ℚ) : ℝ) = sinLo t := by simp [sinLoQ, sinLo]

/-- `C^T` -/
def tanCTQ (uq : ℚ) (n : ℕ) (dS dC dD rb : ℚ) : ℚ :=
  (1 + 2 * uq ^ n) * (max ((1 + dS) * (1 + dD) / (1 - dC)) ((1 + dC) * (1 + dD) / (1 - dS)) - 1 +
    (1 + 2 * uq ^ n) * uq ^ n * (2 * rb / sinLoQ (2 * rb)))

/-- a quotient `(1 + a)(1 + d)/(1 - c)` grows with `a`, `d` and `c < 1` -/
theorem tan_quot_le {a d c a' d' c' : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ a') (hd0 : 0 ≤ d) (hd : d ≤ d') (hc : c ≤ c')
    (hc1 : c' < 1) : (1 + a) * (1 + d) / (1 - c) ≤ (1 + a') * (1 + d') / (1 - c') := by
  have hn : (1 + a) * (1 + d) ≤ (1 + a') * (1 + d') :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hn0 : 0 ≤ (1 + a') * (1 + d') := mul_nonneg (by linarith) (by linarith)
  calc (1 + a) * (1 + d) / (1 - c) ≤ (1 + a') * (1 + d') / (1 - c) :=
        div_le_div_of_nonneg_right hn (by linarith)
    _ ≤ (1 + a') * (1 + d') / (1 - c') := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        exact mul_le_mul_of_nonneg_left (by linarith) hn0

/-- `C^T` grows with `δ_S`, `δ_C` and `δ_D`, and its mirror computes it -/
theorem tanCT_le (p : ℤ) (n : ℕ) {uq : ℚ} (h : (uq : ℝ) = u p) {dS dC dD : ℝ} {dSq dCq dDq : ℚ} (rb : ℚ)
    (hS0 : 0 ≤ dS) (hS : dS ≤ ((dSq : ℚ) : ℝ)) (hS1 : dSq < 1) (hC0 : 0 ≤ dC) (hC : dC ≤ ((dCq : ℚ) : ℝ))
    (hC1 : dCq < 1) (hD0 : 0 ≤ dD) (hD : dD ≤ ((dDq : ℚ) : ℝ)) :
    tanCT p n dS dC dD (rb : ℝ) ≤ ((tanCTQ uq n dSq dCq dDq rb : ℚ) : ℝ) := by
  have hu := u_pos p
  have hS1' : ((dSq : ℚ) : ℝ) < 1 := by exact_mod_cast hS1
  have hC1' : ((dCq : ℚ) : ℝ) < 1 := by exact_mod_cast hC1
  have e1 := tan_quot_le hS0 hS hD0 hD hC hC1'
  have e2 := tan_quot_le hC0 hC hD0 hD hS hS1'
  unfold tanCT tanCTQ
  push_cast
  rw [cast_sinLo]
  push_cast
  rw [h]
  exact mul_le_mul_of_nonneg_left (by linarith [max_le_max e1 e2]) (by positivity)

end ExpansionBounds
