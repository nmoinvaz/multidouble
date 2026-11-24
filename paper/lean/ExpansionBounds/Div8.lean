import ExpansionBounds.Div
import ExpansionBounds.Sloppy8

/-!
# Theorem 19 (`thm:t6`) at `n = 8` and `p = 53`

DIV's `κ_DIV` evaluated in rational arithmetic, as `div_consts.py` computes it: `κ_DIV ≤ 2^{26.0}` on `H(1)` and
`2^{27.48}` on `H(2)`, so `|a/b - x| ≤ (1 + 2^{-25.5})2^{-424}|a/b|` on `H(2)` operands. The recursion `P^{(k)}` runs
eight steps, each reading the last one at several indices; simp's cache evaluates each value once, and the exact
rationals reach about 3800 digits.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) [Prec_gt_0 p]

omit [Prec_gt_0 p] in
theorem inf_eq_min_real (a b : ℝ) : a ⊓ b = min a b := rfl

omit [Prec_gt_0 p] in
set_option maxHeartbeats 20000000 in
/-- Theorem 19 at `n = 8` on `H(1)`: `κ_DIV ≤ 2^{26.0}` -/
theorem kdiv8_one (hp : p = 53) : kdiv p 8 (1 * u p) ≤ 2 ^ 26 := by
  have hu := u_53 p hp
  norm_num (config := { maxSteps := 5000000 }) [kdiv, divTheta, divXi, divQb, divEps, divR, renMin, renB, vB, divPk,
    divP', gParts, divX, levX, levD, divA, divG, divT, sigmaX, Vb, us, hu, ← Finset.Ico_add_one_add_one_eq_Ioc,
    sum_Ico_eq_sum_range, sum_range_succ, Finset.range_add_one, Finset.inf'_insert, inf_eq_min_real, min_def]

omit [Prec_gt_0 p] in
set_option maxHeartbeats 20000000 in
/-- Theorem 19 at `n = 8` on `H(2)`: `κ_DIV ≤ 2^{27.48}` -/
theorem kdiv8_two (hp : p = 53) : kdiv p 8 (2 * u p) ≤ (2 : ℝ) ^ (27.48 : ℝ) := by
  have hu := u_53 p hp
  refine le_trans ?_
    (le_two_rpow (m := 187000000) (d := 1) (N := 2748) (K := 100) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel))
  norm_num (config := { maxSteps := 5000000 }) [kdiv, divTheta, divXi, divQb, divEps, divR, renMin, renB, vB, divPk,
    divP', gParts, divX, levX, levD, divA, divG, divT, sigmaX, Vb, us, hu, ← Finset.Ico_add_one_add_one_eq_Ioc,
    sum_Ico_eq_sum_range, sum_range_succ, Finset.range_add_one, Finset.inf'_insert, inf_eq_min_real, min_def]

/-- Theorem 19 at `n = 8`, `p = 53`: DIV of `H(2)` operands errs by at most `(1 + 2^{-25.5})2^{-424}|a/b|` -/
theorem div8 (hp : p = 53) (a b : ℕ → ℝ) (ha : ∀ i < 8, F p (a i)) (hb : ∀ i < 8, F p (b i))
    (haH : Htheta p 8 2 a) (hbH : Htheta p 8 2 b) (hb0 : b 0 ≠ 0) :
    |(∑ i ∈ range 8, a i) / (∑ i ∈ range 8, b i) - (divOp p 8 a b).sum| ≤
      (1 + (2 : ℝ) ^ (-25.5 : ℝ)) * (2 : ℝ) ^ (-424 : ℝ) * |(∑ i ∈ range 8, a i) / ∑ i ∈ range 8, b i| := by
  have hu := u_53 p hp
  have h := thm19 p 8 (by rw [hp]; norm_num) (by norm_num) (by rw [hu]; norm_num) (θ := 2) (by norm_num)
    (by rw [hu]; norm_num) a b ha hb haH hbH hb0
  have hk : kdiv p 8 (2 * u p) * u p ≤ (2 : ℝ) ^ (-25.5 : ℝ) :=
    (mul_u_53 p hp (kdiv8_two p hp)).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
  have h8 := mul_le_mul_of_nonneg_left hk (pow_nonneg (u_pos p).le 8)
  rw [← u8_53 p hp]
  calc u p ^ 8 + kdiv p 8 (2 * u p) * u p ^ (8 + 1) = u p ^ 8 + u p ^ 8 * (kdiv p 8 (2 * u p) * u p) := by ring
    _ ≤ u p ^ 8 + u p ^ 8 * (2 : ℝ) ^ (-25.5 : ℝ) := by linarith
    _ = (1 + (2 : ℝ) ^ (-25.5 : ℝ)) * u p ^ 8 := by ring

end ExpansionBounds
