import ExpansionBounds.Kappa8
import ExpansionBounds.Sloppy

/-!
# Theorem 30 (`thm:sloppy`) at `n = 8` and `p = 53`

SLOPPY-MUL's constant `R_s + Δ_8u` evaluated in rational arithmetic, as `sloppy_consts.py` computes it:
`R_s + Δ_8u ≤ 2^{30.4117}` on `H(1)` and `2^{31.9242}` on `H(2)`, of which `Δ_8u ≤ 2^{-50.41}` and `2^{-41.41}`, so
`|ab - x| ≤ 2^{30.4117}u^8|a_0b_0|` and `2^{31.9242}u^8|a_0b_0|`. The four-decimal powers of two are bounded below
through `c^{10000} ≤ 2^{10000x}`.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) [Prec_gt_0 p]

omit [Prec_gt_0 p] in
/-- `y ≤ 2^x` gives `yu ≤ 2^{x - 53}` at `p = 53` -/
theorem mul_u_53 (hp : p = 53) {y x : ℝ} (h : y ≤ (2 : ℝ) ^ x) : y * u p ≤ (2 : ℝ) ^ (x - 53) := by
  rw [Real.rpow_sub (by norm_num), div_eq_mul_inv, u_53 p hp, show (53 : ℝ) = ((53 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  exact mul_le_mul h (by norm_num) (by norm_num) (by positivity)

omit [Prec_gt_0 p] in
/-- Theorem 30 at `n = 8` for `θ = 1`: `R_s + Δ_8u ≤ 2^{30.4117}` and `Δ_8u ≤ 2^{-50.41}` -/
theorem sloppy8_one (hp : p = 53) :
    (((7 + 1) ^ 2 : ℕ) : ℝ) * sloppyL p 7 1 7 + thmDelta p (7 + 1) 1 * u p ≤ (2 : ℝ) ^ (30.4117 : ℝ) ∧
      thmDelta p (7 + 1) 1 * u p ≤ (2 : ℝ) ^ (-50.41 : ℝ) := by
  have hu := u_53 p hp
  constructor
  · refine le_trans ?_
      (le_two_rpow (m := 1428300000) (d := 1) (N := 304117) (K := 10000) (by norm_num) (by norm_num) (by norm_num)
        (by decide +kernel))
    simp only [sloppyL, thmL, thmD, hatAsloppy, hatAmul, mulT, thmDelta, sum_Ico_eq_sum_range, sum_range_succ,
      sum_range_zero, hu]
    norm_num
  · have h := mul_u_53 p hp (le_trans (show thmDelta p (7 + 1) 1 ≤ 6000001 / 1000000 by
      simp only [thmDelta, sum_Ico_eq_sum_range, sum_range_succ, sum_range_zero, hu]; norm_num)
      (le_two_rpow (m := 6000001) (d := 1000000) (N := 259) (x := 2.59) (K := 100) (by norm_num) (by norm_num)
        (by norm_num) (by decide +kernel)))
    rwa [show (2.59 : ℝ) - 53 = -50.41 by norm_num] at h

omit [Prec_gt_0 p] in
/-- Theorem 30 at `n = 8` for `θ = 2`: `R_s + Δ_8u ≤ 2^{31.9242}` and `Δ_8u ≤ 2^{-41.41}` -/
theorem sloppy8_two (hp : p = 53) :
    (((7 + 1) ^ 2 : ℕ) : ℝ) * sloppyL p 7 2 7 + thmDelta p (7 + 1) 2 * u p ≤ (2 : ℝ) ^ (31.9242 : ℝ) ∧
      thmDelta p (7 + 1) 2 * u p ≤ (2 : ℝ) ^ (-41.41 : ℝ) := by
  have hu := u_53 p hp
  constructor
  · refine le_trans ?_
      (le_two_rpow (m := 4075120000) (d := 1) (N := 319242) (K := 10000) (by norm_num) (by norm_num) (by norm_num)
        (by decide +kernel))
    simp only [sloppyL, thmL, thmD, hatAsloppy, hatAmul, mulT, thmDelta, sum_Ico_eq_sum_range, sum_range_succ,
      sum_range_zero, hu]
    norm_num
  · have h := mul_u_53 p hp (le_trans (show thmDelta p (7 + 1) 2 ≤ 3072001 / 1000 by
      simp only [thmDelta, sum_Ico_eq_sum_range, sum_range_succ, sum_range_zero, hu]; norm_num)
      (le_two_rpow (m := 3072001) (d := 1000) (N := 1159) (x := 11.59) (K := 100) (by norm_num) (by norm_num)
        (by norm_num) (by decide +kernel)))
    rwa [show (11.59 : ℝ) - 53 = -41.41 by norm_num] at h

/-- Theorem 30 (b) at `n = 8`, `p = 53`: SLOPPY-MUL errs by at most `2^{30.4117}u^8|a_0b_0|` on `H(1)` operands and
`2^{31.9242}u^8|a_0b_0|` on `H(2)` operands -/
theorem sloppy8_mul (hp : p = 53) (a b : ℕ → ℝ) (ha : ∀ i ≤ 7, F p (a i)) (hb : ∀ j ≤ 7, F p (b j)) :
    (Htheta p 8 1 a → Htheta p 8 1 b →
      |(∑ i ∈ range 8, a i) * (∑ j ∈ range 8, b j) - (sloppyOp p 7 a b).sum| ≤
        (2 : ℝ) ^ (30.4117 : ℝ) * u p ^ 8 * |a 0 * b 0|) ∧
    (Htheta p 8 2 a → Htheta p 8 2 b →
      |(∑ i ∈ range 8, a i) * (∑ j ∈ range 8, b j) - (sloppyOp p 7 a b).sum| ≤
        (2 : ℝ) ^ (31.9242 : ℝ) * u p ^ 8 * |a 0 * b 0|) := by
  have hu := u_53 p hp
  have hQ : ((7 : ℕ) + 1 : ℝ) ^ 2 * u p < 1 := by rw [hu]; norm_num
  refine ⟨fun hHa hHb => ?_, fun hHa hHb => ?_⟩
  · refine (thm30b p 7 (by rw [hp]; norm_num) (by norm_num) hQ 1 (by norm_num) a b ha hb hHa hHb).1.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (sloppy8_one p hp).1 (by positivity))
      (abs_nonneg _)
  · refine (thm30b p 7 (by rw [hp]; norm_num) (by norm_num) hQ 2 (by norm_num) a b ha hb hHa hHb).1.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (sloppy8_two p hp).1 (by positivity))
      (abs_nonneg _)

end ExpansionBounds
