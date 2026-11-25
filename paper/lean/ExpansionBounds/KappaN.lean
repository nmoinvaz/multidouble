import ExpansionBounds.Sloppy8

/-!
# Table II (`tab:main`): Theorem 15's `κ_n u` at `n = 2`, `4`, `8` and `12` and `p = 53`

Theorem 15's `κ` on `H(2)` evaluated in rational arithmetic, as `constants.py` computes it, times `u`: at most
`2^{-48.4}`, `2^{-43.8}`, `2^{-33.0}` and `2^{-19.5}` for ADD and MULF, `2^{-49.1}`, `2^{-46.6}`, `2^{-42.4}` and
`2^{-38.4}` for ADDF, and `2^{-45.8}`, `2^{-37.3}`, `2^{-15.0}` and `2^{12.6}` for MUL. The rows at `n = 8` follow
from Table IV. For MUL `κ_n u < 1` at `n = 10` and `κ_n u > 1` at `n = 11` and `12`: from eleven parts the second term
of the bound is the larger one. Each power of two is bounded below through `c^{10} ≤ 2^{10x}`.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ)

/-- Theorem 15's `κ` for MUL on `H(2)` -/
noncomputable def kappaMul (n : ℕ) : ℝ :=
  thmKappa p n (mulL p n 2) (((n ^ 2 + n - 1 : ℕ) : ℝ) * mulL p n 2 n + thmDelta p n 2)

/-- Theorem 15's `κ` for ADD and MULF on `H(2)` -/
noncomputable def kappaPair (n : ℕ) : ℝ := thmKappa p n (pairL p n 2) (((n - 1 : ℕ) : ℝ) * pairL p n 2 n)

/-- Theorem 15's `κ` for ADDF on `H(2)` -/
noncomputable def kappaAddf (n : ℕ) : ℝ := thmKappa p n (addfL p n 2) 0

/-- `κ ≤ m/d` and `m^K ≤ 2^{K(x + 53)}d^K` give `κu ≤ 2^x` at `p = 53` -/
theorem kappa_u_le (hp : p = 53) {κ x : ℝ} {m d N K : ℕ} (hd : 0 < d) (hK : K ≠ 0) (hN : (x + 53) * K = N)
    (h : m ^ K ≤ 2 ^ N * d ^ K) (hκ : κ ≤ (m : ℝ) / d) : κ * u p ≤ (2 : ℝ) ^ x := by
  have h2 := mul_u_53 p hp (hκ.trans (le_two_rpow hd hK hN h))
  rwa [add_sub_cancel_right] at h2

/-- `κ ≤ 2^y` with `y ≤ x + 53` gives `κu ≤ 2^x` at `p = 53` -/
theorem kappa_u_le_of_rpow (hp : p = 53) {κ x y : ℝ} (hκ : κ ≤ (2 : ℝ) ^ y) (hy : y ≤ x + 53) :
    κ * u p ≤ (2 : ℝ) ^ x :=
  (mul_u_53 p hp hκ).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))

/-- Table II for ADD and MULF: `κ_n u ≤ 2^{-48.4}`, `2^{-43.8}`, `2^{-33.0}` and `2^{-19.5}` at `n = 2`, `4`, `8` and
`12` -/
theorem table2_pair (hp : p = 53) :
    kappaPair p 2 * u p ≤ (2 : ℝ) ^ (-48.4 : ℝ) ∧ kappaPair p 4 * u p ≤ (2 : ℝ) ^ (-43.8 : ℝ) ∧
      kappaPair p 8 * u p ≤ (2 : ℝ) ^ (-33 : ℝ) ∧ kappaPair p 12 * u p ≤ (2 : ℝ) ^ (-19.5 : ℝ) := by
  have hu := u_53 p hp
  refine ⟨?_, ?_, kappa_u_le_of_rpow p hp (kappa8_pair p hp).2 (by norm_num), ?_⟩
  · refine kappa_u_le p hp (m := 24) (d := 1) (N := 46) (K := 10) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) ?_
    simp only [kappaPair, thmKappa, pairL, thmL, thmD, hatApair, id, sum_range_succ, sum_range_zero, hu]
    norm_num
  · refine kappa_u_le p hp (m := 577) (d := 1) (N := 92) (K := 10) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) ?_
    simp only [kappaPair, thmKappa, pairL, thmL, thmD, hatApair, id, sum_range_succ, sum_range_zero, hu]
    norm_num
  · refine kappa_u_le p hp (m := 11700000000) (d := 1) (N := 335) (K := 10) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel) ?_
    simp only [kappaPair, thmKappa, pairL, thmL, thmD, hatApair, id, sum_range_succ, sum_range_zero, hu]
    norm_num

/-- Table II for ADDF: `κ_n u ≤ 2^{-49.1}`, `2^{-46.6}`, `2^{-42.4}` and `2^{-38.4}` at `n = 2`, `4`, `8` and `12` -/
theorem table2_addf (hp : p = 53) :
    kappaAddf p 2 * u p ≤ (2 : ℝ) ^ (-49.1 : ℝ) ∧ kappaAddf p 4 * u p ≤ (2 : ℝ) ^ (-46.6 : ℝ) ∧
      kappaAddf p 8 * u p ≤ (2 : ℝ) ^ (-42.4 : ℝ) ∧ kappaAddf p 12 * u p ≤ (2 : ℝ) ^ (-38.4 : ℝ) := by
  have hu := u_53 p hp
  refine ⟨?_, ?_, kappa_u_le_of_rpow p hp (kappa8_addf p hp).2 (by norm_num), ?_⟩
  · refine kappa_u_le p hp (m := 141) (d := 10) (N := 39) (K := 10) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) ?_
    simp only [kappaAddf, thmKappa, addfL, sum_range_succ, sum_range_zero, hu]
    norm_num
  · refine kappa_u_le p hp (m := 83) (d := 1) (N := 64) (K := 10) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) ?_
    simp only [kappaAddf, thmKappa, addfL, sum_range_succ, sum_range_zero, hu]
    norm_num
  · refine kappa_u_le p hp (m := 24600) (d := 1) (N := 146) (K := 10) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) ?_
    simp only [kappaAddf, thmKappa, addfL, sum_range_succ, sum_range_zero, hu]
    norm_num

/-- Table II for MUL: `κ_n u ≤ 2^{-45.8}`, `2^{-37.3}`, `2^{-15.0}` and `2^{12.6}` at `n = 2`, `4`, `8` and `12` -/
theorem table2_mul (hp : p = 53) :
    kappaMul p 2 * u p ≤ (2 : ℝ) ^ (-45.8 : ℝ) ∧ kappaMul p 4 * u p ≤ (2 : ℝ) ^ (-37.3 : ℝ) ∧
      kappaMul p 8 * u p ≤ (2 : ℝ) ^ (-15 : ℝ) ∧ kappaMul p 12 * u p ≤ (2 : ℝ) ^ (12.6 : ℝ) := by
  have hu := u_53 p hp
  refine ⟨?_, ?_, kappa_u_le_of_rpow p hp (kappa8_mul p hp).2 (by norm_num), ?_⟩
  · refine kappa_u_le p hp (m := 139) (d := 1) (N := 72) (K := 10) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) ?_
    simp only [kappaMul, thmKappa, mulL, thmL, thmD, hatAmul, mulT, thmDelta, sum_Ico_eq_sum_range, sum_range_succ,
      sum_range_zero, hu]
    norm_num
  · refine kappa_u_le p hp (m := 52700) (d := 1) (N := 157) (K := 10) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel) ?_
    simp only [kappaMul, thmKappa, mulL, thmL, thmD, hatAmul, mulT, thmDelta, sum_Ico_eq_sum_range, sum_range_succ,
      sum_range_zero, hu]
    norm_num
  · refine kappa_u_le p hp (m := 53000000000000000000) (d := 1) (N := 656) (K := 10) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel) ?_
    simp only [kappaMul, thmKappa, mulL, thmL, thmD, hatAmul, mulT, thmDelta, sum_Ico_eq_sum_range, sum_range_succ,
      sum_range_zero, hu]
    norm_num

/-- Table II's caption: for MUL the second term `κ_n u^{n+1}M` is below `u^n M` at `n = 10` and above it at `n = 11`
and `12` -/
theorem table2_mul_crossover (hp : p = 53) :
    kappaMul p 10 * u p < 1 ∧ 1 < kappaMul p 11 * u p ∧ 1 < kappaMul p 12 * u p := by
  have hu := u_53 p hp
  refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [kappaMul, thmKappa, mulL, thmL, thmD, hatAmul, mulT, thmDelta, sum_Ico_eq_sum_range, sum_range_succ,
        sum_range_zero, hu]
      norm_num

end ExpansionBounds
