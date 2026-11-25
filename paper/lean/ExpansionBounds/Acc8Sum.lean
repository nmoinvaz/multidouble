import ExpansionBounds.Acc8
import ExpansionBounds.AccSum

/-!
# Theorem 27's thresholds at `n = 8` and `p = 53`: `H(1)` and sums

After Theorem 27 the appendix quotes the largest `K` whose second term is at most `u^8W/8` and at most `u^8W`: `38`
and `50` for products on `H(2)` (`Acc8.lean`), `40` and `52` on `H(1)`, and for sums of octo-doubles `41` and `53` on
`H(2)` and `42` and `54` on `H(1)`, as `acc_bound.py` finds them. Each is proved here for every `K` up to it, with
the next `K` above the threshold. `Φ` on `H(1)` is evaluated once, at `K = 1024`, by the kernel on its rational
mirror, and the sums take the `Φ` of products, which is at least theirs.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ)

/-- `Φ ≤ 2^{-47}u^8` at `K = 1024` on `H(1)`, by the kernel on `accPhiQ` -/
theorem accPhi8_one_1024 (hp : p = 53) : accPhi p 8 1 1024 ≤ u p ^ 8 / 2 ^ 47 := by
  have h := u_53_rat p hp
  have hq : accPhiQ (1 / 9007199254740992) 8 1 1024 ≤ (1 / 9007199254740992) ^ 8 / 2 ^ 47 := by decide +kernel
  have hc := cast_accPhi p 8 h 1 1024
  push_cast at hc
  rw [← h, ← hc]
  exact_mod_cast hq

/-- `Φ ≤ 2^{-47}u^8` for `K ≤ 1024` on `H(1)` -/
theorem accPhi8_one (hp : p = 53) {K : ℕ} (hK : K ≤ 1024) : accPhi p 8 1 K ≤ u p ^ 8 / 2 ^ 47 :=
  (accPhi_mono p 8 (by norm_num) hK (acc8_hK p hp le_rfl)).trans (accPhi8_one_1024 p hp)

/-! ### Products on `H(1)` -/

/-- products on `H(1)`: the second term is at most `u^8W/8` for `K ≤ 40` and `u^8W` for `K ≤ 52`, and above them at
`K = 41` and `53` -/
theorem accC8_h1 (hp : p = 53) :
    (∀ K ≤ 40, accC p 8 1 K ≤ u p ^ 8 / 8) ∧ (∀ K ≤ 52, accC p 8 1 K ≤ u p ^ 8) ∧
      u p ^ 8 / 8 < accC p 8 1 41 ∧ u p ^ 8 < accC p 8 1 53 := by
  have hu := u_53 p hp
  have hle : ∀ K ≤ 1024, accC p 8 1 K ≤ (1 + u p ^ 8) * accLevProd p 8 1 K + u p ^ 8 / 2 ^ 47 := fun K hK => by
    unfold accC
    exact add_le_add le_rfl (accPhi8_one p hp hK)
  have hge : ∀ K ≤ 1024, (1 + u p ^ 8) * accLevProd p 8 1 K ≤ accC p 8 1 K := fun K hK => by
    unfold accC
    exact le_add_of_nonneg_right (accPhi_nonneg p 8 (by norm_num) (acc8_hK p hp hK))
  refine ⟨fun K hK => ?_, fun K hK => ?_, ?_, ?_⟩
  · refine (accC_mono p 8 (by norm_num) hK (acc8_hK p hp (by norm_num))).trans ((hle 40 (by norm_num)).trans ?_)
    norm_num [accLevProd, accE, accGamma, accTau, mulL, thmL, thmD, hatAmul, mulT, thmDelta, rise, hu,
      sum_Ico_eq_sum_range, sum_range_succ, prod_range_succ, max_def, Nat.choose]
  · refine (accC_mono p 8 (by norm_num) hK (acc8_hK p hp (by norm_num))).trans ((hle 52 (by norm_num)).trans ?_)
    norm_num [accLevProd, accE, accGamma, accTau, mulL, thmL, thmD, hatAmul, mulT, thmDelta, rise, hu,
      sum_Ico_eq_sum_range, sum_range_succ, prod_range_succ, max_def, Nat.choose]
  · refine lt_of_lt_of_le ?_ (hge 41 (by norm_num))
    norm_num [accLevProd, accE, accGamma, accTau, mulL, thmL, thmD, hatAmul, mulT, thmDelta, rise, hu,
      sum_Ico_eq_sum_range, sum_range_succ, prod_range_succ, max_def, Nat.choose]
  · refine lt_of_lt_of_le ?_ (hge 53 (by norm_num))
    norm_num [accLevProd, accE, accGamma, accTau, mulL, thmL, thmD, hatAmul, mulT, thmDelta, rise, hu,
      sum_Ico_eq_sum_range, sum_range_succ, prod_range_succ, max_def, Nat.choose]

/-! ### Sums -/

/-- `c^X_K ≤ (1 + u^8)Ē_lev + 2^{-47}u^8` for `K ≤ 1024`, from the `Φ` of products -/
theorem accCX8_le (hp : p = 53) {θ : ℝ} (hθ : 0 ≤ θ) (hΦ : ∀ K ≤ 1024, accPhi p 8 θ K ≤ u p ^ 8 / 2 ^ 47) {K : ℕ}
    (hK : K ≤ 1024) :
    accCX p 8 θ K ≤ (1 + u p ^ 8) * accE (accTauX p 8 θ) 1 (accGamma p 8 K) (u p) 8 K + u p ^ 8 / 2 ^ 47 := by
  unfold accCX
  exact add_le_add le_rfl ((accPhiX_le p 8 hθ (acc8_hK p hp hK)).trans (hΦ K hK))

/-- `(1 + u^8)Ē_lev ≤ c^X_K` for `K ≤ 1024` -/
theorem accCX8_ge (hp : p = 53) {θ : ℝ} (hθ : 0 ≤ θ) {K : ℕ} (hK : K ≤ 1024) :
    (1 + u p ^ 8) * accE (accTauX p 8 θ) 1 (accGamma p 8 K) (u p) 8 K ≤ accCX p 8 θ K := by
  unfold accCX
  exact le_add_of_nonneg_right (accPhiX_nonneg p 8 hθ (acc8_hK p hp hK))

/-- sums on `H(2)`: the second term is at most `u^8W/8` for `K ≤ 41` and `u^8W` for `K ≤ 53`, and above them at
`K = 42` and `54` -/
theorem accCX8_two (hp : p = 53) :
    (∀ K ≤ 41, accCX p 8 2 K ≤ u p ^ 8 / 8) ∧ (∀ K ≤ 53, accCX p 8 2 K ≤ u p ^ 8) ∧
      u p ^ 8 / 8 < accCX p 8 2 42 ∧ u p ^ 8 < accCX p 8 2 54 := by
  have hu := u_53 p hp
  have hΦ : ∀ K ≤ 1024, accPhi p 8 2 K ≤ u p ^ 8 / 2 ^ 47 := fun K hK => accPhi8 p hp hK
  refine ⟨fun K hK => ?_, fun K hK => ?_, ?_, ?_⟩
  · refine (accCX_mono p 8 (by norm_num) hK (acc8_hK p hp (by norm_num))).trans
      ((accCX8_le p hp (by norm_num) hΦ (by norm_num)).trans ?_)
    norm_num [accE, accGamma, accTauX, rise, hu, sum_range_succ, prod_range_succ, Nat.choose]
  · refine (accCX_mono p 8 (by norm_num) hK (acc8_hK p hp (by norm_num))).trans
      ((accCX8_le p hp (by norm_num) hΦ (by norm_num)).trans ?_)
    norm_num [accE, accGamma, accTauX, rise, hu, sum_range_succ, prod_range_succ, Nat.choose]
  · refine lt_of_lt_of_le ?_ (accCX8_ge p hp (by norm_num) (by norm_num))
    norm_num [accE, accGamma, accTauX, rise, hu, sum_range_succ, prod_range_succ, Nat.choose]
  · refine lt_of_lt_of_le ?_ (accCX8_ge p hp (by norm_num) (by norm_num))
    norm_num [accE, accGamma, accTauX, rise, hu, sum_range_succ, prod_range_succ, Nat.choose]

/-- sums on `H(1)`: the second term is at most `u^8W/8` for `K ≤ 42` and `u^8W` for `K ≤ 54`, and above them at
`K = 43` and `55` -/
theorem accCX8_one (hp : p = 53) :
    (∀ K ≤ 42, accCX p 8 1 K ≤ u p ^ 8 / 8) ∧ (∀ K ≤ 54, accCX p 8 1 K ≤ u p ^ 8) ∧
      u p ^ 8 / 8 < accCX p 8 1 43 ∧ u p ^ 8 < accCX p 8 1 55 := by
  have hu := u_53 p hp
  have hΦ : ∀ K ≤ 1024, accPhi p 8 1 K ≤ u p ^ 8 / 2 ^ 47 := fun K hK => accPhi8_one p hp hK
  refine ⟨fun K hK => ?_, fun K hK => ?_, ?_, ?_⟩
  · refine (accCX_mono p 8 (by norm_num) hK (acc8_hK p hp (by norm_num))).trans
      ((accCX8_le p hp (by norm_num) hΦ (by norm_num)).trans ?_)
    norm_num [accE, accGamma, accTauX, rise, hu, sum_range_succ, prod_range_succ, Nat.choose]
  · refine (accCX_mono p 8 (by norm_num) hK (acc8_hK p hp (by norm_num))).trans
      ((accCX8_le p hp (by norm_num) hΦ (by norm_num)).trans ?_)
    norm_num [accE, accGamma, accTauX, rise, hu, sum_range_succ, prod_range_succ, Nat.choose]
  · refine lt_of_lt_of_le ?_ (accCX8_ge p hp (by norm_num) (by norm_num))
    norm_num [accE, accGamma, accTauX, rise, hu, sum_range_succ, prod_range_succ, Nat.choose]
  · refine lt_of_lt_of_le ?_ (accCX8_ge p hp (by norm_num) (by norm_num))
    norm_num [accE, accGamma, accTauX, rise, hu, sum_range_succ, prod_range_succ, Nat.choose]

variable [Prec_gt_0 p]

/-- Theorem 27 at `n = 8`, `p = 53` for sums: `K ≤ 53` octo-doubles on `H(2)`, accumulated by ADDX and FINISH, give
`|Z - x| ≤ 2^{-424}(|Z| + W)` with `W = ∑|a_0|`, and `K ≤ 41` give `|Z - x| ≤ 2^{-424}|Z| + 2^{-427}W` -/
theorem acc8_sum (hp : p = 53) (K : ℕ) (hK1 : 1 ≤ K) (hK : K ≤ 53) (a : ℕ → ℕ → ℝ)
    (ha : ∀ k ∈ Icc 1 K, ∀ i < 8, F p (a k i)) (hHa : ∀ k ∈ Icc 1 K, Htheta p 8 2 (a k)) :
    |∑ k ∈ Icc 1 K, ∑ i ∈ range 8, a k i - ∑ i ∈ range 8, finishR p 8 (accLevX p 8 a K) 8 i| ≤
        (2 : ℝ) ^ (-424 : ℝ) * (|∑ k ∈ Icc 1 K, ∑ i ∈ range 8, a k i| + ∑ k ∈ Icc 1 K, |a k 0|) ∧
      (K ≤ 41 → |∑ k ∈ Icc 1 K, ∑ i ∈ range 8, a k i - ∑ i ∈ range 8, finishR p 8 (accLevX p 8 a K) 8 i| ≤
        (2 : ℝ) ^ (-424 : ℝ) * |∑ k ∈ Icc 1 K, ∑ i ∈ range 8, a k i| +
          (2 : ℝ) ^ (-427 : ℝ) * ∑ k ∈ Icc 1 K, |a k 0|) := by
  have h := thm27_addx p 8 (by rw [hp]; norm_num) (by norm_num) 2 (by norm_num) K hK1 (acc8_hK p hp (by omega)) a
    ha hHa
  have hW : 0 ≤ ∑ k ∈ Icc 1 K, |a k 0| := sum_nonneg fun k _ => abs_nonneg _
  obtain ⟨h8, h1, -, -⟩ := accCX8_two p hp
  refine ⟨?_, fun hK41 => ?_⟩
  · rw [← u8_53 p hp]
    have := mul_le_mul_of_nonneg_right (h1 K hK) hW
    linarith
  · rw [← u8_53 p hp, ← u8_div8_53 p hp]
    have := mul_le_mul_of_nonneg_right (h8 K hK41) hW
    linarith

end ExpansionBounds
