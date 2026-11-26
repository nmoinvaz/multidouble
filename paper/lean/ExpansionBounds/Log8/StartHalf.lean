import ExpansionBounds.Log8.Start

/-!
# Theorem 42 at `n = 8` and `p = 53`: the start with the halving

Where `x_0 ≥ 2^{1023}`, step (1) takes the double word of `x/2`: each part halved and rounded by `S`, binary64's
rule, which moves a part by at most `η_0 = 2^{-1075}` and keeps the leading one. The model has no largest finite
value, so the branch is stated by its test, `2^{1023} ≤ x_0`. Here: the halved double word `x̃_h` is positive, a
double word, and `|ln x̃_h - ln(x/2)| ≤ δ_0 + 2^{-2000}` (`ln8Xh_spec`): the tail is within
`g(ρ/(1 - ρ)·x_0/2 + 7η_0) + 7η_0` of the halved lower parts' sum, and `7η_0(1 + g) ≤ 2^{-2094}·x_0/2`. With
`ln x ≥ ln 2`, `log8_start_half` gives the start's bound `E(|ln x|)` (`log8_start_halved`), from the double-word
logarithm's bound on `ln x̃_h` and AccurateDWPlusDW's bound.
-/

namespace ExpansionBounds

open Finset

/-- `τ = 2^{-2094}`: `7η_0(1 + g) ≤ τ·x_0/2` for `x_0 ≥ 2^{1023}` -/
def log8Tau : ℚ := 1 / 2 ^ 2094

/-- `N = gρ/(1 - ρ) + τ`: `|x/2 - x̃_h| ≤ N·x_0/2`, with `g = 6u/(1 - 6u)` and `ρ = 2u` -/
def log8NumH : ℚ := 6 * red8U / (1 - 6 * red8U) * (2 * red8U / (1 - 2 * red8U)) + log8Tau

/-- `D = (1 - 2ρ)/(1 - ρ) - N`: `x̃_h ≥ D·x_0/2` -/
def log8DenH : ℚ := (1 - 2 * (2 * red8U)) / (1 - 2 * red8U) - log8NumH

/-- `w_h = N/D`: `|x/2 - x̃_h| ≤ w_h x̃_h` -/
def log8Wh : ℚ := log8NumH / log8DenH

/-- The constants of the halved double word: `N ≥ 0`, `D > 0`, `w_h < 1`, `w_h/(1 - w_h) ≤ δ_0 + 2^{-2000}`, and
`ρ/(1 - ρ) + N ≤ 1`, for FastTwoSum. -/
theorem log8_halved_consts : 0 ≤ log8NumH ∧ 0 < log8DenH ∧ log8Wh < 1 ∧
    log8Wh / (1 - log8Wh) ≤ log8D0 + 1 / 2 ^ 2000 ∧ 2 * red8U / (1 - 2 * red8U) + log8NumH ≤ 1 := by
  decide +kernel

variable (p : ℤ) [Prec_gt_0 p]

/-- step (1)'s double word of the halved `x`: `FastTwoSum` of the leading part and the rounded sum of the others,
each part of `x/2` rounded by `S` -/
noncomputable def ln8Xh (S : ℝ → ℝ) (x : ℕ → ℝ) : ℝ × ℝ := ln8Xt p fun i => S (x i / 2)

/-- Step (1)'s halved double word `x̃_h` for `x > 0` in `F` on `H(2)` at `p = 53` with `x_0 ≥ 2^{1023}`, the
halving rounded by binary64's rule: its parts are in `F`, it is a double word, it is positive,
`|ln x̃_h - (ln x - ln 2)| ≤ δ_0 + 2^{-2000}`, and `ln x ≥ ln 2` -/
theorem ln8Xh_spec (hp : p = 53) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℕ → ℝ) (hx : ∀ i < 8, F p (x i)) (hH : Htheta p 8 2 x) (hX0 : 0 < ∑ i ∈ range 8, x i)
    (hbig : (2 : ℝ) ^ (1023 : ℤ) ≤ x 0) :
    F p (ln8Xh p S x).1 ∧ F p (ln8Xh p S x).2 ∧ RN p ((ln8Xh p S x).1 + (ln8Xh p S x).2) = (ln8Xh p S x).1 ∧
      0 < (ln8Xh p S x).1 + (ln8Xh p S x).2 ∧
      |Real.log ((ln8Xh p S x).1 + (ln8Xh p S x).2) - (Real.log (∑ i ∈ range 8, x i) - Real.log 2)| ≤
        ((log8D0 : ℚ) : ℝ) + 1 / 2 ^ 2000 ∧
      Real.log 2 ≤ Real.log (∑ i ∈ range 8, x i) := by
  have hu : ((red8U : ℚ) : ℝ) = u p := by unfold red8U; exact u_53_rat p hp
  have hu53 : u p = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  have hρ : (2 : ℝ) * (2 * u p) < 1 := by rw [hu53]; norm_num
  obtain ⟨cN, cD, cW1, cW, cF⟩ := log8_halved_consts
  obtain ⟨l1, l2⟩ := Htheta_lead_pos p 8 (by norm_num) 2 (by norm_num) hρ x hH hX0
  have hx0 : 0 < x 0 := lt_of_lt_of_le (mul_pos (by rw [hu53]; norm_num) hX0) l1
  have hx0h : 0 < x 0 / 2 := half_pos hx0
  -- the halved parts: each within `η_0` of `x_i/2`, the leading one kept
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = (2 : ℝ) ^ (-1075 : ℤ) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  obtain ⟨z, hzd⟩ : ∃ z : ℕ → ℝ, z = fun i => S (x i / 2) := ⟨_, rfl⟩
  have hz : ∀ i, |z i - x i / 2| ≤ η := fun i => by
    rw [hzd, hη]
    show |S (x i / 2) - x i / 2| ≤ _
    rcases hS (x i / 2) with h | ⟨-, -, h⟩
    · rw [h, sub_self, abs_zero]
      positivity
    · exact h
  have h22 : (2 : ℝ) ^ (1022 : ℤ) ≤ x 0 / 2 := by
    have e : (2 : ℝ) ^ (1023 : ℤ) = (2 : ℝ) ^ (1022 : ℤ) * 2 := by
      rw [show (1023 : ℤ) = 1022 + 1 by norm_num, zpow_add₀ two_ne_zero, zpow_one]
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), ← e]
    exact hbig
  have h4 : (4 : ℝ) ≤ x 0 := by
    have h5 : (2 : ℝ) ^ (2 : ℤ) ≤ (2 : ℝ) ^ (1023 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℤ) by norm_num]
    exact h5.trans hbig
  have hz0 : z 0 = x 0 / 2 := by
    rw [hzd]
    show S (x 0 / 2) = x 0 / 2
    rcases hS (x 0 / 2) with h | ⟨-, h, -⟩
    · exact h
    · have h1 : (2 : ℝ) ^ (-1022 : ℤ) ≤ (2 : ℝ) ^ (1022 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
      rw [abs_of_pos hx0h] at h
      exact absurd h (not_lt.mpr (h1.trans h22))
  -- `7η_0(1 + g) ≤ τ·x_0/2`, with `g = 6u/(1 - 6u)`
  have hg : (1 + u p) ^ 6 - 1 ≤ 6 * u p / (1 - 6 * u p) := by rw [hu53]; norm_num
  obtain ⟨g, hgd⟩ : ∃ g : ℝ, g = 6 * u p / (1 - 6 * u p) := ⟨_, rfl⟩
  have hg1 : 7 * (1 + g) ≤ 8 := by rw [hgd, hu53]; norm_num
  have hgg0 : 0 ≤ g := by rw [hgd, hu53]; norm_num
  have hτx : 7 * η * (1 + g) ≤ ((log8Tau : ℚ) : ℝ) * (x 0 / 2) := by
    have hτ : ((log8Tau : ℚ) : ℝ) = (2 : ℝ) ^ (-2094 : ℤ) := by
      unfold log8Tau
      rw [show (-2094 : ℤ) = -((2094 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast, ← one_div]
      simp only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat]
    have e1 : (2 : ℝ) ^ (-2094 : ℤ) * (2 : ℝ) ^ (1022 : ℤ) = 8 * η := by
      rw [hη, ← zpow_add₀ two_ne_zero, show (-2094 : ℤ) + 1022 = 3 + -1075 by norm_num,
        zpow_add₀ two_ne_zero, show (2 : ℝ) ^ (3 : ℤ) = 8 by norm_num]
    rw [hτ]
    calc 7 * η * (1 + g) = η * (7 * (1 + g)) := by ring
      _ ≤ η * 8 := mul_le_mul_of_nonneg_left hg1 hη0.le
      _ = (2 : ℝ) ^ (-2094 : ℤ) * (2 : ℝ) ^ (1022 : ℤ) := by rw [e1, mul_comm]
      _ ≤ (2 : ℝ) ^ (-2094 : ℤ) * (x 0 / 2) := mul_le_mul_of_nonneg_left h22 (by positivity)
  clear hbig h22 hη
  -- the sum of the magnitudes of the lower parts of `x`
  have hH' : Htheta p 8 2 fun i => |x i| := fun i h1 h8 => by simpa [abs_abs] using hH i h1 h8
  have ht := Htheta_tail p 8 (by norm_num) 2 (by norm_num) (by linarith) (fun i => |x i|) hH'
  have hsA : ∑ i ∈ range 8, |x i| = |x 0| + ∑ i ∈ Ico 1 8, |x i| := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by norm_num)]
  have hsX : ∑ i ∈ range 8, x i = x 0 + ∑ i ∈ Ico 1 8, x i := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by norm_num)]
  simp only [abs_abs] at ht
  rw [hsA, add_sub_cancel_left, abs_of_pos hx0] at ht
  have hA0 : 0 ≤ ∑ i ∈ Ico 1 8, |x i| := sum_nonneg fun i _ => abs_nonneg _
  rw [abs_of_nonneg hA0] at ht
  have hSA : |∑ l ∈ Ico 1 8, x l| ≤ ∑ l ∈ Ico 1 8, |x l| := abs_sum_le_sum_abs _ _
  have hdef : ln8Xh p S x = fastTwoSum p (z 0) (tailSum p z 1 6) := by rw [hzd]; rfl
  have hT : |tailSum p z 1 6 - ∑ l ∈ Ico 1 8, z l| ≤ ((1 + u p) ^ 6 - 1) * ∑ l ∈ Ico 1 8, |z l| :=
    tailSum_err p z 6 1
  have hAz : ∑ l ∈ Ico 1 8, |z l| ≤ (∑ l ∈ Ico 1 8, |x l|) / 2 + 7 * η := by
    have h1 : ∀ l ∈ Ico 1 8, |z l| ≤ |x l| / 2 + η := fun l _ => by
      have h2 := abs_sub_abs_le_abs_sub (z l) (x l / 2)
      have h3 : |x l / 2| = |x l| / 2 := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [hz l]
    refine (sum_le_sum h1).trans (le_of_eq ?_)
    rw [sum_add_distrib, ← sum_div, sum_const, Nat.card_Ico, nsmul_eq_mul]
    norm_num
  have hSz : |∑ l ∈ Ico 1 8, z l - (∑ l ∈ Ico 1 8, x l) / 2| ≤ 7 * η := by
    rw [sum_div, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun l _ => hz l).trans (le_of_eq ?_))
    rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
    norm_num
  have hAz0 : 0 ≤ ∑ l ∈ Ico 1 8, |z l| := sum_nonneg fun i _ => abs_nonneg _
  obtain ⟨T, hTd⟩ : ∃ T, T = tailSum p z 1 6 := ⟨_, rfl⟩
  obtain ⟨Sz, hSzd⟩ : ∃ Sz, Sz = ∑ l ∈ Ico 1 8, z l := ⟨_, rfl⟩
  obtain ⟨Az, hAzd⟩ : ∃ Az, Az = ∑ l ∈ Ico 1 8, |z l| := ⟨_, rfl⟩
  obtain ⟨Sg, hSd⟩ : ∃ Sg, Sg = ∑ l ∈ Ico 1 8, x l := ⟨_, rfl⟩
  obtain ⟨A, hAd⟩ : ∃ A, A = ∑ l ∈ Ico 1 8, |x l| := ⟨_, rfl⟩
  obtain ⟨X, hXd⟩ : ∃ X, X = ∑ i ∈ range 8, x i := ⟨_, rfl⟩
  rw [← hTd, ← hSzd, ← hAzd] at hT
  rw [← hAzd, ← hAd] at hAz
  rw [← hSzd, ← hSd] at hSz
  rw [← hAzd] at hAz0
  rw [← hSd, ← hAd] at hSA
  rw [← hAd] at ht hA0
  rw [← hSd, ← hXd] at hsX
  rw [← hXd] at hX0 l1 l2 ⊢
  rw [← hTd] at hdef
  -- `g`, `ρ/(1 - ρ)`, `N` and `D`
  obtain ⟨ρq, hρq⟩ : ∃ ρq : ℝ, ρq = 2 * u p / (1 - 2 * u p) := ⟨_, rfl⟩
  rw [← hgd] at hg
  rw [← hρq] at ht
  have hρq0 : 0 ≤ ρq := by rw [hρq, hu53]; norm_num
  have hN : ((log8NumH : ℚ) : ℝ) = g * ρq + ((log8Tau : ℚ) : ℝ) := by
    unfold log8NumH
    push_cast
    rw [hu, hgd, hρq]
  have hD : ((log8DenH : ℚ) : ℝ) = (1 - 2 * (2 * u p)) / (1 - 2 * u p) - ((log8NumH : ℚ) : ℝ) := by
    unfold log8DenH
    push_cast
    rw [hu]
  have hW : ((log8Wh : ℚ) : ℝ) = ((log8NumH : ℚ) : ℝ) / ((log8DenH : ℚ) : ℝ) := by
    unfold log8Wh
    push_cast
    rfl
  have hDpos : (0 : ℝ) < ((log8DenH : ℚ) : ℝ) := by exact_mod_cast cD
  have hNnn : (0 : ℝ) ≤ ((log8NumH : ℚ) : ℝ) := by exact_mod_cast cN
  -- the tail against the halved lower parts' sum
  have hd : |T - Sg / 2| ≤ ((log8NumH : ℚ) : ℝ) * (x 0 / 2) := by
    have h1 : |T - Sg / 2| ≤ |T - Sz| + |Sz - Sg / 2| := by
      have := abs_add_le (T - Sz) (Sz - Sg / 2)
      rwa [sub_add_sub_cancel] at this
    have h2 : |T - Sz| ≤ g * (A / 2 + 7 * η) :=
      hT.trans ((mul_le_mul_of_nonneg_right hg hAz0).trans (mul_le_mul_of_nonneg_left hAz hgg0))
    have h3 : g * (A / 2) ≤ g * (ρq * (x 0 / 2)) := mul_le_mul_of_nonneg_left (by linarith) hgg0
    rw [hN]
    linarith
  -- FastTwoSum is exact
  have hTF : F p T := by
    rw [hTd]
    exact F_RN p _
  have hz0F : F p (z 0) := by
    rw [hz0, show x 0 / 2 = (2 : ℝ) ^ (-1 : ℤ) * x 0 by rw [zpow_neg_one]; ring]
    exact F_zpow_mul p (-1) (hx 0 (by norm_num))
  have hTx : |T| ≤ |z 0| := by
    rw [hz0, abs_of_pos hx0h]
    have h1 := abs_sub_abs_le_abs_sub T (Sg / 2)
    have h2 : |Sg / 2| ≤ ρq * (x 0 / 2) := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have h3 := (Rat.cast_le (K := ℝ)).mpr cF
    push_cast at h3
    rw [hu, ← hρq] at h3
    have h4 := mul_le_mul_of_nonneg_right h3 hx0h.le
    linarith
  have hsum : (ln8Xh p S x).1 + (ln8Xh p S x).2 = z 0 + T := by
    rw [hdef]
    exact fastTwoSum_add p (by omega) hz0F hTF hTx
  have hfst : (ln8Xh p S x).1 = RN p (z 0 + T) := by rw [hdef]; rfl
  -- `x̃_h ≥ D·x_0/2 > 0`
  have hXh : X / 2 = x 0 / 2 + Sg / 2 := by rw [hsX]; ring
  have hXlow : x 0 / 2 * ((1 - 2 * (2 * u p)) / (1 - 2 * u p)) ≤ X / 2 := by
    rw [hu53] at l2 ⊢
    norm_num at l2 ⊢
    linarith
  obtain ⟨d1, d2⟩ := abs_le.mp hd
  have hlow : ((log8DenH : ℚ) : ℝ) * (x 0 / 2) ≤ z 0 + T := by
    rw [hD, hz0]
    rw [hXh] at hXlow
    linarith
  have hpos : 0 < z 0 + T := lt_of_lt_of_le (mul_pos hDpos hx0h) hlow
  -- `|x/2 - x̃_h| ≤ w_h x̃_h`
  have hw : |X / 2 - (z 0 + T)| ≤ ((log8Wh : ℚ) : ℝ) * (z 0 + T) := by
    rw [show X / 2 - (z 0 + T) = -(T - Sg / 2) by rw [hXh, hz0]; ring, abs_neg, hW]
    refine hd.trans ?_
    calc ((log8NumH : ℚ) : ℝ) * (x 0 / 2) =
          ((log8NumH : ℚ) : ℝ) / ((log8DenH : ℚ) : ℝ) * (((log8DenH : ℚ) : ℝ) * (x 0 / 2)) := by
          rw [← mul_assoc, div_mul_cancel₀ _ hDpos.ne']
      _ ≤ ((log8NumH : ℚ) : ℝ) / ((log8DenH : ℚ) : ℝ) * (z 0 + T) :=
          mul_le_mul_of_nonneg_left hlow (div_nonneg hNnn hDpos.le)
  have hlog := log_near hpos (by linarith : 0 < X / 2) hw (by exact_mod_cast cW1)
  rw [Real.log_div hX0.ne' two_ne_zero] at hlog
  -- `x ≥ 2`
  have hX2 : 2 ≤ X := by
    rw [hu53] at l2
    norm_num at l2
    linarith
  have hcW := (Rat.cast_le (K := ℝ)).mpr cW
  push_cast at hcW
  rw [hsum]
  refine ⟨by rw [hfst]; exact F_RN p _, by rw [hdef]; exact F_RN p _, by rw [hfst], hpos, ?_,
    Real.log_le_log (by norm_num) hX2⟩
  rw [abs_sub_comm]
  exact hlog.trans hcW

/-- The start of `LOG_{8,6,43,4}` with the halving, `x_0 ≥ 2^{1023}`: for `x > 0` in `F` on `H(2)` at `p = 53`
with `|ln x| ≤ 745.2`, `W` within `ε_DW|ln x̃_h| + Φ_DW` of `ln x̃_h`, Proposition 44's bound with its quoted
constants on the halved double word, and `y_0` within `e_A|W + c_L|` of `W + c_L`, AccurateDWPlusDW's bound with
`e_A = 3u²/(1 - 4u)` and `c_L` the double-double `ln 2`: `y_0` is within `E(|ln x|)` of `ln x`, the hypothesis `hE`
of `thm42_8` -/
theorem log8_start_halved (hp : p = 53) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℕ → ℝ) (hx : ∀ i < 8, F p (x i)) (hH : Htheta p 8 2 x) (hX0 : 0 < ∑ i ∈ range 8, x i)
    (hX : |Real.log (∑ i ∈ range 8, x i)| ≤ 7452 / 10) (hbig : (2 : ℝ) ^ (1023 : ℤ) ≤ x 0) (W Y0 : ℝ)
    (hW : |W - Real.log ((ln8Xh p S x).1 + (ln8Xh p S x).2)| ≤
      15351 / 1000 * u p ^ 2 * |Real.log ((ln8Xh p S x).1 + (ln8Xh p S x).2)| + 1 / 2 ^ 1071)
    (hA : |Y0 - (W + (((dyQ log8CL0 : ℚ) : ℝ) + ((dyQ log8CL1 : ℚ) : ℝ)))| ≤
      3 * u p ^ 2 / (1 - 4 * u p) * |W + (((dyQ log8CL0 : ℚ) : ℝ) + ((dyQ log8CL1 : ℚ) : ℝ))|) :
    |Y0 - Real.log (∑ i ∈ range 8, x i)| ≤ log8E |Real.log (∑ i ∈ range 8, x i)| := by
  obtain ⟨-, -, -, -, hd, hl2⟩ := ln8Xh_spec p hp S hS x hx hH hX0 hbig
  exact log8_start_half p hp hl2 ((le_abs_self _).trans hX) hd hW hA

end ExpansionBounds
