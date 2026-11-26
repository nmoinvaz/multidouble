import ExpansionBounds.Log8.Driver

/-!
# Theorem 42 at `n = 8` and `p = 53`: the start

Step (1) of `LOG_{8,6,43,4}` forms the double word `x̃ = FastTwoSum(x_0, RN(x_1 + RN(x_2 + …)))` and takes its
double-word logarithm `y_0`. Here: the tail is the sum of seven parts rounded six times, within
`((1 + u)^6 - 1)∑_{i ≥ 1}|x_i|` of their sum (`tailSum_err`); `FastTwoSum` is exact and returns a double word; and
`|ln x - ln x̃| ≤ δ_0` for `x > 0` on `H(2)` (`ln8Xt_spec`). So a `y_0` within `ε_DW|ln x̃| + Φ_DW` of `ln x̃`, the
bound of Proposition 44 with its quoted constants, is within `E(|ln x|)` of `ln x` (`log8_start`): the hypothesis
of `thm42_8`, for the branch of step (1) without the halving (`x_0 < 2^{1023}` in binary64). For the branch with
the halving, `log8_start_half` is the accounting of the paper's proof, from AccurateDWPlusDW's bound and the
distance of the halved double word's logarithm from `ln(x/2)`, which is a hypothesis there.
-/

namespace ExpansionBounds

open Finset

/-- `|ln X - ln X̃| ≤ w/(1 - w)` for positive `X`, `X̃` with `|X - X̃| ≤ wX̃` and `w < 1` -/
theorem log_near {X Xt w : ℝ} (hXt : 0 < Xt) (hX : 0 < X) (hw : |X - Xt| ≤ w * Xt) (hw1 : w < 1) :
    |Real.log X - Real.log Xt| ≤ w / (1 - w) := by
  have hw0 : 0 ≤ w := by
    by_contra h
    have := abs_nonneg (X - Xt)
    nlinarith
  have ht : |(X - Xt) / Xt| ≤ w := by
    rw [abs_div, abs_of_pos hXt, div_le_iff₀ hXt]
    exact hw
  have h := log_lip (x := (X - Xt) / Xt) (y := 0) ht (by simpa using hw0) hw1
  have e : 1 + (X - Xt) / Xt = X / Xt := by
    field_simp
    ring
  rw [e, add_zero, Real.log_one, sub_zero, sub_zero, Real.log_div hX.ne' hXt.ne'] at h
  exact h.trans (div_le_div_of_nonneg_right ht (by linarith))

/-- The start's constants: `ε_DW δ_0 + δ_0 + Φ_DW ≤ e₀` and `ε_DW ≤ e₁`, with `ε_DW`, `δ_0` nonnegative. -/
theorem log8_start_consts : log8EpsDW * log8D0 + log8D0 + 1 / 2 ^ 1071 ≤ log8E0 ∧ log8EpsDW ≤ log8E1 ∧
    0 ≤ log8EpsDW ∧ 0 ≤ log8D0 := by
  decide +kernel

variable (p : ℤ) [Prec_gt_0 p]

/-- step (1)'s tail from part `i`: `RN(x_i + RN(x_{i+1} + … + RN(x_{i+j-1} + x_{i+j})))`, `j` roundings -/
noncomputable def tailSum (x : ℕ → ℝ) : ℕ → ℕ → ℝ
  | i, 0 => x i
  | i, j + 1 => RN p (x i + tailSum x (i + 1) j)

/-- The sum of `j + 1` parts rounded `j` times is within `((1 + u)^j - 1)∑|x_l|` of their sum. -/
theorem tailSum_err (x : ℕ → ℝ) : ∀ j i, |tailSum p x i j - ∑ l ∈ Ico i (i + j + 1), x l| ≤
    ((1 + u p) ^ j - 1) * ∑ l ∈ Ico i (i + j + 1), |x l|
  | 0, i => by simp [tailSum]
  | j + 1, i => by
    have ih := tailSum_err x j (i + 1)
    have hu := u_pos p
    have hsum : ∑ l ∈ Ico i (i + (j + 1) + 1), x l = x i + ∑ l ∈ Ico (i + 1) (i + 1 + j + 1), x l := by
      rw [sum_eq_sum_Ico_succ_bot (by omega), show i + (j + 1) + 1 = i + 1 + j + 1 by omega]
    have habs : ∑ l ∈ Ico i (i + (j + 1) + 1), |x l| = |x i| + ∑ l ∈ Ico (i + 1) (i + 1 + j + 1), |x l| := by
      rw [sum_eq_sum_Ico_succ_bot (by omega), show i + (j + 1) + 1 = i + 1 + j + 1 by omega]
    rw [hsum, habs]
    have hSA : |∑ l ∈ Ico (i + 1) (i + 1 + j + 1), x l| ≤ ∑ l ∈ Ico (i + 1) (i + 1 + j + 1), |x l| :=
      abs_sum_le_sum_abs _ _
    obtain ⟨T, hT⟩ : ∃ T, T = tailSum p x (i + 1) j := ⟨_, rfl⟩
    obtain ⟨Sg, hS⟩ : ∃ Sg, Sg = ∑ l ∈ Ico (i + 1) (i + 1 + j + 1), x l := ⟨_, rfl⟩
    obtain ⟨A, hA⟩ : ∃ A, A = ∑ l ∈ Ico (i + 1) (i + 1 + j + 1), |x l| := ⟨_, rfl⟩
    rw [← hT, ← hS, ← hA] at ih
    rw [← hS, ← hA] at hSA
    show |RN p (x i + tailSum p x (i + 1) j) - (x i + _)| ≤ _
    rw [← hT, ← hS, ← hA]
    obtain ⟨G, hG⟩ : ∃ G, G = (1 + u p) ^ j := ⟨_, rfl⟩
    have hG1 : 1 ≤ G := by rw [hG]; exact one_le_pow₀ (by linarith)
    rw [pow_succ, ← hG]
    rw [← hG] at ih
    have hA0 : 0 ≤ A := (abs_nonneg _).trans hSA
    have hx0 := abs_nonneg (x i)
    have hTb : |T| ≤ G * A := by
      have := abs_sub_abs_le_abs_sub T Sg
      nlinarith
    have h1 : |RN p (x i + T) - (x i + T)| ≤ u p * (|x i| + G * A) := by
      have h2 := abs_RN_sub_le_us p (x i + T)
      have h3 := abs_add_le (x i) T
      have h4 : us p * |x i + T| ≤ u p * |x i + T| := mul_le_mul_of_nonneg_right (us_le_u p) (abs_nonneg _)
      have h5 : u p * |x i + T| ≤ u p * (|x i| + G * A) := mul_le_mul_of_nonneg_left (by linarith) hu.le
      linarith
    have h2 : |RN p (x i + T) - (x i + Sg)| ≤ |RN p (x i + T) - (x i + T)| + |T - Sg| := by
      have := abs_add_le (RN p (x i + T) - (x i + T)) (T - Sg)
      rwa [show RN p (x i + T) - (x i + T) + (T - Sg) = RN p (x i + T) - (x i + Sg) by ring] at this
    have h3 : 0 ≤ (G - 1) * (1 + u p) * |x i| := mul_nonneg (mul_nonneg (by linarith) (by linarith)) hx0
    nlinarith

/-- step (1)'s double word `x̃ = FastTwoSum(x_0, RN(x_1 + RN(x_2 + …)))`, for eight parts -/
noncomputable def ln8Xt (x : ℕ → ℝ) : ℝ × ℝ := fastTwoSum p (x 0) (tailSum p x 1 6)

/-- Step (1)'s `x̃` for `x > 0` in `F` on `H(2)` at `p = 53`: its parts are in `F`, it is a double word, it is
positive, and `|ln x - ln x̃| ≤ δ_0`, the paper's `δ_0 = w/(1 - w)` with `w = gρ/(1 - 2ρ - gρ)`,
`g = 6u/(1 - 6u)` and `ρ = 2u` -/
theorem ln8Xt_spec (hp : p = 53) (x : ℕ → ℝ) (hx : ∀ i < 8, F p (x i)) (hH : Htheta p 8 2 x)
    (hX0 : 0 < ∑ i ∈ range 8, x i) :
    F p (ln8Xt p x).1 ∧ F p (ln8Xt p x).2 ∧ RN p ((ln8Xt p x).1 + (ln8Xt p x).2) = (ln8Xt p x).1 ∧
      0 < (ln8Xt p x).1 + (ln8Xt p x).2 ∧
      |Real.log (∑ i ∈ range 8, x i) - Real.log ((ln8Xt p x).1 + (ln8Xt p x).2)| ≤ ((log8D0 : ℚ) : ℝ) := by
  have hu : ((red8U : ℚ) : ℝ) = u p := by unfold red8U; exact u_53_rat p hp
  have hu53 : u p = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  have hρ : (2 : ℝ) * (2 * u p) < 1 := by rw [hu53]; norm_num
  obtain ⟨l1, l2⟩ := Htheta_lead_pos p 8 (by norm_num) 2 (by norm_num) hρ x hH hX0
  have hx0 : 0 < x 0 := lt_of_lt_of_le (mul_pos (by rw [hu53]; norm_num) hX0) l1
  -- the sum of the magnitudes of the lower parts
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
  -- the tail
  have hT : |tailSum p x 1 6 - ∑ l ∈ Ico 1 8, x l| ≤ ((1 + u p) ^ 6 - 1) * ∑ l ∈ Ico 1 8, |x l| :=
    tailSum_err p x 6 1
  have hSA : |∑ l ∈ Ico 1 8, x l| ≤ ∑ l ∈ Ico 1 8, |x l| := abs_sum_le_sum_abs _ _
  obtain ⟨T, hTd⟩ : ∃ T, T = tailSum p x 1 6 := ⟨_, rfl⟩
  obtain ⟨Sg, hSd⟩ : ∃ Sg, Sg = ∑ l ∈ Ico 1 8, x l := ⟨_, rfl⟩
  obtain ⟨A, hAd⟩ : ∃ A, A = ∑ l ∈ Ico 1 8, |x l| := ⟨_, rfl⟩
  obtain ⟨X, hXd⟩ : ∃ X, X = ∑ i ∈ range 8, x i := ⟨_, rfl⟩
  rw [← hTd, ← hSd, ← hAd] at hT
  rw [← hSd, ← hAd] at hSA
  rw [← hAd] at ht hA0
  rw [← hSd, ← hXd] at hsX
  rw [← hXd] at hX0 l1 l2 ⊢
  have hTF : F p T := by
    rw [hTd]
    exact F_RN p _
  have hg : (1 + u p) ^ 6 - 1 ≤ 6 * u p / (1 - 6 * u p) := by rw [hu53]; norm_num
  have hg0 : (0 : ℝ) ≤ (1 + u p) ^ 6 - 1 := by rw [hu53]; norm_num
  -- `|x - x̃| ≤ g·ρ/(1 - ρ)·x_0`, with `g = 6u/(1 - 6u)`
  have hd : |X - (x 0 + T)| ≤ 6 * u p / (1 - 6 * u p) * (2 * u p / (1 - 2 * u p) * x 0) := by
    rw [hsX, show x 0 + Sg - (x 0 + T) = -(T - Sg) by ring, abs_neg]
    refine hT.trans ?_
    have h1 := mul_le_mul_of_nonneg_left ht hg0
    have h2 := mul_le_mul_of_nonneg_right hg
      (mul_nonneg (by rw [hu53]; norm_num : (0 : ℝ) ≤ 2 * u p / (1 - 2 * u p)) hx0.le)
    linarith
  -- FastTwoSum is exact
  have hTx : |T| ≤ |x 0| := by
    rw [abs_of_pos hx0]
    have h1 := abs_sub_abs_le_abs_sub T Sg
    have h2 : (1 + u p) ^ 6 * (2 * u p / (1 - 2 * u p)) ≤ 1 := by rw [hu53]; norm_num
    have h3 := mul_le_mul_of_nonneg_left ht (by linarith : (0 : ℝ) ≤ (1 + u p) ^ 6)
    have h4 := mul_le_mul_of_nonneg_right h2 hx0.le
    nlinarith
  have hsum : (ln8Xt p x).1 + (ln8Xt p x).2 = x 0 + T := by
    rw [hTd]
    exact fastTwoSum_add p (by omega) (hx 0 (by norm_num)) (by rw [← hTd]; exact hTF) (by rw [← hTd]; exact hTx)
  have hfst : (ln8Xt p x).1 = RN p (x 0 + T) := by rw [hTd]; rfl
  -- `x̃ ≥ x_0(1 - 2ρ - gρ)/(1 - ρ) > 0`
  have hXlow : x 0 * ((1 - 2 * (2 * u p)) / (1 - 2 * u p)) ≤ X := by
    rw [hu53] at l2 ⊢
    norm_num at l2 ⊢
    linarith
  obtain ⟨d1, d2⟩ := abs_le.mp hd
  have hXt : x 0 * ((1 - 2 * (2 * u p) - 6 * u p / (1 - 6 * u p) * (2 * u p)) / (1 - 2 * u p)) ≤ x 0 + T := by
    have e : x 0 * ((1 - 2 * (2 * u p) - 6 * u p / (1 - 6 * u p) * (2 * u p)) / (1 - 2 * u p)) =
        x 0 * ((1 - 2 * (2 * u p)) / (1 - 2 * u p)) -
          6 * u p / (1 - 6 * u p) * (2 * u p / (1 - 2 * u p) * x 0) := by
      ring
    rw [e]
    linarith
  have hpos : 0 < x 0 + T := lt_of_lt_of_le (mul_pos hx0 (by rw [hu53]; norm_num)) hXt
  -- `|x - x̃| ≤ w·x̃`
  have hw : |X - (x 0 + T)| ≤
      6 * u p / (1 - 6 * u p) * (2 * u p) / (1 - 2 * (2 * u p) - 6 * u p / (1 - 6 * u p) * (2 * u p)) *
        (x 0 + T) := by
    refine hd.trans (le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hXt (by rw [hu53]; norm_num)))
    rw [hu53]
    ring
  have hlog := log_near hpos hX0 hw (by rw [hu53]; norm_num)
  have hD0 : ((log8D0 : ℚ) : ℝ) =
      6 * u p / (1 - 6 * u p) * (2 * u p) / (1 - 2 * (2 * u p) - 6 * u p / (1 - 6 * u p) * (2 * u p)) /
        (1 - 6 * u p / (1 - 6 * u p) * (2 * u p) /
          (1 - 2 * (2 * u p) - 6 * u p / (1 - 6 * u p) * (2 * u p))) := by
    unfold log8D0
    push_cast
    rw [hu]
  rw [hsum, hD0]
  refine ⟨by rw [hfst]; exact F_RN p _, F_RN p _, by rw [hfst], hpos, hlog⟩

/-- The start of `LOG_{8,6,43,4}` without the halving: for `x > 0` in `F` on `H(2)` at `p = 53`, a `y_0` within
`ε_DW|ln x̃| + Φ_DW` of `ln x̃`, with the quoted `ε_DW = 15.351u²` and `Φ_DW = 2^{-1071}` of Proposition 44, is
within `E(|ln x|)` of `ln x`: the hypothesis `hE` of `thm42_8` -/
theorem log8_start (hp : p = 53) (x : ℕ → ℝ) (hx : ∀ i < 8, F p (x i)) (hH : Htheta p 8 2 x)
    (hX0 : 0 < ∑ i ∈ range 8, x i) (Y0 : ℝ)
    (hDW : |Y0 - Real.log ((ln8Xt p x).1 + (ln8Xt p x).2)| ≤
      15351 / 1000 * u p ^ 2 * |Real.log ((ln8Xt p x).1 + (ln8Xt p x).2)| + 1 / 2 ^ 1071) :
    |Y0 - Real.log (∑ i ∈ range 8, x i)| ≤ log8E |Real.log (∑ i ∈ range 8, x i)| := by
  have hu : ((red8U : ℚ) : ℝ) = u p := by unfold red8U; exact u_53_rat p hp
  obtain ⟨-, -, -, -, hlog⟩ := ln8Xt_spec p hp x hx hH hX0
  obtain ⟨c1, c2, c3, c4⟩ := log8_start_consts
  have hε : ((log8EpsDW : ℚ) : ℝ) = 15351 / 1000 * u p ^ 2 := by
    unfold log8EpsDW
    push_cast
    rw [hu]
  have h1 := (Rat.cast_le (K := ℝ)).mpr c1
  have h2 := (Rat.cast_le (K := ℝ)).mpr c2
  have h3 : (0 : ℝ) ≤ ((log8EpsDW : ℚ) : ℝ) := by exact_mod_cast c3
  push_cast at h1
  rw [← hε] at hDW
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ, Φ = 1 / 2 ^ 1071 := ⟨_, rfl⟩
  rw [← hΦ] at hDW h1
  obtain ⟨Lt, hLt⟩ : ∃ Lt, Lt = Real.log ((ln8Xt p x).1 + (ln8Xt p x).2) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log (∑ i ∈ range 8, x i) := ⟨_, rfl⟩
  rw [← hLt] at hDW hlog
  rw [← hL] at hlog ⊢
  simp only [log8E, logE]
  -- `|ln x̃| ≤ |ln x| + δ_0`
  have h4 : |Lt| ≤ |L| + ((log8D0 : ℚ) : ℝ) := by
    have := abs_sub_abs_le_abs_sub Lt L
    rw [abs_sub_comm] at this
    linarith
  have h5 : |Y0 - L| ≤ |Y0 - Lt| + |L - Lt| := by
    have := abs_add_le (Y0 - Lt) (Lt - L)
    rw [show Y0 - Lt + (Lt - L) = Y0 - L by ring, abs_sub_comm Lt L] at this
    exact this
  have h6 := mul_le_mul_of_nonneg_left h4 h3
  have h7 : ((log8EpsDW : ℚ) : ℝ) * |L| ≤ ((log8E1 : ℚ) : ℝ) * |L| :=
    mul_le_mul_of_nonneg_right h2 (abs_nonneg L)
  linarith

/-- The constants of the start with the halving: `ε_DW X + e₀ ≤ 1` at `X = 745.2`, `e_A ≥ 0` and `ln 2 ≥ 1/2` on
its enclosure. -/
theorem log8_half_consts : log8EpsDW * (7452 / 10) + log8E0 ≤ 1 ∧ 0 ≤ log8EA ∧ (1 / 2 : ℚ) ≤ ln2A := by
  decide +kernel

omit [Prec_gt_0 p] in
/-- The start with the halving (`x_0 ≥ 2^{1023}` in binary64), the accounting of the paper's proof: with
`L = ln x ≥ ln 2`, `L ≤ X = 745.2`, `L_h` the logarithm of the double word of the halved `x`, within
`δ_0 + 2^{-2000}` of `ln(x/2)`, `W` the double-word logarithm's result within `ε_DW|L_h| + Φ_DW` of `L_h`, and
`y_0` within `e_A|W + c_L|` of `W + c_L`, AccurateDWPlusDW's bound with `e_A = 3u²/(1 - 4u)`: `y_0` is within
`E(|ln x|)` of `ln x`. The distance of `L_h` from `ln(x/2)` is a hypothesis here. -/
theorem log8_start_half (hp : p = 53) {L Lh W Y0 : ℝ} (hL : Real.log 2 ≤ L) (hLX : L ≤ 7452 / 10)
    (hLh : |Lh - (L - Real.log 2)| ≤ ((log8D0 : ℚ) : ℝ) + 1 / 2 ^ 2000)
    (hW : |W - Lh| ≤ 15351 / 1000 * u p ^ 2 * |Lh| + 1 / 2 ^ 1071)
    (hA : |Y0 - (W + (((dyQ log8CL0 : ℚ) : ℝ) + ((dyQ log8CL1 : ℚ) : ℝ)))| ≤
      3 * u p ^ 2 / (1 - 4 * u p) * |W + (((dyQ log8CL0 : ℚ) : ℝ) + ((dyQ log8CL1 : ℚ) : ℝ))|) :
    |Y0 - L| ≤ log8E |L| := by
  have hu : ((red8U : ℚ) : ℝ) = u p := by unfold red8U; exact u_53_rat p hp
  obtain ⟨-, -, c3, c4⟩ := log8_start_consts
  obtain ⟨k1, k2, k3⟩ := log8_half_consts
  obtain ⟨lA, lB⟩ := log_two_600
  have hε : ((log8EpsDW : ℚ) : ℝ) = 15351 / 1000 * u p ^ 2 := by
    unfold log8EpsDW
    push_cast
    rw [hu]
  have heA : ((log8EA : ℚ) : ℝ) = 3 * u p ^ 2 / (1 - 4 * u p) := by
    unfold log8EA
    push_cast
    rw [hu]
  rw [← hε] at hW
  rw [← heA] at hA
  have hε0 : (0 : ℝ) ≤ ((log8EpsDW : ℚ) : ℝ) := by exact_mod_cast c3
  have hδ0 : (0 : ℝ) ≤ ((log8D0 : ℚ) : ℝ) := by exact_mod_cast c4
  have heA0 : (0 : ℝ) ≤ ((log8EA : ℚ) : ℝ) := by exact_mod_cast k2
  have hln2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr k3
    push_cast at h
    linarith
  have hτ1 : (1 : ℝ) / 2 ^ 2000 ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ 2000 := pow_le_pow_right₀ (by norm_num) (by norm_num))
  have hτ0 : (0 : ℝ) ≤ 1 / 2 ^ 2000 := by positivity
  have hE0 : ((log8E0 : ℚ) : ℝ) = ((log8EpsDW : ℚ) : ℝ) * ((log8D0 : ℚ) : ℝ) + ((log8D0 : ℚ) : ℝ) +
      1 / 2 ^ 1071 + ((log8EA : ℚ) : ℝ) + ((log8EtaL : ℚ) : ℝ) + 1 / 2 ^ 2000 := by
    unfold log8E0
    push_cast
    rfl
  have hE1 : ((log8E1 : ℚ) : ℝ) = ((log8EpsDW : ℚ) : ℝ) + ((log8EA : ℚ) : ℝ) := by
    unfold log8E1
    push_cast
    rfl
  have hk1 := (Rat.cast_le (K := ℝ)).mpr k1
  push_cast at hk1
  -- `|c_L - ln 2| ≤ η_L`
  have hη : |((dyQ log8CL0 : ℚ) : ℝ) + ((dyQ log8CL1 : ℚ) : ℝ) - Real.log 2| ≤ ((log8EtaL : ℚ) : ℝ) := by
    unfold log8EtaL
    push_cast
    have h1 := le_max_left |((ln2A : ℚ) : ℝ) - (((dyQ log8CL0 : ℚ) : ℝ) + ((dyQ log8CL1 : ℚ) : ℝ))|
      |((ln2B : ℚ) : ℝ) - (((dyQ log8CL0 : ℚ) : ℝ) + ((dyQ log8CL1 : ℚ) : ℝ))|
    have h2 := le_max_right |((ln2A : ℚ) : ℝ) - (((dyQ log8CL0 : ℚ) : ℝ) + ((dyQ log8CL1 : ℚ) : ℝ))|
      |((ln2B : ℚ) : ℝ) - (((dyQ log8CL0 : ℚ) : ℝ) + ((dyQ log8CL1 : ℚ) : ℝ))|
    have h3 := neg_abs_le (((ln2A : ℚ) : ℝ) - (((dyQ log8CL0 : ℚ) : ℝ) + ((dyQ log8CL1 : ℚ) : ℝ)))
    have h4 := le_abs_self (((ln2A : ℚ) : ℝ) - (((dyQ log8CL0 : ℚ) : ℝ) + ((dyQ log8CL1 : ℚ) : ℝ)))
    have h5 := neg_abs_le (((ln2B : ℚ) : ℝ) - (((dyQ log8CL0 : ℚ) : ℝ) + ((dyQ log8CL1 : ℚ) : ℝ)))
    have h6 := le_abs_self (((ln2B : ℚ) : ℝ) - (((dyQ log8CL0 : ℚ) : ℝ) + ((dyQ log8CL1 : ℚ) : ℝ)))
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ((dyQ log8CL0 : ℚ) : ℝ) + ((dyQ log8CL1 : ℚ) : ℝ) := ⟨_, rfl⟩
  rw [← hc] at hA hη
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ, Φ = 1 / 2 ^ 1071 := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = 1 / 2 ^ 2000 := ⟨_, rfl⟩
  rw [← hΦ] at hW hE0
  rw [← hτ] at hLh hE0 hτ0 hτ1
  have hl : |L| = L := abs_of_nonneg (by linarith)
  -- `|L_h| ≤ L + δ_0`
  have h1 : |Lh| ≤ L + ((log8D0 : ℚ) : ℝ) := by
    obtain ⟨a, b⟩ := abs_le.mp hLh
    rw [abs_le]
    constructor <;> linarith
  have h2 : |W - Lh| ≤ ((log8EpsDW : ℚ) : ℝ) * (L + ((log8D0 : ℚ) : ℝ)) + Φ :=
    hW.trans (by linarith [mul_le_mul_of_nonneg_left h1 hε0])
  have h3 : |W + c - L| ≤ ((log8EpsDW : ℚ) : ℝ) * (L + ((log8D0 : ℚ) : ℝ)) + Φ + (((log8D0 : ℚ) : ℝ) + τ) +
      ((log8EtaL : ℚ) : ℝ) := by
    rw [show W + c - L = (W - Lh) + (Lh - (L - Real.log 2)) + (c - Real.log 2) by ring]
    exact (abs_add_three _ _ _).trans (by linarith)
  have h7 := mul_le_mul_of_nonneg_left hLX hε0
  -- `|W + c_L| ≤ L + 1`
  have h4 : |W + c| ≤ L + 1 := by
    have := abs_sub_abs_le_abs_sub (W + c) L
    rw [hl] at this
    linarith
  have h5 : |Y0 - L| ≤ |Y0 - (W + c)| + |W + c - L| := by
    have := abs_add_le (Y0 - (W + c)) (W + c - L)
    rwa [sub_add_sub_cancel] at this
  have h6 := mul_le_mul_of_nonneg_left h4 heA0
  simp only [log8E, logE]
  rw [hl, hE0, hE1]
  linarith

end ExpansionBounds
