import ExpansionBounds.DWPlusFP

/-!
# DWTimesFP3, the product of a double word by a float

Algorithm 9 of Joldes, Muller and Popescu (2017), the MULF of `DD::exp` and `DD::ln`, with a fused multiply-add:

  `(c_h, c_ℓ1) = TwoProd(x_h, y)`, `c_ℓ3 = RN(c_ℓ1 + x_ℓ y)`, `(z_h, z_ℓ) = FastTwoSum(c_h, c_ℓ3)`.

Theorem 4.3 of that paper, with its result a double word (`dwTimesFP3_good`): for `p ≥ 3`, a double word `x` and a
float `y`, the result is a double word within `2u²` of `xy`, relatively. The paper omits the proof as "very similar"
to that of its Theorem 4.2; this is that proof with one rounding fewer. On `x_h, y ∈ [1, 2)`: `|c_ℓ1| ≤ 2u` and
`|x_ℓ y| ≤ 2u`, so `c_ℓ3` is within `2u²` of `c_ℓ1 + x_ℓ y`; `c_h ≥ 1 ≥ |c_ℓ3|`, so the last FastTwoSum is exact; and
`xy ≥ (1 - u)(1 + 2u) ≥ 1` for `y > 1`, while `y = 1` is exact.
-/

namespace ExpansionBounds

variable (p : ℤ)

/-- DWTimesFP3: `(c_h, c_ℓ1) = TwoProd(x_h, y)`, `c_ℓ3 = RN(c_ℓ1 + x_ℓ y)` and
`(z_h, z_ℓ) = FastTwoSum(c_h, c_ℓ3)` -/
noncomputable def dwTimesFP3 (x : ℝ × ℝ) (y : ℝ) : ℝ × ℝ :=
  fastTwoSum p (twoProd p x.1 y).1 (RN p ((twoProd p x.1 y).2 + x.2 * y))

/-- DWTimesFP3 commutes with scalings by powers of two -/
theorem dwTimesFP3_scale (a b : ℤ) (x : ℝ × ℝ) (y : ℝ) :
    dwTimesFP3 p ((2 : ℝ) ^ a * x.1, (2 : ℝ) ^ a * x.2) ((2 : ℝ) ^ b * y) =
      ((2 : ℝ) ^ (a + b) * (dwTimesFP3 p x y).1, (2 : ℝ) ^ (a + b) * (dwTimesFP3 p x y).2) := by
  have e : (2 : ℝ) ^ a * x.2 * ((2 : ℝ) ^ b * y) = (2 : ℝ) ^ (a + b) * (x.2 * y) := by
    rw [zpow_add₀ two_ne_zero]; ring
  unfold dwTimesFP3
  simp only [twoProd_scale, e, ← mul_add, RN_zpow_mul, fastTwoSum_scale]

variable [Prec_gt_0 p]

/-- DWTimesFP3 commutes with the negation of `x` -/
theorem dwTimesFP3_neg_left (x : ℝ × ℝ) (y : ℝ) :
    dwTimesFP3 p (-x.1, -x.2) y = (-(dwTimesFP3 p x y).1, -(dwTimesFP3 p x y).2) := by
  unfold dwTimesFP3
  simp only [twoProd_neg_left, neg_mul, ← neg_add, RN_neg, fastTwoSum_neg]

/-- DWTimesFP3 commutes with the negation of `y` -/
theorem dwTimesFP3_neg_right (x : ℝ × ℝ) (y : ℝ) :
    dwTimesFP3 p x (-y) = (-(dwTimesFP3 p x y).1, -(dwTimesFP3 p x y).2) := by
  unfold dwTimesFP3
  simp only [twoProd_neg_right, mul_neg, ← neg_add, RN_neg, fastTwoSum_neg]

omit [Prec_gt_0 p] in
/-- DWTimesFP3 of a zero `x` is zero -/
theorem dwTimesFP3_zero_left (y : ℝ) : dwTimesFP3 p (0, 0) y = (0, 0) := by
  simp [dwTimesFP3, twoProd, fastTwoSum, RN_zero]

omit [Prec_gt_0 p] in
/-- DWTimesFP3 by a zero `y` is zero -/
theorem dwTimesFP3_zero_right (x : ℝ × ℝ) : dwTimesFP3 p x 0 = (0, 0) := by
  simp [dwTimesFP3, twoProd, fastTwoSum, RN_zero]

/-- the conclusion of Theorem 4.3 of JMP17 at `(x_h, x_ℓ)` and `y`: the result is a double word within `2u²` of
`xy`, relatively -/
def TimesFPGood (xh xl y : ℝ) : Prop :=
  DW p (dwTimesFP3 p (xh, xl) y) ∧
    |dwVal (dwTimesFP3 p (xh, xl) y) - (xh + xl) * y| ≤ 2 * u p ^ 2 * |(xh + xl) * y|

/-- `TimesFPGood` passes from operands scaled by powers of two -/
theorem TimesFPGood.of_scale {xh xl y : ℝ} (a b : ℤ)
    (h : TimesFPGood p ((2 : ℝ) ^ a * xh) ((2 : ℝ) ^ a * xl) ((2 : ℝ) ^ b * y)) : TimesFPGood p xh xl y := by
  have hK : (0 : ℝ) < (2 : ℝ) ^ (a + b) := by positivity
  have hs : dwTimesFP3 p ((2 : ℝ) ^ a * xh, (2 : ℝ) ^ a * xl) ((2 : ℝ) ^ b * y) =
      ((2 : ℝ) ^ (a + b) * (dwTimesFP3 p (xh, xl) y).1, (2 : ℝ) ^ (a + b) * (dwTimesFP3 p (xh, xl) y).2) :=
    dwTimesFP3_scale p a b (xh, xl) y
  unfold TimesFPGood at h ⊢
  rw [hs] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨DW.of_scale p (a + b) h1, ?_⟩
  have e1 : dwVal ((2 : ℝ) ^ (a + b) * (dwTimesFP3 p (xh, xl) y).1,
      (2 : ℝ) ^ (a + b) * (dwTimesFP3 p (xh, xl) y).2) - ((2 : ℝ) ^ a * xh + (2 : ℝ) ^ a * xl) * ((2 : ℝ) ^ b * y) =
        (2 : ℝ) ^ (a + b) * (dwVal (dwTimesFP3 p (xh, xl) y) - (xh + xl) * y) := by
    unfold dwVal
    rw [zpow_add₀ two_ne_zero]; ring
  have e2 : ((2 : ℝ) ^ a * xh + (2 : ℝ) ^ a * xl) * ((2 : ℝ) ^ b * y) = (2 : ℝ) ^ (a + b) * ((xh + xl) * y) := by
    rw [zpow_add₀ two_ne_zero]; ring
  rw [e1, e2, abs_mul, abs_mul, abs_of_pos hK] at h2
  exact le_of_mul_le_mul_left (by linarith) hK

/-- `TimesFPGood` passes from the negated `x` -/
theorem TimesFPGood.of_neg_left {xh xl y : ℝ} (h : TimesFPGood p (-xh) (-xl) y) : TimesFPGood p xh xl y := by
  have hs : dwTimesFP3 p (-xh, -xl) y = (-(dwTimesFP3 p (xh, xl) y).1, -(dwTimesFP3 p (xh, xl) y).2) :=
    dwTimesFP3_neg_left p (xh, xl) y
  unfold TimesFPGood at h ⊢
  rw [hs] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨DW.of_neg p h1, ?_⟩
  have e1 : dwVal (-(dwTimesFP3 p (xh, xl) y).1, -(dwTimesFP3 p (xh, xl) y).2) - (-xh + -xl) * y =
      -(dwVal (dwTimesFP3 p (xh, xl) y) - (xh + xl) * y) := by
    unfold dwVal
    ring
  rw [e1, abs_neg, show (-xh + -xl) * y = -((xh + xl) * y) by ring, abs_neg] at h2
  exact h2

/-- `TimesFPGood` passes from the negated `y` -/
theorem TimesFPGood.of_neg_right {xh xl y : ℝ} (h : TimesFPGood p xh xl (-y)) : TimesFPGood p xh xl y := by
  have hs : dwTimesFP3 p (xh, xl) (-y) = (-(dwTimesFP3 p (xh, xl) y).1, -(dwTimesFP3 p (xh, xl) y).2) :=
    dwTimesFP3_neg_right p (xh, xl) y
  unfold TimesFPGood at h ⊢
  rw [hs] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨DW.of_neg p h1, ?_⟩
  have e1 : dwVal (-(dwTimesFP3 p (xh, xl) y).1, -(dwTimesFP3 p (xh, xl) y).2) - (xh + xl) * -y =
      -(dwVal (dwTimesFP3 p (xh, xl) y) - (xh + xl) * y) := by
    unfold dwVal
    ring
  rw [e1, abs_neg, show (xh + xl) * -y = -((xh + xl) * y) by ring, abs_neg] at h2
  exact h2

/-- Theorem 4.3 of JMP17 on operands in `[1, 2)` -/
theorem dwTimesFP3_norm (hp : 3 ≤ p) {xh xl y : ℝ} (hxh : F p xh) (hxl : F p xl) (hy : F p y)
    (hdw : RN p (xh + xl) = xh) (hx1 : 1 ≤ xh) (hx2 : xh < 2) (hy1 : 1 ≤ y) (hy2 : y < 2) :
    TimesFPGood p xh xl y := by
  have hu := u_pos p
  have hu8 := u_le_eighth p hp
  have hp1 : 1 < p := by omega
  have hl := dw_lo_le p hp1 hxh hdw hx1 hx2
  obtain ⟨hl1, hl2⟩ := abs_le.mp hl
  obtain ⟨hsum, -, -⟩ := facts_c p hxh hy
  have hc1 : (twoProd p xh y).1 = RN p (xh * y) := rfl
  unfold TimesFPGood
  show DW p (fastTwoSum p (twoProd p xh y).1 (RN p ((twoProd p xh y).2 + xl * y))) ∧
    |dwVal (fastTwoSum p (twoProd p xh y).1 (RN p ((twoProd p xh y).2 + xl * y))) - (xh + xl) * y| ≤
      2 * u p ^ 2 * |(xh + xl) * y|
  rcases eq_or_lt_of_le hy1 with hy0 | hy0
  · -- `y = 1`: every step is exact
    subst hy0
    have h1 : (twoProd p xh 1).1 = xh := by rw [hc1, mul_one, RN_of_F p hxh]
    have h2 : (twoProd p xh 1).2 = 0 := by
      rw [h1, mul_one] at hsum
      linarith
    rw [h1, h2, zero_add, mul_one, RN_of_F p hxl]
    have hadd := fastTwoSum_add p hp1 hxh hxl (by rw [abs_of_pos (by linarith : (0 : ℝ) < xh)]; linarith)
    refine ⟨fastTwoSum_dw p hadd, ?_⟩
    rw [show dwVal (fastTwoSum p xh xl) - (xh + xl) * 1 = 0 by unfold dwVal; rw [hadd]; ring, abs_zero]
    positivity
  · -- `y ≥ 1 + 2u`
    have hm1 : Mult (1 - p) (1 : ℝ) := by
      have := Mult.zpow (E := 1 - p) (e := 0) (by omega)
      rwa [zpow_zero] at this
    have hy3 := Mult.le_sub hm1 (mult_of_one_le p hy hy1) hy0
    rw [two_zpow_sub_p, zpow_one] at hy3
    have e4 : (2 : ℝ) ^ (2 : ℤ) = 4 := by norm_num
    have hxy1 : 1 ≤ xh * y := by nlinarith
    have hxy4 : xh * y ≤ 4 := by nlinarith
    -- `c_h ≥ 1` and `|c_ℓ1| ≤ 2u`
    have hch : 1 ≤ (twoProd p xh y).1 := by
      have := RN_mono p hxy1
      rwa [RN_of_F p (F_one p)] at this
    have hcl : |(twoProd p xh y).2| ≤ 2 * u p := by
      have hg := RN_grid p 2 (z := xh * y) (by rw [e4, abs_of_pos (by linarith)]; exact hxy4)
      rw [e4] at hg
      have he : (twoProd p xh y).2 = -(RN p (xh * y) - xh * y) := by rw [← hc1]; linarith
      rw [he, abs_neg]
      linarith
    -- `|c_ℓ1 + x_ℓ y| ≤ 4u`, so its rounding errs by at most `2u²`
    have hxly : |xl * y| ≤ 2 * u p := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < y)]
      nlinarith [abs_nonneg xl]
    have hsm : |(twoProd p xh y).2 + xl * y| ≤ (2 : ℝ) ^ (2 : ℤ) * u p := by
      rw [e4]
      have := abs_add_le (twoProd p xh y).2 (xl * y)
      linarith
    have hε := RN_grid p (2 - p) (z := (twoProd p xh y).2 + xl * y) (by rw [two_zpow_sub_p]; exact hsm)
    rw [two_zpow_sub_p, e4] at hε
    rw [e4] at hsm
    -- the last FastTwoSum is exact
    have hv : |RN p ((twoProd p xh y).2 + xl * y)| ≤ |(twoProd p xh y).1| := by
      have h1 := abs_add_le (RN p ((twoProd p xh y).2 + xl * y) - ((twoProd p xh y).2 + xl * y))
        ((twoProd p xh y).2 + xl * y)
      rw [sub_add_cancel] at h1
      rw [abs_of_pos (by linarith : (0 : ℝ) < (twoProd p xh y).1)]
      nlinarith
    have hF1 : F p (twoProd p xh y).1 := F_RN p _
    have hadd := fastTwoSum_add p hp1 hF1 (F_RN p ((twoProd p xh y).2 + xl * y)) hv
    refine ⟨fastTwoSum_dw p hadd, ?_⟩
    have hval : dwVal (fastTwoSum p (twoProd p xh y).1 (RN p ((twoProd p xh y).2 + xl * y))) - (xh + xl) * y =
        RN p ((twoProd p xh y).2 + xl * y) - ((twoProd p xh y).2 + xl * y) := by
      unfold dwVal
      rw [hadd]
      linarith
    rw [hval]
    have hX : 1 ≤ (xh + xl) * y := by nlinarith
    calc |RN p ((twoProd p xh y).2 + xl * y) - ((twoProd p xh y).2 + xl * y)| ≤ 4 * u p * u p / 2 := hε
      _ = 2 * u p ^ 2 * 1 := by ring
      _ ≤ 2 * u p ^ 2 * |(xh + xl) * y| :=
        mul_le_mul_of_nonneg_left (hX.trans (le_abs_self _)) (by positivity)

/-- Theorem 4.3 of JMP17 for positive `x_h` and `y`: the operands scaled into `[1, 2)` -/
theorem dwTimesFP3_pos (hp : 3 ≤ p) {xh xl y : ℝ} (hxh : F p xh) (hxl : F p xl) (hy : F p y)
    (hdw : RN p (xh + xl) = xh) (hx0 : 0 < xh) (hy0 : 0 < y) : TimesFPGood p xh xl y := by
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hx0 (by norm_num : (1 : ℝ) < 2)
  obtain ⟨m, hm1, hm2⟩ := exists_mem_Ico_zpow hy0 (by norm_num : (1 : ℝ) < 2)
  have ha : (0 : ℝ) < (2 : ℝ) ^ (-n) := by positivity
  have hb : (0 : ℝ) < (2 : ℝ) ^ (-m) := by positivity
  have s1 : ∀ k : ℤ, (2 : ℝ) ^ (-k) * (2 : ℝ) ^ k = 1 := fun k => by
    rw [← zpow_add₀ two_ne_zero, neg_add_cancel, zpow_zero]
  have s2 : ∀ k : ℤ, (2 : ℝ) ^ (-k) * (2 : ℝ) ^ (k + 1) = 2 := fun k => by
    rw [← zpow_add₀ two_ne_zero, show -k + (k + 1) = 1 by ring, zpow_one]
  exact TimesFPGood.of_scale p (-n) (-m) (dwTimesFP3_norm p hp (F_zpow_mul p (-n) hxh) (F_zpow_mul p (-n) hxl)
    (F_zpow_mul p (-m) hy) (by rw [← mul_add, RN_zpow_mul, hdw])
    (by have := mul_le_mul_of_nonneg_left hn1 ha.le; rwa [s1] at this)
    (by have := mul_lt_mul_of_pos_left hn2 ha; rwa [s2] at this)
    (by have := mul_le_mul_of_nonneg_left hm1 hb.le; rwa [s1] at this)
    (by have := mul_lt_mul_of_pos_left hm2 hb; rwa [s2] at this))

/-- Theorem 4.3 of JMP17, with its result a double word: for `p ≥ 3`, a double word `x` and a float `y`,
`DWTimesFP3(x, y)` is a double word within `2u²` of `xy`, relatively -/
theorem dwTimesFP3_good (hp : 3 ≤ p) {x : ℝ × ℝ} (hx : DW p x) {y : ℝ} (hy : F p y) :
    DW p (dwTimesFP3 p x y) ∧ |dwVal (dwTimesFP3 p x y) - dwVal x * y| ≤ 2 * u p ^ 2 * |dwVal x * y| := by
  obtain ⟨xh, xl⟩ := x
  obtain ⟨hxh, hxl, hdw⟩ := hx
  have hxh' : F p xh := hxh
  have hxl' : F p xl := hxl
  have hdw' : RN p (xh + xl) = xh := hdw
  show TimesFPGood p xh xl y
  -- a zero result
  have zero : ∀ {xh xl y : ℝ}, dwTimesFP3 p (xh, xl) y = (0, 0) → (xh + xl) * y = 0 → TimesFPGood p xh xl y := by
    intro xh xl y h0 h1
    unfold TimesFPGood
    rw [h0, h1]
    exact ⟨DW.of_F p (F_zero p), by simp [dwVal]⟩
  -- a positive `y`, and any `x_h`
  have key : ∀ {y : ℝ}, F p y → 0 < y → TimesFPGood p xh xl y := by
    intro y hy hy0
    rcases lt_trichotomy xh 0 with hx | hx | hx
    · exact TimesFPGood.of_neg_left p (dwTimesFP3_pos p hp (F_neg p hxh') (F_neg p hxl') hy
        (by rw [← neg_add, RN_neg, hdw']) (by linarith) hy0)
    · have hl0 : xl = 0 := RN_eq_zero p (by rw [hx, zero_add] at hdw'; exact hdw')
      exact zero (by rw [hx, hl0]; exact dwTimesFP3_zero_left p y) (by rw [hx, hl0]; ring)
    · exact dwTimesFP3_pos p hp hxh' hxl' hy hdw' hx hy0
  rcases lt_trichotomy y 0 with hy0 | hy0 | hy0
  · exact TimesFPGood.of_neg_right p (key (F_neg p hy) (by linarith))
  · exact zero (by rw [hy0]; exact dwTimesFP3_zero_right p _) (by rw [hy0]; ring)
  · exact key hy hy0

/-- Theorem 4.3 of JMP17: for `p ≥ 3`, DWTimesFP3 of a double word `x` and a float `y` is within `2u²` of `xy`,
relatively -/
theorem dwTimesFP3_err (hp : 3 ≤ p) {x : ℝ × ℝ} (hx : DW p x) {y : ℝ} (hy : F p y) :
    |dwVal (dwTimesFP3 p x y) - dwVal x * y| ≤ 2 * u p ^ 2 * |dwVal x * y| := (dwTimesFP3_good p hp hx hy).2

/-- the result of DWTimesFP3 is a double word: its last FastTwoSum is exact -/
theorem dwTimesFP3_dw (hp : 3 ≤ p) {x : ℝ × ℝ} (hx : DW p x) {y : ℝ} (hy : F p y) : DW p (dwTimesFP3 p x y) :=
  (dwTimesFP3_good p hp hx hy).1

end ExpansionBounds
