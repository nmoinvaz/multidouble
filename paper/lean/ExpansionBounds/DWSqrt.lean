import ExpansionBounds.DWDiv

/-!
# Double-word arithmetic: SQRTDWtoDW

The square root of a double-word number, Algorithm 8 of Lefèvre, Louvet, Muller, Picot and Rideau (2023), within
`25u²/8` of the exact root, relatively, for `p ≥ 5` (Theorem 3.5 of their preprint, HAL hal-03482567v1). The
proof is theirs: `s_h = RN(√x_h)`, the remainder
`x_h - s_h²` is exact, the two other roundings are bounded on their grids, and Heron's identity gives
`s_h + s_l - √x = ((s_h - √x)² + ε₁)/(2s_h) + ε₂`. It is done for `x_h` in `[1, 2)` and in `[2, 4)`, then scaled by
powers of four.
-/

namespace ExpansionBounds

/-- Heron's identity for one step from `s_h`: with `ε₁ = ρ₂ - (x - s_h²)` and `ε₂ = s_l - ρ₂/(2s_h)`,
`s_h + s_l - √x = ((s_h - √x)² + ε₁)/(2s_h) + ε₂` -/
theorem sqrtDW_heron {sh sl ρ2 S X : ℝ} (hsh : sh ≠ 0) (hS : S * S = X) :
    sh + sl - S = ((sh - S) ^ 2 + (ρ2 - (X - sh * sh))) / (2 * sh) + (sl - ρ2 / (2 * sh)) := by
  rw [← hS]
  field_simp
  ring

/-- the error of one Heron step, from bounds on `s_h - √x`, `ε₁` and `ε₂` and a lower bound `m` on `s_h` -/
theorem sqrtDW_step {sh sl ρ2 S X d e1 e2 m : ℝ} (hm : 0 < m) (hsh : m ≤ sh) (hS : S * S = X) (hd : |sh - S| ≤ d)
    (he1 : |ρ2 - (X - sh * sh)| ≤ e1) (he2 : |sl - ρ2 / (2 * sh)| ≤ e2) :
    |sh + sl - S| ≤ (d ^ 2 + e1) / (2 * m) + e2 := by
  have hsh0 : 0 < sh := lt_of_lt_of_le hm hsh
  rw [sqrtDW_heron hsh0.ne' hS]
  refine (abs_add_le _ _).trans (add_le_add ?_ he2)
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * sh)]
  have hsq : (sh - S) ^ 2 ≤ d ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hd 2
  have hnum : |(sh - S) ^ 2 + (ρ2 - (X - sh * sh))| ≤ d ^ 2 + e1 := by
    refine (abs_add_le _ _).trans (add_le_add ?_ he1)
    rwa [abs_of_nonneg (sq_nonneg _)]
  exact div_le_div₀ (by linarith [abs_nonneg ((sh - S) ^ 2 + (ρ2 - (X - sh * sh)))]) hnum (by linarith) (by linarith)

/-- `x_h` in `[1, 2)`: the remainder is at most `u(2s_h + u)`, and `x_l + ρ₁` at most `4u` -/
theorem sqrtDW_A1 {u xh xl s sh : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 32) (hx2 : xh < 2) (hxl : |xl| ≤ u)
    (hs : s * s = xh) (hsh1 : 1 ≤ sh) (hshs : |sh - s| ≤ u) :
    |xh - sh * sh| ≤ u * (2 * sh + u) ∧ |xl + (xh - sh * sh)| ≤ 4 * u := by
  obtain ⟨l1, l2⟩ := abs_le.mp hshs
  have hs142 : s < 142 / 100 := by
    by_contra h
    have h' := not_lt.mp h
    nlinarith [mul_nonneg (sub_nonneg.mpr h') (by linarith : (0 : ℝ) ≤ s + 142 / 100)]
  have hρ : |xh - sh * sh| ≤ u * (s + sh) := by
    rw [← hs, show s * s - sh * sh = (s - sh) * (s + sh) by ring, abs_mul, abs_of_pos (by linarith : 0 < s + sh),
      abs_sub_comm]
    exact mul_le_mul_of_nonneg_right hshs (by linarith)
  have h1 : u * (s + sh) ≤ u * (2 * sh + u) := mul_le_mul_of_nonneg_left (by linarith) hu0.le
  have h2 : u * (2 * sh + u) ≤ u * (284 / 100 + 3 * u) := mul_le_mul_of_nonneg_left (by linarith) hu0.le
  have h3 : u * u ≤ u * (1 / 32) := mul_le_mul_of_nonneg_left hu hu0.le
  refine ⟨hρ.trans h1, (abs_add_le _ _).trans ?_⟩
  linarith

/-- `x_h` in `[1, 2)`: `ρ₂/(2s_h)` is at most `2u` -/
theorem sqrtDW_A2 {u xl ρ1 sh ρ2 : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 32) (hxl : |xl| ≤ u) (hsh1 : 1 ≤ sh)
    (hρ : |ρ1| ≤ u * (2 * sh + u)) (hε1 : |ρ2 - (xl + ρ1)| ≤ 2 * u ^ 2) : |ρ2 / (2 * sh)| ≤ 2 * u := by
  have h2 : u * 1 ≤ u * sh := mul_le_mul_of_nonneg_left hsh1 hu0.le
  have h3 : u * u ≤ u * (1 / 32) := mul_le_mul_of_nonneg_left hu hu0.le
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * sh), div_le_iff₀ (by linarith)]
  obtain ⟨a1, a2⟩ := abs_le.mp hxl
  obtain ⟨b1, b2⟩ := abs_le.mp hρ
  obtain ⟨c1, c2⟩ := abs_le.mp hε1
  rw [abs_le]
  constructor <;> linarith

/-- `x_h` in `[1, 2)` and `x ≥ 1`: the error is at most `25u²/8` -/
theorem sqrtDW_A3 {u xh xl s sh ρ2 sl S : ℝ} (hx1 : 1 ≤ xh) (hxl : |xl| ≤ u) (hX1 : 1 ≤ xh + xl) (hs0 : 0 ≤ s)
    (hs : s * s = xh) (hS0 : 0 ≤ S) (hS : S * S = xh + xl) (hsh1 : 1 ≤ sh) (hshs : |sh - s| ≤ u)
    (hε1 : |ρ2 - (xl + (xh - sh * sh))| ≤ 2 * u ^ 2) (hε2 : |sl - ρ2 / (2 * sh)| ≤ u ^ 2) :
    |sh + sl - S| ≤ 25 / 8 * u ^ 2 * S := by
  have hs1 : 1 ≤ s := by
    by_contra h
    have h' := not_le.mp h
    nlinarith
  have hS1 : 1 ≤ S := by
    by_contra h
    have h' := not_le.mp h
    nlinarith
  have hsS : |s - S| ≤ u / 2 := by
    have e : (s - S) * (s + S) = -xl := by
      rw [show (s - S) * (s + S) = s * s - S * S by ring, hs, hS]
      ring
    have h : |s - S| * (s + S) = |xl| := by
      rw [← abs_neg xl, ← e, abs_mul, abs_of_pos (by linarith : 0 < s + S)]
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : (2 : ℝ) ≤ s + S) (abs_nonneg (s - S))]
  have hd : |sh - S| ≤ 3 / 2 * u := by
    rw [show sh - S = (sh - s) + (s - S) by ring]
    exact (abs_add_le _ _).trans (by linarith)
  have h := sqrtDW_step (e1 := 2 * u ^ 2) (by norm_num : (0 : ℝ) < 1) hsh1 hS hd
    (by rw [show xh + xl - sh * sh = xl + (xh - sh * sh) by ring]; exact hε1) hε2
  calc |sh + sl - S| ≤ ((3 / 2 * u) ^ 2 + 2 * u ^ 2) / (2 * 1) + u ^ 2 := h
    _ = 25 / 8 * u ^ 2 * 1 := by ring
    _ ≤ 25 / 8 * u ^ 2 * S := mul_le_mul_of_nonneg_left hS1 (by positivity)

/-- `x_h = 1` and `x < 1`: then `s_h = 1`, and the error is at most `17u²/8` -/
theorem sqrtDW_A3' {u xh xl sh ρ2 sl S : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 32) (hxh : xh = 1) (hsh : sh = 1)
    (hxl : |xl| ≤ u / 2) (hX1 : xh + xl < 1) (hS0 : 0 ≤ S) (hS : S * S = xh + xl)
    (hε1 : |ρ2 - (xl + (xh - sh * sh))| ≤ 2 * u ^ 2) (hε2 : |sl - ρ2 / (2 * sh)| ≤ u ^ 2) :
    |sh + sl - S| ≤ 25 / 8 * u ^ 2 * S := by
  subst hxh hsh
  obtain ⟨a1, a2⟩ := abs_le.mp hxl
  have hSlt : S < 1 := by
    by_contra h
    have h' := not_lt.mp h
    nlinarith
  have hSge : 1 + xl ≤ S := by nlinarith [mul_nonneg hS0 (by linarith : (0 : ℝ) ≤ 1 - S)]
  have hd : |(1 : ℝ) - S| ≤ u / 2 := by
    rw [abs_of_pos (by linarith)]
    linarith
  have h := sqrtDW_step (e1 := 2 * u ^ 2) (by norm_num : (0 : ℝ) < 1) le_rfl hS hd
    (by rw [show (1 : ℝ) + xl - 1 * 1 = xl + (1 - 1 * 1) by ring]; exact hε1) hε2
  calc |1 + sl - S| ≤ ((u / 2) ^ 2 + 2 * u ^ 2) / (2 * 1) + u ^ 2 := h
    _ = 25 / 8 * u ^ 2 * (17 / 25) := by ring
    _ ≤ 25 / 8 * u ^ 2 * S := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- `x_h` in `[2, 4)`: `s_h ≥ 1.36`, the remainder is at most `u(2s_h + u)`, and `x_l + ρ₁` at most `8u` -/
theorem sqrtDW_B1 {u xh xl s sh : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 32) (hx1 : 2 ≤ xh) (hxl : |xl| ≤ 2 * u)
    (hs0 : 0 ≤ s) (hs : s * s = xh) (hsh2 : sh ≤ 2) (hshs : |sh - s| ≤ u) :
    136 / 100 ≤ sh ∧ |xh - sh * sh| ≤ u * (2 * sh + u) ∧ |xl + (xh - sh * sh)| ≤ 8 * u := by
  obtain ⟨l1, l2⟩ := abs_le.mp hshs
  have hs141 : 141 / 100 ≤ s := by
    by_contra h
    have h' := not_le.mp h
    nlinarith [mul_pos (sub_pos.mpr h') (by linarith : (0 : ℝ) < 141 / 100 + s)]
  have hsh : 136 / 100 ≤ sh := by linarith
  have hρ : |xh - sh * sh| ≤ u * (s + sh) := by
    rw [← hs, show s * s - sh * sh = (s - sh) * (s + sh) by ring, abs_mul, abs_of_pos (by linarith : 0 < s + sh),
      abs_sub_comm]
    exact mul_le_mul_of_nonneg_right hshs (by linarith)
  have h1 : u * (s + sh) ≤ u * (2 * sh + u) := mul_le_mul_of_nonneg_left (by linarith) hu0.le
  have h2 : u * (2 * sh + u) ≤ u * (4 + u) := mul_le_mul_of_nonneg_left (by linarith) hu0.le
  have h3 : u * u ≤ u * (1 / 32) := mul_le_mul_of_nonneg_left hu hu0.le
  refine ⟨hsh, hρ.trans h1, (abs_add_le _ _).trans ?_⟩
  linarith

/-- `x_h` in `[2, 4)`: `ρ₂/(2s_h)` is at most `2u` -/
theorem sqrtDW_B2 {u xl ρ1 sh ρ2 : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 32) (hxl : |xl| ≤ 2 * u) (hsh : 136 / 100 ≤ sh)
    (hρ : |ρ1| ≤ u * (2 * sh + u)) (hε1 : |ρ2 - (xl + ρ1)| ≤ 4 * u ^ 2) : |ρ2 / (2 * sh)| ≤ 2 * u := by
  have h2 : u * (136 / 100) ≤ u * sh := mul_le_mul_of_nonneg_left hsh hu0.le
  have h3 : u * u ≤ u * (1 / 32) := mul_le_mul_of_nonneg_left hu hu0.le
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * sh), div_le_iff₀ (by linarith)]
  obtain ⟨a1, a2⟩ := abs_le.mp hxl
  obtain ⟨b1, b2⟩ := abs_le.mp hρ
  obtain ⟨c1, c2⟩ := abs_le.mp hε1
  rw [abs_le]
  constructor <;> linarith

/-- `x_h` in `[2, 4)`: the error is at most `3.56u²`, under `25u²/8` of `√x ≥ 1.39` -/
theorem sqrtDW_B3 {u xh xl s sh ρ2 sl S : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 32) (hx1 : 2 ≤ xh) (hxl : |xl| ≤ 2 * u)
    (hs0 : 0 ≤ s) (hs : s * s = xh) (hS0 : 0 ≤ S) (hS : S * S = xh + xl) (hsh : 136 / 100 ≤ sh)
    (hshs : |sh - s| ≤ u) (hε1 : |ρ2 - (xl + (xh - sh * sh))| ≤ 4 * u ^ 2) (hε2 : |sl - ρ2 / (2 * sh)| ≤ u ^ 2) :
    |sh + sl - S| ≤ 25 / 8 * u ^ 2 * S := by
  obtain ⟨a1, a2⟩ := abs_le.mp hxl
  have hs141 : 141 / 100 ≤ s := by
    by_contra h
    have h' := not_le.mp h
    nlinarith [mul_pos (sub_pos.mpr h') (by linarith : (0 : ℝ) < 141 / 100 + s)]
  have hS139 : 139 / 100 ≤ S := by
    by_contra h
    have h' := not_le.mp h
    nlinarith [mul_pos (sub_pos.mpr h') (by linarith : (0 : ℝ) < 139 / 100 + S)]
  have hsS : |s - S| ≤ 72 / 100 * u := by
    have e : (s - S) * (s + S) = -xl := by
      rw [show (s - S) * (s + S) = s * s - S * S by ring, hs, hS]
      ring
    have h : |s - S| * (s + S) = |xl| := by
      rw [← abs_neg xl, ← e, abs_mul, abs_of_pos (by linarith : 0 < s + S)]
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : (280 / 100 : ℝ) ≤ s + S) (abs_nonneg (s - S))]
  have hd : |sh - S| ≤ 172 / 100 * u := by
    rw [show sh - S = (sh - s) + (s - S) by ring]
    exact (abs_add_le _ _).trans (by linarith)
  have h := sqrtDW_step (e1 := 4 * u ^ 2) (by norm_num : (0 : ℝ) < 136 / 100) hsh hS hd
    (by rw [show xh + xl - sh * sh = xl + (xh - sh * sh) by ring]; exact hε1) hε2
  have e : ((172 / 100 * u) ^ 2 + 4 * u ^ 2) / (2 * (136 / 100)) + u ^ 2 = 96784 / 27200 * u ^ 2 := by ring
  rw [e] at h
  calc |sh + sl - S| ≤ 96784 / 27200 * u ^ 2 := h
    _ ≤ 25 / 8 * u ^ 2 * (139 / 100) := by nlinarith [sq_nonneg u]
    _ ≤ 25 / 8 * u ^ 2 * S := mul_le_mul_of_nonneg_left hS139 (by positivity)

variable (p : ℤ) [Prec_gt_0 p]

omit [Prec_gt_0 p] in
theorem u_le_32nd (hp : 5 ≤ p) : u p ≤ 1 / 32 := by
  unfold u
  calc (2 : ℝ) ^ (-p) ≤ (2 : ℝ) ^ (-5 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ = 1 / 32 := by norm_num

/-- SQRTDWtoDW, Algorithm 8 of Lefèvre, Louvet, Muller, Picot and Rideau: `√(x_h + x_l)` -/
noncomputable def sqrtDW (xh xl : ℝ) : ℝ × ℝ :=
  let sh := RN p (Real.sqrt xh)
  let ρ1 := RN p (xh - sh * sh)
  let ρ2 := RN p (xl + ρ1)
  let sl := RN p (ρ2 / (2 * sh))
  fastTwoSum p sh sl

/-- `s_h = RN(√x_h)` for `x_h` in `[1, 4)`: it is in `[1, 2]`, within `u` of `√x_h`, and `x_h - s_h²` is in `F` -/
theorem sqrtDW_sh (hp : 1 < p) {xh : ℝ} (hxh : F p xh) (h1 : 1 ≤ xh) (h4 : xh < 4) :
    1 ≤ RN p (Real.sqrt xh) ∧ RN p (Real.sqrt xh) ≤ 2 ∧ |RN p (Real.sqrt xh) - Real.sqrt xh| ≤ u p ∧
      F p (xh - RN p (Real.sqrt xh) * RN p (Real.sqrt xh)) := by
  have hu := u_pos p
  obtain ⟨s, hsd⟩ : ∃ s, s = Real.sqrt xh := ⟨_, rfl⟩
  rw [← hsd]
  have hs0 : 0 ≤ s := hsd ▸ Real.sqrt_nonneg _
  have hs : s * s = xh := by rw [hsd]; exact Real.mul_self_sqrt (by linarith)
  have hs1 : 1 ≤ s := by
    by_contra h
    have h' := not_le.mp h
    nlinarith
  have hs2 : s ≤ 2 := by
    by_contra h
    have h' := not_le.mp h
    nlinarith
  have hF2 : F p 2 := by simpa using F_two_zpow p 1
  have hsh1 : 1 ≤ RN p s := by
    have := RN_mono p hs1
    rwa [RN_of_F p (F_one p)] at this
  have hsh2 : RN p s ≤ 2 := by
    have := RN_mono p hs2
    rwa [RN_of_F p hF2] at this
  have herr : |RN p s - s| ≤ u p := by
    have := RN_grid p 1 (z := s) (by rw [zpow_one, abs_of_nonneg hs0]; exact hs2)
    rw [zpow_one] at this
    linarith
  refine ⟨hsh1, hsh2, herr, ?_⟩
  obtain ⟨sh, hshd⟩ : ∃ sh, sh = RN p s := ⟨_, rfl⟩
  rw [← hshd] at hsh1 hsh2 herr ⊢
  have hmx : Mult (1 - p) xh := mult_of_F p hxh (by
    rw [show (1 - p + p - 1 : ℤ) = 0 by ring, zpow_zero, abs_of_pos (by linarith)]; exact h1)
  have hms : Mult (1 - p) sh := mult_of_F p (hshd ▸ F_RN p _) (by
    rw [show (1 - p + p - 1 : ℤ) = 0 by ring, zpow_zero, abs_of_pos (by linarith)]; exact hsh1)
  have hm : Mult ((1 - p) + (1 - p)) (xh - sh * sh) := (hmx.mono (by omega)).sub (hms.mul hms)
  refine F_of_mult_le p hm ?_
  -- `|x_h - s_h²| = |s - s_h|(s + s_h) ≤ 4u`
  have e4 : (2 : ℝ) ^ (1 - p + (1 - p) + p) = 4 * u p := by
    rw [show (1 - p + (1 - p) + p : ℤ) = 2 - p by ring, two_zpow_sub_p]
    norm_num
  rw [e4, ← hs, show s * s - sh * sh = (s - sh) * (s + sh) by ring, abs_mul, abs_of_pos (by linarith : 0 < s + sh),
    abs_sub_comm]
  calc |sh - s| * (s + sh) ≤ u p * 4 := mul_le_mul herr (by linarith) (by linarith) hu.le
    _ = 4 * u p := by ring

/-- Theorem 3.5 of LLMPR23 (HAL hal-03482567v1) for `x_h` in `[1, 4)` -/
theorem sqrtDW_norm (hp : 5 ≤ p) {xh xl : ℝ} (hxh : F p xh) (hdw : RN p (xh + xl) = xh) (h1 : 1 ≤ xh)
    (h4 : xh < 4) :
    |(sqrtDW p xh xl).1 + (sqrtDW p xh xl).2 - Real.sqrt (xh + xl)| ≤ 25 / 8 * u p ^ 2 * Real.sqrt (xh + xl) ∧
      RN p ((sqrtDW p xh xl).1 + (sqrtDW p xh xl).2) = (sqrtDW p xh xl).1 := by
  have hu0 := u_pos p
  have hu := u_le_32nd p hp
  obtain ⟨hsh1, hsh2, hshs, hρF⟩ := sqrtDW_sh p (by omega) hxh h1 h4
  obtain ⟨s, hsd⟩ : ∃ s, s = Real.sqrt xh := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := hsd ▸ Real.sqrt_nonneg _
  have hs : s * s = xh := by rw [hsd]; exact Real.mul_self_sqrt (by linarith)
  rw [← hsd] at hsh1 hsh2 hshs hρF
  obtain ⟨sh, hshd⟩ : ∃ sh, sh = RN p s := ⟨_, rfl⟩
  have hshF : F p sh := hshd ▸ F_RN p _
  rw [← hshd] at hsh1 hsh2 hshs hρF
  -- `x = x_h + x_l` is positive
  have hxlu := dw_lo_le_u p hdw
  rw [abs_of_pos (by linarith : 0 < xh)] at hxlu
  have hX0 : 0 ≤ xh + xl := by nlinarith [(abs_le.mp hxlu).1]
  obtain ⟨S, hSd⟩ : ∃ S, S = Real.sqrt (xh + xl) := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := hSd ▸ Real.sqrt_nonneg _
  have hS : S * S = xh + xl := by rw [hSd]; exact Real.mul_self_sqrt hX0
  -- the steps of the algorithm
  obtain ⟨ρ2, hρ2d⟩ : ∃ ρ2, ρ2 = RN p (xl + (xh - sh * sh)) := ⟨_, rfl⟩
  obtain ⟨sl, hsld⟩ : ∃ sl, sl = RN p (ρ2 / (2 * sh)) := ⟨_, rfl⟩
  have hdef : sqrtDW p xh xl = fastTwoSum p sh sl := by
    simp only [sqrtDW]
    rw [← hsd, ← hshd, RN_of_F p hρF, ← hρ2d, ← hsld]
  have e2 : (2 : ℝ) ^ ((1 : ℤ) - p) = 2 * u p := by rw [two_zpow_sub_p, zpow_one]
  have e4 : (2 : ℝ) ^ ((2 : ℤ) - p) = 4 * u p := by rw [two_zpow_sub_p]; norm_num
  have e8 : (2 : ℝ) ^ ((3 : ℤ) - p) = 8 * u p := by rw [two_zpow_sub_p]; norm_num
  -- the error, and `|ρ₂/(2s_h)| ≤ 2u`
  have key : |sh + sl - S| ≤ 25 / 8 * u p ^ 2 * S ∧ |ρ2 / (2 * sh)| ≤ 2 * u p := by
    rcases lt_or_ge xh 2 with hlt | hge
    · have hxl := dw_lo_le p (by omega) hxh hdw h1 hlt
      obtain ⟨a1, a2⟩ := sqrtDW_A1 hu0 hu hlt hxl hs hsh1 hshs
      have hε1 : |ρ2 - (xl + (xh - sh * sh))| ≤ 2 * u p ^ 2 := by
        have h := RN_grid p (2 - p) (z := xl + (xh - sh * sh)) (by rw [e4]; exact a2)
        rw [e4, ← hρ2d] at h
        linarith
      have a3 := sqrtDW_A2 hu0 hu hxl hsh1 a1 hε1
      have hε2 : |sl - ρ2 / (2 * sh)| ≤ u p ^ 2 := by
        have h := RN_grid p (1 - p) (z := ρ2 / (2 * sh)) (by rw [e2]; exact a3)
        rw [e2, ← hsld] at h
        linarith
      refine ⟨?_, a3⟩
      rcases le_or_gt 1 (xh + xl) with hX1 | hX1
      · exact sqrtDW_A3 h1 hxl hX1 hs0 hs hS0 hS hsh1 hshs hε1 hε2
      · -- `x < 1`: then `x_h = 1` and `s_h = 1`
        have hxh1 : xh = 1 := by
          have h := RN_mono p hX1.le
          rw [hdw, RN_of_F p (F_one p)] at h
          linarith
        have hs1 : s = 1 := by rw [hsd, hxh1, Real.sqrt_one]
        have hsh1' : sh = 1 := by rw [hshd, hs1, RN_of_F p (F_one p)]
        have hxl2 : |xl| ≤ u p / 2 := by
          have h := RN_grid p 0 (z := xh + xl) (by
            rw [zpow_zero, abs_of_nonneg hX0]; exact hX1.le)
          rw [hdw, zpow_zero, show xh - (xh + xl) = -xl by ring, abs_neg] at h
          linarith
        exact sqrtDW_A3' hu0 hu hxh1 hsh1' hxl2 hX1 hS0 hS hε1 hε2
    · have hxl : |xl| ≤ 2 * u p := by
        have hh : (2 : ℝ) ^ (-1 : ℤ) = 1 / 2 := by norm_num
        have h := dw_lo_le p (by omega) (F_zpow_mul p (-1) hxh) (xl := (2 : ℝ) ^ (-1 : ℤ) * xl)
          (by rw [← mul_add, RN_zpow_mul, hdw]) (by rw [hh]; linarith) (by rw [hh]; linarith)
        rw [hh, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
        linarith
      obtain ⟨a0, a1, a2⟩ := sqrtDW_B1 hu0 hu hge hxl hs0 hs hsh2 hshs
      have hε1 : |ρ2 - (xl + (xh - sh * sh))| ≤ 4 * u p ^ 2 := by
        have h := RN_grid p (3 - p) (z := xl + (xh - sh * sh)) (by rw [e8]; exact a2)
        rw [e8, ← hρ2d] at h
        linarith
      have a3 := sqrtDW_B2 hu0 hu hxl a0 a1 hε1
      have hε2 : |sl - ρ2 / (2 * sh)| ≤ u p ^ 2 := by
        have h := RN_grid p (1 - p) (z := ρ2 / (2 * sh)) (by rw [e2]; exact a3)
        rw [e2, ← hsld] at h
        linarith
      exact ⟨sqrtDW_B3 hu0 hu hge hxl hs0 hs hS0 hS a0 hshs hε1 hε2, a3⟩
  obtain ⟨herr, hq⟩ := key
  -- the last Fast2Sum is exact: `|s_l| ≤ (1 + u)2u ≤ 1 ≤ s_h`
  have hle : |sl| ≤ |sh| := by
    have h := abs_RN_le p (ρ2 / (2 * sh))
    rw [← hsld] at h
    have h3 : (1 + u p) * |ρ2 / (2 * sh)| ≤ (1 + u p) * (2 * u p) := mul_le_mul_of_nonneg_left hq (by linarith)
    have h4 : u p * u p ≤ u p * (1 / 32) := mul_le_mul_of_nonneg_left hu hu0.le
    rw [abs_of_pos (by linarith : 0 < sh)]
    linarith
  have hsum := fastTwoSum_add p (by omega) hshF (hsld ▸ F_RN p _) hle
  rw [hdef, hsum, ← hSd]
  exact ⟨herr, rfl⟩

omit [Prec_gt_0 p] in
/-- SQRTDWtoDW commutes with a scaling by a power of four -/
theorem sqrtDW_scale (k : ℤ) (xh xl : ℝ) : sqrtDW p ((2 : ℝ) ^ (2 * k) * xh) ((2 : ℝ) ^ (2 * k) * xl) =
    ((2 : ℝ) ^ k * (sqrtDW p xh xl).1, (2 : ℝ) ^ k * (sqrtDW p xh xl).2) := by
  have h2 : (2 : ℝ) ^ (2 * k) = (2 : ℝ) ^ k * (2 : ℝ) ^ k := by rw [two_mul, zpow_add₀ two_ne_zero]
  have hk : (2 : ℝ) ^ k ≠ 0 := zpow_ne_zero k two_ne_zero
  have hsq : Real.sqrt ((2 : ℝ) ^ (2 * k) * xh) = (2 : ℝ) ^ k * Real.sqrt xh := by
    rw [Real.sqrt_mul (by positivity), h2, Real.sqrt_mul_self (by positivity)]
  have e1 : ∀ a b : ℝ, (2 : ℝ) ^ (2 * k) * a - (2 : ℝ) ^ k * b * ((2 : ℝ) ^ k * b) = (2 : ℝ) ^ (2 * k) * (a - b * b) :=
    fun a b => by rw [h2]; ring
  have e2 : ∀ a b : ℝ, (2 : ℝ) ^ (2 * k) * a + (2 : ℝ) ^ (2 * k) * b = (2 : ℝ) ^ (2 * k) * (a + b) :=
    fun a b => by ring
  have e3 : ∀ a b : ℝ, (2 : ℝ) ^ (2 * k) * a / (2 * ((2 : ℝ) ^ k * b)) = (2 : ℝ) ^ k * (a / (2 * b)) := fun a b => by
    rw [h2, show 2 * ((2 : ℝ) ^ k * b) = (2 : ℝ) ^ k * (2 * b) by ring, mul_assoc, mul_div_mul_left _ _ hk,
      mul_div_assoc]
  simp only [sqrtDW, hsq, RN_zpow_mul, e1, e2, e3, fastTwoSum_scale]

/-- Theorem 3.5 of LLMPR23 (HAL hal-03482567v1): for `p ≥ 5`, SQRTDWtoDW of a double word `x = (x_h, x_l)` with
`x_h > 0` is within `25u²/8` of `√x`, relatively; its result is a double word -/
theorem sqrtDW_err (hp : 5 ≤ p) {xh xl : ℝ} (hdw : RN p (xh + xl) = xh) (hx0 : 0 < xh) :
    |(sqrtDW p xh xl).1 + (sqrtDW p xh xl).2 - Real.sqrt (xh + xl)| ≤ 25 / 8 * u p ^ 2 * Real.sqrt (xh + xl) ∧
      RN p ((sqrtDW p xh xl).1 + (sqrtDW p xh xl).2) = (sqrtDW p xh xl).1 := by
  have hxh : F p xh := hdw ▸ F_RN p _
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hx0 (by norm_num : (1 : ℝ) < 4)
  have h4 : ∀ m : ℤ, (4 : ℝ) ^ m = (2 : ℝ) ^ (2 * m) := fun m => by
    rw [zpow_mul]
    norm_num
  rw [h4] at hn1 hn2
  have ha : (0 : ℝ) < (2 : ℝ) ^ (2 * -n) := by positivity
  have hb : (0 : ℝ) < (2 : ℝ) ^ (-n) := by positivity
  have s1 : (2 : ℝ) ^ (2 * -n) * (2 : ℝ) ^ (2 * n) = 1 := by
    rw [← zpow_add₀ two_ne_zero, show 2 * -n + 2 * n = (0 : ℤ) by ring, zpow_zero]
  have s2 : (2 : ℝ) ^ (2 * -n) * (2 : ℝ) ^ (2 * (n + 1)) = 4 := by
    rw [← zpow_add₀ two_ne_zero, show 2 * -n + 2 * (n + 1) = (2 : ℤ) by ring]
    norm_num
  obtain ⟨herr, hdw'⟩ := sqrtDW_norm p hp (F_zpow_mul p (2 * -n) hxh) (xl := (2 : ℝ) ^ (2 * -n) * xl)
    (by rw [← mul_add, RN_zpow_mul, hdw])
    (by have := mul_le_mul_of_nonneg_left hn1 ha.le; rwa [s1] at this)
    (by have := mul_lt_mul_of_pos_left hn2 ha; rwa [s2] at this)
  rw [sqrtDW_scale] at herr hdw'
  simp only [] at herr hdw'
  have hsq : Real.sqrt ((2 : ℝ) ^ (2 * -n) * xh + (2 : ℝ) ^ (2 * -n) * xl) = (2 : ℝ) ^ (-n) * Real.sqrt (xh + xl) := by
    rw [← mul_add, Real.sqrt_mul (by positivity),
      show (2 : ℝ) ^ (2 * -n) = (2 : ℝ) ^ (-n) * (2 : ℝ) ^ (-n) by rw [two_mul, zpow_add₀ two_ne_zero],
      Real.sqrt_mul_self (by positivity)]
  rw [hsq] at herr
  constructor
  · rw [show (2 : ℝ) ^ (-n) * (sqrtDW p xh xl).1 + (2 : ℝ) ^ (-n) * (sqrtDW p xh xl).2 -
        (2 : ℝ) ^ (-n) * Real.sqrt (xh + xl) =
          (2 : ℝ) ^ (-n) * ((sqrtDW p xh xl).1 + (sqrtDW p xh xl).2 - Real.sqrt (xh + xl)) by ring,
      abs_mul, abs_of_pos hb,
      show 25 / 8 * u p ^ 2 * ((2 : ℝ) ^ (-n) * Real.sqrt (xh + xl)) =
        (2 : ℝ) ^ (-n) * (25 / 8 * u p ^ 2 * Real.sqrt (xh + xl)) by ring] at herr
    exact le_of_mul_le_mul_left herr hb
  · rw [← mul_add, RN_zpow_mul] at hdw'
    exact mul_left_cancel₀ hb.ne' hdw'

end ExpansionBounds
