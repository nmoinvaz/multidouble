import ExpansionBounds.LnB
import ExpansionBounds.LogThm

/-!
# Proposition 44 (`prop:ddexplog`): the start of `DD::ln`

`DD::ln` starts from `y_0 = RN(ln_b(x_h) + RN(x_l/x_h))` for a double word `x = x_h + x_l` with `|x_l/x_h| ≤ u`. With
Lemma 43's `η_b = 5.915u` and `δ_1 = u/(1 - u)`, `|y_0 - ln x| ≤ E(ℓ)` for `ℓ ≥ |ln x|`, the proposition's
`E(ℓ) = (η_b + u(1 + η_b))ℓ + η_bδ_1 + u² + u²/(2(1 - u)) + u((1 + η_b)δ_1 + u(1 + u))` with `η_0 = 0`, as the
exponent range is unbounded.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) [Prec_gt_0 p]

/-- Proposition 44's start, with an unbounded exponent range so `η_0 = 0`: for positive `x_h ∈ F`, `|x_l/x_h| ≤ u` and
`ℓ ≥ |ln x|`, `|RN(ln_b(x_h) + RN(x_l/x_h)) - ln x| ≤ E(ℓ)` -/
theorem prop44_start (hp : p = 53) {xh xl ℓ : ℝ} (hxh : F p xh) (hxh0 : 0 < xh) (hv : |xl / xh| ≤ u p)
    (hℓ : |Real.log (xh + xl)| ≤ ℓ) :
    |RN p (lnB p xh + RN p (xl / xh)) - Real.log (xh + xl)| ≤
      (5915 / 1000 * u p + u p * (1 + 5915 / 1000 * u p)) * ℓ + 5915 / 1000 * u p * (u p / (1 - u p)) +
        u p ^ 2 + u p ^ 2 / (2 * (1 - u p)) +
        u p * ((1 + 5915 / 1000 * u p) * (u p / (1 - u p)) + u p * (1 + u p)) := by
  have hu := u_pos p
  have hu53 : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num
  have hu1 : u p < 1 := by rw [hu53]; norm_num
  have hus := us_le_u p
  set v := xl / xh with hvd
  set η := 5915 / 1000 * u p with hη
  set δ1 := u p / (1 - u p) with hδ1
  have hη0 : 0 ≤ η := by positivity
  have hv1 : |v| < 1 := lt_of_le_of_lt hv hu1
  -- `x = x_h(1 + v)`, so `ln x = ln x_h + ln(1 + v)` with `|ln(1 + v)| ≤ δ_1`
  have h1v : 0 < 1 + v := by linarith [neg_abs_le v]
  have hx : xh + xl = xh * (1 + v) := by rw [hvd]; field_simp
  have hlx : Real.log (xh + xl) = Real.log xh + Real.log (1 + v) := by
    rw [hx, Real.log_mul hxh0.ne' h1v.ne']
  have hl1v : |Real.log (1 + v)| ≤ δ1 := by
    have h := log_lip (x := v) (y := 0) (C := u p) hv (by rw [abs_zero]; exact hu.le) hu1
    rw [add_zero, Real.log_one, sub_zero, sub_zero] at h
    exact h.trans (div_le_div_of_nonneg_right hv (by linarith))
  have hlxh : |Real.log xh| ≤ ℓ + δ1 := by
    have : Real.log xh = Real.log (xh + xl) - Real.log (1 + v) := by rw [hlx]; ring
    rw [this]
    exact (abs_sub _ _).trans (add_le_add hℓ hl1v)
  -- the three errors: `ln_b`, `RN(v)` and `ln(1 + v) ≈ v`
  have hL := (lemma43 p hp).2 xh hxh0 hxh
  set L := lnB p xh with hLd
  set w := RN p v with hwd
  have hw : |w - v| ≤ u p * u p :=
    (abs_RN_sub_le_us p v).trans (mul_le_mul hus hv (abs_nonneg _) hu.le)
  have ht := log_tail (c := v) hv1 1
  simp only [range_one, sum_singleton, Nat.cast_zero, Nat.cast_one, zero_add, pow_one, div_one] at ht
  have hvl : |v - Real.log (1 + v)| ≤ u p ^ 2 / (2 * (1 - u p)) := by
    rw [abs_sub_comm, show Real.log (1 + v) - v = Real.log (1 + v) + -v by ring]
    refine ht.trans ?_
    rw [show |v| ^ (1 + 1) = |v| ^ 2 by norm_num, show ((1 : ℝ) + 1) = 2 by norm_num]
    exact div_le_div₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg _) hv 2) (by nlinarith)
      (mul_le_mul_of_nonneg_left (by linarith) (by norm_num))
  -- `|L + w| ≤ (1 + η)(ℓ + δ_1) + u(1 + u)`
  have hLw : |L + w| ≤ (1 + η) * (ℓ + δ1) + u p * (1 + u p) := by
    have h1 : |L| ≤ (1 + η) * |Real.log xh| := by
      have := abs_sub_abs_le_abs_sub L (Real.log xh)
      rw [hη]
      linarith
    have h2 : |w| ≤ u p * (1 + u p) := by
      have := abs_sub_abs_le_abs_sub w v
      nlinarith
    calc |L + w| ≤ |L| + |w| := abs_add_le _ _
      _ ≤ (1 + η) * (ℓ + δ1) + u p * (1 + u p) :=
          add_le_add (h1.trans (mul_le_mul_of_nonneg_left hlxh (by linarith))) h2
  have hR := (abs_RN_sub_le_us p (L + w)).trans (mul_le_mul hus hLw (abs_nonneg _) hu.le)
  rw [hlx]
  have e : RN p (L + w) - (Real.log xh + Real.log (1 + v)) =
      (RN p (L + w) - (L + w)) + (L - Real.log xh) + (w - v) + (v - Real.log (1 + v)) := by ring
  rw [e]
  have hη' : |L - Real.log xh| ≤ η * (ℓ + δ1) := hL.trans (mul_le_mul_of_nonneg_left hlxh hη0)
  calc _ ≤ |RN p (L + w) - (L + w)| + |L - Real.log xh| + |w - v| + |v - Real.log (1 + v)| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl))
          le_rfl)
    _ ≤ u p * ((1 + η) * (ℓ + δ1) + u p * (1 + u p)) + η * (ℓ + δ1) + u p * u p + u p ^ 2 / (2 * (1 - u p)) := by
        linarith
    _ = _ := by ring

omit [Prec_gt_0 p] in
/-- a float other than 1 is at least `u` from 1, at `p = 53` -/
theorem F_ne_one_far (hp : p = 53) {h : ℝ} (hF : F p h) (h1 : h ≠ 1) : u p ≤ |h - 1| := by
  have hu53 : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num
  by_cases hb : 1 / 2 ≤ |h|
  · obtain ⟨a, ha⟩ := mult_of_F p (E := -53) hF (by rw [hp]; norm_num; exact hb)
    have h1' : (1 : ℝ) = 9007199254740992 * (2 : ℝ) ^ (-53 : ℤ) := by norm_num
    rw [ha, h1', ← sub_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (-53 : ℤ)), hu53]
    have hne : a ≠ 9007199254740992 := by
      intro h'; apply h1; rw [ha, h', h1']; push_cast; ring
    have : (1 : ℝ) ≤ |(a : ℝ) - 9007199254740992| := by
      have h2 : (1 : ℤ) ≤ |a - 9007199254740992| := Int.one_le_abs (sub_ne_zero.mpr hne)
      exact_mod_cast h2
    calc 1 / 9007199254740992 = 1 * (2 : ℝ) ^ (-53 : ℤ) := by norm_num
      _ ≤ |(a : ℝ) - 9007199254740992| * (2 : ℝ) ^ (-53 : ℤ) := mul_le_mul_of_nonneg_right this (by positivity)
  · push Not at hb
    rw [hu53]
    have := abs_sub_abs_le_abs_sub 1 h
    rw [abs_one, abs_sub_comm] at this
    linarith

/-- Proposition 44's start, with an unbounded exponent range, for `ℓ < u(1 - u)/2`, `ℓ ≥ |ln x|`, `x_h, x_l ∈ F` and
`x > 0`: when `x_h = RN(x_h + x_l)`, as `FastTwoSum` returns, `x_h = 1`, `y_0 = x_l` and
`|y_0 - ln x| ≤ ℓ(u(1 + ℓ) + ℓ)` -/
theorem prop44_start_small (hp : p = 53) {xh xl ℓ : ℝ} (hxh : F p xh) (hxl : F p xl)
    (hr : RN p (xh + xl) = xh) (hxpos : 0 < xh + xl) (hℓ : |Real.log (xh + xl)| ≤ ℓ)
    (hℓu : ℓ < u p * (1 - u p) / 2) :
    xh = 1 ∧ |RN p (lnB p xh + RN p (xl / xh)) - Real.log (xh + xl)| ≤ ℓ * (u p * (1 + ℓ) + ℓ) := by
  have hu := u_pos p
  have hu53 : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num
  have hℓ0 : 0 ≤ ℓ := (abs_nonneg _).trans hℓ
  set x := xh + xl with hxd
  -- `x_h ≠ 1` would put `x` at least `u/2` from 1, and `|ln x| ≥ u(1 - u)/2`
  have hx1 : xh = 1 := by
    by_contra hne
    have hfar := F_ne_one_far p hp hxh hne
    have hn := (RN_nearest p x).2 1 (F_one p)
    rw [hr, abs_sub_comm xh x, abs_sub_comm 1 x] at hn
    have hd : u p / 2 ≤ |x - 1| := by
      have := abs_sub_le xh x 1
      rw [abs_sub_comm xh x] at this
      linarith
    have hlog : u p * (1 - u p) / 2 ≤ |Real.log x| := by
      rcases le_total x 1 with h | h
      · rw [abs_of_nonpos (by linarith : x - 1 ≤ 0)] at hd
        have := Real.log_le_sub_one_of_pos hxpos
        rw [abs_of_nonpos (Real.log_nonpos hxpos.le h)]
        nlinarith
      · rw [abs_of_nonneg (by linarith : 0 ≤ x - 1)] at hd
        have h2 := Real.one_sub_inv_le_log_of_pos hxpos
        rw [abs_of_nonneg (Real.log_nonneg h)]
        have h3 : u p * (1 - u p) / 2 ≤ 1 - x⁻¹ := by
          rw [← one_div, le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hxpos]
          have : (1 - u p * (1 - u p) / 2) * (1 + u p / 2) ≥ 1 := by rw [hu53]; norm_num
          nlinarith
        linarith
    linarith
  refine ⟨hx1, ?_⟩
  -- `y_0 = x_l`, and `|x_l - ln(1 + x_l)| ≤ x_l²/(2(1 - |x_l|)) ≤ ℓ²`
  have hR0 : RN p 0 = 0 := RN_of_F p (F_zero p)
  have hy : RN p (lnB p xh + RN p (xl / xh)) = xl := by
    rw [hx1, (lemma43 p hp).1, div_one, zero_add, RN_of_F p hxl, RN_of_F p hxl]
  rw [hy, hxd, hx1]
  have hl1 : |Real.log (1 + xl)| ≤ ℓ := by rw [← hx1]; exact hℓ
  have hℓ1 : ℓ ≤ 1 / 10 := by rw [hu53] at hℓu; linarith
  -- `|x_l| ≤ e^ℓ - 1 ≤ ℓ(1 + ℓ)`
  have hxl1 : |xl| ≤ ℓ * (1 + ℓ) := by
    have he := Real.abs_exp_sub_one_sub_id_le (x := ℓ) (by rw [abs_of_nonneg hℓ0]; linarith)
    have hp1 : 0 < 1 + xl := by rw [← hx1]; exact hxpos
    rcases le_total 0 xl with h | h
    · rw [abs_of_nonneg h]
      have : Real.log (1 + xl) ≤ ℓ := (le_abs_self _).trans hl1
      have h2 : 1 + xl ≤ Real.exp ℓ := by rw [← Real.exp_log hp1]; exact Real.exp_le_exp.mpr this
      nlinarith [abs_le.mp he]
    · rw [abs_of_nonpos h]
      have : -ℓ ≤ Real.log (1 + xl) := (neg_abs_le _).trans' (neg_le_neg hl1)
      have h2 : Real.exp (-ℓ) ≤ 1 + xl := by rw [← Real.exp_log hp1]; exact Real.exp_le_exp.mpr this
      have h3 := Real.add_one_le_exp (-ℓ)
      nlinarith
  have hxs : |xl| < 1 := by nlinarith
  have ht := log_tail (c := xl) hxs 1
  simp only [range_one, sum_singleton, Nat.cast_zero, Nat.cast_one, zero_add, pow_one, div_one] at ht
  rw [abs_sub_comm, show Real.log (1 + xl) - xl = Real.log (1 + xl) + -xl by ring]
  refine ht.trans ?_
  rw [div_le_iff₀ (by nlinarith)]
  have h4 : |xl| ^ (1 + 1) ≤ (ℓ * (1 + ℓ)) ^ 2 := by
    rw [show 1 + 1 = 2 by norm_num]; exact pow_le_pow_left₀ (abs_nonneg _) hxl1 2
  have h5 : (ℓ * (1 + ℓ)) ^ 2 ≤ ℓ * ℓ * ((1 + 1) * (1 - |xl|)) := by
    have : (1 + ℓ) ^ 2 ≤ (1 + 1) * (1 - ℓ * (1 + ℓ)) := by nlinarith
    nlinarith [mul_nonneg hℓ0 hℓ0]
  have h6 : ℓ * ℓ ≤ ℓ * (u p * (1 + ℓ) + ℓ) := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg hℓ0 hℓ0) (by linarith : (0 : ℝ) ≤ (1 + 1) * (1 - |xl|))]

end ExpansionBounds
