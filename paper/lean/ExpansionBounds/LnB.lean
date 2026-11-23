import ExpansionBounds.ExpThm
import ExpansionBounds.ExpRed
import ExpansionBounds.SinCos
import ExpansionBounds.Sharp
import FloatSpec.src.Prop.Sterbenz
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Lemma 43 (`lem:lnb`): the binary64 logarithm `ln_b`

`ln_b(h)`, for a positive `h ∈ F` at `p = 53`, writes `h = 2^e m` with `m ∈ (μ/2, μ]`, `μ = RN(√2)`, forms
`s = RN((m - 1)/RN(m + 1))` and `z = RN(s²)`, evaluates `v = Σ_{j ≤ 9} z^j/(2j + 1)` by Horner's rule with fused
multiply-adds from `c_j = RN(1/(2j + 1))`, and returns `RN(ec_L + RN(2sv))`, `c_L = RN(ln 2)`. Then `ln_b(1) = 0` and
`|ln_b(h) - ln h| ≤ 5.915u|ln h|`. The exponent range is unbounded, so the scaling of subnormal `h` is the identity.
-/

namespace ExpansionBounds

open Finset

/-! ## The series of `artanh` -/

/-- `Σ_{k < K} y^k/(2k + 1)` -/
noncomputable def atS (y : ℝ) (K : ℕ) : ℝ := ∑ k ∈ range K, y ^ k / (2 * k + 1)

theorem atS_summable {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) : Summable fun k : ℕ => y ^ k / (2 * k + 1) :=
  (summable_geometric_of_lt_one h0 h1).of_nonneg_of_le (fun k => by positivity)
    (fun k => div_le_self (pow_nonneg h0 k) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]))

/-- the tail after `K` terms: `V_K ≤ V_∞ ≤ V_K + y^K/((2K + 1)(1 - y))` -/
theorem atS_tail {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) (K : ℕ) :
    atS y K ≤ ∑' k : ℕ, y ^ k / (2 * k + 1) ∧
      ∑' k : ℕ, y ^ k / (2 * k + 1) ≤ atS y K + y ^ K / ((2 * K + 1) * (1 - y)) := by
  have hs := atS_summable h0 h1
  refine ⟨hs.sum_le_tsum _ (fun k _ => by positivity), ?_⟩
  rw [← hs.sum_add_tsum_nat_add K]
  refine add_le_add le_rfl ?_
  have hg : HasSum (fun k : ℕ => y ^ K / (2 * K + 1) * y ^ k) (y ^ K / (2 * K + 1) * (1 - y)⁻¹) :=
    (hasSum_geometric_of_lt_one h0 h1).mul_left _
  have hle : ∀ k : ℕ, y ^ (k + K) / (2 * ((k + K : ℕ) : ℝ) + 1) ≤ y ^ K / (2 * K + 1) * y ^ k := by
    intro k
    rw [pow_add, div_mul_eq_mul_div, mul_comm (y ^ K)]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    push_cast
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  calc ∑' k : ℕ, y ^ (k + K) / (2 * ((k + K : ℕ) : ℝ) + 1) ≤ y ^ K / (2 * K + 1) * (1 - y)⁻¹ :=
        (hs.comp_injective (add_left_injective K)).tsum_le_of_sum_le fun s => (sum_le_sum fun k _ => hle k).trans
          (hg.summable.sum_le_tsum s (fun k _ => by positivity) |>.trans_eq hg.tsum_eq)
    _ = y ^ K / ((2 * K + 1) * (1 - y)) := by rw [div_mul_eq_div_div, div_eq_mul_inv (y ^ K / (2 * K + 1))]

/-- `ln((1 + x)/(1 - x)) = 2x V_∞(x²)` for `|x| < 1` -/
theorem log_artanh {x : ℝ} (h : |x| < 1) :
    Real.log (1 + x) - Real.log (1 - x) = 2 * x * ∑' k : ℕ, (x ^ 2) ^ k / (2 * k + 1) := by
  have hx2 : x ^ 2 < 1 := by rw [← sq_abs]; nlinarith [abs_nonneg x]
  have hs := (atS_summable (sq_nonneg x) hx2).hasSum.mul_left (2 * x)
  refine (Real.hasSum_log_sub_log_of_abs_lt_one h).unique ?_
  convert hs using 1
  funext k
  rw [pow_succ, pow_mul]
  ring

/-- `ln 2 = (2/3)V_∞(1/9)`, within `1.7·10^{-23}` -/
theorem log_two_bounds :
    2 / 3 * atS (1 / 9) 22 ≤ Real.log 2 ∧
      Real.log 2 ≤ 2 / 3 * atS (1 / 9) 22 + 2 / 3 * ((1 / 9) ^ 22 / (45 * (8 / 9))) := by
  have h := log_artanh (x := 1 / 3) (by rw [abs_of_pos (by norm_num)]; norm_num)
  rw [show Real.log (1 + 1 / 3) - Real.log (1 - 1 / 3) = Real.log 2 by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num] at h
  obtain ⟨h1, h2⟩ := atS_tail (y := 1 / 9) (by norm_num) (by norm_num) 22
  rw [show ((1 : ℝ) / 3) ^ 2 = 1 / 9 by norm_num] at h
  rw [h]
  constructor
  · nlinarith
  · have : ((1 : ℝ) / 9) ^ 22 / ((2 * (22 : ℕ) + 1) * (1 - 1 / 9)) = (1 / 9) ^ 22 / (45 * (8 / 9)) := by norm_num
    rw [this] at h2
    nlinarith

/-! ## Rounding to a known float -/

variable (p : ℤ) [Prec_gt_0 p]

/-- `RN(x) = f` when `f ∈ F` and `x` lie at or above `2^{E+p-1}` and `|x - f| < 2^E/2`, half the spacing there -/
theorem RN_eq_of_near {E : ℤ} {x f : ℝ} (hf : F p f) (hfE : (2 : ℝ) ^ (E + p - 1) ≤ f)
    (hxE : (2 : ℝ) ^ (E + p - 1) ≤ x) (hxf : |x - f| < (2 : ℝ) ^ E / 2) : RN p x = f := by
  have hP : (0 : ℝ) < (2 : ℝ) ^ (E + p - 1) := by positivity
  have hg : (2 : ℝ) ^ (E + p - 1) ≤ RN p x := by
    have := RN_mono p hxE
    rwa [RN_of_F p (F_two_zpow p _)] at this
  obtain ⟨a, ha⟩ := mult_of_F p (F_RN p x) (by rw [abs_of_pos (hP.trans_le hg)]; exact hg)
  obtain ⟨b, hb⟩ := mult_of_F p hf (by rw [abs_of_pos (hP.trans_le hfE)]; exact hfE)
  have hn := (RN_nearest p x).2 f hf
  have hd : |RN p x - f| < (2 : ℝ) ^ E := by
    have := abs_sub_le (RN p x) x f
    have hxf' : |f - x| < (2 : ℝ) ^ E / 2 := by rw [abs_sub_comm]; exact hxf
    linarith
  rw [ha, hb, ← sub_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ E)] at hd
  have hab : |((a - b : ℤ) : ℝ)| < 1 := by
    push_cast
    exact (mul_lt_iff_lt_one_left (by positivity)).mp hd
  have : a = b := by
    have h1 : |a - b| < 1 := by exact_mod_cast hab
    have := abs_lt.mp h1
    omega
  rw [ha, hb, this]

/-- `√2` within `10^{-19}` -/
theorem sqrt_two_bounds : (14142135623730950488 / 10 ^ 19 : ℝ) ≤ Real.sqrt 2 ∧
    Real.sqrt 2 ≤ 14142135623730950489 / 10 ^ 19 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num

/-- `μ = RN(√2) = 6369051672525773·2^{-52}` -/
theorem mu_eq (hp : p = 53) : RN p (Real.sqrt 2) = 6369051672525773 / 2 ^ 52 := by
  obtain ⟨h1, h2⟩ := sqrt_two_bounds
  have hF : F p (6369051672525773 / 2 ^ 52) := by
    refine F_of_mult p (E := -52) ⟨6369051672525773, by norm_num⟩ ?_
    rw [hp]; norm_num
  refine RN_eq_of_near p (E := -52) hF ?_ ?_ ?_
  · rw [hp]; norm_num
  · rw [hp]; norm_num; try linarith
  · rw [abs_lt]; constructor <;> norm_num <;> linarith

/-- `c_L = RN(ln 2) = 6243314768165359·2^{-53}` -/
theorem cL_eq (hp : p = 53) : RN p (Real.log 2) = 6243314768165359 / 2 ^ 53 := by
  obtain ⟨h1, h2⟩ := log_two_bounds
  simp only [atS, sum_range_succ, sum_range_zero] at h1 h2
  norm_num at h1 h2
  have hF : F p (6243314768165359 / 2 ^ 53) := by
    refine F_of_mult p (E := -53) ⟨6243314768165359, by norm_num⟩ ?_
    rw [hp]; norm_num
  refine RN_eq_of_near p (E := -53) hF ?_ ?_ ?_
  · rw [hp]; norm_num
  · rw [hp]; norm_num; try linarith
  · rw [abs_lt]; constructor <;> norm_num <;> linarith

/-! ## The routine -/

/-- `c_j = RN(1/(2j + 1))` -/
noncomputable def lnbC (j : ℕ) : ℝ := RN p (1 / (2 * j + 1))

/-- Horner's `v` after `k` fused multiply-adds from `c_9`: `v ← RN(zv + c_{8-k})` -/
noncomputable def lnbW (z : ℝ) : ℕ → ℝ
  | 0 => lnbC p 9
  | k + 1 => RN p (z * lnbW z k + lnbC p (8 - k))

omit [Prec_gt_0 p] in
/-- its exact value `V_{9-k}(z)` -/
noncomputable def lnbV (z : ℝ) : ℕ → ℝ
  | 0 => 1 / 19
  | k + 1 => z * lnbV z k + 1 / (2 * ((8 - k : ℕ) : ℝ) + 1)

omit [Prec_gt_0 p] in
/-- `h = 2^{e_0}m_0` with `m_0 ∈ [1, 2)` -/
noncomputable def lnbE0 (h : ℝ) : ℤ := ⌊Real.log h / Real.log 2⌋

/-- `e`, raised by one where `m_0 > μ` -/
noncomputable def lnbE (h : ℝ) : ℤ := if RN p (Real.sqrt 2) < h / 2 ^ lnbE0 h then lnbE0 h + 1 else lnbE0 h

/-- `s = RN((m - 1)/RN(m + 1))`, with `m - 1` rounded too -/
noncomputable def lnbS (m : ℝ) : ℝ := RN p (RN p (m - 1) / RN p (m + 1))

/-- `ln_b(h) = RN(ec_L + RN(2sv))` with `m = 2^{-e}h`, `s` and `z = RN(s²)` -/
noncomputable def lnB (h : ℝ) : ℝ :=
  RN p (lnbE p h * RN p (Real.log 2) + RN p (2 * lnbS p (h / 2 ^ lnbE p h) *
    lnbW p (RN p (lnbS p (h / 2 ^ lnbE p h) * lnbS p (h / 2 ^ lnbE p h))) 9))

omit [Prec_gt_0 p] in
theorem lnbV_nine (z : ℝ) : lnbV z 9 = atS z 10 := by
  simp only [lnbV, atS, sum_range_succ, sum_range_zero]
  norm_num
  ring

omit [Prec_gt_0 p] in
/-- `0 ≤ V(z) ≤ V(Z)` for `0 ≤ z ≤ Z` -/
theorem lnbV_mono {z Z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ Z) (k : ℕ) : 0 ≤ lnbV z k ∧ lnbV z k ≤ lnbV Z k := by
  induction k with
  | zero => simp only [lnbV]; norm_num
  | succ k ih =>
    simp only [lnbV]
    have hp : (0 : ℝ) ≤ 1 / (2 * ((8 - k : ℕ) : ℝ) + 1) := by positivity
    exact ⟨by nlinarith [ih.1], by nlinarith [ih.1, ih.2]⟩

/-- one fused multiply-add of Horner's rule: with `v` within `r` of `A`, `c` within `c_e ≤ r` of `γ` and
`0 ≤ zA ≤ Q`, `RN(zv + c)` is within `((Qr + γc_e)/(Q + γ) + 1)(1 + ū) - 1` of `zA + γ` -/
theorem horner_rel {z A v c γ r ce Q : ℝ} (hz : 0 ≤ z) (hA : 0 ≤ A) (hQ : z * A ≤ Q) (hγ : 0 < γ)
    (hce : 0 ≤ ce) (hcr : ce ≤ r) (hv : |v - A| ≤ r * A) (hc : |c - γ| ≤ ce * γ) :
    |RN p (z * v + c) - (z * A + γ)| ≤ (((Q * r + γ * ce) / (Q + γ) + 1) * (1 + us p) - 1) * (z * A + γ) := by
  set q := z * A with hq
  have hq0 : 0 ≤ q := mul_nonneg hz hA
  have hQ0 : 0 ≤ Q := hq0.trans hQ
  have hr0 : 0 ≤ r := hce.trans hcr
  set ρ := (Q * r + γ * ce) / (Q + γ) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have h1 : |z * v + c - (q + γ)| ≤ r * q + ce * γ := by
    rw [show z * v + c - (q + γ) = z * (v - A) + (c - γ) by rw [hq]; ring]
    refine (abs_add_le _ _).trans (add_le_add ?_ hc)
    rw [abs_mul, abs_of_nonneg hz]
    exact (mul_le_mul_of_nonneg_left hv hz).trans_eq (by rw [hq]; ring)
  have h2 : r * q + ce * γ ≤ ρ * (q + γ) := by
    rw [hρ, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hγ.le (sub_nonneg.mpr hQ)) (sub_nonneg.mpr hcr)]
  have h3 : |RN p (z * v + c) - (z * v + c)| ≤ us p * ((1 + ρ) * (q + γ)) := by
    refine (abs_RN_sub_le_us p _).trans (mul_le_mul_of_nonneg_left ?_ (us_nonneg p))
    have := abs_sub_abs_le_abs_sub (z * v + c) (q + γ)
    rw [abs_of_nonneg (by positivity : 0 ≤ q + γ)] at this
    linarith
  calc |RN p (z * v + c) - (q + γ)| ≤ |RN p (z * v + c) - (z * v + c)| + |z * v + c - (q + γ)| := abs_sub_le _ _ _
    _ ≤ us p * ((1 + ρ) * (q + γ)) + ρ * (q + γ) := add_le_add h3 (h1.trans h2)
    _ = ((ρ + 1) * (1 + us p) - 1) * (q + γ) := by ring

/-- a step of the chain, with the bound of the next value checked in rational arithmetic -/
theorem lnb_step {z Z : ℝ} (hz0 : 0 ≤ z) (hzZ : z ≤ Z) (k : ℕ) {r r' ce : ℝ} (hce : 0 ≤ ce) (hcr : ce ≤ r)
    (hc : |lnbC p (8 - k) - 1 / (2 * ((8 - k : ℕ) : ℝ) + 1)| ≤ ce * (1 / (2 * ((8 - k : ℕ) : ℝ) + 1)))
    (hv : |lnbW p z k - lnbV z k| ≤ r * lnbV z k)
    (hnum : ((Z * lnbV Z k * r + 1 / (2 * ((8 - k : ℕ) : ℝ) + 1) * ce) /
      (Z * lnbV Z k + 1 / (2 * ((8 - k : ℕ) : ℝ) + 1)) + 1) * (1 + us p) - 1 ≤ r') :
    |lnbW p z (k + 1) - lnbV z (k + 1)| ≤ r' * lnbV z (k + 1) := by
  obtain ⟨hV0, hVZ⟩ := lnbV_mono hz0 hzZ k
  have hQ : z * lnbV z k ≤ Z * lnbV Z k := mul_le_mul hzZ hVZ hV0 (hz0.trans hzZ)
  simp only [lnbW, lnbV]
  refine (horner_rel p hz0 hV0 hQ (by positivity) hce hcr hv hc).trans ?_
  exact mul_le_mul_of_nonneg_right hnum (by positivity)

/-- Horner's rule of `ln_b` for `0 ≤ z ≤ 0.02943726`: `v` within `1.0199604u` of `V_0(z)` -/
theorem lnb_horner (hp : p = 53) {z : ℝ} (hz0 : 0 ≤ z) (hzZ : z ≤ 2943726 / 10 ^ 8) :
    |lnbW p z 9 - lnbV z 9| ≤ 10199604 / 10000000 * u p * lnbV z 9 := by
  have hu : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num
  have hus : us p = u p / (1 + u p) := rfl
  have hus_le : ∀ c : ℝ, 1 ≤ c → us p ≤ c * u p := fun c hc =>
    (us_le_u p).trans (le_mul_of_one_le_left (u_pos p).le hc)
  have hcj : ∀ j : ℕ, |lnbC p j - 1 / (2 * (j : ℝ) + 1)| ≤ us p * (1 / (2 * (j : ℝ) + 1)) := fun j => by
    have := abs_RN_sub_le_us p (1 / (2 * (j : ℝ) + 1))
    rwa [abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * (j : ℝ) + 1))] at this
  have hc0 : |lnbC p (8 - 8) - 1 / (2 * ((8 - 8 : ℕ) : ℝ) + 1)| ≤ 0 * (1 / (2 * ((8 - 8 : ℕ) : ℝ) + 1)) := by
    simp only [lnbC, Nat.sub_self, Nat.cast_zero, mul_zero, zero_add, div_one, zero_mul]
    rw [RN_of_F p (F_one p), sub_self, abs_zero]
  have h0 : |lnbW p z 0 - lnbV z 0| ≤ us p * lnbV z 0 := by
    have := hcj 9
    simp only [lnbW, lnbV]
    norm_num at this ⊢
    exact this
  have h1 : |lnbW p z 1 - lnbV z 1| ≤ 2 * u p * lnbV z 1 :=
    lnb_step p hz0 hzZ 0 (ce := us p) (us_nonneg p) le_rfl (hcj 8) h0
      (by rw [hus, hu]; norm_num [lnbV])
  have h2 : |lnbW p z 2 - lnbV z 2| ≤ 2025966 / 1000000 * u p * lnbV z 2 :=
    lnb_step p hz0 hzZ 1 (ce := us p) (us_nonneg p) (hus_le _ (by norm_num)) (hcj 7) h1
      (by rw [hus, hu]; norm_num [lnbV])
  have h3 : |lnbW p z 3 - lnbV z 3| ≤ 20261867 / 10000000 * u p * lnbV z 3 :=
    lnb_step p hz0 hzZ 2 (ce := us p) (us_nonneg p) (hus_le _ (by norm_num)) (hcj 6) h2
      (by rw [hus, hu]; norm_num [lnbV])
  have h4 : |lnbW p z 4 - lnbV z 4| ≤ 20255765 / 10000000 * u p * lnbV z 4 :=
    lnb_step p hz0 hzZ 3 (ce := us p) (us_nonneg p) (hus_le _ (by norm_num)) (hcj 5) h3
      (by rw [hus, hu]; norm_num [lnbV])
  have h5 : |lnbW p z 5 - lnbV z 5| ≤ 20247218 / 10000000 * u p * lnbV z 5 :=
    lnb_step p hz0 hzZ 4 (ce := us p) (us_nonneg p) (hus_le _ (by norm_num)) (hcj 4) h4
      (by rw [hus, hu]; norm_num [lnbV])
  have h6 : |lnbW p z 6 - lnbV z 6| ≤ 20234901 / 10000000 * u p * lnbV z 6 :=
    lnb_step p hz0 hzZ 5 (ce := us p) (us_nonneg p) (hus_le _ (by norm_num)) (hcj 3) h5
      (by rw [hus, hu]; norm_num [lnbV])
  have h7 : |lnbW p z 7 - lnbV z 7| ≤ 20215615 / 10000000 * u p * lnbV z 7 :=
    lnb_step p hz0 hzZ 6 (ce := us p) (us_nonneg p) (hus_le _ (by norm_num)) (hcj 2) h6
      (by rw [hus, hu]; norm_num [lnbV])
  have h8 : |lnbW p z 8 - lnbV z 8| ≤ 20181049 / 10000000 * u p * lnbV z 8 :=
    lnb_step p hz0 hzZ 7 (ce := us p) (us_nonneg p) (hus_le _ (by norm_num)) (hcj 1) h7
      (by rw [hus, hu]; norm_num [lnbV])
  have h9 : |lnbW p z 9 - lnbV z 9| ≤ 10199604 / 10000000 * u p * lnbV z 9 :=
    lnb_step p hz0 hzZ 8 (ce := 0) le_rfl (mul_nonneg (by norm_num) (u_pos p).le) hc0 h8
      (by rw [hus, hu]; norm_num [lnbV])
  exact h9

/-! ## Composing the relative errors -/

omit [Prec_gt_0 p] in
theorem lnb_rel_trans {a b c x y : ℝ} (hx : 0 ≤ x) (h1 : |a - b| ≤ x * |b|) (h2 : |b - c| ≤ y * |c|) :
    |a - c| ≤ ((1 + x) * (1 + y) - 1) * |c| := by
  have hb : |b| ≤ (1 + y) * |c| := by
    have := abs_sub_abs_le_abs_sub b c
    linarith
  calc |a - c| ≤ |a - b| + |b - c| := abs_sub_le _ _ _
    _ ≤ x * ((1 + y) * |c|) + y * |c| := add_le_add (h1.trans (mul_le_mul_of_nonneg_left hb hx)) h2
    _ = ((1 + x) * (1 + y) - 1) * |c| := by ring

omit [Prec_gt_0 p] in
theorem lnb_rel_mul {a A b B x y : ℝ} (hx : 0 ≤ x) (h1 : |a - A| ≤ x * |A|) (h2 : |b - B| ≤ y * |B|) :
    |a * b - A * B| ≤ ((1 + x) * (1 + y) - 1) * |A * B| := by
  have hb : |b| ≤ (1 + y) * |B| := by
    have := abs_sub_abs_le_abs_sub b B
    linarith
  rw [show a * b - A * B = (a - A) * b + A * (b - B) by ring, abs_mul A B]
  calc |(a - A) * b + A * (b - B)| ≤ |a - A| * |b| + |A| * |b - B| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
    _ ≤ x * |A| * ((1 + y) * |B|) + |A| * (y * |B|) :=
        add_le_add (mul_le_mul h1 hb (abs_nonneg _) (by positivity)) (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
    _ = ((1 + x) * (1 + y) - 1) * (|A| * |B|) := by ring

omit [Prec_gt_0 p] in
/-- `|V(z) - V(y)| ≤ |z - y|Σ_k kZ^{k-1}/(2k + 1)` on `[0, Z]` -/
theorem atS_lip {z y Z : ℝ} (hz : 0 ≤ z) (hy : 0 ≤ y) (hzZ : z ≤ Z) (hyZ : y ≤ Z) (K : ℕ) :
    |atS z K - atS y K| ≤ |z - y| * ∑ k ∈ range K, k * Z ^ (k - 1) / (2 * k + 1) := by
  unfold atS
  rw [← sum_sub_distrib, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
  rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * k + 1), mul_div_assoc', ← mul_assoc]
  refine div_le_div_of_nonneg_right ((abs_pow_sub_pow_le z y k).trans ?_) (by positivity)
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) (by positivity)
  rw [abs_of_nonneg hz, abs_of_nonneg hy]
  exact max_le hzZ hyZ

omit [Prec_gt_0 p] in
theorem atS_ge_one {y : ℝ} (hy : 0 ≤ y) {K : ℕ} (hK : 1 ≤ K) : 1 ≤ atS y K := by
  unfold atS
  have := single_le_sum (f := fun k : ℕ => y ^ k / (2 * k + 1)) (fun k _ => by positivity) (mem_range.mpr hK)
  simpa using this

/-! ## The bound -/

/-- `h = 2^e m` with `m ∈ F` and `m ∈ (μ/2, μ]` -/
theorem lnb_split (hp : p = 53) {h : ℝ} (hh : 0 < h) (hF : F p h) :
    F p (h / 2 ^ lnbE p h) ∧ 6369051672525773 / 2 ^ 52 / 2 < h / 2 ^ lnbE p h ∧
      h / 2 ^ lnbE p h ≤ 6369051672525773 / 2 ^ 52 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set e0 := lnbE0 h with he0
  have hf1 : (e0 : ℝ) ≤ Real.log h / Real.log 2 := Int.floor_le _
  have hf2 : Real.log h / Real.log 2 < e0 + 1 := Int.lt_floor_add_one _
  have h1 : (2 : ℝ) ^ e0 ≤ h := by
    rw [← exp_int_mul_log_two, ← Real.exp_log hh]
    exact Real.exp_le_exp.mpr ((le_div_iff₀ hl2).mp hf1)
  have h2 : h < (2 : ℝ) ^ e0 * 2 := by
    rw [← zpow_add_one₀ two_ne_zero, ← exp_int_mul_log_two, ← Real.exp_log hh]
    refine Real.exp_lt_exp.mpr ?_
    push_cast
    exact (div_lt_iff₀ hl2).mp hf2
  have hpos : (0 : ℝ) < 2 ^ e0 := by positivity
  have hm1 : 1 ≤ h / 2 ^ e0 := by rw [le_div_iff₀ hpos]; linarith
  have hm2 : h / 2 ^ e0 < 2 := by rw [div_lt_iff₀ hpos]; linarith
  have hμ := mu_eq p hp
  have hF' : ∀ e : ℤ, F p (h / 2 ^ e) := fun e => by
    rw [div_eq_mul_inv, ← zpow_neg, mul_comm]; exact F_zpow_mul p _ hF
  refine ⟨hF' _, ?_⟩
  unfold lnbE
  rw [← he0, hμ]
  split_ifs with hc
  · rw [zpow_add_one₀ two_ne_zero, ← div_div]
    constructor
    · linarith
    · linarith [show (1 : ℝ) ≤ 6369051672525773 / 2 ^ 52 by norm_num]
  · push Not at hc
    exact ⟨by linarith [show (6369051672525773 / 2 ^ 52 / 2 : ℝ) < 1 by norm_num], hc⟩

/-- `s = RN((m - 1)/RN(m + 1))` is within `2u` of `s_t = (m - 1)/(m + 1)`, `m - 1` being exact -/
theorem lnb_s (hp : p = 53) {m : ℝ} (hmF : F p m) (hml : 7 / 10 < m) (hmu : m < 142 / 100) :
    |lnbS p m - (m - 1) / (m + 1)| ≤ 2 * u p * |(m - 1) / (m + 1)| := by
  have hu : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num
  have hus : us p = u p / (1 + u p) := rfl
  have hu0 := u_pos p
  have hus0 := us_nonneg p
  have hus1 : us p * (1 + u p) = u p := by rw [hus]; field_simp
  have hsub : RN p (m - 1) = m - 1 :=
    RN_of_F p (sterbenz 2 (FloatSpec.Core.FLX.FLX_exp p) m 1 hmF (F_one p) (by norm_num)
      ⟨by linarith, by linarith⟩)
  set st := (m - 1) / (m + 1) with hst
  rw [lnbS, hsub]
  set d := RN p (m + 1) with hdd
  have hd : |d - (m + 1)| ≤ us p * (m + 1) := by
    have := abs_RN_sub_le_us p (m + 1)
    rwa [abs_of_pos (by linarith : 0 < m + 1)] at this
  have hd0 : (1 - us p) * (m + 1) ≤ d := by have := (abs_le.mp hd).1; nlinarith
  have hus2 : us p ≤ 1 / 2 := by rw [hus, hu]; norm_num
  have hdp : 0 < d := lt_of_lt_of_le (by nlinarith) hd0
  have hone : (1 - us p) * (1 + u p) = 1 := by rw [hus]; field_simp; ring
  have hmd : m + 1 ≤ d * (1 + u p) :=
    calc m + 1 = (1 - us p) * (m + 1) * (1 + u p) := by rw [mul_right_comm, hone, one_mul]
      _ ≤ d * (1 + u p) := mul_le_mul_of_nonneg_right hd0 (by linarith)
  have ht : (m + 1) / d ≤ 1 + u p := by rw [div_le_iff₀ hdp]; linarith
  have hq : (m - 1) / d = st * ((m + 1) / d) := by rw [hst]; field_simp
  have hq1 : |(m - 1) / d| ≤ (1 + u p) * |st| := by
    rw [hq, abs_mul, abs_of_pos (by positivity : 0 < (m + 1) / d), mul_comm]
    exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)
  have hq2 : |(m - 1) / d - st| ≤ u p * |st| := by
    rw [hq, show st * ((m + 1) / d) - st = st * ((m + 1 - d) / d) by field_simp, abs_mul, mul_comm (u p)]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_div, abs_of_pos hdp, abs_sub_comm, div_le_iff₀ hdp]
    calc |d - (m + 1)| ≤ us p * (m + 1) := hd
      _ ≤ us p * (d * (1 + u p)) := mul_le_mul_of_nonneg_left hmd hus0
      _ = u p * d := by rw [mul_comm d, ← mul_assoc, hus1]
  have h3 := abs_RN_sub_le_us p ((m - 1) / d)
  calc |RN p ((m - 1) / d) - st| ≤ |RN p ((m - 1) / d) - (m - 1) / d| + |(m - 1) / d - st| := abs_sub_le _ _ _
    _ ≤ us p * ((1 + u p) * |st|) + u p * |st| := add_le_add (h3.trans
        (mul_le_mul_of_nonneg_left hq1 hus0)) hq2
    _ = 2 * u p * |st| := by rw [← mul_assoc, hus1]; ring

/-- `z = RN(s²)` is within `θ_z = (1 + 2u)²(1 + ū) - 1` of `s_t²`, and in `[0, 0.02943726]` -/
theorem lnb_z (hp : p = 53) {s st : ℝ} (hs : |s - st| ≤ 2 * u p * |st|)
    (hsb : |st| ≤ (6369051672525773 / 2 ^ 52 - 1) / (6369051672525773 / 2 ^ 52 + 1)) :
    |RN p (s * s) - st ^ 2| ≤ ((1 + 2 * u p) ^ 2 * (1 + us p) - 1) * st ^ 2 ∧ 0 ≤ RN p (s * s) ∧
      RN p (s * s) ≤ 2943726 / 10 ^ 8 := by
  have hu : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num
  have hus : us p = u p / (1 + u p) := rfl
  have hu0 := u_pos p
  have hy0 : 0 ≤ st ^ 2 := sq_nonneg _
  have hz : |RN p (s * s) - st ^ 2| ≤ ((1 + 2 * u p) ^ 2 * (1 + us p) - 1) * st ^ 2 := by
    have h2 := lnb_rel_mul (by linarith) hs hs
    have h3 := lnb_rel_trans (us_nonneg p) (abs_RN_sub_le_us p (s * s)) h2
    rw [show st * st = st ^ 2 by ring, abs_of_nonneg hy0] at h3
    exact h3.trans_eq (by ring)
  have hθ : (1 + 2 * u p) ^ 2 * (1 + us p) - 1 ≤ 1 / 10 ^ 14 := by rw [hus, hu]; norm_num
  have hy : st ^ 2 ≤ ((6369051672525773 / 2 ^ 52 - 1) / (6369051672525773 / 2 ^ 52 + 1)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hsb 2
  have hθ0 : 0 ≤ (1 + 2 * u p) ^ 2 * (1 + us p) - 1 := by
    have := us_nonneg p
    nlinarith
  refine ⟨hz, ?_, ?_⟩
  · have := (abs_le.mp hz).1
    nlinarith
  · have := (abs_le.mp hz).2
    have : RN p (s * s) ≤ (1 + 1 / 10 ^ 14) * ((6369051672525773 / 2 ^ 52 - 1) / (6369051672525773 / 2 ^ 52 + 1)) ^ 2 :=
      by nlinarith
    exact this.trans (by norm_num)

/-- Horner's `v` against `V_∞(y)`: within `(1 + 1.0199604u)(1 + 0.35θ_z Z)(1 + Z^{10}/(21(1 - Z))) - 1`,
`Z = 0.02943726`, for `z` within `θ_z` of `y` -/
theorem lnb_v (hp : p = 53) {z y θz : ℝ} (hz0 : 0 ≤ z) (hzZ : z ≤ 2943726 / 10 ^ 8) (hy0 : 0 ≤ y)
    (hyZ : y ≤ 2943726 / 10 ^ 8) (hθz0 : 0 ≤ θz) (hz : |z - y| ≤ θz * y) :
    |lnbW p z 9 - ∑' k : ℕ, y ^ k / (2 * k + 1)| ≤
      ((1 + 10199604 / 10000000 * u p) * (1 + θz * (2943726 / 10 ^ 8) * (35 / 100)) *
        (1 + (2943726 / 10 ^ 8 : ℝ) ^ 10 / (21 * (1 - 2943726 / 10 ^ 8))) - 1) *
        |∑' k : ℕ, y ^ k / (2 * k + 1)| := by
  have hv := lnb_horner p hp hz0 hzZ
  rw [lnbV_nine] at hv
  obtain ⟨ht1, ht2⟩ := atS_tail hy0 (by linarith) 10
  set Vinf := ∑' k : ℕ, y ^ k / (2 * k + 1) with hVinf
  have hV1 : 1 ≤ atS y 10 := atS_ge_one hy0 (by norm_num)
  have hVz1 : 1 ≤ atS z 10 := atS_ge_one hz0 (by norm_num)
  set θV := θz * (2943726 / 10 ^ 8) * (35 / 100) with hθV
  have hzy : |atS z 10 - atS y 10| ≤ θV * |atS y 10| := by
    have h1 := atS_lip hz0 hy0 hzZ hyZ 10
    have hP : ∑ k ∈ range 10, (k : ℝ) * (2943726 / 10 ^ 8) ^ (k - 1) / (2 * k + 1) ≤ 35 / 100 := by
      simp only [sum_range_succ, sum_range_zero]; norm_num
    rw [abs_of_pos (by linarith : (0 : ℝ) < atS y 10)]
    calc |atS z 10 - atS y 10| ≤ θz * y * (35 / 100) :=
          h1.trans (mul_le_mul hz hP (sum_nonneg fun k _ => by positivity) (by positivity))
      _ ≤ θz * (2943726 / 10 ^ 8) * (35 / 100) * 1 := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hyZ hθz0) (by norm_num)
      _ ≤ θV * atS y 10 := mul_le_mul_of_nonneg_left hV1 (by positivity)
  set tr := (2943726 / 10 ^ 8 : ℝ) ^ 10 / (21 * (1 - 2943726 / 10 ^ 8)) with htr
  have hyi : |atS y 10 - Vinf| ≤ tr * |Vinf| := by
    have h1 : y ^ 10 / ((2 * ((10 : ℕ) : ℝ) + 1) * (1 - y)) ≤ tr := by
      rw [htr, show (2 * ((10 : ℕ) : ℝ) + 1) = 21 by norm_num]
      exact div_le_div₀ (by positivity) (pow_le_pow_left₀ hy0 hyZ 10) (by norm_num)
        (mul_le_mul_of_nonneg_left (by linarith) (by norm_num))
    rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ Vinf - atS y 10),
      abs_of_pos (by linarith : (0 : ℝ) < Vinf)]
    have htr0 : 0 ≤ tr := by positivity
    have : tr ≤ tr * Vinf := le_mul_of_one_le_right htr0 (hV1.trans ht1)
    clear_value Vinf tr
    linarith
  have hR0 : 0 ≤ 10199604 / 10000000 * u p := mul_nonneg (by norm_num) (u_pos p).le
  have hθV0 : 0 ≤ θV := mul_nonneg (mul_nonneg hθz0 (by norm_num)) (by norm_num)
  have h := lnb_rel_trans (by nlinarith) (lnb_rel_trans hR0
    (show |lnbW p z 9 - atS z 10| ≤ _ * |atS z 10| by
      rw [abs_of_pos (by linarith : (0 : ℝ) < atS z 10)]; exact hv) hzy) hyi
  exact h.trans_eq (by ring)

/-- `w = RN(2sv)` is within `4.312u` of `ln m` for `m ∈ F ∩ (μ/2, μ]` -/
theorem lnb_w (hp : p = 53) {m : ℝ} (hmF : F p m) (hm1 : 6369051672525773 / 2 ^ 52 / 2 < m)
    (hm2 : m ≤ 6369051672525773 / 2 ^ 52) :
    |RN p (2 * lnbS p m * lnbW p (RN p (lnbS p m * lnbS p m)) 9) - Real.log m| ≤
      4312 / 1000 * u p * |Real.log m| := by
  have hu : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num
  have hus : us p = u p / (1 + u p) := rfl
  have hml : 7 / 10 < m := lt_trans (by norm_num) hm1
  have hmu : m < 142 / 100 := lt_of_le_of_lt hm2 (by norm_num)
  set st := (m - 1) / (m + 1) with hst
  set s := lnbS p m with hsd
  have hs1 : |s - st| ≤ 2 * u p * |st| := lnb_s p hp hmF hml hmu
  have hs : |2 * s - 2 * st| ≤ 2 * u p * |2 * st| := by
    rw [← mul_sub, abs_mul, abs_mul (2 : ℝ) st, abs_two]
    linarith
  have hsb : |st| ≤ (6369051672525773 / 2 ^ 52 - 1) / (6369051672525773 / 2 ^ 52 + 1) := by
    rw [hst, abs_div, abs_of_pos (by linarith : 0 < m + 1), div_le_div_iff₀ (by linarith) (by norm_num)]
    rcases abs_cases (m - 1) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nlinarith
  obtain ⟨hz, hz0, hzZ⟩ := lnb_z p hp hs1 hsb
  have hyZ : st ^ 2 ≤ 2943726 / 10 ^ 8 := by
    have : st ^ 2 ≤ ((6369051672525773 / 2 ^ 52 - 1) / (6369051672525773 / 2 ^ 52 + 1)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hsb 2
    exact this.trans (by norm_num)
  have hθz0 : 0 ≤ (1 + 2 * u p) ^ 2 * (1 + us p) - 1 := by
    have := us_nonneg p
    have := u_pos p
    nlinarith
  have hv := lnb_v p hp hz0 hzZ (sq_nonneg st) hyZ hθz0 hz
  -- `ln m = 2s_tV_∞(s_t²)`
  have hst1 : |st| < 1 := lt_of_le_of_lt hsb (by norm_num)
  have hlog : Real.log m = 2 * st * ∑' k : ℕ, (st ^ 2) ^ k / (2 * k + 1) := by
    rw [← log_artanh hst1, ← Real.log_div (ne_of_gt (by linarith [(abs_lt.mp hst1).1]))
      (ne_of_gt (by linarith [(abs_lt.mp hst1).2]))]
    congr 1
    rw [hst]
    field_simp
    ring
  have hsv := lnb_rel_mul (by linarith [u_pos p]) hs hv
  have hw := lnb_rel_trans (us_nonneg p) (abs_RN_sub_le_us p (2 * s * lnbW p (RN p (s * s)) 9)) hsv
  rw [← hlog] at hw
  refine hw.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
  rw [hus, hu]
  norm_num

omit [Prec_gt_0 p] in
/-- `ln 2` to 23 digits -/
theorem log_two_dec : (69314718055994530941721 / 10 ^ 23 : ℝ) ≤ Real.log 2 ∧
    Real.log 2 ≤ 69314718055994530941724 / 10 ^ 23 := by
  obtain ⟨h1, h2⟩ := log_two_bounds
  simp only [atS, sum_range_succ, sum_range_zero] at h1 h2
  norm_num at h1 h2
  constructor <;> linarith

omit [Prec_gt_0 p] in
/-- `ln μ ≤ ln 2/2 + (μ - 1.4142135623730950488)/1.4142135623730950488` and `2 ≤ μ²` -/
theorem log_mu_le : Real.log (6369051672525773 / 2 ^ 52) ≤ 69314718055994530941724 / 10 ^ 23 / 2 +
    (6369051672525773 / 2 ^ 52 - 14142135623730950488 / 10 ^ 19) / (14142135623730950488 / 10 ^ 19) := by
  obtain ⟨s1, s2⟩ := sqrt_two_bounds
  have l2 := log_two_dec.2
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have e : Real.log (6369051672525773 / 2 ^ 52) =
      Real.log (Real.sqrt 2) + Real.log (6369051672525773 / 2 ^ 52 / Real.sqrt 2) := by
    rw [← Real.log_mul hs0.ne' (by positivity)]
    congr 1
    field_simp
  rw [e, Real.log_sqrt (by norm_num)]
  have h1 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 6369051672525773 / 2 ^ 52 / Real.sqrt 2)
  have h2 : 6369051672525773 / 2 ^ 52 / Real.sqrt 2 - 1 ≤
      (6369051672525773 / 2 ^ 52 - 14142135623730950488 / 10 ^ 19) / (14142135623730950488 / 10 ^ 19) := by
    rw [div_sub_one hs0.ne']
    calc (6369051672525773 / 2 ^ 52 - Real.sqrt 2) / Real.sqrt 2 ≤
          (6369051672525773 / 2 ^ 52 - 14142135623730950488 / 10 ^ 19) / Real.sqrt 2 :=
          div_le_div_of_nonneg_right (by linarith) hs0.le
      _ ≤ (6369051672525773 / 2 ^ 52 - 14142135623730950488 / 10 ^ 19) / (14142135623730950488 / 10 ^ 19) :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) s1
  linarith

/-- Lemma 43 (`lem:lnb`) with an unbounded exponent range, where the paper's scaling of subnormal `h` by `2^54` is the
identity: at `p = 53`, `ln_b(1) = 0` and `|ln_b(h) - ln h| ≤ 5.915u|ln h|` for positive `h ∈ F` -/
theorem lemma43 (hp : p = 53) :
    lnB p 1 = 0 ∧ ∀ h : ℝ, 0 < h → F p h → |lnB p h - Real.log h| ≤ 5915 / 1000 * u p * |Real.log h| := by
  have hu : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num
  have hus : us p = u p / (1 + u p) := rfl
  have hμ := mu_eq p hp
  have hcL := cL_eq p hp
  have hR0 : RN p 0 = 0 := RN_of_F p (F_zero p)
  constructor
  · have he : lnbE p 1 = 0 := by
      unfold lnbE lnbE0
      rw [Real.log_one, zero_div, Int.floor_zero, hμ]
      norm_num
    have hs : lnbS p (1 / 2 ^ lnbE p 1) = 0 := by
      rw [he, lnbS]
      norm_num [hR0]
    rw [lnB, hs, he]
    simp [hR0]
  intro h hh hF
  obtain ⟨hmF, hm1, hm2⟩ := lnb_split p hp hh hF
  have hw := lnb_w p hp hmF hm1 hm2
  set e := lnbE p h with hed
  set m := h / 2 ^ e with hmd
  set w := RN p (2 * lnbS p m * lnbW p (RN p (lnbS p m * lnbS p m)) 9) with hwd
  have hm0 : 0 < m := lt_trans (by norm_num) hm1
  have hlogh : Real.log h = e * Real.log 2 + Real.log m := by
    have : h = 2 ^ e * m := by rw [hmd]; field_simp
    rw [this, Real.log_mul (by positivity) hm0.ne', Real.log_zpow]
  have hres : lnB p h = RN p (e * RN p (Real.log 2) + w) := rfl
  rw [hres, hlogh, hcL]
  set L := Real.log m with hLd
  have hEW : 4312 / 1000 * u p ≤ 5915 / 1000 * u p := by rw [hu]; norm_num
  by_cases he0 : e = 0
  · rw [he0, Int.cast_zero, zero_mul, zero_mul, zero_add, zero_add, RN_of_F p (F_RN p _)]
    exact hw.trans (mul_le_mul_of_nonneg_right hEW (abs_nonneg _))
  -- `e ≠ 0`
  obtain ⟨l2lo, l2hi⟩ := log_two_dec
  have hlμ := log_mu_le
  set LM := (69314718055994530941724 / 10 ^ 23 / 2 +
    (6369051672525773 / 2 ^ 52 - 14142135623730950488 / 10 ^ 19) / (14142135623730950488 / 10 ^ 19) : ℝ) with hLM
  -- `|ln m| ≤ ln μ`
  clear_value L LM
  have hL : |L| ≤ LM := by
    rw [abs_le, hLd]
    constructor
    · have h1 : Real.log (6369051672525773 / 2 ^ 52 / 2) < Real.log m := Real.log_lt_log (by norm_num) hm1
      rw [Real.log_div (by norm_num) (by norm_num)] at h1
      have h2 : Real.log 2 ≤ 2 * Real.log (6369051672525773 / 2 ^ 52) := by
        rw [← Real.log_rpow (by norm_num)]
        exact Real.log_le_log (by norm_num) (by norm_num)
      linarith
    · exact (Real.log_le_log hm0 hm2).trans hlμ
  have hE : (1 : ℝ) ≤ |(e : ℝ)| := by exact_mod_cast Int.one_le_abs he0
  set E := |(e : ℝ)| with hEd
  set Dn := 2088813 / 10 ^ 7 * u p with hDn
  have hD : |6243314768165359 / 2 ^ 53 - Real.log 2| ≤ Dn := by
    rw [hDn, hu, abs_le]; constructor <;> norm_num <;> linarith
  have hB : |e * (6243314768165359 / 2 ^ 53) + w - (e * Real.log 2 + L)| ≤ E * Dn + 4312 / 1000 * u p * LM := by
    rw [show e * (6243314768165359 / 2 ^ 53) + w - (e * Real.log 2 + L) =
      e * (6243314768165359 / 2 ^ 53 - Real.log 2) + (w - L) by ring]
    refine (abs_add_le _ _).trans (add_le_add ?_ (hw.trans (mul_le_mul_of_nonneg_left hL (by positivity))))
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hD (abs_nonneg _)
  have hlh : E * (69314718055994530941721 / 10 ^ 23) - LM ≤ |e * Real.log 2 + L| := by
    have h1 := abs_sub_abs_le_abs_sub (e * Real.log 2) (-L)
    rw [sub_neg_eq_add, abs_neg, abs_mul, abs_of_pos (Real.log_pos (by norm_num) : 0 < Real.log 2), ← hEd] at h1
    have h2 : E * (69314718055994530941721 / 10 ^ 23) ≤ E * Real.log 2 := mul_le_mul_of_nonneg_left l2lo (abs_nonneg _)
    linarith
  -- the bound is linear in `|e|`, largest relative to `|ln h|` at `|e| = 1`
  have hus0 := us_nonneg p
  have hK : (1 + us p) * (E * Dn + 4312 / 1000 * u p * LM) ≤
      (5915 / 1000 * u p - us p) * (E * (69314718055994530941721 / 10 ^ 23) - LM) := by
    have k1 : (1 + us p) * (Dn + 4312 / 1000 * u p * LM) ≤
        (5915 / 1000 * u p - us p) * (69314718055994530941721 / 10 ^ 23 - LM) := by
      rw [hDn, hLM, hus, hu]; norm_num
    have k2 : (1 + us p) * Dn ≤ (5915 / 1000 * u p - us p) * (69314718055994530941721 / 10 ^ 23) := by
      rw [hDn, hus, hu]; norm_num
    nlinarith [mul_le_mul_of_nonneg_left k2 (by linarith : (0 : ℝ) ≤ E - 1)]
  have hKu : 0 ≤ 5915 / 1000 * u p - us p := by rw [hus, hu]; norm_num
  set Y := e * (6243314768165359 / 2 ^ 53) + w with hY
  have hRY := abs_RN_sub_le_us p Y
  have hYa : |Y| ≤ |e * Real.log 2 + L| + (E * Dn + 4312 / 1000 * u p * LM) := by
    have := abs_sub_abs_le_abs_sub Y (e * Real.log 2 + L)
    linarith
  calc |RN p Y - (e * Real.log 2 + L)| ≤ |RN p Y - Y| + |Y - (e * Real.log 2 + L)| := abs_sub_le _ _ _
    _ ≤ us p * (|e * Real.log 2 + L| + (E * Dn + 4312 / 1000 * u p * LM)) + (E * Dn + 4312 / 1000 * u p * LM) :=
        add_le_add (hRY.trans (mul_le_mul_of_nonneg_left hYa hus0)) hB
    _ = us p * |e * Real.log 2 + L| + (1 + us p) * (E * Dn + 4312 / 1000 * u p * LM) := by ring
    _ ≤ us p * |e * Real.log 2 + L| + (5915 / 1000 * u p - us p) * |e * Real.log 2 + L| :=
        add_le_add le_rfl (hK.trans (mul_le_mul_of_nonneg_left hlh hKu))
    _ = 5915 / 1000 * u p * |e * Real.log 2 + L| := by ring

end ExpansionBounds
