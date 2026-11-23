import ExpansionBounds.Trig
import Mathlib.Analysis.Real.Pi.Irrational

/-!
# Theorem 35: TAN

TAN_n returns `x` below `|x_0| < u^{n/2}`, and otherwise `2^{-e}DIV(2^eY_s, Y_c)` for even `q` and `-DIV(Y_c, Y_s)` for
odd `q`, with `Y_s` and `Y_c` SINR and COSR of RED's `r`. Theorem 19 bounds the quotient relative to `Y_s/Y_c`, and
with Lemma 34 the quotient is within `(1 + δ_S)(1 + δ_D)/(1 - δ_C) - 1` of `tan r`, relatively; the move from `r` to
`r_e` costs `|tan r - tan r_e| = |sin(r - r_e)|/|cos r cos r_e|`, at most `εu^n 2|r_e|/sin 2|r_e|` relative to
`|tan r_e|` plus a term in `E_π`.
-/

namespace ExpansionBounds

open Finset

/-- a quotient of approximations: with `A` within `x|S|` of `S`, `B` within `y|C|` of `C` and `D` within `z|A/B|` of
`A/B`, `D` is within `((1 + x)(1 + z)/(1 - y) - 1)|S/C|` of `S/C` -/
theorem ratio_bound {A B D S C x y z : ℝ} (hC : C ≠ 0) (hy : y < 1) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z)
    (hA : |A - S| ≤ x * |S|) (hB : |B - C| ≤ y * |C|) (hD : |A / B - D| ≤ z * |A / B|) :
    |D - S / C| ≤ ((1 + x) * (1 + z) / (1 - y) - 1) * |S / C| := by
  have hCp : 0 < |C| := abs_pos.mpr hC
  have h1y : 0 < 1 - y := by linarith
  have hBlo : (1 - y) * |C| ≤ |B| := by
    have := abs_sub_abs_le_abs_sub C B
    rw [abs_sub_comm] at this
    linarith
  have hBp : 0 < |B| := lt_of_lt_of_le (mul_pos h1y hCp) hBlo
  have hB0 : B ≠ 0 := abs_pos.mp hBp
  have hAhi : |A| ≤ (1 + x) * |S| := by
    have := abs_sub_abs_le_abs_sub A S
    linarith
  -- `|A/B| ≤ (1 + x)/(1 - y)|S/C|`
  have hAB : |A / B| ≤ (1 + x) / (1 - y) * |S / C| := by
    rw [abs_div, abs_div, div_le_iff₀ hBp]
    calc |A| ≤ (1 + x) * |S| := hAhi
      _ = (1 + x) / (1 - y) * (|S| / |C|) * ((1 - y) * |C|) := by field_simp
      _ ≤ (1 + x) / (1 - y) * (|S| / |C|) * |B| :=
          mul_le_mul_of_nonneg_left hBlo (mul_nonneg (div_nonneg (by linarith) h1y.le)
            (div_nonneg (abs_nonneg _) hCp.le))
  -- `|A/B - S/C| ≤ (x + y)/(1 - y)|S/C|`
  have hdiff : |A / B - S / C| ≤ (x + y) / (1 - y) * |S / C| := by
    rw [show A / B - S / C = ((A - S) * C - S * (B - C)) / (B * C) by field_simp; ring, abs_div, abs_mul,
      div_le_iff₀ (mul_pos hBp hCp)]
    have h1 : |(A - S) * C - S * (B - C)| ≤ (x + y) * |S| * |C| := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul]
      have e1 := mul_le_mul_of_nonneg_right hA (abs_nonneg C)
      have e2 := mul_le_mul_of_nonneg_left hB (abs_nonneg S)
      linarith
    calc |(A - S) * C - S * (B - C)| ≤ (x + y) * |S| * |C| := h1
      _ = (x + y) / (1 - y) * (|S| / |C|) * ((1 - y) * |C| * |C|) := by field_simp
      _ ≤ (x + y) / (1 - y) * (|S| / |C|) * (|B| * |C|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hBlo hCp.le)
            (mul_nonneg (div_nonneg (by linarith) h1y.le) (div_nonneg (abs_nonneg _) hCp.le))
      _ = _ := by rw [abs_div]
  calc |D - S / C| ≤ |A / B - S / C| + |A / B - D| := by
        have := abs_sub_le D (A / B) (S / C)
        rw [abs_sub_comm D (A / B)] at this
        linarith
    _ ≤ (x + y) / (1 - y) * |S / C| + z * ((1 + x) / (1 - y) * |S / C|) :=
        add_le_add hdiff (hD.trans (mul_le_mul_of_nonneg_left hAB hz0))
    _ = ((1 + x) * (1 + z) / (1 - y) - 1) * |S / C| := by field_simp; ring

/-- `sin₋(t) = t - t³/6 + t⁵/120 - t⁷/5040`, below `sin t` on `[0, 2]` -/
noncomputable def sinLo (t : ℝ) : ℝ := t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040

theorem sin_terms_antitone {t : ℝ} (h0 : 0 ≤ t) (h2 : t ≤ 2) :
    Antitone fun i : ℕ => t ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ) := by
  refine antitone_nat_of_succ_le fun i => ?_
  have hf : ((2 * (i + 1) + 1).factorial : ℝ) = (2 * i + 1).factorial * ((2 * i + 2) * (2 * i + 3)) := by
    rw [show 2 * (i + 1) + 1 = (2 * i + 1) + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have hpos : (0 : ℝ) < (2 * i + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  rw [hf, show 2 * (i + 1) + 1 = 2 * i + 1 + 2 by ring, pow_add, div_le_div_iff₀ (by positivity) hpos]
  have ht2 : t ^ 2 ≤ 4 := by nlinarith
  have hi : (4 : ℝ) ≤ (2 * i + 2) * (2 * i + 3) := by
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    nlinarith
  have := pow_nonneg h0 (2 * i + 1)
  nlinarith [mul_le_mul_of_nonneg_left (ht2.trans hi) (mul_nonneg this hpos.le)]

theorem sinLo_le_sin {t : ℝ} (h0 : 0 ≤ t) (h2 : t ≤ 2) : sinLo t ≤ Real.sin t := by
  set f : ℕ → ℝ := fun i => t ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)
  have hsin : HasSum (fun i => (-1) ^ i * f i) (Real.sin t) := by
    have := Real.hasSum_sin t
    convert this using 1
    funext i
    simp only [f]
    ring
  have hlo := (sin_terms_antitone h0 h2).alternating_series_le_tendsto hsin.tendsto_sum_nat 2
  have hval : ∑ i ∈ range (2 * 2), (-1) ^ i * f i = sinLo t := by
    simp [f, sum_range_succ, sinLo, Nat.factorial]
    ring
  rwa [hval] at hlo

/-- `t/sin t` increases on `(0, π)`, by the concavity of `sin` -/
theorem div_sin_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi) : a / Real.sin a ≤ b / Real.sin b := by
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha (by linarith)
  have hsb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi (by linarith) hb
  have hb0 : 0 < b := by linarith
  have hc := strictConcaveOn_sin_Icc.concaveOn.2 (show (0 : ℝ) ∈ Set.Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
    (show b ∈ Set.Icc 0 Real.pi from ⟨hb0.le, hb.le⟩)
    (show (0 : ℝ) ≤ 1 - a / b by rw [sub_nonneg, div_le_one hb0]; exact hab)
    (show (0 : ℝ) ≤ a / b by positivity) (show 1 - a / b + a / b = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.sin_zero] at hc
  rw [show a / b * b = a by field_simp] at hc
  rw [div_le_div_iff₀ hsa hsb]
  have := mul_le_mul_of_nonneg_left hc (by linarith : (0 : ℝ) ≤ b)
  rw [show b * (a / b * Real.sin b) = a * Real.sin b by field_simp] at this
  linarith

/-- `|t|/(|sin t| cos t) ≤ 2r̄/sin₋(2r̄)` for `0 < |t| ≤ r̄ ≤ 0.8` -/
theorem K_le {t rb : ℝ} (ht : 0 < |t|) (htr : |t| ≤ rb) (hrb : rb ≤ 8 / 10) :
    |t| / (|Real.sin t| * Real.cos t) ≤ 2 * rb / sinLo (2 * rb) := by
  have hpi := Real.pi_gt_three
  have hrb0 : 0 < rb := lt_of_lt_of_le ht htr
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have hst : |Real.sin t| * Real.cos t = Real.sin (2 * |t|) / 2 := by
    rw [Real.sin_two_mul, ← Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith), Real.cos_abs]; ring
  rw [hst, div_div_eq_mul_div, mul_comm]
  have h1 := div_sin_mono (by linarith : 0 < 2 * |t|) (by linarith : 2 * |t| ≤ 2 * rb) (by linarith)
  have h2 : sinLo (2 * rb) ≤ Real.sin (2 * rb) := sinLo_le_sin (by linarith) (by linarith)
  have h3 : 0 < sinLo (2 * rb) := by
    unfold sinLo
    have h4 : 2 * rb ≤ 16 / 10 := by linarith
    nlinarith [pow_pos (by linarith : (0 : ℝ) < 2 * rb) 3, pow_pos (by linarith : (0 : ℝ) < 2 * rb) 5,
      pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 2 * rb) h4 2, pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 2 * rb) h4 4,
      pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 2 * rb) h4 6]
  calc 2 * |t| / Real.sin (2 * |t|) ≤ 2 * rb / Real.sin (2 * rb) := h1
    _ ≤ 2 * rb / sinLo (2 * rb) := div_le_div_of_nonneg_left (by linarith) h3 h2

theorem cosLo_ge {rb : ℝ} (h0 : 0 ≤ rb) (h1 : rb ≤ 8 / 10) : 69 / 100 ≤ cosLo rb := by
  unfold cosLo
  have h2 : rb ^ 2 ≤ 64 / 100 := by nlinarith
  nlinarith [pow_nonneg h0 4, pow_nonneg h0 6, pow_le_pow_left₀ h0 h1 6]

/-- the move from `r` to `r_e` for the tangent: with `|R - r_e| ≤ w|r_e| + 2E` and `0 < |r_e| ≤ r̄ ≤ 0.8`,
`|sin R/cos R - sin r_e/cos r_e| ≤ (εwK + 3E/(|sin r_e| cos r_e))|sin r_e/cos r_e|`, `K = 2r̄/sin₋(2r̄)` -/
theorem tan_move {R re w E rb : ℝ} (hw : 0 ≤ w) (hw1 : w ≤ 1 / 100) (hE : 0 ≤ E) (hE1 : E ≤ 1 / 1000)
    (hre0 : 0 < |re|) (hre : |re| ≤ rb) (hrb : rb ≤ 8 / 10) (hη : |R - re| ≤ w * |re| + 2 * E) :
    |Real.sin R / Real.cos R - Real.sin re / Real.cos re| ≤
      ((1 + 2 * w) * w * (2 * rb / sinLo (2 * rb)) + 3 * E / (|Real.sin re| * Real.cos re)) *
        |Real.sin re / Real.cos re| := by
  set η := |R - re| with hηd
  set t := |re| with htd
  set s := |Real.sin re| with hsd
  set c := Real.cos re with hcd
  set K := 2 * rb / sinLo (2 * rb) with hKd
  have hrb0 : 0 ≤ rb := (abs_nonneg re).trans hre
  have hc : 69 / 100 ≤ c := (cosLo_ge hrb0 hrb).trans (cos_ge_cosLo re rb hre (by linarith))
  have hpi := Real.pi_gt_three
  have hs : 0 < s := by
    rw [hsd, Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith)]
    exact Real.sin_pos_of_pos_of_lt_pi hre0 (by linarith)
  have hK : t / (s * c) ≤ K := K_le hre0 hre hrb
  have ht8 : t ≤ 8 / 10 := hre.trans hrb
  have hη1 : η ≤ 1 / 100 := by nlinarith
  have hcR : c - η ≤ Real.cos R := by
    have := Real.abs_cos_sub_cos_le R re
    have := neg_abs_le (Real.cos R - Real.cos re)
    linarith
  have hcR0 : 0 < c - η := by linarith
  -- `tan R - tan r_e = sin(R - r_e)/(cos R cos r_e)`
  have hcRp : 0 < Real.cos R := lt_of_lt_of_le hcR0 hcR
  have hdiff : |Real.sin R / Real.cos R - Real.sin re / Real.cos re| ≤ η / ((c - η) * c) := by
    rw [div_sub_div _ _ hcRp.ne' (by linarith : Real.cos re ≠ 0), show Real.sin R * Real.cos re -
      Real.cos R * Real.sin re = Real.sin (R - re) by rw [Real.sin_sub], abs_div, abs_mul,
      abs_of_pos hcRp, abs_of_pos (by linarith : 0 < Real.cos re)]
    have h1 : |Real.sin (R - re)| ≤ η := Real.abs_sin_le_abs
    calc |Real.sin (R - re)| / (Real.cos R * c) ≤ η / (Real.cos R * c) :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ η / ((c - η) * c) :=
          div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (mul_le_mul_of_nonneg_right hcR (by linarith))
  -- `η/(c - η) ≤ εwt/c + 3E/c`
  have hkey : η / (c - η) ≤ (1 + 2 * w) * w * t / c + 3 * E / c := by
    rw [div_le_iff₀ hcR0]
    have hσ : η ≤ (116 / 100 * w + 29 / 10 * E) * c := by nlinarith
    have e1 : ((1 + 2 * w) * w * t / c + 3 * E / c) * (c - η) =
        (1 + 2 * w) * w * t + 3 * E - ((1 + 2 * w) * w * t + 3 * E) * (η / c) := by field_simp
    rw [e1]
    have hηc : η / c ≤ 116 / 100 * w + 29 / 10 * E := by rw [div_le_iff₀ (by linarith)]; linarith
    have h2 : ((1 + 2 * w) * w * t + 3 * E) * (η / c) ≤ ((1 + 2 * w) * w * t + 3 * E) * (116 / 100 * w + 29 / 10 * E) :=
      mul_le_mul_of_nonneg_left hηc (by positivity)
    nlinarith [mul_nonneg hw (abs_nonneg re), mul_nonneg (mul_nonneg hw hw) (abs_nonneg re), mul_nonneg hw hE,
      mul_nonneg (mul_nonneg hw (abs_nonneg re)) hE, mul_nonneg hE hE]
  have hfin : η / ((c - η) * c) ≤ ((1 + 2 * w) * w * K + 3 * E / (s * c)) * (s / c) := by
    have e2 : η / ((c - η) * c) = η / (c - η) / c := by field_simp
    rw [e2]
    have h3 : (1 + 2 * w) * w * t / c ≤ (1 + 2 * w) * w * K * s := by
      have := mul_le_mul_of_nonneg_left hK (by positivity : (0 : ℝ) ≤ (1 + 2 * w) * w * s)
      have e3 : (1 + 2 * w) * w * s * (t / (s * c)) = (1 + 2 * w) * w * t / c := by field_simp
      linarith
    have e4 : ((1 + 2 * w) * w * K + 3 * E / (s * c)) * (s / c) = ((1 + 2 * w) * w * K * s + 3 * E / c) / c := by
      field_simp
    rw [e4]
    exact div_le_div_of_nonneg_right (hkey.trans (by linarith)) (by linarith)
  rw [abs_div, abs_of_pos (by linarith : 0 < Real.cos re)]
  exact hdiff.trans hfin

/-- the move from `r` to `r_e` for the cotangent, odd `q`: with `|R - r_e| ≤ w|r_e| + 2E`, `2E ≤ 2^{-90}w|r_e|` and
`0 < |r_e| ≤ r̄ ≤ 0.8`, `|cos R/sin R - cos r_e/sin r_e| ≤ (εwK + 3E/(|sin r_e| cos r_e))|cos r_e/sin r_e|` -/
theorem cot_move {R re w E rb : ℝ} (hw : 0 ≤ w) (hw1 : w ≤ 1 / 100) (hE : 0 ≤ E) (hre0 : 0 < |re|)
    (hre : |re| ≤ rb) (hrb : rb ≤ 8 / 10) (hη : |R - re| ≤ w * |re| + 2 * E) (hEre : 2 * E ≤ w * |re| / 2 ^ 90) :
    |Real.cos R / Real.sin R - Real.cos re / Real.sin re| ≤
      ((1 + 2 * w) * w * (2 * rb / sinLo (2 * rb)) + 3 * E / (|Real.sin re| * Real.cos re)) *
        |Real.cos re / Real.sin re| := by
  set η := |R - re| with hηd
  set t := |re| with htd
  set s := |Real.sin re| with hsd
  set c := Real.cos re with hcd
  set K := 2 * rb / sinLo (2 * rb) with hKd
  have hrb0 : 0 ≤ rb := (abs_nonneg re).trans hre
  have hc : 69 / 100 ≤ c := (cosLo_ge hrb0 hrb).trans (cos_ge_cosLo re rb hre (by linarith))
  have hpi := Real.pi_gt_three
  have hs : 0 < s := by
    rw [hsd, Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith)]
    exact Real.sin_pos_of_pos_of_lt_pi hre0 (by linarith)
  have hK : t / (s * c) ≤ K := K_le hre0 hre hrb
  have ht8 : t ≤ 8 / 10 := hre.trans hrb
  have hts : t ≤ 112 / 100 * s := abs_le_sin re ht8
  -- `η ≤ 1.13ws`
  have hηs : η ≤ 113 / 100 * w * s := by
    have h1 : w * t / 2 ^ 90 ≤ w * t / 1000 := div_le_div_of_nonneg_left (by positivity) (by norm_num) (by norm_num)
    have h2 : w * t ≤ w * (112 / 100 * s) := mul_le_mul_of_nonneg_left hts hw
    nlinarith
  have hsR : s - η ≤ |Real.sin R| := by
    have := Real.abs_sin_sub_sin_le R re
    have := abs_sub_abs_le_abs_sub (Real.sin re) (Real.sin R)
    rw [abs_sub_comm (Real.sin re)] at this
    linarith
  have hsη : 0 < s - η := by nlinarith
  have hsRp : 0 < |Real.sin R| := lt_of_lt_of_le hsη hsR
  have hsR0 : Real.sin R ≠ 0 := abs_pos.mp hsRp
  have hsre0 : Real.sin re ≠ 0 := abs_pos.mp hs
  -- `cot R - cot r_e = sin(r_e - R)/(sin R sin r_e)`
  have hdiff : |Real.cos R / Real.sin R - Real.cos re / Real.sin re| ≤ η / ((s - η) * s) := by
    rw [div_sub_div _ _ hsR0 hsre0, show Real.cos R * Real.sin re - Real.sin R * Real.cos re =
      Real.sin (re - R) by rw [Real.sin_sub]; ring, abs_div, abs_mul]
    have h1 : |Real.sin (re - R)| ≤ η := by rw [hηd, abs_sub_comm]; exact Real.abs_sin_le_abs
    calc |Real.sin (re - R)| / (|Real.sin R| * s) ≤ η / (|Real.sin R| * s) :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ η / ((s - η) * s) :=
          div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (mul_le_mul_of_nonneg_right hsR hs.le)
  -- `η/(s - η) ≤ εwt/s + 3E/s`
  have hkey : η / (s - η) ≤ (1 + 2 * w) * w * t / s + 3 * E / s := by
    rw [div_le_iff₀ hsη]
    have e1 : ((1 + 2 * w) * w * t / s + 3 * E / s) * (s - η) =
        (1 + 2 * w) * w * t + 3 * E - ((1 + 2 * w) * w * t + 3 * E) * (η / s) := by field_simp
    rw [e1]
    have hηs' : η / s ≤ 113 / 100 * w := by rw [div_le_iff₀ hs]; linarith
    have h2 : ((1 + 2 * w) * w * t + 3 * E) * (η / s) ≤ ((1 + 2 * w) * w * t + 3 * E) * (113 / 100 * w) :=
      mul_le_mul_of_nonneg_left hηs' (by positivity)
    nlinarith [mul_nonneg hw (abs_nonneg re), mul_nonneg (mul_nonneg hw hw) (abs_nonneg re), mul_nonneg hw hE,
      mul_nonneg (mul_nonneg (mul_nonneg hw hw) hw) (abs_nonneg re)]
  have hfin : η / ((s - η) * s) ≤ ((1 + 2 * w) * w * K + 3 * E / (s * c)) * (c / s) := by
    have e2 : η / ((s - η) * s) = η / (s - η) / s := by field_simp
    rw [e2]
    have h3 : (1 + 2 * w) * w * t / s ≤ (1 + 2 * w) * w * K * c := by
      have := mul_le_mul_of_nonneg_left hK (by positivity : (0 : ℝ) ≤ (1 + 2 * w) * w * c)
      have e3 : (1 + 2 * w) * w * c * (t / (s * c)) = (1 + 2 * w) * w * t / s := by field_simp
      linarith
    have e4 : ((1 + 2 * w) * w * K + 3 * E / (s * c)) * (c / s) = ((1 + 2 * w) * w * K * c + 3 * E / s) / s := by
      field_simp
    rw [e4]
    exact div_le_div_of_nonneg_right (hkey.trans (by linarith)) hs.le
  rw [abs_div, abs_of_pos (by linarith : 0 < Real.cos re)]
  exact hdiff.trans hfin

/-- the tangent's error: from `D` within `(M - 1)|τ_R|` of `τ_R` and `τ_R` within `(εwK + 3E/sc)|τ|` of `τ`, with
`1 ≤ M ≤ 5/3` and `εK ≤ 2`, `D` is within `(ε(M - 1 + εwK) + 5E/sc)|τ|` of `τ` -/
theorem tan_combine {D τR τ M w K E sc : ℝ} (hM1 : 1 ≤ M) (hMm : M ≤ 5 / 3) (hw : 0 ≤ w) (hK0 : 0 ≤ K)
    (hK : (1 + 2 * w) * K ≤ 2) (hE : 0 ≤ E) (hsc : 0 < sc) (h1 : |D - τR| ≤ (M - 1) * |τR|)
    (h2 : |τR - τ| ≤ ((1 + 2 * w) * w * K + 3 * E / sc) * |τ|) :
    |D - τ| ≤ ((1 + 2 * w) * (M - 1 + (1 + 2 * w) * w * K) + 5 * E / sc) * |τ| := by
  set T := (1 + 2 * w) * w * K + 3 * E / sc with hT
  have hT0 : 0 ≤ T := by positivity
  have hτR : |τR| ≤ (1 + T) * |τ| := by
    have := abs_sub_abs_le_abs_sub τR τ
    linarith
  have hτ : 0 ≤ |τ| := abs_nonneg _
  calc |D - τ| ≤ |D - τR| + |τR - τ| := abs_sub_le _ _ _
    _ ≤ (M - 1) * ((1 + T) * |τ|) + T * |τ| := add_le_add (h1.trans
        (mul_le_mul_of_nonneg_left hτR (by linarith))) h2
    _ = (M - 1 + M * ((1 + 2 * w) * w * K) + 3 * M * (E / sc)) * |τ| := by rw [hT]; ring
    _ ≤ ((1 + 2 * w) * (M - 1 + (1 + 2 * w) * w * K) + 5 * E / sc) * |τ| := by
        refine mul_le_mul_of_nonneg_right ?_ hτ
        have hEs : 0 ≤ E / sc := div_nonneg hE hsc.le
        have key : (1 + 2 * w) * (M - 1 + (1 + 2 * w) * w * K) + 5 * E / sc -
            (M - 1 + M * ((1 + 2 * w) * w * K) + 3 * M * (E / sc)) =
            w * ((M - 1) * (2 - (1 + 2 * w) * K) + 2 * w * ((1 + 2 * w) * K)) + (5 - 3 * M) * (E / sc) := by ring
        have : 0 ≤ w * ((M - 1) * (2 - (1 + 2 * w) * K) + 2 * w * ((1 + 2 * w) * K)) + (5 - 3 * M) * (E / sc) :=
          add_nonneg (mul_nonneg hw (add_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)))
            (mul_nonneg (by linarith) hEs)
        linarith

/-- `tan(r + kπ/2)` is `tan r` for even `k` and `-cot r` for odd `k`, and `|sin x cos x| = |sin r||cos r|` -/
theorem tan_quarter (re : ℝ) (k : ℤ) :
    Real.sin (re + k * (Real.pi / 2)) / Real.cos (re + k * (Real.pi / 2)) =
        (if k % 2 = 0 then Real.sin re / Real.cos re else -(Real.cos re / Real.sin re)) ∧
      |Real.sin (re + k * (Real.pi / 2)) * Real.cos (re + k * (Real.pi / 2))| = |Real.sin re| * |Real.cos re| := by
  rw [cos_add_quarter, sin_add_quarter, sin_add_quarter]
  have h0 := Int.emod_nonneg k (by norm_num : (4 : ℤ) ≠ 0)
  have h4 := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 4)
  have h2 : k % 2 = k % 4 % 2 := by omega
  rcases (show k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 by omega) with h | h | h | h
  · simp [h, show (k + 1) % 4 = 1 by omega, show k % 2 = 0 by omega, abs_mul]
  · simp [h, show (k + 1) % 4 = 2 by omega, show k % 2 = 1 by omega, abs_mul, mul_comm]
    exact div_neg _
  · simp [h, show (k + 1) % 4 = 3 by omega, show k % 2 = 0 by omega, abs_mul, neg_div_neg_eq]
  · simp [h, show (k + 1) % 4 = 0 by omega, show k % 2 = 1 by omega, abs_mul, mul_comm]
    exact neg_div _ _

/-- `K = 2r̄/sin₋(2r̄)` is nonnegative with `εK ≤ 2`, for `r̄ ≤ 0.8` and `w ≤ 1/100` -/
theorem K_bound {rb w : ℝ} (h0 : 0 ≤ rb) (h1 : rb ≤ 8 / 10) (hw1 : w ≤ 1 / 100) :
    0 ≤ 2 * rb / sinLo (2 * rb) ∧ (1 + 2 * w) * (2 * rb / sinLo (2 * rb)) ≤ 2 := by
  set t := 2 * rb with ht
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t ≤ 16 / 10 := by linarith
  rcases eq_or_lt_of_le ht0 with h | h
  · rw [← h]; simp
  have hlo : t * (1 - t ^ 2 / 6 - t ^ 6 / 5040) ≤ sinLo t := by
    unfold sinLo; nlinarith [pow_nonneg ht0 5]
  have hpos : 0 < t * (1 - t ^ 2 / 6 - t ^ 6 / 5040) := by
    have h2 : t ^ 2 ≤ 256 / 100 := by nlinarith
    have h6 : t ^ 6 ≤ 17 := by nlinarith [pow_le_pow_left₀ ht0 ht1 6]
    nlinarith
  have hs : 0 < sinLo t := lt_of_lt_of_le hpos hlo
  refine ⟨div_nonneg ht0 hs.le, ?_⟩
  rw [mul_div_assoc', div_le_iff₀ hs]
  have h2 : t ^ 2 ≤ 256 / 100 := by nlinarith
  have h6 : t ^ 6 ≤ 17 := by nlinarith [pow_le_pow_left₀ ht0 ht1 6]
  nlinarith

/-- `sin₊ t/(t cos₋ t)` grows on `[0, 1]`: the cross difference is `(b² - a²)Q(a², b²)` with
`Q ≥ 1/3 - 1/15 - 1/2160` -/
theorem tanHi_ratio_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (1 - a ^ 2 / 6 + a ^ 4 / 120) * cosLo b ≤ (1 - b ^ 2 / 6 + b ^ 4 / 120) * cosLo a := by
  have hb0 : 0 ≤ b := ha.trans hab
  set A := a ^ 2 with hA
  set B := b ^ 2 with hB
  have hA0 : 0 ≤ A := sq_nonneg a
  have hAB : A ≤ B := pow_le_pow_left₀ ha hab 2
  have hB1 : B ≤ 1 := by rw [hB]; exact pow_le_one₀ hb0 hb
  have e : (1 - b ^ 2 / 6 + b ^ 4 / 120) * cosLo a - (1 - a ^ 2 / 6 + a ^ 4 / 120) * cosLo b =
      (B - A) * (1 / 3 - (A + B) / 30 + (A ^ 2 + B ^ 2) / 720 + A * B / 240 - A * B * (A + B) / 4320 +
        A ^ 2 * B ^ 2 / 86400) := by
    unfold cosLo; rw [hA, hB]; ring
  have hAB1 : A * B ≤ 1 := (mul_le_mul (hAB.trans hB1) hB1 (hA0.trans hAB) zero_le_one).trans_eq (one_mul 1)
  have h3 : A * B * (A + B) ≤ 1 * 2 := mul_le_mul hAB1 (by linarith) (by linarith) zero_le_one
  have hQ : 0 ≤ 1 / 3 - (A + B) / 30 + (A ^ 2 + B ^ 2) / 720 + A * B / 240 - A * B * (A + B) / 4320 +
      A ^ 2 * B ^ 2 / 86400 := by
    have : 0 ≤ A * B := mul_nonneg hA0 (hA0.trans hAB)
    nlinarith [sq_nonneg A, sq_nonneg B, mul_nonneg (sq_nonneg A) (sq_nonneg B)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hAB) hQ]

/-- TAN's early return: for `|t| ≤ r̄ ≤ 1`, `|t - tan t| ≤ (tan₊(r̄)/r̄ - 1)|tan t|` -/
theorem tan_small {t rb : ℝ} (ht : |t| ≤ rb) (hrb0 : 0 < rb) (hrb : rb ≤ 1) :
    |t - Real.tan t| ≤ (tanHi rb / rb - 1) * |Real.tan t| := by
  wlog h0 : 0 ≤ t generalizing t
  · have := this (t := -t) (by rwa [abs_neg]) (by linarith)
    rwa [Real.tan_neg, abs_neg, show -t - -Real.tan t = -(t - Real.tan t) by ring, abs_neg] at this
  rw [abs_of_nonneg h0] at ht
  have hpi := Real.pi_gt_three
  have ht1 : t ≤ 1 := ht.trans hrb
  have hT : t ≤ Real.tan t := Real.le_tan h0 (by linarith)
  have hcl := cosLo_pos h0 ht1
  have hclb := cosLo_pos hrb0.le hrb
  have hc : cosLo t ≤ Real.cos t := cos_ge_cosLo t t (abs_of_nonneg h0).le ht1
  set y := tanHi rb / rb with hy
  have hsh : 0 ≤ sinHi t := by
    have : t ^ 2 ≤ 1 := pow_le_one₀ h0 ht1
    have e : sinHi t = t * (1 - t ^ 2 / 6) + t ^ 5 / 120 := by unfold sinHi; ring
    rw [e]
    exact add_nonneg (mul_nonneg h0 (by linarith)) (by positivity)
  -- `tan t ≤ sin₊ t/cos₋ t ≤ t y`
  have hTy : Real.tan t ≤ t * y := by
    have h1 : Real.tan t ≤ sinHi t / cosLo t := by
      rw [Real.tan_eq_sin_div_cos]
      have hs0 : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith)
      calc Real.sin t / Real.cos t ≤ sinHi t / Real.cos t :=
            div_le_div_of_nonneg_right (sin_le_sinHi h0 ht1) (by linarith)
        _ ≤ sinHi t / cosLo t := div_le_div_of_nonneg_left hsh hcl hc
    have e1 : sinHi t / cosLo t = t * ((1 - t ^ 2 / 6 + t ^ 4 / 120) / cosLo t) := by
      unfold sinHi; rw [mul_div_assoc']; congr 1; ring
    have e2 : tanHi rb / rb = (1 - rb ^ 2 / 6 + rb ^ 4 / 120) / cosLo rb := by
      unfold tanHi sinHi; rw [div_div, div_eq_div_iff (mul_pos hclb hrb0).ne' hclb.ne']; ring
    have h2 : sinHi t / cosLo t ≤ t * y := by
      rw [hy, e1, e2]
      refine mul_le_mul_of_nonneg_left ?_ h0
      rw [div_le_div_iff₀ hcl hclb]
      exact tanHi_ratio_mono h0 ht hrb
    exact h1.trans h2
  have hT0 : 0 ≤ Real.tan t := h0.trans hT
  rw [abs_of_nonneg hT0, abs_sub_comm, abs_of_nonneg (by linarith)]
  rcases le_or_gt 2 y with h2 | h2
  · nlinarith
  · have := mul_le_mul_of_nonneg_left hTy (by linarith : (0 : ℝ) ≤ 2 - y)
    nlinarith [mul_nonneg h0 (sq_nonneg (1 - y))]

variable (p : ℤ) (n : ℕ)

/-- TAN_n: `x` below `|x_0| < u^{n/2}`, else `2^{-e}DIV(2^eY_s, Y_c)` for even `q` and `-DIV(Y_c, Y_s)` for odd `q`,
the scaling `e` chosen from `|r_0|` -/
noncomputable def tanN (es et : ℝ → ℤ) (Ks Kc : ℝ → ℕ) (Fs Fc : ℕ → ℕ → ℝ) (x : ℕ → ℝ) : ℕ → ℝ :=
  if |x 0| < u p ^ (n / 2) then x
  else if redK p n x % 2 = 0 then fun i => (2 : ℝ) ^ (-et |redR p n x 0|) *
      (divOp p n (fun i => (2 : ℝ) ^ et |redR p n x 0| * trigYs p n es Ks Fs x i) (trigYc p n Kc Fc x)).getD i 0
  else fun i => -(divOp p n (trigYc p n Kc Fc x) (trigYs p n es Ks Fs x)).getD i 0

/-- Lemma 34's part bounds of SINR, in units of `|r|` -/
noncomputable def tanPs (r0 rb : ℝ) (Fs : ℕ → ℕ → ℝ) (K : ℕ) (i : ℕ) : ℝ :=
  if |r0| < u p ^ (n / 2) then (if i < n then abar (2 * u p) i else 0) else sinPsi p n (abar (2 * u p)) rb Fs K i

/-- Lemma 34's part bounds of COSR -/
noncomputable def tanPc (r0 rb : ℝ) (Fc : ℕ → ℕ → ℝ) (K : ℕ) (i : ℕ) : ℝ :=
  if |r0| < u p ^ (n / 2) then (if i = 0 then 1 else 0) else cosPsi p n (abar (2 * u p)) rb Fc K i

/-- `C^T = ε(max((1 + δ_S)(1 + δ_D)/(1 - δ_C), (1 + δ_C)(1 + δ_D)/(1 - δ_S)) - 1 + εu^n 2r̄/sin₋(2r̄))` with
`ε = 1 + 2u^n` -/
noncomputable def tanCT (dS dC dD rb : ℝ) : ℝ :=
  (1 + 2 * u p ^ n) * (max ((1 + dS) * (1 + dD) / (1 - dC)) ((1 + dC) * (1 + dD) / (1 - dS)) - 1 +
    (1 + 2 * u p ^ n) * u p ^ n * (2 * rb / sinLo (2 * rb)))

variable [Prec_gt_0 p]

/-- the quotient on `H(θ)` operands and its scaled form: `|A/B - 2^{-e}DIV(2^e a, b)| ≤ δ_D|A/B|` -/
theorem div_scaled (hp : 1 < p) (hn : 1 ≤ n) (hQ : ((2 * n - 1 : ℕ) : ℝ) * u p < 1) {θ : ℝ} (hθ : 0 ≤ θ)
    (hρ : 2 * (θ * u p) < 1) (a b : ℕ → ℝ) (ha : ∀ i < n, F p (a i)) (hb : ∀ i < n, F p (b i))
    (haH : Htheta p n θ a) (hbH : Htheta p n θ b) (hb0 : b 0 ≠ 0) (e : ℤ) :
    |(∑ i ∈ range n, a i) / (∑ i ∈ range n, b i) -
        ∑ i ∈ range n, (2 : ℝ) ^ (-e) * (divOp p n (fun i => (2 : ℝ) ^ e * a i) b).getD i 0| ≤
      (u p ^ n + kdiv p n (θ * u p) * u p ^ (n + 1)) * |(∑ i ∈ range n, a i) / ∑ i ∈ range n, b i| := by
  have he : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  have haF : ∀ i < n, F p ((2 : ℝ) ^ e * a i) := fun i hi => F_zpow_mul p e (ha i hi)
  have haH' : Htheta p n θ (fun i => (2 : ℝ) ^ e * a i) := fun i h1 h2 => by
    simp only [abs_mul, abs_of_pos he]
    have := haH i h1 h2
    nlinarith [abs_nonneg (a i)]
  have h := thm19 p n hp hn hQ hθ hρ _ b haF hb haH' hbH hb0
  have hlen : (divOp p n (fun i => (2 : ℝ) ^ e * a i) b).length ≤ n :=
    (ren_spec p n hn _ (fun i _ => F_RN p _)).1
  have hs : ∑ i ∈ range n, (2 : ℝ) ^ (-e) * (divOp p n (fun i => (2 : ℝ) ^ e * a i) b).getD i 0 =
      (2 : ℝ) ^ (-e) * (divOp p n (fun i => (2 : ℝ) ^ e * a i) b).sum := by
    rw [← mul_sum, list_sum_getD _ n hlen]
  have hsa : ∑ i ∈ range n, (2 : ℝ) ^ e * a i = (2 : ℝ) ^ e * ∑ i ∈ range n, a i := by rw [mul_sum]
  rw [hsa] at h
  rw [hs]
  set A := ∑ i ∈ range n, a i with hA
  set B := ∑ i ∈ range n, b i with hB
  set Q := (divOp p n (fun i => (2 : ℝ) ^ e * a i) b).sum with hQd
  set δ := u p ^ n + kdiv p n (θ * u p) * u p ^ (n + 1) with hδ
  have hee : (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e = 1 := by rw [← zpow_add₀ two_ne_zero]; simp
  have he' : (0 : ℝ) < (2 : ℝ) ^ (-e) := by positivity
  have e1 : A / B - (2 : ℝ) ^ (-e) * Q = (2 : ℝ) ^ (-e) * ((2 : ℝ) ^ e * A / B - Q) := by
    rw [mul_sub, mul_div_assoc, ← mul_assoc, hee, one_mul]
  have e2 : |(2 : ℝ) ^ e * A / B| = (2 : ℝ) ^ e * |A / B| := by
    rw [mul_div_assoc, abs_mul, abs_of_pos he]
  rw [e2] at h
  rw [e1, abs_mul, abs_of_pos he']
  calc (2 : ℝ) ^ (-e) * |(2 : ℝ) ^ e * A / B - Q| ≤ (2 : ℝ) ^ (-e) * (δ * ((2 : ℝ) ^ e * |A / B|)) :=
        mul_le_mul_of_nonneg_left h he'.le
    _ = ((2 : ℝ) ^ (-e) * (2 : ℝ) ^ e) * (δ * |A / B|) := by ring
    _ = δ * |A / B| := by rw [hee, one_mul]

omit [Prec_gt_0 p] in
/-- an element of `F` is rational -/
theorem F_rat {x : ℝ} (hx : F p x) : ∃ q : ℚ, (q : ℝ) = x := by
  obtain ⟨m, hm⟩ := F_mult p hx
  set E := FloatSpec.Core.Generic_fmt.cexp 2 (FloatSpec.Core.FLX.FLX_exp p) x with hE
  exact ⟨m * (2 : ℚ) ^ E, by push_cast; exact hm.symm⟩

omit [Prec_gt_0 p] in
/-- `x - kπ/2 ≠ 0` for `k ≠ 0` and `x` a sum of elements of `F`, as `π` is irrational -/
theorem sub_kpi_ne (x : ℕ → ℝ) (hx : ∀ i < n, F p (x i)) (k : ℤ) (hk : k ≠ 0) :
    ∑ i ∈ range n, x i - k * (Real.pi / 2) ≠ 0 := by
  have hq : ∃ q : ℚ, (q : ℝ) = ∑ i ∈ range n, x i := by
    choose f hf using fun i (hi : i < n) => F_rat p (hx i hi)
    refine ⟨∑ i ∈ (range n).attach, f i.1 (mem_range.mp i.2), ?_⟩
    push_cast
    rw [← sum_attach (range n) (fun i => x i)]
    exact sum_congr rfl fun i _ => hf _ _
  obtain ⟨q, hq⟩ := hq
  intro h
  have hpi : Real.pi = ((2 * q / k : ℚ) : ℝ) := by
    push_cast
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    rw [hq]
    field_simp
    linarith
  exact irrational_pi ⟨_, hpi.symm⟩

omit [Prec_gt_0 p] in
/-- the parts of a sum near `f`, `m S ≤ |f|`, with `|Y_i| ≤ ψ_i S` and `ψ_i ≤ ρ^iλ`, `λ = m(1 - δ) - Σ_{i≥1}ψ_i`, give
`λS ≤ |Y_0|` and `Y ∈ H(θ)` -/
theorem parts_H (hn : 1 ≤ n) {Y ψ : ℕ → ℝ} {f S m d θ : ℝ} (hθ : 0 ≤ θ) (hd : d ≤ 1) (hS : 0 ≤ S)
    (hf : m * S ≤ |f|) (h1 : |∑ i ∈ range n, Y i - f| ≤ d * |f|) (h2 : ∀ i, |Y i| ≤ ψ i * S)
    (hψ : ∀ i, 1 ≤ i → i < n → ψ i ≤ (θ * u p) ^ i * (m * (1 - d) - ∑ i ∈ Ico 1 n, ψ i)) :
    (m * (1 - d) - ∑ i ∈ Ico 1 n, ψ i) * S ≤ |Y 0| ∧ Htheta p n θ Y := by
  have h0 : (m * (1 - d) - ∑ i ∈ Ico 1 n, ψ i) * S ≤ |Y 0| := by
    have g1 : (1 - d) * |f| ≤ |∑ i ∈ range n, Y i| := by
      have := abs_sub_abs_le_abs_sub f (∑ i ∈ range n, Y i)
      rw [abs_sub_comm] at this
      linarith
    have g2 : |∑ i ∈ range n, Y i - Y 0| ≤ ∑ i ∈ Ico 1 n, ψ i * S := by
      rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega), add_sub_cancel_left]
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => h2 i)
    have g3 : |∑ i ∈ range n, Y i| ≤ |Y 0| + (∑ i ∈ Ico 1 n, ψ i) * S := by
      have := abs_sub_abs_le_abs_sub (∑ i ∈ range n, Y i) (Y 0)
      rw [← sum_mul] at g2
      linarith
    have g4 : (1 - d) * (m * S) ≤ (1 - d) * |f| := mul_le_mul_of_nonneg_left hf (by linarith)
    have e : (m * (1 - d) - ∑ i ∈ Ico 1 n, ψ i) * S = (1 - d) * (m * S) - (∑ i ∈ Ico 1 n, ψ i) * S := by ring
    rw [e]
    linarith
  refine ⟨h0, fun i i1 i2 => ?_⟩
  calc |Y i| ≤ ψ i * S := h2 i
    _ ≤ (θ * u p) ^ i * (m * (1 - d) - ∑ i ∈ Ico 1 n, ψ i) * S := mul_le_mul_of_nonneg_right (hψ i i1 i2) hS
    _ ≤ (θ * u p) ^ i * |Y 0| := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left h0 (pow_nonneg (mul_nonneg hθ (u_pos p).le) i)

/-- the quotient step: `S/C` within `(M - 1)|S/C|` of `D`, `M = (1 + x)(1 + z)/(1 - y)`, then the move -/
theorem tan_ratio {A B D S C τ w K E sc x y z : ℝ} (hC : C ≠ 0) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z)
    (hx : x ≤ 1 / 10) (hy : y ≤ 1 / 10) (hz : z ≤ 1 / 10) (hw : 0 ≤ w) (hK0 : 0 ≤ K) (hK : (1 + 2 * w) * K ≤ 2)
    (hE : 0 ≤ E) (hsc : 0 < sc) (hA : |A - S| ≤ x * |S|) (hB : |B - C| ≤ y * |C|) (hD : |A / B - D| ≤ z * |A / B|)
    (hm : |S / C - τ| ≤ ((1 + 2 * w) * w * K + 3 * E / sc) * |τ|) :
    |D - τ| ≤ ((1 + 2 * w) * ((1 + x) * (1 + z) / (1 - y) - 1 + (1 + 2 * w) * w * K) + 5 * E / sc) * |τ| := by
  have h1 : 1 ≤ (1 + x) * (1 + z) := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have h2 : (1 + x) * (1 + z) ≤ 11 / 10 * (11 / 10) := mul_le_mul (by linarith) (by linarith) (by linarith)
    (by norm_num)
  have hM1 : 1 ≤ (1 + x) * (1 + z) / (1 - y) := (le_div_iff₀ (show (0 : ℝ) < 1 - y by linarith)).mpr (by linarith)
  have hM5 : (1 + x) * (1 + z) / (1 - y) ≤ 5 / 3 :=
    (div_le_iff₀ (show (0 : ℝ) < 1 - y by linarith)).mpr (by linarith)
  exact tan_combine hM1 hM5 hw hK0 hK hE hsc (ratio_bound hC (by linarith) hx0 hy0 hz0 hA hB hD) hm

/-- `r_e = x - kπ/2 ≠ 0` beyond TAN's early return -/
theorem tan_re_pos (hp : p = 53) (hn : 1 ≤ n) (x : ℕ → ℝ) (hx : ∀ i < n, F p (x i)) (hH : Htheta p n 2 x)
    (hx0 : |x 0| ≤ 2 ^ 52) (hbig : ¬|x 0| < u p ^ (n / 2)) :
    0 < |∑ i ∈ range n, x i - redK p n x * (Real.pi / 2)| := by
  have hu := u_pos p
  have hu53 : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num
  obtain ⟨-, hka, hkb⟩ := lemma32_k p n hp hn x hH hx0
  refine abs_pos.mpr ?_
  by_cases hk0 : redK1 p x = 0
  · obtain ⟨hk', -, -⟩ := hka hk0
    rw [hk', Int.cast_zero, zero_mul, sub_zero]
    intro hX0
    have htail := Htheta_tail p n hn 2 (by norm_num) (by rw [hu53]; norm_num) x hH
    rw [hX0, zero_sub, abs_neg, hu53] at htail
    norm_num at htail
    have : 0 < |x 0| := lt_of_lt_of_le (pow_pos hu _) (not_lt.mp hbig)
    linarith
  · exact sub_kpi_ne p n x hx _ (hkb hk0).1

omit [Prec_gt_0 p] in
/-- `|r_e| ≥ 2^{pn-1074}` and `|k| ≤ 0.64·2^{52}` give `2E_π ≤ 2^{-90}u^n|r_e|` -/
theorem tan_far {k : ℤ} {re : ℝ} (hk : |(k : ℝ)| ≤ 64 / 100 * 2 ^ 52)
    (hre : (2 : ℝ) ^ (p * n - 1074) ≤ |re|) :
    2 * (|(k : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) ≤ u p ^ n * |re| / 2 ^ 90 := by
  have hun : u p ^ n * (2 : ℝ) ^ (p * n - 1074) = (2 : ℝ) ^ (-1074 : ℤ) := by
    unfold u
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ two_ne_zero]
    congr 1
    ring
  have h1 : (2 : ℝ) ^ (-1074 : ℤ) ≤ u p ^ n * |re| := by
    rw [← hun]; exact mul_le_mul_of_nonneg_left hre (pow_nonneg (u_pos p).le n)
  have h2 : (2 : ℝ) ^ (-1074 : ℤ) = 2 ^ 90 * ((2 : ℝ) ^ 52 * (2 : ℝ) ^ (-1217 : ℤ)) * 2 := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero,
      ← zpow_add_one₀ two_ne_zero]
    norm_num
  have h3 : 0 < (2 : ℝ) ^ (-1217 : ℤ) := by positivity
  rw [le_div_iff₀ (by positivity)]
  have h4 : |(k : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ) ≤ 64 / 100 * ((2 : ℝ) ^ 52 * (2 : ℝ) ^ (-1217 : ℤ)) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hk h3.le
  have h5 : 0 ≤ (2 : ℝ) ^ 52 * (2 : ℝ) ^ (-1217 : ℤ) := by positivity
  nlinarith

/-- Theorem 35 for TAN (`thm:trig`), at `p = 53` beyond the early return, for `x` on `H(2)` with `|x_0| ≤ 2^52` and
`(n² + n)u < 1`: with RED's `r` and `r_e` within `r̄ ≤ 0.8`, Lemma 34's `δ_S, δ_C ∈ [0, 1/10]`, series of at least two
terms, SINR's and COSR's parts on `H(θ)` with `0 ≤ θ` and `2θu < 1` through `ψ_{s,i} ≤ (θu)^iλ_s` and
`ψ_{c,i} ≤ (θu)^iλ_c` with `λ_s, λ_c > 0`, `δ_D = u^n + κ_DIV u^{n+1} ∈ [0, 1/10]`, and `|x - kπ/2| ≥ 2^{pn-1074}` for
`k ≠ 0`, `|TAN_n(x) - tan x| ≤ (C^T + 5E_π/|sin x cos x|)|tan x|` -/
theorem thm35_tan (hp : p = 53) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (x : ℕ → ℝ)
    (hx : ∀ i < n, F p (x i)) (hH : Htheta p n 2 x) (hx0 : |x 0| ≤ 2 ^ 52) (hbig : ¬|x 0| < u p ^ (n / 2))
    (es et : ℝ → ℤ) (Ks Kc : ℝ → ℕ) (Fs Fc : ℕ → ℕ → ℝ) (hFs : ∀ k, ∀ i < n, F p (Fs k i))
    (hFc : ∀ k, ∀ i < n, F p (Fc k i)) (hKs : 2 ≤ Ks |redR p n x 0|) (hKc : 2 ≤ Kc |redR p n x 0|) (rb : ℝ)
    (hrb : rb ≤ 8 / 10) (hr : |∑ i ∈ range n, redR p n x i| ≤ rb)
    (hre : |∑ i ∈ range n, x i - redK p n x * (Real.pi / 2)| ≤ rb)
    (hdS0 : 0 ≤ trigDS p n (redR p n x 0) rb Fs (Ks |redR p n x 0|))
    (hdS : trigDS p n (redR p n x 0) rb Fs (Ks |redR p n x 0|) ≤ 1 / 10)
    (hdC0 : 0 ≤ trigDC p n (redR p n x 0) rb Fc (Kc |redR p n x 0|))
    (hdC : trigDC p n (redR p n x 0) rb Fc (Kc |redR p n x 0|) ≤ 1 / 10) {θ : ℝ} (hθ : 0 ≤ θ)
    (hρ : 2 * (θ * u p) < 1) (hdD0 : 0 ≤ u p ^ n + kdiv p n (θ * u p) * u p ^ (n + 1))
    (hdD : u p ^ n + kdiv p n (θ * u p) * u p ^ (n + 1) ≤ 1 / 10)
    (hlamS : 0 < (1 - rb ^ 2 / 6) * (1 - trigDS p n (redR p n x 0) rb Fs (Ks |redR p n x 0|)) -
      ∑ i ∈ Ico 1 n, tanPs p n (redR p n x 0) rb Fs (Ks |redR p n x 0|) i)
    (hψs : ∀ i, 1 ≤ i → i < n → tanPs p n (redR p n x 0) rb Fs (Ks |redR p n x 0|) i ≤ (θ * u p) ^ i *
      ((1 - rb ^ 2 / 6) * (1 - trigDS p n (redR p n x 0) rb Fs (Ks |redR p n x 0|)) -
        ∑ i ∈ Ico 1 n, tanPs p n (redR p n x 0) rb Fs (Ks |redR p n x 0|) i))
    (hlamC : 0 < cosLo rb * (1 - trigDC p n (redR p n x 0) rb Fc (Kc |redR p n x 0|)) -
      ∑ i ∈ Ico 1 n, tanPc p n (redR p n x 0) rb Fc (Kc |redR p n x 0|) i)
    (hψc : ∀ i, 1 ≤ i → i < n → tanPc p n (redR p n x 0) rb Fc (Kc |redR p n x 0|) i ≤ (θ * u p) ^ i *
      (cosLo rb * (1 - trigDC p n (redR p n x 0) rb Fc (Kc |redR p n x 0|)) -
        ∑ i ∈ Ico 1 n, tanPc p n (redR p n x 0) rb Fc (Kc |redR p n x 0|) i))
    (hfar : redK p n x ≠ 0 → (2 : ℝ) ^ (p * n - 1074) ≤ |∑ i ∈ range n, x i - redK p n x * (Real.pi / 2)|) :
    |∑ i ∈ range n, tanN p n es et Ks Kc Fs Fc x i - Real.tan (∑ i ∈ range n, x i)| ≤
      (tanCT p n (trigDS p n (redR p n x 0) rb Fs (Ks |redR p n x 0|))
          (trigDC p n (redR p n x 0) rb Fc (Kc |redR p n x 0|)) (u p ^ n + kdiv p n (θ * u p) * u p ^ (n + 1)) rb +
        5 * (|(redK p n x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) /
          |Real.sin (∑ i ∈ range n, x i) * Real.cos (∑ i ∈ range n, x i)|) * |Real.tan (∑ i ∈ range n, x i)| := by
  have hp1 : 1 < p := by omega
  have hu := u_pos p
  have hu53 : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num
  obtain ⟨hk, -, -⟩ := lemma32_k p n hp hn x hH hx0
  obtain ⟨hrF, hrH, -, hη, -⟩ := lemma32_r p n hp hn x hx hH hx0
  set k := redK p n x with hkd
  set r := redR p n x with hrd
  set R := ∑ i ∈ range n, r i with hRd
  set X := ∑ i ∈ range n, x i with hXd
  set re := X - k * (Real.pi / 2) with hred
  set E := |(k : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ) with hEd
  set dS := trigDS p n (r 0) rb Fs (Ks |r 0|) with hdSd
  set dC := trigDC p n (r 0) rb Fc (Kc |r 0|) with hdCd
  set dD := u p ^ n + kdiv p n (θ * u p) * u p ^ (n + 1) with hdDd
  set w := u p ^ n with hwd
  set K := 2 * rb / sinLo (2 * rb) with hKd
  set ψs := tanPs p n (r 0) rb Fs (Ks |r 0|) with hψsd
  set ψc := tanPc p n (r 0) rb Fc (Kc |r 0|) with hψcd
  set lamS := (1 - rb ^ 2 / 6) * (1 - dS) - ∑ i ∈ Ico 1 n, ψs i with hlamSd
  set lamC := cosLo rb * (1 - dC) - ∑ i ∈ Ico 1 n, ψc i with hlamCd
  have hrb0 : 0 ≤ rb := (abs_nonneg _).trans hr
  have hrb1 : rb ≤ 1 := by linarith
  have hre0 : 0 < |re| := tan_re_pos p n hp hn x hx hH hx0 hbig
  -- the parts of `r` and Lemma 34
  have hρ2 : 2 * (2 * u p) < 1 := by rw [hu53]; norm_num
  have hab0 : ∀ i, 0 ≤ abar (2 * u p) i := fun i => by
    unfold abar; exact mul_nonneg (pow_nonneg (by positivity) i) (div_nonneg (by linarith) (by linarith))
  have hab : ∀ i < n, |r i| ≤ abar (2 * u p) i * |R| := fun i hi => by
    have h0 := Htheta_a0 p n hn 2 (by norm_num) hρ2 r hrH
    calc |r i| ≤ (2 * u p) ^ i * |r 0| := Htheta_le p n hrH i hi
      _ ≤ (2 * u p) ^ i * ((1 - 2 * u p) / (1 - 2 * (2 * u p)) * |R|) :=
          mul_le_mul_of_nonneg_left h0 (pow_nonneg (by positivity) i)
      _ = _ := by unfold abar; ring
  obtain ⟨s1, s2, s3⟩ := lemma34_sin p n hp1 hn hA3 r hrF _ hab0 hab rb rb (fun _ => hr) hrb1 (fun _ => hr) hrb1 Fs
    hFs (Ks |r 0|) hKs (es |r 0|)
  obtain ⟨c1, c2, c3⟩ := lemma34_cos p n hp1 hn hA3 r hrF _ hab0 hab rb rb (fun _ => hr) hrb1 (fun _ => hr) hrb1 Fc
    hFc (Kc |r 0|) hKc
  set Ys := trigYs p n es Ks Fs x with hYsd
  set Yc := trigYc p n Kc Fc x with hYcd
  set A := ∑ i ∈ range n, Ys i with hAd
  set B := ∑ i ∈ range n, Yc i with hBd
  replace s1 : |A - Real.sin R| ≤ dS * |Real.sin R| := s1
  replace c1 : |B - Real.cos R| ≤ dC * Real.cos R := c1
  replace s2 : ∀ i, |Ys i| ≤ ψs i * |R| := s2
  replace c2 : ∀ i, |Yc i| ≤ ψc i := c2
  replace s3 : ∀ i, F p (Ys i) := s3
  replace c3 : ∀ i, F p (Yc i) := c3
  -- `cos R ≥ cos₋ r̄ ≥ 0.69` and `|sin R| ≥ |R|(1 - r̄²/6)`
  have hcR : cosLo rb ≤ Real.cos R := cos_ge_cosLo R rb hr hrb1
  have hcl : 69 / 100 ≤ cosLo rb := cosLo_ge hrb0 hrb
  have hsR : |R| * (1 - rb ^ 2 / 6) ≤ |Real.sin R| := by
    have h := abs_sin_ge R (hr.trans hrb1)
    have : R ^ 2 ≤ rb ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hr 2
    nlinarith [abs_nonneg R]
  -- `Y_s` and `Y_c` on `H(θ)`
  have hcRp : 0 < Real.cos R := by linarith
  have hcR' : |B - Real.cos R| ≤ dC * |Real.cos R| := by rw [abs_of_pos hcRp]; exact c1
  obtain ⟨hYs0, hYsH⟩ := parts_H p n hn hθ (by linarith) (abs_nonneg R) (by rw [mul_comm]; exact hsR) s1 s2 hψs
  obtain ⟨hYc0, hYcH⟩ := parts_H p n hn hθ (by linarith) zero_le_one
    (by rw [mul_one, abs_of_pos hcRp]; exact hcR) hcR' (fun i => by rw [mul_one]; exact c2 i) hψc
  rw [mul_one] at hYc0
  have hYc00 : Yc 0 ≠ 0 := abs_pos.mp (lt_of_lt_of_le hlamC hYc0)
  have hQ : ((2 * n - 1 : ℕ) : ℝ) * u p < 1 := by
    have hn2 : n ≤ n ^ 2 := Nat.le_self_pow (by norm_num) n
    have h1 : (2 * n - 1 : ℕ) ≤ n ^ 2 + n := by omega
    have h2 : ((2 * n - 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 + n := by exact_mod_cast h1
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right h2 hu.le) hA3
  -- the move's constants
  have hw0 : 0 ≤ w := pow_nonneg hu.le n
  have hw1 : w ≤ 1 / 100 := by
    calc w ≤ u p ^ 1 := pow_le_pow_of_le_one hu.le (by rw [hu53]; norm_num) hn
      _ = u p := pow_one _
      _ ≤ 1 / 100 := by rw [hu53]; norm_num
  have hE0 : 0 ≤ E := by positivity
  have hE1 : E ≤ 1 / 1000 := by
    have h2 : (2 : ℝ) ^ (-1217 : ℤ) ≤ 1 / 2 ^ 70 := by
      rw [zpow_neg, ← one_div, one_div_le_one_div (by positivity) (by positivity)]
      exact_mod_cast pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : 70 ≤ 1217)
    calc E ≤ 64 / 100 * 2 ^ 52 * (1 / 2 ^ 70) := mul_le_mul hk.le h2 (by positivity) (by positivity)
      _ ≤ 1 / 1000 := by norm_num
  have husn : us p ^ n ≤ w := pow_le_pow_left₀ (us_nonneg p) (us_le_u p) n
  have hη' : |R - re| ≤ w * |re| + 2 * E := by
    have := mul_le_mul_of_nonneg_right husn (abs_nonneg re)
    linarith
  obtain ⟨hK0, hK⟩ := K_bound hrb0 hrb hw1
  have hcre : 0 < Real.cos re := by
    have := cos_ge_cosLo re rb hre hrb1
    linarith
  have hsc : 0 < |Real.sin re| * Real.cos re := by
    have hpi := Real.pi_gt_three
    have : 0 < |Real.sin re| := by
      rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith)]
      exact Real.sin_pos_of_pos_of_lt_pi hre0 (by linarith)
    positivity
  obtain ⟨htq, hsc'⟩ := tan_quarter re k
  have hXre : X = re + k * (Real.pi / 2) := by rw [hred]; ring
  rw [hXre, Real.tan_eq_sin_div_cos, htq, hsc', abs_of_pos hcre]
  set Me := (1 + dS) * (1 + dD) / (1 - dC) with hMe
  set Mo := (1 + dC) * (1 + dD) / (1 - dS) with hMo
  have hfin : ∀ M τ D : ℝ, M ≤ max Me Mo →
      |D - τ| ≤ ((1 + 2 * w) * (M - 1 + (1 + 2 * w) * w * K) + 5 * E / (|Real.sin re| * Real.cos re)) * |τ| →
      |D - τ| ≤ (tanCT p n dS dC dD rb + 5 * E / (|Real.sin re| * Real.cos re)) * |τ| := by
    intro M τ D hM h
    refine h.trans (mul_le_mul_of_nonneg_right (add_le_add ?_ le_rfl) (abs_nonneg _))
    unfold tanCT
    rw [← hwd, ← hKd]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hlen : ∀ a b : ℕ → ℝ, (divOp p n a b).length ≤ n := fun a b => (ren_spec p n hn _ (fun i _ => F_RN p _)).1
  by_cases hev : k % 2 = 0
  · -- even `q`: `2^{-e}DIV(2^eY_s, Y_c)` and `tan r_e`
    simp only [hev, ite_true]
    have hT : ∑ i ∈ range n, tanN p n es et Ks Kc Fs Fc x i =
        ∑ i ∈ range n, (2 : ℝ) ^ (-et |r 0|) * (divOp p n (fun i => (2 : ℝ) ^ et |r 0| * Ys i) Yc).getD i 0 := by
      simp only [tanN, hbig, ite_false, ← hkd, hev, ite_true]
      rfl
    rw [hT]
    have hD := div_scaled p n hp1 hn hQ hθ hρ Ys Yc (fun i _ => s3 i) (fun i _ => c3 i) hYsH hYcH hYc00 (et |r 0|)
    rw [← hAd, ← hBd] at hD
    exact hfin Me _ _ (le_max_left _ _) (tan_ratio hcRp.ne' hdS0 hdC0 hdD0 hdS hdC hdD hw0 hK0 hK hE0 hsc s1 hcR' hD
      (tan_move hw0 hw1 hE0 hE1 hre0 hre hrb hη'))
  · -- odd `q`: `-DIV(Y_c, Y_s)` and `-cot r_e`
    simp only [hev, ite_false]
    have hk1 : k % 2 = 1 := by omega
    have hT : ∑ i ∈ range n, tanN p n es et Ks Kc Fs Fc x i = -(divOp p n Yc Ys).sum := by
      simp only [tanN, hbig, ite_false, ← hkd, hev]
      rw [sum_neg_distrib, ← list_sum_getD _ n (hlen _ _)]
    rw [hT, neg_sub_neg, abs_sub_comm, abs_neg]
    have hEre : 2 * E ≤ w * |re| / 2 ^ 90 := tan_far p n hk.le (hfar (by omega))
    -- `R ≠ 0`, so `sin R ≠ 0` and `Y_s,0 ≠ 0`
    have hRpos : 0 < |R| := by
      have h3 : 2 * E ≤ w * |re| / 2 := hEre.trans (div_le_div_of_nonneg_left (by positivity) (by norm_num)
        (by norm_num))
      have := abs_sub_abs_le_abs_sub re R
      rw [abs_sub_comm re] at this
      have := mul_le_mul_of_nonneg_right hw1 (abs_nonneg re)
      linarith
    have hrb2 : rb ^ 2 ≤ (8 / 10) ^ 2 := pow_le_pow_left₀ hrb0 hrb 2
    have hsRp : 0 < |Real.sin R| := lt_of_lt_of_le (mul_pos hRpos (by linarith)) hsR
    have hYs00 : Ys 0 ≠ 0 := abs_pos.mp (lt_of_lt_of_le (mul_pos hlamS hRpos) hYs0)
    have hD := thm19 p n hp1 hn hQ hθ hρ Yc Ys (fun i _ => c3 i) (fun i _ => s3 i) hYcH hYsH hYs00
    rw [← hAd, ← hBd] at hD
    exact hfin Mo _ _ (le_max_right _ _) (tan_ratio (abs_pos.mp hsRp) hdC0 hdS0 hdD0 hdC hdS hdD hw0 hK0 hK hE0 hsc
      hcR' s1 hD (cot_move hw0 hw1 hE0 hre0 hre hrb hη' hEre))

omit [Prec_gt_0 p] in
/-- Theorem 35 for TAN's early return: for `n ≥ 2` and `x` on `H(2)` below `|x_0| < u^{n/2}`, TAN returns `x` within
`(tan₊(r̄_min)/r̄_min - 1)|tan x|`, `r̄_min = u^{n/2}(1 + 2^{-50})` -/
theorem thm35_tan_small (hp : p = 53) (hn : 2 ≤ n) (x : ℕ → ℝ) (hH : Htheta p n 2 x)
    (hsmall : |x 0| < u p ^ (n / 2)) (es et : ℝ → ℤ) (Ks Kc : ℝ → ℕ) (Fs Fc : ℕ → ℕ → ℝ) :
    |∑ i ∈ range n, tanN p n es et Ks Kc Fs Fc x i - Real.tan (∑ i ∈ range n, x i)| ≤
      (tanHi (u p ^ (n / 2) * (1 + 1 / 2 ^ 50)) / (u p ^ (n / 2) * (1 + 1 / 2 ^ 50)) - 1) *
        |Real.tan (∑ i ∈ range n, x i)| := by
  have hu := u_pos p
  have hu53 : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num
  obtain ⟨hX, -, -⟩ := thm35_small p n hp hn x hH hsmall es Ks Kc Fs Fc
  have hT : ∑ i ∈ range n, tanN p n es et Ks Kc Fs Fc x i = ∑ i ∈ range n, x i := by
    simp only [tanN, hsmall, ite_true]
  rw [hT]
  have hun : u p ^ (n / 2) ≤ u p ^ 1 := pow_le_pow_of_le_one hu.le (by rw [hu53]; norm_num) (by omega)
  rw [pow_one] at hun
  exact tan_small hX (by positivity) (by linarith)


end ExpansionBounds
