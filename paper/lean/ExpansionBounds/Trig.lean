import ExpansionBounds.Red
import ExpansionBounds.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Theorem 35: SIN and COS

SIN_n and COS_n return `x` and `1` below `|x_0| < u^{n/2}`, and otherwise SINR and COSR of RED's `r`, chosen and
signed by the quadrant `q = k mod 4`, as `sin x` and `cos x` are `±sin r_e` or `±cos r_e` with `r_e = x - kπ/2`.
Lemma 32 puts `r` within `η ≤ ū^n|r_e| + 2E_π` of `r_e` and both within `r̄`, Lemma 34 bounds SINR and COSR
relative to `sin r` and `cos r`, and the moves from `r` to `r_e` cost `|sin r - sin r_e| ≤ η(cos r_e + η/2)` and
`|cos r - cos r_e| ≤ η(|sin r_e| + η/2)`, with `|r_e|cos r_e ≤ |sin r_e|`, `|r_e| ≤ 1.12|sin r_e|` and
`|r_e||sin r_e| ≤ r̄ tan₊(r̄) cos r_e`.
-/

namespace ExpansionBounds

open Finset

/-- `sin(r + kπ/2)` by `k mod 4`: `sin r`, `cos r`, `-sin r`, `-cos r` -/
theorem sin_add_quarter (r : ℝ) (k : ℤ) : Real.sin (r + k * (Real.pi / 2)) =
    if k % 4 = 0 then Real.sin r else if k % 4 = 1 then Real.cos r else if k % 4 = 2 then -Real.sin r
    else -Real.cos r := by
  have hk : (k : ℝ) = ((k % 4 : ℤ) : ℝ) + ((k / 4 : ℤ) : ℝ) * 4 := by
    have := Int.emod_add_mul_ediv k 4
    exact_mod_cast (by linarith : k = k % 4 + k / 4 * 4)
  have h : r + k * (Real.pi / 2) = (r + ((k % 4 : ℤ) : ℝ) * (Real.pi / 2)) + ((k / 4 : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hk]; ring
  rw [h, Real.sin_add_int_mul_two_pi]
  have h0 := Int.emod_nonneg k (by norm_num : (4 : ℤ) ≠ 0)
  have h4 := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 4)
  obtain ⟨q, hq⟩ : ∃ q, q = k % 4 := ⟨_, rfl⟩
  rw [← hq] at h0 h4 ⊢
  interval_cases q
  · simp
  · simp [Real.sin_add_pi_div_two]
  · have : r + ((2 : ℤ) : ℝ) * (Real.pi / 2) = r + Real.pi := by push_cast; ring
    simp only [this, Real.sin_add_pi]
    norm_num
  · have : r + ((3 : ℤ) : ℝ) * (Real.pi / 2) = (r + Real.pi) + Real.pi / 2 := by push_cast; ring
    simp only [this, Real.sin_add_pi_div_two, Real.cos_add_pi]
    norm_num

/-- `cos(r + kπ/2) = sin(r + (k + 1)π/2)` -/
theorem cos_add_quarter (r : ℝ) (k : ℤ) : Real.cos (r + k * (Real.pi / 2)) =
    Real.sin (r + ((k + 1 : ℤ) : ℝ) * (Real.pi / 2)) := by
  rw [← Real.sin_add_pi_div_two]
  congr 1
  push_cast
  ring

/-- `sin₊(t) = t - t³/6 + t⁵/120 ≥ sin t` on `[0, 1]` -/
noncomputable def sinHi (t : ℝ) : ℝ := t - t ^ 3 / 6 + t ^ 5 / 120

/-- `tan₊ = sin₊/cos₋` -/
noncomputable def tanHi (t : ℝ) : ℝ := sinHi t / cosLo t

theorem sin_le_sinHi {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : Real.sin t ≤ sinHi t := by
  set f : ℕ → ℝ := fun i => t ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)
  have hsin : HasSum (fun i => (-1) ^ i * f i) (Real.sin t) := by
    have := Real.hasSum_sin t
    convert this using 1
    funext i
    simp only [f]
    ring
  have hhi := (pow_div_fact_antitone t h0 h1 1).tendsto_le_alternating_series hsin.tendsto_sum_nat 1
  have hval : ∑ i ∈ range (2 * 1 + 1), (-1) ^ i * f i = sinHi t := by
    simp [f, sum_range_succ, sinHi, Nat.factorial]
    ring
  rwa [hval] at hhi

theorem sin_ge_cube {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : t - t ^ 3 / 6 ≤ Real.sin t := by
  set f : ℕ → ℝ := fun i => t ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)
  have hsin : HasSum (fun i => (-1) ^ i * f i) (Real.sin t) := by
    have := Real.hasSum_sin t
    convert this using 1
    funext i
    simp only [f]
    ring
  have hlo := (pow_div_fact_antitone t h0 h1 1).alternating_series_le_tendsto hsin.tendsto_sum_nat 1
  have hval : ∑ i ∈ range (2 * 1), (-1) ^ i * f i = t - t ^ 3 / 6 := by
    simp [f, sum_range_succ, Nat.factorial]
    ring
  rwa [hval] at hlo

theorem cos_le_quartic {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : Real.cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 := by
  set f : ℕ → ℝ := fun i => t ^ (2 * i + 0) / ((2 * i + 0).factorial : ℝ)
  have hcos : HasSum (fun i => (-1) ^ i * f i) (Real.cos t) := by
    have := Real.hasSum_cos t
    convert this using 1
    funext i
    simp only [f, add_zero]
    ring
  have hhi := (pow_div_fact_antitone t h0 h1 0).tendsto_le_alternating_series hcos.tendsto_sum_nat 1
  have hval : ∑ i ∈ range (2 * 1 + 1), (-1) ^ i * f i = 1 - t ^ 2 / 2 + t ^ 4 / 24 := by
    simp [f, sum_range_succ, Nat.factorial]
    ring
  rwa [hval] at hhi

/-- `|t| cos t ≤ |sin t|` for `|t| ≤ 1` -/
theorem abs_mul_cos_le (t : ℝ) (ht : |t| ≤ 1) : |t| * Real.cos t ≤ |Real.sin t| := by
  wlog h0 : 0 ≤ t generalizing t
  · have := this (-t) (by rwa [abs_neg]) (by linarith)
    rwa [abs_neg, Real.cos_neg, Real.sin_neg, abs_neg] at this
  have h1 : t ≤ 1 := by rwa [abs_of_nonneg h0] at ht
  have hs := sin_ge_cube h0 h1
  have hc := cos_le_quartic h0 h1
  have hs0 : 0 ≤ t - t ^ 3 / 6 := by nlinarith [pow_le_one₀ h0 h1 (n := 2)]
  rw [abs_of_nonneg h0, abs_of_nonneg (hs0.trans hs)]
  have : t * (1 - t ^ 2 / 2 + t ^ 4 / 24) ≤ t - t ^ 3 / 6 := by
    have h2 : t ^ 2 ≤ 1 := pow_le_one₀ h0 h1
    nlinarith [pow_nonneg h0 3, pow_nonneg h0 5, mul_nonneg (pow_nonneg h0 3) (sub_nonneg.mpr h2)]
  nlinarith [mul_le_mul_of_nonneg_left hc h0]

/-- `|t| ≤ 1.12|sin t|` for `|t| ≤ 0.8` -/
theorem abs_le_sin (t : ℝ) (ht : |t| ≤ 8 / 10) : |t| ≤ 112 / 100 * |Real.sin t| := by
  have h := abs_sin_ge t (ht.trans (by norm_num))
  have h2 : t ^ 2 ≤ 64 / 100 := by rw [← sq_abs]; nlinarith [abs_nonneg t]
  nlinarith [abs_nonneg t]

/-- `|sin a - sin b| ≤ |a - b|(cos b + |a - b|/2)` for `|b| ≤ π/2` -/
theorem sin_near (a b : ℝ) (hb : |b| ≤ Real.pi / 2) :
    |Real.sin a - Real.sin b| ≤ |a - b| * (Real.cos b + |a - b| / 2) := by
  rw [Real.sin_sub_sin, abs_mul, abs_mul, abs_two]
  have h1 : |Real.sin ((a - b) / 2)| ≤ |a - b| / 2 := by
    have := Real.abs_sin_le_abs (x := (a - b) / 2)
    rwa [abs_div, abs_two] at this
  have h2 : |Real.cos ((a + b) / 2)| ≤ Real.cos b + |a - b| / 2 := by
    have := Real.abs_cos_sub_cos_le ((a + b) / 2) b
    have hc : 0 ≤ Real.cos b := Real.cos_nonneg_of_mem_Icc ⟨by linarith [(abs_le.mp hb).1], (abs_le.mp hb).2⟩
    rw [show (a + b) / 2 - b = (a - b) / 2 by ring, abs_div, abs_two] at this
    have := abs_sub_abs_le_abs_sub (Real.cos ((a + b) / 2)) (Real.cos b)
    rw [abs_of_nonneg hc] at this
    linarith
  calc 2 * |Real.sin ((a - b) / 2)| * |Real.cos ((a + b) / 2)| ≤ 2 * (|a - b| / 2) * (Real.cos b + |a - b| / 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- `|cos a - cos b| ≤ |a - b|(|sin b| + |a - b|/2)` -/
theorem cos_near (a b : ℝ) : |Real.cos a - Real.cos b| ≤ |a - b| * (|Real.sin b| + |a - b| / 2) := by
  rw [Real.cos_sub_cos, abs_mul, abs_mul, abs_neg, abs_two]
  have h1 : |Real.sin ((a - b) / 2)| ≤ |a - b| / 2 := by
    have := Real.abs_sin_le_abs (x := (a - b) / 2)
    rwa [abs_div, abs_two] at this
  have h2 : |Real.sin ((a + b) / 2)| ≤ |Real.sin b| + |a - b| / 2 := by
    have := Real.abs_sin_sub_sin_le ((a + b) / 2) b
    rw [show (a + b) / 2 - b = (a - b) / 2 by ring, abs_div, abs_two] at this
    have := abs_sub_abs_le_abs_sub (Real.sin ((a + b) / 2)) (Real.sin b)
    linarith
  calc 2 * |Real.sin ((a + b) / 2)| * |Real.sin ((a - b) / 2)| ≤ 2 * (|Real.sin b| + |a - b| / 2) * (|a - b| / 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) h1 (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- `sin₊` increases on `[0, 1]` -/
theorem sinHi_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : sinHi a ≤ sinHi b := by
  have key : sinHi b - sinHi a = (b - a) * (1 - (a ^ 2 + a * b + b ^ 2) / 6 +
      (a ^ 4 + a ^ 3 * b + a ^ 2 * b ^ 2 + a * b ^ 3 + b ^ 4) / 120) := by unfold sinHi; ring
  have hb0 : 0 ≤ b := ha.trans hab
  have h1 : a ^ 2 + a * b + b ^ 2 ≤ 3 := by nlinarith
  have h2 : 0 ≤ a ^ 4 + a ^ 3 * b + a ^ 2 * b ^ 2 + a * b ^ 3 + b ^ 4 := by positivity
  have : 0 ≤ (b - a) * (1 - (a ^ 2 + a * b + b ^ 2) / 6 +
      (a ^ 4 + a ^ 3 * b + a ^ 2 * b ^ 2 + a * b ^ 3 + b ^ 4) / 120) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

/-- `|t||sin t| ≤ r̄ tan₊(r̄) cos t` for `|t| ≤ r̄ ≤ 1` -/
theorem abs_mul_sin_le (t rb : ℝ) (ht : |t| ≤ rb) (hrb : rb ≤ 1) :
    |t| * |Real.sin t| ≤ rb * tanHi rb * Real.cos t := by
  have hrb0 : 0 ≤ rb := (abs_nonneg t).trans ht
  have hcl := cosLo_pos hrb0 hrb
  have hcos := cos_ge_cosLo t rb ht hrb
  have hsin : |Real.sin t| ≤ sinHi rb := by
    have h := sin_le_sinHi (abs_nonneg t) (ht.trans hrb)
    rw [← Real.abs_sin_eq_sin_abs_of_abs_le_pi] at h
    · exact h.trans (sinHi_mono (abs_nonneg t) ht hrb)
    · linarith [Real.pi_gt_three, ht.trans hrb]
  have hsh0 : 0 ≤ sinHi rb := (abs_nonneg _).trans hsin
  calc |t| * |Real.sin t| ≤ rb * sinHi rb := mul_le_mul ht hsin (abs_nonneg _) hrb0
    _ ≤ rb * sinHi rb * (Real.cos t / cosLo rb) :=
        le_mul_of_one_le_right (mul_nonneg hrb0 hsh0) ((one_le_div hcl).mpr hcos)
    _ = rb * tanHi rb * Real.cos t := by unfold tanHi; ring

/-- `r̄ tan₊(r̄) ≤ 1` for `r̄ ≤ 0.8` -/
theorem tanHi_le {rb : ℝ} (h0 : 0 ≤ rb) (h1 : rb ≤ 8 / 10) : rb * tanHi rb ≤ 1 := by
  have hcl : 69 / 100 ≤ cosLo rb := by
    unfold cosLo
    have h2 : rb ^ 2 ≤ 64 / 100 := by nlinarith
    nlinarith [pow_nonneg h0 4, pow_nonneg h0 6, pow_le_pow_left₀ h0 h1 6]
  have hsh : sinHi rb ≤ 8 / 10 := by
    have := sinHi_mono h0 h1 (by norm_num)
    unfold sinHi at this ⊢
    norm_num at this
    linarith
  unfold tanHi
  rw [mul_div_assoc', div_le_one (by linarith)]
  nlinarith [sinHi_mono le_rfl h0 (by linarith), show sinHi 0 = 0 by unfold sinHi; ring]

/-- the move from `r` to `r_e` for the sine: with `Y` within `δ_S|sin R|` of `sin R`, `|R - r_e| ≤ w|r_e| + 2E` and
`|r_e| ≤ 0.8`, `Y` is within `ε(δ_S + εw)|sin r_e| + 5E` of `sin r_e`, `ε = 1 + 2w` -/
theorem sin_move {Y R re w E dS : ℝ} (hw : 0 ≤ w) (hw1 : w ≤ 1 / 8) (hE : 0 ≤ E) (hE1 : E ≤ 1 / 8) (hdS0 : 0 ≤ dS)
    (hdS : dS ≤ 1 / 2) (hre : |re| ≤ 8 / 10) (hY : |Y - Real.sin R| ≤ dS * |Real.sin R|)
    (hη : |R - re| ≤ w * |re| + 2 * E) :
    |Y - Real.sin re| ≤ (1 + 2 * w) * (dS + (1 + 2 * w) * w) * |Real.sin re| + 5 * E := by
  set η := |R - re| with hηd
  set s := |Real.sin re| with hsd
  set t := |re| with htd
  set c := Real.cos re with hcd
  have hη0 : 0 ≤ η := abs_nonneg _
  have hs0 : 0 ≤ s := abs_nonneg _
  have ht0 : 0 ≤ t := abs_nonneg _
  have hpi : 8 / 10 ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hc0 : 0 ≤ c := Real.cos_nonneg_of_mem_Icc ⟨by linarith [(abs_le.mp (hre.trans hpi)).1],
    (abs_le.mp (hre.trans hpi)).2⟩
  have hc1 : c ≤ 1 := Real.cos_le_one _
  have hts : t ≤ 112 / 100 * s := abs_le_sin re hre
  have htc : t * c ≤ s := abs_mul_cos_le re (hre.trans (by norm_num))
  have hnear : |Real.sin R - Real.sin re| ≤ η * (c + η / 2) := sin_near R re (hre.trans hpi)
  have hsR : |Real.sin R| ≤ s + η := by
    have := Real.abs_sin_sub_sin_le R re
    have := abs_sub_abs_le_abs_sub (Real.sin R) (Real.sin re)
    linarith
  have h1 : |Y - Real.sin re| ≤ dS * (s + η) + (η * c + η ^ 2 / 2) := by
    calc |Y - Real.sin re| ≤ |Y - Real.sin R| + |Real.sin R - Real.sin re| := abs_sub_le _ _ _
      _ ≤ dS * |Real.sin R| + η * (c + η / 2) := add_le_add hY hnear
      _ ≤ dS * (s + η) + η * (c + η / 2) := by gcongr
      _ = _ := by ring
  have hηb : η ≤ 112 / 100 * w * s + 2 * E := by nlinarith
  have h5 : η * c ≤ w * s + 2 * E := by nlinarith [mul_le_mul_of_nonneg_right hη hc0]
  have h7 : η ^ 2 / 2 ≤ 448 / 1000 * w ^ 2 * s + 45 / 100 * E := by
    have ht2 : t ^ 2 ≤ 896 / 1000 * s := by nlinarith
    have hwt : w * t ≤ 1 / 10 := by nlinarith
    have hsq : η ^ 2 ≤ (w * t + 2 * E) ^ 2 := pow_le_pow_left₀ hη0 hη 2
    nlinarith [mul_le_mul_of_nonneg_left ht2 (sq_nonneg w), mul_nonneg hw ht0, mul_nonneg hE (mul_nonneg hw ht0)]
  have h8 : dS * η ≤ dS * (112 / 100 * w * s + 2 * E) := mul_le_mul_of_nonneg_left hηb hdS0
  have key : (1 + 2 * w) * (dS + (1 + 2 * w) * w) * s + 5 * E -
      (dS * s + dS * (112 / 100 * w * s + 2 * E) + (w * s + 2 * E) + (448 / 1000 * w ^ 2 * s + 45 / 100 * E)) =
      s * (88 / 100 * w * dS + 3552 / 1000 * w ^ 2 + 4 * w ^ 3) + E * (255 / 100 - 2 * dS) := by ring
  have hk : 0 ≤ s * (88 / 100 * w * dS + 3552 / 1000 * w ^ 2 + 4 * w ^ 3) + E * (255 / 100 - 2 * dS) :=
    add_nonneg (by positivity) (mul_nonneg hE (by linarith))
  nlinarith

/-- the move from `r` to `r_e` for the cosine: with `Y` within `δ_C cos R` of `cos R`, `|R - r_e| ≤ w|r_e| + 2E` and
`|r_e| ≤ r̄ ≤ 0.8`, `Y` is within `ε(δ_C + εw r̄ tan₊ r̄)cos r_e + 5E` of `cos r_e` -/
theorem cos_move {Y R re w E dC rb : ℝ} (hw : 0 ≤ w) (hw1 : w ≤ 1 / 8) (hE : 0 ≤ E) (hE1 : E ≤ 1 / 8) (hdC0 : 0 ≤ dC)
    (hdC : dC ≤ 1 / 2) (hre : |re| ≤ rb) (hrb : rb ≤ 8 / 10) (hY : |Y - Real.cos R| ≤ dC * Real.cos R)
    (hη : |R - re| ≤ w * |re| + 2 * E) :
    |Y - Real.cos re| ≤ (1 + 2 * w) * (dC + (1 + 2 * w) * w * (rb * tanHi rb)) * Real.cos re + 5 * E := by
  set η := |R - re| with hηd
  set s := |Real.sin re| with hsd
  set t := |re| with htd
  set c := Real.cos re with hcd
  set T := rb * tanHi rb with hTd
  have hη0 : 0 ≤ η := abs_nonneg _
  have hs0 : 0 ≤ s := abs_nonneg _
  have ht0 : 0 ≤ t := abs_nonneg _
  have hrb0 : 0 ≤ rb := ht0.trans hre
  have hT1 : T ≤ 1 := tanHi_le hrb0 hrb
  have hs1 : s ≤ 1 := Real.abs_sin_le_one _
  have hpi : 8 / 10 ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hre8 : |re| ≤ 8 / 10 := hre.trans hrb
  have hc0 : 0 ≤ c := Real.cos_nonneg_of_mem_Icc ⟨by linarith [(abs_le.mp (hre8.trans hpi)).1],
    (abs_le.mp (hre8.trans hpi)).2⟩
  have hts : t ≤ 112 / 100 * s := abs_le_sin re hre8
  have htsT : t * s ≤ T * c := abs_mul_sin_le re rb hre (hrb.trans (by norm_num))
  have hd : |Real.cos R - Real.cos re| ≤ η * (s + η / 2) := cos_near R re
  set d := |Real.cos R - Real.cos re| with hdd
  have hcR : Real.cos R ≤ c + d := by
    have := le_abs_self (Real.cos R - Real.cos re)
    linarith
  have h1 : |Y - Real.cos re| ≤ dC * c + (1 + dC) * d := by
    calc |Y - Real.cos re| ≤ |Y - Real.cos R| + d := abs_sub_le _ _ _
      _ ≤ dC * (c + d) + d := add_le_add ((hY.trans (mul_le_mul_of_nonneg_left hcR hdC0))) le_rfl
      _ = _ := by ring
  have h2 : η * s ≤ w * (T * c) + 2 * E := by
    calc η * s ≤ (w * t + 2 * E) * s := mul_le_mul_of_nonneg_right hη hs0
      _ = w * (t * s) + 2 * E * s := by ring
      _ ≤ w * (T * c) + 2 * E * 1 := add_le_add (mul_le_mul_of_nonneg_left htsT hw)
          (mul_le_mul_of_nonneg_left hs1 (by positivity))
      _ = _ := by ring
  have ht2 : t ^ 2 ≤ 112 / 100 * (T * c) := by
    calc t ^ 2 = t * t := by ring
      _ ≤ t * (112 / 100 * s) := mul_le_mul_of_nonneg_left hts ht0
      _ = 112 / 100 * (t * s) := by ring
      _ ≤ 112 / 100 * (T * c) := mul_le_mul_of_nonneg_left htsT (by norm_num)
  have hwt : w * t ≤ 1 / 10 := by
    calc w * t ≤ 1 / 8 * (8 / 10) := mul_le_mul hw1 (hre.trans hrb) ht0 (by norm_num)
      _ = 1 / 10 := by norm_num
  have h3 : η ^ 2 / 2 ≤ 56 / 100 * w ^ 2 * (T * c) + 45 / 100 * E := by
    have hsq : η ^ 2 ≤ (w * t + 2 * E) ^ 2 := pow_le_pow_left₀ hη0 hη 2
    have e1 : (w * t + 2 * E) ^ 2 = w ^ 2 * t ^ 2 + 4 * (w * t) * E + 4 * E * E := by ring
    have e2 : w ^ 2 * t ^ 2 ≤ w ^ 2 * (112 / 100 * (T * c)) := mul_le_mul_of_nonneg_left ht2 (sq_nonneg w)
    have e3 : 4 * (w * t) * E ≤ 4 * (1 / 10) * E := by
      have := mul_le_mul_of_nonneg_right hwt hE
      linarith
    have e4 : 4 * E * E ≤ 4 * (1 / 8) * E := by
      have := mul_le_mul_of_nonneg_left hE1 hE
      linarith
    linarith
  have hdb : d ≤ (w + 56 / 100 * w ^ 2) * (T * c) + 245 / 100 * E := by
    have : η * (s + η / 2) = η * s + η ^ 2 / 2 := by ring
    linarith
  have hTc : 0 ≤ T * c := (mul_nonneg ht0 hs0).trans htsT
  have h4 : (1 + dC) * d ≤ (1 + dC) * ((w + 56 / 100 * w ^ 2) * (T * c) + 245 / 100 * E) :=
    mul_le_mul_of_nonneg_left hdb (by linarith)
  have hT0 : 0 ≤ T := by
    have hcl := cosLo_pos hrb0 (hrb.trans (by norm_num))
    have hsh : 0 ≤ sinHi rb := by
      unfold sinHi
      have : rb ^ 2 ≤ 1 := by nlinarith
      nlinarith [pow_nonneg hrb0 3, pow_nonneg hrb0 5]
    exact mul_nonneg hrb0 (div_nonneg hsh hcl.le)
  have key : (1 + 2 * w) * (dC + (1 + 2 * w) * w * T) * c + 5 * E -
      (dC * c + (1 + dC) * ((w + 56 / 100 * w ^ 2) * (T * c) + 245 / 100 * E)) =
      w * dC * c * (2 - T - 56 / 100 * w * T) + w * (T * c) * (344 / 100 * w + 4 * w ^ 2) +
        E * (255 / 100 - 245 / 100 * dC) := by ring
  have h5 : 0 ≤ 2 - T - 56 / 100 * w * T := by
    have : w * T ≤ 1 / 8 * 1 := mul_le_mul hw1 hT1 hT0 (by norm_num)
    linarith
  have hk : 0 ≤ w * dC * c * (2 - T - 56 / 100 * w * T) + w * (T * c) * (344 / 100 * w + 4 * w ^ 2) +
      E * (255 / 100 - 245 / 100 * dC) :=
    add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hw hdC0) hc0) h5)
      (mul_nonneg (mul_nonneg hw hTc) (by positivity))) (mul_nonneg hE (by linarith))
  linarith

variable (p : ℤ) (n : ℕ)

/-- the quadrant's choice: `a`, `b`, `-a`, `-b` for `q = 0, 1, 2, 3` -/
noncomputable def quadSel (q : ℤ) (a b : ℕ → ℝ) : ℕ → ℝ :=
  if q % 4 = 0 then a else if q % 4 = 1 then b else if q % 4 = 2 then fun i => -a i else fun i => -b i

/-- SINR and COSR of RED's `r`, with the series lengths and SINR's scaling chosen from `|r_0|` -/
noncomputable def trigYs (es : ℝ → ℤ) (Ks : ℝ → ℕ) (Fs : ℕ → ℕ → ℝ) (x : ℕ → ℝ) : ℕ → ℝ :=
  sinRN p n (es |redR p n x 0|) (redR p n x) Fs (Ks |redR p n x 0|)

noncomputable def trigYc (Kc : ℝ → ℕ) (Fc : ℕ → ℕ → ℝ) (x : ℕ → ℝ) : ℕ → ℝ :=
  cosRN p n (redR p n x) Fc (Kc |redR p n x 0|)

/-- SIN_n: `x` below `|x_0| < u^{n/2}`, else `Y_s`, `Y_c`, `-Y_s`, `-Y_c` by the quadrant -/
noncomputable def sinN (es : ℝ → ℤ) (Ks Kc : ℝ → ℕ) (Fs Fc : ℕ → ℕ → ℝ) (x : ℕ → ℝ) : ℕ → ℝ :=
  if |x 0| < u p ^ (n / 2) then x
  else quadSel (redK p n x) (trigYs p n es Ks Fs x) (trigYc p n Kc Fc x)

/-- COS_n: `1` below `|x_0| < u^{n/2}`, else `Y_c`, `-Y_s`, `-Y_c`, `Y_s` by the quadrant -/
noncomputable def cosN (es : ℝ → ℤ) (Ks Kc : ℝ → ℕ) (Fs Fc : ℕ → ℕ → ℝ) (x : ℕ → ℝ) : ℕ → ℝ :=
  if |x 0| < u p ^ (n / 2) then fun i => if i = 0 then 1 else 0
  else quadSel (redK p n x + 1) (trigYs p n es Ks Fs x) (trigYc p n Kc Fc x)

/-- Lemma 34's `δ_S` for the run, with `r̄` in both branches -/
noncomputable def trigDS (r0 rb : ℝ) (Fs : ℕ → ℕ → ℝ) (K : ℕ) : ℝ :=
  if |r0| < u p ^ (n / 2) then rb ^ 2 / (6 - rb ^ 2) else sinDelta p n (abar (2 * u p)) rb Fs K

/-- Lemma 34's `δ_C` for the run -/
noncomputable def trigDC (r0 rb : ℝ) (Fc : ℕ → ℕ → ℝ) (K : ℕ) : ℝ :=
  if |r0| < u p ^ (n / 2) then rb ^ 2 / (2 * cosLo rb) else cosDelta p n (abar (2 * u p)) rb Fc K

/-- `C = ε max(δ_S + εu^n, δ_C + εu^n r̄ tan₊ r̄)`, `ε = 1 + 2u^n` -/
noncomputable def trigC (dS dC rb : ℝ) : ℝ :=
  (1 + 2 * u p ^ n) * max (dS + (1 + 2 * u p ^ n) * u p ^ n) (dC + (1 + 2 * u p ^ n) * u p ^ n * (rb * tanHi rb))

theorem sum_quadSel (q : ℤ) (a b : ℕ → ℝ) (N : ℕ) : ∑ i ∈ range N, quadSel q a b i =
    if q % 4 = 0 then ∑ i ∈ range N, a i else if q % 4 = 1 then ∑ i ∈ range N, b i
    else if q % 4 = 2 then -∑ i ∈ range N, a i else -∑ i ∈ range N, b i := by
  unfold quadSel
  split_ifs <;> simp [sum_neg_distrib]

/-- the quadrant step: if `a` is within `C|sin r_e| + E` of `sin r_e` and `b` within `C|cos r_e| + E` of `cos r_e`,
the quadrant's choice is within `C|sin x| + E` of `sin x` for `x = r_e + kπ/2` -/
theorem quad_bound {re A B C E : ℝ} (k : ℤ) (ha : |A - Real.sin re| ≤ C * |Real.sin re| + E)
    (hb : |B - Real.cos re| ≤ C * |Real.cos re| + E) :
    |(if k % 4 = 0 then A else if k % 4 = 1 then B else if k % 4 = 2 then -A else -B) -
        Real.sin (re + k * (Real.pi / 2))| ≤ C * |Real.sin (re + k * (Real.pi / 2))| + E := by
  rw [sin_add_quarter]
  split_ifs
  · exact ha
  · exact hb
  · rw [show -A - -Real.sin re = -(A - Real.sin re) by ring, abs_neg, abs_neg]; exact ha
  · rw [show -B - -Real.cos re = -(B - Real.cos re) by ring, abs_neg, abs_neg]; exact hb

variable [Prec_gt_0 p]

/-- Theorem 35 for SIN and COS (`thm:trig`), at `p = 53` beyond the early return, for `x` on `H(2)` with `|x_0| ≤ 2^52`
and `(n² + n)u < 1`: with RED's `r` and `r_e` within `r̄ ≤ 0.8`, Lemma 34's `δ_S, δ_C ∈ [0, 1/2]` and series of at least
two terms, `|SIN_n(x) - sin x| ≤ C|sin x| + 5E_π` and `|COS_n(x) - cos x| ≤ C|cos x| + 5E_π`,
`C = ε max(δ_S + εu^n, δ_C + εu^n r̄ tan₊ r̄)` and `ε = 1 + 2u^n` -/
theorem thm35_sincos (hp : p = 53) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1)
    (x : ℕ → ℝ) (hx : ∀ i < n, F p (x i)) (hH : Htheta p n 2 x) (hx0 : |x 0| ≤ 2 ^ 52)
    (hbig : ¬|x 0| < u p ^ (n / 2)) (es : ℝ → ℤ) (Ks Kc : ℝ → ℕ) (Fs Fc : ℕ → ℕ → ℝ)
    (hFs : ∀ k, ∀ i < n, F p (Fs k i)) (hFc : ∀ k, ∀ i < n, F p (Fc k i)) (hKs : 2 ≤ Ks |redR p n x 0|)
    (hKc : 2 ≤ Kc |redR p n x 0|) (rb : ℝ) (hrb : rb ≤ 8 / 10) (hr : |∑ i ∈ range n, redR p n x i| ≤ rb)
    (hre : |∑ i ∈ range n, x i - redK p n x * (Real.pi / 2)| ≤ rb)
    (hdS0 : 0 ≤ trigDS p n (redR p n x 0) rb Fs (Ks |redR p n x 0|))
    (hdS : trigDS p n (redR p n x 0) rb Fs (Ks |redR p n x 0|) ≤ 1 / 2)
    (hdC0 : 0 ≤ trigDC p n (redR p n x 0) rb Fc (Kc |redR p n x 0|))
    (hdC : trigDC p n (redR p n x 0) rb Fc (Kc |redR p n x 0|) ≤ 1 / 2) :
    |∑ i ∈ range n, sinN p n es Ks Kc Fs Fc x i - Real.sin (∑ i ∈ range n, x i)| ≤
        trigC p n (trigDS p n (redR p n x 0) rb Fs (Ks |redR p n x 0|))
          (trigDC p n (redR p n x 0) rb Fc (Kc |redR p n x 0|)) rb * |Real.sin (∑ i ∈ range n, x i)| +
          5 * (|(redK p n x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) ∧
      |∑ i ∈ range n, cosN p n es Ks Kc Fs Fc x i - Real.cos (∑ i ∈ range n, x i)| ≤
        trigC p n (trigDS p n (redR p n x 0) rb Fs (Ks |redR p n x 0|))
          (trigDC p n (redR p n x 0) rb Fc (Kc |redR p n x 0|)) rb * |Real.cos (∑ i ∈ range n, x i)| +
          5 * (|(redK p n x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) := by
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
  -- the parts of `r` within `ā_i|r|`
  have hρ : 2 * (2 * u p) < 1 := by rw [hu53]; norm_num
  have hab0 : ∀ i, 0 ≤ abar (2 * u p) i := fun i => by
    unfold abar; exact mul_nonneg (pow_nonneg (by positivity) i) (div_nonneg (by linarith) (by linarith))
  have hab : ∀ i < n, |r i| ≤ abar (2 * u p) i * |R| := fun i hi => by
    have h0 := Htheta_a0 p n hn 2 (by norm_num) hρ r hrH
    calc |r i| ≤ (2 * u p) ^ i * |r 0| := Htheta_le p n hrH i hi
      _ ≤ (2 * u p) ^ i * ((1 - 2 * u p) / (1 - 2 * (2 * u p)) * |R|) :=
          mul_le_mul_of_nonneg_left h0 (pow_nonneg (by positivity) i)
      _ = _ := by unfold abar; ring
  have hrb1 : rb ≤ 1 := by linarith
  -- Lemma 34
  obtain ⟨s1, -, -⟩ := lemma34_sin p n hp1 hn hA3 r hrF _ hab0 hab rb rb (fun _ => hr) hrb1 (fun _ => hr) hrb1 Fs
    hFs (Ks |r 0|) hKs (es |r 0|)
  obtain ⟨c1, -, -⟩ := lemma34_cos p n hp1 hn hA3 r hrF _ hab0 hab rb rb (fun _ => hr) hrb1 (fun _ => hr) hrb1 Fc
    hFc (Kc |r 0|) hKc
  -- `|R - r_e| ≤ u^n|r_e| + 2E_π`
  have husn : us p ^ n ≤ u p ^ n := pow_le_pow_left₀ (us_nonneg p) (us_le_u p) n
  have hη' : |R - re| ≤ u p ^ n * |re| + 2 * E := by
    have := mul_le_mul_of_nonneg_right husn (abs_nonneg re)
    linarith
  have hw1 : u p ^ n ≤ 1 / 8 := by
    calc u p ^ n ≤ u p ^ 1 := pow_le_pow_of_le_one hu.le (by rw [hu53]; norm_num) hn
      _ = u p := pow_one _
      _ ≤ 1 / 8 := by rw [hu53]; norm_num
  have hE1 : E ≤ 1 / 8 := by
    have h2 : (2 : ℝ) ^ (-1217 : ℤ) ≤ 1 / 2 ^ 60 := by
      rw [zpow_neg, ← one_div, one_div_le_one_div (by positivity) (by positivity)]
      exact_mod_cast pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : 60 ≤ 1217)
    calc E ≤ 64 / 100 * 2 ^ 52 * (1 / 2 ^ 60) := mul_le_mul hk.le h2 (by positivity) (by positivity)
      _ ≤ 1 / 8 := by norm_num
  have hE0 : 0 ≤ E := by positivity
  -- the moves to `r_e`
  have hsin := sin_move (pow_nonneg hu.le n) hw1 hE0 hE1 hdS0 hdS (hre.trans hrb) s1 hη'
  have hcos := cos_move (pow_nonneg hu.le n) hw1 hE0 hE1 hdC0 hdC hre hrb c1 hη'
  set Ys := ∑ i ∈ range n, trigYs p n es Ks Fs x i with hYs
  set Yc := ∑ i ∈ range n, trigYc p n Kc Fc x i with hYc
  set Cc := trigC p n dS dC rb with hCc
  have hpi : 8 / 10 ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hcpos : 0 ≤ Real.cos re := Real.cos_nonneg_of_mem_Icc ⟨by linarith [(abs_le.mp (hre.trans (hrb.trans hpi))).1],
    (abs_le.mp (hre.trans (hrb.trans hpi))).2⟩
  have hA : |Ys - Real.sin re| ≤ Cc * |Real.sin re| + 5 * E := by
    refine hsin.trans (add_le_add (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)) le_rfl)
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
  have hB : |Yc - Real.cos re| ≤ Cc * |Real.cos re| + 5 * E := by
    rw [abs_of_nonneg hcpos]
    refine hcos.trans (add_le_add (mul_le_mul_of_nonneg_right ?_ hcpos) le_rfl)
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
  have hXre : X = re + k * (Real.pi / 2) := by rw [hred]; ring
  have hXre1 : Real.cos X = Real.sin (re + ((k + 1 : ℤ) : ℝ) * (Real.pi / 2)) := by
    rw [hXre]; exact cos_add_quarter re k
  constructor
  · have h := quad_bound k hA hB
    rw [← hXre] at h
    have hs : ∑ i ∈ range n, sinN p n es Ks Kc Fs Fc x i =
        (if k % 4 = 0 then Ys else if k % 4 = 1 then Yc else if k % 4 = 2 then -Ys else -Yc) := by
      simp only [sinN, hbig, ite_false]
      exact sum_quadSel _ _ _ _
    rw [hs]
    exact h
  · have h := quad_bound (k + 1) hA hB
    rw [← hXre1] at h
    have hs : ∑ i ∈ range n, cosN p n es Ks Kc Fs Fc x i = (if (k + 1) % 4 = 0 then Ys else if (k + 1) % 4 = 1 then Yc
        else if (k + 1) % 4 = 2 then -Ys else -Yc) := by
      simp only [cosN, hbig, ite_false]
      exact sum_quadSel _ _ _ _
    rw [hs]
    exact h

omit [Prec_gt_0 p] in
/-- Theorem 35's early return, at `p = 53`, `n ≥ 2` and `|x_0| < u^{n/2}` on `H(2)`:
`|x| ≤ r̄_min = u^{n/2}(1 + 2^{-50})`, and `SIN_n(x) = x` and `COS_n(x) = 1` err by at most
`r̄_min²/(6 - r̄_min²)|sin x|` and `r̄_min²/(2cos₋ r̄_min) cos x` -/
theorem thm35_small (hp : p = 53) (hn : 2 ≤ n) (x : ℕ → ℝ) (hH : Htheta p n 2 x) (hsmall : |x 0| < u p ^ (n / 2))
    (es : ℝ → ℤ) (Ks Kc : ℝ → ℕ) (Fs Fc : ℕ → ℕ → ℝ) :
    |∑ i ∈ range n, x i| ≤ u p ^ (n / 2) * (1 + 1 / 2 ^ 50) ∧
      |∑ i ∈ range n, sinN p n es Ks Kc Fs Fc x i - Real.sin (∑ i ∈ range n, x i)| ≤
        (u p ^ (n / 2) * (1 + 1 / 2 ^ 50)) ^ 2 / (6 - (u p ^ (n / 2) * (1 + 1 / 2 ^ 50)) ^ 2) *
          |Real.sin (∑ i ∈ range n, x i)| ∧
      |∑ i ∈ range n, cosN p n es Ks Kc Fs Fc x i - Real.cos (∑ i ∈ range n, x i)| ≤
        (u p ^ (n / 2) * (1 + 1 / 2 ^ 50)) ^ 2 / (2 * cosLo (u p ^ (n / 2) * (1 + 1 / 2 ^ 50))) *
          Real.cos (∑ i ∈ range n, x i) := by
  have hu := u_pos p
  have hu53 : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num
  set rbm := u p ^ (n / 2) * (1 + 1 / 2 ^ 50) with hrbm
  have hun : u p ^ (n / 2) ≤ 1 := pow_le_one₀ hu.le (by rw [hu53]; norm_num)
  have htail := Htheta_tail p n (by omega) 2 (by norm_num) (by rw [hu53]; norm_num) x hH
  rw [hu53] at htail
  norm_num at htail
  have hX : |∑ i ∈ range n, x i| ≤ rbm := by
    have := abs_sub_abs_le_abs_sub (∑ i ∈ range n, x i) (x 0)
    have h0 : 0 ≤ u p ^ (n / 2) := pow_nonneg hu.le _
    rw [hrbm]
    nlinarith [abs_nonneg (x 0)]
  have hrbm1 : rbm ≤ 1 := by
    have : u p ^ (n / 2) ≤ u p ^ 1 := pow_le_pow_of_le_one hu.le (by rw [hu53]; norm_num) (by omega)
    rw [pow_one] at this
    rw [hrbm]
    linarith [hu53]
  refine ⟨hX, ?_, ?_⟩
  · have hs : ∑ i ∈ range n, sinN p n es Ks Kc Fs Fc x i = ∑ i ∈ range n, x i := by
      simp only [sinN, hsmall, ite_true]
    rw [hs]
    exact sinr_small _ rbm hX hrbm1
  · have hc : ∑ i ∈ range n, cosN p n es Ks Kc Fs Fc x i = 1 := by
      simp only [cosN, hsmall, ite_true]
      rw [sum_ite_eq']
      simp [show 0 < n by omega]
    rw [hc]
    exact cosr_small _ rbm hX hrbm1

end ExpansionBounds
