import ExpansionBounds.Log8.Cert
import ExpansionBounds.ExpRed8

/-!
# Theorem 42 at `n = 8` and `p = 53`: the arguments of the bound at a rational `ℓ`

The paper's arguments of `𝓔(ℓ)` at `n = 8`, as functions of a real `ℓ`: the start's bound `log8E`, `ȳ = ℓ + E(ℓ)`
(`log8Yb`), `π^y`, and for `k ≠ 0` Lemma 38's `r̄_max`, `α`, `δ*`, `δ` and `π^r` with multidouble's constants
(`log8DsR`, `log8DR`, `log8PR`). At a rational `ℓ` each is at most the rational that the kernel evaluates:
`log8Eq`, `log8PiY`, `log8RMax`, `log8Alpha`, `log8DeltaS`, `log8Delta`, `log8PiR` of `Log8/Defs.lean`.
-/

namespace ExpansionBounds

open Finset

/-- `E(ℓ) = e₀ + e₁ℓ` at `n = 8`, on the rational `e₀` and `e₁` of `Log8/Defs.lean` -/
noncomputable def log8E (l : ℝ) : ℝ := logE ((log8E0 : ℚ) : ℝ) ((log8E1 : ℚ) : ℝ) l

/-- `ȳ = ℓ + E(ℓ)` at `n = 8` -/
noncomputable def log8Yb (l : ℝ) : ℝ := logYb ((log8E0 : ℚ) : ℝ) ((log8E1 : ℚ) : ℝ) l

/-- `e₀` and `e₁` are nonnegative, which the kernel evaluates. -/
theorem log8E_consts : 0 ≤ log8E0 ∧ 0 ≤ log8E1 ∧ 0 ≤ cr8 := by decide +kernel

/-- `E(ℓ)` at a rational `ℓ` is at most `log8Eq`. -/
theorem log8E_le (l : ℚ) : log8E ((l : ℚ) : ℝ) ≤ ((log8Eq l : ℚ) : ℝ) := by
  have h : (((log8E0 + log8E1 * l : ℚ)) : ℝ) ≤ ((log8Eq l : ℚ) : ℝ) :=
    Rat.cast_le.mpr (le_upQ 200 (log8E0 + log8E1 * l))
  simp only [log8E, logE]
  push_cast at h
  exact h

/-- `E(ℓ) ≥ 0` for `ℓ ≥ 0`. -/
theorem log8E_nonneg {l : ℝ} (hl : 0 ≤ l) : 0 ≤ log8E l := by
  obtain ⟨h0, h1, -⟩ := log8E_consts
  have h0' : (0 : ℝ) ≤ ((log8E0 : ℚ) : ℝ) := by exact_mod_cast h0
  have h1' : (0 : ℝ) ≤ ((log8E1 : ℚ) : ℝ) := by exact_mod_cast h1
  simp only [log8E, logE]
  exact add_nonneg h0' (mul_nonneg h1' hl)

/-- `ȳ` at a rational `ℓ` is at most `ℓ + log8Eq ℓ`. -/
theorem log8Yb_le (l : ℚ) : log8Yb ((l : ℚ) : ℝ) ≤ (((l + log8Eq l : ℚ)) : ℝ) := by
  have h := log8E_le l
  simp only [log8E] at h
  simp only [log8Yb, logYb]
  push_cast
  linarith

/-- `ȳ ≥ 0` for `ℓ ≥ 0`. -/
theorem log8Yb_nonneg {l : ℝ} (hl : 0 ≤ l) : 0 ≤ log8Yb l := by
  have h := log8E_nonneg hl
  simp only [log8E] at h
  simp only [log8Yb, logYb]
  linarith

/-- `π^y` at a rational `ℓ` is at most `log8PiY`. -/
theorem log8PiY_le (l : ℚ) (i : ℕ) :
    logPiY 53 ((log8E0 : ℚ) : ℝ) ((log8E1 : ℚ) : ℝ) ((l : ℚ) : ℝ) i ≤ ((log8PiY l i : ℚ) : ℝ) := by
  have hu : ((red8U : ℚ) : ℝ) = u (53 : ℤ) := by unfold red8U; exact u_53_rat 53 rfl
  have hu53 : u (53 : ℤ) = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  have h1 : (0 : ℝ) ≤ 1 - u 53 := by rw [hu53]; norm_num
  have h2 : (0 : ℝ) < 1 - 2 * u 53 := by rw [hu53]; norm_num
  have hY := log8Yb_le l
  simp only [log8Yb] at hY
  have hq : logYb ((log8E0 : ℚ) : ℝ) ((log8E1 : ℚ) : ℝ) ((l : ℚ) : ℝ) * (1 - u 53) / (1 - 2 * u 53) ≤
      ((((l + log8Eq l) * (1 - red8U) / (1 - 2 * red8U) : ℚ)) : ℝ) := by
    push_cast at hY ⊢
    rw [hu]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hY h1) h2.le
  obtain rfl | rfl | h : i = 0 ∨ i = 1 ∨ 2 ≤ i := by omega
  · simp only [logPiY, ladderB, log8PiY, show (0 : ℕ) < 2 by norm_num, ↓reduceIte, pow_zero, one_mul]
    exact hq
  · simp only [logPiY, ladderB, log8PiY, show (1 : ℕ) < 2 by norm_num, one_ne_zero, ↓reduceIte, pow_one]
    rw [Rat.cast_mul, hu]
    exact mul_le_mul_of_nonneg_left hq (by rw [hu53]; norm_num)
  · simp only [logPiY, ladderB, log8PiY, show ¬i < 2 by omega, show i ≠ 0 by omega, show i ≠ 1 by omega,
      ↓reduceIte, Rat.cast_zero, le_refl]

variable [Prec_gt_0 (53 : ℤ)]

/-- The constants of Lemma 38 at `n = 8`: `c_r` within `red8Dl` of `1/ln 2`, `c_h` and `c_h + ∑ c_ℓ` within
their bounds of `ln 2`, and `ε_1` and `μ` equal to their mirrors -/
theorem log8_red_consts : |cR 53 - 1 / Real.log 2| ≤ ((red8Dl : ℚ) : ℝ) ∧
    |Real.log 2 - ((ch8 : ℚ) : ℝ)| ≤ ((max |ch8 - ln2A| |ch8 - ln2B| : ℚ) : ℝ) ∧
    etaL 8 ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)) ≤ ((red8Eta : ℚ) : ℝ) ∧
    redE1 53 8 (fun i => ((cl8 i : ℚ) : ℝ)) = ((red8E1 : ℚ) : ℝ) ∧
    redMu 53 8 (fun i => ((cl8 i : ℚ) : ℝ)) = fun i => ((red8Mu i : ℚ) : ℝ) := by
  have hu : ((red8U : ℚ) : ℝ) = u (53 : ℤ) := by unfold red8U; exact u_53_rat 53 rfl
  obtain ⟨lA, lB⟩ := log_two_600
  obtain ⟨kA, -, -, -⟩ := red8_check
  have hApos : (0 : ℝ) < ((ln2A : ℚ) : ℝ) := by exact_mod_cast kA
  have hL0 : 0 < Real.log 2 := lt_of_lt_of_le hApos lA
  have hinv1 : 1 / ((ln2B : ℚ) : ℝ) ≤ 1 / Real.log 2 := one_div_le_one_div_of_le hL0 lB
  have hinv2 : 1 / Real.log 2 ≤ 1 / ((ln2A : ℚ) : ℝ) := one_div_le_one_div_of_le hApos lA
  have hDl : |cR 53 - 1 / Real.log 2| ≤ ((red8Dl : ℚ) : ℝ) := by
    rw [cR_eq 53 rfl]
    have h := abs_sub_le_max (c := ((cr8 : ℚ) : ℝ)) hinv1 hinv2
    simpa [red8Dl] using h
  have hDe : |Real.log 2 - ((ch8 : ℚ) : ℝ)| ≤ ((max |ch8 - ln2A| |ch8 - ln2B| : ℚ) : ℝ) := by
    rw [abs_sub_comm]
    have h := abs_sub_le_max (c := ((ch8 : ℚ) : ℝ)) lA lB
    simpa using h
  have hEta : etaL 8 ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)) ≤ ((red8Eta : ℚ) : ℝ) := by
    unfold etaL
    rw [show Real.log 2 - ((ch8 : ℚ) : ℝ) - ∑ i ∈ range 8, ((cl8 i : ℚ) : ℝ) =
      -((((ch8 : ℚ) : ℝ) + ∑ i ∈ range 8, ((cl8 i : ℚ) : ℝ)) - Real.log 2) by ring, abs_neg]
    have h := abs_sub_le_max (c := ((ch8 : ℚ) : ℝ) + ∑ i ∈ range 8, ((cl8 i : ℚ) : ℝ)) lA lB
    simpa [red8Eta] using h
  have hcabs : (fun i => ((|cl8 i| : ℚ) : ℝ)) = fun i => |((cl8 i : ℚ) : ℝ)| := by
    funext i
    simp
  have hZc : ((1075 * |∑ i ∈ range 8, cl8 i| : ℚ) : ℝ) = 1075 * |∑ i ∈ range 8, ((cl8 i : ℚ) : ℝ)| := by simp
  refine ⟨hDl, hDe, hEta, ?_, ?_⟩
  · unfold redE1 red8E1
    rw [cast_GmulfE 53 8 hu, hcabs, hZc]
    simp
  · funext i
    unfold redMu red8Mu
    rw [cast_GmulfP 53 8 hu, hcabs, hZc]
    simp

/-- `r̄_max` at a rational `ℓ ≥ 0`, with `X = ȳ/(1 - u)` and `x̄_t = 2uȳ`, is at most `log8RMax`. -/
theorem log8RMax_le (l : ℚ) (hl : 0 ≤ l) :
    rMax 53 (log8Yb ((l : ℚ) : ℝ) / (1 - u 53)) (2 * u 53 * log8Yb ((l : ℚ) : ℝ)) ≤ ((log8RMax l : ℚ) : ℝ) := by
  have hu : ((red8U : ℚ) : ℝ) = u (53 : ℤ) := by unfold red8U; exact u_53_rat 53 rfl
  have hu53 : u (53 : ℤ) = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  have h1 : (0 : ℝ) < 1 - u 53 := by rw [hu53]; norm_num
  have hu0 : (0 : ℝ) ≤ u 53 := by rw [hu53]; norm_num
  obtain ⟨hDl, -, -, -, -⟩ := log8_red_consts
  obtain ⟨-, lB⟩ := log_two_600
  have hL0 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  obtain ⟨-, -, hcr⟩ := log8E_consts
  have hcr0 : (0 : ℝ) ≤ ((cr8 : ℚ) : ℝ) := by exact_mod_cast hcr
  have hl' : (0 : ℝ) ≤ ((l : ℚ) : ℝ) := by exact_mod_cast hl
  have hY := log8Yb_le l
  have hY0 := log8Yb_nonneg hl'
  have hX : log8Yb ((l : ℚ) : ℝ) / (1 - u 53) ≤ (((l + log8Eq l : ℚ)) : ℝ) / (1 - u 53) :=
    div_le_div_of_nonneg_right hY h1.le
  have hX0 : 0 ≤ log8Yb ((l : ℚ) : ℝ) / (1 - u 53) := div_nonneg hY0 h1.le
  have hc0 : 0 ≤ |cR 53 - 1 / Real.log 2| + u 53 * cR 53 := by
    rw [cR_eq 53 rfl]
    exact add_nonneg (abs_nonneg _) (mul_nonneg hu0 hcr0)
  have hE : epsK 53 (log8Yb ((l : ℚ) : ℝ) / (1 - u 53)) ≤
      (((l + log8Eq l : ℚ)) : ℝ) / (1 - u 53) * (((red8Dl : ℚ) : ℝ) + u 53 * ((cr8 : ℚ) : ℝ)) := by
    unfold epsK
    refine mul_le_mul hX ?_ hc0 (hX0.trans hX)
    rw [cR_eq 53 rfl] at hDl ⊢
    linarith
  have hE0 : 0 ≤ epsK 53 (log8Yb ((l : ℚ) : ℝ) / (1 - u 53)) := mul_nonneg hX0 hc0
  have hm := mul_le_mul (add_le_add (le_refl (1 / 2 : ℝ)) hE) lB hL0 (by linarith)
  have hx := mul_le_mul_of_nonneg_left hY (by linarith : (0 : ℝ) ≤ 2 * u 53)
  have hc : ((log8RMax l : ℚ) : ℝ) = (1 / 2 + (((l + log8Eq l : ℚ)) : ℝ) / (1 - u 53) *
      (((red8Dl : ℚ) : ℝ) + u 53 * ((cr8 : ℚ) : ℝ))) * ((ln2B : ℚ) : ℝ) +
      2 * u 53 * (((l + log8Eq l : ℚ)) : ℝ) := by
    simp only [log8RMax]
    push_cast
    rw [hu]
  rw [hc]
  unfold rMax
  linarith

/-- Lemma 38's `α` at a rational `ℓ ≥ 0` is at most `log8Alpha`. -/
theorem log8Alpha_le (l : ℚ) (hl : 0 ≤ l) (i : ℕ) :
    logAlpha 53 ((ch8 : ℚ) : ℝ) ((log8E0 : ℚ) : ℝ) ((log8E1 : ℚ) : ℝ) ((l : ℚ) : ℝ) i ≤
      ((log8Alpha l i : ℚ) : ℝ) := by
  have hu : ((red8U : ℚ) : ℝ) = u (53 : ℤ) := by unfold red8U; exact u_53_rat 53 rfl
  have hu53 : u (53 : ℤ) = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  by_cases hi : i = 0
  · subst hi
    obtain ⟨-, hDe, -, -, -⟩ := log8_red_consts
    have hR := log8RMax_le l hl
    have hY := log8Yb_le l
    have hx := mul_le_mul_of_nonneg_left hY (by rw [hu53]; norm_num : (0 : ℝ) ≤ 2 * u 53)
    simp only [log8Yb] at hR hx
    simp only [logAlpha, log8Alpha, ↓reduceIte, expA0]
    push_cast at hx hDe ⊢
    rw [hu]
    linarith
  · simp only [logAlpha, log8Alpha, hi, ↓reduceIte]
    exact log8PiY_le l i

/-- `δ*` of Lemma 38 (b) for the reduction of `-y_0`, at `r̄ = r̄_max`, with VecSum's second bound alone -/
noncomputable def log8DsR (l : ℝ) : ℝ :=
  redDeltaC 53 8 (redE1 53 8 fun i => ((cl8 i : ℚ) : ℝ)) (1075 * etaL 8 ((ch8 : ℚ) : ℝ) fun i => ((cl8 i : ℚ) : ℝ))
    (logAlpha 53 ((ch8 : ℚ) : ℝ) ((log8E0 : ℚ) : ℝ) ((log8E1 : ℚ) : ℝ) l) (redMu 53 8 fun i => ((cl8 i : ℚ) : ℝ))
    (rMax 53 (log8Yb l / (1 - u 53)) (2 * u 53 * log8Yb l))

/-- `δ` of Lemma 38 (b) at `r̄ = b + δ*` -/
noncomputable def log8DR (b l : ℝ) : ℝ :=
  redDeltaC 53 8 (redE1 53 8 fun i => ((cl8 i : ℚ) : ℝ)) (1075 * etaL 8 ((ch8 : ℚ) : ℝ) fun i => ((cl8 i : ℚ) : ℝ))
    (logAlpha 53 ((ch8 : ℚ) : ℝ) ((log8E0 : ℚ) : ℝ) ((log8E1 : ℚ) : ℝ) l) (redMu 53 8 fun i => ((cl8 i : ℚ) : ℝ))
    (b + log8DsR l)

/-- `π^r` of Lemma 38 (b) at `r̄ = b + δ*` -/
noncomputable def log8PR (b l : ℝ) (i : ℕ) : ℝ :=
  redPiC 53 8 (redE1 53 8 fun i => ((cl8 i : ℚ) : ℝ)) (1075 * etaL 8 ((ch8 : ℚ) : ℝ) fun i => ((cl8 i : ℚ) : ℝ))
    (logAlpha 53 ((ch8 : ℚ) : ℝ) ((log8E0 : ℚ) : ℝ) ((log8E1 : ℚ) : ℝ) l) (redMu 53 8 fun i => ((cl8 i : ℚ) : ℝ))
    (b + log8DsR l) i

/-- `G_ADD(α, μ; r̄ + k̄η_ℓ + ε_1)` of the reduction at a rational `ℓ ≥ 0` and a bound `r̄_q` of `r̄` is at most its
mirror, the error bound and each part bound -/
theorem log8_red_le (l : ℚ) (hl : 0 ≤ l) {rb : ℝ} {rq : ℚ} (hr : rb ≤ ((rq : ℚ) : ℝ)) :
    GaddEC 53 8 (logAlpha 53 ((ch8 : ℚ) : ℝ) ((log8E0 : ℚ) : ℝ) ((log8E1 : ℚ) : ℝ) ((l : ℚ) : ℝ))
        (redMu 53 8 fun i => ((cl8 i : ℚ) : ℝ))
        (rb + 1075 * etaL 8 ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)) +
          redE1 53 8 fun i => ((cl8 i : ℚ) : ℝ)) ≤
        ((GaddECQ red8U 8 (log8Alpha l) red8Mu (rq + 1075 * red8Eta + red8E1) : ℚ) : ℝ) ∧
      ∀ i, GaddPC 53 8 (logAlpha 53 ((ch8 : ℚ) : ℝ) ((log8E0 : ℚ) : ℝ) ((log8E1 : ℚ) : ℝ) ((l : ℚ) : ℝ))
        (redMu 53 8 fun i => ((cl8 i : ℚ) : ℝ))
        (rb + 1075 * etaL 8 ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)) +
          redE1 53 8 fun i => ((cl8 i : ℚ) : ℝ)) i ≤
        ((GaddPCQ red8U 8 (log8Alpha l) red8Mu (rq + 1075 * red8Eta + red8E1) i : ℚ) : ℝ) := by
  have hu : ((red8U : ℚ) : ℝ) = u (53 : ℤ) := by unfold red8U; exact u_53_rat 53 rfl
  have hu53 : u (53 : ℤ) = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  have hA3 : (((8 : ℕ) : ℝ) ^ 2 + (8 : ℕ)) * u (53 : ℤ) < 1 := by rw [hu53]; norm_num
  obtain ⟨-, -, hEta, hE1, hMu⟩ := log8_red_consts
  have hZ : rb + 1075 * etaL 8 ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)) +
      redE1 53 8 (fun i => ((cl8 i : ℚ) : ℝ)) ≤ (((rq + 1075 * red8Eta + red8E1 : ℚ)) : ℝ) := by
    rw [hE1]
    push_cast
    linarith
  obtain ⟨g1, g2⟩ := GaddC_mono 53 8 hA3 (fun i => log8Alpha_le l hl i)
    (fun j => le_refl (redMu 53 8 (fun i => ((cl8 i : ℚ) : ℝ)) j)) hZ
  rw [cast_GaddEC 53 8 hu, ← hMu]
  exact ⟨g1, fun i => by rw [cast_GaddPC 53 8 hu, ← hMu]; exact g2 i⟩

/-- `δ*` at a rational `ℓ ≥ 0` is at most `log8DeltaS`. -/
theorem log8DsR_le (l : ℚ) (hl : 0 ≤ l) : log8DsR ((l : ℚ) : ℝ) ≤ ((log8DeltaS l : ℚ) : ℝ) := by
  obtain ⟨-, -, hEta, hE1, -⟩ := log8_red_consts
  obtain ⟨g1, -⟩ := log8_red_le l hl (log8RMax_le l hl)
  simp only [log8DsR, redDeltaC, log8DeltaS]
  refine le_trans ?_ (Rat.cast_le.mpr (le_upQ 200 _))
  rw [hE1] at g1 ⊢
  push_cast
  linarith

/-- `δ` at a rational `ℓ ≥ 0` and `b ≤ b_q` is at most `log8Delta`. -/
theorem log8DR_le (l : ℚ) (hl : 0 ≤ l) {br : ℝ} {b : ℚ} (hb : br ≤ ((b : ℚ) : ℝ)) :
    log8DR br ((l : ℚ) : ℝ) ≤ ((log8Delta l b : ℚ) : ℝ) := by
  obtain ⟨-, -, hEta, hE1, -⟩ := log8_red_consts
  have hr : br + log8DsR ((l : ℚ) : ℝ) ≤ (((b + log8DeltaS l : ℚ)) : ℝ) := by
    push_cast
    linarith [log8DsR_le l hl]
  obtain ⟨g1, -⟩ := log8_red_le l hl hr
  simp only [log8DR, redDeltaC, log8Delta]
  refine le_trans ?_ (Rat.cast_le.mpr (le_upQ 200 _))
  rw [hE1] at g1 ⊢
  push_cast
  linarith

/-- `π^r` at a rational `ℓ ≥ 0` and `b ≤ b_q` is at most `log8PiR`. -/
theorem log8PR_le (l : ℚ) (hl : 0 ≤ l) {br : ℝ} {b : ℚ} (hb : br ≤ ((b : ℚ) : ℝ)) (i : ℕ) :
    log8PR br ((l : ℚ) : ℝ) i ≤ ((log8PiR l b i : ℚ) : ℝ) := by
  have hr : br + log8DsR ((l : ℚ) : ℝ) ≤ (((b + log8DeltaS l : ℚ)) : ℝ) := by
    push_cast
    linarith [log8DsR_le l hl]
  obtain ⟨-, g2⟩ := log8_red_le l hl hr
  simp only [log8PR, redPiC, log8PiR]
  exact (g2 i).trans (Rat.cast_le.mpr (le_upQ 200 _))

end ExpansionBounds
