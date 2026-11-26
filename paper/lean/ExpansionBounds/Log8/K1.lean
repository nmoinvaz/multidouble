import ExpansionBounds.Log8.K0

/-!
# Theorem 42 at `n = 8` and `p = 53`: the reduction of `-y_0` for `k ≠ 0`

Lemma 38 (`lem:expred`) applied to `-y_0`, a two-part expansion with `|y_0| ≤ ȳ = ℓ + E(ℓ)`: `X = ȳ/(1 - u)`,
`x̄_t = 2uȳ`, `α_0` of the lemma and `α_i = π^y_i`. With `δ*` its `δ` at `r̄ = r̄_max` and `|r| ≤ b`, the run's `r`
is within `δ` of `r_e` and its parts within `π^r`, both at `r̄ = b + δ*` (`log8_red_run`); these are the functions
`log8DR` and `log8PR` of `ℓ = |ln x|` that the kernel's checks bound at the ends of an interval, and `log8_k1` is
`log8_chord_case` for them.
-/

namespace ExpansionBounds

open Finset Set

variable [Prec_gt_0 (53 : ℤ)]

/-- Lemma 38's hypotheses for `-y_0`, a two-part start within `E(ℓ)` of `L = ln x` with `ℓ = |L|` at most a rational
`ℓ₂` where the lemma applies (`X ≤ 745.3` and `α_0 < 1/2`, on their mirrors): `|y_{0,0}| ≤ X = ȳ/(1 - u)`,
`X ≤ 745.3`, `|y_0 - y_{0,0}| ≤ x̄_t = 2uȳ` and `α_0 < 1/2` at `ℓ` -/
theorem log8_red_hyp (y0 : ℕ → ℝ) (hy1 : |y0 1| ≤ u 53 * |y0 0|) (hy2 : ∀ i, 2 ≤ i → y0 i = 0) {L : ℝ}
    (hE : |∑ i ∈ range 8, y0 i - L| ≤ log8E |L|) {l₂ : ℚ} (hL : |L| ≤ ((l₂ : ℚ) : ℝ))
    (hX1 : (l₂ + log8Eq l₂) / (1 - red8U) ≤ 7453 / 10) (hA0 : log8Alpha l₂ 0 < 1 / 2) :
    |(fun i => -y0 i) 0| ≤ log8Yb |L| / (1 - u 53) ∧ log8Yb |L| / (1 - u 53) ≤ 745.3 ∧
      |∑ i ∈ range 8, (fun i => -y0 i) i - (fun i => -y0 i) 0| ≤ 2 * u 53 * log8Yb |L| ∧
      expA0 53 (log8Yb |L| / (1 - u 53)) (2 * u 53 * log8Yb |L|) ((ch8 : ℚ) : ℝ) < 1 / 2 := by
  have hu : ((red8U : ℚ) : ℝ) = u (53 : ℤ) := by unfold red8U; exact u_53_rat 53 rfl
  have hu53 : u (53 : ℤ) = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  have h1u : (0 : ℝ) < 1 - u 53 := by rw [hu53]; norm_num
  have hu0 : (0 : ℝ) ≤ u 53 := by rw [hu53]; norm_num
  obtain ⟨he0, he1, hcr⟩ := log8E_consts
  have he0' : (0 : ℝ) ≤ ((log8E0 : ℚ) : ℝ) := by exact_mod_cast he0
  have he1' : (0 : ℝ) ≤ ((log8E1 : ℚ) : ℝ) := by exact_mod_cast he1
  have hcR : 0 ≤ cR 53 := by
    rw [cR_eq 53 rfl]
    exact_mod_cast hcr
  obtain ⟨hY, hπy⟩ := log8_start_parts y0 hy1 hy2 hE
  have hl0 : (0 : ℝ) ≤ |L| := abs_nonneg L
  have hYb0 : 0 ≤ log8Yb |L| := (abs_nonneg _).trans hY
  -- the leading part and the tail of `-y_0`
  have hsum : ∑ i ∈ range 8, y0 i = y0 0 + y0 1 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hy2 2 le_rfl, hy2 3 (by norm_num),
      hy2 4 (by norm_num), hy2 5 (by norm_num), hy2 6 (by norm_num), hy2 7 (by norm_num)]
    ring
  have h0 : |y0 0| * (1 - u 53) ≤ log8Yb |L| := by
    have h2 : |y0 0| - |y0 1| ≤ |y0 0 + y0 1| := by
      have := abs_sub_abs_le_abs_sub (y0 0) (-y0 1)
      rwa [abs_neg, sub_neg_eq_add] at this
    rw [hsum] at hY
    linarith
  have hX : |(fun i => -y0 i) 0| ≤ log8Yb |L| / (1 - u 53) := by
    rw [abs_neg]
    exact (le_div_iff₀ h1u).mpr h0
  have hnsum : ∑ i ∈ range 8, (fun i => -y0 i) i = -∑ i ∈ range 8, y0 i := by
    simp only [Finset.sum_neg_distrib]
  have hxt : |∑ i ∈ range 8, (fun i => -y0 i) i - (fun i => -y0 i) 0| ≤ 2 * u 53 * log8Yb |L| := by
    rw [hnsum, hsum]
    have e : -(y0 0 + y0 1) - -y0 0 = -y0 1 := by ring
    rw [e, abs_neg]
    have h3 : |y0 0| ≤ 2 * log8Yb |L| := by
      have : (1 : ℝ) / 2 ≤ 1 - u 53 := by rw [hu53]; norm_num
      nlinarith [abs_nonneg (y0 0)]
    calc |y0 1| ≤ u 53 * |y0 0| := hy1
      _ ≤ u 53 * (2 * log8Yb |L|) := mul_le_mul_of_nonneg_left h3 hu0
      _ = 2 * u 53 * log8Yb |L| := by ring
  -- Lemma 38 applies up to `ℓ₂`
  have hs : Convex ℝ (Icc (0 : ℝ) ((l₂ : ℚ) : ℝ)) := convex_Icc _ _
  have hpos : ∀ l ∈ Icc (0 : ℝ) ((l₂ : ℚ) : ℝ), 0 ≤ l := fun l h => h.1
  have hl₂0 : (0 : ℝ) ≤ ((l₂ : ℚ) : ℝ) := hl0.trans hL
  have hl₂q : (0 : ℚ) ≤ l₂ := by exact_mod_cast hl₂0
  have mL : |L| ∈ Icc (0 : ℝ) ((l₂ : ℚ) : ℝ) := ⟨hl0, hL⟩
  have m2 : ((l₂ : ℚ) : ℝ) ∈ Icc (0 : ℝ) ((l₂ : ℚ) : ℝ) := ⟨hl₂0, le_rfl⟩
  have hYmono : log8Yb |L| ≤ (((l₂ + log8Eq l₂ : ℚ)) : ℝ) :=
    ((logYb_cvx hs hpos he0' he1').mono mL m2 hL).trans (log8Yb_le l₂)
  have hX1' : log8Yb |L| / (1 - u 53) ≤ 745.3 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hX1
    push_cast at h
    rw [hu] at h
    have := div_le_div_of_nonneg_right hYmono h1u.le
    push_cast at this
    norm_num at h ⊢
    linarith
  have hA0' : expA0 53 (log8Yb |L| / (1 - u 53)) (2 * u 53 * log8Yb |L|) ((ch8 : ℚ) : ℝ) < 1 / 2 := by
    have h1 := (logAlpha_cvx 53 hs hpos (by rw [hu53]; norm_num) hcR ((ch8 : ℚ) : ℝ) he0' he1' 0).mono mL m2 hL
    have h2 := log8Alpha_le l₂ hl₂q 0
    have h3 := (Rat.cast_lt (K := ℝ)).mpr hA0
    push_cast at h3
    simp only [logAlpha, ↓reduceIte] at h1 h2
    simp only [log8Yb]
    linarith
  exact ⟨hX, hX1', hxt, hA0'⟩

/-- Lemma 38 (`lem:expred`) for the reduction of `-y_0` at `n = 8` and `k ≠ 0`, for a two-part start within `E(ℓ)`
of `L = ln x`, `ℓ = |L|` at most a rational `ℓ₂` where the lemma applies: `|k| ≤ 1075`, `-y_{0,0} - k c_h ∈ F`,
`|r_e| ≤ r̄_max`, and for `|r_e| ≤ r̄`, `|r - r_e| ≤ δ` and `|r_i| ≤ π^r_i`, with VecSum's second bound alone -/
theorem log8_red_b (y0 : ℕ → ℝ) (hy0 : ∀ i < 8, F 53 (y0 i)) (hy1 : |y0 1| ≤ u 53 * |y0 0|)
    (hy2 : ∀ i, 2 ≤ i → y0 i = 0) {L : ℝ} (hE : |∑ i ∈ range 8, y0 i - L| ≤ log8E |L|) {l₂ : ℚ}
    (hL : |L| ≤ ((l₂ : ℚ) : ℝ)) (hX1 : (l₂ + log8Eq l₂) / (1 - red8U) ≤ 7453 / 10) (hA0 : log8Alpha l₂ 0 < 1 / 2)
    (hk : expK 53 (-y0 0) ≠ 0) :
    |expK 53 (-y0 0)| ≤ 1075 ∧ F 53 (-y0 0 - expK 53 (-y0 0) * ((ch8 : ℚ) : ℝ)) ∧
      |-∑ i ∈ range 8, y0 i - expK 53 (-y0 0) * Real.log 2| ≤
        rMax 53 (log8Yb |L| / (1 - u 53)) (2 * u 53 * log8Yb |L|) ∧
      ∀ rb : ℝ, |-∑ i ∈ range 8, y0 i - expK 53 (-y0 0) * Real.log 2| ≤ rb →
        |∑ i ∈ range 8, expR 53 8 (fun i => -y0 i) ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)) i -
            (-∑ i ∈ range 8, y0 i - expK 53 (-y0 0) * Real.log 2)| ≤
          redDeltaC 53 8 (redE1 53 8 fun i => ((cl8 i : ℚ) : ℝ))
            (1075 * etaL 8 ((ch8 : ℚ) : ℝ) fun i => ((cl8 i : ℚ) : ℝ))
            (logAlpha 53 ((ch8 : ℚ) : ℝ) ((log8E0 : ℚ) : ℝ) ((log8E1 : ℚ) : ℝ) |L|)
            (redMu 53 8 fun i => ((cl8 i : ℚ) : ℝ)) rb ∧
        ∀ i, |expR 53 8 (fun i => -y0 i) ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)) i| ≤
          redPiC 53 8 (redE1 53 8 fun i => ((cl8 i : ℚ) : ℝ))
            (1075 * etaL 8 ((ch8 : ℚ) : ℝ) fun i => ((cl8 i : ℚ) : ℝ))
            (logAlpha 53 ((ch8 : ℚ) : ℝ) ((log8E0 : ℚ) : ℝ) ((log8E1 : ℚ) : ℝ) |L|)
            (redMu 53 8 fun i => ((cl8 i : ℚ) : ℝ)) rb i := by
  have hu : ((red8U : ℚ) : ℝ) = u (53 : ℤ) := by unfold red8U; exact u_53_rat 53 rfl
  have hu53 : u (53 : ℤ) = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  have hA3 : (((8 : ℕ) : ℝ) ^ 2 + (8 : ℕ)) * u (53 : ℤ) < 1 := by rw [hu53]; norm_num
  obtain ⟨-, hπy⟩ := log8_start_parts y0 hy1 hy2 hE
  obtain ⟨hX, hX1', hxt, hA0'⟩ := log8_red_hyp y0 hy1 hy2 hE hL hX1 hA0
  have hnsum : ∑ i ∈ range 8, (fun i => -y0 i) i = -∑ i ∈ range 8, y0 i := by
    simp only [Finset.sum_neg_distrib]
  have hx' : ∀ i < 8, F 53 ((fun i => -y0 i) i) := fun i hi => F_neg 53 (hy0 i hi)
  obtain ⟨a1, a2, -, a4⟩ := lemma_expred_a 53 8 (by norm_num) (fun i => -y0 i) (hx' 0 (by norm_num)) _ _ _ hX hX1'
    hxt (ch8_mult 53 rfl) hA0'
  have hα0 : expA0 53 (log8Yb |L| / (1 - u 53)) (2 * u 53 * log8Yb |L|) ((ch8 : ℚ) : ℝ) ≤
      logAlpha 53 ((ch8 : ℚ) : ℝ) ((log8E0 : ℚ) : ℝ) ((log8E1 : ℚ) : ℝ) |L| 0 := by
    simp only [logAlpha, ↓reduceIte, log8Yb, le_refl]
  have hαi : ∀ i, 1 ≤ i → i < 8 → |(fun i => -y0 i) i| ≤
      logAlpha 53 ((ch8 : ℚ) : ℝ) ((log8E0 : ℚ) : ℝ) ((log8E1 : ℚ) : ℝ) |L| i := fun i h1 h8 => by
    simp only [logAlpha, show i ≠ 0 by omega, ↓reduceIte, abs_neg]
    exact hπy i h8
  have hlem := fun (rb : ℝ) hrb => lemma_expred_b 53 8 (by norm_num) (by norm_num) hA3 (fun i => -y0 i) hx' _ _ _
    (fun i => ((cl8 i : ℚ) : ℝ)) _ hX hX1' hxt (ch8_mult 53 rfl) (fun i _ => cl8_F 53 rfl i) hA0' hα0 hαi hk rb hrb
  rw [hnsum] at a2 hlem
  exact ⟨a1, a4 hk, a2, fun rb hrb => ⟨(hlem rb hrb).1.trans (red_le_redDeltaC 53 8 _ _ _ _), fun i =>
    ((hlem rb hrb).2 i).trans (red_le_redPiC 53 8 _ _ _ _ i)⟩⟩

/-- The reduction of `-y_0` at `n = 8` for `k ≠ 0`: for a two-part start within `E(ℓ)` of `L = ln x`, `ℓ = |L|`
at most a rational `ℓ₂` where Lemma 38 applies (`X ≤ 745.3` and `α_0 < 1/2`), and `|r| ≤ b`: `|r - r_e| ≤ δ` and
`|r_i| ≤ π^r_i` at `r̄ = b + δ*`, with VecSum's second bound alone -/
theorem log8_red_run (y0 : ℕ → ℝ) (hy0 : ∀ i < 8, F 53 (y0 i)) (hy1 : |y0 1| ≤ u 53 * |y0 0|)
    (hy2 : ∀ i, 2 ≤ i → y0 i = 0) {L : ℝ} (hE : |∑ i ∈ range 8, y0 i - L| ≤ log8E |L|) {l₂ : ℚ}
    (hL : |L| ≤ ((l₂ : ℚ) : ℝ)) (hX1 : (l₂ + log8Eq l₂) / (1 - red8U) ≤ 7453 / 10) (hA0 : log8Alpha l₂ 0 < 1 / 2)
    (hk : expK 53 (-y0 0) ≠ 0) {b : ℝ}
    (hb : |∑ i ∈ range 8, expR 53 8 (fun i => -y0 i) ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)) i| ≤ b) :
    |∑ i ∈ range 8, expR 53 8 (fun i => -y0 i) ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)) i -
        (-∑ i ∈ range 8, y0 i - expK 53 (-y0 0) * Real.log 2)| ≤ log8DR b |L| ∧
      ∀ i, |expR 53 8 (fun i => -y0 i) ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)) i| ≤ log8PR b |L| i := by
  obtain ⟨-, -, a2, hlem⟩ := log8_red_b y0 hy0 hy1 hy2 hE hL hX1 hA0 hk
  -- `δ*`, then `r̄ = b + δ*`
  have hds : _ ≤ log8DsR |L| := (hlem _ a2).1
  have hre : |-∑ i ∈ range 8, y0 i - expK 53 (-y0 0) * Real.log 2| ≤ b + log8DsR |L| := by
    have h := abs_sub_le_add
      (∑ i ∈ range 8, expR 53 8 (fun i => -y0 i) ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)) i)
      (∑ i ∈ range 8, expR 53 8 (fun i => -y0 i) ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)) i -
        (-∑ i ∈ range 8, y0 i - expK 53 (-y0 0) * Real.log 2))
    rw [sub_sub_cancel] at h
    linarith
  exact hlem _ hre

omit [Prec_gt_0 (53 : ℤ)] in
/-- `ε_1` and `μ` of the reduction are nonnegative. -/
theorem log8_red_nonneg : 0 ≤ redE1 53 8 (fun i => ((cl8 i : ℚ) : ℝ)) ∧
    ∀ i, 0 ≤ redMu 53 8 (fun i => ((cl8 i : ℚ) : ℝ)) i := by
  have hu : ((red8U : ℚ) : ℝ) = u (53 : ℤ) := by unfold red8U; exact u_53_rat 53 rfl
  have hu53 : u (53 : ℤ) = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  have hA3 : (((8 : ℕ) : ℝ) ^ 2 + (8 : ℕ)) * u (53 : ℤ) < 1 := by rw [hu53]; norm_num
  have hl : ∀ m, 0 ≤ |((cl8 m : ℚ) : ℝ)| * 1075 := fun m => mul_nonneg (abs_nonneg _) (by norm_num)
  have hX := pairX_nonneg (53 : ℤ) 8 hA3 (lam := fun m => |((cl8 m : ℚ) : ℝ)| * 1075) hl
  have hR : 0 ≤ pairR 53 8 (fun m => |((cl8 m : ℚ) : ℝ)| * 1075) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (u_pos 53).le) (hX 8)
  have hZ : (0 : ℝ) ≤ 1075 * |∑ i ∈ range 8, ((cl8 i : ℚ) : ℝ)| := by positivity
  exact ⟨gErr_nonneg 53 8 hX hZ hR, gParts_nonneg 53 8 hX hZ hR⟩

/-- `r̄_max`, `δ*`, `δ` and `π^r` of the reduction of `-y_0`, as functions of `ℓ`, are in the class on a convex set
of `ℓ ≥ 0`, for `r̄ = b + δ*` with a constant `b ≥ 0`. -/
theorem log8_red_cvx {s : Set ℝ} (hs : Convex ℝ s) (hpos : ∀ l ∈ s, 0 ≤ l) {rb : ℝ} (hrb0 : 0 ≤ rb) :
    Cvx s (fun l => rMax 53 (log8Yb l / (1 - u 53)) (2 * u 53 * log8Yb l)) ∧ Cvx s log8DsR ∧
      Cvx s (log8DR rb) ∧ ∀ i, Cvx s fun l => log8PR rb l i := by
  have hu : ((red8U : ℚ) : ℝ) = u (53 : ℤ) := by unfold red8U; exact u_53_rat 53 rfl
  have hu53 : u (53 : ℤ) = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  have hA3 : (((8 : ℕ) : ℝ) ^ 2 + (8 : ℕ)) * u (53 : ℤ) < 1 := by rw [hu53]; norm_num
  have h1u : (0 : ℝ) < 1 - u 53 := by rw [hu53]; norm_num
  obtain ⟨he0, he1, hcr⟩ := log8E_consts
  have he0' : (0 : ℝ) ≤ ((log8E0 : ℚ) : ℝ) := by exact_mod_cast he0
  have he1' : (0 : ℝ) ≤ ((log8E1 : ℚ) : ℝ) := by exact_mod_cast he1
  have hcR : 0 ≤ cR 53 := by
    rw [cR_eq 53 rfl]
    exact_mod_cast hcr
  obtain ⟨hε, hμ⟩ := log8_red_nonneg
  have hkη : (0 : ℝ) ≤ 1075 * etaL 8 ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)) :=
    mul_nonneg (by norm_num) (abs_nonneg _)
  have hα := fun i => logAlpha_cvx 53 hs hpos (by rw [hu53]; norm_num) hcR ((ch8 : ℚ) : ℝ) he0' he1' i
  have hYc := logYb_cvx hs hpos he0' he1'
  have hrmax := rMax_cvx 53 hs hcR (hYc.div_const h1u.le)
    (hYc.const_mul (by rw [hu53]; norm_num : (0 : ℝ) ≤ 2 * u 53))
  have hds : Cvx s log8DsR := redDeltaC_cvx 53 8 hA3 hs hε hkη hα hμ hrmax
  have hrbc := (Cvx.const hs hrb0).add hds
  exact ⟨hrmax, hds, redDeltaC_cvx 53 8 hA3 hs hε hkη hα hμ hrbc, fun i =>
    redPiC_cvx 53 8 hA3 hs hε hkη hα hμ hrbc i⟩

/-- Theorem 42 (`thm:log`) at `n = 8` for a case of `k ≠ 0` on an interval `[ℓ₁, ℓ₂]` of `|ln x|`, from the kernel's
two evaluations of the case: `r` is EXP's reduction of `-y_0` with multidouble's constants, the start has two parts
with `|y_{0,1}| ≤ u|y_{0,0}|`, `|r| ≤ b` for the case's rational `b`, and Lemma 38 applies up to `ℓ₂` (`X ≤ 745.3`
and `α_0 < 1/2`, on their mirrors); `δ` and `π` are Lemma 38 (b)'s at `r̄ = b + δ*`, as functions of `ℓ` -/
theorem log8_k1 {m : ℕ} {S₁ S₂ Sx Sp Sc : ℝ → ℝ} (hS₁ : Scl 53 ((exp8Eta1 m : ℚ) : ℝ) S₁)
    (hS₂ : Scl 53 ((exp8Eta : ℚ) : ℝ) S₂) (hSx : Scl 53 ((2 * exp8Eta : ℚ) : ℝ) Sx)
    (hSp : Scl 53 ((2 * exp8Eta : ℚ) : ℝ) Sp) (hSc : Scl 53 ((exp8Eta : ℚ) : ℝ) Sc) (x : ℕ → ℝ)
    (hx : ∀ i < 8, F 53 (x i)) (hX0 : 0 < ∑ i ∈ range 8, x i) (hH : Htheta 53 8 2 x) (y0 : ℕ → ℝ)
    (hy0 : ∀ i < 8, F 53 (y0 i)) (hy1 : |y0 1| ≤ u 53 * |y0 0|) (hy2 : ∀ i, 2 ≤ i → y0 i = 0) {l₁ l₂ : ℚ}
    (h0 : 0 ≤ l₁) (hl : |Real.log (∑ i ∈ range 8, x i)| ∈ Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ))
    (hE : |∑ i ∈ range 8, y0 i - Real.log (∑ i ∈ range 8, x i)| ≤ log8E |Real.log (∑ i ∈ range 8, x i)|)
    (r : ℕ → ℝ) (hr : ∀ i < 8, F 53 (r i))
    (hrd : r = expR 53 8 (fun i => -y0 i) ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ))) (k : ℤ)
    (hkd : k = expK 53 (-y0 0)) (hk : k ≠ 0) (hX1 : (l₂ + log8Eq l₂) / (1 - red8U) ≤ 7453 / 10)
    (hA0 : log8Alpha l₂ 0 < 1 / 2) (a : ℚ)
    (ha : ((a : ℚ) : ℝ) ≤ |∑ i ∈ range 8, r i|)
    (rb : ℚ) (hb : |∑ i ∈ range 8, r i| ≤ ((rb : ℚ) : ℝ)) (pos : Bool)
    (hsgn : if pos then 0 ≤ ∑ i ∈ range 8, r i else ∑ i ∈ range 8, r i ≤ 0) (e : ℤ)
    (hU : ∑ i ∈ range 8, |r i| < (2 : ℝ) ^ (e + 1)) (d' : ℕ) (hd : 1 ≤ d')
    (hF : ∀ k, ∀ i < 8, F 53 ((exp8F k i : ℚ) : ℝ))
    (hφF : ∀ k, |∑ i ∈ range 8, ((exp8F k i : ℚ) : ℝ) - invF k| ≤ ((exp8Phi k : ℚ) : ℝ))
    (hπx : ∀ i < 8, |Sx ((2 : ℝ) ^ k * x i)| ≤ logPiX 8 (2 * u 53) ((2 * exp8Eta : ℚ) : ℝ)
      (logXi ((8 : ℕ) * ((2 * exp8Eta : ℚ) : ℝ)) pos (log8E |Real.log (∑ i ∈ range 8, x i)|) ((a : ℚ) : ℝ)
        ((rb : ℚ) : ℝ) (log8DR ((rb : ℚ) : ℝ) |Real.log (∑ i ∈ range 8, x i)|)) i)
    (hSx0 : 1 / 2 ≤ (2 : ℝ) ^ k * x 0 → (2 : ℝ) ^ k * x 0 ≤ 2 → Sx ((2 : ℝ) ^ k * x 0) = (2 : ℝ) ^ k * x 0)
    (eφ et ec : ℤ)
    (hUφ : ∑ i ∈ range 8, |logPhi 53 8 Sx k x i| < (2 : ℝ) ^ (eφ + 1))
    (hUt : ∑ i ∈ range 8, |expCore 53 8 S₁ S₂ e m r (fun k i => ((exp8F k i : ℚ) : ℝ)) d' i| < (2 : ℝ) ^ (et + 1))
    (hUc : ∑ i ∈ range 8, |logC 53 8 Sp 436 eφ et (logPhi 53 8 Sx k x)
      (expCore 53 8 S₁ S₂ e m r (fun k i => ((exp8F k i : ℚ) : ℝ)) d') i| < (2 : ℝ) ^ (ec + 1))
    (hF' : ∀ k, ∀ i < 8, F 53 ((log8F k i : ℚ) : ℝ))
    (hφ' : ∀ k, |∑ i ∈ range 8, ((log8F k i : ℚ) : ℝ) - logFe k| ≤ ((log8Phi k : ℚ) : ℝ))
    (hsh : Log8Shared) {zero : Bool} {δ₁ δ₂ : ℚ} (ev₁ : Log8Eval false pos m d' a l₁ zero rb δ₁)
    (ev₂ : Log8Eval false pos m d' a l₂ zero rb δ₂) (hc : rb + log8Eq l₂ + δ₂ ≤ 3 / 5) :
    |(logOp 53 8 Sx Sp Sc y0 x k (expCore 53 8 S₁ S₂ e m r (fun k i => ((exp8F k i : ℚ) : ℝ)) d') 436 eφ et ec
        (fun k i => ((log8F k i : ℚ) : ℝ)) 4).sum - Real.log (∑ i ∈ range 8, x i)| ≤
      (if zero then (1 : ℝ) / 2 ^ 509 else 0) + 9926 / 1000 * u 53 ^ 8 * |Real.log (∑ i ∈ range 8, x i)| := by
  have hl₁ : (0 : ℝ) ≤ ((l₁ : ℚ) : ℝ) := by exact_mod_cast h0
  have h12 : ((l₁ : ℚ) : ℝ) ≤ ((l₂ : ℚ) : ℝ) := hl.1.trans hl.2
  have h02 : (0 : ℚ) ≤ l₂ := by exact_mod_cast hl₁.trans h12
  have hs : Convex ℝ (Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ)) := convex_Icc _ _
  have hpos : ∀ l ∈ Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ), 0 ≤ l := fun l h => hl₁.trans h.1
  have hrb0 : (0 : ℝ) ≤ ((rb : ℚ) : ℝ) := (abs_nonneg _).trans hb
  obtain ⟨-, -, hδc, hπc⟩ := log8_red_cvx hs hpos hrb0
  -- the run
  obtain ⟨-, hπy⟩ := log8_start_parts y0 hy1 hy2 hE
  subst hrd hkd
  obtain ⟨hδ, hπ⟩ := log8_red_run y0 hy0 hy1 hy2 hE hl.2 hX1 hA0 hk hb
  -- the ends
  have e₁ := ev₁
  have e₂ := ev₂
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨-, -, -, -, -, -, -, -, hd₁, -⟩, -⟩ := e₁
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨-, -, -, -, -, -, -, -, hd₂, -⟩, -⟩ := e₂
  simp only [Bool.false_eq_true, ↓reduceIte] at hd₁ hd₂
  exact log8_chord_case hS₁ hS₂ hSx hSp hSc x hx hX0 hH y0 hy0 h0 hl (Cvx.const hs hrb0) hδc hπc hπy hE _ hr _ hδ
    a ha hb (fun i _ => hπ i) pos hsgn e hU d' hd hF hφF hπx hSx0 eφ et ec hUφ hUt hUc hF' hφ' hsh ev₁ ev₂ le_rfl
    ((log8DR_le l₁ h0 le_rfl).trans (Rat.cast_le.mpr hd₁))
    (fun i _ => by simpa using log8PR_le l₁ h0 (le_refl ((rb : ℚ) : ℝ)) i) le_rfl
    ((log8DR_le l₂ h02 le_rfl).trans (Rat.cast_le.mpr hd₂))
    (fun i _ => by simpa using log8PR_le l₂ h02 (le_refl ((rb : ℚ) : ℝ)) i) hc

end ExpansionBounds
