import ExpansionBounds.LogConvexBound

/-!
# The arguments of Theorem 42's bound as functions of `ℓ`

Theorem 42's proof (`thm:log`), paragraph "Convexity": for `k = 0`, `ℓ` enters the bound through `E(ℓ)` and `b`; for
`k ≠ 0`, through `E(ℓ)`, `ȳ = ℓ + E(ℓ)` and Lemma 38's `X = ȳ/(1 - u)`, `x̄_t = 2uȳ` and `α = π^y`, all linear in `ℓ`.
Here are these arguments: `logE`, `logYb`, the ladders `logPiY` and `logPiX`, Lemma 38's `α` (`logAlpha`) and its
`δ` and `π^r` with VecSum's second bound alone in `G_ADD` (`redDeltaC`, `redPiC`). Each is nonnegative, nondecreasing
and convex in `ℓ ≥ 0`, and `redDeltaC` and `redPiC` are at least Lemma 38 (b)'s bounds (`red_le_redDeltaC`,
`red_le_redPiC`).
-/

namespace ExpansionBounds

open Finset Set

variable (p : ℤ) (n : ℕ) {s : Set ℝ}

/-- `E(ℓ) = e₀ + e₁ℓ`, the bound on the start: `e₁ = ε_DW + e_A` and
`e₀ = ε_DW δ₀ + δ₀ + Φ_DW + e_A + η_L + 2^{-2000}` -/
noncomputable def logE (e0 e1 ℓ : ℝ) : ℝ := e0 + e1 * ℓ

/-- `ȳ = ℓ + E(ℓ)` -/
noncomputable def logYb (e0 e1 ℓ : ℝ) : ℝ := ℓ + logE e0 e1 ℓ

/-- the part bounds of an expansion of `k` parts on the ladder of ratio `ρ` with value at most `t`:
`ρ^i t(1 - ρ)/(1 - 2ρ)`, by `(eq:a0)` -/
noncomputable def ladderB (ρ : ℝ) (k : ℕ) (t : ℝ) (i : ℕ) : ℝ :=
  if i < k then ρ ^ i * (t * (1 - ρ) / (1 - 2 * ρ)) else 0

/-- `π^y`: the part bounds of the two-part start on `H(1)` with value at most `ȳ` -/
noncomputable def logPiY (e0 e1 ℓ : ℝ) (i : ℕ) : ℝ := ladderB (u p) 2 (logYb e0 e1 ℓ) i

/-- `π^x`: the part bounds of an expansion on `H(θ)`, `ρ = θu`, with value at most `ξ`, each plus `η_x` -/
noncomputable def logPiX (ρ ηx ξ : ℝ) (i : ℕ) : ℝ := ladderB ρ n ξ i + ηx

/-- Lemma 38's `α` for the reduction of `-y_0`: `α_0` at `X = ȳ/(1 - u)` and `x̄_t = 2uȳ`, and `α_i = π^y_i` -/
noncomputable def logAlpha (ch e0 e1 ℓ : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then expA0 p (logYb e0 e1 ℓ / (1 - u p)) (2 * u p * logYb e0 e1 ℓ) ch else logPiY p e0 e1 ℓ i

/-- Lemma 38 (b)'s `δ = ε_1 + ε_2 + k̄η_ℓ` with VecSum's second bound alone in `G_ADD`; `kη` stands for `k̄η_ℓ` -/
noncomputable def redDeltaC (ε1 kη : ℝ) (α μ : ℕ → ℝ) (rb : ℝ) : ℝ := ε1 + GaddEC p n α μ (rb + kη + ε1) + kη

/-- Lemma 38 (b)'s `π^r` with VecSum's second bound alone in `G_ADD` -/
noncomputable def redPiC (ε1 kη : ℝ) (α μ : ℕ → ℝ) (rb : ℝ) : ℕ → ℝ := GaddPC p n α μ (rb + kη + ε1)

/-- Lemma 38 (b)'s `δ` is at most its convex variant. -/
theorem red_le_redDeltaC (ch : ℝ) (cl α : ℕ → ℝ) (rb : ℝ) :
    redE1 p n cl + GaddE p n α (redMu p n cl) (redZ p n ch cl rb) + 1075 * etaL n ch cl ≤
      redDeltaC p n (redE1 p n cl) (1075 * etaL n ch cl) α (redMu p n cl) rb := by
  have h := GaddE_le_GaddEC p n α (redMu p n cl) (redZ p n ch cl rb)
  simp only [redDeltaC, redZ] at h ⊢
  linarith

/-- Lemma 38 (b)'s `π^r` is at most its convex variant. -/
theorem red_le_redPiC (ch : ℝ) (cl α : ℕ → ℝ) (rb : ℝ) (i : ℕ) :
    GaddP p n α (redMu p n cl) (redZ p n ch cl rb) i ≤
      redPiC p n (redE1 p n cl) (1075 * etaL n ch cl) α (redMu p n cl) rb i :=
  GaddP_le_GaddPC p n α (redMu p n cl) (redZ p n ch cl rb) i

/-! ### The class `Cvx` -/

/-- `E(ℓ)` is in the class on `ℓ ≥ 0`. -/
theorem logE_cvx (hs : Convex ℝ s) (h0 : ∀ x ∈ s, 0 ≤ x) {e0 e1 : ℝ} (he0 : 0 ≤ e0) (he1 : 0 ≤ e1) :
    Cvx s (logE e0 e1) :=
  Cvx.affine hs h0 he0 he1

/-- `ȳ = ℓ + E(ℓ)` is in the class on `ℓ ≥ 0`. -/
theorem logYb_cvx (hs : Convex ℝ s) (h0 : ∀ x ∈ s, 0 ≤ x) {e0 e1 : ℝ} (he0 : 0 ≤ e0) (he1 : 0 ≤ e1) :
    Cvx s (logYb e0 e1) :=
  (Cvx.id hs h0).add (logE_cvx hs h0 he0 he1)

/-- The ladder's part bounds are in the class when the bound on the value is, for `0 ≤ ρ` and `2ρ < 1`. -/
theorem ladderB_cvx (hs : Convex ℝ s) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : 2 * ρ < 1) (k : ℕ) {t : ℝ → ℝ} (ht : Cvx s t)
    (i : ℕ) : Cvx s fun l => ladderB ρ k (t l) i := by
  simp only [ladderB]
  exact Cvx.ite _ (fun _ => ((ht.mul_const (by linarith : (0 : ℝ) ≤ 1 - ρ)).div_const
    (by linarith : (0 : ℝ) ≤ 1 - 2 * ρ)).const_mul (pow_nonneg hρ0 i)) fun _ => Cvx.const hs le_rfl

/-- `π^y` is in the class on `ℓ ≥ 0`, for `2u < 1`. -/
theorem logPiY_cvx (hs : Convex ℝ s) (h0 : ∀ x ∈ s, 0 ≤ x) (hu : 2 * u p < 1) {e0 e1 : ℝ} (he0 : 0 ≤ e0)
    (he1 : 0 ≤ e1) (i : ℕ) : Cvx s fun l => logPiY p e0 e1 l i :=
  ladderB_cvx hs (u_pos p).le hu 2 (logYb_cvx hs h0 he0 he1) i

/-- `π^x` is in the class when `ξ` is, for `0 ≤ ρ`, `2ρ < 1` and `0 ≤ η_x`. -/
theorem logPiX_cvx (hs : Convex ℝ s) {ρ ηx : ℝ} (hρ0 : 0 ≤ ρ) (hρ : 2 * ρ < 1) (hηx : 0 ≤ ηx) {ξ : ℝ → ℝ}
    (hξ : Cvx s ξ) (i : ℕ) : Cvx s fun l => logPiX n ρ ηx (ξ l) i :=
  (ladderB_cvx hs hρ0 hρ n hξ i).add (Cvx.const hs hηx)

/-- `r̄_max` of Lemma 38 is in the class when `X` and `x̄_t` are, for `c_r ≥ 0`. -/
theorem rMax_cvx (hs : Convex ℝ s) (hcR : 0 ≤ cR p) {X xt : ℝ → ℝ} (hX : Cvx s X) (hxt : Cvx s xt) :
    Cvx s fun l => rMax p (X l) (xt l) := by
  have hc : 0 ≤ |cR p - 1 / Real.log 2| + u p * cR p := add_nonneg (abs_nonneg _) (mul_nonneg (u_pos p).le hcR)
  simp only [rMax, epsK]
  exact (((Cvx.const hs (by norm_num : (0 : ℝ) ≤ 1 / 2)).add (hX.mul_const hc)).mul_const
    (Real.log_nonneg one_le_two)).add hxt

/-- Lemma 38's `α` for the reduction of `-y_0` is in the class on `ℓ ≥ 0`, for `2u < 1` and `c_r ≥ 0`. -/
theorem logAlpha_cvx (hs : Convex ℝ s) (h0 : ∀ x ∈ s, 0 ≤ x) (hu : 2 * u p < 1) (hcR : 0 ≤ cR p) (ch : ℝ)
    {e0 e1 : ℝ} (he0 : 0 ≤ e0) (he1 : 0 ≤ e1) (i : ℕ) : Cvx s fun l => logAlpha p ch e0 e1 l i := by
  have hu0 := u_pos p
  have hy := logYb_cvx hs h0 he0 he1
  have hX : Cvx s fun l => logYb e0 e1 l / (1 - u p) := hy.div_const (by linarith)
  have hxt : Cvx s fun l => 2 * u p * logYb e0 e1 l := hy.const_mul (by positivity)
  have hc : (0 : ℝ) ≤ 1075 * |Real.log 2 - ch| := mul_nonneg (by norm_num) (abs_nonneg _)
  have hA0 : Cvx s fun l => expA0 p (logYb e0 e1 l / (1 - u p)) (2 * u p * logYb e0 e1 l) ch := by
    simp only [expA0]
    exact ((rMax_cvx p hs hcR hX hxt).add hxt).add (Cvx.const hs hc)
  simp only [logAlpha]
  exact Cvx.ite _ (fun _ => hA0) fun _ => logPiY_cvx p hs h0 hu he0 he1 i

/-- The convex `δ` of Lemma 38 (b) is in the class when `α` and `r̄` are, for constant `ε_1`, `k̄η_ℓ`, `μ ≥ 0`. -/
theorem redDeltaC_cvx (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (hs : Convex ℝ s) {ε1 kη : ℝ} (hε : 0 ≤ ε1)
    (hk : 0 ≤ kη) {α : ℝ → ℕ → ℝ} (hα : ∀ i, Cvx s fun l => α l i) {μ : ℕ → ℝ} (hμ : ∀ i, 0 ≤ μ i) {rb : ℝ → ℝ}
    (hr : Cvx s rb) : Cvx s fun l => redDeltaC p n ε1 kη (α l) μ (rb l) := by
  simp only [redDeltaC]
  exact ((Cvx.const hs hε).add (GaddEC_cvx p n hA3 hs hα (β := fun _ => μ) (fun i => Cvx.const hs (hμ i))
    ((hr.add (Cvx.const hs hk)).add (Cvx.const hs hε)))).add (Cvx.const hs hk)

/-- The convex `π^r` of Lemma 38 (b) is in the class when `α` and `r̄` are, for constant `ε_1`, `k̄η_ℓ`, `μ ≥ 0`. -/
theorem redPiC_cvx (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (hs : Convex ℝ s) {ε1 kη : ℝ} (hε : 0 ≤ ε1)
    (hk : 0 ≤ kη) {α : ℝ → ℕ → ℝ} (hα : ∀ i, Cvx s fun l => α l i) {μ : ℕ → ℝ} (hμ : ∀ i, 0 ≤ μ i) {rb : ℝ → ℝ}
    (hr : Cvx s rb) (i : ℕ) : Cvx s fun l => redPiC p n ε1 kη (α l) μ (rb l) i := by
  simp only [redPiC]
  exact GaddPC_cvx p n hA3 hs hα (β := fun _ => μ) (fun i => Cvx.const hs (hμ i))
    ((hr.add (Cvx.const hs hk)).add (Cvx.const hs hε)) i

end ExpansionBounds
