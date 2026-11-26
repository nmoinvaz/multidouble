import ExpansionBounds.Log8.Case

/-!
# Theorem 42 at `n = 8` and `p = 53`: a case of `k = 0`

For `k = 0` the reduction returns `r = -y_0`, so `δ = 0` and `π = π^y`: the part bounds of the two-part start
`y_0` on `H(1)`, with `|y_0| ≤ ȳ = ℓ + E(ℓ)` (`log8_start_parts`). `log8_k0` is `log8_chord_case` for these, with
the case's `b` still a function of `ℓ` in the class: `ȳ`, or a constant for the cases taken from `ℓ = 0`.
-/

namespace ExpansionBounds

open Finset Set

/-- The start `y_0`, two parts with `|y_{0,1}| ≤ u|y_{0,0}|`, within `E(ℓ)` of `ln x` for `ℓ = |ln x|`: `|y_0| ≤ ȳ`,
and its parts are within `π^y`, by `(eq:a0)` for two parts -/
theorem log8_start_parts (y0 : ℕ → ℝ) (hy1 : |y0 1| ≤ u 53 * |y0 0|) (hy2 : ∀ i, 2 ≤ i → y0 i = 0) {L : ℝ}
    (hE : |∑ i ∈ range 8, y0 i - L| ≤ log8E |L|) :
    |∑ i ∈ range 8, y0 i| ≤ log8Yb |L| ∧
      ∀ i < 8, |y0 i| ≤ logPiY 53 ((log8E0 : ℚ) : ℝ) ((log8E1 : ℚ) : ℝ) |L| i := by
  have hu : ((red8U : ℚ) : ℝ) = u (53 : ℤ) := by unfold red8U; exact u_53_rat 53 rfl
  have hu53 : u (53 : ℤ) = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  have h1u : (0 : ℝ) < 1 - u 53 := by rw [hu53]; norm_num
  have h2u : (0 : ℝ) < 1 - 2 * u 53 := by rw [hu53]; norm_num
  have hu0 : (0 : ℝ) ≤ u 53 := by rw [hu53]; norm_num
  have hY : |∑ i ∈ range 8, y0 i| ≤ log8Yb |L| := by
    have h1 := abs_add_le L (∑ i ∈ range 8, y0 i - L)
    rw [add_sub_cancel] at h1
    simp only [log8E] at hE
    simp only [log8Yb, logYb]
    linarith
  have hsum : ∑ i ∈ range 8, y0 i = y0 0 + y0 1 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hy2 2 le_rfl, hy2 3 (by norm_num),
      hy2 4 (by norm_num), hy2 5 (by norm_num), hy2 6 (by norm_num), hy2 7 (by norm_num)]
    ring
  -- `|y_{0,0}|(1 - u) ≤ |y_0|`
  have h0 : |y0 0| * (1 - u 53) ≤ log8Yb |L| := by
    have h2 : |y0 0| - |y0 1| ≤ |y0 0 + y0 1| := by
      have := abs_sub_abs_le_abs_sub (y0 0) (-y0 1)
      rwa [abs_neg, sub_neg_eq_add] at this
    rw [hsum] at hY
    linarith
  have hYb0 : 0 ≤ log8Yb |L| := (abs_nonneg _).trans hY
  have hq : log8Yb |L| / (1 - u 53) ≤ log8Yb |L| * (1 - u 53) / (1 - 2 * u 53) := by
    rw [div_le_div_iff₀ h1u h2u]
    nlinarith [mul_nonneg hYb0 (sq_nonneg (u 53))]
  have hh : |y0 0| ≤ log8Yb |L| * (1 - u 53) / (1 - 2 * u 53) :=
    ((le_div_iff₀ h1u).mpr h0).trans hq
  refine ⟨hY, fun i hi => ?_⟩
  obtain rfl | rfl | h : i = 0 ∨ i = 1 ∨ 2 ≤ i := by omega
  · simp only [logPiY, ladderB, show (0 : ℕ) < 2 by norm_num, ↓reduceIte, pow_zero, one_mul]
    exact hh
  · simp only [logPiY, ladderB, show (1 : ℕ) < 2 by norm_num, ↓reduceIte, pow_one]
    exact hy1.trans (mul_le_mul_of_nonneg_left hh hu0)
  · rw [hy2 i h, abs_zero]
    simp only [logPiY, ladderB, show ¬i < 2 by omega, ↓reduceIte, le_refl]

variable [Prec_gt_0 (53 : ℤ)]

/-- Theorem 42 (`thm:log`) at `n = 8` for a case of `k = 0` on an interval `[ℓ₁, ℓ₂]` of `|ln x|`, from the kernel's
two evaluations of the case: the reduction returns `r = -y_0`, the start has two parts with
`|y_{0,1}| ≤ u|y_{0,0}|`, and the case's `b` is a function of `ℓ` in the class `Cvx` above `|r|` at `ℓ = |ln x|`
and below the evaluations' `b` at the ends -/
theorem log8_k0 {m : ℕ} {S₁ S₂ Sx Sp Sc : ℝ → ℝ} (hS₁ : Scl 53 ((exp8Eta1 m : ℚ) : ℝ) S₁)
    (hS₂ : Scl 53 ((exp8Eta : ℚ) : ℝ) S₂) (hSx : Scl 53 ((2 * exp8Eta : ℚ) : ℝ) Sx)
    (hSp : Scl 53 ((2 * exp8Eta : ℚ) : ℝ) Sp) (hSc : Scl 53 ((exp8Eta : ℚ) : ℝ) Sc) (x : ℕ → ℝ)
    (hx : ∀ i < 8, F 53 (x i)) (hX0 : 0 < ∑ i ∈ range 8, x i) (hH : Htheta 53 8 2 x) (y0 : ℕ → ℝ)
    (hy0 : ∀ i < 8, F 53 (y0 i)) (hy1 : |y0 1| ≤ u 53 * |y0 0|) (hy2 : ∀ i, 2 ≤ i → y0 i = 0) {l₁ l₂ : ℚ}
    (h0 : 0 ≤ l₁) (hl : |Real.log (∑ i ∈ range 8, x i)| ∈ Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ)) {b : ℝ → ℝ}
    (hbc : Cvx (Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ)) b)
    (hE : |∑ i ∈ range 8, y0 i - Real.log (∑ i ∈ range 8, x i)| ≤ log8E |Real.log (∑ i ∈ range 8, x i)|)
    (r : ℕ → ℝ) (hr : ∀ i < 8, F 53 (r i)) (hry : ∀ i, r i = -y0 i) (a : ℚ)
    (ha : ((a : ℚ) : ℝ) ≤ |∑ i ∈ range 8, r i|)
    (hb : |∑ i ∈ range 8, r i| ≤ b |Real.log (∑ i ∈ range 8, x i)|) (pos : Bool)
    (hsgn : if pos then 0 ≤ ∑ i ∈ range 8, r i else ∑ i ∈ range 8, r i ≤ 0) (e : ℤ)
    (hU : ∑ i ∈ range 8, |r i| < (2 : ℝ) ^ (e + 1)) (d' : ℕ) (hd : 1 ≤ d')
    (hF : ∀ k, ∀ i < 8, F 53 ((exp8F k i : ℚ) : ℝ))
    (hφF : ∀ k, |∑ i ∈ range 8, ((exp8F k i : ℚ) : ℝ) - invF k| ≤ ((exp8Phi k : ℚ) : ℝ))
    (hπx : ∀ i < 8, |Sx ((2 : ℝ) ^ (0 : ℤ) * x i)| ≤ logPiX 8 (2 * u 53) ((2 * exp8Eta : ℚ) : ℝ)
      (logXi ((8 : ℕ) * ((2 * exp8Eta : ℚ) : ℝ)) pos (log8E |Real.log (∑ i ∈ range 8, x i)|) ((a : ℚ) : ℝ)
        (b |Real.log (∑ i ∈ range 8, x i)|) 0) i)
    (hSx0 : 1 / 2 ≤ (2 : ℝ) ^ (0 : ℤ) * x 0 → (2 : ℝ) ^ (0 : ℤ) * x 0 ≤ 2 →
      Sx ((2 : ℝ) ^ (0 : ℤ) * x 0) = (2 : ℝ) ^ (0 : ℤ) * x 0) (eφ et ec : ℤ)
    (hUφ : ∑ i ∈ range 8, |logPhi 53 8 Sx 0 x i| < (2 : ℝ) ^ (eφ + 1))
    (hUt : ∑ i ∈ range 8, |expCore 53 8 S₁ S₂ e m r (fun k i => ((exp8F k i : ℚ) : ℝ)) d' i| < (2 : ℝ) ^ (et + 1))
    (hUc : ∑ i ∈ range 8, |logC 53 8 Sp 436 eφ et (logPhi 53 8 Sx 0 x)
      (expCore 53 8 S₁ S₂ e m r (fun k i => ((exp8F k i : ℚ) : ℝ)) d') i| < (2 : ℝ) ^ (ec + 1))
    (hF' : ∀ k, ∀ i < 8, F 53 ((log8F k i : ℚ) : ℝ))
    (hφ' : ∀ k, |∑ i ∈ range 8, ((log8F k i : ℚ) : ℝ) - logFe k| ≤ ((log8Phi k : ℚ) : ℝ))
    (hsh : Log8Shared) {zero : Bool} {b₁ b₂ : ℚ} (ev₁ : Log8Eval true pos m d' a l₁ zero b₁ 0)
    (ev₂ : Log8Eval true pos m d' a l₂ zero b₂ 0) (hb₁ : b ((l₁ : ℚ) : ℝ) ≤ ((b₁ : ℚ) : ℝ))
    (hb₂ : b ((l₂ : ℚ) : ℝ) ≤ ((b₂ : ℚ) : ℝ)) (hc : b₂ + log8Eq l₂ ≤ 3 / 5) :
    |(logOp 53 8 Sx Sp Sc y0 x 0 (expCore 53 8 S₁ S₂ e m r (fun k i => ((exp8F k i : ℚ) : ℝ)) d') 436 eφ et ec
        (fun k i => ((log8F k i : ℚ) : ℝ)) 4).sum - Real.log (∑ i ∈ range 8, x i)| ≤
      (if zero then (1 : ℝ) / 2 ^ 509 else 0) + 9926 / 1000 * u 53 ^ 8 * |Real.log (∑ i ∈ range 8, x i)| := by
  have hu : ((red8U : ℚ) : ℝ) = u (53 : ℤ) := by unfold red8U; exact u_53_rat 53 rfl
  have hu53 : u (53 : ℤ) = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  obtain ⟨he0, he1, -⟩ := log8E_consts
  have he0' : (0 : ℝ) ≤ ((log8E0 : ℚ) : ℝ) := by exact_mod_cast he0
  have he1' : (0 : ℝ) ≤ ((log8E1 : ℚ) : ℝ) := by exact_mod_cast he1
  have hl₁ : (0 : ℝ) ≤ ((l₁ : ℚ) : ℝ) := by exact_mod_cast h0
  have hs : Convex ℝ (Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ)) := convex_Icc _ _
  have hpos : ∀ l ∈ Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ), 0 ≤ l := fun l h => hl₁.trans h.1
  obtain ⟨-, hπy⟩ := log8_start_parts y0 hy1 hy2 hE
  have hδ : |∑ i ∈ range 8, r i - (-∑ i ∈ range 8, y0 i - ((0 : ℤ) : ℝ) * Real.log 2)| ≤
      (fun _ : ℝ => (0 : ℝ)) |Real.log (∑ i ∈ range 8, x i)| := by
    simp [hry, Finset.sum_neg_distrib]
  have hπ : ∀ i < 8, |r i| ≤ (fun l i => logPiY 53 ((log8E0 : ℚ) : ℝ) ((log8E1 : ℚ) : ℝ) l i)
      |Real.log (∑ i ∈ range 8, x i)| i := fun i hi => by
    rw [hry i, abs_neg]
    exact hπy i hi
  exact log8_chord_case hS₁ hS₂ hSx hSp hSc x hx hX0 hH y0 hy0 h0 hl hbc (Cvx.const hs (le_refl (0 : ℝ)))
    (fun i => logPiY_cvx 53 hs hpos (by rw [hu53]; norm_num) he0' he1' i) hπy hE r hr 0 hδ a ha hb hπ pos hsgn e
    hU d' hd hF hφF hπx hSx0 eφ et ec hUφ hUt hUc hF' hφ' hsh ev₁ ev₂ hb₁ (by simp)
    (fun i _ => by simpa using log8PiY_le l₁ i) hb₂ (by simp) (fun i _ => by simpa using log8PiY_le l₂ i)
    (by simpa using hc)

end ExpansionBounds
