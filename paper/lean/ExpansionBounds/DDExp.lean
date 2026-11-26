import ExpansionBounds.DDExpCore
import ExpansionBounds.DDExpRed

/-!
# Proposition 44 (`prop:ddexplog`): `DD::exp`, for a case

Theorem 40 (`thm:exp`) read with `n = 2`. For a double word `r` within `δ` of `r_e = x - k ln 2`, with
`a ≤ |r| ≤ b`, the case's sign and degree `d'`, `t` is step (3)'s result (`dd_core`, `m = 0`), and
`y = 2^k DWPlusFP(t, 1)`. With `E_0` of the core, `Z = e^b + E_0` for `r ≥ 0` and `e^{-a} + E_0` for `r ≤ 0`, and
`v = e^{a-δ}` or `e^{-b-δ}`,

  `ε = (E_0 + e_F Z)/v + e^δ - 1`, `|y - e^x| ≤ ε e^x + 2η₃`,

the bound of `Exp.exp_bin` in `explog_consts.py` for double words, before its roundings up; `η₃` bounds what the last
scaling moves a part by. With binary64's rounding at each scaling and the last one in two steps, the last term is
`2·2η_0 = 2^{-1073}` (`dd_thm40_case_sub`): there the scaling back of step (3) rounds each part, and keeps a double
word whose high part is at least `2^{-967}` (`SclDW.of_grid`).
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ)

/-- the bound of a case read with `n = 2`: `ε = (E_0 + e_F Z)/v + e^δ - 1` -/
noncomputable def ddExpEps (η : ℝ) (pos : Bool) (a b δ : ℝ) (φ : ℕ → ℝ) (d' : ℕ) : ℝ :=
  (ddCoreE p (coreT pos b 0) η b φ d' + eF p * expZ pos a b (ddCoreE p (coreT pos b 0) η b φ d')) /
    expV pos a b δ + Real.exp δ - 1

variable [Prec_gt_0 p]

/-- Theorem 40 (`thm:exp`) read with `n = 2`, for a case: if the double word `r` is within `δ` of
`r_e = x - k ln 2`, with `a ≤ |r| ≤ b`, the case's sign and degree `d'`, then `y = 2^k DWPlusFP(t, 1)`, each part of
the scaling rounded by `S₃`, satisfies `|y - e^x| ≤ ε e^x + 2η₃` -/
theorem dd_thm40_case {O : DWOps} (hO : DWSpec p O) (hu : 4 * u p < 1) {η lo η₃ : ℝ} {S : ℝ × ℝ → ℝ × ℝ}
    (hS : SclDW p η lo S) {S₃ : ℝ → ℝ} (hS₃ : Scl p η₃ S₃) (r : ℝ × ℝ) (hr : DW p r) (X : ℝ) (k : ℤ) (δ : ℝ)
    (hδ : |dwVal r - (X - k * Real.log 2)| ≤ δ) (a b : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ |dwVal r|)
    (hb : |dwVal r| ≤ b) (e : ℤ) (d' : ℕ) (hd : 1 ≤ d') (hbd : b < d' + 2) (Fk : ℕ → ℝ × ℝ)
    (hF : ∀ k, DW p (Fk k)) (φ : ℕ → ℝ) (hφ : ∀ k, |dwVal (Fk k) - invF k| ≤ φ k) (pos : Bool)
    (hsgn : if pos then 0 ≤ dwVal r else dwVal r ≤ 0)
    (hlo : d' ≠ 1 → lo * (1 + u p) ≤ a / (1 + a) - ddCoreE p (coreT pos b 0) 0 b φ d') :
    |S₃ ((2 : ℝ) ^ k * (O.addF (ddExpT O S e r Fk d') 1).1) +
        S₃ ((2 : ℝ) ^ k * (O.addF (ddExpT O S e r Fk d') 1).2) - Real.exp X| ≤
      ddExpEps p η pos a b δ φ d' * Real.exp X + 2 * η₃ := by
  obtain ⟨c1, c2, -⟩ := dd_core p hO hu hS r hr a b ha0 ha hb e d' hd hbd Fk hF φ hφ pos hsgn hlo
  obtain ⟨R, hR⟩ : ∃ R, R = dwVal r := ⟨_, rfl⟩
  rw [← hR] at hδ ha hb hsgn c1
  obtain ⟨E, hE⟩ : ∃ E, E = ddCoreE p (coreT pos b 0) η b φ d' := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = ddExpT O S e r Fk d' := ⟨_, rfl⟩
  rw [← hE, ← ht] at c1
  rw [← ht] at c2 ⊢
  obtain ⟨y, hy⟩ : ∃ y, y = O.addF t 1 := ⟨_, rfl⟩
  rw [← hy]
  have heF := eF_nonneg p
  -- the last scaling moves each part by at most `η₃`
  have hsc : |S₃ ((2 : ℝ) ^ k * y.1) + S₃ ((2 : ℝ) ^ k * y.2) - (2 : ℝ) ^ k * dwVal y| ≤ 2 * η₃ := by
    have h1 := hS₃.err ((2 : ℝ) ^ k * y.1)
    have h2 := hS₃.err ((2 : ℝ) ^ k * y.2)
    calc _ = |(S₃ ((2 : ℝ) ^ k * y.1) - (2 : ℝ) ^ k * y.1) + (S₃ ((2 : ℝ) ^ k * y.2) - (2 : ℝ) ^ k * y.2)| := by
          simp only [dwVal]; ring_nf
      _ ≤ |S₃ ((2 : ℝ) ^ k * y.1) - (2 : ℝ) ^ k * y.1| + |S₃ ((2 : ℝ) ^ k * y.2) - (2 : ℝ) ^ k * y.2| :=
          abs_add_le _ _
      _ ≤ 2 * η₃ := by linarith
  suffices hmain : |(2 : ℝ) ^ k * dwVal y - Real.exp X| ≤ ddExpEps p η pos a b δ φ d' * Real.exp X by
    rw [show S₃ ((2 : ℝ) ^ k * y.1) + S₃ ((2 : ℝ) ^ k * y.2) - Real.exp X =
      (S₃ ((2 : ℝ) ^ k * y.1) + S₃ ((2 : ℝ) ^ k * y.2) - (2 : ℝ) ^ k * dwVal y) +
        ((2 : ℝ) ^ k * dwVal y - Real.exp X) by ring]
    exact (abs_add_le _ _).trans (by linarith)
  obtain ⟨T, hT⟩ : ∃ T, T = dwVal t := ⟨_, rfl⟩
  rw [← hT] at c1
  have hE0 : 0 ≤ E := (abs_nonneg _).trans c1
  -- `e^r ≤ e^b` or `e^{-a}`, so `|t + 1| ≤ Z`
  have heR : Real.exp R ≤ (if pos then Real.exp b else Real.exp (-a)) := by
    cases pos with
    | true =>
      simp only [ite_true]
      exact Real.exp_le_exp.mpr ((le_abs_self R).trans hb)
    | false =>
      simp only [Bool.false_eq_true, ite_false] at hsgn ⊢
      rw [abs_of_nonpos hsgn] at ha
      exact Real.exp_le_exp.mpr (by linarith)
  have hZ : |T + 1| ≤ expZ pos a b E := by
    unfold expZ
    rw [show T + 1 = Real.exp R + (T - (Real.exp R - 1)) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_pos (Real.exp_pos R)]
    linarith
  -- DWPlusFP
  obtain ⟨εs, hεsd⟩ : ∃ εs, εs = eF p * expZ pos a b E := ⟨_, rfl⟩
  have hεs : |dwVal y - (T + 1)| ≤ εs := by
    rw [hεsd, hy, hT]
    exact (hO.addF_err t 1 c2 (F_one p)).trans (mul_le_mul_of_nonneg_left (hT ▸ hZ) heF)
  -- `e^x = 2^k e^{r_e}` and `|e^r - e^{r_e}| ≤ e^{r_e}(e^δ - 1)`
  obtain ⟨re, hre⟩ : ∃ re, re = X - k * Real.log 2 := ⟨_, rfl⟩
  rw [← hre] at hδ
  have hX : Real.exp X = (2 : ℝ) ^ k * Real.exp re := by
    rw [hre, Real.exp_sub, exp_int_mul_log_two]
    field_simp
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hδ
  have hdiff : |Real.exp R - Real.exp re| ≤ Real.exp re * (Real.exp δ - 1) := by
    rw [show Real.exp R - Real.exp re = Real.exp re * (Real.exp (R - re) - 1) by
      rw [mul_sub, ← Real.exp_add]; ring_nf, abs_mul, abs_of_pos (Real.exp_pos re)]
    refine mul_le_mul_of_nonneg_left ((abs_exp_sub_one_le _).trans ?_) (Real.exp_pos re).le
    linarith [Real.exp_le_exp.mpr hδ]
  -- `e^{r_e} ≥ v`
  have hv : expV pos a b δ ≤ Real.exp re := by
    unfold expV
    have h1 := (abs_le.mp hδ)
    cases pos with
    | true =>
      simp only [ite_true] at hsgn ⊢
      rw [abs_of_nonneg hsgn] at ha
      exact Real.exp_le_exp.mpr (by linarith)
    | false =>
      simp only [Bool.false_eq_true, ite_false] at hsgn ⊢
      have := neg_abs_le R
      exact Real.exp_le_exp.mpr (by linarith)
  have hv0 : 0 < expV pos a b δ := by unfold expV; split_ifs <;> exact Real.exp_pos _
  -- assemble
  have hεs0 : 0 ≤ εs := (abs_nonneg _).trans hεs
  have hyb : |dwVal y - Real.exp re| ≤ E + εs + Real.exp re * (Real.exp δ - 1) := by
    rw [show dwVal y - Real.exp re = (dwVal y - (T + 1)) + (T - (Real.exp R - 1)) + (Real.exp R - Real.exp re) by ring]
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hεs c1)) hdiff) |>.trans_eq ?_
    ring
  have hfac : E + εs ≤ (E + εs) / expV pos a b δ * Real.exp re := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hv0]
    exact mul_le_mul_of_nonneg_left hv (by linarith)
  have heps : ddExpEps p η pos a b δ φ d' = (E + εs) / expV pos a b δ + Real.exp δ - 1 := by
    rw [ddExpEps, ← hE, hεsd]
  rw [heps, hX, show (2 : ℝ) ^ k * dwVal y - (2 : ℝ) ^ k * Real.exp re = (2 : ℝ) ^ k * (dwVal y - Real.exp re) by ring,
    abs_mul, abs_of_pos (by positivity)]
  rw [show ((E + εs) / expV pos a b δ + Real.exp δ - 1) * ((2 : ℝ) ^ k * Real.exp re) =
    (2 : ℝ) ^ k * ((E + εs) / expV pos a b δ * Real.exp re + Real.exp re * (Real.exp δ - 1)) by ring]
  exact mul_le_mul_of_nonneg_left (hyb.trans (by linarith)) (by positivity)

/-- binary64's scaling of a double word, each part rounded by `S`, which keeps a value or rounds one below
`2^{-1022}` to a multiple of `2^{-1074}` within `η_0 = 2^{-1075}`: each part moves by at most `η_0`, and a double
word whose high part is at least `2^{-967}` stays one, as its low part then stays below half the spacing of the
floats around the high part -/
theorem SclDW.of_grid (hp : p = 53) (S : ℝ → ℝ)
    (h : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ))) :
    SclDW p ((2 : ℝ) ^ (-1075 : ℤ)) ((2 : ℝ) ^ (-967 : ℤ)) fun v => (S v.1, S v.2) := by
  have hS0 := Scl.of_grid p hp S h
  refine ⟨fun v => hS0.err v.1, fun v => hS0.err v.2, fun v hv hlo => ?_⟩
  have e1 : (2 : ℝ) ^ (-1022 : ℤ) = (2 : ℝ) ^ (-1075 : ℤ) * 2 ^ (53 : ℕ) := by
    rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]
    norm_num
  have e2 : (2 : ℝ) ^ (-1020 : ℤ) = (2 : ℝ) ^ (-1075 : ℤ) * 2 ^ (55 : ℕ) := by
    rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]
    norm_num
  have e3 : (2 : ℝ) ^ (-968 : ℤ) = (2 : ℝ) ^ (-1075 : ℤ) * 2 ^ (107 : ℕ) := by
    rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]
    norm_num
  have e4 : (2 : ℝ) ^ (-967 : ℤ) = (2 : ℝ) ^ (-1075 : ℤ) * 2 ^ (108 : ℕ) := by
    rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]
    norm_num
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-1075 : ℤ) := by positivity
  -- the high part is kept
  have h1 : S v.1 = v.1 := by
    rcases h v.1 with h1 | ⟨-, h2, -⟩
    · exact h1
    · exfalso
      rw [e4] at hlo
      rw [e1] at h2
      nlinarith
  show F p (S v.1) ∧ F p (S v.2) ∧ RN p (S v.1 + S v.2) = S v.1
  rw [h1]
  refine ⟨hv.1, hS0.mem _ hv.2.1, ?_⟩
  rcases h v.2 with h2 | ⟨-, h3, h4⟩
  · rw [h2]
    exact hv.2.2
  -- the rounded low part `w` is below `2^{-1021}`, so `RN(v_h + w)` is within `2^{-1020}` of `v_h`
  obtain ⟨w, hw⟩ : ∃ w, w = S v.2 := ⟨_, rfl⟩
  rw [← hw] at h4 ⊢
  have hwb : |w| < (2 : ℝ) ^ (-1075 : ℤ) * 2 ^ (54 : ℕ) := by
    have := abs_sub_abs_le_abs_sub w v.2
    rw [e1] at h3
    nlinarith
  obtain ⟨g, hg⟩ : ∃ g, g = RN p (v.1 + w) := ⟨_, rfl⟩
  rw [← hg]
  have hgF : F p g := hg ▸ F_RN p _
  have hn := (RN_nearest p (v.1 + w)).2 v.1 hv.1
  rw [← hg, show v.1 - (v.1 + w) = -w by ring, abs_neg] at hn
  have hgv : |g - v.1| < (2 : ℝ) ^ (-1020 : ℤ) := by
    rw [e2]
    calc |g - v.1| = |(g - (v.1 + w)) + w| := by ring_nf
      _ ≤ |g - (v.1 + w)| + |w| := abs_add_le _ _
      _ < (2 : ℝ) ^ (-1075 : ℤ) * 2 ^ (55 : ℕ) := by nlinarith
  -- both are multiples of `2^{-1020}`
  have hmv : Mult (-1020) v.1 := mult_of_F p hv.1 (by
    rw [hp, show (-1020 + 53 - 1 : ℤ) = -968 by norm_num]
    rw [e4] at hlo
    rw [e3]
    nlinarith)
  have hmg : Mult (-1020) g := mult_of_F p hgF (by
    rw [hp, show (-1020 + 53 - 1 : ℤ) = -968 by norm_num]
    have := abs_sub_abs_le_abs_sub v.1 g
    rw [abs_sub_comm] at this
    rw [e4] at hlo
    rw [e2] at hgv
    rw [e3]
    nlinarith)
  obtain ⟨kv, hkv⟩ := hmv
  obtain ⟨kg, hkg⟩ := hmg
  have hpos2 : (0 : ℝ) < (2 : ℝ) ^ (-1020 : ℤ) := by positivity
  have hk : |((kg - kv : ℤ) : ℝ)| < 1 := by
    have : g - v.1 = ((kg - kv : ℤ) : ℝ) * (2 : ℝ) ^ (-1020 : ℤ) := by rw [hkg, hkv]; push_cast; ring
    rw [this, abs_mul, abs_of_pos hpos2] at hgv
    nlinarith [abs_nonneg ((kg - kv : ℤ) : ℝ)]
  have hk0 : kg - kv = 0 := by
    rw [← Int.cast_abs] at hk
    have : |kg - kv| < 1 := by exact_mod_cast hk
    have h0 := abs_nonneg (kg - kv)
    exact abs_eq_zero.mp (by omega)
  rw [hkg, hkv, show kg = kv by omega]

/-- Theorem 40 (`thm:exp`) read with `n = 2`, for a case, with binary64's subnormals and no overflow: every scaling
rounds each part by `S`, which keeps a value or rounds one below `2^{-1022}` to a multiple of `2^{-1074}` within
`η_0 = 2^{-1075}`, and the last scaling, by `2^k`, is in two steps, `2^{k₁}` then `2^{k₂}` with `k₂ ≤ 0`. The
factors of a product are scaled exactly, as in Lemma 33, which binary64 does where it scales them up, as a run does.
Then `|y - e^x| ≤ ε e^x + 2^{-1073}`, with step (3)'s `2η_0` in `ε`; the floor of the scaling back is `2^{-967}` -/
theorem dd_thm40_case_sub (hp : p = 53) {O : DWOps} (hO : DWSpec p O) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (r : ℝ × ℝ) (hr : DW p r) (X : ℝ) (k₁ k₂ : ℤ) (hk : k₂ ≤ 0) (δ : ℝ)
    (hδ : |dwVal r - (X - (k₁ + k₂ : ℤ) * Real.log 2)| ≤ δ) (a b : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ |dwVal r|)
    (hb : |dwVal r| ≤ b) (e : ℤ) (d' : ℕ) (hd : 1 ≤ d') (hbd : b < d' + 2) (Fk : ℕ → ℝ × ℝ)
    (hF : ∀ k, DW p (Fk k)) (φ : ℕ → ℝ) (hφ : ∀ k, |dwVal (Fk k) - invF k| ≤ φ k) (pos : Bool)
    (hsgn : if pos then 0 ≤ dwVal r else dwVal r ≤ 0)
    (hlo : d' ≠ 1 → (2 : ℝ) ^ (-967 : ℤ) * (1 + u p) ≤ a / (1 + a) - ddCoreE p (coreT pos b 0) 0 b φ d') :
    |S ((2 : ℝ) ^ k₂ * S ((2 : ℝ) ^ k₁ * (O.addF (ddExpT O (fun v => (S v.1, S v.2)) e r Fk d') 1).1)) +
        S ((2 : ℝ) ^ k₂ * S ((2 : ℝ) ^ k₁ * (O.addF (ddExpT O (fun v => (S v.1, S v.2)) e r Fk d') 1).2)) -
          Real.exp X| ≤
      ddExpEps p ((2 : ℝ) ^ (-1075 : ℤ)) pos a b δ φ d' * Real.exp X + (2 : ℝ) ^ (-1073 : ℤ) := by
  have hS0 := Scl.of_grid p hp S hS
  have hu : 4 * u p < 1 := by
    unfold u
    rw [hp]
    norm_num
  have h := dd_thm40_case p hO hu (SclDW.of_grid p hp S hS) (hS0.two_step p hk) r hr X (k₁ + k₂) δ hδ a b ha0 ha hb
    e d' hd hbd Fk hF φ hφ pos hsgn hlo
  have hsc : ∀ s : ℝ, (2 : ℝ) ^ (-k₂) * ((2 : ℝ) ^ (k₁ + k₂) * s) = (2 : ℝ) ^ k₁ * s := fun s => by
    rw [← mul_assoc, ← zpow_add₀ two_ne_zero, show -k₂ + (k₁ + k₂) = k₁ by ring]
  have h2 : (2 : ℝ) * ((2 : ℝ) * (2 : ℝ) ^ (-1075 : ℤ)) = (2 : ℝ) ^ (-1073 : ℤ) := by
    rw [show (-1073 : ℤ) = 1 + (1 + -1075) by norm_num, zpow_add₀ two_ne_zero, zpow_add₀ two_ne_zero, zpow_one]
  simp only [hsc, h2] at h
  exact h

end ExpansionBounds
