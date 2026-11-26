import ExpansionBounds.DDLogThm

/-!
# Proposition 44 (`prop:ddexplog`): `DD::ln` for a case, with binary64's subnormals

Every scaling of `DD::ln` rounds each part by `S`, which keeps a value or rounds one below `2^{-1022}` to a multiple
of `2^{-1074}` within `η_0 = 2^{-1075}`, but for the factors of a product, scaled exactly as in Lemma 33. The
scaling of `x` by `2^k` and the scaling back of step (4)'s product are
in two steps, the second by `2^j` with `j ≤ 0`; as a function of the exactly scaled pair they are `ddS2 S j`, which
moves a part by at most `2η_0` and keeps a double word whose high part is at least `2^{-967}` (`SclDW.two_step`), as
the one-step scaling does (`SclDW.of_grid`). So Theorem 42 for a case holds with `η = η_c = η_0`,
`η_x = η_p = 2η_0`, the paper's terms in `η_0`, and every floor `2^{-967}` (`dd_thm42_case_sub`).
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ)

/-- a scaling in two steps, the second by `2^j`, each part rounded by `S` at both, as a function of the exactly
scaled pair -/
noncomputable def ddS2 (S : ℝ → ℝ) (j : ℤ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (S ((2 : ℝ) ^ j * S ((2 : ℝ) ^ (-j) * v.1)), S ((2 : ℝ) ^ j * S ((2 : ℝ) ^ (-j) * v.2)))

/-- on `2^{i+j} x` it is the two scalings in a row, by `2^i` and then by `2^j` -/
theorem ddS2_apply (S : ℝ → ℝ) (i j : ℤ) (x : ℝ × ℝ) :
    ddS2 S j (dwScale (i + j) x) =
      (S ((2 : ℝ) ^ j * S ((2 : ℝ) ^ i * x.1)), S ((2 : ℝ) ^ j * S ((2 : ℝ) ^ i * x.2))) := by
  have hsc : ∀ s : ℝ, (2 : ℝ) ^ (-j) * ((2 : ℝ) ^ (i + j) * s) = (2 : ℝ) ^ i * s := fun s => by
    rw [← mul_assoc, ← zpow_add₀ two_ne_zero, show -j + (i + j) = i by ring]
  simp only [ddS2, dwScale, hsc]

variable [Prec_gt_0 p]

/-- at `p = 53`, a float `v_h` of magnitude at least `2^{-967}` is the rounding of `v_h + w` for `|w| < 2^{-1021}`:
the floats around `v_h` are multiples of `2^{-1020}` -/
theorem rn_add_small (hp : p = 53) {v1 w : ℝ} (hv1 : F p v1) (hlo : (2 : ℝ) ^ (-967 : ℤ) ≤ |v1|)
    (hwb : |w| < (2 : ℝ) ^ (-1075 : ℤ) * 2 ^ (54 : ℕ)) : RN p (v1 + w) = v1 := by
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
  obtain ⟨g, hg⟩ : ∃ g, g = RN p (v1 + w) := ⟨_, rfl⟩
  rw [← hg]
  have hgF : F p g := hg ▸ F_RN p _
  have hn := (RN_nearest p (v1 + w)).2 v1 hv1
  rw [← hg, show v1 - (v1 + w) = -w by ring, abs_neg] at hn
  have hgv : |g - v1| < (2 : ℝ) ^ (-1020 : ℤ) := by
    rw [e2]
    calc |g - v1| = |(g - (v1 + w)) + w| := by ring_nf
      _ ≤ |g - (v1 + w)| + |w| := abs_add_le _ _
      _ < (2 : ℝ) ^ (-1075 : ℤ) * 2 ^ (55 : ℕ) := by nlinarith
  -- both are multiples of `2^{-1020}`
  have hmv : Mult (-1020) v1 := mult_of_F p hv1 (by
    rw [hp, show (-1020 + 53 - 1 : ℤ) = -968 by norm_num]
    rw [e4] at hlo
    rw [e3]
    nlinarith)
  have hmg : Mult (-1020) g := mult_of_F p hgF (by
    rw [hp, show (-1020 + 53 - 1 : ℤ) = -968 by norm_num]
    have := abs_sub_abs_le_abs_sub v1 g
    rw [abs_sub_comm] at this
    rw [e4] at hlo
    rw [e2] at hgv
    rw [e3]
    nlinarith)
  obtain ⟨kv, hkv⟩ := hmv
  obtain ⟨kg, hkg⟩ := hmg
  have hpos2 : (0 : ℝ) < (2 : ℝ) ^ (-1020 : ℤ) := by positivity
  have hk : |((kg - kv : ℤ) : ℝ)| < 1 := by
    have : g - v1 = ((kg - kv : ℤ) : ℝ) * (2 : ℝ) ^ (-1020 : ℤ) := by rw [hkg, hkv]; push_cast; ring
    rw [this, abs_mul, abs_of_pos hpos2] at hgv
    nlinarith [abs_nonneg ((kg - kv : ℤ) : ℝ)]
  have hk0 : kg - kv = 0 := by
    rw [← Int.cast_abs] at hk
    have : |kg - kv| < 1 := by exact_mod_cast hk
    have h0 := abs_nonneg (kg - kv)
    exact abs_eq_zero.mp (by omega)
  rw [hkg, hkv, show kg = kv by omega]

/-- binary64's scaling of a double word in two steps, the second by `2^j` with `j ≤ 0`: each part moves by at most
`2η_0`, and a double word whose high part is at least `2^{-967}` stays one: its high part is kept, and its low part
is kept or ends below `2^{-1021}` -/
theorem SclDW.two_step (hp : p = 53) (S : ℝ → ℝ)
    (h : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    {j : ℤ} (hj : j ≤ 0) : SclDW p (2 * (2 : ℝ) ^ (-1075 : ℤ)) ((2 : ℝ) ^ (-967 : ℤ)) (ddS2 S j) := by
  have hS0 := Scl.of_grid p hp S h
  have hT := hS0.two_step p hj
  refine ⟨fun v => hT.err v.1, fun v => hT.err v.2, fun v hv hlo => ?_⟩
  have e1 : (2 : ℝ) ^ (-1022 : ℤ) = (2 : ℝ) ^ (-1075 : ℤ) * 2 ^ (53 : ℕ) := by
    rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]
    norm_num
  have e4 : (2 : ℝ) ^ (-967 : ℤ) = (2 : ℝ) ^ (-1075 : ℤ) * 2 ^ (108 : ℕ) := by
    rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]
    norm_num
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-1075 : ℤ) := by positivity
  have hj1 : (2 : ℝ) ^ j ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hj
  have hj0 : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hjn : (1 : ℝ) ≤ (2 : ℝ) ^ (-j) := one_le_zpow₀ (by norm_num) (by omega)
  have hsc : ∀ s : ℝ, (2 : ℝ) ^ j * ((2 : ℝ) ^ (-j) * s) = s := fun s => by
    rw [← mul_assoc, ← zpow_add₀ two_ne_zero, add_neg_cancel, zpow_zero, one_mul]
  -- a value of magnitude at least `2^{-1022}` is kept
  have hkeep : ∀ z : ℝ, (2 : ℝ) ^ (-1075 : ℤ) * 2 ^ (53 : ℕ) ≤ |z| → S z = z := fun z hz => by
    rcases h z with h1 | ⟨-, h2, -⟩
    · exact h1
    · rw [e1] at h2
      exact absurd h2 (not_lt.mpr hz)
  -- the high part is kept at both steps
  have h1 : S ((2 : ℝ) ^ j * S ((2 : ℝ) ^ (-j) * v.1)) = v.1 := by
    have ha : (2 : ℝ) ^ (-1075 : ℤ) * 2 ^ (53 : ℕ) ≤ |(2 : ℝ) ^ (-j) * v.1| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (-j))]
      rw [e4] at hlo
      nlinarith [abs_nonneg v.1]
    rw [hkeep _ ha, hsc]
    refine hkeep _ ?_
    rw [e4] at hlo
    nlinarith
  show F p (ddS2 S j v).1 ∧ F p (ddS2 S j v).2 ∧ RN p ((ddS2 S j v).1 + (ddS2 S j v).2) = (ddS2 S j v).1
  have hd1 : (ddS2 S j v).1 = v.1 := h1
  rw [hd1]
  refine ⟨hv.1, hT.mem _ hv.2.1, ?_⟩
  -- the low part is kept, or ends below `2^{-1021}`
  have hlow : (ddS2 S j v).2 = v.2 ∨ |(ddS2 S j v).2| < (2 : ℝ) ^ (-1075 : ℤ) * 2 ^ (54 : ℕ) := by
    show S ((2 : ℝ) ^ j * S ((2 : ℝ) ^ (-j) * v.2)) = v.2 ∨
      |S ((2 : ℝ) ^ j * S ((2 : ℝ) ^ (-j) * v.2))| < (2 : ℝ) ^ (-1075 : ℤ) * 2 ^ (54 : ℕ)
    rcases h ((2 : ℝ) ^ (-j) * v.2) with ha | ⟨-, ha2, ha3⟩
    · rw [ha, hsc]
      rcases h v.2 with hb | ⟨-, hb2, hb3⟩
      · exact Or.inl hb
      · refine Or.inr ?_
        have := abs_sub_abs_le_abs_sub (S v.2) v.2
        rw [e1] at hb2
        nlinarith
    · refine Or.inr ?_
      obtain ⟨c, hc⟩ : ∃ c, c = S ((2 : ℝ) ^ (-j) * v.2) := ⟨_, rfl⟩
      rw [← hc] at ha3 ⊢
      have hcb : |c| < (2 : ℝ) ^ (-1075 : ℤ) * 2 ^ (53 : ℕ) + (2 : ℝ) ^ (-1075 : ℤ) := by
        have := abs_sub_abs_le_abs_sub c ((2 : ℝ) ^ (-j) * v.2)
        rw [e1] at ha2
        linarith only [this, ha2, ha3]
      have hjc : |(2 : ℝ) ^ j * c| ≤ |c| := by
        rw [abs_mul, abs_of_pos hj0]
        exact mul_le_of_le_one_left (abs_nonneg _) hj1
      rcases h ((2 : ℝ) ^ j * c) with hb | ⟨-, -, hb3⟩
      · rw [hb]
        nlinarith
      · have := abs_sub_abs_le_abs_sub (S ((2 : ℝ) ^ j * c)) ((2 : ℝ) ^ j * c)
        nlinarith
  rcases hlow with hl | hl
  · rw [hl]
    exact hv.2.2
  · exact rn_add_small p hp hv.1 hlo hl

/-- Theorem 42 (`thm:log`) read with `n = 2`, for a case, with binary64's subnormals and no overflow: every scaling
rounds each part by `S`; `x' = 2^k x` is formed in two steps, `2^{k₁}` then `2^{k₂}` with `k₂ ≤ 0`, and step (4)'s
product is scaled back by `2^{e_φ}` and then by `2^{e_t}`, `e_t ≤ 0`. The factors of a product are scaled exactly,
as in Lemma 33, which binary64 does where it scales them up, as with the exponents that a run selects, at most 0.
Then `|y - ln x| ≤ 𝓔(ℓ)` with the paper's terms in `η_0 = 2^{-1075}`, for any `t̄`, `φ̄` and `ξ` at least the
theorem's; the hypotheses are those of `dd_thm42_case_g`, with every floor `2^{-967}` -/
theorem dd_thm42_case_sub (hp : p = 53) {O : DWOps} (hO : DWSpec p O) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℝ × ℝ) (hx : DW p x) (hX0 : 0 < dwVal x) (y0 : ℝ) (hy0 : F p y0) (ℓ E : ℝ) (hℓ : |Real.log (dwVal x)| ≤ ℓ)
    (hE : |y0 - Real.log (dwVal x)| ≤ E) (r : ℝ × ℝ) (hr : DW p r) (k₁ k₂ : ℤ) (hk2 : k₂ ≤ 0) (δ : ℝ)
    (hδ : |dwVal r - (-y0 - (k₁ + k₂ : ℤ) * Real.log 2)| ≤ δ) (a b : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ |dwVal r|)
    (hb : |dwVal r| ≤ b) (pos : Bool) (hsgn : if pos then 0 ≤ dwVal r else dwVal r ≤ 0) (e : ℤ) (d' : ℕ) (hd : 1 ≤ d')
    (hbd : b < d' + 2) (Fk : ℕ → ℝ × ℝ) (hF : ∀ k, DW p (Fk k)) (φF : ℕ → ℝ) (hφF : ∀ k, |dwVal (Fk k) - invF k| ≤ φF k)
    (hlo : d' ≠ 1 → (2 : ℝ) ^ (-967 : ℤ) * (1 + u p) ≤ a / (1 + a) - ddCoreE p (coreT pos b 0) 0 b φF d')
    (hlox : (2 : ℝ) ^ (-967 : ℤ) ≤ |(2 : ℝ) ^ (k₁ + k₂) * x.1|)
    (hφex : dwVal (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) = dwVal (ddS2 S k₂ (dwScale (k₁ + k₂) x)) - 1) (B eφ et ec : ℤ)
    (het : et ≤ 0)
    (hUφ : |(ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x).1| + |(ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x).2| < (2 : ℝ) ^ (eφ + 1))
    (hUt : |(ddExpT O (fun v => (S v.1, S v.2)) e r Fk d').1| + |(ddExpT O (fun v => (S v.1, S v.2)) e r Fk d').2| < (2
      : ℝ) ^ (et + 1))
    (hUc : |(ddLogC O (ddS2 S et) B eφ et (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) (ddExpT O (fun v => (S v.1, S v.2)) e r
      Fk d')).1| + |(ddLogC O (ddS2 S et) B eφ et (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) (ddExpT O (fun v => (S v.1, S
      v.2)) e r Fk d')).2| < (2 : ℝ) ^ (ec + 1)) (F' : ℕ → ℝ × ℝ) (hF' : ∀ k, DW p (F' k)) (φ' : ℕ → ℝ)
    (hφ' : ∀ k, |dwVal (F' k) - logFe k| ≤ φ' k) (q : ℕ) (hq : 2 ≤ q) {tb φb ξ : ℝ} (htbT : coreT pos b 0 ≤ tb)
    (hφbP : logPhiB (2 * (2 * (2 : ℝ) ^ (-1075 : ℤ))) pos E a b δ ≤ φb)
    (hξX : logXi (2 * (2 * (2 : ℝ) ^ (-1075 : ℤ))) pos E a b δ ≤ ξ) {lφ lt lc lv : ℝ} (hlφ0 : 0 ≤ lφ) (hlc0 : 0 ≤ lc)
    (hfl4 : ¬ min eφ et < -B - 13 → DW p (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) → DW p (ddExpT O (fun v => (S v.1, S v.2))
      e r Fk d') → lφ ≤ |dwVal (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x)| ∧ lt ≤ |dwVal (ddExpT O (fun v => (S v.1, S v.2)) e
      r Fk d')| ∧ (2 : ℝ) ^ (-967 : ℤ) * (1 + u p) ≤ (1 - eP p) * (lφ * lt))
    (hfl5 : ¬ ec < -B - 13 → DW p (ddLogC O (ddS2 S et) B eφ et (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) (ddExpT O (fun v =>
      (S v.1, S v.2)) e r Fk d')) → lc ≤ |dwVal (ddLogC O (ddS2 S et) B eφ et (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x)
      (ddExpT O (fun v => (S v.1, S v.2)) e r Fk d'))| ∧ (∀ j, 2 ≤ j → j ≤ q → lv ≤ 1 / (j : ℝ) - (Real.exp E - 1 +
      ddLogEc p (2 * (2 * (2 : ℝ) ^ (-1075 : ℤ))) (2 * (2 * (2 : ℝ) ^ (-1075 : ℤ))) φb tb (ddCoreE p tb ((2 : ℝ) ^
      (-1075 : ℤ)) b φF d') E δ b ξ B) * logV (Real.exp E - 1 + ddLogEc p (2 * (2 * (2 : ℝ) ^ (-1075 : ℤ))) (2 * (2 * (2
      : ℝ) ^ (-1075 : ℤ))) φb tb (ddCoreE p tb ((2 : ℝ) ^ (-1075 : ℤ)) b φF d') E δ b ξ B) q (j + 1) - ddHornerB p
      (Real.exp E - 1 + ddLogEc p (2 * (2 * (2 : ℝ) ^ (-1075 : ℤ))) (2 * (2 * (2 : ℝ) ^ (-1075 : ℤ))) φb tb (ddCoreE p
      tb ((2 : ℝ) ^ (-1075 : ℤ)) b φF d') E δ b ξ B) (2 * (2 : ℝ) ^ (-1075 : ℤ)) φ' (logV (Real.exp E - 1 + ddLogEc p (2
      * (2 * (2 : ℝ) ^ (-1075 : ℤ))) (2 * (2 * (2 : ℝ) ^ (-1075 : ℤ))) φb tb (ddCoreE p tb ((2 : ℝ) ^ (-1075 : ℤ)) b φF
      d') E δ b ξ B) q) q (q - j)) ∧ (2 : ℝ) ^ (-967 : ℤ) * (1 + u p) ≤ (1 - eP p) * (lc * lv) ∧ (2 : ℝ) ^ (-967 : ℤ) *
      (1 + u p) ≤ (1 - eP p) * (lc * ((1 - eF p) * (1 - ddLogHb p (2 * (2 : ℝ) ^ (-1075 : ℤ)) (Real.exp E - 1 + ddLogEc
      p (2 * (2 * (2 : ℝ) ^ (-1075 : ℤ))) (2 * (2 * (2 : ℝ) ^ (-1075 : ℤ))) φb tb (ddCoreE p tb ((2 : ℝ) ^ (-1075 : ℤ))
      b φF d') E δ b ξ B) φ' q))))
    (hC : Real.exp E - 1 + ddLogEc p (2 * (2 * (2 : ℝ) ^ (-1075 : ℤ))) (2 * (2 * (2 : ℝ) ^ (-1075 : ℤ))) φb tb (ddCoreE
      p tb ((2 : ℝ) ^ (-1075 : ℤ)) b φF d') E δ b ξ B < 1) :
    |dwVal (ddLogOp O (ddS2 S k₂) (ddS2 S et) (fun v => (S v.1, S v.2)) y0 x (k₁ + k₂) (ddExpT O (fun v => (S v.1, S
      v.2)) e r Fk d') B eφ et ec F' q) - Real.log (dwVal x)| ≤ ddLogBoundG p ((2 : ℝ) ^ (-1075 : ℤ)) (2 * (2 : ℝ) ^
      (-1075 : ℤ)) (2 * (2 : ℝ) ^ (-1075 : ℤ)) ((2 : ℝ) ^ (-1075 : ℤ)) ℓ E tb φb ξ b δ φF d' φ' q B := by
  have hu : 4 * u p < 1 := by
    unfold u
    rw [hp]
    norm_num
  exact dd_thm42_case_g p hO hu (SclDW.of_grid p hp S hS) (SclDW.two_step p hp S hS hk2)
    (SclDW.two_step p hp S hS het) (SclDW.of_grid p hp S hS) x hx hX0 y0 hy0 ℓ E hℓ hE r hr (k₁ + k₂) δ hδ a b ha0
    ha hb pos hsgn e d' hd hbd Fk hF φF hφF hlo hlox hφex B eφ et ec hUφ hUt hUc F' hF' φ' hφ' q hq htbT hφbP hξX
    hlφ0 hlc0 hfl4 hfl5 hC

end ExpansionBounds
