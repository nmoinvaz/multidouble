import ExpansionBounds.DDOps

/-!
# Proposition 44 (`prop:ddexplog`): the reduction of `DD::exp`

Lemma 38 (`lem:expred`) read with `n = 2`. For a double word `x`, step (1)'s `k` is that of EXP, and for `k ≠ 0`

  `r = DWPlusFP(DWPlusFP(P, x_l), x_h - k c_h)`, `P = DWTimesFP3(c_ℓ, -k)`,

with `c_ℓ` a double word and `η_ℓ = |ln 2 - c_h - c_ℓ|`. With `k̄ = 1075`, `|x_l| ≤ x̄_t` and `|r_e| ≤ r̄` for
`r_e = x - k ln 2`, the proposition's error of the reduction is `e_M k̄|c_ℓ|` for `P`, `e_F` times the magnitudes of the
two sums, and `k̄η_ℓ`:

  `ε_1 = e_M k̄|c_ℓ|`, `ε_q = e_F(k̄|c_ℓ| + ε_1 + x̄_t)`, `ε_2 = e_F(r̄ + k̄η_ℓ + ε_1 + ε_q)`,
  `δ = ε_1 + ε_q + ε_2 + k̄η_ℓ`,

the `dr` of `Exp.reduce` in `explog_consts.py` for double words (`e1`, `eq`, its first `e2`), before its roundings up.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ)

/-- `η_ℓ = |ln 2 - c_h - c_ℓ|` for the double word `c_ℓ` -/
noncomputable def ddEtaL (ch : ℝ) (cl : ℝ × ℝ) : ℝ := |Real.log 2 - ch - dwVal cl|

/-- `ε_1 = e_M k̄|c_ℓ|`, the error of `P = DWTimesFP3(c_ℓ, -k)` -/
noncomputable def ddRedE1 (cl : ℝ × ℝ) : ℝ := eM p * (1075 * |dwVal cl|)

/-- `ε_q = e_F(k̄|c_ℓ| + ε_1 + x̄_t)`, the error of `Q = DWPlusFP(P, x_l)` -/
noncomputable def ddRedEq (cl : ℝ × ℝ) (xt : ℝ) : ℝ := eF p * (1075 * |dwVal cl| + ddRedE1 p cl + xt)

/-- `ε_2 = e_F(r̄ + k̄η_ℓ + ε_1 + ε_q)`, the error of `r = DWPlusFP(Q, x_h - k c_h)` -/
noncomputable def ddRedE2 (ch : ℝ) (cl : ℝ × ℝ) (xt rb : ℝ) : ℝ :=
  eF p * (rb + 1075 * ddEtaL ch cl + ddRedE1 p cl + ddRedEq p cl xt)

/-- `δ = ε_1 + ε_q + ε_2 + k̄η_ℓ`, the reduction's error -/
noncomputable def ddRedDelta (ch : ℝ) (cl : ℝ × ℝ) (xt rb : ℝ) : ℝ :=
  ddRedE1 p cl + ddRedEq p cl xt + ddRedE2 p ch cl xt rb + 1075 * ddEtaL ch cl

/-- step (1)'s `r` on double words: `x` for `k = 0`, otherwise
`DWPlusFP(DWPlusFP(DWTimesFP3(c_ℓ, -k), x_l), x_h - k c_h)` -/
noncomputable def ddExpR (O : DWOps) (x : ℝ × ℝ) (ch : ℝ) (cl : ℝ × ℝ) : ℝ × ℝ :=
  if expK p x.1 = 0 then x
  else O.addF (O.addF (O.mulF cl (-(expK p x.1 : ℝ))) x.2) (x.1 - expK p x.1 * ch)

variable [Prec_gt_0 p]

/-- Lemma 38 (a) (`lem:expred`) read with `n = 2`: `|k| ≤ k̄ = 1075`, `|r_e| ≤ r̄_max` and `|x_h - k c_h| ≤ α_0`, and
for `k ≠ 0`, `x_h - k c_h ∈ F` -/
theorem dd_expred_a (hp : 14 ≤ p) (x : ℝ × ℝ) (hx0 : F p x.1) (X xt ch : ℝ) (hX : |x.1| ≤ X) (hX1 : X ≤ 745.3)
    (hxt : |x.2| ≤ xt) (hch : Mult (-p - 1) ch) (hA0 : expA0 p X xt ch < 1 / 2) :
    |expK p x.1| ≤ 1075 ∧ |dwVal x - expK p x.1 * Real.log 2| ≤ rMax p X xt ∧
      |x.1 - expK p x.1 * ch| ≤ expA0 p X xt ch ∧ (expK p x.1 ≠ 0 → F p (x.1 - expK p x.1 * ch)) := by
  have hs : ∑ i ∈ range 2, (fun i : ℕ => if i = 0 then x.1 else x.2) i = x.1 + x.2 := by
    simp [sum_range_succ]
  have h := lemma_expred_a p 2 hp (fun i => if i = 0 then x.1 else x.2) (by simpa using hx0) X xt ch
    (by simpa using hX) hX1 (by rw [hs]; simpa using hxt) hch hA0
  rw [hs] at h
  simpa [dwVal] using h

/-- Proposition 44's reduction, Lemma 38 (b) (`lem:expred`) read with `n = 2`: for `k ≠ 0` and `|r_e| ≤ r̄`, the
double word `r = DWPlusFP(DWPlusFP(DWTimesFP3(c_ℓ, -k), x_l), x_h - k c_h)` satisfies
`|r - r_e| ≤ δ = ε_1 + ε_q + ε_2 + k̄η_ℓ` -/
theorem dd_expred_b (hp : 14 ≤ p) {O : DWOps} (hO : DWSpec p O) (x : ℝ × ℝ) (hx : DW p x) (X xt ch : ℝ)
    (cl : ℝ × ℝ) (hcl : DW p cl) (hX : |x.1| ≤ X) (hX1 : X ≤ 745.3) (hxt : |x.2| ≤ xt) (hch : Mult (-p - 1) ch)
    (hA0 : expA0 p X xt ch < 1 / 2) (hk : expK p x.1 ≠ 0) (rb : ℝ)
    (hrb : |dwVal x - expK p x.1 * Real.log 2| ≤ rb) :
    |dwVal (ddExpR p O x ch cl) - (dwVal x - expK p x.1 * Real.log 2)| ≤ ddRedDelta p ch cl xt rb ∧
      DW p (ddExpR p O x ch cl) := by
  obtain ⟨hkb, -, -, hF0⟩ := dd_expred_a p hp x hx.1 X xt ch hX hX1 hxt hch hA0
  obtain ⟨k, hkdef⟩ : ∃ k, k = expK p x.1 := ⟨_, rfl⟩
  rw [← hkdef] at hk hkb hF0 hrb ⊢
  obtain ⟨P, hP⟩ : ∃ P, P = O.mulF cl (-(k : ℝ)) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = O.addF P x.2 := ⟨_, rfl⟩
  have hr : ddExpR p O x ch cl = O.addF Q (x.1 - k * ch) := by
    simp only [ddExpR, ← hkdef, hk, ↓reduceIte, hQ, hP]
  rw [hr]
  have hkb' : |(k : ℝ)| ≤ 1075 := by rw [← Int.cast_abs]; exact_mod_cast hkb
  -- `-k ∈ F`, as `|k| < 2^p`
  have hkF : F p (-(k : ℝ)) := by
    refine F_of_mult p (E := 0) ⟨-k, by push_cast; ring⟩ ?_
    rw [abs_neg, zero_add]
    calc |(k : ℝ)| ≤ 1075 := hkb'
      _ < (2 : ℝ) ^ (14 : ℤ) := by norm_num
      _ ≤ (2 : ℝ) ^ p := zpow_le_zpow_right₀ (by norm_num) hp
  have heM := eM_nonneg p
  have heF := eF_nonneg p
  obtain ⟨C, hC⟩ : ∃ C, C = dwVal cl := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log 2 := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = dwVal x := ⟨_, rfl⟩
  rw [← hL, ← hS] at hrb ⊢
  have hCk : |C * -(k : ℝ)| ≤ 1075 * |C| := by
    rw [abs_mul, abs_neg, mul_comm]
    exact mul_le_mul_of_nonneg_right hkb' (abs_nonneg _)
  have heta : |(k : ℝ) * (L - ch - C)| ≤ 1075 * ddEtaL ch cl := by
    unfold ddEtaL
    rw [← hL, ← hC, abs_mul]
    exact mul_le_mul_of_nonneg_right hkb' (abs_nonneg _)
  -- `P = DWTimesFP3(c_ℓ, -k)`, within `ε_1` of `-k c_ℓ`
  have hPdw : DW p P := hP ▸ hO.mulF_dw cl _ hcl hkF
  have hP1 : |dwVal P - C * -(k : ℝ)| ≤ ddRedE1 p cl := by
    have h := hO.mulF_err cl _ hcl hkF
    rw [← hP, ← hC] at h
    unfold ddRedE1
    rw [← hC]
    exact h.trans (mul_le_mul_of_nonneg_left hCk heM)
  -- `Q = DWPlusFP(P, x_l)`, within `ε_q` of `P + x_l`
  have hQdw : DW p Q := hQ ▸ hO.addF_dw P _ hPdw hx.2.1
  have hQ1 : |dwVal Q - (dwVal P + x.2)| ≤ ddRedEq p cl xt := by
    have h := hO.addF_err P _ hPdw hx.2.1
    rw [← hQ] at h
    have hZ : |dwVal P + x.2| ≤ 1075 * |dwVal cl| + ddRedE1 p cl + xt := by
      rw [← hC]
      calc |dwVal P + x.2| = |C * -(k : ℝ) + (dwVal P - C * -(k : ℝ)) + x.2| := by ring_nf
        _ ≤ |C * -(k : ℝ)| + |dwVal P - C * -(k : ℝ)| + |x.2| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ 1075 * |C| + ddRedE1 p cl + xt := add_le_add (add_le_add hCk hP1) hxt
    exact h.trans (mul_le_mul_of_nonneg_left hZ heF)
  -- the exact sum that the last DWPlusFP rounds: `r_e + k(ln 2 - c_h - c_ℓ)` plus the two errors
  have hsum : dwVal Q + (x.1 - k * ch) =
      (S - k * L) + k * (L - ch - C) + (dwVal P - C * -(k : ℝ)) + (dwVal Q - (dwVal P + x.2)) := by
    simp only [hS, dwVal]
    ring
  have hZ2 : |dwVal Q + (x.1 - k * ch)| ≤ rb + 1075 * ddEtaL ch cl + ddRedE1 p cl + ddRedEq p cl xt := by
    rw [hsum]
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add hrb heta)) hP1)) hQ1)
  have hR1 : |dwVal (O.addF Q (x.1 - k * ch)) - (dwVal Q + (x.1 - k * ch))| ≤ ddRedE2 p ch cl xt rb :=
    (hO.addF_err Q _ hQdw (hF0 hk)).trans (mul_le_mul_of_nonneg_left hZ2 heF)
  refine ⟨?_, hO.addF_dw Q _ hQdw (hF0 hk)⟩
  have hsplit : dwVal (O.addF Q (x.1 - k * ch)) - (S - k * L) =
      (dwVal (O.addF Q (x.1 - k * ch)) - (dwVal Q + (x.1 - k * ch))) + k * (L - ch - C) +
        (dwVal P - C * -(k : ℝ)) + (dwVal Q - (dwVal P + x.2)) := by
    rw [hsum]
    ring
  rw [hsplit]
  unfold ddRedDelta
  calc _ ≤ ddRedE2 p ch cl xt rb + 1075 * ddEtaL ch cl + ddRedE1 p cl + ddRedEq p cl xt :=
        (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
          (add_le_add hR1 heta)) hP1)) hQ1)
    _ = ddRedE1 p cl + ddRedEq p cl xt + ddRedE2 p ch cl xt rb + 1075 * ddEtaL ch cl := by ring

end ExpansionBounds
