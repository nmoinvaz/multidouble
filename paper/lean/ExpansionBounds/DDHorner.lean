import ExpansionBounds.DDOps
import ExpansionBounds.DWDiv

/-!
# Proposition 44 (`prop:ddexplog`): Horner's rule on double words

Lemma 33 (`lem:horner`) read with `n = 2`, with no part bounds and each `G_OP`'s error replaced by `e_OP Z̄`:
`p_d = F_d` and `p_k = ADD(F_k, M(p_{k+1}))`, where `M` multiplies by a double word of value `z`, `|z| ≤ z̄`, within
`e_P|z p| + D`. `D = 0` for DWTimesDW2 itself, and `D = 2η_0` for a product formed on a factor scaled by a power of
two and scaled back with a loss of at most `η_0` per part. With `|F_k - F^e_k| ≤ φ_k` and `v_k ≥ |p^e_k|`,

  `ε^p_k = e_P z̄(v_{k+1} + e_{k+1}) + D`, `D_k = z̄ e_{k+1} + φ_k + ε^p_k`, `e_k = D_k + e_A(v_k + D_k)`, `e_d = φ_d`,

the recursion of `qe` in `Exp.core` and of `he` in `Log.series` of `explog_consts.py`, before their roundings up.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ)

/-- Horner's rule on double words with the product `M` by `z`: `ddHornerP j` is `p_{d-j}`, with `p_d = F_d` and
`p_k = ADD(F_k, M(p_{k+1}))` -/
noncomputable def ddHornerP (O : DWOps) (M : ℝ × ℝ → ℝ × ℝ) (Fk : ℕ → ℝ × ℝ) (d : ℕ) : ℕ → ℝ × ℝ
  | 0 => Fk d
  | j + 1 => O.add (Fk (d - (j + 1))) (M (ddHornerP O M Fk d j))

/-- the bound `e_{d-j}`: `e_d = φ_d`, then `ε^p_k = e_P z̄(v_{k+1} + e_{k+1}) + D`, `D_k = z̄ e_{k+1} + φ_k + ε^p_k`
and `e_k = D_k + e_A(v_k + D_k)` -/
noncomputable def ddHornerB (zb D : ℝ) (φ v : ℕ → ℝ) (d : ℕ) : ℕ → ℝ
  | 0 => φ d
  | j + 1 =>
    let k := d - (j + 1)
    let e1 := ddHornerB zb D φ v d j
    let Dk := zb * e1 + φ k + (eP p * (zb * (v (k + 1) + e1)) + D)
    Dk + eA p * (v k + Dk)

variable [Prec_gt_0 p]

/-- a scaling by a power of two keeps a double word -/
theorem DW.scale {x : ℝ × ℝ} (hx : DW p x) (k : ℤ) : DW p ((2 : ℝ) ^ k * x.1, (2 : ℝ) ^ k * x.2) :=
  ⟨F_zpow_mul p k hx.1, F_zpow_mul p k hx.2.1, by
    show RN p ((2 : ℝ) ^ k * x.1 + (2 : ℝ) ^ k * x.2) = (2 : ℝ) ^ k * x.1
    rw [← mul_add, RN_zpow_mul, hx.2.2]⟩

/-- a float with a zero low part is a double word -/
theorem DW.of_F {y : ℝ} (hy : F p y) : DW p (y, 0) :=
  ⟨hy, F_zero p, by
    show RN p (y + 0) = y
    rw [add_zero, RN_of_F p hy]⟩

/-- `|x_l| ≤ u|x_h|` and `|x_h| ≤ (1 + u)|x|` for a double word -/
theorem DW.parts {x : ℝ × ℝ} (hx : DW p x) : |x.2| ≤ u p * |x.1| ∧ |x.1| ≤ (1 + u p) * |dwVal x| :=
  ⟨dw_lo_le_u p hx.2.2, by
    have h := abs_RN_le p (x.1 + x.2)
    rwa [hx.2.2] at h⟩

omit [Prec_gt_0 p] in
/-- Lemma 33 (`lem:horner`) read with `n = 2`, by steps: for a product `M` by `z` within `e_P|z b| + D` on the double
words `b` that satisfy `A`, each `p_{d-j}` whose predecessors satisfy `A` is a double word within `e_{d-j}` of
`p^e_{d-j}` -/
theorem dd_horner_step {O : DWOps} (hO : DWSpec p O) (hu : 4 * u p < 1) {M : ℝ × ℝ → ℝ × ℝ}
    {A : ℝ × ℝ → Prop} {ze zb D : ℝ} (hzb : |ze| ≤ zb)
    (hM : ∀ b, DW p b → A b → DW p (M b) ∧ |dwVal (M b) - ze * dwVal b| ≤ eP p * |ze * dwVal b| + D)
    (Fk : ℕ → ℝ × ℝ) (hF : ∀ k, DW p (Fk k)) (Fe φ v : ℕ → ℝ) (hφ : ∀ k, |dwVal (Fk k) - Fe k| ≤ φ k)
    (d k0 : ℕ) (hv : ∀ k, k0 ≤ k → k ≤ d → |hornerE Fe ze d k| ≤ v k) :
    ∀ j, j ≤ d - k0 → (∀ i < j, A (ddHornerP O M Fk d i)) →
      |dwVal (ddHornerP O M Fk d j) - hornerE Fe ze d (d - j)| ≤ ddHornerB p zb D φ v d j ∧
        DW p (ddHornerP O M Fk d j) := by
  have heA := eA_nonneg p hu
  have heP := eP_nonneg p
  have hzb0 : 0 ≤ zb := (abs_nonneg _).trans hzb
  intro j
  induction j with
  | zero =>
    intro _ _
    have h0 : hornerE Fe ze d d = Fe d := by simp [hornerE]
    simp only [ddHornerP, ddHornerB, Nat.sub_zero]
    rw [h0]
    exact ⟨hφ d, hF d⟩
  | succ j ih =>
    intro hj hA
    obtain ⟨h1, hdw⟩ := ih (by omega) (fun i hi => hA i (by omega))
    obtain ⟨k, hkdef⟩ : ∃ k, k = d - (j + 1) := ⟨_, rfl⟩
    have hk1 : d - j = k + 1 := by omega
    rw [hk1] at h1
    obtain ⟨hMdw, hMe⟩ := hM _ hdw (hA j (by omega))
    obtain ⟨q, hq⟩ : ∃ q, q = ddHornerP O M Fk d j := ⟨_, rfl⟩
    obtain ⟨e1, he1⟩ : ∃ e1, e1 = ddHornerB p zb D φ v d j := ⟨_, rfl⟩
    rw [← hq] at h1 hdw hMdw hMe
    rw [← he1] at h1
    have hstepP : ddHornerP O M Fk d (j + 1) = O.add (Fk k) (M q) := by rw [hq, hkdef]; rfl
    have hstepB : ddHornerB p zb D φ v d (j + 1) =
        zb * e1 + φ k + (eP p * (zb * (v (k + 1) + e1)) + D) +
          eA p * (v k + (zb * e1 + φ k + (eP p * (zb * (v (k + 1) + e1)) + D))) := by rw [he1, hkdef]; rfl
    rw [hstepP, hstepB, ← hkdef]
    obtain ⟨pe1, hpe1⟩ : ∃ pe1, pe1 = hornerE Fe ze d (k + 1) := ⟨_, rfl⟩
    have hpe : hornerE Fe ze d k = Fe k + ze * pe1 := by rw [hpe1]; exact hornerE_succ Fe ze d k (by omega)
    have hv1 : |pe1| ≤ v (k + 1) := hpe1 ▸ hv (k + 1) (by omega) (by omega)
    have hvk : |Fe k + ze * pe1| ≤ v k := hpe ▸ hv k (by omega) (by omega)
    rw [← hpe1] at h1
    rw [hpe]
    -- the product: `|z p_{k+1}| ≤ z̄(v_{k+1} + e_{k+1})`
    have hq1 : |dwVal q| ≤ v (k + 1) + e1 := by
      calc |dwVal q| = |pe1 + (dwVal q - pe1)| := by ring_nf
        _ ≤ |pe1| + |dwVal q - pe1| := abs_add_le _ _
        _ ≤ v (k + 1) + e1 := add_le_add hv1 h1
    have hzq : |ze * dwVal q| ≤ zb * (v (k + 1) + e1) := by
      rw [abs_mul]
      exact mul_le_mul hzb hq1 (abs_nonneg _) hzb0
    have hm : |dwVal (M q) - ze * dwVal q| ≤ eP p * (zb * (v (k + 1) + e1)) + D :=
      hMe.trans (add_le_add (mul_le_mul_of_nonneg_left hzq heP) le_rfl)
    have hze1 : |ze * (dwVal q - pe1)| ≤ zb * e1 := by
      rw [abs_mul]
      exact mul_le_mul hzb h1 (abs_nonneg _) hzb0
    -- the exact sum that ADD rounds, within `D_k` of `p^e_k`
    have hS : dwVal (Fk k) + dwVal (M q) - (Fe k + ze * pe1) =
        ze * (dwVal q - pe1) + (dwVal (Fk k) - Fe k) + (dwVal (M q) - ze * dwVal q) := by ring
    have hSd : |dwVal (Fk k) + dwVal (M q) - (Fe k + ze * pe1)| ≤
        zb * e1 + φ k + (eP p * (zb * (v (k + 1) + e1)) + D) := by
      rw [hS]
      exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hze1 (hφ k))) hm)
    have hSb : |dwVal (Fk k) + dwVal (M q)| ≤ v k + (zb * e1 + φ k + (eP p * (zb * (v (k + 1) + e1)) + D)) := by
      calc |dwVal (Fk k) + dwVal (M q)| =
            |(Fe k + ze * pe1) + (dwVal (Fk k) + dwVal (M q) - (Fe k + ze * pe1))| := by ring_nf
        _ ≤ |Fe k + ze * pe1| + |dwVal (Fk k) + dwVal (M q) - (Fe k + ze * pe1)| := abs_add_le _ _
        _ ≤ _ := add_le_add hvk hSd
    have hadd := (hO.add_err (Fk k) (M q) (hF k) hMdw).trans (mul_le_mul_of_nonneg_left hSb heA)
    refine ⟨?_, hO.add_dw _ _ (hF k) hMdw⟩
    calc |dwVal (O.add (Fk k) (M q)) - (Fe k + ze * pe1)| =
          |(dwVal (Fk k) + dwVal (M q) - (Fe k + ze * pe1)) +
            (dwVal (O.add (Fk k) (M q)) - (dwVal (Fk k) + dwVal (M q)))| := by ring_nf
      _ ≤ |dwVal (Fk k) + dwVal (M q) - (Fe k + ze * pe1)| +
            |dwVal (O.add (Fk k) (M q)) - (dwVal (Fk k) + dwVal (M q))| := abs_add_le _ _
      _ ≤ _ := add_le_add hSd hadd

end ExpansionBounds
