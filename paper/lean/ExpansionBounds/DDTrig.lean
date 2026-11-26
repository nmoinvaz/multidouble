import ExpansionBounds.DWTimesDW3
import ExpansionBounds.Trig8.Defs
import ExpansionBounds.SinCos
import ExpansionBounds.Kappa8

/-!
# Theorem 35 (`thm:trig`) for the double-double functions: SINR and COSR on double words

multidouble's `DD` sine, cosine and tangent run SINR and COSR on double words, with DWTimesDW3 for MUL,
AccurateDWPlusDW for ADD and DWPlusFP for ADDF. Lemma 34 (`lem:sincosr`) then holds with each `G_OP` replaced by the
operation's relative bound times a bound of its exact result, and no part bounds: `e_M = (4u² + u³/2)/(1 + u)²`,
`e_A = 3u²/(1 - 4u)` and `e_F = 2u²`, at `p = 53`. For a double word `r` with `|r| ≤ r̄ ≤ 1`, `z = MUL(r, r)` and the
coefficients `F_k` within `φ_k` of `C_k`:

  `e_{K-1} = φ_{K-1}`, `D_k = (1 + e_M)r̄² e_{k+1} + e_M r̄²|C_{k+1}| + φ_k + e_M(1 + e_M)r̄²(|C_{k+1}| + e_{k+1})`,
  `e_k = D_k + e_A(|C_k| + D_k)`, `E_t = (1 + e_M)e_1 + e_M|C_1| + e_M(1 + e_M)(|C_1| + e_1)`,

and `δ_S = e_A + (1 + e_A)(r̄²(E_t + e_M(1/6 + E_t)) + r̄^{2K}/(2K + 1)!)/(1 - r̄²/6)`,
`δ_C = e_F + (1 + e_F)(r̄²E_t + r̄^{2K}/(2K)!)/cos₋ r̄` (`dd_sinr`, `dd_cosr`). These are the recursions of
`trig_consts.py` for its double-word model, before its roundings up. The bounds are rationals, which the kernel
evaluates, and the statements cast them to the reals.
-/

namespace ExpansionBounds

open Finset

/-- `e_M = (4u² + u³/2)/(1 + u)²` at `p = 53`, the relative error of DWTimesDW3 (Muller and Rideau, 2022) -/
def ddtEM : ℚ := (4 * trig8U ^ 2 + trig8U ^ 3 / 2) / (1 + trig8U) ^ 2

/-- `e_A = 3u²/(1 - 4u)` at `p = 53`, the relative error of AccurateDWPlusDW -/
def ddtEA : ℚ := 3 * trig8U ^ 2 / (1 - 4 * trig8U)

/-- `e_F = 2u²` at `p = 53`, the relative error of DWPlusFP -/
def ddtEF : ℚ := 2 * trig8U ^ 2

/-- `15u² + 56u³` at `p = 53`, the relative error of DWDivDW2 -/
def ddtED : ℚ := 15 * trig8U ^ 2 + 56 * trig8U ^ 3

/-- Horner's bound `e_{d-j}` on double words, for `|z| ≤ (1 + e_M)R²`, `|z - z_e| ≤ e_M R²`, coefficients within `φ`
and exact sums within `v` -/
def ddtH (R2 : ℚ) (φ v : ℕ → ℚ) (d : ℕ) : ℕ → ℚ
  | 0 => φ d
  | j + 1 =>
    let k := d - (j + 1)
    let E := ddtH R2 φ v d j
    let D := (1 + ddtEM) * R2 * E + ddtEM * R2 * v (k + 1) + φ k + ddtEM * ((1 + ddtEM) * R2 * (v (k + 1) + E))
    D + ddtEA * (v k + D)

/-- `E_t`: `t = MUL(z, p_1)` is within `E_t r²` of `r² p^e_1` -/
def ddtEt (R2 : ℚ) (φ v : ℕ → ℚ) (K : ℕ) : ℚ :=
  (1 + ddtEM) * ddtH R2 φ v (K - 1) (K - 2) + ddtEM * v 1 +
    ddtEM * ((1 + ddtEM) * (v 1 + ddtH R2 φ v (K - 1) (K - 2)))

/-- `δ_S` on double words -/
def ddtDS (rb : ℚ) (φ : ℕ → ℚ) (K : ℕ) : ℚ :=
  ddtEA + (1 + ddtEA) * (rb ^ 2 * (ddtEt (rb ^ 2) φ (fun k => |sinCQ k|) K +
    ddtEM * (|sinCQ 1| + ddtEt (rb ^ 2) φ (fun k => |sinCQ k|) K)) + rb ^ (2 * K) / ((2 * K + 1).factorial : ℚ)) /
      (1 - rb ^ 2 / 6)

/-- `δ_C` on double words -/
def ddtDC (rb : ℚ) (φ : ℕ → ℚ) (K : ℕ) : ℚ :=
  ddtEF + (1 + ddtEF) * (rb ^ 2 * ddtEt (rb ^ 2) φ (fun k => |cosCQ k|) K + rb ^ (2 * K) / ((2 * K).factorial : ℚ)) /
    cosLoQ rb

theorem ddtEM_nonneg : 0 ≤ ddtEM := by
  unfold ddtEM trig8U
  positivity

theorem ddtEA_nonneg : 0 ≤ ddtEA := by
  unfold ddtEA trig8U
  norm_num

theorem ddtEF_nonneg : 0 ≤ ddtEF := by
  unfold ddtEF trig8U
  positivity

variable (p : ℤ)

/-- Horner's rule on double words: `ddtHorner j` is `p_{d-j}`, with `p_d = F_d` and
`p_k = ADD(MUL(z, p_{k+1}), F_k)` -/
noncomputable def ddtHorner (z : ℝ × ℝ) (Fk : ℕ → ℝ × ℝ) (d : ℕ) : ℕ → ℝ × ℝ
  | 0 => Fk d
  | j + 1 => accDWPlusDW p (dwTimesDW3 p z (ddtHorner z Fk d j)) (Fk (d - (j + 1)))

/-- `t = MUL(z, p_1)` with `z = MUL(r, r)`, for a series of `K` terms -/
noncomputable def ddtT (r : ℝ × ℝ) (Fk : ℕ → ℝ × ℝ) (K : ℕ) : ℝ × ℝ :=
  dwTimesDW3 p (dwTimesDW3 p r r) (ddtHorner p (dwTimesDW3 p r r) Fk (K - 1) (K - 2))

/-- SINR on double words: `2^{-e} ADD(r', MUL(r', t))` with `r' = 2^e r` -/
noncomputable def ddSinR (e : ℤ) (r : ℝ × ℝ) (Fk : ℕ → ℝ × ℝ) (K : ℕ) : ℝ × ℝ :=
  ((2 : ℝ) ^ (-e) * (accDWPlusDW p ((2 : ℝ) ^ e * r.1, (2 : ℝ) ^ e * r.2)
      (dwTimesDW3 p ((2 : ℝ) ^ e * r.1, (2 : ℝ) ^ e * r.2) (ddtT p r Fk K))).1,
    (2 : ℝ) ^ (-e) * (accDWPlusDW p ((2 : ℝ) ^ e * r.1, (2 : ℝ) ^ e * r.2)
      (dwTimesDW3 p ((2 : ℝ) ^ e * r.1, (2 : ℝ) ^ e * r.2) (ddtT p r Fk K))).2)

/-- COSR on double words: `DWPlusFP(t, 1)` -/
noncomputable def ddCosR (r : ℝ × ℝ) (Fk : ℕ → ℝ × ℝ) (K : ℕ) : ℝ × ℝ := dwPlusFP p (ddtT p r Fk K) 1

theorem cast_trig8U (hp : p = 53) : ((trig8U : ℚ) : ℝ) = u p := by
  unfold trig8U
  exact u_53_rat p hp

theorem cast_ddtEM (hp : p = 53) : ((ddtEM : ℚ) : ℝ) = (4 * u p ^ 2 + u p ^ 3 / 2) / (1 + u p) ^ 2 := by
  unfold ddtEM
  push_cast
  rw [cast_trig8U p hp]

theorem cast_ddtEA (hp : p = 53) : ((ddtEA : ℚ) : ℝ) = 3 * u p ^ 2 / (1 - 4 * u p) := by
  unfold ddtEA
  push_cast
  rw [cast_trig8U p hp]

theorem cast_ddtEF (hp : p = 53) : ((ddtEF : ℚ) : ℝ) = 2 * u p ^ 2 := by
  unfold ddtEF
  push_cast
  rw [cast_trig8U p hp]

theorem cast_ddtED (hp : p = 53) : ((ddtED : ℚ) : ℝ) = 15 * u p ^ 2 + 56 * u p ^ 3 := by
  unfold ddtED
  push_cast
  rw [cast_trig8U p hp]

variable [Prec_gt_0 p]

/-- Lemma 33 (`lem:horner`) on double words: for a double word `z` with `|z| ≤ (1 + e_M)R²` and
`|z - z_e| ≤ e_M R²`, coefficients `F_k` within `φ_k` of `F^e_k` and `|p^e_k| ≤ v_k`, each `p_{d-j}` is a double word
within `e_{d-j}` of `p^e_{d-j}` -/
theorem ddt_horner (hp : p = 53) {z : ℝ × ℝ} (hz : DW p z) {ze : ℝ} {R2 : ℚ}
    (hzb : |dwVal z| ≤ (1 + ((ddtEM : ℚ) : ℝ)) * (R2 : ℝ)) (hzd : |dwVal z - ze| ≤ ((ddtEM : ℚ) : ℝ) * (R2 : ℝ))
    (Fk : ℕ → ℝ × ℝ) (hF : ∀ k, DW p (Fk k)) (Fe : ℕ → ℝ) (φ v : ℕ → ℚ)
    (hφ : ∀ k, |dwVal (Fk k) - Fe k| ≤ (φ k : ℝ)) (d : ℕ)
    (hv : ∀ k, 1 ≤ k → k ≤ d → |hornerE Fe ze d k| ≤ (v k : ℝ)) :
    ∀ j, j ≤ d - 1 →
      |dwVal (ddtHorner p z Fk d j) - hornerE Fe ze d (d - j)| ≤ ((ddtH R2 φ v d j : ℚ) : ℝ) ∧
        DW p (ddtHorner p z Fk d j) := by
  have hp5 : 5 ≤ p := by omega
  have hp3 : 3 ≤ p := by omega
  have hM := cast_ddtEM p hp
  have hA := cast_ddtEA p hp
  have hM0 : (0 : ℝ) ≤ ((ddtEM : ℚ) : ℝ) := by exact_mod_cast ddtEM_nonneg
  have hA0 : (0 : ℝ) ≤ ((ddtEA : ℚ) : ℝ) := by exact_mod_cast ddtEA_nonneg
  obtain ⟨eM, heM⟩ : ∃ e : ℝ, e = ((ddtEM : ℚ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨eA, heA⟩ : ∃ e : ℝ, e = ((ddtEA : ℚ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = dwVal z := ⟨_, rfl⟩
  rw [← heM] at hzb hzd hM hM0
  rw [← heA] at hA hA0
  rw [← hZ] at hzb hzd
  have hzmax0 : 0 ≤ (1 + eM) * (R2 : ℝ) := (abs_nonneg _).trans hzb
  have hzd0 : 0 ≤ eM * (R2 : ℝ) := (abs_nonneg _).trans hzd
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : hornerE Fe ze d d = Fe d := by simp [hornerE]
    simp only [ddtHorner, ddtH, Nat.sub_zero]
    rw [h0]
    exact ⟨hφ d, hF d⟩
  | succ j ih =>
    intro hj
    obtain ⟨h1, hdw⟩ := ih (by omega)
    obtain ⟨k, hkdef⟩ : ∃ k, k = d - (j + 1) := ⟨_, rfl⟩
    have hk1 : d - j = k + 1 := by omega
    have hk0 : 1 ≤ k := by omega
    rw [hk1] at h1
    obtain ⟨q, hq⟩ : ∃ q, q = ddtHorner p z Fk d j := ⟨_, rfl⟩
    obtain ⟨e1, he1⟩ : ∃ e1 : ℝ, e1 = ((ddtH R2 φ v d j : ℚ) : ℝ) := ⟨_, rfl⟩
    rw [← hq] at h1 hdw
    rw [← he1] at h1
    obtain ⟨hmdw, hme⟩ := dwTimesDW3_good p hp5 hz hdw
    rw [← hM, ← hZ] at hme
    obtain ⟨m, hm⟩ : ∃ m, m = dwTimesDW3 p z q := ⟨_, rfl⟩
    rw [← hm] at hmdw hme
    obtain ⟨hadw, hae⟩ := accDWPlusDW_good p hp3 hmdw (hF k)
    rw [← hA] at hae
    have hstepP : ddtHorner p z Fk d (j + 1) = accDWPlusDW p m (Fk k) := by rw [hm, hq, hkdef]; rfl
    have hstepB : ((ddtH R2 φ v d (j + 1) : ℚ) : ℝ) =
        ((1 + eM) * R2 * e1 + eM * R2 * v (k + 1) + φ k + eM * ((1 + eM) * R2 * (v (k + 1) + e1))) +
          eA * (v k + ((1 + eM) * R2 * e1 + eM * R2 * v (k + 1) + φ k +
            eM * ((1 + eM) * R2 * (v (k + 1) + e1)))) := by
      rw [he1, heM, heA, hkdef]
      simp only [ddtH]
      push_cast
      ring
    rw [hstepP, hstepB, ← hkdef]
    obtain ⟨pe1, hpe1⟩ : ∃ pe1, pe1 = hornerE Fe ze d (k + 1) := ⟨_, rfl⟩
    have hpe : hornerE Fe ze d k = Fe k + ze * pe1 := by rw [hpe1]; exact hornerE_succ Fe ze d k (by omega)
    have hv1 : |pe1| ≤ (v (k + 1) : ℝ) := hpe1 ▸ hv (k + 1) (by omega) (by omega)
    have hvk : |Fe k + ze * pe1| ≤ (v k : ℝ) := hpe ▸ hv k hk0 (by omega)
    rw [← hpe1] at h1
    rw [hpe]
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = dwVal q := ⟨_, rfl⟩
    rw [← hQ] at h1 hme
    have hq1 : |Q| ≤ v (k + 1) + e1 := by
      calc |Q| = |pe1 + (Q - pe1)| := by ring_nf
        _ ≤ |pe1| + |Q - pe1| := abs_add_le _ _
        _ ≤ v (k + 1) + e1 := add_le_add hv1 h1
    have hzq : |Z * Q| ≤ (1 + eM) * R2 * (v (k + 1) + e1) := by
      rw [abs_mul]
      exact mul_le_mul hzb hq1 (abs_nonneg _) hzmax0
    have hm1 : |dwVal m - Z * Q| ≤ eM * ((1 + eM) * R2 * (v (k + 1) + e1)) :=
      hme.trans (mul_le_mul_of_nonneg_left hzq hM0)
    have hz1 : |Z * (Q - pe1)| ≤ (1 + eM) * R2 * e1 := by
      rw [abs_mul]
      exact mul_le_mul hzb h1 (abs_nonneg _) hzmax0
    have hz2 : |(Z - ze) * pe1| ≤ eM * R2 * v (k + 1) := by
      rw [abs_mul]
      exact mul_le_mul hzd hv1 (abs_nonneg _) hzd0
    obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (1 + eM) * R2 * e1 + eM * R2 * v (k + 1) + φ k +
        eM * ((1 + eM) * R2 * (v (k + 1) + e1)) := ⟨_, rfl⟩
    rw [← hD]
    have hS : dwVal m + dwVal (Fk k) - (Fe k + ze * pe1) =
        Z * (Q - pe1) + (Z - ze) * pe1 + (dwVal (Fk k) - Fe k) + (dwVal m - Z * Q) := by ring
    have hSd : |dwVal m + dwVal (Fk k) - (Fe k + ze * pe1)| ≤ D := by
      rw [hS, hD]
      exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
        (add_le_add ((abs_add_le _ _).trans (add_le_add hz1 hz2)) (hφ k))) hm1)
    have hSb : |dwVal m + dwVal (Fk k)| ≤ v k + D := by
      calc |dwVal m + dwVal (Fk k)| =
            |(Fe k + ze * pe1) + (dwVal m + dwVal (Fk k) - (Fe k + ze * pe1))| := by ring_nf
        _ ≤ |Fe k + ze * pe1| + |dwVal m + dwVal (Fk k) - (Fe k + ze * pe1)| := abs_add_le _ _
        _ ≤ _ := add_le_add hvk hSd
    have hadd := hae.trans (mul_le_mul_of_nonneg_left hSb hA0)
    refine ⟨?_, hadw⟩
    calc |dwVal (accDWPlusDW p m (Fk k)) - (Fe k + ze * pe1)| =
          |(dwVal m + dwVal (Fk k) - (Fe k + ze * pe1)) +
            (dwVal (accDWPlusDW p m (Fk k)) - (dwVal m + dwVal (Fk k)))| := by ring_nf
      _ ≤ |dwVal m + dwVal (Fk k) - (Fe k + ze * pe1)| +
            |dwVal (accDWPlusDW p m (Fk k)) - (dwVal m + dwVal (Fk k))| := abs_add_le _ _
      _ ≤ D + eA * (v k + D) := add_le_add hSd hadd

/-- `t = MUL(z, p_1)` on double words, for the series of `C` with alternating partial sums: `t` is a double word
within `E_t r²` of `r² p^e_1`, and `|t| ≤ (|C_1| + E_t) r²` -/
theorem ddt_t (hp : p = 53) {r : ℝ × ℝ} (hr : DW p r) {rb : ℚ} (hR : |dwVal r| ≤ (rb : ℝ)) (hrb : rb ≤ 1)
    (Fk : ℕ → ℝ × ℝ) (hF : ∀ k, DW p (Fk k)) {C : ℕ → ℝ} {CQ : ℕ → ℚ} (hC : ∀ k, ((CQ k : ℚ) : ℝ) = C k)
    (halt : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∀ d k, |hornerE C x d k| ≤ |C k|) {φ : ℕ → ℚ}
    (hφ : ∀ k, |dwVal (Fk k) - C k| ≤ (φ k : ℝ)) (K : ℕ) (hK : 2 ≤ K) :
    |dwVal (ddtT p r Fk K) - dwVal r ^ 2 * hornerE C (dwVal r ^ 2) (K - 1) 1| ≤
        ((ddtEt (rb ^ 2) φ (fun k => |CQ k|) K : ℚ) : ℝ) * dwVal r ^ 2 ∧
      |dwVal (ddtT p r Fk K)| ≤ (|C 1| + ((ddtEt (rb ^ 2) φ (fun k => |CQ k|) K : ℚ) : ℝ)) * dwVal r ^ 2 ∧
      0 ≤ ((ddtEt (rb ^ 2) φ (fun k => |CQ k|) K : ℚ) : ℝ) ∧ DW p (ddtT p r Fk K) := by
  have hp5 : 5 ≤ p := by omega
  have hM := cast_ddtEM p hp
  have hM0 : (0 : ℝ) ≤ ((ddtEM : ℚ) : ℝ) := by exact_mod_cast ddtEM_nonneg
  obtain ⟨eM, heM⟩ : ∃ e : ℝ, e = ((ddtEM : ℚ) : ℝ) := ⟨_, rfl⟩
  rw [← heM] at hM hM0
  obtain ⟨R, hRd⟩ : ∃ R, R = dwVal r := ⟨_, rfl⟩
  rw [← hRd] at hR ⊢
  have hrb0 : (0 : ℝ) ≤ rb := (abs_nonneg _).trans hR
  have hrb1 : (rb : ℝ) ≤ 1 := by exact_mod_cast hrb
  have hR2 : R ^ 2 ≤ (rb : ℝ) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hR 2
  have hR20 : 0 ≤ R ^ 2 := sq_nonneg R
  have hR21 : R ^ 2 ≤ 1 := hR2.trans (by nlinarith)
  have h1M : (0 : ℝ) ≤ 1 + eM := by linarith
  -- `z = MUL(r, r)`
  obtain ⟨hzdw, hze⟩ := dwTimesDW3_good p hp5 hr hr
  obtain ⟨z, hzd⟩ : ∃ z, z = dwTimesDW3 p r r := ⟨_, rfl⟩
  rw [← hzd] at hzdw hze
  rw [← hM, ← hRd, ← sq, abs_of_nonneg hR20] at hze
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = dwVal z := ⟨_, rfl⟩
  rw [← hZ] at hze
  have hZb : |Z| ≤ (1 + eM) * R ^ 2 := by
    have := abs_sub_abs_le_abs_sub Z (R ^ 2)
    rw [abs_of_nonneg hR20] at this
    linarith
  have hT : ddtT p r Fk K = dwTimesDW3 p z (ddtHorner p z Fk (K - 1) (K - 2)) := by rw [hzd]; rfl
  -- Horner's rule
  obtain ⟨h1, hdw⟩ := ddt_horner p hp hzdw (ze := R ^ 2) (R2 := rb ^ 2)
    (by rw [← heM, ← hZ]; push_cast; exact hZb.trans (mul_le_mul_of_nonneg_left hR2 h1M))
    (by rw [← heM, ← hZ]; push_cast; exact hze.trans (mul_le_mul_of_nonneg_left hR2 hM0))
    Fk hF C φ (fun k => |CQ k|) hφ (K - 1)
    (fun k _ _ => by push_cast; rw [hC]; exact halt _ hR20 hR21 _ _) (K - 2) (by omega)
  rw [show K - 1 - (K - 2) = 1 by omega] at h1
  obtain ⟨P, hP⟩ : ∃ P, P = hornerE C (R ^ 2) (K - 1) 1 := ⟨_, rfl⟩
  obtain ⟨p1, hp1⟩ : ∃ p1, p1 = ddtHorner p z Fk (K - 1) (K - 2) := ⟨_, rfl⟩
  obtain ⟨E1, hE1⟩ : ∃ E1 : ℝ, E1 = ((ddtH (rb ^ 2) φ (fun k => |CQ k|) (K - 1) (K - 2) : ℚ) : ℝ) := ⟨_, rfl⟩
  rw [← hP, ← hp1, ← hE1] at h1
  rw [← hp1] at hdw hT
  have hE10 : 0 ≤ E1 := (abs_nonneg _).trans h1
  have hPb : |P| ≤ |C 1| := by rw [hP]; exact halt _ hR20 hR21 _ _
  obtain ⟨htdw, hte⟩ := dwTimesDW3_good p hp5 hzdw hdw
  rw [← hM, ← hZ] at hte
  rw [hT, ← hP]
  obtain ⟨T, hTd⟩ : ∃ T, T = dwVal (dwTimesDW3 p z p1) := ⟨_, rfl⟩
  obtain ⟨P1, hP1⟩ : ∃ P1, P1 = dwVal p1 := ⟨_, rfl⟩
  rw [← hTd, ← hP1] at hte
  rw [← hP1] at h1
  rw [← hTd]
  have hEt : ((ddtEt (rb ^ 2) φ (fun k => |CQ k|) K : ℚ) : ℝ) =
      (1 + eM) * E1 + eM * |C 1| + eM * ((1 + eM) * (|C 1| + E1)) := by
    rw [hE1, heM, ← hC 1]
    unfold ddtEt
    push_cast
    ring
  obtain ⟨Et, hEtd⟩ : ∃ Et : ℝ, Et = ((ddtEt (rb ^ 2) φ (fun k => |CQ k|) K : ℚ) : ℝ) := ⟨_, rfl⟩
  rw [← hEtd] at hEt ⊢
  have hP1b : |P1| ≤ |C 1| + E1 := by
    calc |P1| = |P + (P1 - P)| := by ring_nf
      _ ≤ |P| + |P1 - P| := abs_add_le _ _
      _ ≤ _ := add_le_add hPb h1
  have hzm0 : 0 ≤ (1 + eM) * R ^ 2 := mul_nonneg h1M hR20
  have hZP : |Z * P1| ≤ (1 + eM) * R ^ 2 * (|C 1| + E1) := by
    rw [abs_mul]
    exact mul_le_mul hZb hP1b (abs_nonneg _) hzm0
  have key : |T - R ^ 2 * P| ≤ Et * R ^ 2 := by
    have e : T - R ^ 2 * P = Z * (P1 - P) + (Z - R ^ 2) * P + (T - Z * P1) := by ring
    have a1 : |Z * (P1 - P)| ≤ (1 + eM) * R ^ 2 * E1 := by
      rw [abs_mul]
      exact mul_le_mul hZb h1 (abs_nonneg _) hzm0
    have a2 : |(Z - R ^ 2) * P| ≤ eM * R ^ 2 * |C 1| := by
      rw [abs_mul]
      exact mul_le_mul hze hPb (abs_nonneg _) (mul_nonneg hM0 hR20)
    have a3 : |T - Z * P1| ≤ eM * ((1 + eM) * R ^ 2 * (|C 1| + E1)) :=
      hte.trans (mul_le_mul_of_nonneg_left hZP hM0)
    rw [e, hEt]
    calc |Z * (P1 - P) + (Z - R ^ 2) * P + (T - Z * P1)|
        ≤ |Z * (P1 - P)| + |(Z - R ^ 2) * P| + |T - Z * P1| := abs_add_three _ _ _
      _ ≤ (1 + eM) * R ^ 2 * E1 + eM * R ^ 2 * |C 1| + eM * ((1 + eM) * R ^ 2 * (|C 1| + E1)) := by linarith
      _ = _ := by ring
  have hEt0 : 0 ≤ Et := by
    rw [hEt]
    exact add_nonneg (add_nonneg (mul_nonneg h1M hE10) (mul_nonneg hM0 (abs_nonneg _)))
      (mul_nonneg hM0 (mul_nonneg h1M (add_nonneg (abs_nonneg _) hE10)))
  refine ⟨key, ?_, hEt0, htdw⟩
  calc |T| = |R ^ 2 * P + (T - R ^ 2 * P)| := by ring_nf
    _ ≤ |R ^ 2 * P| + |T - R ^ 2 * P| := abs_add_le _ _
    _ ≤ R ^ 2 * |C 1| + Et * R ^ 2 := by
        rw [abs_mul, abs_of_nonneg hR20]
        exact add_le_add (mul_le_mul_of_nonneg_left hPb hR20) key
    _ = _ := by ring

/-- Lemma 34 (`lem:sincosr`) for SINR on double words: for a double word `r` with `|r| ≤ r̄ ≤ 1` and coefficients
`F_k` within `φ_k` of `s_k`, `|SINR(r) - sin r| ≤ δ_S|sin r|`, and SINR(r) is a double word -/
theorem dd_sinr (hp : p = 53) {r : ℝ × ℝ} (hr : DW p r) {rb : ℚ} (hR : |dwVal r| ≤ (rb : ℝ)) (hrb : rb ≤ 1)
    (Fk : ℕ → ℝ × ℝ) (hF : ∀ k, DW p (Fk k)) {φ : ℕ → ℚ} (hφ : ∀ k, |dwVal (Fk k) - sinC k| ≤ (φ k : ℝ))
    (K : ℕ) (hK : 2 ≤ K) (e : ℤ) :
    |dwVal (ddSinR p e r Fk K) - Real.sin (dwVal r)| ≤ ((ddtDS rb φ K : ℚ) : ℝ) * |Real.sin (dwVal r)| ∧
      0 ≤ ((ddtDS rb φ K : ℚ) : ℝ) ∧ DW p (ddSinR p e r Fk K) := by
  have hp5 : 5 ≤ p := by omega
  have hp3 : 3 ≤ p := by omega
  have hM := cast_ddtEM p hp
  have hA := cast_ddtEA p hp
  have hM0 : (0 : ℝ) ≤ ((ddtEM : ℚ) : ℝ) := by exact_mod_cast ddtEM_nonneg
  have hA0 : (0 : ℝ) ≤ ((ddtEA : ℚ) : ℝ) := by exact_mod_cast ddtEA_nonneg
  obtain ⟨eM, heM⟩ : ∃ e : ℝ, e = ((ddtEM : ℚ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨eA, heA⟩ : ∃ e : ℝ, e = ((ddtEA : ℚ) : ℝ) := ⟨_, rfl⟩
  rw [← heM] at hM hM0
  rw [← heA] at hA hA0
  obtain ⟨hte, htb, hEt0, htdw⟩ := ddt_t p hp hr hR hrb Fk hF cast_sinC sinC_alt hφ K hK
  obtain ⟨R, hRd⟩ : ∃ R, R = dwVal r := ⟨_, rfl⟩
  obtain ⟨Et, hEtd⟩ : ∃ Et : ℝ, Et = ((ddtEt (rb ^ 2) φ (fun k => |sinCQ k|) K : ℚ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨t, htd⟩ : ∃ t, t = ddtT p r Fk K := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = hornerE sinC (R ^ 2) (K - 1) 1 := ⟨_, rfl⟩
  rw [← hRd, ← hEtd, ← htd, ← hP] at hte
  rw [← hRd, ← hEtd, ← htd] at htb
  rw [← hEtd] at hEt0
  rw [← htd] at htdw
  rw [← hRd] at hR ⊢
  obtain ⟨T, hTd⟩ : ∃ T, T = dwVal t := ⟨_, rfl⟩
  rw [← hTd] at hte htb
  have hrb0 : (0 : ℝ) ≤ rb := (abs_nonneg _).trans hR
  have hrb1 : (rb : ℝ) ≤ 1 := by exact_mod_cast hrb
  have hR1 : |R| ≤ 1 := hR.trans hrb1
  have hR2 : R ^ 2 ≤ (rb : ℝ) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hR 2
  have hR20 : 0 ≤ R ^ 2 := sq_nonneg R
  have hrb2 : (rb : ℝ) ^ 2 ≤ 1 := by nlinarith
  have hs1 : (0 : ℝ) ≤ |sinC 1| := abs_nonneg _
  -- `r' = 2^e r` and `w = MUL(r', t)`
  have hσ : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  have hσ' : (0 : ℝ) < (2 : ℝ) ^ (-e) := by positivity
  have hσi : (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e = 1 := by
    rw [← zpow_add₀ two_ne_zero, neg_add_cancel, zpow_zero]
  have hr' := DW.scale p hr e
  obtain ⟨r', hr'd⟩ : ∃ r' : ℝ × ℝ, r' = ((2 : ℝ) ^ e * r.1, (2 : ℝ) ^ e * r.2) := ⟨_, rfl⟩
  rw [← hr'd] at hr'
  have hr'v : dwVal r' = (2 : ℝ) ^ e * R := by
    rw [hr'd, hRd]
    unfold dwVal
    ring
  obtain ⟨hwdw, hwe⟩ := dwTimesDW3_good p hp5 hr' htdw
  obtain ⟨w, hwd⟩ : ∃ w, w = dwTimesDW3 p r' t := ⟨_, rfl⟩
  rw [← hwd] at hwdw hwe
  rw [← hM, hr'v, ← hTd] at hwe
  obtain ⟨W, hW⟩ : ∃ W, W = dwVal w := ⟨_, rfl⟩
  rw [← hW] at hwe
  obtain ⟨hydw, hye⟩ := accDWPlusDW_good p hp3 hr' hwdw
  obtain ⟨y, hyd⟩ : ∃ y, y = accDWPlusDW p r' w := ⟨_, rfl⟩
  rw [← hyd] at hydw hye
  rw [← hA, hr'v, ← hW] at hye
  obtain ⟨Y, hY⟩ : ∃ Y, Y = dwVal y := ⟨_, rfl⟩
  rw [← hY] at hye
  have hres : ddSinR p e r Fk K = ((2 : ℝ) ^ (-e) * y.1, (2 : ℝ) ^ (-e) * y.2) := by
    rw [hyd, hwd, hr'd, htd]
    rfl
  have hresv : dwVal (ddSinR p e r Fk K) = (2 : ℝ) ^ (-e) * Y := by
    rw [hres, hY]
    unfold dwVal
    ring
  -- the bound as a real
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (rb : ℝ) ^ 2 * (Et + eM * (|sinC 1| + Et)) +
      (rb : ℝ) ^ (2 * K) / ((2 * K + 1).factorial : ℝ) := ⟨_, rfl⟩
  have hDS : ((ddtDS rb φ K : ℚ) : ℝ) = eA + (1 + eA) * D / (1 - (rb : ℝ) ^ 2 / 6) := by
    rw [hD, hEtd, heM, heA, ← cast_sinC 1]
    unfold ddtDS
    push_cast
    ring
  have hfact : (0 : ℝ) < ((2 * K + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hD0 : 0 ≤ D := by
    rw [hD]
    exact add_nonneg (mul_nonneg (sq_nonneg _) (add_nonneg hEt0 (mul_nonneg hM0 (add_nonneg hs1 hEt0))))
      (div_nonneg (pow_nonneg hrb0 _) hfact.le)
  have hq : 0 < 1 - (rb : ℝ) ^ 2 / 6 := by linarith
  -- `w` against `r' r² P`
  have hTb : |(2 : ℝ) ^ e * R * T| ≤ (2 : ℝ) ^ e * |R| * ((|sinC 1| + Et) * R ^ 2) := by
    rw [abs_mul, abs_mul, abs_of_pos hσ]
    exact mul_le_mul_of_nonneg_left htb (mul_nonneg hσ.le (abs_nonneg _))
  have hw1 : |W - (2 : ℝ) ^ e * R * (R ^ 2 * P)| ≤
      (2 : ℝ) ^ e * |R| * ((rb : ℝ) ^ 2 * (Et + eM * (|sinC 1| + Et))) := by
    have e1 : W - (2 : ℝ) ^ e * R * (R ^ 2 * P) =
        (W - (2 : ℝ) ^ e * R * T) + (2 : ℝ) ^ e * R * (T - R ^ 2 * P) := by ring
    have a1 : |W - (2 : ℝ) ^ e * R * T| ≤ eM * ((2 : ℝ) ^ e * |R| * ((|sinC 1| + Et) * R ^ 2)) :=
      hwe.trans (mul_le_mul_of_nonneg_left hTb hM0)
    have a2 : |(2 : ℝ) ^ e * R * (T - R ^ 2 * P)| ≤ (2 : ℝ) ^ e * |R| * (Et * R ^ 2) := by
      rw [abs_mul, abs_mul, abs_of_pos hσ]
      exact mul_le_mul_of_nonneg_left hte (mul_nonneg hσ.le (abs_nonneg _))
    have hc0 : 0 ≤ (2 : ℝ) ^ e * |R| * (Et + eM * (|sinC 1| + Et)) :=
      mul_nonneg (mul_nonneg hσ.le (abs_nonneg _)) (add_nonneg hEt0 (mul_nonneg hM0 (add_nonneg hs1 hEt0)))
    rw [e1]
    calc |(W - (2 : ℝ) ^ e * R * T) + (2 : ℝ) ^ e * R * (T - R ^ 2 * P)|
        ≤ |W - (2 : ℝ) ^ e * R * T| + |(2 : ℝ) ^ e * R * (T - R ^ 2 * P)| := abs_add_le _ _
      _ ≤ eM * ((2 : ℝ) ^ e * |R| * ((|sinC 1| + Et) * R ^ 2)) + (2 : ℝ) ^ e * |R| * (Et * R ^ 2) :=
          add_le_add a1 a2
      _ = (2 : ℝ) ^ e * |R| * (Et + eM * (|sinC 1| + Et)) * R ^ 2 := by ring
      _ ≤ (2 : ℝ) ^ e * |R| * (Et + eM * (|sinC 1| + Et)) * (rb : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hR2 hc0
      _ = _ := by ring
  -- the series' remainder
  have hsin := sin_taylor R hR1 K
  rw [sin_horner R K (by omega), ← hP] at hsin
  have hrem : |R + R * (R ^ 2 * P) - Real.sin R| ≤ |R| * ((rb : ℝ) ^ (2 * K) / ((2 * K + 1).factorial : ℝ)) := by
    rw [abs_sub_comm]
    refine hsin.trans ?_
    rw [pow_succ', mul_div_assoc]
    refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hfact.le) (abs_nonneg _)
    exact pow_le_pow_left₀ (abs_nonneg _) hR _
  -- `r' + w` against `2^e sin r`
  have hX : |(2 : ℝ) ^ e * R + W - (2 : ℝ) ^ e * Real.sin R| ≤ (2 : ℝ) ^ e * |R| * D := by
    have e1 : (2 : ℝ) ^ e * R + W - (2 : ℝ) ^ e * Real.sin R =
        (W - (2 : ℝ) ^ e * R * (R ^ 2 * P)) + (2 : ℝ) ^ e * (R + R * (R ^ 2 * P) - Real.sin R) := by ring
    have a2 : |(2 : ℝ) ^ e * (R + R * (R ^ 2 * P) - Real.sin R)| ≤
        (2 : ℝ) ^ e * (|R| * ((rb : ℝ) ^ (2 * K) / ((2 * K + 1).factorial : ℝ))) := by
      rw [abs_mul, abs_of_pos hσ]
      exact mul_le_mul_of_nonneg_left hrem hσ.le
    rw [e1, hD]
    calc _ ≤ |W - (2 : ℝ) ^ e * R * (R ^ 2 * P)| + |(2 : ℝ) ^ e * (R + R * (R ^ 2 * P) - Real.sin R)| :=
          abs_add_le _ _
      _ ≤ (2 : ℝ) ^ e * |R| * ((rb : ℝ) ^ 2 * (Et + eM * (|sinC 1| + Et))) +
            (2 : ℝ) ^ e * (|R| * ((rb : ℝ) ^ (2 * K) / ((2 * K + 1).factorial : ℝ))) := add_le_add hw1 a2
      _ = _ := by ring
  have hXabs : |(2 : ℝ) ^ e * R + W| ≤ (2 : ℝ) ^ e * |Real.sin R| + (2 : ℝ) ^ e * |R| * D := by
    have := abs_sub_abs_le_abs_sub ((2 : ℝ) ^ e * R + W) ((2 : ℝ) ^ e * Real.sin R)
    rw [abs_mul, abs_of_pos hσ] at this
    linarith
  -- `Y = ADD(r', w)`, scaled back
  have hY1 : |Y - (2 : ℝ) ^ e * Real.sin R| ≤
      (2 : ℝ) ^ e * (eA * |Real.sin R| + (1 + eA) * D * |R|) := by
    have h := abs_sub_le Y ((2 : ℝ) ^ e * R + W) ((2 : ℝ) ^ e * Real.sin R)
    have := hye.trans (mul_le_mul_of_nonneg_left hXabs hA0)
    calc |Y - (2 : ℝ) ^ e * Real.sin R|
        ≤ |Y - ((2 : ℝ) ^ e * R + W)| + |(2 : ℝ) ^ e * R + W - (2 : ℝ) ^ e * Real.sin R| := h
      _ ≤ eA * ((2 : ℝ) ^ e * |Real.sin R| + (2 : ℝ) ^ e * |R| * D) + (2 : ℝ) ^ e * |R| * D := add_le_add this hX
      _ = _ := by ring
  have hRs : |R| ≤ |Real.sin R| / (1 - (rb : ℝ) ^ 2 / 6) := by
    rw [le_div_iff₀ hq]
    refine le_trans ?_ (abs_sin_ge R hR1)
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg R)
  have hDS0 : 0 ≤ eA + (1 + eA) * D / (1 - (rb : ℝ) ^ 2 / 6) :=
    add_nonneg hA0 (div_nonneg (mul_nonneg (by linarith) hD0) hq.le)
  refine ⟨?_, by rw [hDS]; exact hDS0, by rw [hres]; exact DW.scale p hydw (-e)⟩
  rw [hresv, hDS, show (2 : ℝ) ^ (-e) * Y - Real.sin R = (2 : ℝ) ^ (-e) * (Y - (2 : ℝ) ^ e * Real.sin R) by
    rw [mul_sub, ← mul_assoc, hσi, one_mul], abs_mul, abs_of_pos hσ']
  calc (2 : ℝ) ^ (-e) * |Y - (2 : ℝ) ^ e * Real.sin R|
      ≤ (2 : ℝ) ^ (-e) * ((2 : ℝ) ^ e * (eA * |Real.sin R| + (1 + eA) * D * |R|)) :=
        mul_le_mul_of_nonneg_left hY1 hσ'.le
    _ = eA * |Real.sin R| + (1 + eA) * D * |R| := by rw [← mul_assoc, hσi, one_mul]
    _ ≤ eA * |Real.sin R| + (1 + eA) * D * (|Real.sin R| / (1 - (rb : ℝ) ^ 2 / 6)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hRs (mul_nonneg (by linarith) hD0))
    _ = _ := by ring

/-- Lemma 34 (`lem:sincosr`) for COSR on double words: for a double word `r` with `|r| ≤ r̄ ≤ 1` and coefficients
`F_k` within `φ_k` of `c_k`, `|COSR(r) - cos r| ≤ δ_C cos r`, and COSR(r) is a double word -/
theorem dd_cosr (hp : p = 53) {r : ℝ × ℝ} (hr : DW p r) {rb : ℚ} (hR : |dwVal r| ≤ (rb : ℝ)) (hrb : rb ≤ 1)
    (Fk : ℕ → ℝ × ℝ) (hF : ∀ k, DW p (Fk k)) {φ : ℕ → ℚ} (hφ : ∀ k, |dwVal (Fk k) - cosC k| ≤ (φ k : ℝ))
    (K : ℕ) (hK : 2 ≤ K) :
    |dwVal (ddCosR p r Fk K) - Real.cos (dwVal r)| ≤ ((ddtDC rb φ K : ℚ) : ℝ) * Real.cos (dwVal r) ∧
      0 ≤ ((ddtDC rb φ K : ℚ) : ℝ) ∧ DW p (ddCosR p r Fk K) := by
  have hp3 : 3 ≤ p := by omega
  have hFc := cast_ddtEF p hp
  have hF0 : (0 : ℝ) ≤ ((ddtEF : ℚ) : ℝ) := by exact_mod_cast ddtEF_nonneg
  obtain ⟨eF, heF⟩ : ∃ e : ℝ, e = ((ddtEF : ℚ) : ℝ) := ⟨_, rfl⟩
  rw [← heF] at hFc hF0
  obtain ⟨hte, -, hEt0, htdw⟩ := ddt_t p hp hr hR hrb Fk hF cast_cosC cosC_alt hφ K hK
  obtain ⟨R, hRd⟩ : ∃ R, R = dwVal r := ⟨_, rfl⟩
  obtain ⟨Et, hEtd⟩ : ∃ Et : ℝ, Et = ((ddtEt (rb ^ 2) φ (fun k => |cosCQ k|) K : ℚ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨t, htd⟩ : ∃ t, t = ddtT p r Fk K := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = hornerE cosC (R ^ 2) (K - 1) 1 := ⟨_, rfl⟩
  rw [← hRd, ← hEtd, ← htd, ← hP] at hte
  rw [← hEtd] at hEt0
  rw [← htd] at htdw
  rw [← hRd] at hR ⊢
  obtain ⟨T, hTd⟩ : ∃ T, T = dwVal t := ⟨_, rfl⟩
  rw [← hTd] at hte
  have hrb0 : (0 : ℝ) ≤ rb := (abs_nonneg _).trans hR
  have hrb1 : (rb : ℝ) ≤ 1 := by exact_mod_cast hrb
  have hR1 : |R| ≤ 1 := hR.trans hrb1
  have hR2 : R ^ 2 ≤ (rb : ℝ) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hR 2
  have hcl := cosLo_pos hrb0 hrb1
  have hc := cos_ge_cosLo R rb hR hrb1
  obtain ⟨hydw, hye⟩ := dwPlusFP_good p hp3 htdw (F_one p)
  have hres : ddCosR p r Fk K = dwPlusFP p t 1 := by rw [htd]; rfl
  rw [← hres] at hydw hye
  rw [← hFc, ← hTd] at hye
  obtain ⟨Y, hY⟩ : ∃ Y, Y = dwVal (ddCosR p r Fk K) := ⟨_, rfl⟩
  rw [← hY] at hye ⊢
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (rb : ℝ) ^ 2 * Et + (rb : ℝ) ^ (2 * K) / ((2 * K).factorial : ℝ) := ⟨_, rfl⟩
  have hDC : ((ddtDC rb φ K : ℚ) : ℝ) = eF + (1 + eF) * D / cosLo (rb : ℝ) := by
    rw [hD, hEtd, heF, ← cast_cosLo]
    unfold ddtDC
    push_cast
    ring
  have hfact : (0 : ℝ) < ((2 * K).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hD0 : 0 ≤ D := by
    rw [hD]
    exact add_nonneg (mul_nonneg (sq_nonneg _) hEt0) (div_nonneg (pow_nonneg hrb0 _) hfact.le)
  have hcos := cos_taylor R hR1 K
  rw [cos_horner R K (by omega), ← hP] at hcos
  have hX : |T + 1 - Real.cos R| ≤ D := by
    have e1 : T + 1 - Real.cos R = (T - R ^ 2 * P) - (Real.cos R - (1 + R ^ 2 * P)) := by ring
    have a1 : |T - R ^ 2 * P| ≤ (rb : ℝ) ^ 2 * Et := by
      have := hte.trans (mul_le_mul_of_nonneg_left hR2 hEt0)
      linarith
    have a2 : |Real.cos R - (1 + R ^ 2 * P)| ≤ (rb : ℝ) ^ (2 * K) / ((2 * K).factorial : ℝ) :=
      hcos.trans (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hR _) hfact.le)
    rw [e1, hD]
    exact (abs_sub _ _).trans (add_le_add a1 a2)
  have hXabs : |T + 1| ≤ Real.cos R + D := by
    have := abs_sub_abs_le_abs_sub (T + 1) (Real.cos R)
    rw [abs_of_pos (by linarith : (0 : ℝ) < Real.cos R)] at this
    linarith
  have hDC0 : 0 ≤ eF + (1 + eF) * D / cosLo (rb : ℝ) :=
    add_nonneg hF0 (div_nonneg (mul_nonneg (by linarith) hD0) hcl.le)
  refine ⟨?_, by rw [hDC]; exact hDC0, hydw⟩
  rw [hDC]
  have h := abs_sub_le Y (T + 1) (Real.cos R)
  have h2 := hye.trans (mul_le_mul_of_nonneg_left hXabs hF0)
  have h3 : (1 + eF) * D ≤ (1 + eF) * D / cosLo (rb : ℝ) * Real.cos R := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hcl]
    exact mul_le_mul_of_nonneg_left hc (mul_nonneg (by linarith) hD0)
  calc |Y - Real.cos R| ≤ |Y - (T + 1)| + |T + 1 - Real.cos R| := h
    _ ≤ eF * (Real.cos R + D) + D := add_le_add h2 hX
    _ = eF * Real.cos R + (1 + eF) * D := by ring
    _ ≤ eF * Real.cos R + (1 + eF) * D / cosLo (rb : ℝ) * Real.cos R := add_le_add le_rfl h3
    _ = _ := by ring

end ExpansionBounds
