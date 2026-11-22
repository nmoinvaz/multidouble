import ExpansionBounds.GScale
import ExpansionBounds.RenormSharp
import ExpansionBounds.Taylor
import FloatSpec.src.Prop.Mult_error

/-!
# Lemma 34: SINR and COSR

`z = MUL(r, r)`, Horner's rule on the coefficients from `p_{K-1} = F_{K-1}` down to `p_1`, `t = MUL(z, p_1)`,
`SINR(r) = 2^{-e} ADD(r', MUL(r', t))` with `r' = 2^e r`, and `COSR(r) = ADDF(t, 1)`; below `|r_0| < u^{n/2}`, SINR
returns `r` and COSR `1` (`sinRN`, `cosRN`). Under (A3), `(n² + n)u < 1`, the bounds hold for any `K ≥ 2`, any exponent
`e` and any `r̄ ≤ 1`. The paper's `K_s(j)` and `K_c(j)` only make them small. Its `e = j + 1` keeps SINR's products
clear of underflow in binary64; in the unbounded model both scalings are exact and `e` leaves the bounds unchanged. The
bounds are in units: `r` in units of `|r|`, `z` in units of `r²`, by the homogeneity of Lemma 13's bounds (`Gmul_smul`,
`Gadd_smul`).
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) (n : ℕ)

/-- the parts of an expansion, zero past its end -/
def pt (l : List ℝ) : ℕ → ℝ := fun i => l.getD i 0

/-- Horner's rule in the order of SINR and COSR: `p_d = F_d` and `p_k = ADD(MUL(z, p_{k+1}), F_k)` -/
noncomputable def hornerS (z : ℕ → ℝ) (Fk : ℕ → ℕ → ℝ) (d : ℕ) : ℕ → ℕ → ℝ
  | 0 => Fk d
  | j + 1 => pt (addOp p n (pt (mulOp p n z (hornerS z Fk d j))) (Fk (d - (j + 1))))

/-- `z = MUL(r, r)` -/
noncomputable def zOf (r : ℕ → ℝ) : ℕ → ℝ := pt (mulOp p n r r)

/-- `t = MUL(z, p_1)`, with `p_1` from `p_{K-1} = F_{K-1}` -/
noncomputable def tOf (r : ℕ → ℝ) (Fk : ℕ → ℕ → ℝ) (K : ℕ) : ℕ → ℝ :=
  pt (mulOp p n (zOf p n r) (hornerS p n (zOf p n r) Fk (K - 1) (K - 2)))

/-- SINR's polynomial branch, `2^{-e} ADD(r', MUL(r', t))` with `r' = 2^e r`, for the coefficients `F_k` of `s_k` -/
noncomputable def sinR (e : ℤ) (r : ℕ → ℝ) (Fk : ℕ → ℕ → ℝ) (K : ℕ) : ℕ → ℝ := fun i =>
  (2 : ℝ) ^ (-e) * pt (addOp p n (fun i => (2 : ℝ) ^ e * r i)
    (pt (mulOp p n (fun i => (2 : ℝ) ^ e * r i) (tOf p n r Fk K)))) i

/-- COSR's polynomial branch, `ADDF(t, 1)`, for the coefficients `F_k` of `c_k` -/
noncomputable def cosR (r : ℕ → ℝ) (Fk : ℕ → ℕ → ℝ) (K : ℕ) : ℕ → ℝ := pt (addfOp p n (tOf p n r Fk K) 1)

/-- SINR: `r` for `|r_0| < u^{n/2}` (`n` even), the polynomial branch `sinR` otherwise -/
noncomputable def sinRN (e : ℤ) (r : ℕ → ℝ) (Fk : ℕ → ℕ → ℝ) (K : ℕ) : ℕ → ℝ :=
  if |r 0| < u p ^ (n / 2) then fun i => if i < n then r i else 0 else sinR p n e r Fk K

/-- COSR: `1` for `|r_0| < u^{n/2}` (`n` even), the polynomial branch `cosR` otherwise -/
noncomputable def cosRN (r : ℕ → ℝ) (Fk : ℕ → ℕ → ℝ) (K : ℕ) : ℕ → ℝ :=
  if |r 0| < u p ^ (n / 2) then fun i => if i = 0 then 1 else 0 else cosR p n r Fk K

/-- Horner's bounds `(E_1, π^{(1)})` for `z = MUL(r, r)` and the coefficients `F_k` of `C_k`: `z̄ = r̄²`,
`π^z = r̄²π̂^z` with `(ε_z, π̂^z) = G_MUL(ā, ā; 1)`, `φ_k = |F_k - C_k|` and `v_k = |C_k|` -/
noncomputable def scH (ab : ℕ → ℝ) (rb : ℝ) (C : ℕ → ℝ) (Fk : ℕ → ℕ → ℝ) (K : ℕ) : ℝ × (ℕ → ℝ) :=
  hornerB p n (fun i => rb ^ 2 * GmulP p n ab ab 1 i) (rb ^ 2) (GmulE p n ab ab 1) 0 Fk
    (fun k => |∑ i ∈ range n, Fk k i - C k|) (fun k => |C k|) (K - 1) (K - 2)

/-- `(1 + ε_z)(|C_1| + E_1)`, `t`'s `Z̄` in units of `r²` -/
noncomputable def scZt (ab : ℕ → ℝ) (rb : ℝ) (C : ℕ → ℝ) (Fk : ℕ → ℕ → ℝ) (K : ℕ) : ℝ :=
  (1 + GmulE p n ab ab 1) * (|C 1| + (scH p n ab rb C Fk K).1)

/-- `ϑ`, of `(ε_t, ϑ) = G_MUL(π̂^z, π^{(1)}; (1 + ε_z)(|C_1| + E_1))` -/
noncomputable def scTh (ab : ℕ → ℝ) (rb : ℝ) (C : ℕ → ℝ) (Fk : ℕ → ℕ → ℝ) (K : ℕ) : ℕ → ℝ :=
  GmulP p n (GmulP p n ab ab 1) (scH p n ab rb C Fk K).2 (scZt p n ab rb C Fk K)

/-- `E_t = (1 + ε_z)E_1 + ε_z|C_1| + ε_t` -/
noncomputable def scEt (ab : ℕ → ℝ) (rb : ℝ) (C : ℕ → ℝ) (Fk : ℕ → ℕ → ℝ) (K : ℕ) : ℝ :=
  (1 + GmulE p n ab ab 1) * (scH p n ab rb C Fk K).1 + GmulE p n ab ab 1 * |C 1| +
    GmulE p n (GmulP p n ab ab 1) (scH p n ab rb C Fk K).2 (scZt p n ab rb C Fk K)

/-- `(ε_w, ω) = G_MUL(ā, ϑ; |s_1| + E_t)` -/
noncomputable def sinWE (ab : ℕ → ℝ) (rb : ℝ) (Fk : ℕ → ℕ → ℝ) (K : ℕ) : ℝ :=
  GmulE p n ab (scTh p n ab rb sinC Fk K) (|sinC 1| + scEt p n ab rb sinC Fk K)

noncomputable def sinWP (ab : ℕ → ℝ) (rb : ℝ) (Fk : ℕ → ℕ → ℝ) (K : ℕ) : ℕ → ℝ :=
  GmulP p n ab (scTh p n ab rb sinC Fk K) (|sinC 1| + scEt p n ab rb sinC Fk K)

/-- `D = r̄²(E_t + ε_w) + r̄^{2K}/(2K + 1)!` -/
noncomputable def sinD (ab : ℕ → ℝ) (rb : ℝ) (Fk : ℕ → ℕ → ℝ) (K : ℕ) : ℝ :=
  rb ^ 2 * (scEt p n ab rb sinC Fk K + sinWE p n ab rb Fk K) + rb ^ (2 * K) / ((2 * K + 1).factorial : ℝ)

/-- `(ε_y, ψ_s) = G_ADD(ā, r̄²ω; 1 + D)` -/
noncomputable def sinY (ab : ℕ → ℝ) (rb : ℝ) (Fk : ℕ → ℕ → ℝ) (K : ℕ) : ℝ :=
  GaddE p n ab (fun i => rb ^ 2 * sinWP p n ab rb Fk K i) (1 + sinD p n ab rb Fk K)

noncomputable def sinPsi (ab : ℕ → ℝ) (rb : ℝ) (Fk : ℕ → ℕ → ℝ) (K : ℕ) : ℕ → ℝ :=
  GaddP p n ab (fun i => rb ^ 2 * sinWP p n ab rb Fk K i) (1 + sinD p n ab rb Fk K)

/-- `δ_S = uⁿ + E_S/(1 - r̄²/6)` with `E_S = D + ε_y - uⁿ` -/
noncomputable def sinDelta (ab : ℕ → ℝ) (rb : ℝ) (Fk : ℕ → ℕ → ℝ) (K : ℕ) : ℝ :=
  u p ^ n + (sinD p n ab rb Fk K + sinY p n ab rb Fk K - u p ^ n) / (1 - rb ^ 2 / 6)

/-- `D_c = r̄²E_t + r̄^{2K}/(2K)!` -/
noncomputable def cosD (ab : ℕ → ℝ) (rb : ℝ) (Fk : ℕ → ℕ → ℝ) (K : ℕ) : ℝ :=
  rb ^ 2 * scEt p n ab rb cosC Fk K + rb ^ (2 * K) / ((2 * K).factorial : ℝ)

/-- `(ε_y, ψ_c) = G_ADDF(r̄²ϑ, 1; 1 + D_c)` -/
noncomputable def cosY (ab : ℕ → ℝ) (rb : ℝ) (Fk : ℕ → ℕ → ℝ) (K : ℕ) : ℝ :=
  GaddfE p n (fun i => rb ^ 2 * scTh p n ab rb cosC Fk K i) 1 (1 + cosD p n ab rb Fk K)

noncomputable def cosPsi (ab : ℕ → ℝ) (rb : ℝ) (Fk : ℕ → ℕ → ℝ) (K : ℕ) : ℕ → ℝ :=
  GaddfP p n (fun i => rb ^ 2 * scTh p n ab rb cosC Fk K i) 1 (1 + cosD p n ab rb Fk K)

/-- `δ_C = uⁿ + E_C/cos₋ r̄` with `E_C = D_c + ε_y - uⁿ` -/
noncomputable def cosDelta (ab : ℕ → ℝ) (rb : ℝ) (Fk : ℕ → ℕ → ℝ) (K : ℕ) : ℝ :=
  u p ^ n + (cosD p n ab rb Fk K + cosY p n ab rb Fk K - u p ^ n) / cosLo rb

theorem abs3 (a b c : ℝ) : |a + b - c| ≤ |a| + |b| + |c| :=
  (abs_sub _ _).trans (add_le_add_left (abs_add_le _ _) _)

/-- a finite alternating sum of decreasing terms: `|∑_{l} (-1)^{k+l} g_{k+l} x^l| ≤ g_k` for `0 ≤ x ≤ 1` -/
theorem hornerE_alt (g : ℕ → ℝ) (hg : Antitone g) (hg0 : ∀ k, 0 ≤ g k) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (d k : ℕ) : |hornerE (fun k => (-1) ^ k * g k) x d k| ≤ g k := by
  unfold hornerE
  have ha : Antitone fun l => g (k + l) * x ^ l := fun l l' hl =>
    mul_le_mul (hg (by omega)) (pow_le_pow_of_le_one hx0 hx1 hl) (pow_nonneg hx0 _) (hg0 _)
  have h := alt_sum_bounds (d + 1 - k) _ ha fun l => mul_nonneg (hg0 _) (pow_nonneg hx0 _)
  have hs : ∑ l ∈ range (d + 1 - k), (-1) ^ (k + l) * g (k + l) * x ^ l =
      (-1) ^ k * ∑ l ∈ range (d + 1 - k), (-1) ^ l * (g (k + l) * x ^ l) := by
    rw [mul_sum]
    exact sum_congr rfl fun l _ => by rw [pow_add]; ring
  rw [hs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg h.1]
  simpa using h.2

theorem inv_fact_antitone (c : ℕ) : Antitone fun k : ℕ => (((2 * k + c).factorial : ℝ))⁻¹ := fun a b hab =>
  inv_anti₀ (by exact_mod_cast Nat.factorial_pos _) (by exact_mod_cast Nat.factorial_le (by omega))

theorem sinC_alt (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (d k : ℕ) : |hornerE sinC x d k| ≤ |sinC k| := by
  have hs : sinC = fun k => (-1) ^ k * (((2 * k + 1).factorial : ℝ))⁻¹ := funext fun k => div_eq_mul_inv _ _
  have hk : |sinC k| = (((2 * k + 1).factorial : ℝ))⁻¹ := by
    rw [hs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (by positivity)]
  rw [hk, hs]
  exact hornerE_alt _ (inv_fact_antitone 1) (fun k => by positivity) x hx0 hx1 d k

theorem cosC_alt (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (d k : ℕ) : |hornerE cosC x d k| ≤ |cosC k| := by
  have hs : cosC = fun k => (-1) ^ k * (((2 * k + 0).factorial : ℝ))⁻¹ := funext fun k => div_eq_mul_inv _ _
  have hk : |cosC k| = (((2 * k + 0).factorial : ℝ))⁻¹ := by
    rw [hs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (by positivity)]
  rw [hk, hs]
  exact hornerE_alt _ (inv_fact_antitone 0) (fun k => by positivity) x hx0 hx1 d k

/-- `r + r z_e p^e_1` is the sine series' first `K` terms -/
theorem sin_horner (R : ℝ) (K : ℕ) (hK : 1 ≤ K) :
    ∑ k ∈ range K, sinC k * R ^ (2 * k + 1) = R + R * (R ^ 2 * hornerE sinC (R ^ 2) (K - 1) 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
  rw [sum_range_succ', hornerE, show m + 1 - 1 + 1 - 1 = m by omega, mul_sum, mul_sum, add_comm]
  congr 1
  · simp [sinC]
  · exact sum_congr rfl fun k _ => by rw [add_comm 1 k]; ring

/-- `1 + z_e p^e_1` is the cosine series' first `K` terms -/
theorem cos_horner (R : ℝ) (K : ℕ) (hK : 1 ≤ K) :
    ∑ k ∈ range K, cosC k * R ^ (2 * k) = 1 + R ^ 2 * hornerE cosC (R ^ 2) (K - 1) 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
  rw [sum_range_succ', hornerE, show m + 1 - 1 + 1 - 1 = m by omega, mul_sum, add_comm]
  congr 1
  · simp [cosC]
  · exact sum_congr rfl fun k _ => by rw [add_comm 1 k]; ring

theorem cosLo_pos {rb : ℝ} (h0 : 0 ≤ rb) (h1 : rb ≤ 1) : 0 < cosLo rb := by
  unfold cosLo
  have h2 : rb ^ 2 ≤ 1 := by nlinarith
  have h6 : rb ^ 6 ≤ 1 := pow_le_one₀ h0 h1
  nlinarith [pow_nonneg h0 4]

theorem gaddE_split (α β : ℕ → ℝ) (Zb : ℝ) : GaddE p n α β Zb = u p ^ n * Zb + GaddE p n α β 0 :=
  gErr_split p n _ Zb _

theorem gaddfE_split (α : ℕ → ℝ) (β0 Zb : ℝ) : GaddfE p n α β0 Zb = u p ^ n * Zb + GaddfE p n α β0 0 :=
  gErr_split p n _ Zb _

theorem addfX_nonneg {α : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i) {lam0 : ℝ} (hl : 0 ≤ lam0) (m : ℕ) :
    0 ≤ addfX p n α lam0 m := by
  have hu := u_pos p
  have he : ∀ k, 0 ≤ addfEps p α lam0 k := by
    intro k
    induction k with
    | zero => exact mul_nonneg hu.le hl
    | succ k ih => exact mul_nonneg hu.le (add_nonneg (hα _) ih)
  simp only [addfX]
  split_ifs
  · exact mul_nonneg (by linarith) hl
  · exact mul_nonneg (by linarith) (add_nonneg (hα _) (he _))
  · exact he _
  · exact le_rfl

theorem Gaddf_nonneg {α : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i) {β0 : ℝ} (hβ : 0 ≤ β0) {Zb : ℝ} (hZ : 0 ≤ Zb) :
    0 ≤ GaddfE p n α β0 Zb ∧ ∀ i, 0 ≤ GaddfP p n α β0 Zb i := by
  have hX := addfX_nonneg p n hα (add_nonneg (hα 0) hβ)
  exact ⟨gErr_nonneg p n hX hZ le_rfl, gParts_nonneg p n hX hZ le_rfl⟩

theorem hornerB_nonneg (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {πz : ℕ → ℝ} (hπz : ∀ i, 0 ≤ πz i) {zb εz η : ℝ}
    (hzb : 0 ≤ zb) (hεz : 0 ≤ εz) (hη : 0 ≤ η) (Fk : ℕ → ℕ → ℝ) {φ v : ℕ → ℝ} (hφ : ∀ k, 0 ≤ φ k)
    (hv : ∀ k, 0 ≤ v k) (d j : ℕ) :
    0 ≤ (hornerB p n πz zb εz η Fk φ v d j).1 ∧ ∀ i, 0 ≤ (hornerB p n πz zb εz η Fk φ v d j).2 i := by
  induction j with
  | zero => exact ⟨hφ d, fun i => abs_nonneg _⟩
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    have hZm : 0 ≤ (1 + εz) * zb * (v (d - (j + 1) + 1) + (hornerB p n πz zb εz η Fk φ v d j).1) :=
      mul_nonneg (mul_nonneg (by linarith) hzb) (add_nonneg (hv _) h1)
    obtain ⟨m1, m2⟩ := Gmul_nonneg p n hA3 hπz h2 hZm
    have hD : 0 ≤ (1 + εz) * zb * (hornerB p n πz zb εz η Fk φ v d j).1 + εz * zb * v (d - (j + 1) + 1) +
        φ (d - (j + 1)) + (GmulE p n πz (hornerB p n πz zb εz η Fk φ v d j).2
          ((1 + εz) * zb * (v (d - (j + 1) + 1) + (hornerB p n πz zb εz η Fk φ v d j).1)) + n * η) :=
      add_nonneg (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by linarith) hzb) h1)
        (mul_nonneg (mul_nonneg hεz hzb) (hv _))) (hφ _)) (add_nonneg m1 (mul_nonneg (Nat.cast_nonneg _) hη))
    obtain ⟨a1, a2⟩ := Gadd_nonneg p n hA3 (fun i => abs_nonneg (Fk (d - (j + 1)) i))
      (fun i => add_nonneg (m2 i) hη) (add_nonneg (hv (d - (j + 1))) hD)
    exact ⟨add_nonneg hD a1, a2⟩

variable [Prec_gt_0 p]

theorem F_one : F p 1 := by simpa using F_two_zpow p 0

theorem F_zpow_mul (e : ℤ) {x : ℝ} (hx : F p x) : F p ((2 : ℝ) ^ e * x) := by
  have h := mult_bpow_exact_FLX 2 p x e (by norm_num) hx
  rw [mul_comm]
  simpa [F, FloatSpec.Core.Raux.bpow] using h

theorem F_mulOp (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (a b : ℕ → ℝ)
    (ha : ∀ i < n, F p (a i)) (hb : ∀ j < n, F p (b j)) : ∀ i, F p ((mulOp p n a b).getD i 0) :=
  (mul_G p n hp hn hA3 a b (fun i => |a i|) (fun j => |b j|) ha hb (fun _ _ => le_rfl) (fun _ _ => le_rfl) _
    le_rfl).2.2.1

theorem F_addOp (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (a b : ℕ → ℝ)
    (ha : ∀ i < n, F p (a i)) (hb : ∀ j < n, F p (b j)) : ∀ i, F p ((addOp p n a b).getD i 0) :=
  (add_G p n hp hn hA3 a b (fun i => |a i|) (fun j => |b j|) ha hb (fun _ _ => le_rfl) (fun _ _ => le_rfl) _
    le_rfl).2.2.1

/-- SINR's and COSR's order of ADD's operands gives Lemma 33's `p_k`, by `addOp_comm` -/
theorem hornerS_eq (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (z : ℕ → ℝ)
    (hz : ∀ i < n, F p (z i)) (Fk : ℕ → ℕ → ℝ) (hF : ∀ k, ∀ i < n, F p (Fk k i)) (d j : ℕ) :
    hornerS p n z Fk d j = hornerP p n (mulOp p n) z Fk d j ∧ ∀ i < n, F p (hornerS p n z Fk d j i) := by
  induction j with
  | zero => exact ⟨rfl, hF d⟩
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    have hm := F_mulOp p n hp hn hA3 z _ hz h2
    refine ⟨?_, fun i _ => F_addOp p n hp hn hA3 _ _ (fun i _ => hm i) (hF _) i⟩
    show pt (addOp p n (pt (mulOp p n z (hornerS p n z Fk d j))) (Fk (d - (j + 1)))) = fun i =>
      (addOp p n (Fk (d - (j + 1))) fun i' => (mulOp p n z (hornerP p n (mulOp p n) z Fk d j)).getD i' 0).getD i 0
    rw [addOp_comm p n hp hn (pt (mulOp p n z (hornerS p n z Fk d j))) (Fk (d - (j + 1))) (fun i _ => hm i) (hF _),
      h1]
    rfl

/-- the part of SINR and COSR before their last steps: `|t - z_e p^e_1| ≤ E_t r²`, and `t` has part bounds `ϑr²`,
for coefficients `C` whose Horner sums are within `|C_k|` -/
theorem sc_core (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (r : ℕ → ℝ)
    (hr : ∀ i < n, F p (r i)) (ab : ℕ → ℝ) (hab0 : ∀ i, 0 ≤ ab i) (R : ℝ) (hR : R = ∑ i ∈ range n, r i)
    (hab : ∀ i < n, |r i| ≤ ab i * |R|) (rb : ℝ) (hrb : |R| ≤ rb) (hrb1 : rb ≤ 1) (C : ℕ → ℝ)
    (hC : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∀ d k, |hornerE C x d k| ≤ |C k|) (Fk : ℕ → ℕ → ℝ)
    (hF : ∀ k, ∀ i < n, F p (Fk k i)) (K : ℕ) (hK : 2 ≤ K) :
    |∑ i ∈ range n, tOf p n r Fk K i - R ^ 2 * hornerE C (R ^ 2) (K - 1) 1| ≤ R ^ 2 * scEt p n ab rb C Fk K ∧
      (∀ i < n, |tOf p n r Fk K i| ≤ R ^ 2 * scTh p n ab rb C Fk K i) ∧ (∀ i < n, F p (tOf p n r Fk K i)) ∧
      |hornerE C (R ^ 2) (K - 1) 1| ≤ |C 1| ∧ 0 ≤ scEt p n ab rb C Fk K ∧ ∀ i, 0 ≤ scTh p n ab rb C Fk K i := by
  have hrb0 : 0 ≤ rb := (abs_nonneg R).trans hrb
  have hA : |R| * |R| = R ^ 2 := by rw [abs_mul_abs_self, sq]
  have hR2 : R ^ 2 ≤ rb ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg R) hrb 2
  have hR21 : R ^ 2 ≤ 1 := hR2.trans (by nlinarith)
  have hR20 : 0 ≤ R ^ 2 := sq_nonneg R
  -- `z = MUL(r, r)`: `|z - r²| ≤ ε_z r²`, part bounds `π̂^z r²`
  obtain ⟨hεz, hπz0⟩ := Gmul_nonneg p n hA3 hab0 hab0 zero_le_one
  have hra : ∀ i < n, |r i| ≤ |R| * ab i := fun i hi => (hab i hi).trans_eq (mul_comm _ _)
  obtain ⟨z1, z2, z3, z4⟩ := mul_G p n hp hn hA3 r r _ _ hr hr hra hra (|R| * |R| * 1)
    (by rw [← hR, abs_mul, mul_one])
  obtain ⟨gz1, gz2⟩ := Gmul_smul p n ab ab 1 (abs_nonneg R) (abs_nonneg R)
  rw [gz1, ← hR, hA] at z1
  simp only [gz2] at z2
  simp only [hA] at z2
  obtain ⟨z, hz⟩ : ∃ z, z = zOf p n r := ⟨_, rfl⟩
  have hzs : ∑ i ∈ range n, z i = (mulOp p n r r).sum := by rw [hz]; exact (list_sum_getD _ n z4).symm
  have hzF : ∀ i < n, F p (z i) := fun i _ => by rw [hz]; exact z3 i
  have hzp : ∀ i < n, |z i| ≤ R ^ 2 * GmulP p n ab ab 1 i := fun i _ => by rw [hz]; exact z2 i
  have hze : |∑ i ∈ range n, z i - R ^ 2| ≤ R ^ 2 * GmulE p n ab ab 1 := by
    rw [← sq] at z1
    rw [hzs, abs_sub_comm]
    exact z1
  have hzabs : |∑ i ∈ range n, z i| ≤ R ^ 2 * (1 + GmulE p n ab ab 1) := by
    have := abs_sub_abs_le_abs_sub (∑ i ∈ range n, z i) (R ^ 2)
    rw [abs_of_nonneg hR20] at this
    nlinarith
  -- Horner's rule down to `p_1`
  have hv : ∀ k, 1 ≤ k → k ≤ K - 1 → |hornerE C (R ^ 2) (K - 1) k| ≤ |C k| := fun k _ _ =>
    hC _ hR20 hR21 _ _
  obtain ⟨hs1, hs2⟩ := hornerS_eq p n hp hn hA3 z hzF Fk hF (K - 1) (K - 2)
  obtain ⟨h1, h2, -⟩ := horner_step p n hp hn hA3 (mulOp_within p n hp hn hA3) z hzF
    (fun i => rb ^ 2 * GmulP p n ab ab 1 i)
    (fun i hi => (hzp i hi).trans (mul_le_mul_of_nonneg_right hR2 (hπz0 i))) (R ^ 2) (rb ^ 2)
    (GmulE p n ab ab 1) (by rw [abs_of_nonneg hR20]; exact hR2) hεz
    ((hze.trans (mul_le_mul_of_nonneg_right hR2 hεz)).trans_eq (mul_comm _ _)) Fk hF C
    (fun k => |∑ i ∈ range n, Fk k i - C k|) (fun k => |C k|) (fun k => le_rfl) (K - 1) 1 hv (K - 2) (by omega)
  rw [show K - 1 - (K - 2) = 1 by omega, ← hs1] at h1
  simp only [← hs1] at h2
  obtain ⟨p1, hp1⟩ : ∃ p1, p1 = hornerS p n z Fk (K - 1) (K - 2) := ⟨_, rfl⟩
  rw [← hp1] at h1 h2 hs2
  obtain ⟨E1, π1, hEπ⟩ : ∃ E1 π1, scH p n ab rb C Fk K = (E1, π1) := ⟨_, _, rfl⟩
  have hE1 : |∑ i ∈ range n, p1 i - hornerE C (R ^ 2) (K - 1) 1| ≤ E1 := by
    have : (scH p n ab rb C Fk K).1 = E1 := by rw [hEπ]
    rw [← this]; exact h1
  have hπ1 : ∀ i < n, |p1 i| ≤ π1 i := by
    have : (scH p n ab rb C Fk K).2 = π1 := by rw [hEπ]
    rw [← this]; exact h2
  obtain ⟨-, hπ10⟩ := hornerB_nonneg p n hA3 (fun i => mul_nonneg (sq_nonneg rb) (hπz0 i)) (sq_nonneg rb) hεz
    le_rfl Fk (fun k => abs_nonneg _) (fun k => abs_nonneg _) (K - 1) (K - 2)
  have hπ10' : ∀ i, 0 ≤ π1 i := by
    have : (scH p n ab rb C Fk K).2 = π1 := by rw [hEπ]
    rw [← this]; exact hπ10
  have hE10 : 0 ≤ E1 := (abs_nonneg _).trans hE1
  have hP := hv 1 le_rfl (by omega)
  -- `t = MUL(z, p_1)`
  have hZt : scZt p n ab rb C Fk K = (1 + GmulE p n ab ab 1) * (|C 1| + E1) := by simp only [scZt, hEπ]
  have hEt : scEt p n ab rb C Fk K = (1 + GmulE p n ab ab 1) * E1 + GmulE p n ab ab 1 * |C 1| +
      GmulE p n (GmulP p n ab ab 1) π1 ((1 + GmulE p n ab ab 1) * (|C 1| + E1)) := by
    simp only [scEt, hEπ, hZt]
  have hTh : scTh p n ab rb C Fk K = GmulP p n (GmulP p n ab ab 1) π1 ((1 + GmulE p n ab ab 1) * (|C 1| + E1)) := by
    simp only [scTh, hEπ, hZt]
  have hp1abs : |∑ i ∈ range n, p1 i| ≤ |C 1| + E1 := by
    have := abs_sub_abs_le_abs_sub (∑ i ∈ range n, p1 i) (hornerE C (R ^ 2) (K - 1) 1)
    linarith
  obtain ⟨t1, t2, t3, t4⟩ := mul_G p n hp hn hA3 z p1 (fun i => |R| * |R| * GmulP p n ab ab 1 i)
    (fun j => 1 * π1 j) hzF hs2 (fun i hi => by rw [hA]; exact hzp i hi) (fun j hj => by rw [one_mul]; exact hπ1 j hj)
    (|R| * |R| * 1 * ((1 + GmulE p n ab ab 1) * (|C 1| + E1))) (by
      rw [abs_mul, hA, mul_one, ← mul_assoc]
      exact mul_le_mul hzabs hp1abs (abs_nonneg _) (mul_nonneg hR20 (by linarith)))
  obtain ⟨gt1, gt2⟩ := Gmul_smul p n (GmulP p n ab ab 1) π1 ((1 + GmulE p n ab ab 1) * (|C 1| + E1))
    (mul_nonneg (abs_nonneg R) (abs_nonneg R)) zero_le_one
  rw [gt1, hA, mul_one] at t1
  simp only [gt2] at t2
  simp only [hA, mul_one] at t2
  obtain ⟨hεt, hϑ0⟩ := Gmul_nonneg p n hA3 hπz0 hπ10' (Zb := (1 + GmulE p n ab ab 1) * (|C 1| + E1))
    (mul_nonneg (by linarith) (add_nonneg (abs_nonneg _) hE10))
  have htdef : tOf p n r Fk K = pt (mulOp p n z p1) := by rw [hp1, hz]; rfl
  have hts : ∑ i ∈ range n, tOf p n r Fk K i = (mulOp p n z p1).sum := by
    rw [htdef]; exact (list_sum_getD _ n t4).symm
  refine ⟨?_, fun i _ => ?_, fun i _ => ?_, hP, ?_, ?_⟩
  · rw [hts, hEt]
    have e1 : |(∑ i ∈ range n, z i) * (∑ i ∈ range n, p1 i - hornerE C (R ^ 2) (K - 1) 1)| ≤
        R ^ 2 * (1 + GmulE p n ab ab 1) * E1 := by
      rw [abs_mul]; exact mul_le_mul hzabs hE1 (abs_nonneg _) (mul_nonneg hR20 (by linarith))
    have e2 : |(∑ i ∈ range n, z i - R ^ 2) * hornerE C (R ^ 2) (K - 1) 1| ≤ R ^ 2 * GmulE p n ab ab 1 * |C 1| := by
      rw [abs_mul]; exact mul_le_mul hze hP (abs_nonneg _) (mul_nonneg hR20 hεz)
    have := abs3 ((∑ i ∈ range n, z i) * (∑ i ∈ range n, p1 i - hornerE C (R ^ 2) (K - 1) 1))
      ((∑ i ∈ range n, z i - R ^ 2) * hornerE C (R ^ 2) (K - 1) 1)
      ((∑ i ∈ range n, z i) * (∑ i ∈ range n, p1 i) - (mulOp p n z p1).sum)
    rw [show (∑ i ∈ range n, z i) * (∑ i ∈ range n, p1 i - hornerE C (R ^ 2) (K - 1) 1) +
        (∑ i ∈ range n, z i - R ^ 2) * hornerE C (R ^ 2) (K - 1) 1 -
        ((∑ i ∈ range n, z i) * (∑ i ∈ range n, p1 i) - (mulOp p n z p1).sum) =
        (mulOp p n z p1).sum - R ^ 2 * hornerE C (R ^ 2) (K - 1) 1 by ring] at this
    nlinarith
  · rw [htdef, hTh]; exact t2 i
  · rw [htdef]; exact t3 i
  · rw [hEt]
    exact add_nonneg (add_nonneg (mul_nonneg (by linarith) hE10) (mul_nonneg hεz (abs_nonneg _))) hεt
  · rw [hTh]; exact hϑ0

/-- Lemma 34 (`lem:sincosr`) for SINR: for `r` with `|r| ≤ r̄ ≤ 1` and `|r_i| ≤ ā_i|r|`,
`|SINR(r) - sin r| ≤ δ_S|sin r|`, and the parts of SINR(r) are at most `ψ_s|r|`, each in `F p` -/
theorem lemma_sinr (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (r : ℕ → ℝ)
    (hr : ∀ i < n, F p (r i)) (ab : ℕ → ℝ) (hab0 : ∀ i, 0 ≤ ab i)
    (hab : ∀ i < n, |r i| ≤ ab i * |∑ i ∈ range n, r i|) (rb : ℝ) (hrb : |∑ i ∈ range n, r i| ≤ rb)
    (hrb1 : rb ≤ 1) (Fk : ℕ → ℕ → ℝ) (hF : ∀ k, ∀ i < n, F p (Fk k i)) (K : ℕ) (hK : 2 ≤ K) (e : ℤ) :
    |∑ i ∈ range n, sinR p n e r Fk K i - Real.sin (∑ i ∈ range n, r i)| ≤
        sinDelta p n ab rb Fk K * |Real.sin (∑ i ∈ range n, r i)| ∧
      (∀ i, |sinR p n e r Fk K i| ≤ sinPsi p n ab rb Fk K i * |∑ i ∈ range n, r i|) ∧
      ∀ i, F p (sinR p n e r Fk K i) := by
  obtain ⟨R, hR⟩ : ∃ R, R = ∑ i ∈ range n, r i := ⟨_, rfl⟩
  rw [← hR] at hab hrb ⊢
  have hu := u_pos p
  have hun : 0 ≤ u p ^ n := pow_nonneg hu.le n
  have hrb0 : 0 ≤ rb := (abs_nonneg R).trans hrb
  have hR1 : |R| ≤ 1 := hrb.trans hrb1
  have hA : |R| * |R| = R ^ 2 := by rw [abs_mul_abs_self, sq]
  have hR2 : R ^ 2 ≤ rb ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg R) hrb 2
  have hR20 : 0 ≤ R ^ 2 := sq_nonneg R
  have hrb2 : rb ^ 2 ≤ 1 := by rw [← one_pow 2]; exact pow_le_pow_left₀ hrb0 hrb1 2
  obtain ⟨c1, c2, c3, hP, hEt0, hϑ0⟩ :=
    sc_core p n hp hn hA3 r hr ab hab0 R hR hab rb hrb hrb1 sinC sinC_alt Fk hF K hK
  obtain ⟨t, ht⟩ : ∃ t, t = tOf p n r Fk K := ⟨_, rfl⟩
  obtain ⟨P, hPd⟩ : ∃ P, P = hornerE sinC (R ^ 2) (K - 1) 1 := ⟨_, rfl⟩
  obtain ⟨Et, hEt⟩ : ∃ Et, Et = scEt p n ab rb sinC Fk K := ⟨_, rfl⟩
  obtain ⟨ϑ, hϑ⟩ : ∃ ϑ, ϑ = scTh p n ab rb sinC Fk K := ⟨_, rfl⟩
  rw [← ht, ← hPd, ← hEt] at c1
  rw [← ht, ← hϑ] at c2
  rw [← ht] at c3
  rw [← hPd] at hP
  rw [← hEt] at hEt0
  rw [← hϑ] at hϑ0
  obtain ⟨εw, hεw⟩ : ∃ x, x = GmulE p n ab ϑ (|sinC 1| + Et) := ⟨_, rfl⟩
  obtain ⟨ω, hω⟩ : ∃ x, x = GmulP p n ab ϑ (|sinC 1| + Et) := ⟨_, rfl⟩
  obtain ⟨D, hDd⟩ : ∃ D, D = sinD p n ab rb Fk K := ⟨_, rfl⟩
  have hD : D = rb ^ 2 * (Et + εw) + rb ^ (2 * K) / ((2 * K + 1).factorial : ℝ) := by
    simp only [hDd, hεw, hϑ, hEt, sinD, sinWE]
  have hYd : sinY p n ab rb Fk K = GaddE p n ab (fun i => rb ^ 2 * ω i) (1 + D) := by
    simp only [hω, hϑ, hEt, hDd, sinY, sinWP]
  have hPsi : sinPsi p n ab rb Fk K = GaddP p n ab (fun i => rb ^ 2 * ω i) (1 + D) := by
    simp only [hω, hϑ, hEt, hDd, sinPsi, sinWP]
  have hDelta : sinDelta p n ab rb Fk K = u p ^ n + (D + sinY p n ab rb Fk K - u p ^ n) / (1 - rb ^ 2 / 6) := by
    simp only [hDd, sinDelta]
  obtain ⟨hεw0, hω0⟩ := Gmul_nonneg p n hA3 hab0 hϑ0 (Zb := |sinC 1| + Et) (add_nonneg (abs_nonneg _) hEt0)
  rw [← hεw] at hεw0
  simp only [← hω] at hω0
  have hfact : (0 : ℝ) < ((2 * K + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hD0 : 0 ≤ D := by
    rw [hD]
    exact add_nonneg (mul_nonneg (sq_nonneg _) (add_nonneg hEt0 hεw0)) (div_nonneg (pow_nonneg hrb0 _) hfact.le)
  -- `|t| ≤ r²(|s_1| + E_t)`
  have htabs : |∑ i ∈ range n, t i| ≤ R ^ 2 * (|sinC 1| + Et) := by
    have := abs_sub_abs_le_abs_sub (∑ i ∈ range n, t i) (R ^ 2 * P)
    rw [abs_mul, abs_of_nonneg hR20] at this
    have := mul_le_mul_of_nonneg_left hP hR20
    linarith
  -- `r' = 2^e r`
  have hσ : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) e
  have hσi : (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e = 1 := by rw [zpow_neg, inv_mul_cancel₀ hσ.ne']
  have hc0 : 0 ≤ (2 : ℝ) ^ e * |R| := mul_nonneg hσ.le (abs_nonneg R)
  have hr'F : ∀ i < n, F p ((2 : ℝ) ^ e * r i) := fun i hi => F_zpow_mul p e (hr i hi)
  have hr'α : ∀ i < n, |(2 : ℝ) ^ e * r i| ≤ (2 : ℝ) ^ e * |R| * ab i := fun i hi => by
    rw [abs_mul, abs_of_pos hσ, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((hab i hi).trans_eq (mul_comm _ _)) hσ.le
  have hr's : ∑ i ∈ range n, (2 : ℝ) ^ e * r i = (2 : ℝ) ^ e * R := by rw [← mul_sum, hR]
  -- `w = MUL(r', t)`
  obtain ⟨w1, w2, w3, w4⟩ := mul_G p n hp hn hA3 (fun i => (2 : ℝ) ^ e * r i) t
    (fun i => (2 : ℝ) ^ e * |R| * ab i) (fun j => |R| * |R| * ϑ j) hr'F c3 hr'α
    (fun j hj => by rw [hA]; exact c2 j hj) ((2 : ℝ) ^ e * |R| * (|R| * |R|) * (|sinC 1| + Et)) (by
      rw [hr's, abs_mul, abs_mul, abs_of_pos hσ, hA, mul_assoc ((2 : ℝ) ^ e * |R|)]
      exact mul_le_mul_of_nonneg_left htabs hc0)
  obtain ⟨gw1, gw2⟩ := Gmul_smul p n ab ϑ (|sinC 1| + Et) hc0 (mul_nonneg (abs_nonneg R) (abs_nonneg R))
  rw [gw1, hr's, ← hεw, hA] at w1
  simp only [gw2] at w2
  simp only [← hω, hA] at w2
  obtain ⟨w, hw⟩ : ∃ w, w = pt (mulOp p n (fun i => (2 : ℝ) ^ e * r i) t) := ⟨_, rfl⟩
  have hws : ∑ i ∈ range n, w i = (mulOp p n (fun i => (2 : ℝ) ^ e * r i) t).sum := by
    rw [hw]; exact (list_sum_getD _ n w4).symm
  have hwF : ∀ i < n, F p (w i) := fun i _ => by rw [hw]; exact w3 i
  have hwβ : ∀ j < n, |w j| ≤ (2 : ℝ) ^ e * |R| * (rb ^ 2 * ω j) := fun j _ => by
    rw [hw]
    refine (w2 j).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hR2 (hω0 j)) hc0
  -- the exact sum `r' + w` is within `2^e|r|D` of `2^e sin r`
  have hsin := sin_taylor R hR1 K
  rw [sin_horner R K (by omega), ← hPd] at hsin
  have hpow : |R| ^ (2 * K + 1) ≤ |R| * rb ^ (2 * K) := by
    rw [pow_succ, mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg R) hrb _) (abs_nonneg R)
  have hX : |∑ i ∈ range n, (2 : ℝ) ^ e * r i + ∑ i ∈ range n, w i - (2 : ℝ) ^ e * Real.sin R| ≤
      (2 : ℝ) ^ e * |R| * D := by
    rw [hr's, hws]
    have e1 : |(2 : ℝ) ^ e * R * (∑ i ∈ range n, t i - R ^ 2 * P)| ≤ (2 : ℝ) ^ e * |R| * (rb ^ 2 * Et) := by
      rw [abs_mul, abs_mul, abs_of_pos hσ]
      exact mul_le_mul_of_nonneg_left (c1.trans (mul_le_mul_of_nonneg_right hR2 hEt0)) hc0
    have e2 : |(2 : ℝ) ^ e * (R + R * (R ^ 2 * P) - Real.sin R)| ≤
        (2 : ℝ) ^ e * |R| * (rb ^ (2 * K) / ((2 * K + 1).factorial : ℝ)) := by
      rw [abs_mul, abs_of_pos hσ, abs_sub_comm, mul_assoc]
      refine mul_le_mul_of_nonneg_left (hsin.trans ?_) hσ.le
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right hpow hfact.le
    have e3 : |(mulOp p n (fun i => (2 : ℝ) ^ e * r i) t).sum - (2 : ℝ) ^ e * R * ∑ i ∈ range n, t i| ≤
        (2 : ℝ) ^ e * |R| * (rb ^ 2 * εw) := by
      rw [abs_sub_comm]
      refine w1.trans ?_
      rw [mul_assoc _ (R ^ 2)]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hR2 hεw0) hc0
    have := abs_add_le ((mulOp p n (fun i => (2 : ℝ) ^ e * r i) t).sum - (2 : ℝ) ^ e * R * ∑ i ∈ range n, t i +
      (2 : ℝ) ^ e * R * (∑ i ∈ range n, t i - R ^ 2 * P)) ((2 : ℝ) ^ e * (R + R * (R ^ 2 * P) - Real.sin R))
    have h4 := abs_add_le ((mulOp p n (fun i => (2 : ℝ) ^ e * r i) t).sum - (2 : ℝ) ^ e * R * ∑ i ∈ range n, t i)
      ((2 : ℝ) ^ e * R * (∑ i ∈ range n, t i - R ^ 2 * P))
    rw [show (mulOp p n (fun i => (2 : ℝ) ^ e * r i) t).sum - (2 : ℝ) ^ e * R * ∑ i ∈ range n, t i +
        (2 : ℝ) ^ e * R * (∑ i ∈ range n, t i - R ^ 2 * P) + (2 : ℝ) ^ e * (R + R * (R ^ 2 * P) - Real.sin R) =
        (2 : ℝ) ^ e * R + (mulOp p n (fun i => (2 : ℝ) ^ e * r i) t).sum - (2 : ℝ) ^ e * Real.sin R by ring]
      at this
    rw [hD]
    linarith
  have hsinR : |Real.sin R| ≤ |R| := by simpa using sin_taylor R hR1 0
  have hXabs : |∑ i ∈ range n, (2 : ℝ) ^ e * r i + ∑ i ∈ range n, w i| ≤
      (2 : ℝ) ^ e * |Real.sin R| + (2 : ℝ) ^ e * |R| * D := by
    have := abs_sub_abs_le_abs_sub (∑ i ∈ range n, (2 : ℝ) ^ e * r i + ∑ i ∈ range n, w i)
      ((2 : ℝ) ^ e * Real.sin R)
    rw [abs_mul, abs_of_pos hσ] at this
    linarith
  -- `Y = ADD(r', w)`
  obtain ⟨y1, -, y3, y4⟩ := add_G p n hp hn hA3 (fun i => (2 : ℝ) ^ e * r i) w (fun i => (2 : ℝ) ^ e * |R| * ab i)
    (fun j => (2 : ℝ) ^ e * |R| * (rb ^ 2 * ω j)) hr'F hwF hr'α hwβ _ le_rfl
  obtain ⟨-, y2, -, -⟩ := add_G p n hp hn hA3 (fun i => (2 : ℝ) ^ e * r i) w (fun i => (2 : ℝ) ^ e * |R| * ab i)
    (fun j => (2 : ℝ) ^ e * |R| * (rb ^ 2 * ω j)) hr'F hwF hr'α hwβ ((2 : ℝ) ^ e * |R| * (1 + D))
    (hXabs.trans (by have := mul_le_mul_of_nonneg_left hsinR hσ.le; linarith))
  obtain ⟨ga1, -⟩ := Gadd_smul p n ab (fun j => rb ^ 2 * ω j) 0 hc0
  obtain ⟨-, ga2⟩ := Gadd_smul p n ab (fun j => rb ^ 2 * ω j) (1 + D) hc0
  rw [mul_zero] at ga1
  rw [gaddE_split, ga1] at y1
  simp only [ga2] at y2
  obtain ⟨G0, hG0⟩ : ∃ G0, G0 = GaddE p n ab (fun j => rb ^ 2 * ω j) 0 := ⟨_, rfl⟩
  rw [← hG0] at y1
  have hG00 : 0 ≤ G0 := by
    rw [hG0]
    exact (Gadd_nonneg p n hA3 hab0 (fun j => mul_nonneg (sq_nonneg rb) (hω0 j)) le_rfl).1
  have hY : sinY p n ab rb Fk K = u p ^ n * (1 + D) + G0 := by rw [hYd, gaddE_split, ← hG0]
  -- scaling back by `2^{-e}`
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = addOp p n (fun i => (2 : ℝ) ^ e * r i) w := ⟨_, rfl⟩
  rw [← hYdef] at y1 y2 y3 y4
  have hsR : sinR p n e r Fk K = fun i => (2 : ℝ) ^ (-e) * Y.getD i 0 := by rw [hYdef, hw, ht]; rfl
  have hYs : ∑ i ∈ range n, sinR p n e r Fk K i = (2 : ℝ) ^ (-e) * Y.sum := by
    rw [hsR, ← mul_sum, list_sum_getD Y n y4]
  have hσ' : (0 : ℝ) < (2 : ℝ) ^ (-e) := zpow_pos (by norm_num) _
  have hfin1 : |Y.sum - (2 : ℝ) ^ e * Real.sin R| ≤
      (2 : ℝ) ^ e * (u p ^ n * |Real.sin R| + |R| * (D + u p ^ n * D + G0)) := by
    have h := abs_sub_le Y.sum (∑ i ∈ range n, (2 : ℝ) ^ e * r i + ∑ i ∈ range n, w i)
      ((2 : ℝ) ^ e * Real.sin R)
    rw [abs_sub_comm Y.sum (∑ i ∈ range n, (2 : ℝ) ^ e * r i + ∑ i ∈ range n, w i)] at h
    have := mul_le_mul_of_nonneg_left hXabs hun
    linarith
  have hfin2 : |∑ i ∈ range n, sinR p n e r Fk K i - Real.sin R| ≤
      u p ^ n * |Real.sin R| + |R| * (D + u p ^ n * D + G0) := by
    rw [hYs, show (2 : ℝ) ^ (-e) * Y.sum - Real.sin R = (2 : ℝ) ^ (-e) * (Y.sum - (2 : ℝ) ^ e * Real.sin R) by
      rw [mul_sub, ← mul_assoc, hσi, one_mul], abs_mul, abs_of_pos hσ']
    calc (2 : ℝ) ^ (-e) * |Y.sum - (2 : ℝ) ^ e * Real.sin R|
        ≤ (2 : ℝ) ^ (-e) * ((2 : ℝ) ^ e * (u p ^ n * |Real.sin R| + |R| * (D + u p ^ n * D + G0))) :=
          mul_le_mul_of_nonneg_left hfin1 hσ'.le
      _ = _ := by rw [← mul_assoc, hσi, one_mul]
  refine ⟨?_, fun i => ?_, fun i => ?_⟩
  · -- `|r| ≤ |sin r|/(1 - r̄²/6)`
    have hq : 0 < 1 - rb ^ 2 / 6 := by linarith
    have hRs : |R| ≤ |Real.sin R| / (1 - rb ^ 2 / 6) := by
      rw [le_div_iff₀ hq]
      refine le_trans ?_ (abs_sin_ge R hR1)
      exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg R)
    have hE0 : 0 ≤ D + u p ^ n * D + G0 := by positivity
    rw [hDelta, hY, show D + (u p ^ n * (1 + D) + G0) - u p ^ n = D + u p ^ n * D + G0 by ring]
    have := mul_le_mul_of_nonneg_right hRs hE0
    rw [div_mul_eq_mul_div] at this
    rw [add_mul, div_mul_eq_mul_div, mul_comm (D + u p ^ n * D + G0)]
    linarith
  · rw [hsR, abs_mul, abs_of_pos hσ', hPsi]
    calc (2 : ℝ) ^ (-e) * |Y.getD i 0|
        ≤ (2 : ℝ) ^ (-e) * ((2 : ℝ) ^ e * |R| * GaddP p n ab (fun j => rb ^ 2 * ω j) (1 + D) i) :=
          mul_le_mul_of_nonneg_left (y2 i) hσ'.le
      _ = _ := by rw [← mul_assoc, ← mul_assoc, hσi, one_mul, mul_comm]
  · rw [hsR]
    exact F_zpow_mul p (-e) (y3 i)

/-- Lemma 34 (`lem:sincosr`) for COSR: for `r` with `|r| ≤ r̄ ≤ 1` and `|r_i| ≤ ā_i|r|`,
`|COSR(r) - cos r| ≤ δ_C cos r`, and the parts of COSR(r) are at most `ψ_c`, each in `F p` -/
theorem lemma_cosr (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (r : ℕ → ℝ)
    (hr : ∀ i < n, F p (r i)) (ab : ℕ → ℝ) (hab0 : ∀ i, 0 ≤ ab i)
    (hab : ∀ i < n, |r i| ≤ ab i * |∑ i ∈ range n, r i|) (rb : ℝ) (hrb : |∑ i ∈ range n, r i| ≤ rb)
    (hrb1 : rb ≤ 1) (Fk : ℕ → ℕ → ℝ) (hF : ∀ k, ∀ i < n, F p (Fk k i)) (K : ℕ) (hK : 2 ≤ K) :
    |∑ i ∈ range n, cosR p n r Fk K i - Real.cos (∑ i ∈ range n, r i)| ≤
        cosDelta p n ab rb Fk K * Real.cos (∑ i ∈ range n, r i) ∧
      (∀ i, |cosR p n r Fk K i| ≤ cosPsi p n ab rb Fk K i) ∧ ∀ i, F p (cosR p n r Fk K i) := by
  obtain ⟨R, hR⟩ : ∃ R, R = ∑ i ∈ range n, r i := ⟨_, rfl⟩
  rw [← hR] at hab hrb ⊢
  have hu := u_pos p
  have hun : 0 ≤ u p ^ n := pow_nonneg hu.le n
  have hrb0 : 0 ≤ rb := (abs_nonneg R).trans hrb
  have hR1 : |R| ≤ 1 := hrb.trans hrb1
  have hR2 : R ^ 2 ≤ rb ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg R) hrb 2
  obtain ⟨c1, c2, c3, -, hEt0, hϑ0⟩ :=
    sc_core p n hp hn hA3 r hr ab hab0 R hR hab rb hrb hrb1 cosC cosC_alt Fk hF K hK
  obtain ⟨t, ht⟩ : ∃ t, t = tOf p n r Fk K := ⟨_, rfl⟩
  obtain ⟨P, hPd⟩ : ∃ P, P = hornerE cosC (R ^ 2) (K - 1) 1 := ⟨_, rfl⟩
  obtain ⟨Et, hEt⟩ : ∃ Et, Et = scEt p n ab rb cosC Fk K := ⟨_, rfl⟩
  obtain ⟨ϑ, hϑ⟩ : ∃ ϑ, ϑ = scTh p n ab rb cosC Fk K := ⟨_, rfl⟩
  rw [← ht, ← hPd, ← hEt] at c1
  rw [← ht, ← hϑ] at c2
  rw [← ht] at c3
  rw [← hEt] at hEt0
  rw [← hϑ] at hϑ0
  obtain ⟨D, hDd⟩ : ∃ D, D = cosD p n ab rb Fk K := ⟨_, rfl⟩
  have hD : D = rb ^ 2 * Et + rb ^ (2 * K) / ((2 * K).factorial : ℝ) := by simp only [hDd, hEt, cosD]
  have hYd : cosY p n ab rb Fk K = GaddfE p n (fun i => rb ^ 2 * ϑ i) 1 (1 + D) := by
    simp only [hϑ, hDd, cosY]
  have hPsi : cosPsi p n ab rb Fk K = GaddfP p n (fun i => rb ^ 2 * ϑ i) 1 (1 + D) := by
    simp only [hϑ, hDd, cosPsi]
  have hDelta : cosDelta p n ab rb Fk K = u p ^ n + (D + cosY p n ab rb Fk K - u p ^ n) / cosLo rb := by
    simp only [hDd, cosDelta]
  have hfact : (0 : ℝ) < ((2 * K).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hD0 : 0 ≤ D := by rw [hD]; exact add_nonneg (mul_nonneg (sq_nonneg _) hEt0) (by positivity)
  have htα : ∀ i < n, |t i| ≤ rb ^ 2 * ϑ i := fun i hi => (c2 i hi).trans (mul_le_mul_of_nonneg_right hR2 (hϑ0 i))
  -- the exact sum `t + 1` is within `D_c` of `cos r`
  have hcos := cos_taylor R hR1 K
  rw [cos_horner R K (by omega), ← hPd] at hcos
  have hX : |∑ i ∈ range n, t i + 1 - Real.cos R| ≤ D := by
    have e1 : |∑ i ∈ range n, t i - R ^ 2 * P| ≤ rb ^ 2 * Et := c1.trans (mul_le_mul_of_nonneg_right hR2 hEt0)
    have e2 : |1 + R ^ 2 * P - Real.cos R| ≤ rb ^ (2 * K) / ((2 * K).factorial : ℝ) := by
      rw [abs_sub_comm]
      exact hcos.trans (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg R) hrb _) hfact.le)
    have := abs_add_le (∑ i ∈ range n, t i - R ^ 2 * P) (1 + R ^ 2 * P - Real.cos R)
    rw [show ∑ i ∈ range n, t i - R ^ 2 * P + (1 + R ^ 2 * P - Real.cos R) = ∑ i ∈ range n, t i + 1 - Real.cos R
      by ring] at this
    rw [hD]
    linarith
  have hlo := cos_ge_cosLo R rb hrb hrb1
  have hlo0 := cosLo_pos hrb0 hrb1
  have hcos0 : 0 < Real.cos R := lt_of_lt_of_le hlo0 hlo
  have hXabs : |∑ i ∈ range n, t i + 1| ≤ Real.cos R + D := by
    have := abs_sub_abs_le_abs_sub (∑ i ∈ range n, t i + 1) (Real.cos R)
    rw [abs_of_pos hcos0] at this
    linarith
  -- `COSR(r) = ADDF(t, 1)`
  obtain ⟨y1, -, y3, y4⟩ := addf_G p n hp hn t 1 (fun i => rb ^ 2 * ϑ i) 1 c3 (F_one p) htα (by simp) _ le_rfl
  obtain ⟨-, y2, -, -⟩ := addf_G p n hp hn t 1 (fun i => rb ^ 2 * ϑ i) 1 c3 (F_one p) htα (by simp) (1 + D)
    (hXabs.trans (by linarith [Real.cos_le_one R]))
  rw [gaddfE_split] at y1
  obtain ⟨G0, hG0⟩ : ∃ G0, G0 = GaddfE p n (fun i => rb ^ 2 * ϑ i) 1 0 := ⟨_, rfl⟩
  rw [← hG0] at y1
  have hG00 : 0 ≤ G0 := by
    rw [hG0]; exact (Gaddf_nonneg p n (fun i => mul_nonneg (sq_nonneg rb) (hϑ0 i)) zero_le_one le_rfl).1
  have hY : cosY p n ab rb Fk K = u p ^ n * (1 + D) + G0 := by rw [hYd, gaddfE_split, ← hG0]
  have hcR : cosR p n r Fk K = pt (addfOp p n t 1) := by rw [ht]; rfl
  have hCs : ∑ i ∈ range n, cosR p n r Fk K i = (addfOp p n t 1).sum := by
    rw [hcR]; exact (list_sum_getD _ n y4).symm
  refine ⟨?_, fun i => ?_, fun i => ?_⟩
  · have hfin : |∑ i ∈ range n, cosR p n r Fk K i - Real.cos R| ≤
        u p ^ n * Real.cos R + (D + u p ^ n * D + G0) := by
      rw [hCs]
      have h := abs_sub_le (addfOp p n t 1).sum (∑ i ∈ range n, t i + 1) (Real.cos R)
      rw [abs_sub_comm (addfOp p n t 1).sum (∑ i ∈ range n, t i + 1)] at h
      have := mul_le_mul_of_nonneg_left hXabs hun
      linarith
    have hE0 : 0 ≤ D + u p ^ n * D + G0 := by positivity
    have hEc : D + u p ^ n * D + G0 ≤ (D + u p ^ n * D + G0) / cosLo rb * Real.cos R := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlo0]
      exact mul_le_mul_of_nonneg_left hlo hE0
    rw [hDelta, hY, show D + (u p ^ n * (1 + D) + G0) - u p ^ n = D + u p ^ n * D + G0 by ring, add_mul]
    linarith
  · rw [hcR, hPsi]; exact y2 i
  · rw [hcR]; exact y3 i

/-- Lemma 34 for `|r_0| < u^{n/2}`, where SINR(r) = r: `|r - sin r| ≤ δ_S|sin r|` with `δ_S = r̄²/(6 - r̄²)` -/
theorem sinr_small (R rb : ℝ) (hR : |R| ≤ rb) (hrb : rb ≤ 1) :
    |R - Real.sin R| ≤ rb ^ 2 / (6 - rb ^ 2) * |Real.sin R| := by
  have hR1 : |R| ≤ 1 := hR.trans hrb
  have h := sin_taylor R hR1 1
  simp only [sum_range_one, sinC, pow_zero, mul_zero, zero_add, pow_one, Nat.factorial, Nat.succ_eq_add_one,
    mul_one, Nat.cast_one, div_one, one_mul] at h
  norm_num at h
  have hs := abs_sin_ge R hR1
  have hR2 : R ^ 2 ≤ rb ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg R) hR 2
  have hrb2 : rb ^ 2 ≤ 1 := by nlinarith [abs_nonneg R]
  have h6 : 0 < 6 - rb ^ 2 := by linarith
  obtain ⟨q, hq⟩ : ∃ q, q = rb ^ 2 / (6 - rb ^ 2) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; exact div_nonneg (sq_nonneg _) h6.le
  have hqe : q * (6 - rb ^ 2) = rb ^ 2 := by rw [hq, div_mul_cancel₀ _ h6.ne']
  have hq6 : R ^ 2 ≤ q * (6 - R ^ 2) := by nlinarith
  have h3 : |R| ^ 3 = |R| * R ^ 2 := by rw [pow_succ, mul_comm, sq_abs]
  rw [← hq, abs_sub_comm]
  rw [h3] at h
  have := mul_le_mul_of_nonneg_left hs hq0
  nlinarith [abs_nonneg R, mul_le_mul_of_nonneg_left hq6 (abs_nonneg R)]

/-- Lemma 34 for `|r_0| < u^{n/2}`, where COSR(r) = 1: `|1 - cos r| ≤ δ_C cos r` with `δ_C = r̄²/(2 cos₋ r̄)` -/
theorem cosr_small (R rb : ℝ) (hR : |R| ≤ rb) (hrb : rb ≤ 1) :
    |1 - Real.cos R| ≤ rb ^ 2 / (2 * cosLo rb) * Real.cos R := by
  have hrb0 : 0 ≤ rb := (abs_nonneg R).trans hR
  have h := cos_taylor R (hR.trans hrb) 1
  simp only [sum_range_one, cosC, pow_zero, mul_zero, div_one, Nat.factorial, Nat.succ_eq_add_one, mul_one,
    Nat.cast_one] at h
  norm_num at h
  have hR2 : R ^ 2 ≤ rb ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg R) hR 2
  have hlo := cos_ge_cosLo R rb hR hrb
  have hlo0 := cosLo_pos hrb0 hrb
  rw [abs_sub_comm, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hlo (sq_nonneg rb)]

/-- Lemma 34 (`lem:sincosr`) for SINR: below `|r_0| < u^{n/2}`, where `|r| ≤ r̄_min ≤ 1`, SINR(r) = r is within
`δ_S = r̄_min²/(6 - r̄_min²)` relative of `sin r`, with parts at most `ā|r|`; otherwise `lemma_sinr` -/
theorem lemma34_sin (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (r : ℕ → ℝ)
    (hr : ∀ i < n, F p (r i)) (ab : ℕ → ℝ) (hab0 : ∀ i, 0 ≤ ab i)
    (hab : ∀ i < n, |r i| ≤ ab i * |∑ i ∈ range n, r i|) (rb rbm : ℝ)
    (hrb : ¬|r 0| < u p ^ (n / 2) → |∑ i ∈ range n, r i| ≤ rb) (hrb1 : rb ≤ 1)
    (hrbm : |r 0| < u p ^ (n / 2) → |∑ i ∈ range n, r i| ≤ rbm) (hrbm1 : rbm ≤ 1) (Fk : ℕ → ℕ → ℝ)
    (hF : ∀ k, ∀ i < n, F p (Fk k i)) (K : ℕ) (hK : 2 ≤ K) (e : ℤ) :
    |∑ i ∈ range n, sinRN p n e r Fk K i - Real.sin (∑ i ∈ range n, r i)| ≤
        (if |r 0| < u p ^ (n / 2) then rbm ^ 2 / (6 - rbm ^ 2) else sinDelta p n ab rb Fk K) *
          |Real.sin (∑ i ∈ range n, r i)| ∧
      (∀ i, |sinRN p n e r Fk K i| ≤
        (if |r 0| < u p ^ (n / 2) then (if i < n then ab i else 0) else sinPsi p n ab rb Fk K i) *
          |∑ i ∈ range n, r i|) ∧
      ∀ i, F p (sinRN p n e r Fk K i) := by
  by_cases hs : |r 0| < u p ^ (n / 2)
  · simp only [sinRN, hs, ite_true]
    have hsum : ∑ i ∈ range n, (if i < n then r i else 0) = ∑ i ∈ range n, r i :=
      sum_congr rfl fun i hi => by simp [mem_range.mp hi]
    refine ⟨?_, fun i => ?_, fun i => ?_⟩
    · rw [hsum]
      exact sinr_small _ rbm (hrbm hs) hrbm1
    · split_ifs with hi
      · exact hab i hi
      · simp
    · split_ifs with hi
      · exact hr i hi
      · exact F_zero p
  · simp only [sinRN, hs, ite_false]
    exact lemma_sinr p n hp hn hA3 r hr ab hab0 hab rb (hrb hs) hrb1 Fk hF K hK e

/-- Lemma 34 (`lem:sincosr`) for COSR: below `|r_0| < u^{n/2}`, where `|r| ≤ r̄_min ≤ 1`, COSR(r) = 1 is within
`δ_C = r̄_min²/(2 cos₋ r̄_min)` relative of `cos r`, with parts `(1, 0, …, 0)`; otherwise `lemma_cosr` -/
theorem lemma34_cos (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (r : ℕ → ℝ)
    (hr : ∀ i < n, F p (r i)) (ab : ℕ → ℝ) (hab0 : ∀ i, 0 ≤ ab i)
    (hab : ∀ i < n, |r i| ≤ ab i * |∑ i ∈ range n, r i|) (rb rbm : ℝ)
    (hrb : ¬|r 0| < u p ^ (n / 2) → |∑ i ∈ range n, r i| ≤ rb) (hrb1 : rb ≤ 1)
    (hrbm : |r 0| < u p ^ (n / 2) → |∑ i ∈ range n, r i| ≤ rbm) (hrbm1 : rbm ≤ 1) (Fk : ℕ → ℕ → ℝ)
    (hF : ∀ k, ∀ i < n, F p (Fk k i)) (K : ℕ) (hK : 2 ≤ K) :
    |∑ i ∈ range n, cosRN p n r Fk K i - Real.cos (∑ i ∈ range n, r i)| ≤
        (if |r 0| < u p ^ (n / 2) then rbm ^ 2 / (2 * cosLo rbm) else cosDelta p n ab rb Fk K) *
          Real.cos (∑ i ∈ range n, r i) ∧
      (∀ i, |cosRN p n r Fk K i| ≤
        if |r 0| < u p ^ (n / 2) then (if i = 0 then 1 else 0) else cosPsi p n ab rb Fk K i) ∧
      ∀ i, F p (cosRN p n r Fk K i) := by
  by_cases hs : |r 0| < u p ^ (n / 2)
  · simp only [cosRN, hs, ite_true]
    have hsum : ∑ i ∈ range n, (if i = 0 then (1 : ℝ) else 0) = 1 := by
      rw [sum_ite_eq']
      simp [mem_range.mpr (show 0 < n by omega)]
    refine ⟨?_, fun i => ?_, fun i => ?_⟩
    · rw [hsum]
      exact cosr_small _ rbm (hrbm hs) hrbm1
    · split_ifs <;> simp
    · split_ifs
      · exact F_one p
      · exact F_zero p
  · simp only [cosRN, hs, ite_false]
    exact lemma_cosr p n hp hn hA3 r hr ab hab0 hab rb (hrb hs) hrb1 Fk hF K hK

end ExpansionBounds
