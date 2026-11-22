import ExpansionBounds.Horner

/-!
# Lemma 13's bounds scale with their operands

"The bounds are homogeneous of degree one in the operands' part bounds, `λ` and `Z̄` together": scaling `α` by `c`,
`β` by `c'` and `Z̄` by `cc'` scales `G_MUL`'s error and part bounds by `cc'`, and scaling `α`, `β` and `Z̄` by `c`
scales `G_ADD`'s by `c`. The bounds are nonnegative for nonnegative operands, and `G_ADDF`, with `λ_0 = α_0 + β_0`,
bounds ADDF. SINR and COSR state their bounds in units of `|r|` and `r²`.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) (n : ℕ)

theorem levD_smul (A : ℕ → ℝ) (T : ℕ → ℕ) (uu c : ℝ) : ∀ m, levD (fun k => c * A k) T uu m = c * levD A T uu m
  | 0 => rfl
  | m + 1 => by
    simp only [levD]
    rw [levD_smul A T uu c m]
    ring

theorem sigmaX_smul (X : ℕ → ℝ) (c : ℝ) (l : ℕ) : sigmaX n (fun m => c * X m) l = c * sigmaX n X l := by
  simp [sigmaX, mul_sum]

theorem Vb_smul (X : ℕ → ℝ) {c : ℝ} (hc : 0 ≤ c) (j : ℕ) : Vb p n (fun m => c * X m) j = c * Vb p n X j := by
  simp only [Vb, sigmaX_smul]
  rw [mul_min_of_nonneg _ _ hc]
  congr 1
  ring

theorem gErr_smul (X : ℕ → ℝ) (Zb Fb : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    gErr p n (fun m => c * X m) (c * Zb) (c * Fb) = c * gErr p n X Zb Fb := by
  simp only [gErr, Vb_smul p n X hc]
  rw [mul_add, mul_add]
  congr 1
  · ring
  · rw [mul_sum]
    exact sum_congr rfl fun _ _ => by ring

theorem gParts_smul (X : ℕ → ℝ) (Zb Fb : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ∀ i, gParts p n (fun m => c * X m) (c * Zb) (c * Fb) i = c * gParts p n X Zb Fb i
  | 0 => by
    simp only [gParts, Vb_smul p n X hc, ← mul_sum]
    ring
  | i + 1 => by
    simp only [gParts, Vb_smul p n X hc, ← mul_sum]
    rw [gParts_smul X Zb Fb hc i]
    split_ifs <;> ring

theorem mulP_smul (α β : ℕ → ℝ) (c c' : ℝ) (m : ℕ) :
    mulP n (fun i => c * α i) (fun j => c' * β j) m = c * c' * mulP n α β m := by
  simp only [mulP, mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem mulA_smul (α β : ℕ → ℝ) (c c' : ℝ) (m : ℕ) :
    mulA p n (fun i => c * α i) (fun j => c' * β j) m = c * c' * mulA p n α β m := by
  simp only [mulA, mulP_smul]
  split_ifs <;> ring

theorem mulDelta_smul (α β : ℕ → ℝ) (c c' : ℝ) :
    mulDelta n (fun i => c * α i) (fun j => c' * β j) = c * c' * mulDelta n α β := by
  simp only [mulDelta, mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem mulX_smul (α β : ℕ → ℝ) (c c' : ℝ) (m : ℕ) :
    mulX p n (fun i => c * α i) (fun j => c' * β j) m = c * c' * mulX p n α β m := by
  have hA : mulA p n (fun i => c * α i) (fun j => c' * β j) = fun k => c * c' * mulA p n α β k :=
    funext fun k => mulA_smul p n α β c c' k
  simp only [mulX, levX, hA, levD_smul]
  split_ifs <;> ring

theorem mulR_smul (α β : ℕ → ℝ) (c c' : ℝ) :
    mulR p n (fun i => c * α i) (fun j => c' * β j) = c * c' * mulR p n α β := by
  simp only [mulR, mulX_smul]
  ring

/-- `G_MUL(cα, c'β; cc'Z̄) = cc' G_MUL(α, β; Z̄)`, error and parts -/
theorem Gmul_smul (α β : ℕ → ℝ) (Zb : ℝ) {c c' : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c') :
    GmulE p n (fun i => c * α i) (fun j => c' * β j) (c * c' * Zb) = c * c' * GmulE p n α β Zb ∧
      ∀ i, GmulP p n (fun i => c * α i) (fun j => c' * β j) (c * c' * Zb) i = c * c' * GmulP p n α β Zb i := by
  have hX : mulX p n (fun i => c * α i) (fun j => c' * β j) = fun m => c * c' * mulX p n α β m :=
    funext fun m => mulX_smul p n α β c c' m
  have hF : mulR p n (fun i => c * α i) (fun j => c' * β j) + mulDelta n (fun i => c * α i) (fun j => c' * β j) =
      c * c' * (mulR p n α β + mulDelta n α β) := by
    rw [mulR_smul, mulDelta_smul]
    ring
  have hcc := mul_nonneg hc hc'
  refine ⟨?_, fun i => ?_⟩
  · simp only [GmulE, hX, hF]
    exact gErr_smul p n _ _ _ hcc
  · simp only [GmulP, hX, hF]
    exact gParts_smul p n _ _ _ hcc i

theorem pairA_smul (lam : ℕ → ℝ) (c : ℝ) (m : ℕ) : pairA p n (fun k => c * lam k) m = c * pairA p n lam m := by
  simp only [pairA]
  split_ifs <;> ring

theorem pairX_smul (lam : ℕ → ℝ) (c : ℝ) (m : ℕ) : pairX p n (fun k => c * lam k) m = c * pairX p n lam m := by
  have hA : pairA p n (fun k => c * lam k) = fun k => c * pairA p n lam k := funext fun k => pairA_smul p n lam c k
  simp only [pairX, levX, hA, levD_smul]
  split_ifs <;> ring

/-- `G_ADD(cα, cβ; cZ̄) = c G_ADD(α, β; Z̄)`, error and parts -/
theorem Gadd_smul (α β : ℕ → ℝ) (Zb : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    GaddE p n (fun i => c * α i) (fun j => c * β j) (c * Zb) = c * GaddE p n α β Zb ∧
      ∀ i, GaddP p n (fun i => c * α i) (fun j => c * β j) (c * Zb) i = c * GaddP p n α β Zb i := by
  have hlam : (fun m => c * α m + c * β m) = fun m => c * (α m + β m) := funext fun m => by ring
  have hX : pairX p n (fun m => c * α m + c * β m) = fun m => c * pairX p n (fun m => α m + β m) m := by
    rw [hlam]
    exact funext fun m => pairX_smul p n _ c m
  have hR : pairR p n (fun m => c * α m + c * β m) = c * pairR p n (fun m => α m + β m) := by
    simp only [pairR, hX]
    ring
  refine ⟨?_, fun i => ?_⟩
  · simp only [GaddE, hX, hR]
    exact gErr_smul p n _ _ _ hc
  · simp only [GaddP, hX, hR]
    exact gParts_smul p n _ _ _ hc i

theorem levD_nonneg {A : ℕ → ℝ} {T : ℕ → ℕ} {uu : ℝ} (hA : ∀ k, 0 ≤ A k) (hu : 0 ≤ uu) (m : ℕ)
    (hT : ∀ k < m, (T k : ℝ) * uu < 1) : 0 ≤ levD A T uu m := by
  induction m with
  | zero => exact hA 0
  | succ m ih =>
    simp only [levD]
    have h1 : 0 < 1 - (T m : ℝ) * uu := by linarith [hT m (by omega)]
    exact add_nonneg (hA _) (div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hu)
      (ih fun k hk => hT k (by omega))) h1.le)

theorem Vb_nonneg {X : ℕ → ℝ} (hX : ∀ m, 0 ≤ X m) (j : ℕ) : 0 ≤ Vb p n X j :=
  le_min (hX _) (mul_nonneg (mul_nonneg (us_nonneg p) (pow_nonneg (by linarith [u_pos p]) _))
    (sum_nonneg fun m _ => hX m))

theorem gErr_split (X : ℕ → ℝ) (Zb Fb : ℝ) : gErr p n X Zb Fb = u p ^ n * Zb + gErr p n X 0 Fb := by
  simp only [gErr]
  ring

theorem gErr_nonneg {X : ℕ → ℝ} (hX : ∀ m, 0 ≤ X m) {Zb Fb : ℝ} (hZ : 0 ≤ Zb) (hF : 0 ≤ Fb) :
    0 ≤ gErr p n X Zb Fb := by
  have hu := u_pos p
  exact add_nonneg (add_nonneg (mul_nonneg (pow_nonneg hu.le _) hZ) (mul_nonneg (by positivity) hF))
    (sum_nonneg fun j _ => mul_nonneg (by positivity) (Vb_nonneg p n hX j))

theorem gParts_nonneg {X : ℕ → ℝ} (hX : ∀ m, 0 ≤ X m) {Zb Fb : ℝ} (hZ : 0 ≤ Zb) (hF : 0 ≤ Fb) :
    ∀ i, 0 ≤ gParts p n X Zb Fb i
  | 0 => mul_nonneg (by linarith [u_pos p]) (add_nonneg (add_nonneg hZ hF)
      (sum_nonneg fun j _ => Vb_nonneg p n hX j))
  | i + 1 => by
    simp only [gParts]
    split_ifs
    · exact mul_nonneg (by linarith [u_pos p]) (add_nonneg (mul_nonneg (u_pos p).le
        (gParts_nonneg hX hZ hF i)) (sum_nonneg fun j _ => Vb_nonneg p n hX j))
    · exact le_rfl

theorem mulX_nonneg (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {α β : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i) (hβ : ∀ j, 0 ≤ β j)
    (m : ℕ) : 0 ≤ mulX p n α β m := by
  have hu := u_pos p
  have hP : ∀ k, 0 ≤ mulP n α β k := fun k =>
    sum_nonneg fun i _ => sum_nonneg fun j _ => by split_ifs; exacts [mul_nonneg (hα i) (hβ j), le_rfl]
  have hA : ∀ k, 0 ≤ mulA p n α β k := fun k => by
    have h1 : 0 ≤ 1 + u p := by linarith
    simp only [mulA]
    split_ifs
    · simpa using mul_nonneg h1 (hP k)
    · exact add_nonneg (mul_nonneg h1 (hP k)) (mul_nonneg hu.le (hP _))
    · exact add_nonneg (hP n) (mul_nonneg hu.le (hP _))
    · exact le_rfl
  have hT : ∀ k < n, (mulT k : ℝ) * u p < 1 := fun k hk => by
    have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
    have : (mulT k : ℝ) ≤ (n : ℝ) ^ 2 + n := by
      simp only [mulT]
      push_cast
      nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    nlinarith
  have hQ : ((n ^ 2 + n - 1 : ℕ) : ℝ) * u p < 1 := by
    have : ((n ^ 2 + n - 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 + n := by exact_mod_cast Nat.sub_le (n ^ 2 + n) 1
    nlinarith
  simp only [mulX, levX]
  split_ifs with hm
  · exact div_nonneg (levD_nonneg hA hu.le m fun k hk => hT k (by omega)) (by linarith [hT m hm])
  · exact div_nonneg (levD_nonneg hA hu.le n hT) (by linarith)

theorem pairX_nonneg (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {lam : ℕ → ℝ} (hl : ∀ m, 0 ≤ lam m) (m : ℕ) :
    0 ≤ pairX p n lam m := by
  have hu := u_pos p
  have hA : ∀ k, 0 ≤ pairA p n lam k := fun k => by
    have h1 : 0 ≤ 1 + u p := by linarith
    simp only [pairA]
    split_ifs
    · simpa using mul_nonneg h1 (hl k)
    · exact add_nonneg (mul_nonneg h1 (hl k)) (mul_nonneg hu.le (hl _))
    · exact mul_nonneg hu.le (hl _)
    · exact le_rfl
  have hT : ∀ k < n, ((id k : ℕ) : ℝ) * u p < 1 := fun k hk => by
    have : (k : ℝ) ≤ (n : ℝ) ^ 2 + n := by
      have : (k : ℝ) ≤ n := by exact_mod_cast hk.le
      nlinarith
    simp only [id]
    nlinarith
  have hQ : ((n - 1 : ℕ) : ℝ) * u p < 1 := by
    have : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 + n := by
      have : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
      nlinarith
    nlinarith
  simp only [pairX, levX]
  split_ifs with hm
  · exact div_nonneg (levD_nonneg hA hu.le m fun k hk => hT k (by omega)) (by linarith [hT m hm])
  · exact div_nonneg (levD_nonneg hA hu.le n hT) (by linarith)

theorem Gmul_nonneg (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {α β : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i) (hβ : ∀ j, 0 ≤ β j)
    {Zb : ℝ} (hZ : 0 ≤ Zb) : 0 ≤ GmulE p n α β Zb ∧ ∀ i, 0 ≤ GmulP p n α β Zb i := by
  have hX := mulX_nonneg p n hA3 hα hβ
  have hR : 0 ≤ mulR p n α β := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (u_pos p).le) (hX n)
  have hΔ : 0 ≤ mulDelta n α β :=
    sum_nonneg fun i _ => sum_nonneg fun j _ => by split_ifs; exacts [mul_nonneg (hα i) (hβ j), le_rfl]
  exact ⟨gErr_nonneg p n hX hZ (add_nonneg hR hΔ), gParts_nonneg p n hX hZ (add_nonneg hR hΔ)⟩

theorem Gadd_nonneg (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {α β : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i) (hβ : ∀ j, 0 ≤ β j)
    {Zb : ℝ} (hZ : 0 ≤ Zb) : 0 ≤ GaddE p n α β Zb ∧ ∀ i, 0 ≤ GaddP p n α β Zb i := by
  have hX := pairX_nonneg p n hA3 (lam := fun m => α m + β m) (fun m => add_nonneg (hα m) (hβ m))
  have hR : 0 ≤ pairR p n (fun m => α m + β m) := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (u_pos p).le) (hX n)
  exact ⟨gErr_nonneg p n hX hZ hR, gParts_nonneg p n hX hZ hR⟩

/-- `G_ADDF(α, β_0; Z̄)`'s error bound, with `λ_0 = α_0 + β_0` and `R = Δ = 0` -/
noncomputable def GaddfE (α : ℕ → ℝ) (β0 Zb : ℝ) : ℝ := gErr p n (addfX p n α (α 0 + β0)) Zb 0

/-- `G_ADDF(α, β_0; Z̄)`'s part bounds -/
noncomputable def GaddfP (α : ℕ → ℝ) (β0 Zb : ℝ) : ℕ → ℝ := gParts p n (addfX p n α (α 0 + β0)) Zb 0

variable [Prec_gt_0 p] in
/-- `G_ADDF` bounds ADDF: for `a` with part bounds `α`, `|b| ≤ β_0` and `|a + b| ≤ Z̄` -/
theorem addf_G (hp : 1 < p) (hn : 1 ≤ n) (a : ℕ → ℝ) (b : ℝ) (α : ℕ → ℝ) (β0 : ℝ) (ha : ∀ i < n, F p (a i))
    (hb : F p b) (hα : ∀ i < n, |a i| ≤ α i) (hβ : |b| ≤ β0) (Zb : ℝ) (hZ : |∑ i ∈ range n, a i + b| ≤ Zb) :
    |(∑ i ∈ range n, a i + b) - (addfOp p n a b).sum| ≤ GaddfE p n α β0 Zb ∧
      (∀ i, |(addfOp p n a b).getD i 0| ≤ GaddfP p n α β0 Zb i) ∧ (∀ i, F p ((addfOp p n a b).getD i 0)) ∧
      (addfOp p n a b).length ≤ n := by
  have hlam : |a 0 + b| ≤ α 0 + β0 := (abs_add_le _ _).trans (add_le_add (hα 0 hn) hβ)
  obtain ⟨r1, r2, r3, -, -⟩ := lemma13_addf p hp hn a b ha hb α hα _ hlam Zb hZ
  have hF : ∀ i ≤ n, F p (addfLevels p n a b i) := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hch := addf_chain p (n' + 1) hp a b ha hb α hα _ hlam
    intro i hi
    rcases Nat.lt_or_ge i (n' + 1) with hlt | hge
    · simp only [addfLevels, hlt, ite_true]
      exact F_twoSum_fst p _ _
    · obtain rfl : i = n' + 1 := by omega
      simp only [addfLevels, lt_irrefl, ite_false, ite_true]
      exact (hch n' (by omega)).2.2.1
  obtain ⟨l1, l2, -⟩ := ren_spec p n hn _ hF
  refine ⟨?_, gParts_le p n _ _ _ _ l1 (by simpa using r2) r3, l2, l1⟩
  simpa [GaddfE, gErr] using r1

end ExpansionBounds
