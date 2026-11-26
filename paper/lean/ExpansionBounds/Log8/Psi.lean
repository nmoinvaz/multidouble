import ExpansionBounds.Log8.Checks

/-!
# Theorem 42 at `n = 8` and `p = 53`: the parts of `t` and the exponent `e_t`

Step (4) scales the product `p` back in two rounded steps, by `2^{e_φ}` and then by `2^{e_t}`; the pair moves a
part by at most `2η_0` where the second does not scale up, `e_t ≤ 0`. That follows from the selection of `e_t`, the
exponent of `U_t ≥ ∑|t_i|`, once `∑|t_i| ≤ 1` (`log8_et`). Lemma 39's part bounds `ψ_m` of `t` give it: for a case
they are at most their convex variants at the upper end `ℓ₂` of the case's interval, which the state after the
squarings bounds (`log8_psi_state`), and the kernel checks the sum of that state's part bounds at most 1
(`Log8Psi`, proved for every case in `Log8/PsiAll.lean`). `log8_tsum` is the statement for a case, and
`log8_tsum_k0`, `log8_tsum_k1` those for `k = 0` and `k ≠ 0`, beside `log8_k0` and `log8_k1`.
-/

namespace ExpansionBounds

open Finset Set

/-- the kernel's check of `ψ_m` for a case, a sign and an end `ℓ`: the rational bounds of the case's arguments, a
state of step (3) above the case's, and the sum of the part bounds of the state after the squarings at most 1 -/
def Log8Psi (k0 pos : Bool) (m d' : ℕ) (a l b δ : ℚ) : Prop :=
  ∃ (bT : ℚ) (pq : List ℚ) (t : ℚ × List ℚ) (xi xs cs xd : ℚ) (ph : List ℚ),
    Log8Leaf k0 pos m a b δ l bT pq xi xs cs xd ph ∧ Log8Head pos m d' pq bT t ∧
      ∑ i ∈ range 8, (log8SqRun pos m a b m t).2.getD i 0 ≤ 1

/-- A check of `ψ_m` from the kernel's checks of a case, a sign and an end. -/
theorem Log8Psi.mk {k0 pos : Bool} {m d' : ℕ} {a b δ l bT : ℚ} {pq : List ℚ} {xi xs cs xd : ℚ} {ph : List ℚ}
    {t : ℚ × List ℚ} (leaf : Log8Leaf k0 pos m a b δ l bT pq xi xs cs xd ph) (hh : Log8Head pos m d' pq bT t)
    {sm : ℚ × List ℚ} (hsq : log8SqRun pos m a b m t = sm) (hsum : ∑ i ∈ range 8, sm.2.getD i 0 ≤ 1) :
    Log8Psi k0 pos m d' a l b δ := by
  subst hsq
  exact ⟨bT, pq, t, xi, xs, cs, xd, ph, leaf, hh, hsum⟩

/-- the checks of `ψ_m` of a group of `k = 0`: for each sign, at the upper end -/
def Log8GroupT0 (g : Log8G0) : Prop :=
  ∀ pos : Bool, Log8Psi true pos g.m g.d g.a g.l₂ g.b₂ 0

/-- the checks of `ψ_m` of a group of `k ≠ 0`: every interval of each sign, at `X` -/
def Log8GroupT1 (g : Log8G1) : Prop :=
  (∀ bn ∈ g.binsP, Log8Psi false true g.m g.d bn.1 log8X bn.2.1 bn.2.2.2) ∧
    ∀ bn ∈ g.binsN, Log8Psi false false g.m g.d bn.1 log8X bn.2.1 bn.2.2.2

variable [Prec_gt_0 (53 : ℤ)]

omit [Prec_gt_0 (53 : ℤ)] in
/-- From the rational bounds of a case and a certified state of its group: the state after the `m` squarings is
above Lemma 39's convex `(E_m, ψ_m)` at any real `b ≤ b_q` and `π` within the case's `π^y` or `π^r` at `ℓ` -/
theorem log8_psi_state {k0 pos : Bool} {m d' : ℕ} {a b δ l bT : ℚ} {pq : List ℚ} {xi xs cs xd : ℚ} {ph : List ℚ}
    {t : ℚ × List ℚ} (leaf : Log8Leaf k0 pos m a b δ l bT pq xi xs cs xd ph) (hh : Log8Head pos m d' pq bT t)
    {br : ℝ} (hbr0 : 0 ≤ br) (hbr : br ≤ ((b : ℚ) : ℝ)) {π : ℕ → ℝ} (hπ0 : ∀ i, 0 ≤ π i)
    (hπ : ∀ i < 8, π i ≤ (((if k0 then log8PiY l i else log8PiR l b i : ℚ)) : ℝ)) :
    Dom 8
      (coreBoundC 53 8 ((exp8Eta1 m : ℚ) : ℝ) ((exp8Eta : ℚ) : ℝ) pos m ((a : ℚ) : ℝ) br π
        (fun k i => ((exp8F k i : ℚ) : ℝ)) (fun k => ((exp8Phi k : ℚ) : ℝ)) d').1
      (coreBoundC 53 8 ((exp8Eta1 m : ℚ) : ℝ) ((exp8Eta : ℚ) : ℝ) pos m ((a : ℚ) : ℝ) br π
        (fun k i => ((exp8F k i : ℚ) : ℝ)) (fun k => ((exp8Phi k : ℚ) : ℝ)) d').2 (log8SqRun pos m a b m t) := by
  have hu : ((red8U : ℚ) : ℝ) = u (53 : ℤ) := by unfold red8U; exact u_53_rat 53 rfl
  have hu53 : u (53 : ℤ) = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  have hA3 : (((8 : ℕ) : ℝ) ^ 2 + (8 : ℕ)) * u (53 : ℤ) < 1 := by rw [hu53]; norm_num
  have ht0 := log8_state leaf hh hbr0 hbr hπ0 hπ
  obtain ⟨ha0, -, -, -, hbp, hbpT1, h2bp, ha1, -⟩ := leaf
  have hη0 : (0 : ℚ) ≤ exp8Eta := by unfold exp8Eta; positivity
  have hη1 : (0 : ℚ) ≤ exp8Eta1 m := by unfold exp8Eta1; split_ifs <;> [exact le_rfl; exact hη0]
  have hη₁' : (0 : ℝ) ≤ ((exp8Eta1 m : ℚ) : ℝ) := by exact_mod_cast hη1
  have hη₂' : (0 : ℝ) ≤ ((exp8Eta : ℚ) : ℝ) := by exact_mod_cast hη0
  have hφ0 : ∀ k, (0 : ℝ) ≤ ((exp8Phi k : ℚ) : ℝ) := fun k => by
    have : (0 : ℚ) ≤ exp8Phi k := by unfold exp8Phi; exact abs_nonneg _
    exact_mod_cast this
  have h2m : (0 : ℝ) < (2 : ℝ) ^ (-(m : ℤ)) := by positivity
  have h2mq : (0 : ℚ) ≤ (2 : ℚ) ^ (-(m : ℤ)) := by positivity
  -- the case's `b'` and `2^{-m}a`
  have hbpr : coreBpC 8 m br ((exp8Eta1 m : ℚ) : ℝ) ≤ ((log8Bp m b : ℚ) : ℝ) := by
    simp only [coreBpC, log8Bp]
    push_cast
    linarith [mul_le_mul_of_nonneg_left hbr h2m.le]
  have hap : ((((2 : ℚ) ^ (-(m : ℤ)) * a : ℚ)) : ℝ) ≤ (2 : ℝ) ^ (-(m : ℤ)) * ((a : ℚ) : ℝ) := by
    push_cast
    exact le_rfl
  have hap0 : (0 : ℚ) ≤ (2 : ℚ) ^ (-(m : ℤ)) * a := mul_nonneg h2mq ha0
  have hap1 : (2 : ℚ) ^ m * ((2 : ℚ) ^ (-(m : ℤ)) * a) ≤ 1 := by
    rw [← mul_assoc, zpow_neg, zpow_natCast, mul_inv_cancel₀ (by positivity), one_mul]
    exact ha1
  have hbpl : log8Bp m b < 1 := lt_of_le_of_lt hbp hbpT1
  have hbp1 : 2 ^ m * log8Bp m b ≤ 1 := (mul_le_mul_of_nonneg_left hbp (by positivity)).trans h2bp
  -- `t̄_j` and `g_j`, as in `logBoundC_cert`
  have hb'0 : 0 ≤ coreBpC 8 m br ((exp8Eta1 m : ℚ) : ℝ) :=
    add_nonneg (mul_nonneg h2m.le hbr0) (mul_nonneg (Nat.cast_nonneg 8) hη₁')
  have hbpB0 : (0 : ℚ) ≤ log8Bp m b := by exact_mod_cast hb'0.trans hbpr
  have hb'1 : coreBpC 8 m br ((exp8Eta1 m : ℚ) : ℝ) < 1 := lt_of_le_of_lt hbpr (by exact_mod_cast hbpl)
  have h2j : ∀ j ≤ m, (2 : ℚ) ^ j * log8Bp m b ≤ 1 := fun j hj =>
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hbpB0).trans hbp1
  have h2a : ∀ j ≤ m, (2 : ℚ) ^ j * ((2 : ℚ) ^ (-(m : ℤ)) * a) ≤ 1 := fun j hj =>
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hap0).trans hap1
  have hT0 : ∀ j, 0 ≤ coreTC pos (coreBpC 8 m br ((exp8Eta1 m : ℚ) : ℝ)) j := fun j => by
    have h2 : (0 : ℝ) ≤ 2 ^ j * coreBpC 8 m br ((exp8Eta1 m : ℚ) : ℝ) := mul_nonneg (by positivity) hb'0
    unfold coreTC
    split_ifs
    · linarith [Real.one_le_exp h2]
    · exact h2
  have hT : ∀ j ≤ m, coreTC pos (coreBpC 8 m br ((exp8Eta1 m : ℚ) : ℝ)) j ≤
      ((coreTCQ (upQ 200) pos (log8Bp m b) j : ℚ) : ℝ) := fun j hj =>
    (coreTC_le (le_upQ 200) hb'0 hbpr j (h2j j hj)).2
  have hg : ∀ j, 0 ≤ coreG pos ((2 : ℝ) ^ (-(m : ℤ)) * ((a : ℚ) : ℝ)) (coreBpC 8 m br ((exp8Eta1 m : ℚ) : ℝ)) j ∧
      (j < m → coreG pos ((2 : ℝ) ^ (-(m : ℤ)) * ((a : ℚ) : ℝ)) (coreBpC 8 m br ((exp8Eta1 m : ℚ) : ℝ)) j ≤
        ((coreGQ (upQ 200) pos ((2 : ℚ) ^ (-(m : ℤ)) * a) (log8Bp m b) j : ℚ) : ℝ)) := fun j =>
    ⟨by unfold coreG; split_ifs <;> exact (Real.exp_pos _).le,
      fun hj => (coreG_le (le_upQ 200) hap0 hap hb'0 hbpr j (h2a j hj.le) (h2j j hj.le)).2⟩
  obtain ⟨hc00, hc02⟩ := core0C_nonneg 53 8 hA3 (π' := corePiC m π ((exp8Eta1 m : ℚ) : ℝ))
    (fun i => add_nonneg (mul_nonneg h2m.le (hπ0 i)) hη₁') hb'0 hb'1 (hT0 0)
    (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg 8)) hη₁') hη₂' (fun k i => ((exp8F k i : ℚ) : ℝ))
    (fun k => ((exp8Phi k : ℚ) : ℝ)) hφ0 d'
  obtain ⟨dm, -, -⟩ := coreEC_cert (53 : ℤ) 8 hu (le_upQ 200) (by norm_num) hA3
    (T := coreTC pos (coreBpC 8 m br ((exp8Eta1 m : ℚ) : ℝ)))
    (g := coreG pos ((2 : ℝ) ^ (-(m : ℤ)) * ((a : ℚ) : ℝ)) (coreBpC 8 m br ((exp8Eta1 m : ℚ) : ℝ)))
    (coreTCQ (upQ 200) pos (log8Bp m b)) (coreGQ (upQ 200) pos ((2 : ℚ) ^ (-(m : ℤ)) * a) (log8Bp m b)) m hT0 hT
    (fun j => (hg j).1) (fun j hj => (hg j).2 hj) hc00 hc02 (fun j => log8SqRun pos m a b j t) ht0
    (fun j _ => rfl) m le_rfl
  exact dm

/-- The parts of `t` for a case on an interval `[ℓ₁, ℓ₂]` of `|ln x|`, from the kernel's check of `ψ_m` at `ℓ₂`:
with the case's `b` and `π` functions of `ℓ` in the class `Cvx` that bound the run's `|r|` and `|r_i|` at `ℓ` and lie
below the check's `b` and `π^y` or `π^r` at `ℓ₂`, `∑|t_i| ≤ 1`, by Lemma 39's part bounds (`lemma_core`) -/
theorem log8_tsum {m : ℕ} {S₁ S₂ : ℝ → ℝ} (hS₁ : Scl 53 ((exp8Eta1 m : ℚ) : ℝ) S₁)
    (hS₂ : Scl 53 ((exp8Eta : ℚ) : ℝ) S₂) {l₁ l₂ : ℚ} (h0 : 0 ≤ l₁) {ℓ : ℝ}
    (hl : ℓ ∈ Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ)) {b : ℝ → ℝ} {π : ℝ → ℕ → ℝ}
    (hbc : Cvx (Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ)) b)
    (hπc : ∀ i, Cvx (Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ)) fun l => π l i) (r : ℕ → ℝ) (hr : ∀ i < 8, F 53 (r i))
    (a : ℚ) (ha : ((a : ℚ) : ℝ) ≤ |∑ i ∈ range 8, r i|) (hb : |∑ i ∈ range 8, r i| ≤ b ℓ)
    (hπ : ∀ i < 8, |r i| ≤ π ℓ i) (pos : Bool)
    (hsgn : if pos then 0 ≤ ∑ i ∈ range 8, r i else ∑ i ∈ range 8, r i ≤ 0) (e : ℤ)
    (hU : ∑ i ∈ range 8, |r i| < (2 : ℝ) ^ (e + 1)) (d' : ℕ) (hd : 1 ≤ d')
    (hF : ∀ k, ∀ i < 8, F 53 ((exp8F k i : ℚ) : ℝ))
    (hφF : ∀ k, |∑ i ∈ range 8, ((exp8F k i : ℚ) : ℝ) - invF k| ≤ ((exp8Phi k : ℚ) : ℝ)) {k0 : Bool} {b₂ δ₂ : ℚ}
    (ps : Log8Psi k0 pos m d' a l₂ b₂ δ₂) (hb₂ : b ((l₂ : ℚ) : ℝ) ≤ ((b₂ : ℚ) : ℝ))
    (hπ₂ : ∀ i < 8, π ((l₂ : ℚ) : ℝ) i ≤ (((if k0 then log8PiY l₂ i else log8PiR l₂ b₂ i : ℚ)) : ℝ)) :
    ∑ i ∈ range 8, |expCore 53 8 S₁ S₂ e m r (fun k i => ((exp8F k i : ℚ) : ℝ)) d' i| ≤ 1 := by
  have hu : ((red8U : ℚ) : ℝ) = u (53 : ℤ) := by unfold red8U; exact u_53_rat 53 rfl
  have hu53 : u (53 : ℤ) = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  have hA3 : (((8 : ℕ) : ℝ) ^ 2 + (8 : ℕ)) * u (53 : ℤ) < 1 := by rw [hu53]; norm_num
  obtain ⟨bT, pq, t, xi, xs, cs, xd, ph, leaf, hh, hsum⟩ := ps
  have hl₁ : (0 : ℝ) ≤ ((l₁ : ℚ) : ℝ) := by exact_mod_cast h0
  have h12 : ((l₁ : ℚ) : ℝ) ≤ ((l₂ : ℚ) : ℝ) := hl.1.trans hl.2
  have hs : Convex ℝ (Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ)) := convex_Icc _ _
  have m₂ : ((l₂ : ℚ) : ℝ) ∈ Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ) := right_mem_Icc.mpr h12
  have hη₁ := Scl.nonneg 53 hS₁
  have hη₂ := Scl.nonneg 53 hS₂
  have hφF0 : ∀ k, (0 : ℝ) ≤ ((exp8Phi k : ℚ) : ℝ) := fun k => (abs_nonneg _).trans (hφF k)
  -- the state after the squarings bounds the convex `ψ_m` at `ℓ₂`
  have dm := log8_psi_state leaf hh (hbc.nonneg _ m₂) hb₂ (fun i => (hπc i).nonneg _ m₂) hπ₂
  -- Lemma 39's hypotheses, at the upper end
  obtain ⟨-, -, -, -, hbp₂, hbT₂, h2bT₂, -⟩ := leaf
  have h2m : (0 : ℝ) ≤ (2 : ℝ) ^ (-(m : ℤ)) := by positivity
  have hbpr : coreBpC 8 m (b ((l₂ : ℚ) : ℝ)) ((exp8Eta1 m : ℚ) : ℝ) ≤ ((bT : ℚ) : ℝ) := by
    refine le_trans ?_ (Rat.cast_le.mpr hbp₂)
    simp only [coreBpC, log8Bp]
    push_cast
    linarith [mul_le_mul_of_nonneg_left hb₂ h2m]
  have hbT' : ((bT : ℚ) : ℝ) < 1 := by exact_mod_cast hbT₂
  have hbd : coreBpC 8 m (b ((l₂ : ℚ) : ℝ)) ((exp8Eta1 m : ℚ) : ℝ) < (d' : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (d' : ℝ) := Nat.cast_nonneg d'
    linarith
  have hb2 : 0 < ((exp8Eta1 m : ℚ) : ℝ) →
      Real.exp (coreBpC 8 m (b ((l₂ : ℚ) : ℝ)) ((exp8Eta1 m : ℚ) : ℝ)) ≤ 2 := fun hpos1 => by
    have hm : m ≠ 0 := by
      intro h
      rw [h] at hpos1
      simp [exp8Eta1] at hpos1
    have h2 : (2 : ℚ) ≤ 2 ^ m := by
      calc (2 : ℚ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
    have hbq0 : (0 : ℚ) ≤ bT := by
      have h1 : (0 : ℝ) ≤ coreBpC 8 m (b ((l₂ : ℚ) : ℝ)) ((exp8Eta1 m : ℚ) : ℝ) :=
        add_nonneg (mul_nonneg h2m (hbc.nonneg _ m₂)) (mul_nonneg (Nat.cast_nonneg 8) hpos1.le)
      exact_mod_cast h1.trans hbpr
    have hhalf : bT ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_right h2 hbq0
      linarith
    have hhalf' : ((bT : ℚ) : ℝ) ≤ 1 / 2 := by
      have h := (Rat.cast_le (K := ℝ)).mpr hhalf
      push_cast at h
      exact h
    obtain ⟨lA, -⟩ := log_two_600
    have hlA : (1 / 2 : ℝ) ≤ ((ln2A : ℚ) : ℝ) := by
      have h := (Rat.cast_le (K := ℝ)).mpr (by decide +kernel : (1 / 2 : ℚ) ≤ ln2A)
      push_cast at h
      exact h
    calc Real.exp (coreBpC 8 m (b ((l₂ : ℚ) : ℝ)) ((exp8Eta1 m : ℚ) : ℝ)) ≤ Real.exp (Real.log 2) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = 2 := Real.exp_log (by norm_num)
  have hbpC := coreBpC_cvx 8 hs m hbc hη₁
  have hbdl : ∀ l ∈ Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ), coreBpC 8 m (b l) ((exp8Eta1 m : ℚ) : ℝ) < d' + 2 :=
    fun l h => (hbpC.mono h m₂ h.2).trans_lt hbd
  have hb0 := hbc.nonneg ℓ hl
  have hπ0 : ∀ i, 0 ≤ π ℓ i := fun i => (hπc i).nonneg ℓ hl
  have hbp2 : coreBp 8 e m (b ℓ) ((exp8Eta1 m : ℚ) : ℝ) ≤ coreBpC 8 m (b ((l₂ : ℚ) : ℝ)) ((exp8Eta1 m : ℚ) : ℝ) :=
    (coreBp_sand 8 e m (Sand.refl hb0) hη₁).le.trans (hbpC.mono hl m₂ hl.2)
  -- the parts of `t`, their convex bounds at `ℓ` and at `ℓ₂`
  obtain ⟨-, hparts, -⟩ := lemma_core 53 8 (by norm_num) (by norm_num) hA3 hS₁ hS₂ r hr _ rfl ((a : ℚ) : ℝ) (b ℓ)
    ha hb (π ℓ) hπ e hU m d' hd (hbp2.trans_lt hbd) (fun h1 => (Real.exp_le_exp.mpr hbp2).trans (hb2 h1))
    (fun k i => ((exp8F k i : ℚ) : ℝ)) hF (fun k => ((exp8Phi k : ℚ) : ℝ)) hφF pos hsgn
  obtain ⟨-, hs2⟩ := coreBound_sand 53 8 hA3 hη₁ hη₂ pos e m ((a : ℚ) : ℝ) (Sand.refl hb0)
    (fun i => Sand.refl (hπ0 i)) (fun k i => ((exp8F k i : ℚ) : ℝ)) hφF0 d' (hbdl ℓ hl)
  obtain ⟨-, hcv⟩ := coreBoundC_cvx 53 8 hA3 hs hη₁ hη₂ pos m ((a : ℚ) : ℝ) hbc hπc
    (fun k i => ((exp8F k i : ℚ) : ℝ)) hφF0 d' hbdl
  have hi : ∀ i < 8, |expCore 53 8 S₁ S₂ e m r (fun k i => ((exp8F k i : ℚ) : ℝ)) d' i| ≤
      (((log8SqRun pos m a b₂ m t).2.getD i 0 : ℚ) : ℝ) := fun i hi =>
    (((hparts i hi).trans (hs2 i).le).trans ((hcv i).mono hl m₂ hl.2)).trans (dm.2 i hi)
  calc ∑ i ∈ range 8, |expCore 53 8 S₁ S₂ e m r (fun k i => ((exp8F k i : ℚ) : ℝ)) d' i| ≤
        ∑ i ∈ range 8, (((log8SqRun pos m a b₂ m t).2.getD i 0 : ℚ) : ℝ) :=
        sum_le_sum fun i hi' => hi i (mem_range.mp hi')
    _ = ((∑ i ∈ range 8, (log8SqRun pos m a b₂ m t).2.getD i 0 : ℚ) : ℝ) := by push_cast; rfl
    _ ≤ 1 := by exact_mod_cast hsum

/-- The parts of `t` for a case of `k = 0`, with the hypotheses of `log8_k0`: `∑|t_i| ≤ 1` -/
theorem log8_tsum_k0 {m : ℕ} {S₁ S₂ : ℝ → ℝ} (hS₁ : Scl 53 ((exp8Eta1 m : ℚ) : ℝ) S₁)
    (hS₂ : Scl 53 ((exp8Eta : ℚ) : ℝ) S₂) (y0 : ℕ → ℝ) (hy1 : |y0 1| ≤ u 53 * |y0 0|)
    (hy2 : ∀ i, 2 ≤ i → y0 i = 0) {L : ℝ} {l₁ l₂ : ℚ} (h0 : 0 ≤ l₁)
    (hl : |L| ∈ Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ)) {b : ℝ → ℝ} (hbc : Cvx (Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ)) b)
    (hE : |∑ i ∈ range 8, y0 i - L| ≤ log8E |L|) (r : ℕ → ℝ) (hr : ∀ i < 8, F 53 (r i))
    (hry : ∀ i, r i = -y0 i) (a : ℚ) (ha : ((a : ℚ) : ℝ) ≤ |∑ i ∈ range 8, r i|)
    (hb : |∑ i ∈ range 8, r i| ≤ b |L|) (pos : Bool)
    (hsgn : if pos then 0 ≤ ∑ i ∈ range 8, r i else ∑ i ∈ range 8, r i ≤ 0) (e : ℤ)
    (hU : ∑ i ∈ range 8, |r i| < (2 : ℝ) ^ (e + 1)) (d' : ℕ) (hd : 1 ≤ d')
    (hF : ∀ k, ∀ i < 8, F 53 ((exp8F k i : ℚ) : ℝ))
    (hφF : ∀ k, |∑ i ∈ range 8, ((exp8F k i : ℚ) : ℝ) - invF k| ≤ ((exp8Phi k : ℚ) : ℝ)) {b₂ : ℚ}
    (ps : Log8Psi true pos m d' a l₂ b₂ 0) (hb₂ : b ((l₂ : ℚ) : ℝ) ≤ ((b₂ : ℚ) : ℝ)) :
    ∑ i ∈ range 8, |expCore 53 8 S₁ S₂ e m r (fun k i => ((exp8F k i : ℚ) : ℝ)) d' i| ≤ 1 := by
  have hu : ((red8U : ℚ) : ℝ) = u (53 : ℤ) := by unfold red8U; exact u_53_rat 53 rfl
  have hu53 : u (53 : ℤ) = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  obtain ⟨he0, he1, -⟩ := log8E_consts
  have he0' : (0 : ℝ) ≤ ((log8E0 : ℚ) : ℝ) := by exact_mod_cast he0
  have he1' : (0 : ℝ) ≤ ((log8E1 : ℚ) : ℝ) := by exact_mod_cast he1
  have hl₁ : (0 : ℝ) ≤ ((l₁ : ℚ) : ℝ) := by exact_mod_cast h0
  have hs : Convex ℝ (Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ)) := convex_Icc _ _
  have hpos : ∀ l ∈ Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ), 0 ≤ l := fun l h => hl₁.trans h.1
  obtain ⟨-, hπy⟩ := log8_start_parts y0 hy1 hy2 hE
  exact log8_tsum hS₁ hS₂ h0 hl hbc (fun i => logPiY_cvx 53 hs hpos (by rw [hu53]; norm_num) he0' he1' i) r hr a
    ha hb (fun i hi => by rw [hry i, abs_neg]; exact hπy i hi) pos hsgn e hU d' hd hF hφF ps hb₂
    (fun i _ => by simpa using log8PiY_le l₂ i)

/-- The parts of `t` for a case of `k ≠ 0`, with the hypotheses of `log8_k1`: `∑|t_i| ≤ 1` -/
theorem log8_tsum_k1 {m : ℕ} {S₁ S₂ : ℝ → ℝ} (hS₁ : Scl 53 ((exp8Eta1 m : ℚ) : ℝ) S₁)
    (hS₂ : Scl 53 ((exp8Eta : ℚ) : ℝ) S₂) (y0 : ℕ → ℝ) (hy0 : ∀ i < 8, F 53 (y0 i))
    (hy1 : |y0 1| ≤ u 53 * |y0 0|) (hy2 : ∀ i, 2 ≤ i → y0 i = 0) {L : ℝ} {l₁ l₂ : ℚ} (h0 : 0 ≤ l₁)
    (hl : |L| ∈ Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ)) (hE : |∑ i ∈ range 8, y0 i - L| ≤ log8E |L|) (r : ℕ → ℝ)
    (hr : ∀ i < 8, F 53 (r i))
    (hrd : r = expR 53 8 (fun i => -y0 i) ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)))
    (hk : expK 53 (-y0 0) ≠ 0) (hX1 : (l₂ + log8Eq l₂) / (1 - red8U) ≤ 7453 / 10)
    (hA0 : log8Alpha l₂ 0 < 1 / 2) (a : ℚ) (ha : ((a : ℚ) : ℝ) ≤ |∑ i ∈ range 8, r i|) (rb : ℚ)
    (hb : |∑ i ∈ range 8, r i| ≤ ((rb : ℚ) : ℝ)) (pos : Bool)
    (hsgn : if pos then 0 ≤ ∑ i ∈ range 8, r i else ∑ i ∈ range 8, r i ≤ 0) (e : ℤ)
    (hU : ∑ i ∈ range 8, |r i| < (2 : ℝ) ^ (e + 1)) (d' : ℕ) (hd : 1 ≤ d')
    (hF : ∀ k, ∀ i < 8, F 53 ((exp8F k i : ℚ) : ℝ))
    (hφF : ∀ k, |∑ i ∈ range 8, ((exp8F k i : ℚ) : ℝ) - invF k| ≤ ((exp8Phi k : ℚ) : ℝ)) {δ₂ : ℚ}
    (ps : Log8Psi false pos m d' a l₂ rb δ₂) :
    ∑ i ∈ range 8, |expCore 53 8 S₁ S₂ e m r (fun k i => ((exp8F k i : ℚ) : ℝ)) d' i| ≤ 1 := by
  have hl₁ : (0 : ℝ) ≤ ((l₁ : ℚ) : ℝ) := by exact_mod_cast h0
  have h12 : ((l₁ : ℚ) : ℝ) ≤ ((l₂ : ℚ) : ℝ) := hl.1.trans hl.2
  have h02 : (0 : ℚ) ≤ l₂ := by exact_mod_cast hl₁.trans h12
  have hs : Convex ℝ (Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ)) := convex_Icc _ _
  have hpos : ∀ l ∈ Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ), 0 ≤ l := fun l h => hl₁.trans h.1
  have hrb0 : (0 : ℝ) ≤ ((rb : ℚ) : ℝ) := (abs_nonneg _).trans hb
  obtain ⟨-, -, -, hπc⟩ := log8_red_cvx hs hpos hrb0
  subst hrd
  obtain ⟨-, hπ⟩ := log8_red_run y0 hy0 hy1 hy2 hE hl.2 hX1 hA0 hk hb
  exact log8_tsum hS₁ hS₂ h0 hl (Cvx.const hs hrb0) hπc _ hr a ha hb (fun i _ => hπ i) pos hsgn e hU d' hd hF hφF
    ps le_rfl (fun i _ => by simpa using log8PR_le l₂ h02 (le_refl ((rb : ℚ) : ℝ)) i)

/-- `e_t ≤ 0` from the selection of `e_t`, the exponent of `U_t` or `-1023` where `U_t < 2^{-1022}`, and
`∑|t_i| ≤ 1`: `U_t ≤ (1 + u)^8(1 + 2^{-48}) < 2` -/
theorem log8_et (t : ℕ → ℝ) (ht : ∑ i ∈ range 8, |t i| ≤ 1) (et : ℤ)
    (hsel : ((2 : ℝ) ^ et ≤ expU 53 8 ((2 : ℝ) ^ (-48 : ℤ)) t ∧
        expU 53 8 ((2 : ℝ) ^ (-48 : ℤ)) t < (2 : ℝ) ^ (et + 1)) ∨
      (expU 53 8 ((2 : ℝ) ^ (-48 : ℤ)) t < (2 : ℝ) ^ (-1022 : ℤ) ∧ et = -1023)) : et ≤ 0 := by
  have hu53 : u (53 : ℤ) = 1 / 9007199254740992 := by rw [← u_53_rat 53 rfl]; norm_num
  rcases hsel with ⟨h1, -⟩ | ⟨-, h⟩
  · have h3 := h1.trans (expU_le 53 8 (by norm_num) ((2 : ℝ) ^ (-48 : ℤ)) (by positivity) t)
    have hc : (1 + u (53 : ℤ)) ^ 8 * (1 + (2 : ℝ) ^ (-48 : ℤ)) < 2 := by rw [hu53]; norm_num
    have hc0 : (0 : ℝ) ≤ (1 + u (53 : ℤ)) ^ 8 * (1 + (2 : ℝ) ^ (-48 : ℤ)) := by rw [hu53]; norm_num
    have h4 : (2 : ℝ) ^ et < (2 : ℝ) ^ (1 : ℤ) := by
      have := mul_le_mul_of_nonneg_left ht hc0
      rw [zpow_one]
      linarith
    have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h4
    omega
  · omega

end ExpansionBounds
