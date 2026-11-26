import ExpansionBounds.Closure

/-!
# Theorem 40: EXP within `ε e^x` in each case

Step (5) of EXP returns `2^k ADDF(t, 1)`. For a case, with `r` within `δ` of `r_e = x - k ln 2` (Lemma 38),
`a ≤ |r| ≤ b` and its sign, Lemma 39 gives `t` within `E_m` of `e^r - 1` with parts at most `ψ_m`. With `Z = e^b + E_m`
for `r ≥ 0` and `e^{-a} + E_m` for `r ≤ 0`, `(ε_s, ·) = G_ADDF(ψ_m, 1; Z, Z + ∑_{i ≥ 1} ψ_{m,i})` and `v = e^{a-δ}` or
`e^{-b-δ}`, `|y - e^x| ≤ ε e^x + nη₃` with `ε = (E_m + ε_s)/v + e^δ - 1`. The scalings are rounded where the exponent
range ends (`Scl`): by `2^{-m}` within `η₁`, step (3)'s scaling back within `η₂` and the last, by `2^k`, within `η₃`. In
binary64 these are `η_0[m > 0]`, `η_0` and `2η_0`, with `η_0 = 2^{-1075}`, and `nη₃` is the paper's `n 2^{-1074}`;
with an unbounded exponent range all three are zero. The bound of EXP is the largest `ε` over the cases that cover
the runs.
-/

namespace ExpansionBounds

open Finset

/-- `|e^h - 1| ≤ e^{|h|} - 1` -/
theorem abs_exp_sub_one_le (h : ℝ) : |Real.exp h - 1| ≤ Real.exp |h| - 1 := by
  rcases le_total 0 h with h0 | h0
  · rw [abs_of_nonneg h0, abs_of_nonneg (by linarith [Real.one_le_exp h0])]
  · have h1 : Real.exp h ≤ 1 := Real.exp_le_one_iff.mpr h0
    rw [abs_of_nonpos h0, abs_of_nonpos (by linarith)]
    have h2 := Real.add_one_le_exp h
    have h3 := Real.add_one_le_exp (-h)
    linarith

/-- `e^{k ln 2} = 2^k` -/
theorem exp_int_mul_log_two (k : ℤ) : Real.exp (k * Real.log 2) = (2 : ℝ) ^ k := by
  rw [← Real.rpow_intCast, Real.rpow_def_of_pos (by norm_num), mul_comm]

variable (p : ℤ) [Prec_gt_0 p] (n : ℕ)

/-- the parts of Horner's rule are in `F` -/
theorem hornerP_F (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (z : ℕ → ℝ)
    (hz : ∀ i < n, F p (z i)) (Fk : ℕ → ℕ → ℝ) (hF : ∀ k, ∀ i < n, F p (Fk k i)) (d : ℕ) :
    ∀ j, ∀ i < n, F p (hornerP p n (mulOp p n) z Fk d j i) := by
  intro j
  induction j with
  | zero => exact hF d
  | succ j ih =>
    intro i _
    exact F_addOp p n hp hn hA3 _ _ (hF _) (fun i' _ => F_mulOp p n hp hn hA3 z _ hz ih i') i

/-- the parts of steps (3) and (4) are in `F` -/
theorem expCore_F (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {η₁ η₂ : ℝ} {S₁ S₂ : ℝ → ℝ}
    (hS₁ : Scl p η₁ S₁) (hS₂ : Scl p η₂ S₂) (e : ℤ) (m : ℕ) (r : ℕ → ℝ)
    (hr : ∀ i < n, F p (r i)) (Fk : ℕ → ℕ → ℝ) (hF : ∀ k, ∀ i < n, F p (Fk k i)) (d' : ℕ) :
    ∀ i < n, F p (expCore p n S₁ S₂ e m r Fk d' i) := by
  have h2 : ∀ (t : ℕ → ℝ), (∀ i < n, F p (t i)) → ∀ i < n, F p (expSq p n t i) := fun t ht i _ =>
    F_addOp p n hp hn hA3 _ _ (fun i hi => by simpa using F_zpow_mul p 1 (ht i hi))
      (fun i _ => F_mulOp p n hp hn hA3 t t ht ht i) i
  have hr' : ∀ i < n, F p (S₁ ((2 : ℝ) ^ (-(m : ℤ)) * r i)) := fun i hi => hS₁.mem _ (F_zpow_mul p _ (hr i hi))
  have h0 : ∀ i < n, F p (expT0 p n S₂ (e - m) (fun i => S₁ ((2 : ℝ) ^ (-(m : ℤ)) * r i)) Fk d' i) := by
    intro i _
    unfold expT0
    split_ifs
    · exact hr' i (by assumption)
    · have hq := hornerP_F p n hp hn hA3 _ hr' Fk hF d' (d' - 2)
      have hw := F_mulOp p n hp hn hA3 _ _ hr' hq
      have hrh : ∀ i < n, F p ((2 : ℝ) ^ (-(e - m)) * S₁ ((2 : ℝ) ^ (-(m : ℤ)) * r i)) := fun i hi =>
        F_zpow_mul p _ (hr' i hi)
      exact hS₂.mem _ (F_zpow_mul p _ (F_addOp p n hp hn hA3 _ _ hrh (fun i _ => F_mulOp p n hp hn hA3 _ _ hrh
        (fun j _ => hw j) i) i))
  have hit : ∀ j (t : ℕ → ℝ), (∀ i < n, F p (t i)) → ∀ i < n, F p ((expSq p n)^[j] t i) := by
    intro j
    induction j with
    | zero => intro t ht; exact ht
    | succ j ih =>
      intro t ht
      rw [Function.iterate_succ_apply]
      exact ih _ (h2 t ht)
  exact hit m _ h0

omit [Prec_gt_0 p] in
/-- `G_ADDF(α, β_0; Z̄, λ_0)`'s error bound with the leading level bound `λ_0` given -/
noncomputable def GaddfE' (α : ℕ → ℝ) (lam0 Zb : ℝ) : ℝ := gErr p n (addfX p n α lam0) Zb 0

/-- `Z = e^b + E_m` for `r ≥ 0` and `e^{-a} + E_m` for `r ≤ 0` -/
noncomputable def expZ (pos : Bool) (a b E : ℝ) : ℝ := (if pos then Real.exp b else Real.exp (-a)) + E

/-- `v = e^{a-δ}` for `r ≥ 0` and `e^{-b-δ}` for `r ≤ 0`, at most `e^{r_e}` -/
noncomputable def expV (pos : Bool) (a b δ : ℝ) : ℝ := if pos then Real.exp (a - δ) else Real.exp (-b - δ)

/-- the bound of a case: `ε = (E_m + ε_s)/v + e^δ - 1`, with `(ε_s, ·) = G_ADDF(ψ_m, 1; Z, Z + ∑_{i ≥ 1} ψ_{m,i})` -/
noncomputable def expEps (η₁ η₂ : ℝ) (pos : Bool) (e : ℤ) (m : ℕ) (a b δ : ℝ) (π : ℕ → ℝ) (Fk : ℕ → ℕ → ℝ)
    (φ : ℕ → ℝ) (d' : ℕ) : ℝ :=
  ((coreBound p n η₁ η₂ pos e m a b π Fk φ d').1 +
      GaddfE' p n (coreBound p n η₁ η₂ pos e m a b π Fk φ d').2
        (expZ pos a b (coreBound p n η₁ η₂ pos e m a b π Fk φ d').1 +
          ∑ i ∈ Ico 1 n, (coreBound p n η₁ η₂ pos e m a b π Fk φ d').2 i)
        (expZ pos a b (coreBound p n η₁ η₂ pos e m a b π Fk φ d').1)) / expV pos a b δ +
    Real.exp δ - 1

/-- Theorem 40 (`thm:exp`), for a case: if `r` is within `δ` of `r_e = x - k ln 2` with `a ≤ |r| ≤ b` and the case's
sign, and steps (2) to (4) run with `∑|r_i| < 2^{e+1}`, `m` squarings and degree `d'`, then `y = 2^k ADDF(t, 1)`, each
part of the scaling rounded by `S₃`, satisfies `|y - e^x| ≤ ε e^x + nη₃` -/
theorem thm40_case (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {η₁ η₂ η₃ : ℝ}
    {S₁ S₂ S₃ : ℝ → ℝ} (hS₁ : Scl p η₁ S₁) (hS₂ : Scl p η₂ S₂) (hS₃ : Scl p η₃ S₃) (r : ℕ → ℝ)
    (hr : ∀ i < n, F p (r i)) (X : ℝ) (k : ℤ) (δ : ℝ)
    (hδ : |∑ i ∈ range n, r i - (X - k * Real.log 2)| ≤ δ) (a b : ℝ) (ha : a ≤ |∑ i ∈ range n, r i|)
    (hb : |∑ i ∈ range n, r i| ≤ b) (π : ℕ → ℝ) (hπ : ∀ i < n, |r i| ≤ π i)
    (e : ℤ) (hU : ∑ i ∈ range n, |r i| < (2 : ℝ) ^ (e + 1)) (m d' : ℕ) (hd : 1 ≤ d') (hbd : coreBp n e m b η₁ < d' + 2)
    (hb2 : 0 < η₁ → Real.exp (coreBp n e m b η₁) ≤ 2)
    (Fk : ℕ → ℕ → ℝ) (hF : ∀ k, ∀ i < n, F p (Fk k i)) (φ : ℕ → ℝ)
    (hφ : ∀ k, |∑ i ∈ range n, Fk k i - invF k| ≤ φ k) (pos : Bool)
    (hsgn : if pos then 0 ≤ ∑ i ∈ range n, r i else ∑ i ∈ range n, r i ≤ 0) :
    |∑ i ∈ range n, S₃ ((2 : ℝ) ^ k * (addfOp p n (expCore p n S₁ S₂ e m r Fk d') 1).getD i 0) - Real.exp X| ≤
      expEps p n η₁ η₂ pos e m a b δ π Fk φ d' * Real.exp X + n * η₃ := by
  have hu := u_pos p
  obtain ⟨R, hR⟩ : ∃ R, R = ∑ i ∈ range n, r i := ⟨_, rfl⟩
  rw [← hR] at hδ ha hb hsgn
  obtain ⟨c1, c2, -⟩ := lemma_core p n hp hn hA3 hS₁ hS₂ r hr R hR a b ha hb π hπ e hU m d' hd hbd hb2 Fk hF
    φ hφ pos hsgn
  obtain ⟨E, hE⟩ : ∃ E, E = (coreBound p n η₁ η₂ pos e m a b π Fk φ d').1 := ⟨_, rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = (coreBound p n η₁ η₂ pos e m a b π Fk φ d').2 := ⟨_, rfl⟩
  rw [← hE] at c1
  rw [← hψ] at c2
  obtain ⟨t, ht⟩ : ∃ t, t = expCore p n S₁ S₂ e m r Fk d' := ⟨_, rfl⟩
  rw [← ht] at c1 c2 ⊢
  have htF : ∀ i < n, F p (t i) := by rw [ht]; exact expCore_F p n hp hn hA3 hS₁ hS₂ e m r hr Fk hF d'
  -- the last scaling moves each part by at most `η₃`
  have hlen : (addfOp p n t 1).length ≤ n := by
    have := renPass_length p ((List.range n).map fun j => vecSum p n (addfLevels p n t 1) (j + 1)) (n - 1)
      (vecSum p n (addfLevels p n t 1) 0)
    unfold addfOp ren
    omega
  have hsc : |∑ i ∈ range n, S₃ ((2 : ℝ) ^ k * (addfOp p n t 1).getD i 0) - (2 : ℝ) ^ k * (addfOp p n t 1).sum| ≤
      n * η₃ := by
    rw [list_sum_getD _ n hlen, mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun i _ => hS₃.err _).trans_eq ?_)
    rw [sum_const, card_range, nsmul_eq_mul]
  suffices hmain : |(2 : ℝ) ^ k * (addfOp p n t 1).sum - Real.exp X| ≤
      expEps p n η₁ η₂ pos e m a b δ π Fk φ d' * Real.exp X by
    rw [show ∑ i ∈ range n, S₃ ((2 : ℝ) ^ k * (addfOp p n t 1).getD i 0) - Real.exp X =
      (∑ i ∈ range n, S₃ ((2 : ℝ) ^ k * (addfOp p n t 1).getD i 0) - (2 : ℝ) ^ k * (addfOp p n t 1).sum) +
        ((2 : ℝ) ^ k * (addfOp p n t 1).sum - Real.exp X) by ring]
    exact (abs_add_le _ _).trans (by linarith)
  obtain ⟨T, hT⟩ : ∃ T, T = ∑ i ∈ range n, t i := ⟨_, rfl⟩
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
  have hlam : |t 0 + 1| ≤ expZ pos a b E + ∑ i ∈ Ico 1 n, ψ i := by
    have hs : T = t 0 + ∑ i ∈ Ico 1 n, t i := by
      rw [hT, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
    have h1 : |∑ i ∈ Ico 1 n, t i| ≤ ∑ i ∈ Ico 1 n, ψ i :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => c2 i (mem_Ico.mp hi).2)
    rw [show t 0 + 1 = (T + 1) - ∑ i ∈ Ico 1 n, t i by rw [hs]; ring]
    exact (abs_sub _ _).trans (add_le_add hZ h1)
  -- ADDF
  obtain ⟨d1, -, -, -, -⟩ := lemma13_addf p hp hn t 1 htF (F_one p) ψ c2 _ hlam (expZ pos a b E)
    (by rw [← hT]; exact hZ)
  rw [← hT] at d1
  have hεs : |T + 1 - (addfOp p n t 1).sum| ≤ GaddfE' p n ψ (expZ pos a b E + ∑ i ∈ Ico 1 n, ψ i) (expZ pos a b E) := by
    unfold GaddfE' gErr
    simpa using d1
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
  obtain ⟨εs, hεsd⟩ : ∃ εs, εs = GaddfE' p n ψ (expZ pos a b E + ∑ i ∈ Ico 1 n, ψ i) (expZ pos a b E) := ⟨_, rfl⟩
  rw [← hεsd] at hεs
  have hεs0 : 0 ≤ εs := (abs_nonneg _).trans hεs
  have hy : |(addfOp p n t 1).sum - Real.exp re| ≤ E + εs + Real.exp re * (Real.exp δ - 1) := by
    rw [show (addfOp p n t 1).sum - Real.exp re =
      -(T + 1 - (addfOp p n t 1).sum) + (T - (Real.exp R - 1)) + (Real.exp R - Real.exp re) by ring]
    have h1 : |-(T + 1 - (addfOp p n t 1).sum)| ≤ εs := by rw [abs_neg]; exact hεs
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h1 c1))
      hdiff) |>.trans_eq ?_
    ring
  have hfac : E + εs ≤ (E + εs) / expV pos a b δ * Real.exp re := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hv0]
    exact mul_le_mul_of_nonneg_left hv (by linarith)
  have heps : expEps p n η₁ η₂ pos e m a b δ π Fk φ d' = (E + εs) / expV pos a b δ + Real.exp δ - 1 := by
    rw [expEps, ← hE, ← hψ, hεsd]
  rw [heps, hX, show (2 : ℝ) ^ k * (addfOp p n t 1).sum - (2 : ℝ) ^ k * Real.exp re =
    (2 : ℝ) ^ k * ((addfOp p n t 1).sum - Real.exp re) by ring, abs_mul, abs_of_pos (by positivity)]
  rw [show ((E + εs) / expV pos a b δ + Real.exp δ - 1) * ((2 : ℝ) ^ k * Real.exp re) =
    (2 : ℝ) ^ k * ((E + εs) / expV pos a b δ * Real.exp re + Real.exp re * (Real.exp δ - 1)) by ring]
  exact mul_le_mul_of_nonneg_left (hy.trans (by linarith)) (by positivity)

/-- `η_0[m > 0]`, with `η_0 = 2^{-1075}` -/
noncomputable def eta0m (m : ℕ) : ℝ := if m = 0 then 0 else (2 : ℝ) ^ (-1075 : ℤ)

/-- Theorem 40 (`thm:exp`), for a case, with binary64's subnormals and no overflow, the model having no largest finite
value: every scaling is rounded by `S`, which keeps a value or rounds one below `2^{-1022}` to a multiple of
`2^{-1074}` within `η_0 = 2^{-1075}`; for `m = 0` nothing is
scaled by `2^{-m}`; and the last scaling, by `2^k`, is in two steps, `2^{k₁}` then `2^{k₂}` with `k₂ ≤ 0`. Then
`|y - e^x| ≤ ε e^x + n 2^{-1074}`, with the terms in `η_0` of Lemma 39 in `ε` -/
theorem thm40_case_sub (hp : p = 53) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (r : ℕ → ℝ) (hr : ∀ i < n, F p (r i)) (X : ℝ) (k₁ k₂ : ℤ) (hk : k₂ ≤ 0) (δ : ℝ)
    (hδ : |∑ i ∈ range n, r i - (X - (k₁ + k₂ : ℤ) * Real.log 2)| ≤ δ) (a b : ℝ) (ha : a ≤ |∑ i ∈ range n, r i|)
    (hb : |∑ i ∈ range n, r i| ≤ b) (π : ℕ → ℝ) (hπ : ∀ i < n, |r i| ≤ π i)
    (e : ℤ) (hU : ∑ i ∈ range n, |r i| < (2 : ℝ) ^ (e + 1)) (m d' : ℕ) (hd : 1 ≤ d')
    (hbd : coreBp n e m b (eta0m m) < d' + 2) (hb2 : 0 < m → Real.exp (coreBp n e m b (eta0m m)) ≤ 2)
    (Fk : ℕ → ℕ → ℝ) (hF : ∀ k, ∀ i < n, F p (Fk k i)) (φ : ℕ → ℝ)
    (hφ : ∀ k, |∑ i ∈ range n, Fk k i - invF k| ≤ φ k) (pos : Bool)
    (hsgn : if pos then 0 ≤ ∑ i ∈ range n, r i else ∑ i ∈ range n, r i ≤ 0) :
    |∑ i ∈ range n, S ((2 : ℝ) ^ k₂ * S ((2 : ℝ) ^ k₁ *
        (addfOp p n (expCore p n (if m = 0 then id else S) S e m r Fk d') 1).getD i 0)) - Real.exp X| ≤
      expEps p n (eta0m m) ((2 : ℝ) ^ (-1075 : ℤ)) pos e m a b δ π Fk φ d' * Real.exp X +
        n * (2 : ℝ) ^ (-1074 : ℤ) := by
  have hS0 := Scl.of_grid p hp S hS
  have hS₁ : Scl p (eta0m m) (if m = 0 then id else S) := by
    unfold eta0m
    split_ifs
    · exact Scl.id p
    · exact hS0
  have hpos : 0 < eta0m m → 0 < m := fun h => by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · simp [eta0m, h0] at h
    · exact h0
  have h := thm40_case p n (by omega) hn hA3 hS₁ hS0 (hS0.two_step p hk) r hr X (k₁ + k₂) δ hδ a b ha hb π hπ e
    hU m d' hd hbd (fun h0 => hb2 (hpos h0)) Fk hF φ hφ pos hsgn
  have hsc : ∀ s : ℝ, (2 : ℝ) ^ (-k₂) * ((2 : ℝ) ^ (k₁ + k₂) * s) = (2 : ℝ) ^ k₁ * s := fun s => by
    rw [← mul_assoc, ← zpow_add₀ two_ne_zero, show -k₂ + (k₁ + k₂) = k₁ by ring]
  have h2 : (2 : ℝ) * (2 : ℝ) ^ (-1075 : ℤ) = (2 : ℝ) ^ (-1074 : ℤ) := by
    rw [show (-1074 : ℤ) = 1 + -1075 by norm_num, zpow_add₀ two_ne_zero, zpow_one]
  simp only [hsc, h2] at h
  exact h

end ExpansionBounds
