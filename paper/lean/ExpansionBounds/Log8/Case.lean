import ExpansionBounds.Log8.Chord

/-!
# Theorem 42 at `n = 8` and `p = 53`: the kernel's checks of a case as one statement

`Log8Head` is a state of step (3) certified by the kernel: Horner's run on a group's `(p_q, b_T)`, the two products
and the sum for a sign, or `(E^tr_1 + D, p_q)` for the degree one. `Log8Eval` is an evaluation: a case, a sign and an
end `ℓ`, with its rational bounds (`Log8Leaf`), its state, the squarings, the two pieces of step (4) and the bound
(`Log8End`). `log8_state` gives, from the first two, a state above step (3)'s `(E_0, ψ_0)` at the real arguments, and
`log8_chord_case` is `log8_chord` from the two evaluations of a case.
-/

namespace ExpansionBounds

open Finset Set

/-- Two pieces of Horner's convex run make one. -/
theorem log8Run_cut (pq : List ℚ) (bp : ℚ) (d a m1 m2 : ℕ) {st st1 st2 : ℚ × List ℚ}
    (h1 : log8Run pq bp d a m1 st = st1) (h2 : log8Run pq bp d (a + m1) m2 st1 = st2) :
    log8Run pq bp d a (m1 + m2) st = st2 := by
  unfold log8Run at *
  rw [hornerRunLC_add, h1, h2]

/-- a state of step (3) on a group's `(p_q, b_T)`, as the kernel certifies it: for a degree `d' ≠ 1`, Horner's run,
the two products and the sum for the sign; for `d' = 1`, `(E^tr_1 + D, p_q)` -/
def Log8Head (pos : Bool) (m d' : ℕ) (pq : List ℚ) (bT : ℚ) (t : ℚ × List ℚ) : Prop :=
  (∀ q ∈ pq, 0 ≤ q) ∧
    if d' = 1 then t = (upQ 200 (eTrQ bT 1 + 2 * ((8 : ℕ) : ℚ) * exp8Eta1 m), pq)
    else ∃ (w : (ℚ × ℚ) × List ℚ) (y : ℚ × List ℚ),
      log8W pq bT (log8Run pq bT d' 0 (d' - 2) (hornerInitL 8 exp8F exp8Phi d')) = w ∧
        log8Y m d' pq bT w = y ∧ log8T pos pq bT y = t

/-- the kernel's checks of a case, a sign and an end `ℓ`: the rational bounds of the case's arguments, a state of
step (3) above the case's, the squarings, step (4)'s two pieces, and the last product and ADD with the bound -/
def Log8Eval (k0 pos : Bool) (m d' : ℕ) (a l : ℚ) (zero : Bool) (b δ : ℚ) : Prop :=
  ∃ (bT : ℚ) (pq : List ℚ) (t : ℚ × List ℚ) (xi xs cs xd : ℚ) (ph : List ℚ)
    (sa : (ℚ × ℚ) × (List ℚ × List ℚ)) (c4 : ℚ × List ℚ),
    Log8Leaf k0 pos m a b δ l bT pq xi xs cs xd ph ∧ Log8Head pos m d' pq bT t ∧
      log8C4a pos m b δ l xi xs ph (log8SqRun pos m a b m t) = sa ∧
      log8C4b pos m b xi cs xd ph (log8SqRun pos m a b m t) sa = c4 ∧ Log8End zero l cs c4

/-- From the rational bounds of a case and a certified state of its group: the state is above step (3)'s
`(E_0, ψ_0)` at any real `b ≤ b_q` and `π` within the case's `π^y` (`k = 0`) or `π^r` (`k ≠ 0`) at `ℓ` -/
theorem log8_state {k0 pos : Bool} {m d' : ℕ} {a b δ l bT : ℚ} {pq : List ℚ} {xi xs cs xd : ℚ} {ph : List ℚ}
    {t : ℚ × List ℚ} (leaf : Log8Leaf k0 pos m a b δ l bT pq xi xs cs xd ph) (hh : Log8Head pos m d' pq bT t)
    {br : ℝ} (hbr0 : 0 ≤ br) (hbr : br ≤ ((b : ℚ) : ℝ)) {π : ℕ → ℝ} (hπ0 : ∀ i, 0 ≤ π i)
    (hπ : ∀ i < 8, π i ≤ (((if k0 then log8PiY l i else log8PiR l b i : ℚ)) : ℝ)) :
    Dom 8
      (core0C 53 8 (coreTC pos (coreBpC 8 m br ((exp8Eta1 m : ℚ) : ℝ)) 0) (2 * (8 : ℕ) * ((exp8Eta1 m : ℚ) : ℝ))
        ((exp8Eta : ℚ) : ℝ) (corePiC m π ((exp8Eta1 m : ℚ) : ℝ)) (coreBpC 8 m br ((exp8Eta1 m : ℚ) : ℝ))
        (fun k i => ((exp8F k i : ℚ) : ℝ)) (fun k => ((exp8Phi k : ℚ) : ℝ)) d').1
      (core0C 53 8 (coreTC pos (coreBpC 8 m br ((exp8Eta1 m : ℚ) : ℝ)) 0) (2 * (8 : ℕ) * ((exp8Eta1 m : ℚ) : ℝ))
        ((exp8Eta : ℚ) : ℝ) (corePiC m π ((exp8Eta1 m : ℚ) : ℝ)) (coreBpC 8 m br ((exp8Eta1 m : ℚ) : ℝ))
        (fun k i => ((exp8F k i : ℚ) : ℝ)) (fun k => ((exp8Phi k : ℚ) : ℝ)) d').2 t := by
  obtain ⟨-, -, -, -, hbp, hbT, -, -, -, hpq, -⟩ := leaf
  obtain ⟨hq, hst⟩ := hh
  have hη1 : (0 : ℝ) ≤ ((exp8Eta1 m : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ exp8Eta1 m := by unfold exp8Eta1 exp8Eta; split_ifs <;> positivity
    exact_mod_cast this
  have h2m : (0 : ℝ) ≤ (2 : ℝ) ^ (-(m : ℤ)) := by positivity
  have hpq0 : ∀ i, 0 ≤ pq.getD i 0 := fun i => by
    rw [List.getD_eq_getElem?_getD]
    cases hi : pq[i]? with
    | none => simp
    | some q => exact hq q (List.mem_of_getElem? hi)
  have hπ' : ∀ i < 8, corePiC m π ((exp8Eta1 m : ℚ) : ℝ) i ≤ ((pq.getD i 0 : ℚ) : ℝ) := fun i hi => by
    refine le_trans ?_ (Rat.cast_le.mpr (hpq i hi))
    simp only [corePiC]
    push_cast
    linarith [mul_le_mul_of_nonneg_left (hπ i hi) h2m]
  have hb' : coreBpC 8 m br ((exp8Eta1 m : ℚ) : ℝ) ≤ ((bT : ℚ) : ℝ) := by
    refine le_trans ?_ (Rat.cast_le.mpr hbp)
    simp only [coreBpC, log8Bp]
    push_cast
    linarith [mul_le_mul_of_nonneg_left hbr h2m]
  have hb0 : 0 ≤ coreBpC 8 m br ((exp8Eta1 m : ℚ) : ℝ) :=
    add_nonneg (mul_nonneg h2m hbr0) (mul_nonneg (Nat.cast_nonneg 8) hη1)
  have hπ0' : ∀ i, 0 ≤ corePiC m π ((exp8Eta1 m : ℚ) : ℝ) i := fun i =>
    add_nonneg (mul_nonneg h2m (hπ0 i)) hη1
  by_cases hd : d' = 1
  · subst hd
    simp only [↓reduceIte] at hst
    subst hst
    have hD : 2 * ((8 : ℕ) : ℝ) * ((exp8Eta1 m : ℚ) : ℝ) ≤ ((2 * ((8 : ℕ) : ℚ) * exp8Eta1 m : ℚ) : ℝ) := by
      push_cast
      exact le_rfl
    exact core0C_cert_one 53 8 (le_upQ 200) pq hπ' hb0 hb' hbT hD _ _ _ _
  · simp only [hd, ↓reduceIte] at hst
    obtain ⟨w, y, hw, hy, ht⟩ := hst
    exact log8_head pos m d' hd hpq0 hbT rfl hw hy ht hπ0' hπ' hb0 hb'

/-- A state of degree `d' ≠ 1` from the kernel's checks of Horner's run, the two products and the sum. -/
theorem Log8Head.mk_ne {pos : Bool} {m d' : ℕ} {pq : List ℚ} {bT : ℚ} (hd : d' ≠ 1) (hq : ∀ q ∈ pq, 0 ≤ q)
    {sH : ℚ × List ℚ} (hr : log8Run pq bT d' 0 (d' - 2) (hornerInitL 8 exp8F exp8Phi d') = sH)
    {w : (ℚ × ℚ) × List ℚ} (hw : log8W pq bT sH = w) {y : ℚ × List ℚ} (hy : log8Y m d' pq bT w = y)
    {t : ℚ × List ℚ} (ht : log8T pos pq bT y = t) : Log8Head pos m d' pq bT t := by
  refine ⟨hq, ?_⟩
  simp only [hd, ↓reduceIte]
  exact ⟨w, y, by rw [hr]; exact hw, hy, ht⟩

/-- The state of degree one. -/
theorem Log8Head.mk_one (pos : Bool) (m : ℕ) {pq : List ℚ} (bT : ℚ) (hq : ∀ q ∈ pq, 0 ≤ q) :
    Log8Head pos m 1 pq bT (upQ 200 (eTrQ bT 1 + 2 * ((8 : ℕ) : ℚ) * exp8Eta1 m), pq) :=
  ⟨hq, by simp only [↓reduceIte]⟩

/-- An evaluation from the kernel's checks of a case, a sign and an end. -/
theorem Log8Eval.mk {k0 pos : Bool} {m d' : ℕ} {a b δ l bT : ℚ} {pq : List ℚ} {xi xs cs xd : ℚ} {ph : List ℚ}
    {t : ℚ × List ℚ} (leaf : Log8Leaf k0 pos m a b δ l bT pq xi xs cs xd ph) (hh : Log8Head pos m d' pq bT t)
    {sm : ℚ × List ℚ} (hsq : log8SqRun pos m a b m t = sm) {sa : (ℚ × ℚ) × (List ℚ × List ℚ)}
    (hA : log8C4a pos m b δ l xi xs ph sm = sa) {c4 : ℚ × List ℚ} (hB : log8C4b pos m b xi cs xd ph sm sa = c4)
    {zero : Bool} (hend : Log8End zero l cs c4) : Log8Eval k0 pos m d' a l zero b δ := by
  subst hsq
  exact ⟨bT, pq, t, xi, xs, cs, xd, ph, sa, c4, leaf, hh, hA, hB, hend⟩

variable [Prec_gt_0 (53 : ℤ)]

/-- Theorem 42 (`thm:log`) at `n = 8` for a case on an interval `[ℓ₁, ℓ₂]` of `|ln x|`, from the kernel's two
evaluations of the case (`Log8Eval` at `ℓ₁` and at `ℓ₂`): `log8_chord` with the states of step (3) from
`log8_state`. The case's `b`, `δ` and `π` are functions of `ℓ` in the class `Cvx` that bound the run's quantities at
`ℓ = |ln x|` and lie below the evaluations' `b`, `δ` and `π^y` or `π^r` at the ends -/
theorem log8_chord_case {m : ℕ} {S₁ S₂ Sx Sp Sc : ℝ → ℝ} (hS₁ : Scl 53 ((exp8Eta1 m : ℚ) : ℝ) S₁)
    (hS₂ : Scl 53 ((exp8Eta : ℚ) : ℝ) S₂) (hSx : Scl 53 ((2 * exp8Eta : ℚ) : ℝ) Sx)
    (hSp : Scl 53 ((2 * exp8Eta : ℚ) : ℝ) Sp) (hSc : Scl 53 ((exp8Eta : ℚ) : ℝ) Sc) (x : ℕ → ℝ)
    (hx : ∀ i < 8, F 53 (x i)) (hX0 : 0 < ∑ i ∈ range 8, x i) (hH : Htheta 53 8 2 x) (y0 : ℕ → ℝ)
    (hy0 : ∀ i < 8, F 53 (y0 i)) {l₁ l₂ : ℚ} (h0 : 0 ≤ l₁)
    (hl : |Real.log (∑ i ∈ range 8, x i)| ∈ Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ)) {b δ : ℝ → ℝ} {π : ℝ → ℕ → ℝ}
    (hbc : Cvx (Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ)) b) (hδc : Cvx (Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ)) δ)
    (hπc : ∀ i, Cvx (Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ)) fun l => π l i)
    (hπy : ∀ i < 8, |y0 i| ≤
      logPiY 53 ((log8E0 : ℚ) : ℝ) ((log8E1 : ℚ) : ℝ) |Real.log (∑ i ∈ range 8, x i)| i)
    (hE : |∑ i ∈ range 8, y0 i - Real.log (∑ i ∈ range 8, x i)| ≤ log8E |Real.log (∑ i ∈ range 8, x i)|)
    (r : ℕ → ℝ) (hr : ∀ i < 8, F 53 (r i)) (k : ℤ)
    (hδ : |∑ i ∈ range 8, r i - (-∑ i ∈ range 8, y0 i - k * Real.log 2)| ≤
      δ |Real.log (∑ i ∈ range 8, x i)|)
    (a : ℚ) (ha : ((a : ℚ) : ℝ) ≤ |∑ i ∈ range 8, r i|)
    (hb : |∑ i ∈ range 8, r i| ≤ b |Real.log (∑ i ∈ range 8, x i)|)
    (hπ : ∀ i < 8, |r i| ≤ π |Real.log (∑ i ∈ range 8, x i)| i) (pos : Bool)
    (hsgn : if pos then 0 ≤ ∑ i ∈ range 8, r i else ∑ i ∈ range 8, r i ≤ 0) (e : ℤ)
    (hU : ∑ i ∈ range 8, |r i| < (2 : ℝ) ^ (e + 1)) (d' : ℕ) (hd : 1 ≤ d')
    (hF : ∀ k, ∀ i < 8, F 53 ((exp8F k i : ℚ) : ℝ))
    (hφF : ∀ k, |∑ i ∈ range 8, ((exp8F k i : ℚ) : ℝ) - invF k| ≤ ((exp8Phi k : ℚ) : ℝ))
    (hπx : ∀ i < 8, |Sx ((2 : ℝ) ^ k * x i)| ≤ logPiX 8 (2 * u 53) ((2 * exp8Eta : ℚ) : ℝ)
      (logXi ((8 : ℕ) * ((2 * exp8Eta : ℚ) : ℝ)) pos (log8E |Real.log (∑ i ∈ range 8, x i)|) ((a : ℚ) : ℝ)
        (b |Real.log (∑ i ∈ range 8, x i)|) (δ |Real.log (∑ i ∈ range 8, x i)|)) i)
    (hSx0 : 1 / 2 ≤ (2 : ℝ) ^ k * x 0 → (2 : ℝ) ^ k * x 0 ≤ 2 → Sx ((2 : ℝ) ^ k * x 0) = (2 : ℝ) ^ k * x 0)
    (eφ et ec : ℤ)
    (hUφ : ∑ i ∈ range 8, |logPhi 53 8 Sx k x i| < (2 : ℝ) ^ (eφ + 1))
    (hUt : ∑ i ∈ range 8, |expCore 53 8 S₁ S₂ e m r (fun k i => ((exp8F k i : ℚ) : ℝ)) d' i| < (2 : ℝ) ^ (et + 1))
    (hUc : ∑ i ∈ range 8, |logC 53 8 Sp 436 eφ et (logPhi 53 8 Sx k x)
      (expCore 53 8 S₁ S₂ e m r (fun k i => ((exp8F k i : ℚ) : ℝ)) d') i| < (2 : ℝ) ^ (ec + 1))
    (hF' : ∀ k, ∀ i < 8, F 53 ((log8F k i : ℚ) : ℝ))
    (hφ' : ∀ k, |∑ i ∈ range 8, ((log8F k i : ℚ) : ℝ) - logFe k| ≤ ((log8Phi k : ℚ) : ℝ))
    (hsh : Log8Shared) {k0 zero : Bool} {b₁ δ₁ b₂ δ₂ : ℚ} (ev₁ : Log8Eval k0 pos m d' a l₁ zero b₁ δ₁)
    (ev₂ : Log8Eval k0 pos m d' a l₂ zero b₂ δ₂) (hb₁ : b ((l₁ : ℚ) : ℝ) ≤ ((b₁ : ℚ) : ℝ))
    (hδ₁ : δ ((l₁ : ℚ) : ℝ) ≤ ((δ₁ : ℚ) : ℝ))
    (hπ₁ : ∀ i < 8, π ((l₁ : ℚ) : ℝ) i ≤ (((if k0 then log8PiY l₁ i else log8PiR l₁ b₁ i : ℚ)) : ℝ))
    (hb₂ : b ((l₂ : ℚ) : ℝ) ≤ ((b₂ : ℚ) : ℝ)) (hδ₂ : δ ((l₂ : ℚ) : ℝ) ≤ ((δ₂ : ℚ) : ℝ))
    (hπ₂ : ∀ i < 8, π ((l₂ : ℚ) : ℝ) i ≤ (((if k0 then log8PiY l₂ i else log8PiR l₂ b₂ i : ℚ)) : ℝ))
    (hc : b₂ + log8Eq l₂ + δ₂ ≤ 3 / 5) :
    |(logOp 53 8 Sx Sp Sc y0 x k (expCore 53 8 S₁ S₂ e m r (fun k i => ((exp8F k i : ℚ) : ℝ)) d') 436 eφ et ec
        (fun k i => ((log8F k i : ℚ) : ℝ)) 4).sum - Real.log (∑ i ∈ range 8, x i)| ≤
      (if zero then (1 : ℝ) / 2 ^ 509 else 0) + 9926 / 1000 * u 53 ^ 8 * |Real.log (∑ i ∈ range 8, x i)| := by
  obtain ⟨bT₁, pq₁, t₁, xi₁, xs₁, cs₁, xd₁, ph₁, sa₁, c4₁, leaf₁, hh₁, hA₁, hB₁, hend₁⟩ := ev₁
  obtain ⟨bT₂, pq₂, t₂, xi₂, xs₂, cs₂, xd₂, ph₂, sa₂, c4₂, leaf₂, hh₂, hA₂, hB₂, hend₂⟩ := ev₂
  have h12 : ((l₁ : ℚ) : ℝ) ≤ ((l₂ : ℚ) : ℝ) := hl.1.trans hl.2
  have m₁ : ((l₁ : ℚ) : ℝ) ∈ Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ) := left_mem_Icc.mpr h12
  have m₂ : ((l₂ : ℚ) : ℝ) ∈ Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ) := right_mem_Icc.mpr h12
  exact log8_chord hS₁ hS₂ hSx hSp hSc x hx hX0 hH y0 hy0 h0 hl hbc hδc hπc hπy hE r hr k hδ a ha hb hπ pos hsgn e
    hU d' hd hF hφF hπx hSx0 eφ et ec hUφ hUt hUc hF' hφ' hsh leaf₁ hb₁ hδ₁ t₁
    (log8_state leaf₁ hh₁ (hbc.nonneg _ m₁) hb₁ (fun i => (hπc i).nonneg _ m₁) hπ₁) rfl hA₁ hB₁ hend₁ leaf₂ hb₂
    hδ₂ t₂ (log8_state leaf₂ hh₂ (hbc.nonneg _ m₂) hb₂ (fun i => (hπc i).nonneg _ m₂) hπ₂) rfl hA₂ hB₂ hend₂ hc

end ExpansionBounds
