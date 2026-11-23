import ExpansionBounds.AccThm
import ExpansionBounds.Sharp

/-!
# Proposition 24 (a) and (c): MUL and MULF err by `u^n(1 + O(u))`

A run's levels depend on the levels it starts from only (`runS`). On the operands of the proposition, which satisfy
`H(1)`, every `TwoProd` is exact or a tie, and every dep either carries a zero or fills a zero level, but for the last
dep of MULF at even `n`: there `TwoSum(u^n, u^{n-1}) = (u^{n-1}, u^n)` carries `u^n`, which rounds with `u^{n+1}` to
`u^n` at level `n` by the tie. The levels are `(1, u, …, u^n)`, and Theorem 9 (c) gives the error. (a) MUL of
`a = (1, u, …, u^{n-2}, 0)` and `b = (1, 0, …, 0, u^{n-1})` errs by `∑_{k=n}^{2n-3} u^k`. (c) With `a_0b = 1 + u`, MULF
of `a = (a_0, 0, a_0u², 0, …)` and `b` errs by `u^n` for odd `n`, and with `a_{n-1} = a_0u^n` by `u^n + u^{n+1}` for
even `n`; `2^p + 1 = m_1m_2` with `m_1, m_2 > 1` gives such `a_0` and `b` in `F`. In each case, (b) included, a bound
`Cu^n|Z| + κu^{n+1}M` with `C, κ ≥ 0` valid on the operands has `C + κu ≥ 1 - O(u)` (`prop24_*_coef`): a `C` at
most `1 - δ` for a fixed `δ > 0` needs `κ ≥ (δ - O(u))/u`, which grows like `1/u`.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) (n : ℕ)

/-- the levels after a dep, from the levels before it -/
noncomputable def depS : ℕ → ℕ → ℝ → (ℕ → ℝ) → ℕ → ℝ
  | 0, _, e, s => Function.update s n (RN p (s n + e))
  | k + 1, m, e, s => depS k (m + 1) (twoSum p (s m) e).2 (Function.update s m (twoSum p (s m) e).1)

/-- the levels after an operation -/
noncomputable def stepS : LOp → (ℕ → ℝ) → ℕ → ℝ
  | .assign m y, s => Function.update s m y
  | .dep l t, s => depS p n (n - l) l t s
  | .round y, s => Function.update s n (RN p (s n + y))

/-- the levels after a run -/
noncomputable def runS : List LOp → (ℕ → ℝ) → ℕ → ℝ
  | [], s => s
  | o :: os, s => runS os (stepS p n o s)

theorem depRun_s : ∀ (k m : ℕ) (e : ℝ) (st : LState), (depRun p n k m e st).2.s = depS p n k m e st.s
  | 0, _, _, _ => rfl
  | k + 1, m, e, st => depRun_s k (m + 1) _ (twoAt p m e st)

theorem stepOp_s (o : LOp) (st : LState) : (stepOp p n o st).2.s = stepS p n o st.s := by
  cases o with
  | assign m y => rfl
  | dep l t => exact depRun_s p n _ _ _ _
  | round y => rfl

/-- a run's levels depend on the levels it starts from only -/
theorem runOps_s : ∀ (ops : List LOp) (st : LState), (runOps p n ops st).2.s = runS p n ops st.s
  | [], _ => rfl
  | o :: os, st => by
    show (runOps p n os (stepOp p n o st).2).2.s = runS p n os (stepS p n o st.s)
    rw [runOps_s os, stepOp_s]

theorem runS_append (l1 l2 : List LOp) (s : ℕ → ℝ) : runS p n (l1 ++ l2) s = runS p n l2 (runS p n l1 s) := by
  induction l1 generalizing s with
  | nil => rfl
  | cons o os ih => exact ih _

theorem runS_assigns (f : ℕ → ℝ) : ∀ (k : ℕ) (s : ℕ → ℝ),
    runS p n ((List.range k).map fun i => LOp.assign i (f i)) s = fun i => if i < k then f i else s i
  | 0, s => by funext i; simp [runS]
  | k + 1, s => by
    rw [List.range_succ, List.map_append, runS_append, runS_assigns f k s]
    funext i
    simp only [List.map_cons, List.map_nil, runS, stepS]
    rw [Function.update_apply]
    by_cases hik : i = k
    · simp [hik]
    · simp only [hik, ite_false]
      by_cases hlt : i < k
      · simp [hlt, show i < k + 1 by omega]
      · simp [hlt, show ¬i < k + 1 by omega]

variable [Prec_gt_0 p]

/-- a dep of `0` leaves levels in `F` as they are -/
theorem depS_zero : ∀ (k m : ℕ) (s : ℕ → ℝ), (∀ j, F p (s j)) → depS p n k m 0 s = s
  | 0, _, s, hF => by
    show Function.update s n (RN p (s n + 0)) = s
    rw [add_zero, RN_of_F p (hF n), Function.update_eq_self]
  | k + 1, m, s, hF => by
    show depS p n k (m + 1) (twoSum p (s m) 0).2 (Function.update s m (twoSum p (s m) 0).1) = s
    rw [twoSum_zero p (hF m), Function.update_eq_self]
    exact depS_zero k (m + 1) s hF

/-- a dep of `e ∈ F` into a zero level below `n` sets that level to `e` -/
theorem depS_into_zero (hp : 1 < p) (k m : ℕ) {e : ℝ} {s : ℕ → ℝ} (hF : ∀ j, F p (s j)) (he : F p e)
    (hs : s m = 0) : depS p n (k + 1) m e s = Function.update s m e := by
  show depS p n k (m + 1) (twoSum p (s m) e).2 (Function.update s m (twoSum p (s m) e).1) = _
  rw [hs, twoSum_zero_left p hp he]
  refine depS_zero p n k (m + 1) _ fun j => ?_
  rw [Function.update_apply]
  split_ifs
  · exact he
  · exact hF j

/-- deps and roundings of `0` leave levels in `F` as they are -/
theorem runS_zero (ops : List LOp) (h : ∀ o ∈ ops, (∃ l, o = LOp.dep l 0) ∨ o = LOp.round 0) :
    ∀ s : ℕ → ℝ, (∀ j, F p (s j)) → runS p n ops s = s := by
  induction ops with
  | nil => intro s _; rfl
  | cons o os ih =>
    intro s hF
    have hs : stepS p n o s = s := by
      rcases h o (by simp) with ⟨l, rfl⟩ | rfl
      · exact depS_zero p n _ _ s hF
      · show Function.update s n (RN p (s n + 0)) = s
        rw [add_zero, RN_of_F p (hF n), Function.update_eq_self]
    show runS p n os (stepS p n o s) = s
    rw [hs]
    exact ih (fun o' ho' => h o' (by simp [ho'])) s hF

omit [Prec_gt_0 p] in
theorem RN_zero : RN p 0 = 0 := roundR_zero _ _

omit [Prec_gt_0 p] in
theorem twoProd_exact {x y : ℝ} (h : F p (x * y)) : twoProd p x y = (x * y, 0) := by
  simp [twoProd, RN_of_F p h, RN_zero]

omit [Prec_gt_0 p] in
theorem twoProd_zero_right (x : ℝ) : twoProd p x 0 = (0, 0) := by
  simp [twoProd, RN_zero]

/-- `TwoProd` of a product `u^i(1 + u)` is `(u^i, u^{i+1})`, by the tie -/
theorem twoProd_tie (hp : 1 < p) (i : ℕ) {x y : ℝ} (h : x * y = u p ^ i + u p ^ (i + 1)) :
    twoProd p x y = (u p ^ i, u p ^ (i + 1)) := by
  have h1 : RN p (x * y) = u p ^ i := by rw [h]; exact congrArg Prod.fst (twoSum_pow p hp i)
  show (RN p (x * y), RN p (x * y - RN p (x * y))) = _
  rw [h1, h, add_sub_cancel_left, RN_of_F p (F_u_pow p _)]

/-- `TwoSum(u^{i+1}, u^i) = (u^i, u^{i+1})`, by the tie -/
theorem twoSum_pow_rev (hp : 1 < p) (i : ℕ) : twoSum p (u p ^ (i + 1)) (u p ^ i) = (u p ^ i, u p ^ (i + 1)) := by
  have h1 : (twoSum p (u p ^ (i + 1)) (u p ^ i)).1 = u p ^ i := by
    show RN p (u p ^ (i + 1) + u p ^ i) = _
    rw [add_comm]
    exact congrArg Prod.fst (twoSum_pow p hp i)
  have h2 := (facts_a p hp (F_u_pow p (i + 1)) (F_u_pow p i)).1
  rw [h1] at h2
  exact Prod.ext h1 (by simp only; linarith)

/-- `Ren_n` of `(1, u, …, u^n)` sums to `∑_{i<n} u^i` -/
theorem ren_pow_sum (hp : 1 < p) (hn : 1 ≤ n) : (ren p n n fun m => u p ^ m).sum = ∑ i ∈ range n, u p ^ i := by
  have h := renErr_pow p hp n hn
  unfold renErr at h
  rw [sum_range_succ] at h
  linarith

/-- the operand `a = (1, u, …, u^{n-2}, 0)` of Proposition 24 (a) -/
noncomputable def sharpA (i : ℕ) : ℝ := if i + 2 ≤ n then u p ^ i else 0

/-- the operand `b = (1, 0, …, 0, u^{n-1})` of Proposition 24 (a) -/
noncomputable def sharpB (j : ℕ) : ℝ := if j = 0 then 1 else if j = n - 1 then u p ^ (n - 1) else 0

/-- the levels of MUL on the operands of Proposition 24 (a) are `(1, u, …, u^n)` -/
theorem mul_sharp_levels (hp : 1 < p) (hn : 3 ≤ n) :
    (runOps p n (mulOps p n (sharpA p n) (sharpB p n)) LState.init).2.s = fun m => if m ≤ n then u p ^ m else 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  set a := sharpA p (k + 3) with ha
  set b := sharpB p (k + 3) with hb
  have hFu := F_u_pow p
  have ha0 : a 0 = 1 := by simp [ha, sharpA]
  have hb0 : b 0 = 1 := by simp [hb, sharpB]
  have hbF : ∀ j, F p (b j) := fun j => by
    simp only [hb, sharpB]
    split_ifs
    · simpa using hFu 0
    · exact hFu _
    · exact F_zero p
  have haF : ∀ i, F p (a i) := fun i => by
    simp only [ha, sharpA]
    split_ifs
    · exact hFu _
    · exact F_zero p
  have htp0 : ∀ j, twoProd p (a 0) (b j) = (b j, 0) := fun j => by
    rw [ha0, twoProd_exact p (by rw [one_mul]; exact hbF j), one_mul]
  -- step (1): `s_j = b_j`
  have hs1 : runS p (k + 3) ((List.range (k + 3)).map fun j => LOp.assign j (twoProd p (a 0) (b j)).1) 0 =
      fun j => if j < k + 3 then b j else 0 := by
    rw [runS_assigns]
    funext j
    simp [htp0]
  -- step (2): `s_n = RN(a_1 b_{n-1}) = u^n`, the other products being zero
  set s2 : ℕ → ℝ := fun j => if j < k + 3 then b j else if j = k + 3 then u p ^ (k + 3) else 0 with hs2
  have hs2F : ∀ j, F p (s2 j) := fun j => by
    simp only [hs2]
    split_ifs
    · exact hbF j
    · exact hFu _
    · exact F_zero p
  have hR : runS p (k + 3) ((List.range (k + 3 - 1)).map fun i => LOp.round (a (i + 1) * b (k + 3 - (i + 1))))
      (fun j => if j < k + 3 then b j else 0) = s2 := by
    rw [show k + 3 - 1 = k + 1 + 1 by omega, List.range_succ_eq_map, List.map_cons, List.map_map]
    have h1 : a (0 + 1) * b (k + 3 - (0 + 1)) = u p ^ (k + 3) := by
      have e1 : a (0 + 1) = u p := by simp [ha, sharpA]
      have e2 : b (k + 3 - (0 + 1)) = u p ^ (k + 2) := by simp [hb, sharpB]
      rw [e1, e2]
      ring
    have hst : stepS p (k + 3) (LOp.round (a (0 + 1) * b (k + 3 - (0 + 1))))
        (fun j => if j < k + 3 then b j else 0) = s2 := by
      rw [h1]
      funext j
      show Function.update (fun j => if j < k + 3 then b j else 0) (k + 3)
        (RN p ((if k + 3 < k + 3 then b (k + 3) else 0) + u p ^ (k + 3))) j = s2 j
      simp only [lt_irrefl, ite_false, zero_add, RN_of_F p (hFu _), Function.update_apply, hs2]
      split_ifs <;> first | rfl | omega
    show runS p (k + 3) _ (stepS p (k + 3) (LOp.round (a (0 + 1) * b (k + 3 - (0 + 1)))) _) = _
    rw [hst]
    refine runS_zero p (k + 3) _ (fun o ho => ?_) _ hs2F
    simp only [List.mem_map, List.mem_range, Function.comp_apply] at ho
    obtain ⟨i, hi, rfl⟩ := ho
    right
    simp only [hb, sharpB]
    simp only [show k + 3 - (Nat.succ i + 1) ≠ 0 by omega, show k + 3 - (Nat.succ i + 1) ≠ k + 3 - 1 by omega,
      ite_false, mul_zero]
  -- step (3): the errors of step (1) are zero
  have hD : runS p (k + 3) ((List.range (k + 3)).map fun l => LOp.dep (l + 1) (twoProd p (a 0) (b l)).2) s2 = s2 :=
    runS_zero p (k + 3) _ (fun o ho => by
      simp only [List.mem_map, List.mem_range] at ho
      obtain ⟨l, -, rfl⟩ := ho
      exact Or.inl ⟨l + 1, by rw [htp0]⟩) s2 hs2F
  -- step (4): row `i` puts `a_{i+1} = u^{i+1}` into the zero level `i + 1`, every other product being zero
  set t : ℕ → ℕ → ℝ := fun I j => if 1 ≤ j ∧ j ≤ I ∧ j + 2 ≤ k + 3 then u p ^ j else s2 j with ht
  have htF : ∀ I j, F p (t I j) := fun I j => by
    simp only [ht]
    split_ifs
    · exact hFu _
    · exact hs2F j
  have hrow : ∀ i, i < k + 2 → runS p (k + 3) ((List.range (k + 3 - 1 - i)).flatMap fun j =>
      [LOp.dep (i + 1 + j) (twoProd p (a (i + 1)) (b j)).1, LOp.dep (i + 1 + j + 1) (twoProd p (a (i + 1)) (b j)).2])
      (t i) = t (i + 1) := by
    intro i hi
    rw [show k + 3 - 1 - i = (k + 1 - i) + 1 by omega, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]
    rw [hb0, twoProd_exact p (by rw [mul_one]; exact haF _), mul_one, runS_append]
    have hz : runS p (k + 3) ((List.range (k + 1 - i)).flatMap fun j =>
        [LOp.dep (i + 1 + (j + 1)) (twoProd p (a (i + 1)) (b (j + 1))).1,
          LOp.dep (i + 1 + (j + 1) + 1) (twoProd p (a (i + 1)) (b (j + 1))).2]) (t (i + 1)) = t (i + 1) := by
      refine runS_zero p (k + 3) _ (fun o ho => ?_) _ (htF _)
      simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff, or_false] at ho
      obtain ⟨j, hj, rfl | rfl⟩ := ho <;>
      · left
        have hbj : b (j + 1) = 0 := by
          simp only [hb, sharpB, show j + 1 ≠ 0 by omega, show j + 1 ≠ k + 3 - 1 by omega, ite_false]
        rw [hbj, twoProd_zero_right]
        exact ⟨_, rfl⟩
    have hfirst : runS p (k + 3) [LOp.dep (i + 1 + 0) (a (i + 1)), LOp.dep (i + 1 + 0 + 1) 0] (t i) = t (i + 1) := by
      show stepS p (k + 3) (LOp.dep (i + 1 + 0 + 1) 0) (stepS p (k + 3) (LOp.dep (i + 1 + 0) (a (i + 1))) (t i)) = _
      by_cases hik : i + 1 + 2 ≤ k + 3
      · have hai : a (i + 1) = u p ^ (i + 1) := by simp [ha, sharpA, hik]
        have h0 : t i (i + 1) = 0 := by
          simp only [ht, hs2, hb, sharpB]
          simp only [show ¬(1 ≤ i + 1 ∧ i + 1 ≤ i ∧ i + 1 + 2 ≤ k + 3) by omega, ite_false,
            show i + 1 < k + 3 by omega, ite_true, show i + 1 ≠ 0 by omega, show i + 1 ≠ k + 3 - 1 by omega]
        rw [hai]
        show depS p (k + 3) (k + 3 - (i + 1 + 0 + 1)) _ 0 (depS p (k + 3) (k + 3 - (i + 1 + 0)) _ _ (t i)) = _
        rw [show k + 3 - (i + 1 + 0) = (k + 1 - i) + 1 by omega, depS_into_zero p (k + 3) hp _ _ (htF i)
          (hFu _) (by simpa using h0)]
        rw [depS_zero p (k + 3) _ _ _ fun j => by
          rw [Function.update_apply]; split_ifs
          · exact hFu _
          · exact htF i j]
        funext j
        simp only [ht, Function.update_apply]
        by_cases hj : j = i + 1 + 0
        · subst hj
          simp only [ite_true]
          simp [show 1 ≤ i + 1 + 0 ∧ i + 1 + 0 ≤ i + 1 ∧ i + 1 + 0 + 2 ≤ k + 3 by omega]
        · simp only [hj, ite_false]
          by_cases hc : 1 ≤ j ∧ j ≤ i ∧ j + 2 ≤ k + 3
          · have hc' : 1 ≤ j ∧ j ≤ i + 1 ∧ j + 2 ≤ k + 3 := by omega
            simp only [hc, hc']
          · have hc' : ¬(1 ≤ j ∧ j ≤ i + 1 ∧ j + 2 ≤ k + 3) := by omega
            simp only [hc, hc', ite_false]
      · have hai : a (i + 1) = 0 := by simp [ha, sharpA, hik]
        rw [hai]
        show depS p (k + 3) _ _ 0 (depS p (k + 3) _ _ 0 (t i)) = _
        rw [depS_zero p (k + 3) _ _ _ (htF i), depS_zero p (k + 3) _ _ _ (htF i)]
        funext j
        simp only [ht]
        by_cases hc : 1 ≤ j ∧ j ≤ i ∧ j + 2 ≤ k + 3
        · have hc' : 1 ≤ j ∧ j ≤ i + 1 ∧ j + 2 ≤ k + 3 := by omega
          simp only [hc, hc']
        · have hc' : ¬(1 ≤ j ∧ j ≤ i + 1 ∧ j + 2 ≤ k + 3) := by omega
          simp only [hc, hc', ite_false]
    have hsplit : ∀ l : List LOp, runS p (k + 3) ([LOp.dep (i + 1 + 0) (a (i + 1)),
        LOp.dep (i + 1 + 0 + 1) 0] ++ l) (t i) = runS p (k + 3) l (t (i + 1)) := fun l => by
      rw [runS_append, hfirst]
    exact (hsplit _).trans hz
  have hS4 : ∀ I, I ≤ k + 2 → runS p (k + 3) ((List.range I).flatMap fun i =>
      (List.range (k + 3 - 1 - i)).flatMap fun j =>
        [LOp.dep (i + 1 + j) (twoProd p (a (i + 1)) (b j)).1,
          LOp.dep (i + 1 + j + 1) (twoProd p (a (i + 1)) (b j)).2]) s2 = t I := by
    intro I
    induction I with
    | zero =>
      intro _
      funext j
      simp only [List.range_zero, List.flatMap_nil, runS, ht]
      have : ¬(1 ≤ j ∧ j ≤ 0 ∧ j + 2 ≤ k + 3) := by omega
      simp only [this, ite_false]
    | succ I ih =>
      intro hI
      rw [List.range_succ, List.flatMap_append, runS_append, ih (by omega), List.flatMap_singleton]
      exact hrow I (by omega)
  have hmul : mulOps p (k + 3) a b = ((List.range (k + 3)).map fun j => LOp.assign j (twoProd p (a 0) (b j)).1) ++
      ((List.range (k + 3 - 1)).map fun i => LOp.round (a (i + 1) * b (k + 3 - (i + 1)))) ++
      ((List.range (k + 3)).map fun l => LOp.dep (l + 1) (twoProd p (a 0) (b l)).2) ++
      mulStep4 p (k + 3) a b := rfl
  rw [runOps_s, hmul, runS_append, runS_append, runS_append]
  show runS p (k + 3) (mulStep4 p (k + 3) a b) (runS p (k + 3) _ (runS p (k + 3) _ (runS p (k + 3) _ 0))) = _
  rw [hs1, hR, hD]
  unfold mulStep4
  rw [show k + 3 - 1 = k + 2 by omega] at *
  rw [hS4 (k + 2) le_rfl]
  funext j
  simp only [ht, hs2, hb, sharpB]
  by_cases hj1 : 1 ≤ j ∧ j ≤ k + 2 ∧ j + 2 ≤ k + 3
  · simp [hj1, show j ≤ k + 3 by omega]
  · simp only [hj1, ite_false]
    rcases Nat.lt_trichotomy j (k + 3) with hlt | rfl | hgt
    · simp only [hlt, ite_true]
      by_cases hj0 : j = 0
      · simp [hj0]
      · simp only [hj0, ite_false]
        have : j = k + 2 := by omega
        simp [this]
    · simp
    · simp [show ¬j < k + 3 by omega, show j ≠ k + 3 by omega, show ¬j ≤ k + 3 by omega]

omit [Prec_gt_0 p] in
/-- the product of the operands of Proposition 24 (a): `ab = ∑_{k<2n-2} u^k` -/
theorem sharpAB_sum (hn : 3 ≤ n) :
    ∑ i ∈ range n, ∑ j ∈ range n, sharpA p n i * sharpB p n j = ∑ i ∈ range (2 * n - 2), u p ^ i := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [← sum_mul_sum]
  have hA : ∑ i ∈ range (k + 3), sharpA p (k + 3) i = ∑ i ∈ range (k + 2), u p ^ i := by
    rw [sum_range_succ]
    simp only [sharpA, show ¬(k + 2 + 2 ≤ k + 3) by omega, ite_false, add_zero]
    exact sum_congr rfl fun i hi => by
      simp only [mem_range] at hi
      simp only [show i + 2 ≤ k + 3 by omega, ite_true]
  have hB : ∑ j ∈ range (k + 3), sharpB p (k + 3) j = 1 + u p ^ (k + 2) := by
    rw [sum_range_succ, sum_range_succ', sum_eq_zero fun j hj => by
      simp only [mem_range] at hj
      simp only [sharpB, show j + 1 ≠ 0 by omega, show j + 1 ≠ k + 3 - 1 by omega, ite_false]]
    have e0 : sharpB p (k + 3) 0 = 1 := by simp [sharpB]
    have e1 : sharpB p (k + 3) (k + 2) = u p ^ (k + 2) := by simp [sharpB]
    rw [e0, e1]
    ring
  rw [hA, hB, show 2 * (k + 3) - 2 = (k + 2) + (k + 2) by omega, sum_range_add (fun i => u p ^ i) (k + 2) (k + 2),
    mul_add, mul_one, sum_mul]
  congr 1
  exact sum_congr rfl fun i _ => by ring

/-- Proposition 24 (a): MUL of `a = (1, u, …, u^{n-2}, 0)` and `b = (1, 0, …, 0, u^{n-1})` errs by
`∑_{k=n}^{2n-3} u^k = u^n |ab| (1 - u^{n-2})/(1 - u^{2n-2})` -/
theorem prop24_mul (hp : 1 < p) (hn : 3 ≤ n) :
    |(∑ i ∈ range n, ∑ j ∈ range n, sharpA p n i * sharpB p n j) - (mulOp p n (sharpA p n) (sharpB p n)).sum| =
        ∑ k ∈ Ico n (2 * n - 2), u p ^ k ∧
      ∑ k ∈ Ico n (2 * n - 2), u p ^ k =
        u p ^ n * |∑ i ∈ range n, ∑ j ∈ range n, sharpA p n i * sharpB p n j| *
          (1 - u p ^ (n - 2)) / (1 - u p ^ (2 * n - 2)) := by
  have hu := u_pos p
  have hu1 : u p < 1 := by linarith [u_le_half p hp]
  have hx : (mulOp p n (sharpA p n) (sharpB p n)).sum = ∑ i ∈ range n, u p ^ i := by
    unfold mulOp
    rw [mul_sharp_levels p n hp hn, ren_congr p n n (c' := fun m => u p ^ m) (fun i hi => by simp [hi]),
      ren_pow_sum p n hp (by omega)]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hab := sharpAB_sum p (k + 3) (by omega)
  have hpos : 0 ≤ ∑ i ∈ range (2 * (k + 3) - 2), u p ^ i := sum_nonneg fun i _ => pow_nonneg hu.le i
  have hsplit : ∑ i ∈ range (2 * (k + 3) - 2), u p ^ i =
      ∑ i ∈ range (k + 3), u p ^ i + ∑ i ∈ Ico (k + 3) (2 * (k + 3) - 2), u p ^ i :=
    (sum_range_add_sum_Ico _ (by omega)).symm
  refine ⟨?_, ?_⟩
  · rw [hx, hab, hsplit, add_sub_cancel_left, abs_of_nonneg (sum_nonneg fun i _ => pow_nonneg hu.le i)]
  · rw [hab, abs_of_nonneg hpos, geom_sum_Ico hu1.ne (by omega), geom_sum_eq hu1.ne]
    have h1 : u p - 1 ≠ 0 := by linarith
    have h2 : 1 - u p ^ (2 * (k + 3) - 2) ≠ 0 := by
      have := pow_lt_one₀ hu.le hu1 (show 2 * (k + 3) - 2 ≠ 0 by omega)
      linarith
    rw [show 2 * (k + 3) - 2 = 2 * k + 4 by omega, show k + 3 - 2 = k + 1 by omega] at *
    field_simp
    ring

omit [Prec_gt_0 p] in
theorem twoProd_zero_left (x : ℝ) : twoProd p 0 x = (0, 0) := by
  simp [twoProd, RN_zero]

/-- the operand `a` of Proposition 24 (c): `a_i = a_0u^i` for even `i`, `a_{n-1} = a_0u^n` for even `n`, and
zero otherwise -/
noncomputable def sharpC (a0 : ℝ) (i : ℕ) : ℝ :=
  if i % 2 = 0 then a0 * u p ^ i else if i + 1 = n then a0 * u p ^ n else 0

/-- `TwoProd(a_i, b)` on the operands of Proposition 24 (c), with `a_0b = 1 + u` -/
theorem sharpC_twoProd (hp : 1 < p) {a0 b : ℝ} (hab : a0 * b = 1 + u p) (i : ℕ) :
    twoProd p (sharpC p n a0 i) b = if i % 2 = 0 then (u p ^ i, u p ^ (i + 1))
      else if i + 1 = n then (u p ^ n, u p ^ (n + 1)) else (0, 0) := by
  unfold sharpC
  split_ifs
  · exact twoProd_tie p hp i (by rw [mul_right_comm, hab]; ring)
  · exact twoProd_tie p hp n (by rw [mul_right_comm, hab]; ring)
  · exact twoProd_zero_left p b

omit [Prec_gt_0 p] in
/-- MULF's program on the operands of Proposition 24 (c) -/
theorem mulfOps_sharpC (a0 b : ℝ) : mulfOps p n (sharpC p n a0) b =
    ((List.range n).map fun i => LOp.assign i (twoProd p (sharpC p n a0 i) b).1) ++
      [LOp.assign n (twoProd p (sharpC p n a0 (n - 1)) b).2] ++
      (List.range (n - 1)).map fun l => LOp.dep (l + 1) (twoProd p (sharpC p n a0 l) b).2 := by
  simp only [mulfOps, pairOps, List.map_map]
  rfl

/-- the levels of MULF on the operands of Proposition 24 (c) for odd `n` are `(1, u, …, u^n)` -/
theorem mulf_sharp_levels_odd (hp : 1 < p) (hn : n % 2 = 1) {a0 b : ℝ} (hab : a0 * b = 1 + u p) :
    mulfLevels p n (sharpC p n a0) b = fun m => if m ≤ n then u p ^ m else 0 := by
  have hFu := F_u_pow p
  have htp := sharpC_twoProd p n hp hab
  set t : ℕ → ℕ → ℝ := fun L j => if j ≤ n ∧ (j % 2 = 0 ∨ j ≤ L ∨ j = n) then u p ^ j else 0 with ht
  have htF : ∀ L j, F p (t L j) := fun L j => by
    simp only [ht]
    split_ifs
    · exact hFu _
    · exact F_zero p
  have h0 : runS p n ([LOp.assign n (twoProd p (sharpC p n a0 (n - 1)) b).2])
      (runS p n ((List.range n).map fun i => LOp.assign i (twoProd p (sharpC p n a0 i) b).1) 0) = t 0 := by
    rw [runS_assigns]
    funext j
    simp only [runS, stepS, Function.update_apply, ht]
    have hn1 : (n - 1) % 2 = 0 := by omega
    by_cases hjn : j = n
    · subst hjn
      simp [htp, hn1, show j - 1 + 1 = j by omega]
    · simp only [hjn, ite_false]
      by_cases hj : j < n
      · rw [htp]
        by_cases he : j % 2 = 0
        · simp [hj, he, show j ≤ n by omega]
        · simp [hj, he, show j + 1 ≠ n by omega, show ¬j ≤ 0 by omega]
      · simp [hj, show ¬j ≤ n by omega]
  have hstep : ∀ L, L < n - 1 → runS p n [LOp.dep (L + 1) (twoProd p (sharpC p n a0 L) b).2] (t L) = t (L + 1) := by
    intro L hL
    show depS p n (n - (L + 1)) (L + 1) _ (t L) = _
    rw [htp]
    by_cases he : L % 2 = 0
    · simp only [he, ite_true]
      have hz : t L (L + 1) = 0 := by
        simp only [ht]
        have : ¬(L + 1 ≤ n ∧ ((L + 1) % 2 = 0 ∨ L + 1 ≤ L ∨ L + 1 = n)) := by omega
        simp only [this, ite_false]
      rw [show n - (L + 1) = (n - L - 2) + 1 by omega, depS_into_zero p n hp _ _ (htF L) (hFu _) hz]
      funext j
      simp only [Function.update_apply, ht]
      by_cases hj : j = L + 1
      · subst hj
        have : L + 1 ≤ n ∧ ((L + 1) % 2 = 0 ∨ L + 1 ≤ L + 1 ∨ L + 1 = n) := by omega
        simp only [ite_true, this, and_self]
      · simp only [hj, ite_false]
        by_cases hc : j ≤ n ∧ (j % 2 = 0 ∨ j ≤ L ∨ j = n)
        · have hc' : j ≤ n ∧ (j % 2 = 0 ∨ j ≤ L + 1 ∨ j = n) := by omega
          simp only [hc, hc']
        · have hc' : ¬(j ≤ n ∧ (j % 2 = 0 ∨ j ≤ L + 1 ∨ j = n)) := by omega
          simp only [hc, hc']
    · simp only [he, ite_false, show L + 1 ≠ n by omega]
      rw [depS_zero p n _ _ _ (htF L)]
      funext j
      simp only [ht]
      by_cases hc : j ≤ n ∧ (j % 2 = 0 ∨ j ≤ L ∨ j = n)
      · have hc' : j ≤ n ∧ (j % 2 = 0 ∨ j ≤ L + 1 ∨ j = n) := by omega
        simp only [hc, hc']
      · have hc' : ¬(j ≤ n ∧ (j % 2 = 0 ∨ j ≤ L + 1 ∨ j = n)) := by omega
        simp only [hc, hc']
  have hD : ∀ L, L ≤ n - 1 →
      runS p n ((List.range L).map fun l => LOp.dep (l + 1) (twoProd p (sharpC p n a0 l) b).2) (t 0) = t L := by
    intro L
    induction L with
    | zero => intro _; rfl
    | succ L ih =>
      intro hL
      rw [List.range_succ, List.map_append, runS_append, ih (by omega)]
      exact hstep L (by omega)
  unfold mulfLevels
  rw [runOps_s, mulfOps_sharpC, runS_append, runS_append]
  show runS p n _ (runS p n _ (runS p n _ 0)) = _
  rw [h0, hD (n - 1) le_rfl]
  funext j
  simp only [ht]
  by_cases hj : j ≤ n
  · have : j ≤ n ∧ (j % 2 = 0 ∨ j ≤ n - 1 ∨ j = n) := by omega
    simp only [this, ite_true, and_self]
  · simp only [hj, false_and, ite_false]

/-- the levels of MULF on the operands of Proposition 24 (c) for even `n` are `(1, u, …, u^n)`: the last dep,
`TwoSum(u^n, u^{n-1}) = (u^{n-1}, u^n)`, rounds `u^{n+1} + u^n` to `u^n` -/
theorem mulf_sharp_levels_even (hp : 1 < p) (hn : n % 2 = 0) (hn2 : 2 ≤ n) {a0 b : ℝ} (hab : a0 * b = 1 + u p) :
    mulfLevels p n (sharpC p n a0) b = fun m => if m ≤ n then u p ^ m else 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hFu := F_u_pow p
  have htp := sharpC_twoProd p (k + 2) hp hab
  set t : ℕ → ℕ → ℝ := fun L j => if j + 1 < k + 2 ∧ (j % 2 = 0 ∨ j ≤ L) then u p ^ j
    else if j + 1 = k + 2 then u p ^ (k + 2) else if j = k + 2 then u p ^ (k + 2 + 1) else 0 with ht
  have htF : ∀ L j, F p (t L j) := fun L j => by
    simp only [ht]
    split_ifs <;> first | exact hFu _ | exact F_zero p
  have h0 : runS p (k + 2) ([LOp.assign (k + 2) (twoProd p (sharpC p (k + 2) a0 (k + 2 - 1)) b).2])
      (runS p (k + 2) ((List.range (k + 2)).map fun i => LOp.assign i (twoProd p (sharpC p (k + 2) a0 i) b).1) 0) =
      t 0 := by
    rw [runS_assigns]
    funext j
    simp only [runS, stepS, Function.update_apply, ht]
    by_cases hjn : j = k + 2
    · rw [hjn, htp]
      simp [show ¬((k + 1) % 2 = 0) by omega]
    · simp only [hjn, ite_false]
      by_cases hj : j < k + 2
      · rw [htp]
        by_cases he : j % 2 = 0
        · simp [hj, he, show j + 1 < k + 2 by omega]
        · by_cases hj1 : j + 1 = k + 2
          · simp [hj, he, hj1]
          · simp [hj, he, show j ≠ k + 1 by omega, show ¬j ≤ 0 by omega]
      · simp [hj, show ¬(j + 1 < k + 2) by omega, show j ≠ k + 1 by omega]
  have hstep : ∀ L, L < k → runS p (k + 2) [LOp.dep (L + 1) (twoProd p (sharpC p (k + 2) a0 L) b).2] (t L) =
      t (L + 1) := by
    intro L hL
    show depS p (k + 2) (k + 2 - (L + 1)) (L + 1) _ (t L) = _
    rw [htp]
    by_cases he : L % 2 = 0
    · simp only [he, ite_true]
      have hz : t L (L + 1) = 0 := by
        simp only [ht]
        have h1 : ¬(L + 1 + 1 < k + 2 ∧ ((L + 1) % 2 = 0 ∨ L + 1 ≤ L)) := by omega
        simp only [h1, ite_false, show L + 1 + 1 ≠ k + 2 by omega, show L + 1 ≠ k + 2 by omega]
      rw [show k + 2 - (L + 1) = (k - L) + 1 by omega, depS_into_zero p (k + 2) hp _ _ (htF L) (hFu _) hz]
      funext j
      simp only [Function.update_apply, ht]
      by_cases hj : j = L + 1
      · subst hj
        have : L + 1 + 1 < k + 2 ∧ ((L + 1) % 2 = 0 ∨ L + 1 ≤ L + 1) := by omega
        simp only [ite_true, this, and_self]
      · simp only [hj, ite_false]
        by_cases hc : j + 1 < k + 2 ∧ (j % 2 = 0 ∨ j ≤ L)
        · have hc' : j + 1 < k + 2 ∧ (j % 2 = 0 ∨ j ≤ L + 1) := by omega
          simp only [hc, hc']
        · have hc' : ¬(j + 1 < k + 2 ∧ (j % 2 = 0 ∨ j ≤ L + 1)) := by omega
          simp only [hc, hc']
    · simp only [he, ite_false, show L + 1 ≠ k + 2 by omega]
      rw [depS_zero p (k + 2) _ _ _ (htF L)]
      funext j
      simp only [ht]
      by_cases hc : j + 1 < k + 2 ∧ (j % 2 = 0 ∨ j ≤ L)
      · have hc' : j + 1 < k + 2 ∧ (j % 2 = 0 ∨ j ≤ L + 1) := by omega
        simp only [hc, hc']
      · have hc' : ¬(j + 1 < k + 2 ∧ (j % 2 = 0 ∨ j ≤ L + 1)) := by omega
        simp only [hc, hc']
  have hD : ∀ L, L ≤ k →
      runS p (k + 2) ((List.range L).map fun l => LOp.dep (l + 1) (twoProd p (sharpC p (k + 2) a0 l) b).2) (t 0) =
        t L := by
    intro L
    induction L with
    | zero => intro _; rfl
    | succ L ih =>
      intro hL
      rw [List.range_succ, List.map_append, runS_append, ih (by omega)]
      exact hstep L (by omega)
  have hs1 : t k (k + 1) = u p ^ (k + 1 + 1) := by
    simp only [ht]
    simp
  have hs2 : t k (k + 2) = u p ^ (k + 2 + 1) := by
    simp only [ht]
    simp
  have hlast : runS p (k + 2) [LOp.dep (k + 1) (twoProd p (sharpC p (k + 2) a0 k) b).2] (t k) =
      fun m => if m ≤ k + 2 then u p ^ m else 0 := by
    rw [htp]
    simp only [show k % 2 = 0 by omega, ite_true]
    show depS p (k + 2) (k + 2 - (k + 1)) (k + 1) (u p ^ (k + 1)) (t k) = _
    rw [show k + 2 - (k + 1) = 0 + 1 by omega]
    show depS p (k + 2) 0 (k + 1 + 1) (twoSum p (t k (k + 1)) (u p ^ (k + 1))).2
      (Function.update (t k) (k + 1) (twoSum p (t k (k + 1)) (u p ^ (k + 1))).1) = _
    rw [hs1, twoSum_pow_rev p hp (k + 1)]
    show Function.update (Function.update (t k) (k + 1) (u p ^ (k + 1))) (k + 2)
      (RN p (Function.update (t k) (k + 1) (u p ^ (k + 1)) (k + 2) + u p ^ (k + 1 + 1))) = _
    have hRN : RN p (u p ^ (k + 2) + u p ^ (k + 2 + 1)) = u p ^ (k + 2) := congrArg Prod.fst (twoSum_pow p hp (k + 2))
    rw [Function.update_of_ne (show k + 2 ≠ k + 1 by omega), hs2,
      show u p ^ (k + 2 + 1) + u p ^ (k + 1 + 1) = u p ^ (k + 2) + u p ^ (k + 2 + 1) by ring, hRN]
    funext j
    simp only [Function.update_apply, ht]
    by_cases hj2 : j = k + 2
    · simp [hj2]
    · by_cases hj1 : j = k + 1
      · simp [hj1]
      · simp only [hj2, hj1, ite_false]
        by_cases hj : j ≤ k
        · have : j + 1 < k + 2 ∧ (j % 2 = 0 ∨ j ≤ k) := by omega
          simp only [this, and_self, ite_true, show j ≤ k + 2 by omega]
        · simp only [show ¬(j + 1 < k + 2 ∧ (j % 2 = 0 ∨ j ≤ k)) by omega, show j + 1 ≠ k + 2 by omega,
            show ¬j ≤ k + 2 by omega, ite_false]
  unfold mulfLevels
  rw [runOps_s, mulfOps_sharpC, runS_append, runS_append]
  show runS p (k + 2) _ (runS p (k + 2) _ (runS p (k + 2) _ 0)) = _
  rw [h0, show k + 2 - 1 = k + 1 by omega, List.range_succ, List.map_append, runS_append, hD k le_rfl]
  exact hlast

omit [Prec_gt_0 p] in
/-- `∑_{i<2k} [i even](u^i + u^{i+1}) = ∑_{i<2k} u^i` -/
theorem sum_even_pairs (k : ℕ) :
    ∑ i ∈ range (2 * k), (if i % 2 = 0 then u p ^ i + u p ^ (i + 1) else 0) = ∑ i ∈ range (2 * k), u p ^ i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ (fun i => u p ^ i) (2 * k + 1), sum_range_succ (fun i => u p ^ i) (2 * k)]
    simp only [show (2 * k) % 2 = 0 by omega, show ¬((2 * k + 1) % 2 = 0) by omega, ite_true, ite_false]
    ring

omit [Prec_gt_0 p] in
theorem sharpC_mul {a0 b : ℝ} (hab : a0 * b = 1 + u p) (i : ℕ) : sharpC p n a0 i * b =
    if i % 2 = 0 then u p ^ i + u p ^ (i + 1) else if i + 1 = n then u p ^ n + u p ^ (n + 1) else 0 := by
  unfold sharpC
  split_ifs
  · rw [mul_right_comm, hab]; ring
  · rw [mul_right_comm, hab]; ring
  · ring

omit [Prec_gt_0 p] in
/-- the terms of the exact product below the last pair are `u^i + u^{i+1}` for even `i` -/
theorem sum_sharpC_mul {a0 b : ℝ} (hab : a0 * b = 1 + u p) (k : ℕ) (hk : 2 * k < n) :
    ∑ i ∈ range (2 * k), sharpC p n a0 i * b = ∑ i ∈ range (2 * k), u p ^ i := by
  rw [← sum_even_pairs p k]
  refine sum_congr rfl fun i hi => ?_
  simp only [mem_range] at hi
  rw [sharpC_mul p n hab]
  simp only [show i + 1 ≠ n by omega, ite_false]

/-- Proposition 24 (c) for odd `n`: with `a_0b = 1 + u`, MULF of `a = (a_0, 0, a_0u², 0, …, a_0u^{n-1})` and `b`
errs by `u^n = u^n |ab| (1 - u)/(1 - u^{n+1})` -/
theorem prop24_mulf_odd (hp : 1 < p) (hn : n % 2 = 1) {a0 b : ℝ} (hab : a0 * b = 1 + u p) :
    |∑ i ∈ range n, sharpC p n a0 i * b - (mulfOp p n (sharpC p n a0) b).sum| = u p ^ n ∧
      u p ^ n = u p ^ n * |∑ i ∈ range n, sharpC p n a0 i * b| * (1 - u p) / (1 - u p ^ (n + 1)) := by
  have hx : (mulfOp p n (sharpC p n a0) b).sum = ∑ i ∈ range n, u p ^ i := by
    unfold mulfOp
    rw [mulf_sharp_levels_odd p n hp hn hab, ren_congr p n n (c' := fun m => u p ^ m) (fun i hi => by simp [hi]),
      ren_pow_sum p n hp (by omega)]
  have hz : ∑ i ∈ range n, sharpC p n a0 i * b = ∑ i ∈ range (n + 1), u p ^ i := by
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    rw [sum_range_succ, sum_sharpC_mul p _ hab k (by omega), sharpC_mul p _ hab,
      sum_range_succ (fun i => u p ^ i) (2 * k + 1), sum_range_succ (fun i => u p ^ i) (2 * k)]
    simp only [show (2 * k) % 2 = 0 by omega, ite_true]
    ring
  refine ⟨?_, ?_⟩
  · rw [hz, hx, sum_range_succ, add_sub_cancel_left, abs_of_pos (pow_pos (u_pos p) n)]
  · rw [hz]
    exact u_pow_rel p hp n

/-- Proposition 24 (c) for even `n`: with `a_0b = 1 + u`, MULF of `a = (a_0, 0, a_0u², 0, …, a_0u^{n-2}, a_0u^n)`
and `b` errs by `u^n + u^{n+1} = u^n |ab| (1 - u²)/(1 - u^{n+2})` -/
theorem prop24_mulf_even (hp : 1 < p) (hn : n % 2 = 0) (hn2 : 2 ≤ n) {a0 b : ℝ} (hab : a0 * b = 1 + u p) :
    |∑ i ∈ range n, sharpC p n a0 i * b - (mulfOp p n (sharpC p n a0) b).sum| = u p ^ n + u p ^ (n + 1) ∧
      u p ^ n + u p ^ (n + 1) =
        u p ^ n * |∑ i ∈ range n, sharpC p n a0 i * b| * (1 - u p ^ 2) / (1 - u p ^ (n + 2)) := by
  have hu := u_pos p
  have hu1 : u p < 1 := by linarith [u_le_half p hp]
  have hx : (mulfOp p n (sharpC p n a0) b).sum = ∑ i ∈ range n, u p ^ i := by
    unfold mulfOp
    rw [mulf_sharp_levels_even p n hp hn hn2 hab, ren_congr p n n (c' := fun m => u p ^ m) (fun i hi => by simp [hi]),
      ren_pow_sum p n hp (by omega)]
  have hz : ∑ i ∈ range n, sharpC p n a0 i * b = ∑ i ∈ range (n + 2), u p ^ i := by
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 2 := ⟨n / 2 - 1, by omega⟩
    rw [show 2 * k + 2 = 2 * k + 1 + 1 by ring, sum_range_succ, sum_range_succ, sum_sharpC_mul p _ hab k (by omega),
      sharpC_mul p _ hab, sharpC_mul p _ hab]
    simp only [show (2 * k) % 2 = 0 by omega, show ¬((2 * k + 1) % 2 = 0) by omega, ite_true, ite_false]
    simp only [sum_range_succ]
    ring
  have hpos : 0 < ∑ i ∈ range (n + 2), u p ^ i :=
    sum_pos (fun i _ => pow_pos hu i) ⟨0, by simp⟩
  refine ⟨?_, ?_⟩
  · rw [hz, hx, show n + 2 = n + 1 + 1 by ring, sum_range_succ, sum_range_succ]
    rw [show ∑ i ∈ range n, u p ^ i + u p ^ n + u p ^ (n + 1) - ∑ i ∈ range n, u p ^ i =
      u p ^ n + u p ^ (n + 1) by ring, abs_of_pos (by positivity)]
  · rw [hz, abs_of_pos hpos, geom_sum_eq hu1.ne]
    have h1 : u p - 1 ≠ 0 := by linarith
    have h2 : 1 - u p ^ (n + 2) ≠ 0 := by
      have := pow_lt_one₀ hu.le hu1 (show n + 2 ≠ 0 by omega)
      linarith
    field_simp
    ring

/-- `2^p + 1 = m_1m_2` with `m_1, m_2 > 1` gives the operands of Proposition 24 (c): `a_0 = m_1 2^{-k}` and
`b = m_2 2^{k-p}`, `k = ⌊log₂ m_1⌋`, with `a_0 2^e` and `b` in `F` and `a_0b = 1 + u` -/
theorem prop24c_operands (hp : 1 < p) (m1 m2 : ℕ) (h1 : 1 < m1) (h2 : 1 < m2) (hm : (m1 : ℝ) * m2 = 2 ^ p + 1) :
    (∀ e : ℤ, F p ((m1 : ℝ) * 2 ^ (-(Nat.log 2 m1 : ℤ)) * 2 ^ e)) ∧
      F p ((m2 : ℝ) * 2 ^ ((Nat.log 2 m1 : ℤ) - p)) ∧
      (m1 : ℝ) * 2 ^ (-(Nat.log 2 m1 : ℤ)) * ((m2 : ℝ) * 2 ^ ((Nat.log 2 m1 : ℤ) - p)) = 1 + u p := by
  set k : ℤ := (Nat.log 2 m1 : ℤ)
  have h2p : (2 : ℝ) < 2 ^ p := by
    calc (2 : ℝ) = 2 ^ (1 : ℤ) := by norm_num
      _ < 2 ^ p := zpow_lt_zpow_right₀ (by norm_num) hp
  have hm1 : (m1 : ℝ) < 2 ^ p := by
    have : (2 : ℝ) ≤ m2 := by exact_mod_cast h2
    nlinarith [(Nat.cast_nonneg m1 : (0 : ℝ) ≤ m1)]
  have hm2 : (m2 : ℝ) < 2 ^ p := by
    have : (2 : ℝ) ≤ m1 := by exact_mod_cast h1
    nlinarith [(Nat.cast_nonneg m2 : (0 : ℝ) ≤ m2)]
  have hF : ∀ (m : ℕ) (E : ℤ), (m : ℝ) < 2 ^ p → F p ((m : ℝ) * 2 ^ E) := fun m E hm => by
    refine F_of_mult p ⟨m, by push_cast; rfl⟩ ?_
    rw [abs_of_nonneg (by positivity), zpow_add₀ (by norm_num), mul_comm ((2 : ℝ) ^ E)]
    exact mul_lt_mul_of_pos_right hm (by positivity)
  refine ⟨fun e => ?_, hF m2 _ hm2, ?_⟩
  · rw [mul_assoc, ← zpow_add₀ (by norm_num)]
    exact hF m1 _ hm1
  · rw [show (m1 : ℝ) * 2 ^ (-k) * ((m2 : ℝ) * 2 ^ (k - p)) = (m1 * m2) * (2 ^ (-k) * 2 ^ (k - p)) by ring,
      ← zpow_add₀ (by norm_num), hm, show -k + (k - p) = -p by ring, add_mul, ← zpow_add₀ (by norm_num)]
    simp [u]

omit [Prec_gt_0 p] in
/-- the operands of Proposition 24 (a) satisfy `H(1)` -/
theorem sharpAB_H : Htheta p n 1 (sharpA p n) ∧ Htheta p n 1 (sharpB p n) := by
  have hu := u_pos p
  refine ⟨fun i hi1 hin => ?_, fun i hi1 hin => ?_⟩
  · simp only [sharpA, one_mul, zero_add, pow_zero]
    by_cases h : i + 2 ≤ n
    · simp [h, show 2 ≤ n by omega, abs_of_pos (pow_pos hu _)]
    · simp only [h, ite_false, abs_zero]
      split_ifs <;> simp [pow_nonneg hu.le]
  · simp only [sharpB, one_mul, show i ≠ 0 by omega, ite_false, ite_true, abs_one, mul_one]
    split_ifs with h
    · rw [h, abs_of_pos (pow_pos hu _)]
    · simp [pow_nonneg hu.le]

omit [Prec_gt_0 p] in
/-- the operand `a` of Proposition 24 (c) satisfies `H(1)` -/
theorem sharpC_H (hp : 1 < p) (a0 : ℝ) : Htheta p n 1 (sharpC p n a0) := by
  have hu := u_pos p
  have hu1 : u p ≤ 1 := by linarith [u_le_half p hp]
  intro i _ hin
  simp only [sharpC, one_mul, Nat.zero_mod, ite_true, pow_zero, mul_one]
  split_ifs
  · rw [abs_mul, abs_of_pos (pow_pos hu _), mul_comm]
  · rw [abs_mul, abs_of_pos (pow_pos hu _), mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hu.le hu1 (by omega)) (abs_nonneg _)
  · simp only [abs_zero]
    exact mul_nonneg (pow_nonneg hu.le _) (abs_nonneg _)

omit [Prec_gt_0 p] in
/-- the coefficients of a bound valid on the sharp inputs: from `wf ≤ CwZ + κwuM` with `1 ≤ Z ≤ 1/(1 - u)`,
`M ≤ gZ`, `g ≥ 1` and `C, κ ≥ 0`, `f(1 - u) ≤ (C + κu)g` -/
theorem coef_lower {w uu f Z M g C κ : ℝ} (hw : 0 < w) (hu1 : uu < 1) (hZ1 : 1 ≤ Z) (hZu : Z * (1 - uu) ≤ 1)
    (hM : M ≤ g * Z) (hg : 1 ≤ g) (hC : 0 ≤ C) (hκ : 0 ≤ κ) (hu0 : 0 ≤ uu)
    (h : w * f ≤ C * w * Z + κ * (w * uu) * M) : f * (1 - uu) ≤ (C + κ * uu) * g := by
  have h1 : C * w * Z + κ * (w * uu) * M ≤ w * ((C + κ * uu) * g * Z) := by
    have e1 : C * w * Z ≤ C * w * (g * Z) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by linarith : (0 : ℝ) ≤ Z) hg) (mul_nonneg hC hw.le)
    have e2 : κ * (w * uu) * M ≤ κ * (w * uu) * (g * Z) := mul_le_mul_of_nonneg_left hM (by positivity)
    nlinarith
  have h2 : f ≤ (C + κ * uu) * g * Z := le_of_mul_le_mul_left (h.trans h1) hw
  have hX : 0 ≤ (C + κ * uu) * g := mul_nonneg (by positivity) (by linarith)
  calc f * (1 - uu) ≤ (C + κ * uu) * g * Z * (1 - uu) := mul_le_mul_of_nonneg_right h2 (by linarith)
    _ = (C + κ * uu) * g * (Z * (1 - uu)) := by ring
    _ ≤ (C + κ * uu) * g * 1 := mul_le_mul_of_nonneg_left hZu hX
    _ = _ := by ring

omit [Prec_gt_0 p] in
/-- `1 ≤ ∑_{i<N} u^i ≤ 1/(1 - u)` -/
theorem geom_u_bounds (hp : 1 < p) {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ ∑ i ∈ range N, u p ^ i ∧ (∑ i ∈ range N, u p ^ i) * (1 - u p) ≤ 1 := by
  have hu := u_pos p
  have hu1 : u p < 1 := by linarith [u_le_half p hp]
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  refine ⟨?_, ?_⟩
  · rw [sum_range_succ']
    simp only [pow_zero]
    linarith [sum_nonneg fun i (_ : i ∈ range k) => pow_nonneg hu.le (i + 1)]
  · have := geom_sum_mul (u p) (k + 1)
    nlinarith [pow_nonneg hu.le (k + 1)]

/-- Proposition 24 (a)'s consequence: a bound `Cu^n|ab| + κu^{n+1}|a_0b_0|`, `C, κ ≥ 0`, valid on its operands has
`C + κu ≥ 1 - u` -/
theorem prop24_mul_coef (hp : 1 < p) (hn : 3 ≤ n) {C κ : ℝ} (hC : 0 ≤ C) (hκ : 0 ≤ κ)
    (h : |(∑ i ∈ range n, ∑ j ∈ range n, sharpA p n i * sharpB p n j) - (mulOp p n (sharpA p n) (sharpB p n)).sum| ≤
      C * u p ^ n * |∑ i ∈ range n, ∑ j ∈ range n, sharpA p n i * sharpB p n j| +
        κ * u p ^ (n + 1) * |sharpA p n 0 * sharpB p n 0|) :
    1 - u p ≤ C + κ * u p := by
  have hu := u_pos p
  have hu1 : u p < 1 := by linarith [u_le_half p hp]
  obtain ⟨h1, -⟩ := prop24_mul p n hp hn
  obtain ⟨hZ1, hZu⟩ := geom_u_bounds p hp (N := 2 * n - 2) (by omega)
  rw [h1, sharpAB_sum p n hn, abs_of_pos (by linarith)] at h
  have h0 : sharpA p n 0 * sharpB p n 0 = 1 := by simp [sharpA, sharpB, show 2 ≤ n by omega]
  rw [h0, abs_one] at h
  have hS : u p ^ n * 1 ≤ ∑ k ∈ Ico n (2 * n - 2), u p ^ k := by
    rw [mul_one]
    exact single_le_sum (f := fun k => u p ^ k) (fun k _ => pow_nonneg hu.le k) (mem_Ico.mpr ⟨le_rfl, by omega⟩)
  have hh := hS.trans h
  rw [pow_succ] at hh
  have := coef_lower (w := u p ^ n) (uu := u p) (f := 1) (Z := ∑ i ∈ range (2 * n - 2), u p ^ i) (M := 1)
    (g := 1) (pow_pos hu n) hu1 hZ1 hZu (by rw [one_mul]; exact hZ1) le_rfl hC hκ hu.le (by linarith)
  linarith

/-- Proposition 24 (c)'s consequence for odd `n`: a bound `Cu^n|ab| + κu^{n+1}|a_0b|`, `C, κ ≥ 0`, valid on its
operands has `C + κu ≥ (1 - u)/(1 + u)` -/
theorem prop24_mulf_odd_coef (hp : 1 < p) (hn : n % 2 = 1) {a0 b : ℝ} (hab : a0 * b = 1 + u p) {C κ : ℝ}
    (hC : 0 ≤ C) (hκ : 0 ≤ κ)
    (h : |∑ i ∈ range n, sharpC p n a0 i * b - (mulfOp p n (sharpC p n a0) b).sum| ≤
      C * u p ^ n * |∑ i ∈ range n, sharpC p n a0 i * b| + κ * u p ^ (n + 1) * |sharpC p n a0 0 * b|) :
    (1 - u p) / (1 + u p) ≤ C + κ * u p := by
  have hu := u_pos p
  have hu1 : u p < 1 := by linarith [u_le_half p hp]
  obtain ⟨h1, h2⟩ := prop24_mulf_odd p n hp hn hab
  have hz : ∑ i ∈ range n, sharpC p n a0 i * b = ∑ i ∈ range (n + 1), u p ^ i := by
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    rw [sum_range_succ, sum_sharpC_mul p _ hab k (by omega), sharpC_mul p _ hab,
      sum_range_succ (fun i => u p ^ i) (2 * k + 1), sum_range_succ (fun i => u p ^ i) (2 * k)]
    simp only [show (2 * k) % 2 = 0 by omega, ite_true]
    ring
  obtain ⟨hZ1, hZu⟩ := geom_u_bounds p hp (N := n + 1) (by omega)
  have h0 : sharpC p n a0 0 * b = 1 + u p := by simp [sharpC, hab]
  rw [h1, hz, abs_of_pos (by linarith), h0, abs_of_pos (by linarith)] at h
  have := coef_lower (pow_pos hu n) hu1 hZ1 hZu
    (show 1 + u p ≤ (1 + u p) * ∑ i ∈ range (n + 1), u p ^ i by nlinarith) (by linarith) hC hκ hu.le
    (show u p ^ n * 1 ≤ _ by rw [mul_one]; exact h.trans (le_of_eq (by ring)))
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- Proposition 24 (c)'s consequence for even `n`: a bound `Cu^n|ab| + κu^{n+1}|a_0b|`, `C, κ ≥ 0`, valid on its
operands has `C + κu ≥ 1 - u` -/
theorem prop24_mulf_even_coef (hp : 1 < p) (hn : n % 2 = 0) (hn2 : 2 ≤ n) {a0 b : ℝ} (hab : a0 * b = 1 + u p)
    {C κ : ℝ} (hC : 0 ≤ C) (hκ : 0 ≤ κ)
    (h : |∑ i ∈ range n, sharpC p n a0 i * b - (mulfOp p n (sharpC p n a0) b).sum| ≤
      C * u p ^ n * |∑ i ∈ range n, sharpC p n a0 i * b| + κ * u p ^ (n + 1) * |sharpC p n a0 0 * b|) :
    1 - u p ≤ C + κ * u p := by
  have hu := u_pos p
  have hu1 : u p < 1 := by linarith [u_le_half p hp]
  obtain ⟨h1, -⟩ := prop24_mulf_even p n hp hn hn2 hab
  have hz : ∑ i ∈ range n, sharpC p n a0 i * b = ∑ i ∈ range (n + 2), u p ^ i := by
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 2 := ⟨n / 2 - 1, by omega⟩
    rw [show 2 * k + 2 = 2 * k + 1 + 1 by ring, sum_range_succ, sum_range_succ, sum_sharpC_mul p _ hab k (by omega),
      sharpC_mul p _ hab, sharpC_mul p _ hab]
    simp only [show (2 * k) % 2 = 0 by omega, show ¬((2 * k + 1) % 2 = 0) by omega, ite_true, ite_false]
    simp only [sum_range_succ]
    ring
  obtain ⟨hZ1, hZu⟩ := geom_u_bounds p hp (N := n + 2) (by omega)
  have h0 : sharpC p n a0 0 * b = 1 + u p := by simp [sharpC, hab]
  rw [h1, hz, abs_of_pos (by linarith), h0, abs_of_pos (by linarith)] at h
  have := coef_lower (pow_pos hu n) hu1 hZ1 hZu
    (show 1 + u p ≤ (1 + u p) * ∑ i ∈ range (n + 2), u p ^ i by nlinarith) (by linarith) hC hκ hu.le
    (show u p ^ n * (1 + u p) ≤ _ by exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring))))
  nlinarith

/-- Proposition 24 (b)'s consequence for ADD: a bound `Cu^n|a + b| + κu^{n+1}(|a_0| + |b_0|)`, `C, κ ≥ 0`, valid on
its operands has `C + κu ≥ (1 - u)/(1 + u^n)` -/
theorem prop24_add_coef (hp : 1 < p) (hn : 2 ≤ n) {C κ : ℝ} (hC : 0 ≤ C) (hκ : 0 ≤ κ)
    (h : |(∑ i ∈ range n, u p ^ i + ∑ i ∈ range n, (if i = 0 then u p ^ n else 0)) -
        (addOp p n (fun i => u p ^ i) (fun i => if i = 0 then u p ^ n else 0)).sum| ≤
      C * u p ^ n * |∑ i ∈ range n, u p ^ i + ∑ i ∈ range n, (if i = 0 then u p ^ n else 0)| +
        κ * u p ^ (n + 1) * (1 + u p ^ n)) :
    (1 - u p) / (1 + u p ^ n) ≤ C + κ * u p := by
  have hu := u_pos p
  have hu1 : u p < 1 := by linarith [u_le_half p hp]
  obtain ⟨h1, -⟩ := prop24_add p hp n hn
  have hz : ∑ i ∈ range n, u p ^ i + ∑ i ∈ range n, (if i = 0 then u p ^ n else 0) = ∑ i ∈ range (n + 1), u p ^ i := by
    rw [sum_ite_eq', sum_range_succ]
    simp [show 0 < n by omega]
  obtain ⟨hZ1, hZu⟩ := geom_u_bounds p hp (N := n + 1) (by omega)
  rw [h1, hz, abs_of_pos (by linarith)] at h
  have hun : 0 < u p ^ n := pow_pos hu n
  rw [pow_succ] at h
  have := coef_lower (w := u p ^ n) (uu := u p) (f := 1) (Z := ∑ i ∈ range (n + 1), u p ^ i) (M := 1 + u p ^ n)
    (g := 1 + u p ^ n) hun hu1 hZ1 hZu (by nlinarith) (by linarith) hC hκ hu.le (by linarith)
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- Proposition 24 (b)'s consequence for ADDF: a bound `Cu^n|a + b| + κu^{n+1}(|a_0| + |b|)`, `C, κ ≥ 0`, valid on
its operands has `C + κu ≥ (1 - u)/(1 + u^n)` -/
theorem prop24_addf_coef (hp : 1 < p) (hn : 1 ≤ n) {C κ : ℝ} (hC : 0 ≤ C) (hκ : 0 ≤ κ)
    (h : |(∑ i ∈ range n, u p ^ i + u p ^ n) - (addfOp p n (fun i => u p ^ i) (u p ^ n)).sum| ≤
      C * u p ^ n * |∑ i ∈ range n, u p ^ i + u p ^ n| + κ * u p ^ (n + 1) * (1 + u p ^ n)) :
    (1 - u p) / (1 + u p ^ n) ≤ C + κ * u p := by
  have hu := u_pos p
  have hu1 : u p < 1 := by linarith [u_le_half p hp]
  obtain ⟨h1, -⟩ := prop24_addf p hp n hn
  have hz : ∑ i ∈ range n, u p ^ i + u p ^ n = ∑ i ∈ range (n + 1), u p ^ i := (sum_range_succ _ n).symm
  obtain ⟨hZ1, hZu⟩ := geom_u_bounds p hp (N := n + 1) (by omega)
  rw [h1, hz, abs_of_pos (by linarith)] at h
  have hun : 0 < u p ^ n := pow_pos hu n
  rw [pow_succ] at h
  have := coef_lower (w := u p ^ n) (uu := u p) (f := 1) (Z := ∑ i ∈ range (n + 1), u p ^ i) (M := 1 + u p ^ n)
    (g := 1 + u p ^ n) hun hu1 hZ1 hZu (by nlinarith) (by linarith) hC hκ hu.le (by linarith)
  rw [div_le_iff₀ (by linarith)]
  linarith

end ExpansionBounds
