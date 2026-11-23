import ExpansionBounds.Div

/-!
# Proposition 24 (d): DIV errs by `u^n|a/b|`

DIV of `a = (1, 0, …, 0)` and `b = (-1, u, 0, …, 0)`, both on `H(1)`, has remainders `r^{(k)} = (u^k, 0, …, 0)` and
quotient terms `q_k = -u^k`: the products `b_0q_k = u^k` and `b_1q_k = -u^{k+1}` are exact, so the levels of the update
are `(0, u^{k+1}, 0, …, 0)` with every error zero, and their renormalization is `(u^{k+1}, 0, …, 0)`. `Ren_n` commutes
with negation, so by Theorem 9 (c) the result is `-(1, u, …, u^{n-1})`, and as `a/b = -1/(1 - u)` the error is
`u^n/(1 - u) = u^n|a/b|`.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) (n : ℕ)

variable [Prec_gt_0 p]

/-- `TwoSum(-a, -b) = -TwoSum(a, b)`, as `RN` is symmetric -/
theorem twoSum_neg (a b : ℝ) : twoSum p (-a) (-b) = (-(twoSum p a b).1, -(twoSum p a b).2) := by
  set s := RN p (a + b) with hs
  set b' := RN p (s - a) with hb'
  have h1 : RN p (-a + -b) = -s := by rw [← neg_add, RN_neg]
  have h2 : RN p (-s - -a) = -b' := by rw [show -s - -a = -(s - a) by ring, RN_neg]
  have h3 : RN p (-s - -b') = -RN p (s - b') := by rw [show -s - -b' = -(s - b') by ring, RN_neg]
  have h4 : RN p (-a - -RN p (s - b')) = -RN p (a - RN p (s - b')) := by
    rw [show -a - -RN p (s - b') = -(a - RN p (s - b')) by ring, RN_neg]
  have h5 : RN p (-b - -b') = -RN p (b - b') := by rw [show -b - -b' = -(b - b') by ring, RN_neg]
  have h6 : RN p (-RN p (a - RN p (s - b')) + -RN p (b - b')) =
      -RN p (RN p (a - RN p (s - b')) + RN p (b - b')) := by rw [← neg_add, RN_neg]
  show (RN p (-a + -b), RN p (RN p (-a - RN p (RN p (-a + -b) - RN p (RN p (-a + -b) - -a))) +
    RN p (-b - RN p (RN p (-a + -b) - -a)))) = _
  rw [h1, h2, h3, h4, h5, h6]
  rfl

theorem vecSum_neg : ∀ (m : ℕ) (c : ℕ → ℝ) (j : ℕ), vecSum p m (fun i => -c i) j = -vecSum p m c j
  | 0, c, j => by simp only [vecSum_zero]; split_ifs <;> simp
  | m + 1, c, j => by
    have ih := vecSum_neg m (fun i => c (i + 1))
    rcases j with _ | _ | j
    · rw [vecSum_succ_zero, vecSum_succ_zero, ih 0, twoSum_neg]
    · rw [vecSum_succ_one, vecSum_succ_one, ih 0, twoSum_neg]
    · rw [vecSum_succ_add_two, vecSum_succ_add_two, ih]

theorem renPass_neg : ∀ (vs : List ℝ) (b : ℕ) (acc : ℝ),
    renPass p b (-acc) (vs.map fun v => -v) = (renPass p b acc vs).map fun v => -v
  | [], _, _ => rfl
  | v :: vs, b, acc => by
    simp only [List.map_cons, renPass, twoSum_neg, ne_eq, neg_eq_zero]
    split_ifs
    · rw [List.map_cons, renPass_neg vs]
    · exact renPass_neg vs b _

omit [Prec_gt_0 p] in
theorem list_sum_map_neg (l : List ℝ) : (l.map fun v => -v).sum = -l.sum := by
  induction l with
  | nil => simp
  | cons v l ih => rw [List.map_cons, List.sum_cons, List.sum_cons, ih]; ring

/-- `Ren_n` commutes with negation -/
theorem ren_neg (m : ℕ) (c : ℕ → ℝ) : ren p n m (fun i => -c i) = (ren p n m c).map fun v => -v := by
  unfold ren
  rw [vecSum_neg, ← renPass_neg]
  congr 1
  rw [List.map_map]
  exact List.map_congr_left fun j _ => vecSum_neg p m c (j + 1)

/-- `Ren_n` of `(0, y, 0, …, 0)` is `(y)` -/
theorem ren_single (hp : 1 < p) (hn : 1 ≤ n) {y : ℝ} (hy : F p y) :
    ren p n n (fun j => if j = 1 then y else 0) = [y] := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set c : ℕ → ℝ := fun j => if j = 1 then y else 0 with hc
  have hc' : ∀ i ≤ m, F p (c (i + 1)) := fun i _ => by
    simp only [hc]; split_ifs
    · exact hy
    · exact F_zero p
  have hz : ∀ j, 0 < j → vecSum p m (fun i => c (i + 1)) j = 0 := fun j hj =>
    vecSum_zero_above p m _ 0 hc' (fun i hi _ => by simp [hc, show i ≠ 0 by omega]) j hj
  have h0 : vecSum p m (fun i => c (i + 1)) 0 = y := by
    have hs := vecSum_sum p hp m _ hc'
    rw [sum_range_succ', sum_eq_zero fun j _ => hz (j + 1) (by omega), zero_add, sum_range_succ',
      sum_eq_zero fun j _ => by simp [hc]] at hs
    simpa [hc] using hs
  have hts : twoSum p (c 0) (vecSum p m (fun i => c (i + 1)) 0) = (y, 0) := by
    rw [h0, show c 0 = 0 by simp [hc]]
    exact twoSum_zero_left p hp hy
  unfold ren
  have hl : (List.range (m + 1)).map (fun j => vecSum p (m + 1) c (j + 1)) = List.replicate (m + 1) 0 := by
    refine List.eq_replicate_iff.mpr ⟨by simp, fun v hv => ?_⟩
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hv
    rcases j with _ | j
    · rw [vecSum_succ_one, hts]
    · rw [vecSum_succ_add_two]
      exact hz _ (by omega)
  rw [hl, vecSum_succ_zero, hts]
  exact renPass_zeros p (m + 1) _ y hy

omit [Prec_gt_0 p] in
/-- the operand `a = (1, 0, …, 0)` of Proposition 24 (d) -/
noncomputable def sharpDa (i : ℕ) : ℝ := if i = 0 then 1 else 0

omit [Prec_gt_0 p] in
/-- the operand `b = (-1, u, 0, …, 0)` of Proposition 24 (d) -/
noncomputable def sharpDb (i : ℕ) : ℝ := if i = 0 then -1 else if i = 1 then u p else 0

/-- one update on `r = (u^k, 0, …, 0)` with `q = -u^k`: the levels are `(0, u^{k+1}, 0, …, 0)` -/
theorem smf_sharp_levels (hp : 1 < p) (hn : 2 ≤ n) (k : ℕ) :
    smfLevels p n (fun i => if i = 0 then u p ^ k else 0) (sharpDb p) (-(u p ^ k)) =
      fun j => if j = 1 then u p ^ (k + 1) else 0 := by
  set r : ℕ → ℝ := fun i => if i = 0 then u p ^ k else 0 with hr
  set q : ℝ := -(u p ^ k) with hq
  have hFu := F_u_pow p
  have htp : ∀ i, twoProd p (sharpDb p i) q =
      (if i = 0 then u p ^ k else if i = 1 then -(u p ^ (k + 1)) else 0, 0) := by
    intro i
    rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi
    · have h : sharpDb p 0 * q = u p ^ k := by simp [sharpDb, hq]
      rw [twoProd_exact p (by rw [h]; exact hFu k), h]
      simp
    · have h : sharpDb p 1 * q = -(u p ^ (k + 1)) := by simp [sharpDb, hq]; ring
      rw [twoProd_exact p (by rw [h]; exact F_neg p (hFu _)), h]
      simp
    · simp only [sharpDb, show i ≠ 0 by omega, show i ≠ 1 by omega, ite_false]
      exact twoProd_zero_left p q
  have hst : ∀ i, smfST p r (sharpDb p) q i = (if i = 1 then u p ^ (k + 1) else 0, 0) := by
    intro i
    simp only [smfST, htp]
    rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi
    · simp only [hr, ite_true]
      have h1 := facts_a p hp (hFu k) (F_neg p (hFu k))
      have hs : (twoSum p (u p ^ k) (-(u p ^ k))).1 = 0 := by
        show RN p (u p ^ k + -(u p ^ k)) = 0
        rw [add_neg_cancel, RN_zero]
      rw [hs, add_neg_cancel, zero_add] at h1
      exact Prod.ext hs h1.1
    · simp only [hr, one_ne_zero, ite_false, ite_true, neg_neg]
      exact twoSum_zero_left p hp (hFu _)
    · simp only [hr, show i ≠ 0 by omega, show i ≠ 1 by omega, ite_false, neg_zero]
      exact twoSum_zero p (F_zero p)
  set s1 : ℕ → ℝ := fun j => if j = 1 then u p ^ (k + 1) else 0 with hs1
  have hs1F : ∀ j, F p (s1 j) := fun j => by
    simp only [hs1]; split_ifs
    · exact hFu _
    · exact F_zero p
  have hA : runS p n ((List.range n).map fun i => LOp.assign i (smfST p r (sharpDb p) q i).1) 0 = s1 := by
    rw [runS_assigns]
    funext j
    simp only [hst, hs1]
    by_cases hj : j < n
    · simp [hj]
    · simp [hj, show j ≠ 1 by omega]
  have hB : runS p n [LOp.assign n (smfST p r (sharpDb p) q (n - 1)).2,
      LOp.round (-(twoProd p (sharpDb p (n - 1)) q).2)] s1 = s1 := by
    show Function.update (Function.update s1 n (smfST p r (sharpDb p) q (n - 1)).2) n
      (RN p (Function.update s1 n (smfST p r (sharpDb p) q (n - 1)).2 n + -(twoProd p (sharpDb p (n - 1)) q).2)) = s1
    rw [hst, htp]
    simp only [Function.update_self, add_zero, neg_zero, RN_zero, Function.update_idem]
    exact Function.update_eq_self_iff.mpr (by simp [hs1, show n ≠ 1 by omega])
  unfold smfLevels
  rw [runOps_s, smfOps, runS_append, runS_append]
  show runS p n _ (runS p n _ (runS p n _ 0)) = s1
  rw [hA, hB]
  refine runS_zero p n _ (fun o ho => ?_) s1 hs1F
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff, or_false] at ho
  obtain ⟨l, -, rfl | rfl⟩ := ho
  · exact Or.inl ⟨l + 1, by rw [hst]⟩
  · exact Or.inl ⟨l + 1, by rw [htp, neg_zero]⟩

/-- DIV's remainders on the operands of Proposition 24 (d) are `r^{(k)} = (u^k, 0, …, 0)` -/
theorem divRem_sharp (hp : 1 < p) (hn : 2 ≤ n) :
    ∀ k, divRem p n sharpDa (sharpDb p) k = fun i => if i = 0 then u p ^ k else 0
  | 0 => by funext i; simp [divRem, sharpDa]
  | k + 1 => by
    have ih := divRem_sharp hp hn k
    have hq : RN p (divRem p n sharpDa (sharpDb p) k 0 / sharpDb p 0) = -(u p ^ k) := by
      rw [ih]
      simp only [ite_true, sharpDb, div_neg, div_one]
      rw [RN_neg, RN_of_F p (F_u_pow p k)]
    funext i
    show (smfOp p n (divRem p n sharpDa (sharpDb p) k) (sharpDb p)
      (RN p (divRem p n sharpDa (sharpDb p) k 0 / sharpDb p 0))).getD i 0 = _
    rw [hq, smfOp, ih, smf_sharp_levels p n hp hn k, ren_single p n hp (by omega) (F_u_pow p _)]
    rcases i with _ | i <;> simp

omit [Prec_gt_0 p] in
/-- the operands of Proposition 24 (d) satisfy `H(1)` -/
theorem sharpD_H : Htheta p n 1 sharpDa ∧ Htheta p n 1 (sharpDb p) := by
  have hu := u_pos p
  refine ⟨fun i hi _ => by simp only [sharpDa, show i ≠ 0 by omega, ite_false, abs_zero]; positivity,
    fun i hi _ => ?_⟩
  simp only [sharpDb, show i ≠ 0 by omega, ite_false, ite_true, abs_neg, abs_one, mul_one, one_mul]
  split_ifs with h
  · subst h; simp [abs_of_pos hu]
  · simp [pow_nonneg hu.le]

/-- Proposition 24 (d): DIV of `a = (1, 0, …, 0)` and `b = (-1, u, 0, …, 0)` errs by exactly `u^n|a/b|` -/
theorem prop24_div (hp : 1 < p) (hn : 2 ≤ n) :
    |(∑ i ∈ range n, sharpDa i) / (∑ i ∈ range n, sharpDb p i) - (divOp p n sharpDa (sharpDb p)).sum| =
      u p ^ n * |(∑ i ∈ range n, sharpDa i) / ∑ i ∈ range n, sharpDb p i| := by
  have hu := u_pos p
  have hu1 : u p < 1 := by linarith [u_le_half p hp]
  have hq : divQ p n sharpDa (sharpDb p) = fun k => -(u p ^ k) := by
    funext k
    rw [divQ, divRem_sharp p n hp hn k]
    simp only [ite_true, sharpDb, div_neg, div_one]
    rw [RN_neg, RN_of_F p (F_u_pow p k)]
  have hx : (divOp p n sharpDa (sharpDb p)).sum = -∑ i ∈ range n, u p ^ i := by
    rw [divOp, hq, ren_neg, list_sum_map_neg, ren_pow_sum p n hp (by omega)]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have ha : ∑ i ∈ range (m + 2), sharpDa i = 1 := by simp [sharpDa]
  have hb : ∑ i ∈ range (m + 2), sharpDb p i = u p - 1 := by
    rw [sum_range_succ', sum_range_succ', sum_eq_zero fun i _ => by simp [sharpDb]]
    simp [sharpDb]
    ring
  have h1 : u p - 1 ≠ 0 := by linarith
  rw [hx, ha, hb, geom_sum_eq hu1.ne]
  rw [show 1 / (u p - 1) - -((u p ^ (m + 2) - 1) / (u p - 1)) = u p ^ (m + 2) / (u p - 1) by field_simp; ring,
    abs_div, abs_div, abs_of_pos (pow_pos hu _), abs_one]
  ring

end ExpansionBounds
