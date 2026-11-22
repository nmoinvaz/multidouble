import ExpansionBounds.Ops

/-!
# Lemma 13 for MUL

MUL as a program of Lemma 11, in the appendix's order: (1) `(s_j, e_{0j}) ← TwoProd(a_0, b_j)` for `j < n`;
(2) `s_n ← RN(a_i b_{n-i} + s_n)` for `i = 1, …, n - 1`; (3) `dep(s, l, e_{0,l-1})` for `l = 1, …, n`; (4) for
`i = 1, …, n - 1` and `j = 0, …, n - 1 - i`, `(p_{ij}, e_{ij}) ← TwoProd(a_i, b_j)`, `dep(s, i + j, p_{ij})` and
`dep(s, i + j + 1, e_{ij})`. It has `T_m = m(m + 1)` `TwoSum`s at level `m < n` and `Q = n² + n - 1` roundings.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) (n : ℕ)

/-- step (4) of MUL, indexed by `i - 1` -/
noncomputable def mulStep4 (a b : ℕ → ℝ) : List LOp :=
  (List.range (n - 1)).flatMap fun i => (List.range (n - 1 - i)).flatMap fun j =>
    [LOp.dep (i + 1 + j) (twoProd p (a (i + 1)) (b j)).1, LOp.dep (i + 1 + j + 1) (twoProd p (a (i + 1)) (b j)).2]

/-- MUL's program -/
noncomputable def mulOps (a b : ℕ → ℝ) : List LOp :=
  ((List.range n).map fun j => LOp.assign j (twoProd p (a 0) (b j)).1) ++
    ((List.range (n - 1)).map fun i => LOp.round (a (i + 1) * b (n - (i + 1)))) ++
    ((List.range n).map fun l => LOp.dep (l + 1) (twoProd p (a 0) (b l)).2) ++
    mulStep4 p n a b

theorem list_sum_map_range_gen {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ((List.range m).map f).sum = ∑ j ∈ range m, f j := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

theorem list_sum_flatMap {α : Type*} {M : Type*} [AddCommMonoid M] (l : List α) (f : α → List LOp)
    (g : LOp → M) : ((l.flatMap f).map g).sum = (l.map fun x => ((f x).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [List.flatMap_cons, ih]

/-- `∑_{i < N} ∑_{j < N - i} f(i + j) = ∑_{k < N} (k + 1) f(k)` -/
theorem sum_tri (f : ℕ → ℕ) (N : ℕ) :
    ∑ i ∈ range N, ∑ j ∈ range (N - i), f (i + j) = ∑ k ∈ range N, (k + 1) * f k := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h : ∀ i ∈ range N, ∑ j ∈ range (N + 1 - i), f (i + j) = ∑ j ∈ range (N - i), f (i + j) + f N := by
      intro i hi
      rw [mem_range] at hi
      rw [show N + 1 - i = N - i + 1 by omega, sum_range_succ, show i + (N - i) = N by omega]
    rw [sum_range_succ, sum_congr rfl h, sum_add_distrib, ih, sum_range_succ (fun k => (k + 1) * f k)]
    simp
    ring

/-- `∑_{k < m} (k + 1) + ∑_{k < m - 1} (k + 1) = m²` -/
theorem sum_succ_pair (m : ℕ) : ∑ k ∈ range m, (k + 1) + ∑ k ∈ range (m - 1), (k + 1) = m * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [sum_range_succ _ m'] at *
      simp only [Nat.add_sub_cancel] at ih
      nlinarith [ih]

/-- MUL's counts: `T_m = m(m + 1)` at level `m < n` and `Q = n² + n - 1` -/
theorem mulOps_counts (hn : 1 ≤ n) (a b : ℕ → ℝ) :
    (∀ m < n, opsT (mulOps p n a b) m = m * (m + 1)) ∧ opsQ (mulOps p n a b) = n ^ 2 + n - 1 := by
  have h4T : ∀ m < n, opsT (mulStep4 p n a b) m = ∑ k ∈ range m, (k + 1) + ∑ k ∈ range (m - 1), (k + 1) := by
    intro m hm
    simp only [opsT, mulStep4, list_sum_flatMap, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, opT, list_sum_map_range_gen]
    have : ∀ i ∈ range (n - 1), ∑ j ∈ range (n - 1 - i),
        ((if i + 1 + j ≤ m then 1 else 0) + (if i + 1 + j + 1 ≤ m then 1 else 0)) =
        ∑ j ∈ range (n - 1 - i), (fun k => (if k + 1 ≤ m then 1 else 0) + (if k + 2 ≤ m then 1 else 0)) (i + j) :=
      fun i _ => sum_congr rfl fun j _ => by simp only [show i + 1 + j = i + j + 1 by ring]
    rw [sum_congr rfl this]
    refine (sum_tri (fun k => (if k + 1 ≤ m then 1 else 0) + (if k + 2 ≤ m then 1 else 0)) (n - 1)).trans ?_
    simp only [mul_add, sum_add_distrib, mul_ite, mul_one, mul_zero]
    rw [← sum_filter, ← sum_filter]
    congr 1
    · rw [show (range (n - 1)).filter (fun k => k + 1 ≤ m) = range m by ext k; simp; omega]
      exact sum_add_distrib
    · rw [show (range (n - 1)).filter (fun k => k + 2 ≤ m) = range (m - 1) by ext k; simp; omega]
      exact sum_add_distrib
  have h4Q : opsQ (mulStep4 p n a b) = (n - 1) * n := by
    simp only [opsQ, mulStep4, list_sum_flatMap, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, opQ, list_sum_map_range_gen]
    have : ∀ i ∈ range (n - 1), ∑ j ∈ range (n - 1 - i), (1 + 1) = ∑ j ∈ range (n - 1 - i), (fun _ => 2) (i + j) :=
      fun i _ => rfl
    rw [sum_congr rfl this]
    refine (sum_tri (fun _ => 2) (n - 1)).trans ?_
    rw [← sum_mul]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have h := sum_range_id_mul_two (n' + 1)
    rw [sum_range_succ'] at h
    simp only [Nat.add_sub_cancel, add_zero] at h ⊢
    rw [h]
    ring
  refine ⟨fun m hm => ?_, ?_⟩
  · have h1 : opsT (mulOps p n a b) m = opsT (mulStep4 p n a b) m + min n m := by
      simp only [opsT, mulOps, List.map_append, List.sum_append, List.map_map, Function.comp_def, opT]
      rw [count_le]
      simp
      ring
    rw [h1, h4T m hm, sum_succ_pair, min_eq_right hm.le]
    ring
  · have h1 : opsQ (mulOps p n a b) = (n - 1) + n + opsQ (mulStep4 p n a b) := by
      simp only [opsQ, mulOps, List.map_append, List.sum_append, List.map_map, Function.comp_def, opQ]
      simp
    rw [h1, h4Q]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [show (n' + 1) ^ 2 + (n' + 1) - 1 = (n' + 1) ^ 2 + n' by
      rw [show (n' + 1) ^ 2 + (n' + 1) = (n' + 1) ^ 2 + n' + 1 by ring, Nat.add_sub_cancel]]
    ring

/-- `P_m = ∑_{i+j=m} α_i β_j` over `0 ≤ i, j < n` -/
noncomputable def mulP (α β : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ range n, ∑ j ∈ range n, if i + j = m then α i * β j else 0

/-- the row `i = 0` of `P_K` -/
noncomputable def mulP0 (α β : ℕ → ℝ) (K : ℕ) : ℝ := ∑ j ∈ range n, if j = K then α 0 * β j else 0

/-- the rows `i ≥ 1` of `P_K` with `i + j ≤ n - 1`, those of step (4) -/
noncomputable def mulP4 (α β : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ i ∈ range (n - 1), ∑ j ∈ range (n - 1 - i), if i + 1 + j = K then α (i + 1) * β j else 0

/-- `P_K = P0_K + P4_K` for `K < n` -/
theorem mulP_split (hn : 1 ≤ n) (α β : ℕ → ℝ) (K : ℕ) (hK : K < n) :
    mulP n α β K = mulP0 n α β K + mulP4 n α β K := by
  unfold mulP mulP0 mulP4
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [sum_range_succ', add_comm]
  simp only [Nat.add_sub_cancel, zero_add]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  symm
  refine sum_subset (range_subset_range.mpr (by omega)) fun j hj hj' => ?_
  simp only [mem_range, not_lt] at hj hj'
  simp only [show i + 1 + j ≠ K by omega, ite_false]

/-- `P_n = ∑_{i=1}^{n-1} α_i β_{n-i}`, the products of step (2) -/
theorem mulP_top (hn : 1 ≤ n) (α β : ℕ → ℝ) :
    mulP n α β n = ∑ i ∈ range (n - 1), α (i + 1) * β (n - (i + 1)) := by
  unfold mulP
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [sum_range_succ', add_comm]
  simp only [Nat.add_sub_cancel, zero_add]
  have h0 : (∑ j ∈ range (n' + 1), if j = n' + 1 then α 0 * β j else 0) = 0 :=
    sum_eq_zero fun j hj => by simp only [mem_range] at hj; simp only [show j ≠ n' + 1 by omega, ite_false]
  rw [h0, zero_add]
  refine sum_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  rw [show n' + 1 - (i + 1) = n' - i by omega]
  have : ∀ j ∈ range (n' + 1), (if i + 1 + j = n' + 1 then α (i + 1) * β j else 0) =
      if j = n' - i then α (i + 1) * β j else 0 := fun j _ => by
    by_cases hj : j = n' - i
    · simp only [hj, show i + 1 + (n' - i) = n' + 1 by omega, ite_true]
    · simp only [hj, show i + 1 + j ≠ n' + 1 by omega, ite_false]
  rw [sum_congr rfl this, sum_ite_eq']
  simp only [mem_range, show n' - i < n' + 1 by omega, ite_true]

/-- `A_m = (1 + u)P_m + uP_{m-1}` for `m < n` and `A_n = P_n + uP_{n-1}`, with `P_{-1} = 0` -/
noncomputable def mulA (α β : ℕ → ℝ) (m : ℕ) : ℝ :=
  if m < n then (1 + u p) * mulP n α β m + (if m = 0 then 0 else u p * mulP n α β (m - 1))
  else if m = n then mulP n α β n + u p * mulP n α β (n - 1) else 0

variable [Prec_gt_0 p]

/-- MUL's levels receive at most `A_m` -/
theorem mulOps_A (hn : 1 ≤ n) (a b α β : ℕ → ℝ) (ha : ∀ i < n, F p (a i)) (hb : ∀ j < n, F p (b j))
    (hα : ∀ i < n, |a i| ≤ α i) (hβ : ∀ j < n, |b j| ≤ β j) (m : ℕ) :
    opsA n (mulOps p n a b) m ≤ mulA p n α β m := by
  have hu := u_pos p
  have hab : ∀ i < n, ∀ j < n, |a i * b j| ≤ α i * β j := fun i hi j hj => by
    rw [abs_mul]
    exact mul_le_mul (hα i hi) (hβ j hj) (abs_nonneg _) ((abs_nonneg _).trans (hα i hi))
  have hq : ∀ i < n, ∀ j < n, |(twoProd p (a i) (b j)).1| ≤ (1 + u p) * (α i * β j) := fun i hi j hj =>
    (facts_c p (ha i hi) (hb j hj)).2.2.trans (mul_le_mul_of_nonneg_left (hab i hi j hj) (by linarith))
  have he : ∀ i < n, ∀ j < n, |(twoProd p (a i) (b j)).2| ≤ u p * (α i * β j) := fun i hi j hj =>
    (facts_c p (ha i hi) (hb j hj)).2.1.trans ((mul_le_mul_of_nonneg_right (us_le_u p) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hab i hi j hj) hu.le))
  have hexp : opsA n (mulOps p n a b) m =
      (∑ j ∈ range n, if j = m then |(twoProd p (a 0) (b j)).1| else 0) +
        (∑ i ∈ range (n - 1), if m = n then |a (i + 1) * b (n - (i + 1))| else 0) +
        (∑ l ∈ range n, if l + 1 = m then |(twoProd p (a 0) (b l)).2| else 0) +
        ∑ i ∈ range (n - 1), ∑ j ∈ range (n - 1 - i),
          ((if i + 1 + j = m then |(twoProd p (a (i + 1)) (b j)).1| else 0) +
            (if i + 1 + j + 1 = m then |(twoProd p (a (i + 1)) (b j)).2| else 0)) := by
    simp only [opsA, mulOps, mulStep4, List.map_append, List.sum_append, List.map_map, Function.comp_def,
      list_sum_flatMap, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, opA,
      list_sum_map_range_gen]
  have hbound : opsA n (mulOps p n a b) m ≤ (1 + u p) * (mulP0 n α β m + mulP4 n α β m) +
      (if m = n then ∑ i ∈ range (n - 1), α (i + 1) * β (n - (i + 1)) else 0) +
      u p * ((∑ l ∈ range n, if l + 1 = m then α 0 * β l else 0) +
        ∑ i ∈ range (n - 1), ∑ j ∈ range (n - 1 - i), if i + 1 + j + 1 = m then α (i + 1) * β j else 0) := by
    rw [hexp]
    have b1 : (∑ j ∈ range n, if j = m then |(twoProd p (a 0) (b j)).1| else 0) ≤ (1 + u p) * mulP0 n α β m := by
      rw [mulP0, mul_sum]
      refine sum_le_sum fun j hj => ?_
      split_ifs
      · exact hq 0 (by omega) j (mem_range.mp hj)
      · simp
    have b2 : (∑ i ∈ range (n - 1), if m = n then |a (i + 1) * b (n - (i + 1))| else 0) ≤
        if m = n then ∑ i ∈ range (n - 1), α (i + 1) * β (n - (i + 1)) else 0 := by
      split_ifs
      · exact sum_le_sum fun i hi => hab (i + 1) (by simp at hi; omega) _ (by simp at hi; omega)
      · simp
    have b3 : (∑ l ∈ range n, if l + 1 = m then |(twoProd p (a 0) (b l)).2| else 0) ≤
        u p * ∑ l ∈ range n, if l + 1 = m then α 0 * β l else 0 := by
      rw [mul_sum]
      refine sum_le_sum fun l hl => ?_
      split_ifs
      · exact he 0 (by omega) l (mem_range.mp hl)
      · simp
    have b4 : ∑ i ∈ range (n - 1), ∑ j ∈ range (n - 1 - i),
        ((if i + 1 + j = m then |(twoProd p (a (i + 1)) (b j)).1| else 0) +
          (if i + 1 + j + 1 = m then |(twoProd p (a (i + 1)) (b j)).2| else 0)) ≤
        (1 + u p) * mulP4 n α β m + u p *
          ∑ i ∈ range (n - 1), ∑ j ∈ range (n - 1 - i), if i + 1 + j + 1 = m then α (i + 1) * β j else 0 := by
      rw [mulP4, mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_le_sum fun i hi => ?_
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_le_sum fun j hj => ?_
      simp only [mem_range] at hi hj
      have hi' : i + 1 < n := by omega
      have hj' : j < n := by omega
      refine add_le_add ?_ ?_ <;> split_ifs
      · exact hq _ hi' _ hj'
      · simp
      · exact he _ hi' _ hj'
      · simp
    nlinarith [b1, b2, b3, b4]
  refine hbound.trans (le_of_eq ?_)
  -- the error terms are the slices of `P_{m-1}`
  have hE : ∀ K, (∑ l ∈ range n, if l + 1 = K + 1 then α 0 * β l else 0) +
      (∑ i ∈ range (n - 1), ∑ j ∈ range (n - 1 - i), if i + 1 + j + 1 = K + 1 then α (i + 1) * β j else 0) =
      mulP0 n α β K + mulP4 n α β K := fun K => by simp only [mulP0, mulP4, Nat.add_right_cancel_iff]
  have hz4 : ∀ K, n - 1 < K → mulP4 n α β K = 0 := fun K hK => sum_eq_zero fun i hi => sum_eq_zero fun j hj => by
    simp only [mem_range] at hi hj
    simp only [show i + 1 + j ≠ K by omega, ite_false]
  have hz0 : ∀ K, n ≤ K → mulP0 n α β K = 0 := fun K hK => sum_eq_zero fun j hj => by
    simp only [mem_range] at hj
    simp only [show j ≠ K by omega, ite_false]
  have hzE : ∀ K, (K = 0 ∨ n < K) → (∑ l ∈ range n, if l + 1 = K then α 0 * β l else 0) +
      (∑ i ∈ range (n - 1), ∑ j ∈ range (n - 1 - i), if i + 1 + j + 1 = K then α (i + 1) * β j else 0) = 0 := by
    intro K hK
    rw [sum_eq_zero fun l hl => by simp only [mem_range] at hl; simp only [show l + 1 ≠ K by omega, ite_false],
      sum_eq_zero fun i hi => sum_eq_zero fun j hj => by
        simp only [mem_range] at hi hj
        simp only [show i + 1 + j + 1 ≠ K by omega, ite_false]]
    simp
  unfold mulA
  rcases Nat.lt_trichotomy m n with hlt | rfl | hgt
  · simp only [hlt, ite_true, show m ≠ n by omega, ite_false, add_zero]
    rw [mulP_split n hn α β m hlt]
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · rw [hzE 0 (Or.inl rfl)]
      simp
    · obtain ⟨K, rfl⟩ : ∃ K, m = K + 1 := ⟨m - 1, by omega⟩
      rw [hE K, Nat.add_sub_cancel, mulP_split n hn α β K (by omega)]
      simp
  · simp only [lt_irrefl, ite_false, ite_true]
    rw [hz0 m le_rfl, hz4 m (by omega), mulP_top m hn]
    obtain ⟨K, hK⟩ : ∃ K, m = K + 1 := ⟨m - 1, by omega⟩
    have h := hE K
    rw [← hK] at h
    rw [h, show m - 1 = K by omega, mulP_split m hn α β K (by omega)]
    ring
  · simp only [show ¬m < n by omega, show m ≠ n by omega, ite_false]
    rw [hz0 m (by omega), hz4 m (by omega), hzE m (Or.inr hgt)]
    ring

/-- `∑_{i,j<n, i+j ≤ n} a_i b_j` is the row `i = 0`, the rows `i ≥ 1` with `i + j ≤ n - 1` and the products of order
`n` -/
theorem sum_le_n_split (hn : 1 ≤ n) (g : ℕ → ℕ → ℝ) :
    (∑ i ∈ range n, ∑ j ∈ range n, if i + j ≤ n then g i j else 0) =
      (∑ j ∈ range n, g 0 j) + ∑ i ∈ range (n - 1), g (i + 1) (n - (i + 1)) +
        ∑ i ∈ range (n - 1), ∑ j ∈ range (n - 1 - i), g (i + 1) j := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [sum_range_succ']
  simp only [Nat.add_sub_cancel, zero_add]
  have h0 : (∑ j ∈ range (n' + 1), if j ≤ n' + 1 then g 0 j else 0) = ∑ j ∈ range (n' + 1), g 0 j :=
    sum_congr rfl fun j hj => by simp only [mem_range] at hj; simp only [show j ≤ n' + 1 by omega, ite_true]
  have hrow : ∀ i ∈ range n', (∑ j ∈ range (n' + 1), if i + 1 + j ≤ n' + 1 then g (i + 1) j else 0) =
      ∑ j ∈ range (n' - i), g (i + 1) j + g (i + 1) (n' - i) := by
    intro i hi
    rw [mem_range] at hi
    rw [← sum_range_succ, show n' - i + 1 = n' + 1 - i by omega]
    symm
    rw [← sum_filter]
    congr 1
    ext j
    simp only [mem_range, mem_filter]
    omega
  rw [h0, sum_congr rfl hrow, sum_add_distrib]
  simp only [Nat.add_sub_add_right]
  ring

/-- `Δ = ∑_{m > n} P_m`, as the products the program drops -/
noncomputable def mulDelta (α β : ℕ → ℝ) : ℝ := ∑ i ∈ range n, ∑ j ∈ range n, if n < i + j then α i * β j else 0

theorem mulDelta_eq (α β : ℕ → ℝ) : mulDelta n α β = ∑ m ∈ Ico (n + 1) (2 * n), mulP n α β m := by
  unfold mulDelta mulP
  symm
  rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  simp only [mem_range] at hi hj
  rw [sum_ite_eq]
  simp only [mem_Ico]
  by_cases h : n < i + j
  · simp only [h, ite_true, show n + 1 ≤ i + j ∧ i + j < 2 * n by omega, and_self]
  · simp only [h, ite_false, show ¬(n + 1 ≤ i + j ∧ i + j < 2 * n) by omega]

/-- MUL's program puts in `∑_{i+j ≤ n} a_i b_j` -/
theorem mulOps_Y (hn : 1 ≤ n) (a b : ℕ → ℝ) (ha : ∀ i < n, F p (a i)) (hb : ∀ j < n, F p (b j)) :
    opsY (mulOps p n a b) = ∑ i ∈ range n, ∑ j ∈ range n, if i + j ≤ n then a i * b j else 0 := by
  rw [sum_le_n_split n hn (fun i j => a i * b j)]
  simp only [opsY, mulOps, mulStep4, List.map_append, List.sum_append, List.map_map, Function.comp_def,
    list_sum_flatMap, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, opY,
    list_sum_map_range_gen]
  have h1 : ∀ j ∈ range n, (twoProd p (a 0) (b j)).1 + (twoProd p (a 0) (b j)).2 = a 0 * b j := fun j hj =>
    (facts_c p (ha 0 (by omega)) (hb j (mem_range.mp hj))).1
  have h4 : ∀ i ∈ range (n - 1), ∑ j ∈ range (n - 1 - i),
      ((twoProd p (a (i + 1)) (b j)).1 + (twoProd p (a (i + 1)) (b j)).2) = ∑ j ∈ range (n - 1 - i), a (i + 1) * b j :=
    fun i hi => sum_congr rfl fun j hj => by
      simp only [mem_range] at hi hj
      exact (facts_c p (ha (i + 1) (by omega)) (hb j (by omega))).1
  rw [← sum_congr rfl h1, ← sum_congr rfl h4, sum_add_distrib]
  ring

omit [Prec_gt_0 p] in
theorem runOps_ok_noassign (ops : List LOp) (h : ∀ o ∈ ops, ∀ m y, o ≠ LOp.assign m y) :
    ∀ st : LState, (runOps p n ops st).2.ok = st.ok := by
  induction ops with
  | nil => intro st; rfl
  | cons o os ih =>
    intro st
    simp only [runOps]
    rw [ih (fun o' ho' => h o' (by simp [ho'])) _]
    cases o with
    | assign m y => exact absurd rfl (h _ (by simp) m y)
    | dep l t => exact depRun_ok p n _ _ _ _
    | round y => rfl

/-- `T_m = m(m + 1)` -/
def mulT (m : ℕ) : ℕ := m * (m + 1)

/-- MUL's level bounds: `X_m` of Lemma 11 with its `A_m`, `T_m = m(m + 1)` and `Q = n² + n - 1` -/
noncomputable def mulX (α β : ℕ → ℝ) (m : ℕ) : ℝ :=
  if m < n then levX (mulA p n α β) mulT (u p) m
  else levD (mulA p n α β) mulT (u p) n / (1 - ((n ^ 2 + n - 1 : ℕ) : ℝ) * u p)

/-- `R = Q u X_n` for MUL -/
noncomputable def mulR (α β : ℕ → ℝ) : ℝ := ((n ^ 2 + n - 1 : ℕ) : ℝ) * u p * mulX p n α β n

/-- Lemma 13 (c) for MUL: the levels stay within `X_m` at every moment, the final ones sum to within `R + Δ` of
`ab`, and there are `T_m = m(m + 1)` `TwoSum`s at level `m < n` and `Q = n² + n - 1` roundings at level `n` -/
theorem mulOps_levels (hp : 1 < p) (hn : 1 ≤ n) (a b α β : ℕ → ℝ) (ha : ∀ i < n, F p (a i))
    (hb : ∀ j < n, F p (b j)) (hα : ∀ i < n, |a i| ≤ α i) (hβ : ∀ j < n, |b j| ≤ β j)
    (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) :
    (∀ x ∈ LState.init :: (runOps p n (mulOps p n a b) LState.init).1, ∀ m ≤ n, |x.s m| ≤ mulX p n α β m) ∧
      |(∑ i ∈ range n, ∑ j ∈ range n, a i * b j) -
          ∑ m ∈ range (n + 1), (runOps p n (mulOps p n a b) LState.init).2.s m| ≤ mulR p n α β + mulDelta n α β ∧
      (∀ m < n, opsT (mulOps p n a b) m = m * (m + 1)) ∧ opsQ (mulOps p n a b) = n ^ 2 + n - 1 ∧
      ∀ m, F p ((runOps p n (mulOps p n a b) LState.init).2.s m) := by
  have hu := u_pos p
  obtain ⟨cT, cQ⟩ := mulOps_counts p n hn a b
  set ops := mulOps p n a b with hops
  have hwf : ∀ o ∈ ops, o.wf p n := by
    intro o ho
    simp only [hops, mulOps, mulStep4, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
      List.mem_cons, List.mem_nil_iff, or_false] at ho
    rcases ho with (((⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨l, hl, rfl⟩) | ⟨i, hi, j, hj, rfl | rfl⟩)
    · exact ⟨by omega, F_RN p _⟩
    · trivial
    · exact ⟨by omega, F_RN p _⟩
    · exact ⟨by omega, F_RN p _⟩
    · exact ⟨by omega, F_RN p _⟩
  have hok : (runOps p n ops LState.init).2.ok := by
    have hsplit : ops = ((List.range n).map fun j => LOp.assign j (twoProd p (a 0) (b j)).1) ++
        (((List.range (n - 1)).map fun i => LOp.round (a (i + 1) * b (n - (i + 1)))) ++
          ((List.range n).map fun l => LOp.dep (l + 1) (twoProd p (a 0) (b l)).2) ++ mulStep4 p n a b) := by
      simp only [hops, mulOps, List.append_assoc]
    rw [hsplit, (runOps_append p n _ _ _).2, runOps_ok_noassign]
    · exact ((runOps_assigns p n _ n LState.init fun _ _ => rfl).1).mpr trivial
    · intro o ho m y
      simp only [mulStep4, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap, List.mem_cons,
        List.mem_nil_iff, or_false] at ho
      rcases ho with ((⟨i, -, rfl⟩ | ⟨l, -, rfl⟩) | ⟨i, -, j, -, rfl | rfl⟩) <;> simp
  have hTu : ∀ m < n, (opsT ops m : ℝ) * u p < 1 := by
    intro m hm
    rw [cT m hm]
    push_cast
    have hm' : (m : ℝ) + 1 ≤ n := by exact_mod_cast hm
    have : (m : ℝ) * (m + 1) ≤ (n : ℝ) ^ 2 + n := by nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    nlinarith
  have hQu : (opsQ ops : ℝ) * u p < 1 := by
    rw [cQ]
    have : ((n ^ 2 + n - 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 + n := by
      have := Nat.sub_le (n ^ 2 + n) 1
      exact_mod_cast this
    nlinarith
  obtain ⟨la, lb, lc, ld⟩ := levels p n hp ops hwf hTu hQu hok
  have hA := mulOps_A p n hn a b α β ha hb hα hβ
  have hT' : ∀ k < n, opsT ops k = mulT k := fun k hk => cT k hk
  have hD : ∀ m ≤ n, levD (opsA n ops) (opsT ops) (u p) m ≤ levD (mulA p n α β) mulT (u p) m := by
    intro m hm
    rw [levD_congr n hT' m hm]
    exact levD_mono hu.le hA n (fun k hk => by have := hTu k hk; rwa [hT' k hk] at this) m hm
  have h1Q : 0 < 1 - ((n ^ 2 + n - 1 : ℕ) : ℝ) * u p := by rw [← cQ]; linarith
  have hX : ∀ m < n, levX (opsA n ops) (opsT ops) (u p) m ≤ mulX p n α β m := by
    intro m hm
    have h1 : 0 < 1 - (mulT m : ℝ) * u p := by have := hTu m hm; rw [hT' m hm] at this; linarith
    simp only [mulX, hm, ite_true, levX, hT' m hm]
    exact div_le_div_of_nonneg_right (hD m hm.le) h1.le
  have hXn : levD (opsA n ops) (opsT ops) (u p) n / (1 - (opsQ ops : ℝ) * u p) ≤ mulX p n α β n := by
    simp only [mulX, lt_irrefl, ite_false, cQ]
    exact div_le_div_of_nonneg_right (hD n le_rfl) h1Q.le
  refine ⟨fun x hx m hm => ?_, ?_, cT, cQ, fun m => ?_⟩
  · rcases Nat.lt_or_ge m n with hlt | hge
    · exact ((la x hx).1 m hlt).trans (hX m hlt)
    · obtain rfl : m = n := by omega
      exact (la x hx).2.trans hXn
  · rw [lc, mulOps_Y p n hn a b ha hb]
    -- the products of order above `n` are dropped
    have hdrop : (∑ i ∈ range n, ∑ j ∈ range n, a i * b j) -
        ∑ i ∈ range n, ∑ j ∈ range n, (if i + j ≤ n then a i * b j else 0) =
        ∑ i ∈ range n, ∑ j ∈ range n, if n < i + j then a i * b j else 0 := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun j _ => ?_
      by_cases h : n < i + j
      · simp [h, show ¬(i + j ≤ n) by omega]
      · simp [h, show i + j ≤ n by omega]
    have hΔ : |∑ i ∈ range n, ∑ j ∈ range n, (if n < i + j then a i * b j else 0)| ≤ mulDelta n α β := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
      simp only [mem_range] at hi hj
      split_ifs
      · rw [abs_mul]
        exact mul_le_mul (hα i hi) (hβ j hj) (abs_nonneg _) ((abs_nonneg _).trans (hα i hi))
      · simp
    have hr := runOps_rS p n ops LState.init (by simp [LState.init])
    have hR : (opsQ ops : ℝ) * u p * (levD (opsA n ops) (opsT ops) (u p) n / (1 - (opsQ ops : ℝ) * u p)) ≤
        mulR p n α β := by
      unfold mulR
      rw [cQ] at hXn ⊢
      exact mul_le_mul_of_nonneg_left hXn (mul_nonneg (Nat.cast_nonneg _) hu.le)
    have hsplit : (∑ i ∈ range n, ∑ j ∈ range n, a i * b j) -
        ((∑ i ∈ range n, ∑ j ∈ range n, if i + j ≤ n then a i * b j else 0) - (runOps p n ops LState.init).2.rS) =
        (∑ i ∈ range n, ∑ j ∈ range n, if n < i + j then a i * b j else 0) + (runOps p n ops LState.init).2.rS := by
      rw [← hdrop]
      ring
    rw [hsplit]
    exact (abs_add_le _ _).trans (by linarith [ld, hr])
  · obtain ⟨-, -, -, h⟩ := runOps_spec p n hp ops LState.init hwf (init_inv p n)
    exact (h hok).2.1 m

/-- MUL: `Ren_n` of its levels -/
noncomputable def mulOp (a b : ℕ → ℝ) : List ℝ := ren p n n (runOps p n (mulOps p n a b) LState.init).2.s

/-- Lemma 13 for MUL, with `|a_i| ≤ α_i`, `|b_j| ≤ β_j`, `A_m = (1 + u)P_m + uP_{m-1}`, `A_n = P_n + uP_{n-1}`,
`T_m = m(m + 1)`, `Q = n² + n - 1` and `Δ = ∑_{m > n} P_m` -/
theorem lemma13_mul (hp : 1 < p) (hn : 1 ≤ n) (a b α β : ℕ → ℝ) (ha : ∀ i < n, F p (a i))
    (hb : ∀ j < n, F p (b j)) (hα : ∀ i < n, |a i| ≤ α i) (hβ : ∀ j < n, |b j| ≤ β j)
    (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (Zb : ℝ) (hZ : |∑ i ∈ range n, ∑ j ∈ range n, a i * b j| ≤ Zb) :
    |(∑ i ∈ range n, ∑ j ∈ range n, a i * b j) - (mulOp p n a b).sum| ≤
        u p ^ n * Zb + (1 + u p ^ n) * (mulR p n α β + mulDelta n α β) +
          ∑ j ∈ Ioc 0 n, (u p ^ n + u p ^ (n + 1 - j)) * Vb p n (mulX p n α β) j ∧
      |(mulOp p n a b).getD 0 0| ≤
        (1 + u p) * (Zb + (mulR p n α β + mulDelta n α β) + ∑ j ∈ Ioc 1 n, Vb p n (mulX p n α β) j) ∧
      (∀ i, 1 ≤ i → i ≤ n - 1 → |(mulOp p n a b).getD i 0| ≤
        (1 + u p) * (u p * |(mulOp p n a b).getD (i - 1) 0| + ∑ j ∈ Ioc i n, Vb p n (mulX p n α β) j)) ∧
      (∀ x ∈ LState.init :: (runOps p n (mulOps p n a b) LState.init).1, ∀ m ≤ n, |x.s m| ≤ mulX p n α β m) ∧
      |(∑ i ∈ range n, ∑ j ∈ range n, a i * b j) -
          ∑ m ∈ range (n + 1), (runOps p n (mulOps p n a b) LState.init).2.s m| ≤ mulR p n α β + mulDelta n α β ∧
      (∀ m < n, opsT (mulOps p n a b) m = m * (m + 1)) ∧ opsQ (mulOps p n a b) = n ^ 2 + n - 1 := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := mulOps_levels p n hp hn a b α β ha hb hα hβ hA3
  have hne : mulOps p n a b ≠ [] := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp [mulOps, List.range_succ]
  have hlast := runOps_last_mem p n _ hne LState.init
  obtain ⟨r1, r2, r3⟩ := ren_of_levels p hp n hn _ (fun i _ => c5 i) (mulX p n α β)
    (c1 _ (List.mem_cons_of_mem _ hlast)) _ Zb _ hZ c2
  exact ⟨r1, r2, r3, c1, c2, c3, c4⟩

end ExpansionBounds
