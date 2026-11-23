import ExpansionBounds.AccThm

/-!
# Theorem 30: SLOPPY-MUL

SLOPPY-MUL on `n = N + 1` parts keeps the levels `s_0, …, s_N` and rounds at level `N`: (1)
`(s_j, e_{0j}) ← TwoProd(a_0, b_j)` for `j < N`; (2) the chain at level `N` of the products of order `n`, then of order
`n - 1`; (3) `dep(s, l, e_{0,l-1})` for `l = 1, …, N`; (4) MUL's step (4) with `N` in place of `n`; (5) `Ren_n(s)`,
which is exact on `n` terms. Below level `N` its inputs are MUL's, so `T_m = m(m + 1)`, and level `N` rounds `Q = n²`
times.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ)

/-- MUL's step (4) has `∑_{k<m}(k + 1) + ∑_{k<m-1}(k + 1)` `TwoSum`s at level `m < n` -/
theorem mulStep4_T (n : ℕ) (a b : ℕ → ℝ) (m : ℕ) (hm : m < n) :
    opsT (mulStep4 p n a b) m = ∑ k ∈ range m, (k + 1) + ∑ k ∈ range (m - 1), (k + 1) := by
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

/-- MUL's step (4) rounds `(n - 1)n` times at the top level -/
theorem mulStep4_Q (n : ℕ) (hn : 1 ≤ n) (a b : ℕ → ℝ) : opsQ (mulStep4 p n a b) = (n - 1) * n := by
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

variable (N : ℕ)

/-- SLOPPY-MUL's levels on `N + 1`-part operands, with level `N` rounding -/
noncomputable def sloppyOps (a b : ℕ → ℝ) : List LOp :=
  ((List.range N).map fun j => LOp.assign j (twoProd p (a 0) (b j)).1) ++
    ((List.range N).map fun i => LOp.round (a (i + 1) * b (N - i))) ++
    ((List.range (N + 1)).map fun i => LOp.round (a i * b (N - i))) ++
    ((List.range N).map fun l => LOp.dep (l + 1) (twoProd p (a 0) (b l)).2) ++
    mulStep4 p N a b

/-- SLOPPY-MUL: `Ren_n` of its `n = N + 1` levels -/
noncomputable def sloppyOp (a b : ℕ → ℝ) : List ℝ := ren p (N + 1) N (runOps p N (sloppyOps p N a b) LState.init).2.s

/-- `T_m = m(m + 1)` and `Q = n²` -/
theorem sloppy_counts (hN : 1 ≤ N) (a b : ℕ → ℝ) :
    (∀ m < N, opsT (sloppyOps p N a b) m = m * (m + 1)) ∧ opsQ (sloppyOps p N a b) = (N + 1) ^ 2 := by
  refine ⟨fun m hm => ?_, ?_⟩
  · have h1 : opsT (sloppyOps p N a b) m = opsT (mulStep4 p N a b) m + min N m := by
      simp only [opsT, sloppyOps, List.map_append, List.sum_append, List.map_map, Function.comp_def, opT]
      rw [count_le]
      simp
      ring
    rw [h1, mulStep4_T p N a b m hm, sum_succ_pair, min_eq_right hm.le]
    ring
  · have h1 : opsQ (sloppyOps p N a b) = N + (N + 1) + N + opsQ (mulStep4 p N a b) := by
      simp only [opsQ, sloppyOps, List.map_append, List.sum_append, List.map_map, Function.comp_def, opQ]
      simp
    rw [h1, mulStep4_Q p N hN]
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring

/-- `Â_m` of SLOPPY-MUL: MUL's for `m < N`, and `n + (n - 1)/θ + (n - 1)ρ` at `m = N` -/
noncomputable def hatAsloppy (θ : ℝ) (m : ℕ) : ℝ :=
  if m < N then hatAmul p N θ m else if m = N then (N + 1 : ℝ) + N / θ + N * (θ * u p) else 0

/-- SLOPPY-MUL's `L_m`: `T_m = m(m + 1)` and `Q = n²` -/
noncomputable def sloppyL (θ : ℝ) (m : ℕ) : ℝ := thmL p N (hatAsloppy p N θ) mulT θ ((N + 1) ^ 2) m

variable [Prec_gt_0 p]

/-- the inputs of SLOPPY-MUL's levels total at most `Â_m ρ^m M` on `H(θ)` operands -/
theorem sloppy_A (hN : 1 ≤ N) (θ : ℝ) (hθ : 0 < θ) (a b : ℕ → ℝ) (ha : ∀ i ≤ N, F p (a i))
    (hb : ∀ j ≤ N, F p (b j)) (hHa : ∀ i ≤ N, |a i| ≤ (θ * u p) ^ i * |a 0|)
    (hHb : ∀ j ≤ N, |b j| ≤ (θ * u p) ^ j * |b 0|) (m : ℕ) (hm : m ≤ N) :
    opsA N (sloppyOps p N a b) m ≤ hatAsloppy p N θ m * (θ * u p) ^ m * (|a 0| * |b 0|) := by
  have hu := u_pos p
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = θ * u p := ⟨_, rfl⟩
  rw [← hρ] at hHa hHb ⊢
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  obtain ⟨α, hα⟩ : ∃ α : ℕ → ℝ, α = fun i => ρ ^ i * |a 0| := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℝ, β = fun j => ρ ^ j * |b 0| := ⟨_, rfl⟩
  have hab : ∀ i ≤ N, ∀ j ≤ N, |a i * b j| ≤ ρ ^ (i + j) * (|a 0| * |b 0|) := fun i hi j hj => by
    rw [abs_mul, pow_add]
    calc |a i| * |b j| ≤ (ρ ^ i * |a 0|) * (ρ ^ j * |b 0|) :=
          mul_le_mul (hHa i hi) (hHb j hj) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  rcases Nat.lt_or_ge m N with hlt | hge
  · -- below level `N` the inputs are MUL's on `N` parts
    have heq : opsA N (sloppyOps p N a b) m = opsA N (mulOps p N a b) m := by
      simp only [opsA, sloppyOps, mulOps, List.map_append, List.sum_append, List.map_map, Function.comp_def, opA,
        show m ≠ N by omega, ite_false, list_sum_map_range_gen, sum_const_zero, add_zero]
    rw [heq]
    have h := mulOps_A p N hN a b α β (fun i hi => ha i hi.le) (fun j hj => hb j hj.le)
      (fun i hi => by rw [hα]; exact hHa i hi.le) (fun j hj => by rw [hβ]; exact hHb j hj.le) m
    rw [hα, hβ, hρ, mulA_geom p N hN θ hθ] at h
    rw [hρ]
    unfold hatAsloppy
    simpa [hlt] using h
  · obtain rfl : m = N := by omega
    -- level `N`: the chain's products of orders `n` and `n - 1`, and the errors of order `n - 2`
    have hexp : opsA m (sloppyOps p m a b) m =
        (∑ i ∈ range m, |a (i + 1) * b (m - i)|) + (∑ i ∈ range (m + 1), |a i * b (m - i)|) +
          ((∑ l ∈ range m, if l + 1 = m then |(twoProd p (a 0) (b l)).2| else 0) +
            ∑ i ∈ range (m - 1), ∑ j ∈ range (m - 1 - i),
              ((if i + 1 + j = m then |(twoProd p (a (i + 1)) (b j)).1| else 0) +
                (if i + 1 + j + 1 = m then |(twoProd p (a (i + 1)) (b j)).2| else 0))) := by
      have hz : ∀ j ∈ range m, (if j = m then |(twoProd p (a 0) (b j)).1| else 0) = 0 := fun j hj => by
        rw [mem_range] at hj; simp [show j ≠ m by omega]
      simp only [opsA, sloppyOps, mulStep4, List.map_append, List.sum_append, List.map_map, Function.comp_def,
        list_sum_flatMap, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, opA,
        list_sum_map_range_gen, ite_true]
      rw [sum_congr rfl hz, sum_const_zero, zero_add]
      ring
    rw [hexp]
    have b1 : ∑ i ∈ range m, |a (i + 1) * b (m - i)| ≤ m * (ρ ^ (m + 1) * (|a 0| * |b 0|)) := by
      calc ∑ i ∈ range m, |a (i + 1) * b (m - i)| ≤ ∑ _i ∈ range m, ρ ^ (m + 1) * (|a 0| * |b 0|) :=
            sum_le_sum fun i hi => by
              rw [mem_range] at hi
              have := hab (i + 1) (by omega) (m - i) (by omega)
              rwa [show i + 1 + (m - i) = m + 1 by omega] at this
        _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]
    have b2 : ∑ i ∈ range (m + 1), |a i * b (m - i)| ≤ (m + 1) * (ρ ^ m * (|a 0| * |b 0|)) := by
      calc ∑ i ∈ range (m + 1), |a i * b (m - i)| ≤ ∑ _i ∈ range (m + 1), ρ ^ m * (|a 0| * |b 0|) :=
            sum_le_sum fun i hi => by
              rw [mem_range] at hi
              have := hab i (by omega) (m - i) (by omega)
              rwa [show i + (m - i) = m by omega] at this
        _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
    -- the errors of order `m - 1`: `u` times the slice `P_{m-1}` of `m` products
    have he : ∀ i ≤ m, ∀ j ≤ m, |(twoProd p (a i) (b j)).2| ≤ u p * (α i * β j) := fun i hi j hj => by
      refine (facts_c p (ha i hi) (hb j hj)).2.1.trans ((mul_le_mul_of_nonneg_right (us_le_u p) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_left ?_ hu.le))
      rw [hα, hβ, abs_mul]
      exact mul_le_mul (hHa i hi) (hHb j hj) (abs_nonneg _) (by positivity)
    have b3 : (∑ l ∈ range m, if l + 1 = m then |(twoProd p (a 0) (b l)).2| else 0) +
        ∑ i ∈ range (m - 1), ∑ j ∈ range (m - 1 - i),
          ((if i + 1 + j = m then |(twoProd p (a (i + 1)) (b j)).1| else 0) +
            (if i + 1 + j + 1 = m then |(twoProd p (a (i + 1)) (b j)).2| else 0)) ≤
        u p * (mulP0 m α β (m - 1) + mulP4 m α β (m - 1)) := by
      rw [mulP0, mulP4, mul_add, mul_sum, mul_sum]
      refine add_le_add (sum_le_sum fun l hl => ?_) (sum_le_sum fun i hi => ?_)
      · rw [mem_range] at hl
        split_ifs with h1 h2
        · exact he 0 (by omega) l (by omega)
        · omega
        · omega
        · simp
      · rw [mem_range] at hi
        rw [mul_sum]
        refine sum_le_sum fun j hj => ?_
        rw [mem_range] at hj
        simp only [show i + 1 + j ≠ m by omega, ite_false, zero_add]
        split_ifs with h1 h2
        · exact he (i + 1) (by omega) j (by omega)
        · omega
        · omega
        · simp
    have hP : mulP0 m α β (m - 1) + mulP4 m α β (m - 1) = m * ρ ^ (m - 1) * (|a 0| * |b 0|) := by
      rw [← mulP_split m hN α β (m - 1) (by omega), hα, hβ, mulP_geom]
      simp only [pairCnt, show m - 1 < m by omega, ite_true]
      rw [show m - 1 + 1 = m by omega]
    rw [hP] at b3
    unfold hatAsloppy
    simp only [lt_irrefl, ite_false, ite_true]
    rw [← hρ]
    have hum : u p * ρ ^ (m - 1) = ρ ^ m / θ := by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ, hρ]
      field_simp
    calc _ ≤ m * (ρ ^ (m + 1) * (|a 0| * |b 0|)) + (m + 1) * (ρ ^ m * (|a 0| * |b 0|)) +
          u p * (m * ρ ^ (m - 1) * (|a 0| * |b 0|)) := add_le_add (add_le_add b1 b2) b3
      _ = ((m : ℝ) + 1 + m / θ + m * ρ) * ρ ^ m * (|a 0| * |b 0|) := by
          rw [show u p * (m * ρ ^ (m - 1) * (|a 0| * |b 0|)) = m * (u p * ρ ^ (m - 1)) * (|a 0| * |b 0|) by ring,
            hum, pow_succ]
          field_simp
          ring

/-- SLOPPY-MUL's program puts in `∑_{i+j ≤ n} a_i b_j` -/
theorem sloppy_Y (hN : 1 ≤ N) (a b : ℕ → ℝ) (ha : ∀ i ≤ N, F p (a i)) (hb : ∀ j ≤ N, F p (b j)) :
    opsY (sloppyOps p N a b) =
      ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), if i + j ≤ N + 1 then a i * b j else 0 := by
  rw [sum_le_n_split (N + 1) (by omega) (fun i j => a i * b j)]
  simp only [opsY, sloppyOps, mulStep4, List.map_append, List.sum_append, List.map_map, Function.comp_def,
    list_sum_flatMap, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, opY,
    list_sum_map_range_gen, Nat.add_sub_cancel]
  have h1 : ∀ j ∈ range N, (twoProd p (a 0) (b j)).1 + (twoProd p (a 0) (b j)).2 = a 0 * b j := fun j hj =>
    (facts_c p (ha 0 (by omega)) (hb j (by rw [mem_range] at hj; omega))).1
  have h4 : ∀ i ∈ range (N - 1), ∑ j ∈ range (N - 1 - i),
      ((twoProd p (a (i + 1)) (b j)).1 + (twoProd p (a (i + 1)) (b j)).2) = ∑ j ∈ range (N - 1 - i), a (i + 1) * b j :=
    fun i hi => sum_congr rfl fun j hj => by
      simp only [mem_range] at hi hj
      exact (facts_c p (ha (i + 1) (by omega)) (hb j (by omega))).1
  have hrow : ∀ i ∈ range N, ∑ j ∈ range (N - i), a (i + 1) * b j =
      ∑ j ∈ range (N - 1 - i), a (i + 1) * b j + a (i + 1) * b (N - 1 - i) := fun i hi => by
    rw [mem_range] at hi
    rw [show N - i = N - 1 - i + 1 by omega, sum_range_succ]
  have hlast : ∑ i ∈ range N, ∑ j ∈ range (N - 1 - i), a (i + 1) * b j =
      ∑ i ∈ range (N - 1), ∑ j ∈ range (N - 1 - i), a (i + 1) * b j := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [sum_range_succ]
    simp
  have e1 : ∑ x ∈ range N, (twoProd p (a 0) (b x)).1 + ∑ x ∈ range N, (twoProd p (a 0) (b x)).2 =
      ∑ x ∈ range N, a 0 * b x := by rw [← sum_add_distrib]; exact sum_congr rfl h1
  have e2 : ∑ x ∈ range N, a (x + 1) * b (N + 1 - (x + 1)) = ∑ x ∈ range N, a (x + 1) * b (N - x) :=
    sum_congr rfl fun x _ => by rw [show N + 1 - (x + 1) = N - x by omega]
  have e3 : ∑ x ∈ range (N + 1), a x * b (N - x) = ∑ x ∈ range N, a (x + 1) * b (N - 1 - x) + a 0 * b N := by
    rw [sum_range_succ']
    simp only [Nat.sub_zero]
    congr 1
    exact sum_congr rfl fun x _ => by rw [show N - (x + 1) = N - 1 - x by omega]
  have e5 : ∑ x ∈ range N, ∑ j ∈ range (N - x), a (x + 1) * b j =
      ∑ x ∈ range N, ∑ j ∈ range (N - 1 - x), a (x + 1) * b j + ∑ x ∈ range N, a (x + 1) * b (N - 1 - x) := by
    rw [← sum_add_distrib]; exact sum_congr rfl hrow
  have e6 := sum_range_succ (fun j => a 0 * b j) N
  have e4 := sum_congr rfl h4
  linarith

omit [Prec_gt_0 p] in
/-- `D_m` depends only on `A_0, …, A_m` -/
theorem levD_congrA {A A' : ℕ → ℝ} {T : ℕ → ℕ} {uu : ℝ} {m : ℕ} (h : ∀ k ≤ m, A k = A' k) :
    levD A T uu m = levD A' T uu m := by
  induction m with
  | zero => exact h 0 le_rfl
  | succ m ih =>
    simp only [levD]
    rw [h (m + 1) le_rfl, ih fun k hk => h k (by omega)]

/-- Theorem 30 (`thm:sloppy`) (a): on `H(θ)` operands with `n²u < 1`, the levels of SLOPPY-MUL stay within
`L_m u^m M` at every moment, with `T_m = m(m + 1)` and `Q = n²`, and its roundings total at most `R_s u^n M` -/
theorem thm30a (hp : 1 < p) (hN : 1 ≤ N) (hQ : ((N : ℝ) + 1) ^ 2 * u p < 1) (θ : ℝ) (hθ : 0 < θ) (a b : ℕ → ℝ)
    (ha : ∀ i ≤ N, F p (a i)) (hb : ∀ j ≤ N, F p (b j)) (hHa : Htheta p (N + 1) θ a) (hHb : Htheta p (N + 1) θ b) :
    (∀ x ∈ LState.init :: (runOps p N (sloppyOps p N a b) LState.init).1, ∀ m ≤ N,
        |x.s m| ≤ sloppyL p N θ m * u p ^ m * (|a 0| * |b 0|)) ∧
      (∀ m < N, opsT (sloppyOps p N a b) m = m * (m + 1)) ∧ opsQ (sloppyOps p N a b) = (N + 1) ^ 2 ∧
      (runOps p N (sloppyOps p N a b) LState.init).2.rA ≤
        ((N + 1) ^ 2 : ℕ) * sloppyL p N θ N * u p ^ (N + 1) * (|a 0| * |b 0|) ∧
      ∑ m ∈ range (N + 1), (runOps p N (sloppyOps p N a b) LState.init).2.s m =
        opsY (sloppyOps p N a b) - (runOps p N (sloppyOps p N a b) LState.init).2.rS ∧
      ∀ m, F p ((runOps p N (sloppyOps p N a b) LState.init).2.s m) := by
  have hu := u_pos p
  obtain ⟨cT, cQ⟩ := sloppy_counts p N hN a b
  set ops := sloppyOps p N a b with hops
  have hwf : ∀ o ∈ ops, o.wf p N := by
    intro o ho
    simp only [hops, sloppyOps, mulStep4, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
      List.mem_cons, List.mem_nil_iff, or_false] at ho
    rcases ho with ((((⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨l, hl, rfl⟩) | ⟨i, hi, j, hj, rfl | rfl⟩)
    · exact ⟨by omega, F_RN p _⟩
    · trivial
    · trivial
    · exact ⟨by omega, F_RN p _⟩
    · exact ⟨by omega, F_RN p _⟩
    · exact ⟨by omega, F_RN p _⟩
  have hok : (runOps p N ops LState.init).2.ok := by
    have hsplit : ops = ((List.range N).map fun j => LOp.assign j (twoProd p (a 0) (b j)).1) ++
        (((List.range N).map fun i => LOp.round (a (i + 1) * b (N - i))) ++
          ((List.range (N + 1)).map fun i => LOp.round (a i * b (N - i))) ++
          ((List.range N).map fun l => LOp.dep (l + 1) (twoProd p (a 0) (b l)).2) ++ mulStep4 p N a b) := by
      simp only [hops, sloppyOps, List.append_assoc]
    rw [hsplit, (runOps_append p N _ _ _).2, runOps_ok_noassign]
    · exact ((runOps_assigns p N _ N LState.init fun _ _ => rfl).1).mpr trivial
    · intro o ho m y
      simp only [mulStep4, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap, List.mem_cons,
        List.mem_nil_iff, or_false] at ho
      rcases ho with (((⟨i, -, rfl⟩ | ⟨i, -, rfl⟩) | ⟨l, -, rfl⟩) | ⟨i, -, j, -, rfl | rfl⟩) <;> simp
  have hTu : ∀ m < N, (opsT ops m : ℝ) * u p < 1 := by
    intro m hm
    rw [cT m hm]
    push_cast
    have hm' : (m : ℝ) + 1 ≤ N := by exact_mod_cast hm
    have : (m : ℝ) * (m + 1) ≤ ((N : ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    nlinarith
  have hQu : (opsQ ops : ℝ) * u p < 1 := by rw [cQ]; push_cast; exact hQ
  obtain ⟨la, -, lc, ld⟩ := levels p N hp ops hwf hTu hQu hok
  have hHa' := Htheta_le p (N + 1) hHa
  have hHb' := Htheta_le p (N + 1) hHb
  have hA : ∀ m ≤ N, opsA N ops m ≤ hatAsloppy p N θ m * (θ * u p) ^ m * (|a 0| * |b 0|) := fun m hm =>
    sloppy_A p N hN θ hθ a b ha hb (fun i hi => hHa' i (by omega)) (fun j hj => hHb' j (by omega)) m hm
  have hT' : ∀ k < N, opsT ops k = mulT k := fun k hk => cT k hk
  have hAle : ∀ k, opsA N ops k ≤
      (if k ≤ N then hatAsloppy p N θ k * (θ * u p) ^ k * (|a 0| * |b 0|) else opsA N ops k) := fun k => by
    split_ifs with hk
    · exact hA k hk
    · exact le_rfl
  have hD : ∀ m ≤ N, levD (opsA N ops) (opsT ops) (u p) m ≤
      thmD p (hatAsloppy p N θ) mulT θ m * (θ * u p) ^ m * (|a 0| * |b 0|) := by
    intro m hm
    rw [levD_congr N hT' m hm]
    refine (levD_mono hu.le hAle N (fun k hk => by have := hTu k hk; rwa [hT' k hk] at this) m hm).trans
      (le_of_eq ?_)
    rw [levD_congrA (A' := fun k => hatAsloppy p N θ k * (θ * u p) ^ k * (|a 0| * |b 0|))
      (fun k hk => by simp only [show k ≤ N by omega, ite_true])]
    exact levD_geom p _ _ θ hθ _ m
  have h1Q : 0 < 1 - (((N + 1) ^ 2 : ℕ) : ℝ) * u p := by rw [← cQ]; linarith
  have hX : ∀ m < N, levX (opsA N ops) (opsT ops) (u p) m ≤ sloppyL p N θ m * u p ^ m * (|a 0| * |b 0|) := by
    intro m hm
    have h1 : 0 < 1 - (mulT m : ℝ) * u p := by have := hTu m hm; rw [hT' m hm] at this; linarith
    simp only [levX, hT' m hm, sloppyL, thmL, hm, ite_true]
    calc levD (opsA N ops) (opsT ops) (u p) m / (1 - (mulT m : ℝ) * u p)
        ≤ thmD p (hatAsloppy p N θ) mulT θ m * (θ * u p) ^ m * (|a 0| * |b 0|) / (1 - (mulT m : ℝ) * u p) :=
          div_le_div_of_nonneg_right (hD m hm.le) h1.le
      _ = θ ^ m * thmD p (hatAsloppy p N θ) mulT θ m / (1 - (mulT m : ℝ) * u p) * u p ^ m * (|a 0| * |b 0|) := by
          rw [mul_pow]; ring
  have hXN : levD (opsA N ops) (opsT ops) (u p) N / (1 - (opsQ ops : ℝ) * u p) ≤
      sloppyL p N θ N * u p ^ N * (|a 0| * |b 0|) := by
    simp only [sloppyL, thmL, lt_irrefl, ite_false, cQ]
    calc levD (opsA N ops) (opsT ops) (u p) N / (1 - (((N + 1) ^ 2 : ℕ) : ℝ) * u p)
        ≤ thmD p (hatAsloppy p N θ) mulT θ N * (θ * u p) ^ N * (|a 0| * |b 0|) /
            (1 - (((N + 1) ^ 2 : ℕ) : ℝ) * u p) := div_le_div_of_nonneg_right (hD N le_rfl) h1Q.le
      _ = _ := by rw [mul_pow]; ring
  refine ⟨fun x hx m hm => ?_, cT, cQ, ?_, lc, fun m => ?_⟩
  · rcases Nat.lt_or_ge m N with hlt | hge
    · exact ((la x hx).1 m hlt).trans (hX m hlt)
    · obtain rfl : m = N := by omega
      exact (la x hx).2.trans hXN
  · refine ld.trans ?_
    calc (opsQ ops : ℝ) * u p * (levD (opsA N ops) (opsT ops) (u p) N / (1 - (opsQ ops : ℝ) * u p))
        ≤ (opsQ ops : ℝ) * u p * (sloppyL p N θ N * u p ^ N * (|a 0| * |b 0|)) :=
          mul_le_mul_of_nonneg_left hXN (by positivity)
      _ = _ := by rw [cQ, pow_succ]; ring
  · obtain ⟨-, -, -, h⟩ := runOps_spec p N hp ops LState.init hwf (init_inv p N)
    exact (h hok).2.1 m

omit [Prec_gt_0 p] in
theorem sloppyL_nonneg (hN : 1 ≤ N) (hQ : ((N : ℝ) + 1) ^ 2 * u p < 1) (θ : ℝ) (hθ : 0 < θ) (m : ℕ) :
    0 ≤ sloppyL p N θ m := by
  have hu := u_pos p
  refine thmL_nonneg p N _ _ θ hθ _ (fun k hk => ?_) (fun k hk => ?_) (by push_cast; exact hQ) m
  · unfold hatAsloppy hatAmul
    split_ifs <;> positivity
  · have h : (mulT k : ℝ) ≤ ((N : ℝ) + 1) ^ 2 := by
      unfold mulT; push_cast
      have : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
      nlinarith
    nlinarith

/-- Theorem 30 (b): `|ab - x| ≤ (R_s + Δ_n u) u^n M`, and relative to `|ab|` by `(eq:a0)` -/
theorem thm30b (hp : 1 < p) (hN : 1 ≤ N) (hQ : ((N : ℝ) + 1) ^ 2 * u p < 1) (θ : ℝ) (hθ : 0 < θ) (a b : ℕ → ℝ)
    (ha : ∀ i ≤ N, F p (a i)) (hb : ∀ j ≤ N, F p (b j)) (hHa : Htheta p (N + 1) θ a) (hHb : Htheta p (N + 1) θ b) :
    |(∑ i ∈ range (N + 1), a i) * (∑ j ∈ range (N + 1), b j) - (sloppyOp p N a b).sum| ≤
        ((((N + 1) ^ 2 : ℕ) : ℝ) * sloppyL p N θ N + thmDelta p (N + 1) θ * u p) * u p ^ (N + 1) * |a 0 * b 0| ∧
      (2 * (θ * u p) < 1 →
        |(∑ i ∈ range (N + 1), a i) * (∑ j ∈ range (N + 1), b j) - (sloppyOp p N a b).sum| ≤
          ((((N + 1) ^ 2 : ℕ) : ℝ) * sloppyL p N θ N + thmDelta p (N + 1) θ * u p) * u p ^ (N + 1) *
            ((1 - θ * u p) / (1 - 2 * (θ * u p))) ^ 2 * |(∑ i ∈ range (N + 1), a i) * (∑ j ∈ range (N + 1), b j)|) := by
  have hu := u_pos p
  obtain ⟨-, -, -, hrA, hsum, hF⟩ := thm30a p N hp hN hQ θ hθ a b ha hb hHa hHb
  obtain ⟨c, hc⟩ : ∃ c, c = (runOps p N (sloppyOps p N a b) LState.init).2.s := ⟨_, rfl⟩
  have hx : (sloppyOp p N a b).sum = ∑ i ∈ range (N + 1), c i := by
    rw [sloppyOp, ← hc]; exact ren_exact p hp (N + 1) N le_rfl c (fun i _ => by rw [hc]; exact hF i)
  rw [← hc] at hsum
  rw [sloppy_Y p N hN a b ha hb] at hsum
  have hHa' := Htheta_le p (N + 1) hHa
  have hHb' := Htheta_le p (N + 1) hHb
  -- the dropped products and the roundings
  have hdrop : |∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), (if N + 1 < i + j then a i * b j else 0)| ≤
      thmDelta p (N + 1) θ * u p ^ (N + 1 + 1) * (|a 0| * |b 0|) := by
    rw [← mulDelta_geom]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
    simp only [mem_range] at hi hj
    split_ifs
    · rw [abs_mul]
      exact mul_le_mul (hHa' i hi) (hHb' j hj) (abs_nonneg _) (by positivity)
    · simp
  have hrS := runOps_rS p N (sloppyOps p N a b) LState.init (by simp [LState.init])
  have hsplit : (∑ i ∈ range (N + 1), a i) * (∑ j ∈ range (N + 1), b j) - ∑ i ∈ range (N + 1), c i =
      (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), (if N + 1 < i + j then a i * b j else 0)) +
        (runOps p N (sloppyOps p N a b) LState.init).2.rS := by
    rw [hsum, sum_mul_sum]
    have : ∀ i ∈ range (N + 1), ∀ j ∈ range (N + 1),
        a i * b j = (if i + j ≤ N + 1 then a i * b j else 0) + (if N + 1 < i + j then a i * b j else 0) :=
      fun i _ j _ => by
        by_cases h : i + j ≤ N + 1
        · simp only [h, ite_true, show ¬(N + 1 < i + j) by omega, ite_false, add_zero]
        · simp only [h, ite_false, show N + 1 < i + j by omega, ite_true, zero_add]
    rw [sum_congr rfl fun i hi => sum_congr rfl fun j hj => this i hi j hj]
    simp only [sum_add_distrib]
    ring
  have habs : |(∑ i ∈ range (N + 1), a i) * (∑ j ∈ range (N + 1), b j) - (sloppyOp p N a b).sum| ≤
      ((((N + 1) ^ 2 : ℕ) : ℝ) * sloppyL p N θ N + thmDelta p (N + 1) θ * u p) * u p ^ (N + 1) * |a 0 * b 0| := by
    rw [hx, hsplit, abs_mul]
    refine (abs_add_le _ _).trans ?_
    have h2 := hrS.trans hrA
    calc _ ≤ thmDelta p (N + 1) θ * u p ^ (N + 1 + 1) * (|a 0| * |b 0|) +
          (((N + 1) ^ 2 : ℕ) : ℝ) * sloppyL p N θ N * u p ^ (N + 1) * (|a 0| * |b 0|) := add_le_add hdrop h2
      _ = _ := by rw [pow_succ]; ring
  refine ⟨habs, fun hρ => habs.trans ?_⟩
  have hk : 0 ≤ (((N + 1) ^ 2 : ℕ) : ℝ) * sloppyL p N θ N + thmDelta p (N + 1) θ * u p :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (sloppyL_nonneg p N hN hQ θ hθ N))
      (mul_nonneg (thmDelta_nonneg p (N + 1) θ hθ.le) hu.le)
  have hcc : 0 ≤ (1 - θ * u p) / (1 - 2 * (θ * u p)) :=
    div_nonneg (by nlinarith [mul_nonneg hθ.le hu.le]) (by linarith)
  have hM : |a 0 * b 0| ≤ ((1 - θ * u p) / (1 - 2 * (θ * u p))) ^ 2 *
      |(∑ i ∈ range (N + 1), a i) * (∑ j ∈ range (N + 1), b j)| := by
    rw [abs_mul, abs_mul, sq]
    calc |a 0| * |b 0| ≤ ((1 - θ * u p) / (1 - 2 * (θ * u p)) * |∑ i ∈ range (N + 1), a i|) *
          ((1 - θ * u p) / (1 - 2 * (θ * u p)) * |∑ j ∈ range (N + 1), b j|) :=
          mul_le_mul (Htheta_a0 p (N + 1) (by omega) θ hθ.le hρ a hHa)
            (Htheta_a0 p (N + 1) (by omega) θ hθ.le hρ b hHb) (abs_nonneg _) (mul_nonneg hcc (abs_nonneg _))
      _ = _ := by ring
  have := mul_le_mul_of_nonneg_left hM (mul_nonneg hk (pow_nonneg hu.le (N + 1)))
  nlinarith

/-- Theorem 27's argument for any deposits within `τ_l μ_k` whose levels sum to within `C μ_k` of their terms -/
theorem acc_finish_core (hp : 1 < p) (n : ℕ) (hn : 1 ≤ n) (K : ℕ) (hK1 : 1 ≤ K) (hK : ((n : ℝ) + 1) * K * u p < 1)
    (t : ℕ → ℕ → ℝ) (top : ℕ → Bool) (τ μ : ℕ → ℝ) (hτ0 : ∀ l, 0 ≤ τ l) (hμ0 : ∀ k, 0 ≤ μ k)
    (ht : ∀ k ∈ Icc 1 K, ∀ l < n, F p (t k l) ∧ |t k l| ≤ τ l * μ k)
    (htop : ∀ k ∈ Icc 1 K, top k = true → |t k n| ≤ τ n * μ k) (Zk : ℕ → ℝ) (C : ℝ)
    (hterm : ∀ k ∈ Icc 1 K, |Zk k - (∑ l ∈ range n, t k l + if top k then t k n else 0)| ≤ C * μ k) :
    |∑ k ∈ Icc 1 K, Zk k - ∑ i ∈ range n, finishR p n (runOps p n (accOps n t top K) LState.init).2.s n i| ≤
      u p ^ n * |∑ k ∈ Icc 1 K, Zk k| +
        (1 + u p ^ n) * (accE τ (∑ j ∈ Icc 1 K, μ j) (1 / (1 - ((n : ℝ) + 1) * K * u p)) (u p) n K +
          C * ∑ j ∈ Icc 1 K, μ j) +
        GaddfE p n (finishP p n (fun m => accSclosed τ (∑ j ∈ Icc 1 K, μ j) (1 / (1 - ((n : ℝ) + 1) * K * u p))
          (u p) m K) (n - 1)) (accSclosed τ (∑ j ∈ Icc 1 K, μ j) (1 / (1 - ((n : ℝ) + 1) * K * u p)) (u p) n K) 0 := by
  have hu := u_pos p
  obtain ⟨A1, A2, A3⟩ := lemma_acc p n hp t top K τ μ hτ0 hμ0 ht htop hK
  obtain ⟨s, hsd⟩ : ∃ s, s = (runOps p n (accOps n t top K) LState.init).2.s := ⟨_, rfl⟩
  obtain ⟨W, hWd⟩ : ∃ W, W = ∑ j ∈ Icc 1 K, μ j := ⟨_, rfl⟩
  obtain ⟨Γ, hΓd⟩ : ∃ Γ, Γ = 1 / (1 - ((n : ℝ) + 1) * K * u p) := ⟨_, rfl⟩
  obtain ⟨S, hSd⟩ : ∃ S : ℕ → ℝ, S = fun m => accSclosed τ W Γ (u p) m K := ⟨_, rfl⟩
  rw [← hsd, ← hWd, ← hΓd]
  rw [← hWd, ← hΓd] at A1 A3
  have hS : ∀ m ≤ n, |s m| ≤ S m := fun m hm => by
    have := A1 K (mem_Icc.mpr ⟨hK1, le_rfl⟩) _ (runOps_last_mem' p n _ _) m hm
    rw [hsd, hSd]; exact this
  have hsF : ∀ m ≤ n, F p (s m) := fun m _ => by
    rw [hsd]; exact runOps_F_noassign p n _ (accOps_noassign n t top K) _ (fun j => F_zero p) m
  obtain ⟨E, hEd⟩ : ∃ E, E = accE τ W Γ (u p) n K := ⟨_, rfl⟩
  rw [← hEd] at A3 ⊢
  have hZS : |∑ k ∈ Icc 1 K, Zk k - ∑ m ∈ range (n + 1), s m| ≤ E + C * W := by
    rw [hsd, A2]
    rw [show ∀ (X Y : ℕ → ℝ) (r : ℝ), ∑ k ∈ Icc 1 K, X k - (∑ k ∈ Icc 1 K, Y k - r) =
      ∑ k ∈ Icc 1 K, (X k - Y k) + r from fun X Y r => by rw [sum_sub_distrib]; ring]
    refine (abs_add_le _ _).trans ?_
    rw [hWd, mul_sum, add_comm]
    exact add_le_add A3 ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm))
  obtain ⟨f1, -, f3, f4⟩ := finish_exact p n hp hn s hsF S hS (n - 1) le_rfl
  obtain ⟨r, hrd⟩ : ∃ r, r = finishR p n s (n - 1) := ⟨_, rfl⟩
  rw [← hrd] at f1 f3 f4
  rw [Nat.sub_add_cancel hn] at f3
  have hfin : finishR p n s n = pt (addfOp p n r (s n)) := by
    have h : ∀ k', finishR p n s (k' + 1) = pt (addfOp p n (finishR p n s k') (s (k' + 1))) := fun _ => rfl
    have := h (n - 1)
    rw [Nat.sub_add_cancel hn] at this
    rw [this, hrd]
  obtain ⟨SS, hSS⟩ : ∃ SS, SS = ∑ m ∈ range (n + 1), s m := ⟨_, rfl⟩
  rw [← hSS] at hZS
  have hZr : |∑ i ∈ range n, r i + s n| ≤ |SS| := by rw [f3, ← sum_range_succ, hSS]
  obtain ⟨g1, -, -, g4⟩ := addf_G p n hp hn r (s n) (finishP p n S (n - 1)) (S n) f1 (hsF n le_rfl)
    (fun i _ => f4 i) (hS n le_rfl) _ hZr
  rw [gaddfE_split, f3, ← sum_range_succ, ← hSS] at g1
  have hxs : ∑ i ∈ range n, finishR p n s n i = (addfOp p n r (s n)).sum := by
    rw [hfin]; exact (list_sum_getD _ n g4).symm
  rw [hxs, show (fun m => accSclosed τ W Γ (u p) m K) = S from hSd.symm, show accSclosed τ W Γ (u p) n K = S n by
    rw [hSd]]
  have hSZ : |SS| ≤ |∑ k ∈ Icc 1 K, Zk k| + (E + C * W) := by
    have := abs_sub_abs_le_abs_sub SS (∑ k ∈ Icc 1 K, Zk k)
    rw [abs_sub_comm] at hZS
    linarith
  have h2 := mul_le_mul_of_nonneg_left hSZ (pow_nonneg hu.le n)
  calc |∑ k ∈ Icc 1 K, Zk k - (addfOp p n r (s n)).sum|
      ≤ |∑ k ∈ Icc 1 K, Zk k - SS| + |SS - (addfOp p n r (s n)).sum| := abs_sub_le _ _ _
    _ ≤ (E + C * W) + (u p ^ n * |SS| + GaddfE p n (finishP p n S (n - 1)) (S n) 0) := add_le_add hZS g1
    _ ≤ _ := by nlinarith

/-- the `k`-th deposit with SLOPPY-MUL: its `n` levels for ADDPROD-SLOPPY, the parts of `a` for ADDX -/
noncomputable def sloppyT (prod : ℕ → Bool) (a b : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun k => if prod k then (runOps p N (sloppyOps p N (a k) (b k)) LState.init).2.s else a k

omit [Prec_gt_0 p] in
/-- `τ_l = max(L_l u^l, ρ^l)` for `l < n` and `τ_n = 0`, with SLOPPY-MUL's `L_l` -/
noncomputable def sloppyTau (θ : ℝ) (l : ℕ) : ℝ :=
  if l < N + 1 then max (sloppyL p N θ l * u p ^ l) ((θ * u p) ^ l) else 0

/-- Theorem 30 (c): FINISH after `K` terms, each ADDPROD-SLOPPY or ADDX of operands on `H(θ)`, satisfies Theorem 27's
bound with `τ_l = max(L_l u^l, ρ^l)` for `l < n`, `τ_n = 0` and `E_prod = (R_s + Δ_n u) u^n W` -/
theorem thm30c (hp : 1 < p) (hN : 1 ≤ N) (hQ : ((N : ℝ) + 1) ^ 2 * u p < 1) (θ : ℝ) (hθ : 0 < θ) (K : ℕ)
    (hK1 : 1 ≤ K) (hK : ((N + 1 : ℕ) + 1 : ℝ) * K * u p < 1) (prod : ℕ → Bool) (a b : ℕ → ℕ → ℝ)
    (ha : ∀ k ∈ Icc 1 K, ∀ i ≤ N, F p (a k i)) (hb : ∀ k ∈ Icc 1 K, prod k = true → ∀ j ≤ N, F p (b k j))
    (hHa : ∀ k ∈ Icc 1 K, Htheta p (N + 1) θ (a k)) (hHb : ∀ k ∈ Icc 1 K, prod k = true → Htheta p (N + 1) θ (b k)) :
    |accZ (N + 1) prod a b K - ∑ i ∈ range (N + 1),
        finishR p (N + 1) (runOps p (N + 1) (accOps (N + 1) (sloppyT p N prod a b) (fun _ => false) K)
          LState.init).2.s (N + 1) i| ≤
      u p ^ (N + 1) * |accZ (N + 1) prod a b K| +
        (1 + u p ^ (N + 1)) * (accE (sloppyTau p N θ) (∑ j ∈ Icc 1 K, accMu prod a b j)
            (1 / (1 - ((N + 1 : ℕ) + 1 : ℝ) * K * u p)) (u p) (N + 1) K +
          ((((N + 1) ^ 2 : ℕ) : ℝ) * sloppyL p N θ N + thmDelta p (N + 1) θ * u p) * u p ^ (N + 1) *
            ∑ j ∈ Icc 1 K, accMu prod a b j) +
        GaddfE p (N + 1) (finishP p (N + 1) (fun m => accSclosed (sloppyTau p N θ) (∑ j ∈ Icc 1 K, accMu prod a b j)
          (1 / (1 - ((N + 1 : ℕ) + 1 : ℝ) * K * u p)) (u p) m K) N)
          (accSclosed (sloppyTau p N θ) (∑ j ∈ Icc 1 K, accMu prod a b j)
            (1 / (1 - ((N + 1 : ℕ) + 1 : ℝ) * K * u p)) (u p) (N + 1) K) 0 := by
  have hu := u_pos p
  have hL0 := sloppyL_nonneg p N hN hQ θ hθ
  have hτ0 : ∀ l, 0 ≤ sloppyTau p N θ l := fun l => by
    unfold sloppyTau; split_ifs
    · exact le_max_of_le_right (by positivity)
    · exact le_rfl
  have hμ0 : ∀ k, 0 ≤ accMu prod a b k := fun k => by unfold accMu; split_ifs <;> positivity
  have hC0 : 0 ≤ ((((N + 1) ^ 2 : ℕ) : ℝ) * sloppyL p N θ N + thmDelta p (N + 1) θ * u p) * u p ^ (N + 1) :=
    mul_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (hL0 N))
      (mul_nonneg (thmDelta_nonneg p (N + 1) θ hθ.le) hu.le)) (by positivity)
  have hprod : ∀ k ∈ Icc 1 K, prod k = true →
      (∀ m ≤ N, |sloppyT p N prod a b k m| ≤ sloppyL p N θ m * u p ^ m * accMu prod a b k) ∧
        (∀ m, F p (sloppyT p N prod a b k m)) ∧
        |(∑ i ∈ range (N + 1), a k i) * (∑ j ∈ range (N + 1), b k j) - ∑ m ∈ range (N + 1), sloppyT p N prod a b k m| ≤
          ((((N + 1) ^ 2 : ℕ) : ℝ) * sloppyL p N θ N + thmDelta p (N + 1) θ * u p) * u p ^ (N + 1) *
            accMu prod a b k := by
    intro k hk hpk
    obtain ⟨t1, -, -, -, -, t6⟩ :=
      thm30a p N hp hN hQ θ hθ (a k) (b k) (ha k hk) (hb k hk hpk) (hHa k hk) (hHb k hk hpk)
    obtain ⟨b1, -⟩ := thm30b p N hp hN hQ θ hθ (a k) (b k) (ha k hk) (hb k hk hpk) (hHa k hk) (hHb k hk hpk)
    have hT : sloppyT p N prod a b k = (runOps p N (sloppyOps p N (a k) (b k)) LState.init).2.s := by
      simp [sloppyT, hpk]
    have hm : accMu prod a b k = |a k 0 * b k 0| := by simp [accMu, hpk]
    have hx : (sloppyOp p N (a k) (b k)).sum = ∑ i ∈ range (N + 1), sloppyT p N prod a b k i := by
      rw [hT, sloppyOp]; exact ren_exact p hp (N + 1) N le_rfl _ (fun i _ => t6 i)
    rw [hm]
    refine ⟨fun m hm' => ?_, fun m => by rw [hT]; exact t6 m, by rw [← hx]; exact b1⟩
    rw [hT, abs_mul]
    have := t1 _ (runOps_last_mem' p N _ _) m hm'
    rwa [← abs_mul] at this ⊢
  have hx : ∀ k ∈ Icc 1 K, prod k = false → sloppyT p N prod a b k = a k ∧ accMu prod a b k = |a k 0| :=
    fun k _ hpk => by simp [sloppyT, accMu, hpk]
  refine acc_finish_core p hp (N + 1) (by omega) K hK1 hK _ _ _ _ hτ0 hμ0 (fun k hk l hl => ?_)
    (fun k _ h => by simp at h)
    (fun k => if prod k then (∑ i ∈ range (N + 1), a k i) * ∑ j ∈ range (N + 1), b k j else ∑ i ∈ range (N + 1), a k i)
    _ (fun k hk => ?_) |>.trans_eq (by rw [Nat.add_sub_cancel]; rfl)
  · cases hpk : prod k with
    | true =>
      obtain ⟨h1, h2, -⟩ := hprod k hk hpk
      refine ⟨h2 l, (h1 l (by omega)).trans (mul_le_mul_of_nonneg_right ?_ (hμ0 k))⟩
      simp only [sloppyTau, hl, ite_true]
      exact le_max_left _ _
    | false =>
      obtain ⟨h1, h2⟩ := hx k hk hpk
      rw [h1, h2]
      refine ⟨ha k hk l (by omega), (Htheta_le p (N + 1) (hHa k hk) l hl).trans
        (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))⟩
      simp only [sloppyTau, hl, ite_true]
      exact le_max_right _ _
  · simp only [Bool.false_eq_true, ite_false, add_zero]
    cases hpk : prod k with
    | true =>
      simp only [ite_true]
      exact (hprod k hk hpk).2.2
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [(hx k hk hpk).1, sub_self, abs_zero]
      exact mul_nonneg hC0 (hμ0 k)

end ExpansionBounds
