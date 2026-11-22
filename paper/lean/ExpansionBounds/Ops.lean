import ExpansionBounds.OpBounds

/-!
# Lemma 13 for ADD and MULF

ADD and MULF are programs of Lemma 11 of one shape: `(s_i, t_i)` from `TwoSum(a_i, b_i)` or `TwoProd(a_i, b)` for
`i < n`, `s_n ← t_{n-1}`, and `dep(s, l, t_{l-1})` for `l = 1, …, n - 1`, then `Ren_n(s)`. Lemma 11 bounds their levels
with `A_m = (1 + u)λ_m + uλ_{m-1}`, `A_n = uλ_{n-1}`, `T_m = m` and `Q = n - 1`, and the result follows from
`ren_of_levels`.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) (n : ℕ)

theorem runOps_append (l1 l2 : List LOp) (st : LState) :
    (runOps p n (l1 ++ l2) st).1 = (runOps p n l1 st).1 ++ (runOps p n l2 (runOps p n l1 st).2).1 ∧
      (runOps p n (l1 ++ l2) st).2 = (runOps p n l2 (runOps p n l1 st).2).2 := by
  induction l1 generalizing st with
  | nil => simp [runOps]
  | cons o os ih =>
    obtain ⟨h1, h2⟩ := ih (stepOp p n o st).2
    simp only [List.cons_append, runOps]
    exact ⟨by rw [h1, List.append_assoc], h2⟩

theorem depRun_ok : ∀ (k m : ℕ) (e : ℝ) (st : LState), (depRun p n k m e st).2.ok = st.ok
  | 0, _, _, _ => rfl
  | k + 1, m, e, st => depRun_ok k (m + 1) _ (twoAt p m e st)

theorem depRun_last_mem : ∀ (k m : ℕ) (e : ℝ) (st : LState), (depRun p n k m e st).2 ∈ (depRun p n k m e st).1
  | 0, _, _, _ => by simp [depRun]
  | k + 1, m, e, st => List.mem_cons_of_mem _ (depRun_last_mem k (m + 1) _ (twoAt p m e st))

theorem stepOp_last_mem (o : LOp) (st : LState) : (stepOp p n o st).2 ∈ (stepOp p n o st).1 := by
  cases o with
  | assign m y => simp [stepOp]
  | dep l t => exact depRun_last_mem p n _ _ _ _
  | round y => simp [stepOp]

theorem runOps_last_mem (ops : List LOp) (hne : ops ≠ []) (st : LState) :
    (runOps p n ops st).2 ∈ (runOps p n ops st).1 := by
  induction ops generalizing st with
  | nil => exact absurd rfl hne
  | cons o os ih =>
    simp only [runOps, List.mem_append]
    rcases eq_or_ne os [] with rfl | hos
    · left
      exact stepOp_last_mem p n o st
    · right
      exact ih hos _

/-- `|∑ r| ≤ ∑ |r|` over the rounding errors of a run -/
theorem depRun_rS : ∀ (k m : ℕ) (e : ℝ) (st : LState), |st.rS| ≤ st.rA →
    |(depRun p n k m e st).2.rS| ≤ (depRun p n k m e st).2.rA
  | 0, m, e, st, h => by
    show |st.rS + (st.s n + e - RN p (st.s n + e))| ≤ st.rA + |RN p (st.s n + e) - (st.s n + e)|
    rw [abs_sub_comm (RN p _)]
    exact (abs_add_le _ _).trans (by linarith)
  | k + 1, m, e, st, h => depRun_rS k (m + 1) _ (twoAt p m e st) h

theorem runOps_rS (ops : List LOp) : ∀ st : LState, |st.rS| ≤ st.rA →
    |(runOps p n ops st).2.rS| ≤ (runOps p n ops st).2.rA := by
  induction ops with
  | nil => intro st h; exact h
  | cons o os ih =>
    intro st h
    refine ih _ ?_
    cases o with
    | assign m y => exact h
    | dep l t => exact depRun_rS p n _ _ _ _ h
    | round y =>
      show |st.rS + (st.s n + y - RN p (st.s n + y))| ≤ st.rA + |RN p (st.s n + y) - (st.s n + y)|
      rw [abs_sub_comm (RN p _)]
      exact (abs_add_le _ _).trans (by linarith)

/-- assignments to the levels `0, …, k - 1`, each still zero, keep `ok` and set those levels -/
theorem runOps_assigns (f : ℕ → ℝ) (k : ℕ) : ∀ st : LState, (∀ i < k, st.s i = 0) →
    ((runOps p n ((List.range k).map fun i => LOp.assign i (f i)) st).2.ok ↔ st.ok) ∧
      ∀ i, (runOps p n ((List.range k).map fun i => LOp.assign i (f i)) st).2.s i = if i < k then f i else st.s i := by
  induction k with
  | zero => intro st _; simp [runOps]
  | succ k ih =>
    intro st h0
    obtain ⟨ih1, ih2⟩ := ih st fun i hi => h0 i (by omega)
    rw [List.range_succ, List.map_append, (runOps_append p n _ _ st).2]
    set st1 := (runOps p n ((List.range k).map fun i => LOp.assign i (f i)) st).2
    have hk : st1.s k = 0 := by rw [ih2]; simp [h0 k (by omega)]
    refine ⟨?_, fun i => ?_⟩
    · show (st1.ok ∧ st1.s k = 0) ↔ st.ok
      rw [ih1]
      simp [hk]
    · show Function.update st1.s k (f k) i = _
      rw [Function.update_apply, ih2]
      by_cases hik : i = k
      · subst hik
        simp
      · by_cases hlt : i < k
        · simp [hik, hlt, show i < k + 1 by omega]
        · simp [hik, hlt, show ¬i < k + 1 by omega]

theorem runOps_ok_of_deps (ls : List (ℕ × ℝ)) : ∀ st : LState,
    (runOps p n (ls.map fun lt => LOp.dep lt.1 lt.2) st).2.ok = st.ok := by
  induction ls with
  | nil => intro st; rfl
  | cons lt ls ih =>
    intro st
    simp only [List.map_cons, runOps]
    rw [ih]
    exact depRun_ok p n _ _ _ _

/-- the programs of ADD and MULF -/
noncomputable def pairOps (g : ℕ → ℝ × ℝ) : List LOp :=
  ((List.range n).map fun i => LOp.assign i (g i).1) ++ [LOp.assign n (g (n - 1)).2] ++
    ((List.range (n - 1)).map fun l => (l + 1, (g l).2)).map fun lt => LOp.dep lt.1 lt.2

/-- the bounds on the inputs of the levels of ADD and MULF: `A_m = (1 + u)λ_m + uλ_{m-1}` for `m < n`, with
`λ_{-1} = 0`, and `A_n = uλ_{n-1}` -/
noncomputable def pairA (lam : ℕ → ℝ) (m : ℕ) : ℝ :=
  if m < n then (1 + u p) * lam m + (if m = 0 then 0 else u p * lam (m - 1))
  else if m = n then u p * lam (n - 1) else 0

theorem list_sum_ite_eq (f : ℕ → ℝ) (N m : ℕ) :
    ((List.range N).map fun i => if i = m then f i else 0).sum = if m < N then f m else 0 := by
  rw [list_sum_map_range, sum_ite_eq']
  simp

theorem count_le (N m : ℕ) : ((List.range N).map fun l => if l + 1 ≤ m then 1 else 0).sum = min N m := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    split_ifs <;> omega

/-- the totals of ADD and MULF's program from `Lemma 11`'s point of view -/
theorem pairOps_counts (hn : 1 ≤ n) (g : ℕ → ℝ × ℝ) :
    (∀ m, opsA n (pairOps n g) m = (if m < n then |(g m).1| else 0) + (if m = n then |(g (n - 1)).2| else 0) +
      (if 1 ≤ m ∧ m < n then |(g (m - 1)).2| else 0)) ∧
      (∀ m < n, opsT (pairOps n g) m = m) ∧ opsQ (pairOps n g) = n - 1 ∧
      opsY (pairOps n g) = ∑ i ∈ range n, ((g i).1 + (g i).2) := by
  refine ⟨fun m => ?_, fun m hm => ?_, ?_, ?_⟩
  · simp only [opsA, pairOps, List.map_append, List.sum_append, List.map_map, Function.comp_def, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero, opA]
    rw [list_sum_ite_eq (fun i => |(g i).1|)]
    congr 1
    · simp [eq_comm]
    · have : ((List.range (n - 1)).map fun l => if l + 1 = m then |(g l).2| else 0).sum =
          if 1 ≤ m ∧ m < n then |(g (m - 1)).2| else 0 := by
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · simp
        · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
          simp only [Nat.add_right_cancel_iff]
          rw [list_sum_ite_eq (fun l => |(g l).2|)]
          by_cases h : m' < n - 1 <;> simp [h] <;> omega
      exact this
  · simp only [opsT, pairOps, List.map_append, List.sum_append, List.map_map, Function.comp_def, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero, opT]
    rw [count_le]
    simp
    omega
  · simp only [opsQ, pairOps, List.map_append, List.sum_append, List.map_map, Function.comp_def, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero, opQ]
    simp
  · simp only [opsY, pairOps, List.map_append, List.sum_append, List.map_map, Function.comp_def, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero, opY]
    simp only [list_sum_map_range]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [sum_add_distrib, sum_range_succ (fun i => (g i).2)]
    simp
    ring

theorem levD_congr {A : ℕ → ℝ} {T T' : ℕ → ℕ} {uu : ℝ} (hT : ∀ k < n, T k = T' k) :
    ∀ m ≤ n, levD A T uu m = levD A T' uu m
  | 0, _ => rfl
  | m + 1, hm => by
    simp only [levD]
    rw [levD_congr hT m (by omega), hT m (by omega)]

/-- the level bounds of ADD and MULF: `X_m` of Lemma 11 with their `A_m`, `T_m = m` and `Q = n - 1` -/
noncomputable def pairX (lam : ℕ → ℝ) (m : ℕ) : ℝ :=
  if m < n then levX (pairA p n lam) id (u p) m
  else levD (pairA p n lam) id (u p) n / (1 - ((n - 1 : ℕ) : ℝ) * u p)

/-- `R = Q u X_n` for ADD and MULF -/
noncomputable def pairR (lam : ℕ → ℝ) : ℝ := ((n - 1 : ℕ) : ℝ) * u p * pairX p n lam n

variable [Prec_gt_0 p]

/-- Lemma 13 (c) for the program of ADD and MULF, whose part pairs `(s_i, t_i)` have `|s_i| ≤ (1 + u)λ_i` and
`|t_i| ≤ uλ_i`: the levels stay within `X_m` at every moment, the final ones sum to within `R` of `∑ (s_i + t_i)`,
and there are `T_m = m` `TwoSum`s at level `m < n` and `Q = n - 1` roundings at level `n` -/
theorem pairOps_levels (hp : 1 < p) (hn : 1 ≤ n) (g : ℕ → ℝ × ℝ) (lam : ℕ → ℝ)
    (hF : ∀ i < n, F p (g i).1 ∧ F p (g i).2) (hs : ∀ i < n, |(g i).1| ≤ (1 + u p) * lam i)
    (ht : ∀ i < n, |(g i).2| ≤ u p * lam i) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) :
    (∀ x ∈ LState.init :: (runOps p n (pairOps n g) LState.init).1, ∀ m ≤ n, |x.s m| ≤ pairX p n lam m) ∧
      |∑ i ∈ range n, ((g i).1 + (g i).2) - ∑ m ∈ range (n + 1), (runOps p n (pairOps n g) LState.init).2.s m| ≤
        pairR p n lam ∧
      (∀ m < n, opsT (pairOps n g) m = m) ∧ opsQ (pairOps n g) = n - 1 ∧
      ∀ m, F p ((runOps p n (pairOps n g) LState.init).2.s m) := by
  have hu := u_pos p
  obtain ⟨cA, cT, cQ, cY⟩ := pairOps_counts n hn g
  set ops := pairOps n g with hops
  -- the operations are those of Lemma 11
  have hwf : ∀ o ∈ ops, o.wf p n := by
    intro o ho
    simp only [hops, pairOps, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at ho
    rcases ho with ((⟨i, hi, rfl⟩ | rfl) | ⟨⟨l, t⟩, ⟨l', hl', hlt⟩, rfl⟩)
    · exact ⟨by omega, (hF i hi).1⟩
    · exact ⟨le_rfl, (hF (n - 1) (by omega)).2⟩
    · simp only [Prod.mk.injEq] at hlt
      obtain ⟨rfl, rfl⟩ := hlt
      exact ⟨by omega, (hF l' (by omega)).2⟩
  -- every assignment is to a zero level
  have hok : (runOps p n ops LState.init).2.ok := by
    rw [hops, pairOps, (runOps_append p n _ _ _).2, (runOps_append p n _ _ _).2, runOps_ok_of_deps]
    obtain ⟨h1, h2⟩ := runOps_assigns p n (fun i => (g i).1) n LState.init (fun _ _ => rfl)
    show (_ ∧ _ = 0)
    refine ⟨h1.mpr trivial, ?_⟩
    rw [h2]
    simp [LState.init]
  have hTu : ∀ m < n, (opsT ops m : ℝ) * u p < 1 := by
    intro m hm
    rw [cT m hm]
    have : (m : ℝ) ≤ (n : ℝ) ^ 2 + n := by
      have : (m : ℝ) ≤ n := by exact_mod_cast hm.le
      nlinarith
    nlinarith
  have hQu : (opsQ ops : ℝ) * u p < 1 := by
    rw [cQ]
    have : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 + n := by
      have : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
      nlinarith
    nlinarith
  obtain ⟨la, lb, lc, ld⟩ := levels p n hp ops hwf hTu hQu hok
  have hA : ∀ m, opsA n ops m ≤ pairA p n lam m := by
    intro m
    rw [cA m]
    unfold pairA
    by_cases hm : m < n
    · have hmn : m ≠ n := by omega
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · have h0n : (0 : ℕ) ≠ n := by omega
        simp only [hm, h0n, ite_true, ite_false, add_zero]
        simpa using hs 0 hm
      · simp only [hm, hmn, ite_true, ite_false, add_zero, show 1 ≤ m by omega, and_self,
          show m ≠ 0 by omega]
        linarith [hs m hm, ht (m - 1) (by omega)]
    · by_cases hmn : m = n
      · subst hmn
        simp [ht (m - 1) (by omega)]
      · simp [hm, hmn]
  have hT' : ∀ k < n, opsT ops k = id k := fun k hk => cT k hk
  have hD : ∀ m ≤ n, levD (opsA n ops) (opsT ops) (u p) m ≤ levD (pairA p n lam) id (u p) m := by
    intro m hm
    rw [levD_congr n hT' m hm]
    exact levD_mono hu.le hA n (fun k hk => by have := hTu k hk; rwa [hT' k hk] at this) m hm
  have h1Q : 0 < 1 - ((n - 1 : ℕ) : ℝ) * u p := by rw [← cQ]; linarith
  have hX : ∀ m < n, levX (opsA n ops) (opsT ops) (u p) m ≤ pairX p n lam m := by
    intro m hm
    have h1 : 0 < 1 - (m : ℝ) * u p := by have := hTu m hm; rw [cT m hm] at this; linarith
    simp only [pairX, hm, ite_true, levX, cT m hm, id]
    exact div_le_div_of_nonneg_right (hD m hm.le) h1.le
  have hXn : levD (opsA n ops) (opsT ops) (u p) n / (1 - (opsQ ops : ℝ) * u p) ≤ pairX p n lam n := by
    simp only [pairX, lt_irrefl, ite_false, cQ]
    exact div_le_div_of_nonneg_right (hD n le_rfl) h1Q.le
  refine ⟨fun x hx m hm => ?_, ?_, cT, cQ, fun m => ?_⟩
  · rcases Nat.lt_or_ge m n with hlt | hge
    · exact ((la x hx).1 m hlt).trans (hX m hlt)
    · obtain rfl : m = n := by omega
      exact (la x hx).2.trans hXn
  · rw [lc, cY, sub_sub_cancel]
    have hr := runOps_rS p n ops LState.init (by simp [LState.init])
    refine hr.trans (ld.trans ?_)
    unfold pairR
    rw [cQ] at hXn ⊢
    exact mul_le_mul_of_nonneg_left hXn (mul_nonneg (Nat.cast_nonneg _) hu.le)
  · obtain ⟨-, -, -, h⟩ := runOps_spec p n hp ops LState.init hwf (init_inv p n)
    exact (h hok).2.1 m

/-- Lemma 13 (a) and (b) for the program of ADD and MULF, with `Δ = 0` -/
theorem pairOps_result (hp : 1 < p) (hn : 1 ≤ n) (g : ℕ → ℝ × ℝ) (lam : ℕ → ℝ)
    (hF : ∀ i < n, F p (g i).1 ∧ F p (g i).2) (hs : ∀ i < n, |(g i).1| ≤ (1 + u p) * lam i)
    (ht : ∀ i < n, |(g i).2| ≤ u p * lam i) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (Zb : ℝ)
    (hZ : |∑ i ∈ range n, ((g i).1 + (g i).2)| ≤ Zb) :
    |∑ i ∈ range n, ((g i).1 + (g i).2) - (ren p n n (runOps p n (pairOps n g) LState.init).2.s).sum| ≤
        u p ^ n * Zb + (1 + u p ^ n) * pairR p n lam +
          ∑ j ∈ Ioc 0 n, (u p ^ n + u p ^ (n + 1 - j)) * Vb p n (pairX p n lam) j ∧
      |(ren p n n (runOps p n (pairOps n g) LState.init).2.s).getD 0 0| ≤
        (1 + u p) * (Zb + pairR p n lam + ∑ j ∈ Ioc 1 n, Vb p n (pairX p n lam) j) ∧
      ∀ i, 1 ≤ i → i ≤ n - 1 → |(ren p n n (runOps p n (pairOps n g) LState.init).2.s).getD i 0| ≤
        (1 + u p) * (u p * |(ren p n n (runOps p n (pairOps n g) LState.init).2.s).getD (i - 1) 0| +
          ∑ j ∈ Ioc i n, Vb p n (pairX p n lam) j) := by
  obtain ⟨c1, c2, -, -, c5⟩ := pairOps_levels p n hp hn g lam hF hs ht hA3
  have hne : pairOps n g ≠ [] := by simp [pairOps]
  have hlast := runOps_last_mem p n _ hne LState.init
  exact ren_of_levels p hp n hn _ (fun i _ => c5 i) (pairX p n lam)
    (c1 _ (List.mem_cons_of_mem _ hlast)) _ Zb _ hZ c2

/-- ADD: `(s_i, t_i) ← TwoSum(a_i, b_i)` for `i < n`, `s_n ← t_{n-1}`, `dep(s, l, t_{l-1})` for `l = 1, …, n - 1` -/
noncomputable def addOps (a b : ℕ → ℝ) : List LOp := pairOps n fun i => twoSum p (a i) (b i)

/-- the levels of ADD at the end -/
noncomputable def addLevels (a b : ℕ → ℝ) : ℕ → ℝ := (runOps p n (addOps p n a b) LState.init).2.s

/-- ADD: `Ren_n` of its levels -/
noncomputable def addOp (a b : ℕ → ℝ) : List ℝ := ren p n n (addLevels p n a b)

/-- MULF: `(s_i, e_i) ← TwoProd(a_i, b)` for `i < n`, `s_n ← e_{n-1}`, `dep(s, l, e_{l-1})` for `l = 1, …, n - 1` -/
noncomputable def mulfOps (a : ℕ → ℝ) (b : ℝ) : List LOp := pairOps n fun i => twoProd p (a i) b

/-- the levels of MULF at the end -/
noncomputable def mulfLevels (a : ℕ → ℝ) (b : ℝ) : ℕ → ℝ := (runOps p n (mulfOps p n a b) LState.init).2.s

/-- MULF: `Ren_n` of its levels -/
noncomputable def mulfOp (a : ℕ → ℝ) (b : ℝ) : List ℝ := ren p n n (mulfLevels p n a b)

/-- Lemma 13 for ADD, with `λ_m ≥ |a_m + b_m|`, `A_m = (1 + u)λ_m + uλ_{m-1}`, `A_n = uλ_{n-1}`, `T_m = m`,
`Q = n - 1` and `Δ = 0` -/
theorem lemma13_add (hp : 1 < p) (hn : 1 ≤ n) (a b : ℕ → ℝ) (ha : ∀ i < n, F p (a i)) (hb : ∀ i < n, F p (b i))
    (lam : ℕ → ℝ) (hlam : ∀ m < n, |a m + b m| ≤ lam m) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (Zb : ℝ)
    (hZ : |∑ i ∈ range n, (a i + b i)| ≤ Zb) :
    |∑ i ∈ range n, (a i + b i) - (addOp p n a b).sum| ≤ u p ^ n * Zb + (1 + u p ^ n) * pairR p n lam +
        ∑ j ∈ Ioc 0 n, (u p ^ n + u p ^ (n + 1 - j)) * Vb p n (pairX p n lam) j ∧
      |(addOp p n a b).getD 0 0| ≤ (1 + u p) * (Zb + pairR p n lam + ∑ j ∈ Ioc 1 n, Vb p n (pairX p n lam) j) ∧
      (∀ i, 1 ≤ i → i ≤ n - 1 → |(addOp p n a b).getD i 0| ≤
        (1 + u p) * (u p * |(addOp p n a b).getD (i - 1) 0| + ∑ j ∈ Ioc i n, Vb p n (pairX p n lam) j)) ∧
      (∀ x ∈ LState.init :: (runOps p n (addOps p n a b) LState.init).1, ∀ m ≤ n, |x.s m| ≤ pairX p n lam m) ∧
      |∑ i ∈ range n, (a i + b i) - ∑ m ∈ range (n + 1), addLevels p n a b m| ≤ pairR p n lam ∧
      (∀ m < n, opsT (addOps p n a b) m = m) ∧ opsQ (addOps p n a b) = n - 1 := by
  have hu := u_pos p
  set g : ℕ → ℝ × ℝ := fun i => twoSum p (a i) (b i) with hg
  have hfa : ∀ i < n, _ := fun i hi => facts_a p hp (ha i hi) (hb i hi)
  have hF : ∀ i < n, F p (g i).1 ∧ F p (g i).2 := fun i _ => ⟨F_twoSum_fst p _ _, F_twoSum_snd p _ _⟩
  have hs : ∀ i < n, |(g i).1| ≤ (1 + u p) * lam i := fun i hi =>
    (abs_RN_le p _).trans (mul_le_mul_of_nonneg_left (hlam i hi) (by linarith))
  have ht : ∀ i < n, |(g i).2| ≤ u p * lam i := fun i hi =>
    ((hfa i hi).2.1.trans (min_le_right _ _)).trans ((mul_le_mul_of_nonneg_right (us_le_u p) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hlam i hi) hu.le))
  have hZg : ∑ i ∈ range n, ((g i).1 + (g i).2) = ∑ i ∈ range n, (a i + b i) :=
    sum_congr rfl fun i hi => (hfa i (mem_range.mp hi)).1
  obtain ⟨r1, r2, r3⟩ := pairOps_result p n hp hn g lam hF hs ht hA3 Zb (by rw [hZg]; exact hZ)
  obtain ⟨c1, c2, c3, c4, -⟩ := pairOps_levels p n hp hn g lam hF hs ht hA3
  rw [hZg] at r1 c2
  exact ⟨r1, r2, r3, c1, c2, c3, c4⟩

/-- Lemma 13 for MULF, with `|a_m| ≤ α_m`, `|b| ≤ β_0` and `λ_m = α_m β_0` -/
theorem lemma13_mulf (hp : 1 < p) (hn : 1 ≤ n) (a : ℕ → ℝ) (b : ℝ) (ha : ∀ i < n, F p (a i)) (hb : F p b)
    (α : ℕ → ℝ) (β0 : ℝ) (hα : ∀ m < n, |a m| ≤ α m) (hβ : |b| ≤ β0) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (Zb : ℝ)
    (hZ : |∑ i ∈ range n, a i * b| ≤ Zb) :
    |∑ i ∈ range n, a i * b - (mulfOp p n a b).sum| ≤ u p ^ n * Zb + (1 + u p ^ n) * pairR p n (fun m => α m * β0) +
        ∑ j ∈ Ioc 0 n, (u p ^ n + u p ^ (n + 1 - j)) * Vb p n (pairX p n fun m => α m * β0) j ∧
      |(mulfOp p n a b).getD 0 0| ≤
        (1 + u p) * (Zb + pairR p n (fun m => α m * β0) + ∑ j ∈ Ioc 1 n, Vb p n (pairX p n fun m => α m * β0) j) ∧
      (∀ i, 1 ≤ i → i ≤ n - 1 → |(mulfOp p n a b).getD i 0| ≤
        (1 + u p) * (u p * |(mulfOp p n a b).getD (i - 1) 0| +
          ∑ j ∈ Ioc i n, Vb p n (pairX p n fun m => α m * β0) j)) ∧
      (∀ x ∈ LState.init :: (runOps p n (mulfOps p n a b) LState.init).1, ∀ m ≤ n,
        |x.s m| ≤ pairX p n (fun m => α m * β0) m) ∧
      |∑ i ∈ range n, a i * b - ∑ m ∈ range (n + 1), mulfLevels p n a b m| ≤ pairR p n (fun m => α m * β0) ∧
      (∀ m < n, opsT (mulfOps p n a b) m = m) ∧ opsQ (mulfOps p n a b) = n - 1 := by
  have hu := u_pos p
  set g : ℕ → ℝ × ℝ := fun i => twoProd p (a i) b with hg
  have hfc : ∀ i < n, _ := fun i hi => facts_c p (ha i hi) hb
  have hab : ∀ i < n, |a i * b| ≤ α i * β0 := fun i hi => by
    rw [abs_mul]
    exact mul_le_mul (hα i hi) hβ (abs_nonneg _) ((abs_nonneg _).trans (hα i hi))
  have hF : ∀ i < n, F p (g i).1 ∧ F p (g i).2 := fun i _ => ⟨F_RN p _, F_RN p _⟩
  have hs : ∀ i < n, |(g i).1| ≤ (1 + u p) * (α i * β0) := fun i hi =>
    (hfc i hi).2.2.trans (mul_le_mul_of_nonneg_left (hab i hi) (by linarith))
  have ht : ∀ i < n, |(g i).2| ≤ u p * (α i * β0) := fun i hi =>
    (hfc i hi).2.1.trans ((mul_le_mul_of_nonneg_right (us_le_u p) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hab i hi) hu.le))
  have hZg : ∑ i ∈ range n, ((g i).1 + (g i).2) = ∑ i ∈ range n, a i * b :=
    sum_congr rfl fun i hi => (hfc i (mem_range.mp hi)).1
  obtain ⟨r1, r2, r3⟩ := pairOps_result p n hp hn g _ hF hs ht hA3 Zb (by rw [hZg]; exact hZ)
  obtain ⟨c1, c2, c3, c4, -⟩ := pairOps_levels p n hp hn g _ hF hs ht hA3
  rw [hZg] at r1 c2
  exact ⟨r1, r2, r3, c1, c2, c3, c4⟩

end ExpansionBounds
