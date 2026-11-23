import ExpansionBounds.SharpMul

/-!
# Theorem 19: DIV

DIV sets `r^{(0)} = a` and `q_k = RN(r^{(k)}_0/b_0)`, with `r^{(k+1)} = SMF(r^{(k)}, b, q_k)` for `k < n`, and returns
`Ren_n(q_0, …, q_n)`. SMF is a program of Lemma 11: `s_i = RN(r_i - p_i)` for `i < n` with
`(p_i, w_i) = TwoProd(b_i, q)` and `(s_i, t_i) = TwoSum(r_i, -p_i)`, `s_n ← t_{n-1}` and a rounding of `-w_{n-1}`, and
the deps of `t_l` and `-w_l` at level `l + 1`, so `T_m = 2m` and `Q = 2n - 1`. In units of `|a_0|`, part bounds `P` of
the remainder give the level inputs `A_m`, Lemma 11 the levels, Theorem 9 (b) and (d) the update's error `ε` and Lemma
12 the part bounds of the next remainder. Summing the updates, `a - b∑_{k ≤ n} q_k = r^{(n)} - q_nb + ∑_k ε_k`, and the
last renormalization adds the error of Theorem 9 (b) with `k = 0`.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) (n : ℕ)

/-- SMF's `TwoSum(r_i, -p_i) = (s_i, t_i)`, with `(p_i, w_i) = TwoProd(b_i, q)` -/
noncomputable def smfST (r b : ℕ → ℝ) (q : ℝ) (i : ℕ) : ℝ × ℝ := twoSum p (r i) (-(twoProd p (b i) q).1)

/-- SMF's program: `s_i = RN(r_i - p_i)` for `i < n`, `s_n ← t_{n-1}`, `s_n ← RN(s_n - w_{n-1})`, and
`dep(s, l + 1, t_l)`, `dep(s, l + 1, -w_l)` for `l = 0, …, n - 2` -/
noncomputable def smfOps (r b : ℕ → ℝ) (q : ℝ) : List LOp :=
  ((List.range n).map fun i => LOp.assign i (smfST p r b q i).1) ++
    [LOp.assign n (smfST p r b q (n - 1)).2, LOp.round (-(twoProd p (b (n - 1)) q).2)] ++
    (List.range (n - 1)).flatMap fun l =>
      [LOp.dep (l + 1) (smfST p r b q l).2, LOp.dep (l + 1) (-(twoProd p (b l) q).2)]

/-- SMF's levels at the end -/
noncomputable def smfLevels (r b : ℕ → ℝ) (q : ℝ) : ℕ → ℝ := (runOps p n (smfOps p n r b q) LState.init).2.s

/-- SMF: `Ren_n` of its levels -/
noncomputable def smfOp (r b : ℕ → ℝ) (q : ℝ) : List ℝ := ren p n n (smfLevels p n r b q)

/-- `T_m = 2m` -/
def divT (m : ℕ) : ℕ := 2 * m

theorem smfOps_counts (hn : 1 ≤ n) (r b : ℕ → ℝ) (q : ℝ) :
    (∀ m < n, opsT (smfOps p n r b q) m = divT m) ∧ opsQ (smfOps p n r b q) = 2 * n - 1 := by
  have hT : ∀ m, opsT ((List.range (n - 1)).flatMap fun l =>
      [LOp.dep (l + 1) (smfST p r b q l).2, LOp.dep (l + 1) (-(twoProd p (b l) q).2)]) m = 2 * min (n - 1) m := by
    intro m
    simp only [opsT, list_sum_flatMap, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, opT]
    rw [← count_le (n - 1) m, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun l _ => ?_
    split_ifs <;> rfl
  refine ⟨fun m hm => ?_, ?_⟩
  · have h1 : opsT (smfOps p n r b q) m = opsT ((List.range (n - 1)).flatMap fun l =>
        [LOp.dep (l + 1) (smfST p r b q l).2, LOp.dep (l + 1) (-(twoProd p (b l) q).2)]) m := by
      simp only [opsT, smfOps, List.map_append, List.sum_append, List.map_map, Function.comp_def, opT,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      simp
    rw [h1, hT, divT, min_eq_right (by omega)]
  · have h1 : opsQ (smfOps p n r b q) = 1 + 2 * (n - 1) := by
      simp only [opsQ, smfOps, List.map_append, List.sum_append, List.map_map, Function.comp_def, opQ,
        list_sum_flatMap, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      simp
      ring
    rw [h1]
    omega

variable (ρ : ℝ)

/-- `G_0 = u(P_0 + q̄)` and `G_i = P_i + (1 + u)ρ^i q̄`, the bounds on `|r_i - p_i|` in units of `|a_0|` -/
noncomputable def divG (P : ℕ → ℝ) (qb : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then u p * (P 0 + qb) else P i + (1 + u p) * ρ ^ i * qb

/-- `A_0 = (1 + u)G_0`, `A_m = (1 + u)G_m + uG_{m-1} + uρ^{m-1}q̄` for `1 ≤ m < n` and `A_n = uG_{n-1} + uρ^{n-1}q̄` -/
noncomputable def divA (P : ℕ → ℝ) (qb : ℝ) (m : ℕ) : ℝ :=
  if m < n then
    (1 + u p) * divG p ρ P qb m + (if m = 0 then 0 else u p * divG p ρ P qb (m - 1) + u p * ρ ^ (m - 1) * qb)
  else if m = n then u p * divG p ρ P qb (n - 1) + u p * ρ ^ (n - 1) * qb else 0

variable [Prec_gt_0 p]

omit [Prec_gt_0 p] in
theorem sum_succ_eq (f : ℕ → ℝ) (N m : ℕ) :
    (∑ x ∈ range N, if x + 1 = m then f x else 0) = if 1 ≤ m ∧ m ≤ N then f (m - 1) else 0 := by
  rcases m with _ | m
  · simp
  · simp only [Nat.add_right_cancel_iff, sum_ite_eq', mem_range]
    by_cases h : m < N
    · simp [h, show 1 ≤ m + 1 ∧ m + 1 ≤ N by omega]
    · simp only [h, ite_false]
      simp only [show ¬(1 ≤ m + 1 ∧ m + 1 ≤ N) by omega, ite_false]

/-- the inputs of SMF's levels are within `A_m M`, for part bounds `|r_i| ≤ P_iM`, `q = RN(r_0/b_0)` and
`|b_i| ≤ ρ^i|b_0|` -/
theorem smfOps_A (hp : 1 < p) (hn : 1 ≤ n) (hρ : 0 ≤ ρ) {M : ℝ} (r b P : ℕ → ℝ) (hr : ∀ i < n, F p (r i))
    (hb : ∀ i < n, F p (b i)) (hP : ∀ i < n, |r i| ≤ P i * M) (hbH : ∀ i < n, |b i| ≤ ρ ^ i * |b 0|)
    (hb0 : b 0 ≠ 0) (m : ℕ) :
    opsA n (smfOps p n r b (RN p (r 0 / b 0))) m ≤ M * divA p n ρ P ((1 + u p) * P 0) m := by
  have hu := u_pos p
  have hus := us_le_u p
  set q := RN p (r 0 / b 0) with hqd
  set qb := (1 + u p) * P 0 with hqb
  have hb0' : 0 < |b 0| := abs_pos.mpr hb0
  have hq : |q * b 0| ≤ qb * M := by
    have h1 : |q| ≤ (1 + u p) * |r 0 / b 0| := abs_RN_le p _
    rw [abs_div] at h1
    rw [abs_mul]
    calc |q| * |b 0| ≤ (1 + u p) * (|r 0| / |b 0|) * |b 0| := mul_le_mul_of_nonneg_right h1 hb0'.le
      _ = (1 + u p) * |r 0| := by field_simp
      _ ≤ (1 + u p) * (P 0 * M) := mul_le_mul_of_nonneg_left (hP 0 (by omega)) (by linarith)
      _ = qb * M := by rw [hqb]; ring
  have hbq : ∀ i < n, |b i * q| ≤ ρ ^ i * (qb * M) := fun i hi => by
    rw [abs_mul]
    calc |b i| * |q| ≤ ρ ^ i * |b 0| * |q| := mul_le_mul_of_nonneg_right (hbH i hi) (abs_nonneg _)
      _ = ρ ^ i * |q * b 0| := by rw [abs_mul]; ring
      _ ≤ ρ ^ i * (qb * M) := mul_le_mul_of_nonneg_left hq (pow_nonneg hρ i)
  have hF : F p q := F_RN p _
  have hw : ∀ i < n, |(twoProd p (b i) q).2| ≤ u p * ρ ^ i * (qb * M) := fun i hi => by
    calc _ ≤ us p * |b i * q| := (facts_c p (hb i hi) hF).2.1
      _ ≤ u p * (ρ ^ i * (qb * M)) := mul_le_mul hus (hbq i hi) (abs_nonneg _) hu.le
      _ = _ := by ring
  have hpp : ∀ i < n, |(twoProd p (b i) q).1| ≤ (1 + u p) * (ρ ^ i * (qb * M)) := fun i hi =>
    (facts_c p (hb i hi) hF).2.2.trans (mul_le_mul_of_nonneg_left (hbq i hi) (by linarith))
  have hG : ∀ i < n, |r i + -(twoProd p (b i) q).1| ≤ divG p ρ P qb i * M := fun i hi => by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have hsum := (facts_c p (hb 0 hi) hF).1
      have hrq : |r 0 - b 0 * q| ≤ u p * (P 0 * M) := by
        have h1 : |q - r 0 / b 0| ≤ us p * |r 0 / b 0| := abs_RN_sub_le_us p (r 0 / b 0)
        have h2 : r 0 - b 0 * q = -(b 0 * (q - r 0 / b 0)) := by field_simp; ring
        rw [h2, abs_neg, abs_mul]
        calc |b 0| * |q - r 0 / b 0| ≤ |b 0| * (us p * |r 0 / b 0|) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
          _ = us p * |r 0| := by rw [abs_div]; field_simp
          _ ≤ u p * (P 0 * M) := mul_le_mul hus (hP 0 hi) (abs_nonneg _) hu.le
      have h0 : r 0 + -(twoProd p (b 0) q).1 = (r 0 - b 0 * q) + (twoProd p (b 0) q).2 := by linarith
      have hw0 := hw 0 hi
      simp only [pow_zero, mul_one] at hw0
      simp only [divG, ite_true]
      rw [h0]
      calc _ ≤ |r 0 - b 0 * q| + |(twoProd p (b 0) q).2| := abs_add_le _ _
        _ ≤ u p * (P 0 * M) + u p * (qb * M) := add_le_add hrq hw0
        _ = u p * (P 0 + qb) * M := by ring
    · simp only [divG, show i ≠ 0 by omega, ite_false]
      calc _ ≤ |r i| + |-(twoProd p (b i) q).1| := abs_add_le _ _
        _ ≤ P i * M + (1 + u p) * (ρ ^ i * (qb * M)) := add_le_add (hP i hi) (by rw [abs_neg]; exact hpp i hi)
        _ = (P i + (1 + u p) * ρ ^ i * qb) * M := by ring
  have hs : ∀ i < n, |(smfST p r b q i).1| ≤ (1 + u p) * (divG p ρ P qb i * M) := fun i hi =>
    (abs_RN_le p _).trans (mul_le_mul_of_nonneg_left (hG i hi) (by linarith))
  have ht : ∀ i < n, |(smfST p r b q i).2| ≤ u p * (divG p ρ P qb i * M) := fun i hi => by
    have := (facts_a p hp (hr i hi) (F_neg p (F_RN p (b i * q)))).2.1
    exact (this.trans (min_le_right _ _)).trans (mul_le_mul hus (hG i hi) (abs_nonneg _) hu.le)
  simp only [opsA, smfOps, List.map_append, List.sum_append, List.map_map, Function.comp_def, opA,
    list_sum_flatMap, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, list_sum_map_range_gen,
    sum_add_distrib, sum_succ_eq, sum_ite_eq', mem_range, abs_neg]
  unfold divA
  rcases lt_trichotomy m n with hlt | rfl | hgt
  · simp only [hlt, ite_true, show n ≠ m by omega, show m ≠ n by omega, ite_false, add_zero]
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp only [show ¬(1 ≤ 0 ∧ 0 ≤ n - 1) by omega, ite_false, ite_true, add_zero]
      linarith [hs 0 hlt]
    · simp only [show 1 ≤ m ∧ m ≤ n - 1 by omega, and_self, ite_true, show m ≠ 0 by omega, ite_false]
      have h1 := ht (m - 1) (by omega)
      have h2 := hw (m - 1) (by omega)
      have h3 := hs m hlt
      nlinarith
  · simp only [lt_irrefl, ite_true, ite_false, show ¬(1 ≤ m ∧ m ≤ m - 1) by omega, add_zero, zero_add]
    have h1 := ht (m - 1) (by omega)
    have h2 := hw (m - 1) (by omega)
    nlinarith
  · simp only [show ¬m < n by omega, show n ≠ m by omega, show m ≠ n by omega,
      show ¬(1 ≤ m ∧ m ≤ n - 1) by omega, ite_false, add_zero, mul_zero, le_refl]

omit [Prec_gt_0 p] in
/-- `X_m` of Lemma 11 for SMF, with its `A_m`, `T_m = 2m` and `Q = 2n - 1`, in units of `|a_0|` -/
noncomputable def divX (P : ℕ → ℝ) (m : ℕ) : ℝ :=
  if m < n then levX (divA p n ρ P ((1 + u p) * P 0)) divT (u p) m
  else levD (divA p n ρ P ((1 + u p) * P 0)) divT (u p) n / (1 - ((2 * n - 1 : ℕ) : ℝ) * u p)

omit [Prec_gt_0 p] in
/-- `R = QuX_n` -/
noncomputable def divR (P : ℕ → ℝ) : ℝ := ((2 * n - 1 : ℕ) : ℝ) * u p * divX p n ρ P n

omit [Prec_gt_0 p] in
/-- SMF's assignments, those to the levels `0, …, n`, come first -/
theorem smfOps_assigns (r b : ℕ → ℝ) (q : ℝ) : smfOps p n r b q =
    ((List.range (n + 1)).map fun i =>
        LOp.assign i (if i < n then (smfST p r b q i).1 else (smfST p r b q (n - 1)).2)) ++
      (LOp.round (-(twoProd p (b (n - 1)) q).2) :: (List.range (n - 1)).flatMap fun l =>
        [LOp.dep (l + 1) (smfST p r b q l).2, LOp.dep (l + 1) (-(twoProd p (b l) q).2)]) := by
  rw [smfOps, List.range_succ, List.map_append]
  simp only [List.map_cons, List.map_nil, lt_irrefl, ite_false, List.append_assoc, List.cons_append,
    List.nil_append]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  simp [hi]

omit [Prec_gt_0 p] in
/-- SMF puts in `∑_i (r_i - b_iq)` -/
theorem smfOps_Y (hp : 1 < p) (hn : 1 ≤ n) (r b : ℕ → ℝ) (q : ℝ) (hr : ∀ i < n, F p (r i))
    (hb : ∀ i < n, F p (b i)) (hq : F p q) [Prec_gt_0 p] :
    opsY (smfOps p n r b q) = ∑ i ∈ range n, (r i - b i * q) := by
  simp only [opsY, smfOps, List.map_append, List.sum_append, List.map_map, Function.comp_def, opY,
    list_sum_flatMap, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, list_sum_map_range_gen]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h : ∀ i < k + 1, (smfST p r b q i).1 + (smfST p r b q i).2 + -(twoProd p (b i) q).2 = r i - b i * q :=
    fun i hi => by
      have hpF : F p (-(twoProd p (b i) q).1) := F_neg p (F_RN p _)
      have h1 := (facts_a p hp (hr i hi) hpF).1
      have h2 := (facts_c p (hb i hi) hq).1
      simp only [smfST] at h1 ⊢
      linarith
  rw [← sum_congr rfl fun i hi => h i (mem_range.mp hi)]
  simp only [sum_range_succ, sum_add_distrib]
  ring

/-- Lemma 11 for SMF: its levels stay within `X_m M`, and they sum to within `RM` of `r - qb` -/
theorem smf_levels (hp : 1 < p) (hn : 1 ≤ n) (hQ : ((2 * n - 1 : ℕ) : ℝ) * u p < 1) (hρ : 0 ≤ ρ) {M : ℝ}
    (r b P : ℕ → ℝ) (hr : ∀ i < n, F p (r i)) (hb : ∀ i < n, F p (b i))
    (hP : ∀ i < n, |r i| ≤ P i * M) (hbH : ∀ i < n, |b i| ≤ ρ ^ i * |b 0|) (hb0 : b 0 ≠ 0) :
    (∀ m ≤ n, |smfLevels p n r b (RN p (r 0 / b 0)) m| ≤ M * divX p n ρ P m) ∧
      |(∑ i ∈ range n, (r i - b i * RN p (r 0 / b 0))) -
          ∑ m ∈ range (n + 1), smfLevels p n r b (RN p (r 0 / b 0)) m| ≤ M * divR p n ρ P ∧
      ∀ m, F p (smfLevels p n r b (RN p (r 0 / b 0)) m) := by
  have hu := u_pos p
  set q := RN p (r 0 / b 0) with hqd
  obtain ⟨cT, cQ⟩ := smfOps_counts p n hn r b q
  set ops := smfOps p n r b q with hops
  have hwf : ∀ o ∈ ops, o.wf p n := by
    intro o ho
    simp only [hops, smfOps, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap, List.mem_cons,
      List.mem_nil_iff, or_false] at ho
    rcases ho with ((⟨i, hi, rfl⟩ | rfl | rfl) | ⟨l, hl, rfl | rfl⟩)
    · exact ⟨by omega, F_RN p _⟩
    · exact ⟨le_rfl, F_RN p _⟩
    · trivial
    · exact ⟨by omega, F_RN p _⟩
    · exact ⟨by omega, F_neg p (F_RN p _)⟩
  have hok : (runOps p n ops LState.init).2.ok := by
    rw [hops, smfOps_assigns p n r b q, (runOps_append p n _ _ _).2, runOps_ok_noassign]
    · exact ((runOps_assigns p n _ (n + 1) LState.init fun _ _ => rfl).1).mpr trivial
    · intro o ho m y
      simp only [List.mem_cons, List.mem_flatMap, List.mem_range, List.mem_nil_iff, or_false] at ho
      rcases ho with rfl | ⟨l, -, rfl | rfl⟩ <;> simp
  have hTu : ∀ m < n, (opsT ops m : ℝ) * u p < 1 := by
    intro m hm
    rw [cT m hm, divT]
    have : ((2 * m : ℕ) : ℝ) ≤ ((2 * n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 * m ≤ 2 * n - 1)
    nlinarith
  have hQu : (opsQ ops : ℝ) * u p < 1 := by rw [cQ]; exact hQ
  obtain ⟨la, -, lc, ld⟩ := levels p n hp ops hwf hTu hQu hok
  have hA : ∀ m, opsA n ops m ≤ M * divA p n ρ P ((1 + u p) * P 0) m :=
    smfOps_A p n ρ hp hn hρ r b P hr hb hP hbH hb0
  have hD : ∀ m ≤ n, levD (opsA n ops) (opsT ops) (u p) m ≤
      M * levD (divA p n ρ P ((1 + u p) * P 0)) divT (u p) m := by
    intro m hm
    rw [levD_congr n (fun k hk => cT k hk) m hm, ← levD_smul]
    exact levD_mono hu.le hA n (fun k hk => by have := hTu k hk; rwa [cT k hk] at this) m hm
  have h1Q : 0 < 1 - ((2 * n - 1 : ℕ) : ℝ) * u p := by linarith
  have hXn : levD (opsA n ops) (opsT ops) (u p) n / (1 - (opsQ ops : ℝ) * u p) ≤ M * divX p n ρ P n := by
    simp only [divX, lt_irrefl, ite_false, cQ, mul_div_assoc']
    exact div_le_div_of_nonneg_right (hD n le_rfl) h1Q.le
  have hne : ops ≠ [] := by simp [hops, smfOps]
  have hlast := runOps_last_mem p n _ hne LState.init
  obtain ⟨hl1, hl2⟩ := la _ (List.mem_cons_of_mem _ hlast)
  refine ⟨fun m hm => ?_, ?_, fun m => ?_⟩
  · rcases Nat.lt_or_ge m n with hlt | hge
    · have h1 : 0 < 1 - (divT m : ℝ) * u p := by have := hTu m hlt; rw [cT m hlt] at this; linarith
      refine (hl1 m hlt).trans ?_
      simp only [divX, hlt, ite_true, levX, cT m hlt, mul_div_assoc']
      exact div_le_div_of_nonneg_right (hD m hlt.le) h1.le
    · obtain rfl : m = n := by omega
      exact hl2.trans hXn
  · show |_ - ∑ m ∈ range (n + 1), (runOps p n ops LState.init).2.s m| ≤ _
    rw [lc, smfOps_Y p n hp hn r b q hr hb (F_RN p _), sub_sub_cancel]
    have hr := runOps_rS p n ops LState.init (by simp [LState.init])
    refine hr.trans (ld.trans ?_)
    unfold divR
    rw [cQ, mul_assoc]
    rw [cQ] at hXn
    calc ((2 * n - 1 : ℕ) : ℝ) * (u p * (levD (opsA n ops) (opsT ops) (u p) n /
          (1 - ((2 * n - 1 : ℕ) : ℝ) * u p))) ≤ ((2 * n - 1 : ℕ) : ℝ) * (u p * (M * divX p n ρ P n)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXn hu.le) (Nat.cast_nonneg _)
      _ = M * (((2 * n - 1 : ℕ) : ℝ) * u p * divX p n ρ P n) := by ring
  · obtain ⟨-, -, -, h⟩ := runOps_spec p n hp ops LState.init hwf (init_inv p n)
    exact (h hok).2.1 m

omit [Prec_gt_0 p] in
/-- `V_0 = (1 + u)^n σ_0` and the `V_j` of Theorem 9 (d) for `j ≥ 1` -/
noncomputable def vB (X : ℕ → ℝ) (j : ℕ) : ℝ := if j = 0 then (1 + u p) ^ n * sigmaX n X 0 else Vb p n X j

omit [Prec_gt_0 p] in
/-- Theorem 9 (b)'s bound `ū^{n-k}V_k + ∑_{j > k} ū^{n+1-j}V_j` -/
noncomputable def renB (X : ℕ → ℝ) (k : ℕ) : ℝ :=
  us p ^ (n - k) * vB p n X k + ∑ j ∈ Ioc k n, us p ^ (n + 1 - j) * vB p n X j

omit [Prec_gt_0 p] in
/-- `min_{0 ≤ k ≤ n}` of Theorem 9 (b)'s bounds -/
noncomputable def renMin (X : ℕ → ℝ) : ℝ := (range (n + 1)).inf' nonempty_range_add_one (renB p n X)

omit [Prec_gt_0 p] in
/-- the update's error `ε = R + min_k B_k`, in units of `|a_0|` -/
noncomputable def divEps (P : ℕ → ℝ) : ℝ := divR p n ρ P + renMin p n (divX p n ρ P)

omit [Prec_gt_0 p] in
/-- the next remainder's part bounds, Lemma 12 with `|S| ≤ σ_0`: `P'_0 = (1 + u)(σ_0 + W_1)` and
`P'_i = (1 + u)(uP'_{i-1} + W_i)` -/
noncomputable def divP' (P : ℕ → ℝ) : ℕ → ℝ := gParts p n (divX p n ρ P) (sigmaX n (divX p n ρ P) 0) 0

/-- Theorem 9 (b) with every `k`: `Ren_n` of levels within `X_m M` loses at most `M min_k B_k` -/
theorem renErr_le_min (hp : 1 < p) (hn : 1 ≤ n) {M : ℝ} (hM : 0 ≤ M) (c X : ℕ → ℝ) (hc : ∀ i ≤ n, F p (c i))
    (hX : ∀ m ≤ n, |c m| ≤ M * X m) : |renErr p n c| ≤ M * renMin p n X := by
  have hu := u_pos p
  have hus := us_nonneg p
  obtain ⟨k, hk, hkeq⟩ := exists_mem_eq_inf' (nonempty_range_add_one (n := n)) (renB p n X)
  rw [renMin, hkeq]
  have hkn : k ≤ n := by simp at hk; omega
  have hv : ∀ j ≤ n, |vecSum p n c j| ≤ M * vB p n X j := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have h := (vecSum_bounds p hp n c hc).1
      have hσ : sigma n c 0 ≤ M * sigmaX n X 0 := by
        rw [sigma, sigmaX, mul_sum]
        exact sum_le_sum fun m hm => hX m (by simp at hm; omega)
      simp only [vB, ite_true]
      calc _ ≤ (1 + u p) ^ n * sigma n c 0 := h
        _ ≤ (1 + u p) ^ n * (M * sigmaX n X 0) := mul_le_mul_of_nonneg_left hσ (pow_nonneg (by linarith) _)
        _ = _ := by ring
    · simp only [vB, show j ≠ 0 by omega, ite_false]
      rw [← Vb_smul p n X hM]
      exact vecSum_le_V p hp n c hc _ hX j hj0 hj
  refine (renErr_le p hp n hn c hc k hkn).trans ?_
  rw [renB, mul_add, mul_sum]
  refine add_le_add ?_ (sum_le_sum fun j hj => ?_)
  · calc _ ≤ us p ^ (n - k) * (M * vB p n X k) := mul_le_mul_of_nonneg_left (hv k hkn) (pow_nonneg hus _)
      _ = _ := by ring
  · calc _ ≤ us p ^ (n + 1 - j) * (M * vB p n X j) :=
          mul_le_mul_of_nonneg_left (hv j (mem_Ioc.mp hj).2) (pow_nonneg hus _)
      _ = _ := by ring

/-- one update of DIV: `r' = SMF(r, b, q)` with `q = RN(r_0/b_0)` is within `εM` of `r - qb`, and its parts are
within `P'M` -/
theorem smf_step (hp : 1 < p) (hn : 1 ≤ n) (hQ : ((2 * n - 1 : ℕ) : ℝ) * u p < 1) (hρ : 0 ≤ ρ) {M : ℝ}
    (hM : 0 ≤ M) (r b P : ℕ → ℝ) (hr : ∀ i < n, F p (r i)) (hb : ∀ i < n, F p (b i))
    (hP : ∀ i < n, |r i| ≤ P i * M) (hbH : ∀ i < n, |b i| ≤ ρ ^ i * |b 0|) (hb0 : b 0 ≠ 0) :
    |(∑ i ∈ range n, (r i - b i * RN p (r 0 / b 0))) - (smfOp p n r b (RN p (r 0 / b 0))).sum| ≤
        M * divEps p n ρ P ∧
      (∀ i, |(smfOp p n r b (RN p (r 0 / b 0))).getD i 0| ≤ M * divP' p n ρ P i) ∧
      (∀ i, F p ((smfOp p n r b (RN p (r 0 / b 0))).getD i 0)) ∧ (smfOp p n r b (RN p (r 0 / b 0))).length ≤ n := by
  obtain ⟨hX, hE, hF⟩ := smf_levels p n ρ hp hn hQ hρ r b P hr hb hP hbH hb0
  set c := smfLevels p n r b (RN p (r 0 / b 0)) with hc
  have hren := renErr_le_min p n hp hn hM c (divX p n ρ P) (fun i _ => hF i) hX
  obtain ⟨l1, l2, -⟩ := ren_spec p n hn c (fun i _ => hF i)
  have hZ : |∑ m ∈ range (n + 1), c m| ≤ M * sigmaX n (divX p n ρ P) 0 := by
    rw [sigmaX, mul_sum, ← range_eq_Ico]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => hX m ?_)
    simp at hm; omega
  obtain ⟨-, r2, r3⟩ := ren_of_levels p hp n hn c (fun i _ => hF i) (fun m => M * divX p n ρ P m) hX
    (∑ m ∈ range (n + 1), c m) _ 0 hZ (by simp)
  refine ⟨?_, fun i => ?_, l2, l1⟩
  · have hsplit : (∑ i ∈ range n, (r i - b i * RN p (r 0 / b 0))) - (smfOp p n r b (RN p (r 0 / b 0))).sum =
        ((∑ i ∈ range n, (r i - b i * RN p (r 0 / b 0))) - ∑ m ∈ range (n + 1), c m) + renErr p n c := by
      simp only [renErr, smfOp, ← hc]
      ring
    rw [hsplit, divEps, mul_add]
    exact (abs_add_le _ _).trans (add_le_add hE hren)
  · have h := gParts_le p n _ _ _ _ l1 r2 r3 i
    have h2 := gParts_smul p n (divX p n ρ P) (sigmaX n (divX p n ρ P) 0) 0 hM i
    rw [mul_zero] at h2
    rw [h2] at h
    exact h

omit [Prec_gt_0 p] in
/-- DIV's remainders: `r^{(0)} = a` and `r^{(k+1)} = SMF(r^{(k)}, b, RN(r^{(k)}_0/b_0))` -/
noncomputable def divRem (a b : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => a
  | k + 1 => fun i => (smfOp p n (divRem a b k) b (RN p (divRem a b k 0 / b 0))).getD i 0

omit [Prec_gt_0 p] in
/-- DIV's quotient terms `q_k = RN(r^{(k)}_0/b_0)` -/
noncomputable def divQ (a b : ℕ → ℝ) (k : ℕ) : ℝ := RN p (divRem p n a b k 0 / b 0)

omit [Prec_gt_0 p] in
/-- DIV: `Ren_n(q_0, …, q_n)` -/
noncomputable def divOp (a b : ℕ → ℝ) : List ℝ := ren p n n (divQ p n a b)

omit [Prec_gt_0 p] in
/-- the remainders' part bounds in units of `|a_0|`: `P^{(0)}_i = ρ^i` and `P^{(k+1)} = P'(P^{(k)})` -/
noncomputable def divPk : ℕ → ℕ → ℝ
  | 0 => fun i => ρ ^ i
  | k + 1 => divP' p n ρ (divPk k)

omit [Prec_gt_0 p] in
/-- `q̄_k = (1 + u)P^{(k)}_0`, the bound on `|q_kb_0|` in units of `|a_0|`: `|q_kb_0| ≤ q̄_k|a_0|` -/
noncomputable def divQb (k : ℕ) : ℝ := (1 + u p) * divPk p n ρ k 0

omit [Prec_gt_0 p] in
/-- `Θ = Θ_0 + ∑_{k=1}^n ε_k` with `Θ_0 = ∑_{i ≥ 1} P^{(n)}_i + uP^{(n)}_0 + q̄_nρ/(1 - ρ)` -/
noncomputable def divTheta : ℝ :=
  ∑ i ∈ range (n - 1), divPk p n ρ n (i + 1) + u p * divPk p n ρ n 0 + divQb p n ρ n * (ρ / (1 - ρ)) +
    ∑ k ∈ range n, divEps p n ρ (divPk p n ρ k)

omit [Prec_gt_0 p] in
/-- `Ξ = ∑_{j=1}^n (u^n + u^{n+1-j})V^q_j`, the `V^q_j` from `X_m = q̄_m` -/
noncomputable def divXi : ℝ := ∑ j ∈ Ioc 0 n, (u p ^ n + u p ^ (n + 1 - j)) * Vb p n (divQb p n ρ) j

omit [Prec_gt_0 p] in
/-- `κ_DIV = ((1 + u^n)Θ(1 - ρ)/(1 - 2ρ) + Ξ)/((1 - 2ρ)u^{n+1})` -/
noncomputable def kdiv : ℝ :=
  ((1 + u p ^ n) * divTheta p n ρ * ((1 - ρ) / (1 - 2 * ρ)) + divXi p n ρ) / ((1 - 2 * ρ) * u p ^ (n + 1))

omit [Prec_gt_0 p] in
/-- the bounds are nonnegative -/
theorem divX_nonneg (hn : 1 ≤ n) (hQ : ((2 * n - 1 : ℕ) : ℝ) * u p < 1) (hρ : 0 ≤ ρ) {P : ℕ → ℝ}
    (hP : ∀ i, 0 ≤ P i) (m : ℕ) : 0 ≤ divX p n ρ P m := by
  have hu := u_pos p
  have hA : ∀ k, 0 ≤ divA p n ρ P ((1 + u p) * P 0) k := fun k => by
    have hqb : 0 ≤ (1 + u p) * P 0 := mul_nonneg (by linarith) (hP 0)
    have hG : ∀ i, 0 ≤ divG p ρ P ((1 + u p) * P 0) i := fun i => by
      unfold divG
      split_ifs
      · exact mul_nonneg hu.le (add_nonneg (hP 0) hqb)
      · exact add_nonneg (hP i) (mul_nonneg (mul_nonneg (by linarith) (pow_nonneg hρ i)) hqb)
    unfold divA
    split_ifs
    · exact add_nonneg (mul_nonneg (by linarith) (hG k)) le_rfl
    · exact add_nonneg (mul_nonneg (by linarith) (hG k))
        (add_nonneg (mul_nonneg hu.le (hG _)) (mul_nonneg (mul_nonneg hu.le (pow_nonneg hρ _)) hqb))
    · exact add_nonneg (mul_nonneg hu.le (hG _)) (mul_nonneg (mul_nonneg hu.le (pow_nonneg hρ _)) hqb)
    · exact le_rfl
  have hT : ∀ k < n, (divT k : ℝ) * u p < 1 := fun k hk => by
    have : ((divT k : ℕ) : ℝ) ≤ ((2 * n - 1 : ℕ) : ℝ) := by exact_mod_cast (by unfold divT; omega)
    nlinarith
  unfold divX
  split_ifs with hm
  · exact div_nonneg (levD_nonneg hA hu.le m fun k hk => hT k (by omega)) (by linarith [hT m hm])
  · exact div_nonneg (levD_nonneg hA hu.le n hT) (by linarith)

omit [Prec_gt_0 p] in
theorem divPk_nonneg (hn : 1 ≤ n) (hQ : ((2 * n - 1 : ℕ) : ℝ) * u p < 1) (hρ : 0 ≤ ρ) :
    ∀ k i, 0 ≤ divPk p n ρ k i
  | 0, i => pow_nonneg hρ i
  | k + 1, i => gParts_nonneg p n (divX_nonneg p n ρ hn hQ hρ (divPk_nonneg hn hQ hρ k)) (sum_nonneg fun m _ =>
      divX_nonneg p n ρ hn hQ hρ (divPk_nonneg hn hQ hρ k) m) le_rfl i

omit [Prec_gt_0 p] in
theorem divEps_nonneg (hn : 1 ≤ n) (hQ : ((2 * n - 1 : ℕ) : ℝ) * u p < 1) (hρ : 0 ≤ ρ) {P : ℕ → ℝ}
    (hP : ∀ i, 0 ≤ P i) : 0 ≤ divEps p n ρ P := by
  have hX := divX_nonneg p n ρ hn hQ hρ hP
  have hu := u_pos p
  have hv : ∀ j, 0 ≤ vB p n (divX p n ρ P) j := fun j => by
    unfold vB
    split_ifs
    · exact mul_nonneg (pow_nonneg (by linarith) _) (sum_nonneg fun m _ => hX m)
    · exact Vb_nonneg p n hX j
  refine add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hu.le) (hX n)) ?_
  refine le_inf' _ _ fun k _ => add_nonneg (mul_nonneg (pow_nonneg (us_nonneg p) _) (hv k))
    (sum_nonneg fun j _ => mul_nonneg (pow_nonneg (us_nonneg p) _) (hv j))

omit [Prec_gt_0 p] in
/-- `ρ + ρ² + … + ρ^{n-1} ≤ ρ/(1 - ρ)` -/
theorem geom_tail_le {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (k : ℕ) : ∑ i ∈ range k, ρ ^ (i + 1) ≤ ρ / (1 - ρ) := by
  have h := geom_le ρ hρ hρ1 k
  simp only [pow_succ, ← sum_mul]
  rw [div_eq_mul_one_div, mul_comm ρ]
  exact mul_le_mul_of_nonneg_right h hρ

/-- `q = RN(r_0/b_0)` has `|r_0 - b_0q| ≤ ū|r_0|` and `|qb_0| ≤ (1 + u)|r_0|` -/
theorem rem_quot {r0 b0 : ℝ} (hb0 : b0 ≠ 0) :
    |r0 - b0 * RN p (r0 / b0)| ≤ us p * |r0| ∧ |RN p (r0 / b0) * b0| ≤ (1 + u p) * |r0| := by
  have hb0' : 0 < |b0| := abs_pos.mpr hb0
  constructor
  · have h1 : |RN p (r0 / b0) - r0 / b0| ≤ us p * |r0 / b0| := abs_RN_sub_le_us p (r0 / b0)
    have h2 : r0 - b0 * RN p (r0 / b0) = -(b0 * (RN p (r0 / b0) - r0 / b0)) := by field_simp; ring
    rw [h2, abs_neg, abs_mul]
    calc |b0| * |RN p (r0 / b0) - r0 / b0| ≤ |b0| * (us p * |r0 / b0|) := mul_le_mul_of_nonneg_left h1 hb0'.le
      _ = us p * |r0| := by rw [abs_div]; field_simp
  · have h1 : |RN p (r0 / b0)| ≤ (1 + u p) * |r0 / b0| := abs_RN_le p _
    rw [abs_div] at h1
    rw [abs_mul]
    calc |RN p (r0 / b0)| * |b0| ≤ (1 + u p) * (|r0| / |b0|) * |b0| := mul_le_mul_of_nonneg_right h1 hb0'.le
      _ = (1 + u p) * |r0| := by field_simp

/-- Theorem 19: DIV of `a` and `b` on `H(θ)` with `0 ≤ θ`, `2θu < 1`, `b_0 ≠ 0` and `(2n - 1)u < 1` errs by at most
`(u^n + κ_DIV u^{n+1})|a/b|`; `Htheta` states only the part inequalities, so the range of `θ`, which the paper's
domain implies, is explicit -/
theorem thm19 (hp : 1 < p) (hn : 1 ≤ n) (hQ : ((2 * n - 1 : ℕ) : ℝ) * u p < 1) {θ : ℝ} (hθ : 0 ≤ θ)
    (hρ : 2 * (θ * u p) < 1) (a b : ℕ → ℝ) (ha : ∀ i < n, F p (a i)) (hb : ∀ i < n, F p (b i))
    (haH : Htheta p n θ a) (hbH : Htheta p n θ b) (hb0 : b 0 ≠ 0) :
    |(∑ i ∈ range n, a i) / (∑ i ∈ range n, b i) - (divOp p n a b).sum| ≤
      (u p ^ n + kdiv p n (θ * u p) * u p ^ (n + 1)) * |(∑ i ∈ range n, a i) / ∑ i ∈ range n, b i| := by
  have hu := u_pos p
  have hus := us_le_u p
  set ρ := θ * u p with hρd
  have hρ0 : 0 ≤ ρ := mul_nonneg hθ hu.le
  have hρ1 : ρ < 1 := by linarith
  set M := |a 0| with hMd
  have hM : 0 ≤ M := abs_nonneg _
  set A := ∑ i ∈ range n, a i with hAd
  set B := ∑ i ∈ range n, b i with hBd
  have hb0' : 0 < |b 0| := abs_pos.mpr hb0
  have hbH' : ∀ i < n, |b i| ≤ ρ ^ i * |b 0| := Htheta_le p n hbH
  have hPk := divPk_nonneg p n ρ hn hQ hρ0
  -- the remainders stay within `P^{(k)}M`
  have hrem : ∀ k, (∀ i < n, F p (divRem p n a b k i)) ∧ ∀ i < n, |divRem p n a b k i| ≤ divPk p n ρ k i * M := by
    intro k
    induction k with
    | zero => exact ⟨ha, fun i hi => Htheta_le p n haH i hi⟩
    | succ k ih =>
      obtain ⟨-, h2, h3, -⟩ := smf_step p n ρ hp hn hQ hρ0 hM _ b _ ih.1 hb ih.2 hbH' hb0
      exact ⟨fun i _ => h3 i, fun i _ => by rw [mul_comm]; exact h2 i⟩
  -- each update errs by at most `ε_kM`
  set R : ℕ → ℝ := fun k => ∑ i ∈ range n, divRem p n a b k i with hR
  set e : ℕ → ℝ := fun k => (R k - divQ p n a b k * B) - R (k + 1) with he
  have hek : ∀ k, |e k| ≤ M * divEps p n ρ (divPk p n ρ k) := by
    intro k
    obtain ⟨h1, -, -, h4⟩ := smf_step p n ρ hp hn hQ hρ0 hM _ b _ (hrem k).1 hb (hrem k).2 hbH' hb0
    have hsum : R (k + 1) = (smfOp p n (divRem p n a b k) b (RN p (divRem p n a b k 0 / b 0))).sum :=
      (list_sum_getD _ n h4).symm
    have hlhs : e k = (∑ i ∈ range n, (divRem p n a b k i - b i * RN p (divRem p n a b k 0 / b 0))) -
        (smfOp p n (divRem p n a b k) b (RN p (divRem p n a b k 0 / b 0))).sum := by
      show R k - divQ p n a b k * B - R (k + 1) = _
      rw [hsum, sum_sub_distrib, ← sum_mul]
      simp only [hR, hBd, divQ]
      ring
    rw [hlhs]
    exact h1
  -- `a - b∑_{k<N} q_k = r^{(N)} + ∑_{k<N} e_k`
  have htel : ∀ N, A - B * ∑ k ∈ range N, divQ p n a b k = R N + ∑ k ∈ range N, e k := by
    intro N
    induction N with
    | zero => simp [hR, hAd, divRem]
    | succ N ih =>
      rw [sum_range_succ, sum_range_succ, mul_add, ← sub_sub, ih]
      simp only [he]
      ring
  -- `|r^{(n)} - q_nb| ≤ Θ_0M`
  have hlast : |R n - divQ p n a b n * B| ≤ (∑ i ∈ range (n - 1), divPk p n ρ n (i + 1) +
      u p * divPk p n ρ n 0 + divQb p n ρ n * (ρ / (1 - ρ))) * M := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨q1, q2⟩ := rem_quot p (r0 := divRem p (k + 1) a b (k + 1) 0) hb0
    have hsplit : R (k + 1) - divQ p (k + 1) a b (k + 1) * B =
        (divRem p (k + 1) a b (k + 1) 0 - b 0 * divQ p (k + 1) a b (k + 1)) +
          ∑ i ∈ range k, divRem p (k + 1) a b (k + 1) (i + 1) -
            divQ p (k + 1) a b (k + 1) * ∑ i ∈ range k, b (i + 1) := by
      rw [hR, hBd]
      simp only [sum_range_succ']
      ring
    have hr1 : |∑ i ∈ range k, divRem p (k + 1) a b (k + 1) (i + 1)| ≤
        (∑ i ∈ range k, divPk p (k + 1) ρ (k + 1) (i + 1)) * M := by
      rw [sum_mul]
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => (hrem (k + 1)).2 (i + 1) (by simp at hi; omega))
    have hb1 : |divQ p (k + 1) a b (k + 1) * ∑ i ∈ range k, b (i + 1)| ≤
        divQb p (k + 1) ρ (k + 1) * M * (ρ / (1 - ρ)) := by
      rw [abs_mul]
      have hs : |∑ i ∈ range k, b (i + 1)| ≤ |b 0| * (ρ / (1 - ρ)) := by
        refine (abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ i ∈ range k, |b (i + 1)| ≤ ∑ i ∈ range k, |b 0| * ρ ^ (i + 1) :=
              sum_le_sum fun i hi => by rw [mul_comm]; exact hbH' (i + 1) (by simp at hi; omega)
          _ = |b 0| * ∑ i ∈ range k, ρ ^ (i + 1) := by rw [mul_sum]
          _ ≤ |b 0| * (ρ / (1 - ρ)) := mul_le_mul_of_nonneg_left (geom_tail_le hρ0 hρ1 k) hb0'.le
      have hq : |divQ p (k + 1) a b (k + 1)| * |b 0| ≤ divQb p (k + 1) ρ (k + 1) * M := by
        rw [← abs_mul]
        refine q2.trans ?_
        rw [divQb, mul_assoc]
        exact mul_le_mul_of_nonneg_left ((hrem (k + 1)).2 0 (by omega)) (by linarith)
      calc |divQ p (k + 1) a b (k + 1)| * |∑ i ∈ range k, b (i + 1)| ≤
            |divQ p (k + 1) a b (k + 1)| * (|b 0| * (ρ / (1 - ρ))) :=
            mul_le_mul_of_nonneg_left hs (abs_nonneg _)
        _ = |divQ p (k + 1) a b (k + 1)| * |b 0| * (ρ / (1 - ρ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hq (div_nonneg hρ0 (by linarith))
    have hr0 : |divRem p (k + 1) a b (k + 1) 0 - b 0 * divQ p (k + 1) a b (k + 1)| ≤
        u p * divPk p (k + 1) ρ (k + 1) 0 * M := by
      refine q1.trans ?_
      rw [mul_assoc]
      exact mul_le_mul hus ((hrem (k + 1)).2 0 (by omega)) (abs_nonneg _) hu.le
    rw [hsplit, show k + 1 - 1 = k by omega]
    calc _ ≤ |divRem p (k + 1) a b (k + 1) 0 - b 0 * divQ p (k + 1) a b (k + 1) +
          ∑ i ∈ range k, divRem p (k + 1) a b (k + 1) (i + 1)| +
          |divQ p (k + 1) a b (k + 1) * ∑ i ∈ range k, b (i + 1)| := abs_sub _ _
      _ ≤ |divRem p (k + 1) a b (k + 1) 0 - b 0 * divQ p (k + 1) a b (k + 1)| +
          |∑ i ∈ range k, divRem p (k + 1) a b (k + 1) (i + 1)| +
          |divQ p (k + 1) a b (k + 1) * ∑ i ∈ range k, b (i + 1)| := by gcongr; exact abs_add_le _ _
      _ ≤ _ := by nlinarith [hr0, hr1, hb1]
  -- `|a - b∑_{k ≤ n} q_k| ≤ ΘM`
  have hAB : |A - B * ∑ k ∈ range (n + 1), divQ p n a b k| ≤ divTheta p n ρ * M := by
    have hid : A - B * ∑ k ∈ range (n + 1), divQ p n a b k = (R n - divQ p n a b n * B) + ∑ k ∈ range n, e k := by
      rw [sum_range_succ, mul_add, ← sub_sub, htel n]
      ring
    rw [hid]
    have hes : |∑ k ∈ range n, e k| ≤ (∑ k ∈ range n, divEps p n ρ (divPk p n ρ k)) * M := by
      rw [sum_mul]
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => by rw [mul_comm]; exact hek k)
    unfold divTheta
    rw [add_mul]
    exact (abs_add_le _ _).trans (add_le_add hlast hes)
  -- (eq:a0) for `a` and `b`, and `|b| ≤ |b_0|/(1 - ρ)`
  have h12 : 0 < 1 - 2 * ρ := by linarith
  have h1ρ : 0 < 1 - ρ := by linarith
  have hBlo : (1 - 2 * ρ) * |b 0| ≤ (1 - ρ) * |B| := by
    have h := mul_le_mul_of_nonneg_left (Htheta_a0 p n hn θ hθ hρ b hbH) h12.le
    calc (1 - 2 * ρ) * |b 0| ≤ (1 - 2 * ρ) * ((1 - ρ) / (1 - 2 * ρ) * |B|) := h
      _ = (1 - ρ) * |B| := by field_simp
  have hAlo : (1 - 2 * ρ) * M ≤ (1 - ρ) * |A| := by
    have h := mul_le_mul_of_nonneg_left (Htheta_a0 p n hn θ hθ hρ a haH) h12.le
    calc (1 - 2 * ρ) * M ≤ (1 - 2 * ρ) * ((1 - ρ) / (1 - 2 * ρ) * |A|) := h
      _ = (1 - ρ) * |A| := by field_simp
  have hBhi : (1 - ρ) * |B| ≤ |b 0| := by
    have h : |B| ≤ |b 0| * (1 / (1 - ρ)) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i ∈ range n, |b i| ≤ ∑ i ∈ range n, |b 0| * ρ ^ i :=
            sum_le_sum fun i hi => by rw [mul_comm]; exact hbH' i (mem_range.mp hi)
        _ = |b 0| * ∑ i ∈ range n, ρ ^ i := by rw [mul_sum]
        _ ≤ |b 0| * (1 / (1 - ρ)) := mul_le_mul_of_nonneg_left (geom_le ρ hρ0 hρ1 n) hb0'.le
    calc (1 - ρ) * |B| ≤ (1 - ρ) * (|b 0| * (1 / (1 - ρ))) := mul_le_mul_of_nonneg_left h h1ρ.le
      _ = |b 0| := by field_simp
  have hBpos : 0 < |B| := by nlinarith
  -- `|a/b - ∑ q| ≤ ΘM(1 - ρ)/((1 - 2ρ)|b_0|)`
  set Zq := ∑ k ∈ range (n + 1), divQ p n a b k with hZq
  have hΘM : 0 ≤ divTheta p n ρ * M := (abs_nonneg _).trans hAB
  have hMb : 0 ≤ M / |b 0| := div_nonneg hM hb0'.le
  have hΘ : 0 ≤ divTheta p n ρ := by
    have hq : ∀ k, 0 ≤ divQb p n ρ k := fun k => mul_nonneg (by linarith) (hPk k 0)
    unfold divTheta
    exact add_nonneg (add_nonneg (add_nonneg (sum_nonneg fun i _ => hPk n _) (mul_nonneg hu.le (hPk n 0)))
      (mul_nonneg (hq n) (div_nonneg hρ0 h1ρ.le)))
      (sum_nonneg fun k _ => divEps_nonneg p n ρ hn hQ hρ0 (hPk k))
  have hD : |A / B - Zq| ≤ (1 - ρ) / (1 - 2 * ρ) * divTheta p n ρ * (M / |b 0|) := by
    have hBne : B ≠ 0 := abs_pos.mp hBpos
    rw [show A / B - Zq = (A - B * Zq) / B by field_simp, abs_div, div_le_iff₀ hBpos]
    calc |A - B * Zq| ≤ divTheta p n ρ * M := hAB
      _ = (1 - ρ) / (1 - 2 * ρ) * divTheta p n ρ * (M / |b 0|) * ((1 - 2 * ρ) * |b 0| / (1 - ρ)) := by
          have h1 := h12.ne'
          have h2 := h1ρ.ne'
          have h3 := hb0'.ne'
          have h4 : (1 : ℝ) - ρ * 2 ≠ 0 := by linarith
          field_simp
      _ ≤ (1 - ρ) / (1 - 2 * ρ) * divTheta p n ρ * (M / |b 0|) * |B| := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (mul_nonneg (div_nonneg h1ρ.le h12.le) hΘ) hMb)
          rw [div_le_iff₀ h1ρ]
          linarith
  -- the last renormalization, `|q_k| ≤ q̄_kM/|b_0|`
  have hqX : ∀ m ≤ n, |divQ p n a b m| ≤ M / |b 0| * divQb p n ρ m := by
    intro m hm
    have h := (rem_quot p (r0 := divRem p n a b m 0) hb0).2
    rw [abs_mul] at h
    have hr0 := (hrem m).2 0 (by omega)
    calc |divQ p n a b m| = |divQ p n a b m| * |b 0| / |b 0| := by field_simp
      _ ≤ (1 + u p) * |divRem p n a b m 0| / |b 0| := div_le_div_of_nonneg_right h hb0'.le
      _ ≤ (1 + u p) * (divPk p n ρ m 0 * M) / |b 0| :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr0 (by linarith)) hb0'.le
      _ = M / |b 0| * divQb p n ρ m := by rw [divQb]; ring
  obtain ⟨hren, -, -⟩ := ren_of_levels p hp n hn (divQ p n a b) (fun i _ => F_RN p _)
    (fun m => M / |b 0| * divQb p n ρ m) hqX Zq |Zq| 0 le_rfl (by rw [hZq, sub_self, abs_zero])
  have hXi : ∑ j ∈ Ioc 0 n, (u p ^ n + u p ^ (n + 1 - j)) * Vb p n (fun m => M / |b 0| * divQb p n ρ m) j =
      M / |b 0| * divXi p n ρ := by
    rw [divXi, mul_sum]
    exact sum_congr rfl fun j _ => by rw [Vb_smul p n _ hMb]; ring
  rw [hXi, mul_zero, add_zero] at hren
  -- `M/|b_0| ≤ |a/b|/(1 - 2ρ)`
  have hMab : M / |b 0| ≤ |A / B| / (1 - 2 * ρ) := by
    rw [abs_div, div_div, div_le_div_iff₀ hb0' (mul_pos hBpos h12)]
    calc M * (|B| * (1 - 2 * ρ)) = ((1 - 2 * ρ) * M) * |B| := by ring
      _ ≤ ((1 - ρ) * |A|) * |B| := mul_le_mul_of_nonneg_right hAlo (abs_nonneg _)
      _ = |A| * ((1 - ρ) * |B|) := by ring
      _ ≤ |A| * |b 0| := mul_le_mul_of_nonneg_left hBhi (abs_nonneg _)
  have hXi0 : 0 ≤ divXi p n ρ := sum_nonneg fun j _ => mul_nonneg (by positivity)
    (Vb_nonneg p n (fun m => mul_nonneg (by linarith) (hPk m 0)) j)
  set C := (1 + u p ^ n) * divTheta p n ρ * ((1 - ρ) / (1 - 2 * ρ)) + divXi p n ρ with hC
  have hC0 : 0 ≤ C := by positivity
  have hk : kdiv p n ρ * u p ^ (n + 1) = C / (1 - 2 * ρ) := by
    rw [kdiv, ← hC]
    field_simp
  have hZ : |Zq| ≤ |A / B| + |A / B - Zq| := by
    have := abs_sub_abs_le_abs_sub Zq (A / B)
    rw [abs_sub_comm Zq] at this
    linarith
  have hun : 0 ≤ u p ^ n := pow_nonneg hu.le n
  calc |A / B - (divOp p n a b).sum| ≤ |A / B - Zq| + |Zq - (divOp p n a b).sum| := abs_sub_le _ _ _
    _ ≤ |A / B - Zq| + (u p ^ n * |Zq| + M / |b 0| * divXi p n ρ) := add_le_add le_rfl hren
    _ ≤ u p ^ n * |A / B| + (1 + u p ^ n) * |A / B - Zq| + M / |b 0| * divXi p n ρ := by
        have := mul_le_mul_of_nonneg_left hZ hun
        linarith
    _ ≤ u p ^ n * |A / B| + C * (M / |b 0|) := by
        have h1 := mul_le_mul_of_nonneg_left hD (by linarith : (0 : ℝ) ≤ 1 + u p ^ n)
        have h2 : C * (M / |b 0|) = (1 + u p ^ n) * ((1 - ρ) / (1 - 2 * ρ) * divTheta p n ρ * (M / |b 0|)) +
            M / |b 0| * divXi p n ρ := by rw [hC]; ring
        linarith
    _ ≤ u p ^ n * |A / B| + C * (|A / B| / (1 - 2 * ρ)) := by gcongr
    _ = (u p ^ n + kdiv p n ρ * u p ^ (n + 1)) * |A / B| := by
        rw [add_mul, hk]
        ring

end ExpansionBounds
