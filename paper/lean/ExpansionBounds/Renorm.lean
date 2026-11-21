import ExpansionBounds.Facts

/-!
# Theorem 9: renormalization in any order

VecSum and `Ren_n` as the appendix defines them, and Theorem 9 (a), (b) and (d). The terms are `c_0, …, c_m`, so
`N = m + 1`, indexed from `0` as in the paper; parts of `v` above `m` are zero.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ)

/-- VecSum of `c_0, …, c_m`: `s ← c_m`, then `(s, v_{i+1}) ← TwoSum(c_i, s)` for `i = m - 1, …, 0`, and `v_0 ← s`.
The VecSum of `c_1, …, c_m` gives `v_2, …, v_m` and the `s` that `TwoSum(c_0, s)` takes. -/
noncomputable def vecSum : ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, c => fun j => if j = 0 then c 0 else 0
  | m + 1, c => fun j =>
    if j = 0 then (twoSum p (c 0) (vecSum m (fun i => c (i + 1)) 0)).1
    else if j = 1 then (twoSum p (c 0) (vecSum m (fun i => c (i + 1)) 0)).2
    else vecSum m (fun i => c (i + 1)) (j - 1)

/-- the second pass of `Ren_n` over `v_j, v_{j+1}, …`, from `acc` with `b = n - 1 - k` emissions left:
`(t, e) ← TwoSum(acc, v_j)`; when `b ≠ 0` and `e ≠ 0` it emits `x_k ← t` and carries `acc ← e`, otherwise
`acc ← t`; at the end `x_k ← acc` -/
noncomputable def renPass : ℕ → ℝ → List ℝ → List ℝ
  | _, acc, [] => [acc]
  | b, acc, v :: vs =>
    if b ≠ 0 ∧ (twoSum p acc v).2 ≠ 0 then (twoSum p acc v).1 :: renPass (b - 1) (twoSum p acc v).2 vs
    else renPass b (twoSum p acc v).1 vs

/-- `Ren_n(c_0, …, c_m)`: the parts `x_0, …, x_k` it sets, the others being zero -/
noncomputable def ren (n m : ℕ) (c : ℕ → ℝ) : List ℝ :=
  renPass p (n - 1) (vecSum p m c 0) ((List.range m).map fun j => vecSum p m c (j + 1))

/-- `E = S - ∑ x_k` for the `n + 1` terms `c_0, …, c_n` -/
noncomputable def renErr (n : ℕ) (c : ℕ → ℝ) : ℝ := ∑ i ∈ range (n + 1), c i - (ren p n n c).sum

/-- the accumulator when every step emits: `acc_0 = v_0`, and `acc_j` is the error of `TwoSum(acc_{j-1}, v_j)` -/
noncomputable def accChain (v : ℕ → ℝ) : ℕ → ℝ
  | 0 => v 0
  | j + 1 => (twoSum p (accChain v j) (v (j + 1))).2

/-- the errors of `TwoSum` carried along `vs` from `acc` -/
noncomputable def chainL (acc : ℝ) (vs : List ℝ) : ℝ := vs.foldl (fun a v => (twoSum p a v).2) acc

/-- `σ_l = ∑_{m ≥ l} |c_m|` over `c_0, …, c_n` -/
noncomputable def sigma (n : ℕ) (c : ℕ → ℝ) (l : ℕ) : ℝ := ∑ m ∈ Ico l (n + 1), |c m|

theorem vecSum_zero (c : ℕ → ℝ) (j : ℕ) : vecSum p 0 c j = if j = 0 then c 0 else 0 := by
  simp [vecSum]

theorem vecSum_succ_zero (m : ℕ) (c : ℕ → ℝ) :
    vecSum p (m + 1) c 0 = (twoSum p (c 0) (vecSum p m (fun i => c (i + 1)) 0)).1 := by
  simp [vecSum]

theorem vecSum_succ_one (m : ℕ) (c : ℕ → ℝ) :
    vecSum p (m + 1) c 1 = (twoSum p (c 0) (vecSum p m (fun i => c (i + 1)) 0)).2 := by
  simp [vecSum]

theorem vecSum_succ_add_two (m : ℕ) (c : ℕ → ℝ) (j : ℕ) :
    vecSum p (m + 1) c (j + 1 + 1) = vecSum p m (fun i => c (i + 1)) (j + 1) := by
  simp [vecSum]

theorem list_sum_map_range (f : ℕ → ℝ) (m : ℕ) : ((List.range m).map f).sum = ∑ j ∈ range m, f j := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

theorem chainL_range (v : ℕ → ℝ) (j : ℕ) :
    chainL p (v 0) ((List.range j).map fun i => v (i + 1)) = accChain p v j := by
  induction j with
  | zero => simp [chainL, accChain]
  | succ j ih =>
    simp only [chainL] at ih ⊢
    rw [List.range_succ, List.map_append, List.foldl_append, ih]
    simp [accChain]

variable [Prec_gt_0 p]

theorem F_zero : F p 0 := by
  have h := F_RN p 0
  rwa [show RN p 0 = 0 from roundR_zero _ _] at h

theorem F_twoSum_fst (a b : ℝ) : F p (twoSum p a b).1 := F_RN p _

theorem F_twoSum_snd (a b : ℝ) : F p (twoSum p a b).2 := F_RN p _

theorem vecSum_F (m : ℕ) : ∀ c : ℕ → ℝ, (∀ i ≤ m, F p (c i)) → ∀ j, F p (vecSum p m c j) := by
  induction m with
  | zero =>
    intro c hc j
    rw [vecSum_zero]
    split_ifs
    · exact hc 0 le_rfl
    · exact F_zero p
  | succ m ih =>
    intro c hc j
    rcases j with _ | _ | j
    · rw [vecSum_succ_zero]
      exact F_twoSum_fst p _ _
    · rw [vecSum_succ_one]
      exact F_twoSum_snd p _ _
    · rw [vecSum_succ_add_two]
      exact ih _ (fun i hi => hc (i + 1) (by omega)) _

/-- Theorem 9 (a): VecSum is exact, `∑ v_j = S` -/
theorem vecSum_sum (hp : 1 < p) (m : ℕ) : ∀ c : ℕ → ℝ, (∀ i ≤ m, F p (c i)) →
    ∑ j ∈ range (m + 1), vecSum p m c j = ∑ i ∈ range (m + 1), c i := by
  induction m with
  | zero => intro c _; simp [vecSum_zero]
  | succ m ih =>
    intro c hc
    have hc' : ∀ i ≤ m, F p (c (i + 1)) := fun i hi => hc (i + 1) (by omega)
    have hts := twoSum_add p hp (hc 0 (by omega)) (vecSum_F p m _ hc' 0)
    have h := ih _ hc'
    rw [sum_range_succ', sum_range_succ']
    conv_rhs => rw [sum_range_succ']
    simp only [zero_add, vecSum_succ_zero, vecSum_succ_one, vecSum_succ_add_two]
    rw [← h, sum_range_succ']
    linarith

theorem renPass_exact (hp : 1 < p) (vs : List ℝ) : ∀ (b : ℕ) (acc : ℝ), vs.length ≤ b → F p acc →
    (∀ v ∈ vs, F p v) → (renPass p b acc vs).sum = acc + vs.sum := by
  induction vs with
  | nil => intro b acc _ _ _; simp [renPass]
  | cons v vs ih =>
    intro b acc hb hacc hvs
    simp only [List.length_cons] at hb
    have hv : F p v := hvs v (by simp)
    have hvs' : ∀ w ∈ vs, F p w := fun w hw => hvs w (by simp [hw])
    have hts := twoSum_add p hp hacc hv
    simp only [renPass]
    split_ifs with h
    · rw [List.sum_cons, ih (b - 1) _ (by omega) (F_twoSum_snd p _ _) hvs', List.sum_cons]
      linarith
    · have he : (twoSum p acc v).2 = 0 := by
        by_contra he
        exact h ⟨by omega, he⟩
      rw [ih b _ (by omega) (F_twoSum_fst p _ _) hvs', List.sum_cons]
      linarith

theorem renPass_loss (hp : 1 < p) (vs : List ℝ) : ∀ (b : ℕ) (acc : ℝ), vs.length = b + 1 → F p acc →
    (∀ v ∈ vs, F p v) → (renPass p b acc vs).sum ≠ acc + vs.sum →
    (renPass p b acc vs).length = b + 1 ∧ (∀ i < b, chainL p acc (vs.take (i + 1)) ≠ 0) ∧
      acc + vs.sum - (renPass p b acc vs).sum = chainL p acc vs := by
  induction vs with
  | nil => intro b acc h; simp at h
  | cons v vs ih =>
    intro b acc hlen hacc hvs hne
    simp only [List.length_cons] at hlen
    have hv : F p v := hvs v (by simp)
    have hvs' : ∀ w ∈ vs, F p w := fun w hw => hvs w (by simp [hw])
    have hts := twoSum_add p hp hacc hv
    rcases b with _ | b
    · obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp only [renPass, ne_eq, not_true_eq_false, false_and, ite_false, List.sum_cons, List.sum_nil] at hne ⊢
      refine ⟨by simp, fun i hi => absurd hi (Nat.not_lt_zero _), ?_⟩
      simp only [chainL, List.foldl_cons, List.foldl_nil]
      linarith
    · simp only [renPass] at hne ⊢
      split_ifs at hne ⊢ with hc
      · have he : (twoSum p acc v).2 ≠ 0 := hc.2
        simp only [Nat.add_sub_cancel, List.sum_cons] at hne ⊢
        have hne' : (renPass p b (twoSum p acc v).2 vs).sum ≠ (twoSum p acc v).2 + vs.sum := by
          intro h
          apply hne
          rw [h]
          linarith
        obtain ⟨h0, h1, h2⟩ := ih b _ (by omega) (F_twoSum_snd p _ _) hvs' hne'
        refine ⟨by simp [h0], fun i hi => ?_, ?_⟩
        · rcases i with _ | i
          · simpa [chainL] using he
          · simpa [chainL, List.take_succ_cons] using h1 i (by omega)
        · simp only [chainL, List.foldl_cons] at h2 ⊢
          linarith
      · exfalso
        have he : (twoSum p acc v).2 = 0 := by
          by_contra he
          exact hc ⟨by omega, he⟩
        rw [renPass_exact p hp vs (b + 1) _ (by omega) (F_twoSum_fst p _ _) hvs', List.sum_cons] at hne
        exact hne (by linarith)

/-- Theorem 9 (a): given `N ≤ n` terms, `Ren_n` is exact, `E = 0` -/
theorem ren_exact (hp : 1 < p) (n m : ℕ) (hmn : m + 1 ≤ n) (c : ℕ → ℝ) (hc : ∀ i ≤ m, F p (c i)) :
    (ren p n m c).sum = ∑ i ∈ range (m + 1), c i := by
  have hv := vecSum_F p m c hc
  unfold ren
  rw [renPass_exact p hp _ _ _ (by simp; omega) (hv 0) (by simp; exact fun j _ => hv _), list_sum_map_range,
    ← vecSum_sum p hp m c hc, sum_range_succ' (fun j => vecSum p m c j)]
  ring

/-- Theorem 9 (a): with `N = n + 1` terms, `E ≠ 0` only if each of the steps `1, …, n - 1` emitted, so that
`Ren_n` sets all `n` parts and `acc_j` is the error of step `j`; then `E` is the error of step `n` -/
theorem renErr_eq_accChain (hp : 1 < p) (n : ℕ) (hn : 1 ≤ n) (c : ℕ → ℝ) (hc : ∀ i ≤ n, F p (c i))
    (hE : renErr p n c ≠ 0) :
    (ren p n n c).length = n ∧ (∀ j, 1 ≤ j → j ≤ n - 1 → accChain p (vecSum p n c) j ≠ 0) ∧
      renErr p n c = accChain p (vecSum p n c) n := by
  have hv := vecSum_F p n c hc
  set vs := (List.range n).map fun j => vecSum p n c (j + 1) with hvs
  have hS : ∑ i ∈ range (n + 1), c i = vecSum p n c 0 + vs.sum := by
    rw [hvs, list_sum_map_range, ← vecSum_sum p hp n c hc, sum_range_succ' (fun j => vecSum p n c j)]
    ring
  have hlen : vs.length = n - 1 + 1 := by simp [hvs]; omega
  have hFvs : ∀ w ∈ vs, F p w := by simp [hvs]; exact fun j _ => hv _
  have hne : (renPass p (n - 1) (vecSum p n c 0) vs).sum ≠ vecSum p n c 0 + vs.sum := by
    intro h
    apply hE
    unfold renErr ren
    rw [← hvs, h, hS]
    ring
  obtain ⟨h0, h1, h2⟩ := renPass_loss p hp vs (n - 1) _ hlen (hv 0) hFvs hne
  refine ⟨?_, fun j hj1 hj2 => ?_, ?_⟩
  · unfold ren
    rw [← hvs, h0]
    omega
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have h := h1 i (by omega)
    rwa [hvs, ← List.map_take, List.take_range, Nat.min_eq_left (by omega), chainL_range] at h
  · unfold renErr ren
    rw [← hvs, hS, h2, hvs, chainL_range]

omit [Prec_gt_0 p] in
theorem us_nonneg : 0 ≤ us p := by
  have h := u_pos p
  unfold us
  positivity

theorem accChain_F (v : ℕ → ℝ) (hv : F p (v 0)) : ∀ j, F p (accChain p v j)
  | 0 => hv
  | _ + 1 => F_twoSum_snd p _ _

theorem abs_accChain_le (hp : 1 < p) (v : ℕ → ℝ) (hv : ∀ j, F p (v j)) (j : ℕ) :
    |accChain p v (j + 1)| ≤ |v (j + 1)| ∧
      |accChain p v (j + 1)| ≤ us p * (|accChain p v j| + |v (j + 1)|) := by
  have h := (facts_a p hp (accChain_F p v (hv 0) j) (hv (j + 1))).2.1
  refine ⟨h.trans ((min_le_left _ _).trans (min_le_right _ _)), h.trans ((min_le_right _ _).trans ?_)⟩
  exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (us_nonneg p)

theorem abs_accChain_le_v (hp : 1 < p) (v : ℕ → ℝ) (hv : ∀ j, F p (v j)) : ∀ j, |accChain p v j| ≤ |v j|
  | 0 => le_rfl
  | j + 1 => (abs_accChain_le p hp v hv j).1

/-- the first inequality of Theorem 9 (b)'s proof, iterated from `j = k + 1` to `k + d` -/
theorem abs_accChain_iter (hp : 1 < p) (v : ℕ → ℝ) (hv : ∀ j, F p (v j)) (k : ℕ) : ∀ d,
    |accChain p v (k + d)| ≤ us p ^ d * |accChain p v k| + ∑ i ∈ Ioc k (k + d), us p ^ (k + d + 1 - i) * |v i|
  | 0 => by simp
  | d + 1 => by
    have ih := abs_accChain_iter hp v hv k d
    have h1 := (abs_accChain_le p hp v hv (k + d)).2
    have hus := us_nonneg p
    have hsum : ∑ i ∈ Ioc k (k + d), us p ^ (k + (d + 1) + 1 - i) * |v i| =
        us p * ∑ i ∈ Ioc k (k + d), us p ^ (k + d + 1 - i) * |v i| := by
      rw [mul_sum]
      refine sum_congr rfl fun i hi => ?_
      rw [mem_Ioc] at hi
      rw [show k + (d + 1) + 1 - i = k + d + 1 - i + 1 by omega, pow_succ]
      ring
    rw [show k + (d + 1) = k + d + 1 by ring, sum_Ioc_succ_top (by omega)]
    rw [show k + d + 1 = k + (d + 1) by ring] at h1 ⊢
    rw [hsum, show k + (d + 1) + 1 - (k + (d + 1)) = 1 by omega, pow_one, pow_succ]
    calc |accChain p v (k + (d + 1))| ≤ us p * (|accChain p v (k + d)| + |v (k + (d + 1))|) := h1
      _ ≤ us p * (us p ^ d * |accChain p v k| + ∑ i ∈ Ioc k (k + d), us p ^ (k + d + 1 - i) * |v i| +
          |v (k + (d + 1))|) := mul_le_mul_of_nonneg_left (by linarith) hus
      _ = _ := by ring

/-- Theorem 9 (b): `|E| ≤ B_k` for each `k ≤ n`, so `|E| ≤ min_k B_k` -/
theorem renErr_le (hp : 1 < p) (n : ℕ) (hn : 1 ≤ n) (c : ℕ → ℝ) (hc : ∀ i ≤ n, F p (c i)) (k : ℕ) (hk : k ≤ n) :
    |renErr p n c| ≤
      us p ^ (n - k) * |vecSum p n c k| + ∑ j ∈ Ioc k n, us p ^ (n + 1 - j) * |vecSum p n c j| := by
  have hv := vecSum_F p n c hc
  have hus := us_nonneg p
  by_cases hE : renErr p n c = 0
  · rw [hE, abs_zero]
    exact add_nonneg (mul_nonneg (pow_nonneg hus _) (abs_nonneg _))
      (sum_nonneg fun j _ => mul_nonneg (pow_nonneg hus _) (abs_nonneg _))
  · rw [(renErr_eq_accChain p hp n hn c hc hE).2.2]
    have h := abs_accChain_iter p hp _ hv k (n - k)
    rw [show k + (n - k) = n by omega] at h
    have hk' := mul_le_mul_of_nonneg_left (abs_accChain_le_v p hp _ hv k) (pow_nonneg hus (n - k))
    linarith

theorem sigma_succ (n : ℕ) (c : ℕ → ℝ) (l : ℕ) : sigma (n + 1) c (l + 1) = sigma n (fun i => c (i + 1)) l := by
  unfold sigma
  rw [← sum_Ico_add' (fun m => |c m|) l (n + 1) 1]

theorem sigma_zero (n : ℕ) (c : ℕ → ℝ) : sigma n c 0 = |c 0| + sigma n c 1 := by
  unfold sigma
  rw [sum_eq_sum_Ico_succ_bot (by omega)]

/-- Theorem 9 (d): `|v_0| ≤ (1 + u)^n σ_0`, and `|v_j| ≤ min(|c_{j-1}|, ū(1 + u)^{n-j} σ_{j-1})` for `1 ≤ j ≤ n` -/
theorem vecSum_bounds (hp : 1 < p) (n : ℕ) : ∀ c : ℕ → ℝ, (∀ i ≤ n, F p (c i)) →
    |vecSum p n c 0| ≤ (1 + u p) ^ n * sigma n c 0 ∧
      ∀ j, 1 ≤ j → j ≤ n → |vecSum p n c j| ≤ |c (j - 1)| ∧
        |vecSum p n c j| ≤ us p * (1 + u p) ^ (n - j) * sigma n c (j - 1) := by
  have hu := u_pos p
  have hus := us_nonneg p
  induction n with
  | zero =>
    intro c _
    refine ⟨by simp [vecSum_zero, sigma], fun j hj1 hj2 => by omega⟩
  | succ n ih =>
    intro c hc
    have hc' : ∀ i ≤ n, F p (c (i + 1)) := fun i hi => hc (i + 1) (by omega)
    obtain ⟨ih0, ihj⟩ := ih _ hc'
    have hw0 := vecSum_F p n _ hc' 0
    have hfa := facts_a p hp (hc 0 (by omega)) hw0
    have hσ : sigma (n + 1) c 0 = |c 0| + sigma n (fun i => c (i + 1)) 0 := by
      rw [sigma_zero, sigma_succ]
    have hσnn : 0 ≤ sigma n (fun i => c (i + 1)) 0 := sum_nonneg fun _ _ => abs_nonneg _
    have hpow : 1 ≤ (1 + u p) ^ n := one_le_pow₀ (by linarith)
    have hsum : |c 0 + vecSum p n (fun i => c (i + 1)) 0| ≤ (1 + u p) ^ n * sigma (n + 1) c 0 := by
      rw [hσ]
      calc |c 0 + vecSum p n (fun i => c (i + 1)) 0|
          ≤ |c 0| + (1 + u p) ^ n * sigma n (fun i => c (i + 1)) 0 := (abs_add_le _ _).trans (by linarith)
        _ ≤ (1 + u p) ^ n * (|c 0| + sigma n (fun i => c (i + 1)) 0) := by nlinarith [abs_nonneg (c 0)]
    refine ⟨?_, fun j hj1 hj2 => ?_⟩
    · rw [vecSum_succ_zero]
      calc |(twoSum p (c 0) (vecSum p n (fun i => c (i + 1)) 0)).1|
          ≤ (1 + u p) * |c 0 + vecSum p n (fun i => c (i + 1)) 0| := abs_RN_le p _
        _ ≤ (1 + u p) * ((1 + u p) ^ n * sigma (n + 1) c 0) := mul_le_mul_of_nonneg_left hsum (by linarith)
        _ = (1 + u p) ^ (n + 1) * sigma (n + 1) c 0 := by ring
    · rcases j with _ | _ | j
      · omega
      · rw [vecSum_succ_one]
        refine ⟨hfa.2.1.trans ((min_le_left _ _).trans (min_le_left _ _)), ?_⟩
        calc |(twoSum p (c 0) (vecSum p n (fun i => c (i + 1)) 0)).2|
            ≤ us p * |c 0 + vecSum p n (fun i => c (i + 1)) 0| := hfa.2.1.trans (min_le_right _ _)
          _ ≤ us p * ((1 + u p) ^ n * sigma (n + 1) c 0) := mul_le_mul_of_nonneg_left hsum hus
          _ = us p * (1 + u p) ^ (n + 1 - (0 + 1)) * sigma (n + 1) c (0 + 1 - 1) := by simp; ring
      · rw [vecSum_succ_add_two]
        obtain ⟨h1, h2⟩ := ihj (j + 1) (by omega) (by omega)
        refine ⟨by simpa using h1, ?_⟩
        rw [show n + 1 - (j + 1 + 1) = n - (j + 1) by omega, show j + 1 + 1 - 1 = j + 1 by omega,
          show j + 1 = j + 1 - 1 + 1 by omega, sigma_succ]
        simpa using h2

omit [Prec_gt_0 p] in
theorem u_le_half (hp : 1 < p) : u p ≤ 1 / 2 := by
  unfold u
  calc (2 : ℝ) ^ (-p) ≤ (2 : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ = 1 / 2 := by norm_num

theorem sum_Ioc_zero (g : ℕ → ℝ) (n : ℕ) : ∑ j ∈ Ioc 0 n, g j = ∑ j ∈ range n, g (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Ioc_succ_top (by omega), ih, sum_range_succ]

theorem sum_Ioc_pow_reflect (x : ℝ) (m : ℕ) :
    ∑ j ∈ Ioc 0 (m + 1), x ^ (m + 1 - j) = ∑ i ∈ range (m + 1), x ^ i := by
  rw [sum_Ioc_zero]
  conv_rhs => rw [← sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  congr 1
  omega

theorem geom_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (m : ℕ) : ∑ i ∈ range m, x ^ i ≤ 1 / (1 - x) := by
  rw [le_div_iff₀ (by linarith), mul_comm, mul_neg_geom_sum]
  linarith [pow_nonneg hx0 m]

/-- `∑_l σ_l = ∑_m (m + 1)|c_m|` -/
theorem sum_sigma (n : ℕ) (c : ℕ → ℝ) :
    ∑ l ∈ range (n + 1), sigma n c l = ∑ m ∈ range (n + 1), ((m : ℝ) + 1) * |c m| := by
  unfold sigma
  rw [sum_comm' (t' := range (n + 1)) (s' := fun m => range (m + 1))
    (fun l m => by simp only [mem_range, mem_Ico]; omega)]
  refine sum_congr rfl fun m _ => ?_
  rw [sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

/-- Theorem 9 (e): if `|c_m| ≤ L_m u^m M` for `0 ≤ m ≤ n`, with `M > 0`, then
`|E| ≤ u^n |S| + 2(1 + u)^{n-1} / (1 - u) · Λ u^{n+1} M` with `Λ = ∑ L_m` -/
theorem renErr_le_scaled (hp : 1 < p) (n : ℕ) (hn : 1 ≤ n) (c : ℕ → ℝ) (hc : ∀ i ≤ n, F p (c i))
    (L : ℕ → ℝ) (M : ℝ) (hM : 0 < M) (hL : ∀ m ≤ n, |c m| ≤ L m * u p ^ m * M) :
    |renErr p n c| ≤ u p ^ n * |∑ i ∈ range (n + 1), c i| +
      2 * (1 + u p) ^ (n - 1) / (1 - u p) * (∑ m ∈ range (n + 1), L m) * u p ^ (n + 1) * M := by
  have hu0 : 0 < u p := u_pos p
  have hu2 : u p ≤ 1 / 2 := u_le_half p hp
  have h1u : 0 < 1 - u p := by linarith
  have h1u' : 0 ≤ 1 + u p := by linarith
  have hus0 := us_nonneg p
  have husu : us p ≤ u p := us_le_u p
  have hL0 : ∀ m ≤ n, 0 ≤ L m := by
    intro m hm
    have h := (abs_nonneg (c m)).trans (hL m hm)
    have hpos : 0 < u p ^ m * M := mul_pos (pow_pos hu0 m) hM
    by_contra hneg
    have := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hpos
    linarith
  set Λ := ∑ m ∈ range (n + 1), L m with hΛdef
  have hΛ : 0 ≤ Λ := sum_nonneg fun m hm => hL0 m (by simp at hm; omega)
  obtain ⟨-, hdj⟩ := vecSum_bounds p hp n c hc
  have hσ0 : ∀ l, 0 ≤ sigma n c l := fun l => sum_nonneg fun _ _ => abs_nonneg _
  have hσ : ∀ l, sigma n c l ≤ M * ∑ m ∈ Ico l (n + 1), L m * u p ^ m := by
    intro l
    unfold sigma
    rw [mul_sum]
    refine sum_le_sum fun m hm => ?_
    have := hL m (by simp at hm; omega)
    linarith
  have hvj : ∀ j ∈ Ioc 0 n, |vecSum p n c j| ≤ u p * (1 + u p) ^ (n - 1) * sigma n c (j - 1) := by
    intro j hj
    rw [mem_Ioc] at hj
    have hpow : (1 + u p) ^ (n - j) ≤ (1 + u p) ^ (n - 1) := pow_le_pow_right₀ (by linarith) (by omega)
    calc |vecSum p n c j| ≤ us p * (1 + u p) ^ (n - j) * sigma n c (j - 1) := (hdj j (by omega) hj.2).2
      _ ≤ u p * (1 + u p) ^ (n - 1) * sigma n c (j - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul husu hpow (pow_nonneg h1u' _) hu0.le) (hσ0 _)
  -- Theorem 9 (b) at k = 0, with ū ≤ u
  have hb : |renErr p n c| ≤
      u p ^ n * |vecSum p n c 0| + ∑ j ∈ Ioc 0 n, u p ^ (n + 1 - j) * |vecSum p n c j| := by
    have h := renErr_le p hp n hn c hc 0 (by omega)
    rw [Nat.sub_zero] at h
    have h1 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hus0 husu n) (abs_nonneg (vecSum p n c 0))
    have h2 : ∑ j ∈ Ioc 0 n, us p ^ (n + 1 - j) * |vecSum p n c j| ≤
        ∑ j ∈ Ioc 0 n, u p ^ (n + 1 - j) * |vecSum p n c j| :=
      sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hus0 husu _) (abs_nonneg _)
    linarith
  -- the first estimate: the sum over `j`
  have hterm : ∀ j ∈ Ioc 0 n, u p ^ (n + 1 - j) * |vecSum p n c j| ≤
      (1 + u p) ^ (n - 1) * M * u p ^ (n + 1) * ∑ m ∈ Ico (j - 1) (n + 1), L m * u p ^ (m + 1 - j) := by
    intro j hj
    have hj' := mem_Ioc.mp hj
    calc u p ^ (n + 1 - j) * |vecSum p n c j|
        ≤ u p ^ (n + 1 - j) * (u p * (1 + u p) ^ (n - 1) * (M * ∑ m ∈ Ico (j - 1) (n + 1), L m * u p ^ m)) :=
          mul_le_mul_of_nonneg_left ((hvj j hj).trans (mul_le_mul_of_nonneg_left (hσ _)
            (mul_nonneg hu0.le (pow_nonneg h1u' _)))) (pow_nonneg hu0.le _)
      _ = _ := by
          simp only [mul_sum]
          refine sum_congr rfl fun m hm => ?_
          have hm' := mem_Ico.mp hm
          have hexp : u p ^ (n + 1 - j) * u p * u p ^ m = u p ^ (n + 1) * u p ^ (m + 1 - j) := by
            rw [← pow_succ, ← pow_add, ← pow_add]
            congr 1
            omega
          linear_combination (1 + u p) ^ (n - 1) * M * L m * hexp
  have hswap : ∑ j ∈ Ioc 0 n, ∑ m ∈ Ico (j - 1) (n + 1), L m * u p ^ (m + 1 - j) =
      ∑ m ∈ range (n + 1), ∑ j ∈ Ioc 0 (min n (m + 1)), L m * u p ^ (m + 1 - j) :=
    sum_comm' fun j m => by simp only [mem_Ioc, mem_Ico, mem_range, le_min_iff]; omega
  have hinner : ∀ m ∈ range (n + 1),
      ∑ j ∈ Ioc 0 (min n (m + 1)), L m * u p ^ (m + 1 - j) ≤ L m / (1 - u p) := by
    intro m hm
    have hLm := hL0 m (by simp at hm; omega)
    calc ∑ j ∈ Ioc 0 (min n (m + 1)), L m * u p ^ (m + 1 - j)
        ≤ ∑ j ∈ Ioc 0 (m + 1), L m * u p ^ (m + 1 - j) :=
          sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right (min_le_right _ _))
            fun j _ _ => mul_nonneg hLm (pow_nonneg hu0.le _)
      _ = L m * ∑ i ∈ range (m + 1), u p ^ i := by rw [← mul_sum, sum_Ioc_pow_reflect]
      _ ≤ L m * (1 / (1 - u p)) := mul_le_mul_of_nonneg_left (geom_le _ hu0.le (by linarith) _) hLm
      _ = L m / (1 - u p) := by ring
  have hK0 : 0 ≤ (1 + u p) ^ (n - 1) * M * u p ^ (n + 1) :=
    mul_nonneg (mul_nonneg (pow_nonneg h1u' _) hM.le) (pow_nonneg hu0.le _)
  have hpart1 : ∑ j ∈ Ioc 0 n, u p ^ (n + 1 - j) * |vecSum p n c j| ≤
      (1 + u p) ^ (n - 1) * M * u p ^ (n + 1) * (Λ / (1 - u p)) := by
    calc ∑ j ∈ Ioc 0 n, u p ^ (n + 1 - j) * |vecSum p n c j|
        ≤ ∑ j ∈ Ioc 0 n, (1 + u p) ^ (n - 1) * M * u p ^ (n + 1) *
            ∑ m ∈ Ico (j - 1) (n + 1), L m * u p ^ (m + 1 - j) := sum_le_sum hterm
      _ = (1 + u p) ^ (n - 1) * M * u p ^ (n + 1) *
            ∑ m ∈ range (n + 1), ∑ j ∈ Ioc 0 (min n (m + 1)), L m * u p ^ (m + 1 - j) := by
          rw [← mul_sum, hswap]
      _ ≤ (1 + u p) ^ (n - 1) * M * u p ^ (n + 1) * ∑ m ∈ range (n + 1), L m / (1 - u p) :=
          mul_le_mul_of_nonneg_left (sum_le_sum hinner) hK0
      _ = _ := by rw [← sum_div]
  -- the second estimate: `|v_0|` through `∑ v_j = S`
  have hS : ∑ i ∈ range (n + 1), c i = vecSum p n c 0 + ∑ j ∈ range n, vecSum p n c (j + 1) := by
    rw [← vecSum_sum p hp n c hc, sum_range_succ']
    ring
  have hv0 : |vecSum p n c 0| ≤ |∑ i ∈ range (n + 1), c i| + ∑ j ∈ range n, |vecSum p n c (j + 1)| := by
    have h1 : vecSum p n c 0 = ∑ i ∈ range (n + 1), c i - ∑ j ∈ range n, vecSum p n c (j + 1) := by
      linarith
    have h2 := abs_add_le (∑ i ∈ range (n + 1), c i) (-∑ j ∈ range n, vecSum p n c (j + 1))
    have h3 := abs_sum_le_sum_abs (fun j => vecSum p n c (j + 1)) (range n)
    rw [abs_neg, ← sub_eq_add_neg, ← h1] at h2
    linarith
  have hmu : ∀ m : ℕ, ((m : ℝ) + 1) * u p ^ m ≤ 1 := by
    intro m
    have hm2 : ((m : ℝ) + 1) ≤ 2 ^ m := by exact_mod_cast Nat.lt_two_pow_self
    have hup : u p ^ m ≤ (1 / 2) ^ m := pow_le_pow_left₀ hu0.le hu2 m
    calc ((m : ℝ) + 1) * u p ^ m ≤ 2 ^ m * (1 / 2) ^ m := mul_le_mul hm2 hup (pow_nonneg hu0.le _) (by positivity)
      _ = 1 := by rw [← mul_pow]; norm_num
  have hsumv : ∑ j ∈ range n, |vecSum p n c (j + 1)| ≤ u p * (1 + u p) ^ (n - 1) * (M * Λ) := by
    have hc0 : 0 ≤ u p * (1 + u p) ^ (n - 1) := mul_nonneg hu0.le (pow_nonneg h1u' _)
    calc ∑ j ∈ range n, |vecSum p n c (j + 1)| ≤ ∑ j ∈ range n, u p * (1 + u p) ^ (n - 1) * sigma n c j := by
          refine sum_le_sum fun j hj => ?_
          rw [mem_range] at hj
          simpa using hvj (j + 1) (by simp; omega)
      _ = u p * (1 + u p) ^ (n - 1) * ∑ j ∈ range n, sigma n c j := by rw [mul_sum]
      _ ≤ u p * (1 + u p) ^ (n - 1) * ∑ l ∈ range (n + 1), sigma n c l := by
          refine mul_le_mul_of_nonneg_left ?_ hc0
          rw [sum_range_succ]
          linarith [hσ0 n]
      _ = u p * (1 + u p) ^ (n - 1) * ∑ m ∈ range (n + 1), ((m : ℝ) + 1) * |c m| := by rw [sum_sigma]
      _ ≤ u p * (1 + u p) ^ (n - 1) * (M * Λ) := by
          refine mul_le_mul_of_nonneg_left ?_ hc0
          rw [hΛdef, mul_sum]
          refine sum_le_sum fun m hm => ?_
          rw [mem_range] at hm
          have hLm := hL0 m (by omega)
          calc ((m : ℝ) + 1) * |c m| ≤ ((m : ℝ) + 1) * (L m * u p ^ m * M) :=
                mul_le_mul_of_nonneg_left (hL m (by omega)) (by positivity)
            _ = (L m * M) * (((m : ℝ) + 1) * u p ^ m) := by ring
            _ ≤ (L m * M) * 1 := mul_le_mul_of_nonneg_left (hmu m) (mul_nonneg hLm hM.le)
            _ = M * L m := by ring
  have hpart2 : u p ^ n * |vecSum p n c 0| ≤
      u p ^ n * |∑ i ∈ range (n + 1), c i| + (1 + u p) ^ (n - 1) * Λ * u p ^ (n + 1) * M := by
    have h := mul_le_mul_of_nonneg_left (hv0.trans (by linarith [hsumv] :
      |∑ i ∈ range (n + 1), c i| + ∑ j ∈ range n, |vecSum p n c (j + 1)| ≤
        |∑ i ∈ range (n + 1), c i| + u p * (1 + u p) ^ (n - 1) * (M * Λ))) (pow_nonneg hu0.le n)
    calc u p ^ n * |vecSum p n c 0| ≤ _ := h
      _ = _ := by ring
  -- adding the two: `K + K / (1 - u) ≤ 2K / (1 - u)`
  set K := (1 + u p) ^ (n - 1) * Λ * u p ^ (n + 1) * M with hK
  have hKnn : 0 ≤ K := by rw [hK]; nlinarith [hK0, hΛ]
  have hKdiv : K ≤ K / (1 - u p) := by
    rw [le_div_iff₀ h1u]
    nlinarith
  have h1 : (1 + u p) ^ (n - 1) * M * u p ^ (n + 1) * (Λ / (1 - u p)) = K / (1 - u p) := by
    rw [hK]
    ring
  have h2 : 2 * (1 + u p) ^ (n - 1) / (1 - u p) * Λ * u p ^ (n + 1) * M = K / (1 - u p) + K / (1 - u p) := by
    rw [hK]
    ring
  rw [h2]
  linarith

end ExpansionBounds
