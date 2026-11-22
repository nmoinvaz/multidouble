import ExpansionBounds.Renorm

/-!
# Lemma 12: the parts of `Ren_n`

For `c ∈ 𝔽ⁿ⁺¹`, `v = VecSum(c)`, `x = Ren_n(c)`, `S = ∑ c_m` and `W_k = ∑_{j=k+1}^n |v_j|`:
`(|S| - W_1) / (1 + u) ≤ |x_0| ≤ (1 + u)(|S| + W_1)` and `|x_i| ≤ (1 + u)(u|x_{i-1}| + W_i)` for `1 ≤ i ≤ n - 1`.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ)

theorem list_abs_sum_nonneg (l : List ℝ) : 0 ≤ (l.map abs).sum :=
  List.sum_nonneg fun x hx => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
    exact abs_nonneg y

theorem list_abs_sum_le (l : List ℝ) : |l.sum| ≤ (l.map abs).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.sum_cons, List.map_cons]
    exact (abs_add_le _ _).trans (by linarith)

theorem list_abs_drop_le (l : List ℝ) (k : ℕ) : ((l.drop k).map abs).sum ≤ (l.map abs).sum := by
  conv_rhs => rw [← List.take_append_drop k l]
  rw [List.map_append, List.sum_append]
  linarith [list_abs_sum_nonneg (l.take k)]

theorem list_abs_take_le (l : List ℝ) (k : ℕ) : ((l.take k).map abs).sum ≤ (l.map abs).sum := by
  conv_rhs => rw [← List.take_append_drop k l]
  rw [List.map_append, List.sum_append]
  linarith [list_abs_sum_nonneg (l.drop k)]

/-- `∑_{j ≥ k} |f(j)|` over `f(0), …, f(n-1)` -/
theorem list_abs_drop_range (f : ℕ → ℝ) (n k : ℕ) :
    ((((List.range n).map f).drop k).map abs).sum = ∑ j ∈ Ico k n, |f j| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append]
    by_cases hk : k ≤ n
    · rw [List.drop_append_of_le_length (by simpa using hk), List.map_append, List.sum_append, ih,
        sum_Ico_succ_top hk]
      simp
    · rw [List.drop_eq_nil_of_le (by simp; omega), Ico_eq_empty (by omega)]
      simp

variable [Prec_gt_0 p]

/-- the first part a second pass sets is `acc` plus a prefix of its terms, at least one if there are any, exactly or
rounded once -/
theorem renPass_first (hp : 1 < p) (vs : List ℝ) : ∀ (b : ℕ) (acc : ℝ), vs.length ≤ b + 1 → F p acc →
    (∀ v ∈ vs, F p v) → ∃ j, (vs ≠ [] → 1 ≤ j) ∧
      ((renPass p b acc vs).getD 0 0 = acc + (vs.take j).sum ∨
        (renPass p b acc vs).getD 0 0 = RN p (acc + (vs.take j).sum)) := by
  induction vs with
  | nil => intro b acc _ _ _; exact ⟨0, fun h => absurd rfl h, Or.inl (by simp [renPass])⟩
  | cons v vs ih =>
    intro b acc hlen hacc hvs
    simp only [List.length_cons] at hlen
    have hv : F p v := hvs v (by simp)
    have hvs' : ∀ w ∈ vs, F p w := fun w hw => hvs w (by simp [hw])
    have hts := twoSum_add p hp hacc hv
    simp only [renPass]
    split_ifs with hc
    · exact ⟨1, fun _ => le_rfl, Or.inr (by simp; rfl)⟩
    · by_cases he : (twoSum p acc v).2 = 0
      · have ht : (twoSum p acc v).1 = acc + v := by linarith
        obtain ⟨j, -, hj⟩ := ih b (twoSum p acc v).1 (by omega) (F_twoSum_fst p acc v) hvs'
        refine ⟨j + 1, fun _ => by omega, ?_⟩
        simp only [List.take_succ_cons, List.sum_cons, ← add_assoc]
        rw [← ht]
        exact hj
      · have hb : b = 0 := by
          by_contra hb
          exact hc ⟨hb, he⟩
        subst hb
        obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
        exact ⟨1, fun _ => le_rfl, Or.inr (by simp [renPass]; rfl)⟩

theorem abs_le_of_RN_or {x P : ℝ} (h : x = P ∨ x = RN p P) : |x| ≤ (1 + u p) * |P| ∧ |P| / (1 + u p) ≤ |x| := by
  have hu := u_pos p
  rcases h with rfl | rfl
  · refine ⟨by nlinarith [abs_nonneg x], ?_⟩
    rw [div_le_iff₀ (by linarith)]
    nlinarith [abs_nonneg x]
  · exact ⟨abs_RN_le p P, abs_RN_ge p P⟩

/-- each later part of a second pass: `|x_i| ≤ (1 + u)(u|x_{i-1}| + ∑_{j ≥ i} |v_j|)` over its terms -/
theorem renPass_next (hp : 1 < p) (vs : List ℝ) : ∀ (b : ℕ) (acc : ℝ), vs.length ≤ b + 1 → F p acc →
    (∀ v ∈ vs, F p v) → ∀ i, 1 ≤ i → |(renPass p b acc vs).getD i 0| ≤
      (1 + u p) * (u p * |(renPass p b acc vs).getD (i - 1) 0| + ((vs.drop i).map abs).sum) := by
  have hu := u_pos p
  induction vs with
  | nil =>
    intro b acc _ _ _ i hi
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    simp only [renPass, List.getD_cons_succ, List.getD_nil, abs_zero]
    exact mul_nonneg (by linarith) (add_nonneg (mul_nonneg hu.le (abs_nonneg _)) (list_abs_sum_nonneg _))
  | cons v vs ih =>
    intro b acc hlen hacc hvs i hi
    simp only [List.length_cons] at hlen
    have hv : F p v := hvs v (by simp)
    have hvs' : ∀ w ∈ vs, F p w := fun w hw => hvs w (by simp [hw])
    have hts := twoSum_add p hp hacc hv
    have hrhs : ∀ y : ℝ, 0 ≤ (1 + u p) * (u p * |y| + ((List.drop i (v :: vs)).map abs).sum) := fun y =>
      mul_nonneg (by linarith) (add_nonneg (mul_nonneg hu.le (abs_nonneg _)) (list_abs_sum_nonneg _))
    simp only [renPass]
    split_ifs with hc
    · obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rcases i with _ | i
      · -- the part after an emission starts from its error, `|e| ≤ u|x_{i-1}|`
        simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_sub_cancel]
        obtain ⟨j, -, hj⟩ := renPass_first p hp vs (b - 1) (twoSum p acc v).2 (by omega) (F_twoSum_snd p _ _) hvs'
        have hP := (abs_le_of_RN_or p hj).1
        have he : |(twoSum p acc v).2| ≤ u p * |(twoSum p acc v).1| := by
          have h := abs_RN_sub_le_u_RN p (acc + v)
          rw [abs_sub_comm] at h
          rw [show (twoSum p acc v).2 = acc + v - RN p (acc + v) by
            have : (twoSum p acc v).1 = RN p (acc + v) := rfl
            linarith]
          exact h
        have htake : |(twoSum p acc v).2 + (vs.take j).sum| ≤ |(twoSum p acc v).2| + (vs.map abs).sum :=
          (abs_add_le _ _).trans (by linarith [list_abs_sum_le (vs.take j), list_abs_take_le vs j])
        calc |(renPass p (b - 1) (twoSum p acc v).2 vs).getD 0 0|
            ≤ (1 + u p) * |(twoSum p acc v).2 + (vs.take j).sum| := hP
          _ ≤ (1 + u p) * (u p * |(twoSum p acc v).1| + (vs.map abs).sum) :=
            mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      · simp only [List.getD_cons_succ, Nat.add_sub_cancel, List.drop_succ_cons]
        have h := ih (b - 1) (twoSum p acc v).2 (by omega) (F_twoSum_snd p acc v) hvs' (i + 1) (by omega)
        simpa using h
    · by_cases he : (twoSum p acc v).2 = 0
      · have h := ih b (twoSum p acc v).1 (by omega) (F_twoSum_fst p acc v) hvs' i hi
        refine h.trans (mul_le_mul_of_nonneg_left (add_le_add_right ?_ _) (by linarith))
        obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [List.drop_succ_cons, ← List.drop_drop]
        exact list_abs_drop_le _ _
      · have hb : b = 0 := by
          by_contra hb
          exact hc ⟨hb, he⟩
        subst hb
        obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
        obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        simp only [renPass, List.getD_cons_succ, List.getD_nil, abs_zero]
        exact hrhs _

/-- Lemma 12: with `W_k = ∑_{j=k+1}^n |v_j|`, `(|S| - W_1) / (1 + u) ≤ |x_0| ≤ (1 + u)(|S| + W_1)`, and
`|x_i| ≤ (1 + u)(u|x_{i-1}| + W_i)` for `1 ≤ i ≤ n - 1` -/
theorem ren_parts (hp : 1 < p) (n : ℕ) (hn : 1 ≤ n) (c : ℕ → ℝ) (hc : ∀ i ≤ n, F p (c i)) :
    (|∑ i ∈ range (n + 1), c i| - ∑ j ∈ Ioc 1 n, |vecSum p n c j|) / (1 + u p) ≤ |(ren p n n c).getD 0 0| ∧
      |(ren p n n c).getD 0 0| ≤ (1 + u p) * (|∑ i ∈ range (n + 1), c i| + ∑ j ∈ Ioc 1 n, |vecSum p n c j|) ∧
      ∀ i, 1 ≤ i → i ≤ n - 1 → |(ren p n n c).getD i 0| ≤
        (1 + u p) * (u p * |(ren p n n c).getD (i - 1) 0| + ∑ j ∈ Ioc i n, |vecSum p n c j|) := by
  have hu := u_pos p
  have hv := vecSum_F p n c hc
  set vs := (List.range n).map fun j => vecSum p n c (j + 1) with hvs
  have hlen : vs.length ≤ n - 1 + 1 := by simp [hvs]; omega
  have hFvs : ∀ w ∈ vs, F p w := by simp [hvs]; exact fun j _ => hv _
  have hren : ren p n n c = renPass p (n - 1) (vecSum p n c 0) vs := rfl
  have hS : ∑ i ∈ range (n + 1), c i = vecSum p n c 0 + vs.sum := by
    rw [hvs, list_sum_map_range, ← vecSum_sum p hp n c hc, sum_range_succ' (fun j => vecSum p n c j)]
    ring
  have hW : ∀ k, ((vs.drop k).map abs).sum = ∑ j ∈ Ioc k n, |vecSum p n c j| := by
    intro k
    rw [hvs, list_abs_drop_range (fun j => vecSum p n c (j + 1)), ← Ico_add_one_add_one_eq_Ioc,
      ← sum_Ico_add' (fun j => |vecSum p n c j|) k n 1]
  obtain ⟨j, hj1, hj⟩ := renPass_first p hp vs (n - 1) _ hlen (hv 0) hFvs
  have hj1' : 1 ≤ j := hj1 (by simp [hvs]; omega)
  -- `S` and the sum `x_0` rounds differ by the terms after the first emission
  have hdiff : |∑ i ∈ range (n + 1), c i - (vecSum p n c 0 + (vs.take j).sum)| ≤ ∑ j ∈ Ioc 1 n, |vecSum p n c j| := by
    rw [hS, show vecSum p n c 0 + vs.sum - (vecSum p n c 0 + (vs.take j).sum) = (vs.drop j).sum by
      have := List.sum_take_add_sum_drop vs j; linarith, ← hW 1]
    calc |(vs.drop j).sum| ≤ ((vs.drop j).map abs).sum := list_abs_sum_le _
      _ ≤ ((vs.drop 1).map abs).sum := by
        rw [show j = 1 + (j - 1) by omega, ← List.drop_drop]
        exact list_abs_drop_le _ _
  obtain ⟨hup, hlo⟩ := abs_le_of_RN_or p hj
  rw [hren]
  refine ⟨?_, ?_, fun i hi1 _ => ?_⟩
  · refine le_trans ?_ hlo
    rw [div_le_div_iff_of_pos_right (by linarith)]
    have := abs_sub_abs_le_abs_sub (∑ i ∈ range (n + 1), c i) (vecSum p n c 0 + (vs.take j).sum)
    linarith
  · refine hup.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    have := abs_sub_abs_le_abs_sub (vecSum p n c 0 + (vs.take j).sum) (∑ i ∈ range (n + 1), c i)
    rw [abs_sub_comm] at this
    linarith
  · rw [← hW i]
    exact renPass_next p hp vs (n - 1) _ hlen (hv 0) hFvs i hi1

end ExpansionBounds
