import ExpansionBounds.ExpThm
import ExpansionBounds.FExact

/-!
# Proposition 24 (b): ADD and ADDF err by `u^n`

ADD of `a = (1, u, …, u^{n-1})` and `b = (u^n, 0, …, 0)`, and ADDF of the same `a` and `b = u^n`, have the levels
`(1, u, …, u^n)`: `TwoSum(u^m, u^k) = (u^m, u^k)` for `m < k`, by the tie for `k = m + 1` and because `u^k` is below
half an ulp of `u^m` otherwise, and `TwoSum(y, 0) = (y, 0)`. By Theorem 9 (c) the result then errs by `u^n`, which is
`u^n |a + b| (1 - u)/(1 - u^{n+1})`, so Theorem 15's leading constant `1` is attained.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ)

/-- VecSum of `c_0, …, c_m` depends on those terms only -/
theorem vecSum_congr : ∀ (m : ℕ) (c c' : ℕ → ℝ), (∀ i ≤ m, c i = c' i) → vecSum p m c = vecSum p m c'
  | 0, c, c', h => funext fun j => by simp [vecSum, h 0 le_rfl]
  | m + 1, c, c', h => by
    have ih := vecSum_congr m (fun i => c (i + 1)) (fun i => c' (i + 1)) (fun i hi => h (i + 1) (by omega))
    funext j
    simp only [vecSum, ih, h 0 (by omega)]

theorem ren_congr (n m : ℕ) {c c' : ℕ → ℝ} (h : ∀ i ≤ m, c i = c' i) : ren p n m c = ren p n m c' := by
  unfold ren
  rw [vecSum_congr p m c c' h]

variable [Prec_gt_0 p]

theorem RN_mono {x y : ℝ} (h : x ≤ y) : RN p x ≤ RN p y :=
  FloatSpec.Core.Generic_fmt.roundR_le 2 (FloatSpec.Core.FLX.FLX_exp p)
    (FloatSpec.Core.Generic_fmt.Znearest tieEven) x y (by norm_num) h

theorem F_u_pow (m : ℕ) : F p (u p ^ m) := by
  rw [u_pow]
  exact F_two_zpow p _

/-- `TwoSum(u^m, u^k) = (u^m, u^k)` for `m < k` -/
theorem twoSum_pow_lt (hp : 1 < p) (m k : ℕ) (hk : m < k) : twoSum p (u p ^ m) (u p ^ k) = (u p ^ m, u p ^ k) := by
  rcases Nat.lt_or_ge (m + 1) k with hk2 | hk1
  · have hu := u_pos p
    have hu1 : u p ≤ 1 := by linarith [u_le_half p hp]
    have hs : (twoSum p (u p ^ m) (u p ^ k)).1 = u p ^ m := by
      show RN p (u p ^ m + u p ^ k) = u p ^ m
      apply le_antisymm
      · have h1 : u p ^ k ≤ u p ^ (m + 1) := pow_le_pow_of_le_one hu.le hu1 (by omega)
        have h2 := RN_mono p (add_le_add (le_refl (u p ^ m)) h1)
        have h3 : RN p (u p ^ m + u p ^ (m + 1)) = u p ^ m := congrArg Prod.fst (twoSum_pow p hp m)
        linarith
      · have h := RN_mono p (le_add_of_nonneg_right (pow_nonneg hu.le k) : u p ^ m ≤ u p ^ m + u p ^ k)
        rwa [RN_of_F p (F_u_pow p m)] at h
    have he := (facts_a p hp (F_u_pow p m) (F_u_pow p k)).1
    rw [hs] at he
    exact Prod.ext hs (by simp only; linarith)
  · obtain rfl : k = m + 1 := by omega
    exact twoSum_pow p hp m

/-- ADDF's carries on `a = (1, u, …, u^{n-1})` and `b = u^n` stay `u^n` -/
theorem addfE_pow (hp : 1 < p) (n : ℕ) : ∀ m ≤ n, addfE p (fun i => u p ^ i) (u p ^ n) m = u p ^ n := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    simp only [addfE]
    rw [ih (by omega), twoSum_pow_lt p hp m n (by omega)]

/-- a dep of `u^n` from level `m ≥ 1` over levels `s_j = u^j` leaves them in place and rounds `u^n` into level `n` -/
theorem depRun_pow (hp : 1 < p) (n : ℕ) : ∀ (k m : ℕ) (st : LState), m + k = n →
    (∀ j, m ≤ j → j < n → st.s j = u p ^ j) →
    (depRun p n k m (u p ^ n) st).2.s = Function.update st.s n (RN p (st.s n + u p ^ n)) := by
  intro k
  induction k with
  | zero => intro m st _ _; rfl
  | succ k ih =>
    intro m st hmk hs
    simp only [depRun]
    have hsm : st.s m = u p ^ m := hs m le_rfl (by omega)
    have htw : twoSum p (st.s m) (u p ^ n) = (u p ^ m, u p ^ n) := by rw [hsm]; exact twoSum_pow_lt p hp m n (by omega)
    have hst : (twoAt p m (u p ^ n) st).s = st.s := by
      show Function.update st.s m (twoSum p (st.s m) (u p ^ n)).1 = st.s
      rw [htw]
      exact Function.update_eq_self_iff.mpr hsm.symm
    rw [htw]
    show (depRun p n k (m + 1) (u p ^ n) (twoAt p m (u p ^ n) st)).2.s = _
    rw [ih (m + 1) _ (by omega) (fun j hj1 hj2 => by rw [hst]; exact hs j (by omega) hj2), hst]

/-- a dep of `0` changes no level in `F` -/
theorem depRun_zero (n : ℕ) : ∀ (k m : ℕ) (st : LState), (∀ j, F p (st.s j)) → (depRun p n k m 0 st).2.s = st.s := by
  intro k
  induction k with
  | zero =>
    intro m st hF
    show Function.update st.s n (RN p (st.s n + 0)) = st.s
    rw [add_zero, RN_of_F p (hF n)]
    exact Function.update_eq_self n st.s
  | succ k ih =>
    intro m st hF
    simp only [depRun]
    have htw : twoSum p (st.s m) 0 = (st.s m, 0) := twoSum_zero p (hF m)
    have hst : (twoAt p m 0 st).s = st.s := by
      show Function.update st.s m (twoSum p (st.s m) 0).1 = st.s
      rw [htw]
      exact Function.update_eq_self m st.s
    rw [htw]
    show (depRun p n k (m + 1) 0 (twoAt p m 0 st)).2.s = _
    rw [ih (m + 1) _ (by rw [hst]; exact hF), hst]

/-- deps of `0` change no level in `F` -/
theorem runOps_deps_zero (n : ℕ) : ∀ (L : List ℕ) (st : LState), (∀ j, F p (st.s j)) →
    (runOps p n (L.map fun l => LOp.dep l 0) st).2.s = st.s := by
  intro L
  induction L with
  | nil => intro st _; rfl
  | cons l L ih =>
    intro st hF
    simp only [List.map_cons, runOps, stepOp]
    have h := depRun_zero p n (n - l) l (entering l 0 st) hF
    rw [ih _ (by rw [h]; exact hF), h]
    rfl

omit [Prec_gt_0 p] in
/-- `∑_{i ≤ n} u^i = (1 - u^{n+1})/(1 - u)`, so `u^n = u^n |a + b| (1 - u)/(1 - u^{n+1})` -/
theorem u_pow_rel (hp : 1 < p) (n : ℕ) :
    u p ^ n = u p ^ n * |∑ i ∈ range (n + 1), u p ^ i| * (1 - u p) / (1 - u p ^ (n + 1)) := by
  have hu := u_pos p
  have hu1 : u p < 1 := by linarith [u_le_half p hp]
  have hpow : u p ^ (n + 1) < 1 := pow_lt_one₀ hu.le hu1 (by omega)
  rw [abs_of_nonneg (sum_nonneg fun i _ => pow_nonneg hu.le i), geom_sum_eq hu1.ne]
  field_simp [show u p - 1 ≠ 0 by linarith, show 1 - u p ^ (n + 1) ≠ 0 by linarith]
  ring

/-- Proposition 24 (b) for ADDF: ADDF of `a = (1, u, …, u^{n-1})` and `b = u^n` errs by `u^n` -/
theorem prop24_addf (hp : 1 < p) (n : ℕ) (hn : 1 ≤ n) :
    |(∑ i ∈ range n, u p ^ i + u p ^ n) - (addfOp p n (fun i => u p ^ i) (u p ^ n)).sum| = u p ^ n ∧
      u p ^ n = u p ^ n * |∑ i ∈ range n, u p ^ i + u p ^ n| * (1 - u p) / (1 - u p ^ (n + 1)) := by
  have hlev : ∀ m ≤ n, addfLevels p n (fun i => u p ^ i) (u p ^ n) m = u p ^ m := by
    intro m hm
    rcases Nat.lt_or_ge m n with hlt | hge
    · simp only [addfLevels, hlt, ite_true]
      rw [addfE_pow p hp n m hm, twoSum_pow_lt p hp m n hlt]
    · obtain rfl : m = n := by omega
      simp only [addfLevels, lt_irrefl, ite_false, ite_true]
      exact addfE_pow p hp m m le_rfl
  have hren : addfOp p n (fun i => u p ^ i) (u p ^ n) = ren p n n fun m => u p ^ m := ren_congr p n n hlev
  have hsum : ∑ i ∈ range n, u p ^ i + u p ^ n = ∑ i ∈ range (n + 1), u p ^ i := (sum_range_succ _ n).symm
  obtain ⟨-, h2, -⟩ := ren_sharp p hp n hn
  rw [hren, hsum]
  exact ⟨h2, u_pow_rel p hp n⟩

/-- Proposition 24 (b) for ADD: ADD of `a = (1, u, …, u^{n-1})` and `b = (u^n, 0, …, 0)` errs by `u^n` -/
theorem prop24_add (hp : 1 < p) (n : ℕ) (hn : 2 ≤ n) :
    |(∑ i ∈ range n, u p ^ i + ∑ i ∈ range n, (if i = 0 then u p ^ n else 0)) -
        (addOp p n (fun i => u p ^ i) (fun i => if i = 0 then u p ^ n else 0)).sum| = u p ^ n ∧
      u p ^ n = u p ^ n * |∑ i ∈ range n, u p ^ i + ∑ i ∈ range n, (if i = 0 then u p ^ n else 0)| *
        (1 - u p) / (1 - u p ^ (n + 1)) := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, a = fun i => u p ^ i := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℝ, b = fun i => if i = 0 then u p ^ n else 0 := ⟨_, rfl⟩
  rw [← ha, ← hb]
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ × ℝ, g = fun i => twoSum p (a i) (b i) := ⟨_, rfl⟩
  have hg0 : g 0 = (1, u p ^ n) := by
    rw [hg, ha, hb]
    simpa using twoSum_pow_lt p hp 0 n (by omega)
  have hgi : ∀ i, 1 ≤ i → g i = (u p ^ i, 0) := fun i hi => by
    rw [hg, ha, hb]
    simp only [show i ≠ 0 by omega, ite_false]
    exact twoSum_zero p (F_u_pow p i)
  -- the assignments: `s_i = u^i` for `i < n` and `s_n = 0`
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hops : addOps p (k + 2) a b = (((List.range (k + 2)).map fun i => LOp.assign i (g i).1) ++
      [LOp.assign (k + 2) (g (k + 1)).2]) ++
      (LOp.dep 1 (u p ^ (k + 2)) :: (List.range k).map fun l => LOp.dep (l + 2) 0) := by
    have h1 : addOps p (k + 2) a b = pairOps (k + 2) g := by rw [hg]; rfl
    rw [h1]
    unfold pairOps
    rw [show k + 2 - 1 = k + 1 by omega]
    congr 1
    rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.map_map, List.map_map]
    congr 1
    · simp [hg0]
    · refine List.map_congr_left fun l _ => ?_
      simp [hgi (l + 1) (by omega)]
  obtain ⟨st1, hst1⟩ : ∃ st1, st1 = (runOps p (k + 2) (((List.range (k + 2)).map fun i => LOp.assign i (g i).1) ++
      [LOp.assign (k + 2) (g (k + 1)).2]) LState.init).2 := ⟨_, rfl⟩
  have hs1 : ∀ i, st1.s i = if i < k + 2 then u p ^ i else 0 := by
    intro i
    rw [hst1, (runOps_append p (k + 2) _ _ _).2]
    obtain ⟨-, h2⟩ := runOps_assigns p (k + 2) (fun i => (g i).1) (k + 2) LState.init (fun _ _ => rfl)
    simp only [runOps, stepOp, assignS]
    rw [hgi (k + 1) (by omega)]
    by_cases hik : i = k + 2
    · subst hik; simp
    · rw [Function.update_of_ne hik, h2]
      split_ifs with h
      · rcases Nat.eq_zero_or_pos i with rfl | hi
        · rw [hg0]; simp
        · rw [hgi i hi]
      · rfl
  -- the dep of `u^n` from level 1, then the deps of zero
  obtain ⟨st2, hst2⟩ : ∃ st2, st2 = (stepOp p (k + 2) (LOp.dep 1 (u p ^ (k + 2))) st1).2 := ⟨_, rfl⟩
  have hs2 : ∀ i, st2.s i = if i ≤ k + 2 then u p ^ i else 0 := by
    intro i
    rw [hst2]
    show (depRun p (k + 2) (k + 2 - 1) 1 (u p ^ (k + 2)) (entering 1 (u p ^ (k + 2)) st1)).2.s i = _
    rw [depRun_pow p hp (k + 2) (k + 2 - 1) 1 _ (by omega) (fun j hj1 hj2 => by
      show st1.s j = _; rw [hs1]; simp [hj2])]
    show Function.update st1.s (k + 2) (RN p (st1.s (k + 2) + u p ^ (k + 2))) i = _
    rw [hs1 (k + 2)]
    simp only [lt_irrefl, ite_false, zero_add]
    rw [RN_of_F p (F_u_pow p _)]
    by_cases hik : i = k + 2
    · subst hik; simp
    · rw [Function.update_of_ne hik, hs1]
      split_ifs <;> first | rfl | omega
  have hF2 : ∀ j, F p (st2.s j) := fun j => by
    rw [hs2]; split_ifs
    · exact F_u_pow p j
    · exact F_zero p
  have hc : ∀ i, (runOps p (k + 2) (addOps p (k + 2) a b) LState.init).2.s i =
      if i ≤ k + 2 then u p ^ i else 0 := by
    intro i
    rw [hops, (runOps_append p (k + 2) _ _ _).2, ← hst1]
    rw [show ∀ os st, (runOps p (k + 2) (LOp.dep 1 (u p ^ (k + 2)) :: os) st).2 =
      (runOps p (k + 2) os (stepOp p (k + 2) (LOp.dep 1 (u p ^ (k + 2))) st).2).2 from fun _ _ => rfl, ← hst2]
    rw [show ((List.range k).map fun l => LOp.dep (l + 2) 0) =
      ((List.range k).map fun l => l + 2).map fun l => LOp.dep l 0 by rw [List.map_map]; rfl]
    rw [runOps_deps_zero p (k + 2) _ st2 hF2, hs2]
  have hren : addOp p (k + 2) a b = ren p (k + 2) (k + 2) fun m => u p ^ m :=
    ren_congr p _ _ fun i hi => by
      show (runOps p (k + 2) (addOps p (k + 2) a b) LState.init).2.s i = _
      rw [hc i]
      simp [hi]
  have hsum : ∑ i ∈ range (k + 2), a i + ∑ i ∈ range (k + 2), b i = ∑ i ∈ range (k + 2 + 1), u p ^ i := by
    rw [sum_range_succ _ (k + 2), ha, hb]
    simp
  obtain ⟨-, h2, -⟩ := ren_sharp p hp (k + 2) (by omega)
  rw [hren, hsum]
  exact ⟨h2, u_pow_rel p hp (k + 2)⟩

end ExpansionBounds
