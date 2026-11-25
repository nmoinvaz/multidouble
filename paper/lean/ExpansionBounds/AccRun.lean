import ExpansionBounds.AccSum
import ExpansionBounds.RoundEval

/-!
# The accumulator run on rationals

The accumulator of sums, ADDX terms and then FINISH, as a computation on rationals: a dep is a chain of `twoSumQ`
down the levels and a rounding `rnQ` at level `n`, and FINISH is ADDF's chain, VecSum and the second pass of the
renormalization. Each mirror, cast to `ℝ`, is the paper's operation on the cast inputs, as long as the inputs are in
`F p`, where TwoSum is exact (Lemma 8 (a)). So the kernel can run the accumulator on given terms.
-/

namespace ExpansionBounds

open Finset

section Mirrors

variable (p : ℤ) (n : ℕ)

/-- the levels after a dep from level `m` with `k = n - m` `TwoSum`s before level `n` -/
def depSQ : ℕ → ℕ → ℚ → (ℕ → ℚ) → ℕ → ℚ
  | 0, _, e, s => Function.update s n (rnQ p (s n + e))
  | k + 1, m, e, s => depSQ k (m + 1) (twoSumQ p (s m) e).2 (Function.update s m (twoSumQ p (s m) e).1)

/-- the levels after ADDX of `t`: a dep of `t_l` at each level `l < n` -/
def addxQ (t : ℕ → ℚ) (s : ℕ → ℚ) : ℕ → ℚ := (List.range n).foldl (fun s l => depSQ p n (n - l) l (t l) s) s

/-- the levels after ADDX of each term of a list -/
def accRunQ (ts : List (ℕ → ℚ)) (s : ℕ → ℚ) : ℕ → ℚ := ts.foldl (fun s t => addxQ p n t s) s

/-- ADDF's carries -/
def addfEQ (a : ℕ → ℚ) (b : ℚ) : ℕ → ℚ
  | 0 => b
  | m + 1 => (twoSumQ p (a m) (addfEQ a b m)).2

/-- ADDF's levels -/
def addfLevelsQ (a : ℕ → ℚ) (b : ℚ) (m : ℕ) : ℚ :=
  if m < n then (twoSumQ p (a m) (addfEQ p a b m)).1 else if m = n then addfEQ p a b n else 0

/-- VecSum -/
def vecSumQ : ℕ → (ℕ → ℚ) → ℕ → ℚ
  | 0, c => fun j => if j = 0 then c 0 else 0
  | m + 1, c => fun j =>
    if j = 0 then (twoSumQ p (c 0) (vecSumQ m (fun i => c (i + 1)) 0)).1
    else if j = 1 then (twoSumQ p (c 0) (vecSumQ m (fun i => c (i + 1)) 0)).2
    else vecSumQ m (fun i => c (i + 1)) (j - 1)

/-- the second pass of `Ren_n` -/
def renPassQ : ℕ → ℚ → List ℚ → List ℚ
  | _, acc, [] => [acc]
  | b, acc, v :: vs =>
    if b ≠ 0 ∧ (twoSumQ p acc v).2 ≠ 0 then (twoSumQ p acc v).1 :: renPassQ (b - 1) (twoSumQ p acc v).2 vs
    else renPassQ b (twoSumQ p acc v).1 vs

/-- `Ren_n` -/
def renQ (n m : ℕ) (c : ℕ → ℚ) : List ℚ :=
  renPassQ p (n - 1) (vecSumQ p m c 0) ((List.range m).map fun j => vecSumQ p m c (j + 1))

/-- ADDF -/
def addfOpQ (a : ℕ → ℚ) (b : ℚ) : List ℚ := renQ p n n (addfLevelsQ p n a b)

/-- FINISH: `r^{(0)} = (s_0, 0, …, 0)` and `r^{(l)} = ADDF(r^{(l-1)}, s_l)` -/
def finishRQ (s : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0 => fun i => if i = 0 then s 0 else 0
  | l + 1 => fun i => (addfOpQ p n (finishRQ s l) (s (l + 1))).getD i 0

end Mirrors

variable (p : ℤ) [Prec_gt_0 p] (n : ℕ)

/-! ### The levels after ADDX, through `depS`, the levels after a dep without the totals of Lemma 11's proof -/

/-- the levels after ADDX of `t` -/
noncomputable def addxS (t : ℕ → ℝ) (s : ℕ → ℝ) : ℕ → ℝ :=
  (List.range n).foldl (fun s l => depS p n (n - l) l (t l) s) s

omit [Prec_gt_0 p] in
theorem runOps_deps_s (t : ℕ → ℝ) : ∀ (ls : List ℕ) (st : LState),
    (runOps p n (ls.map fun l => LOp.dep l (t l)) st).2.s = ls.foldl (fun s l => depS p n (n - l) l (t l) s) st.s
  | [], _ => rfl
  | l :: ls, st => by
    simp only [List.map_cons, runOps, List.foldl_cons]
    rw [runOps_deps_s t ls]
    congr 1
    exact depRun_s p n (n - l) l (t l) (entering l (t l) st)

omit [Prec_gt_0 p] in
/-- the levels after `K + 1` ADDX terms are ADDX of the last term on those after `K` -/
theorem accLevX_succ (a : ℕ → ℕ → ℝ) (K : ℕ) : accLevX p n a (K + 1) = addxS p n (a (K + 1)) (accLevX p n a K) := by
  unfold accLevX addxS
  rw [accOps_succ, (runOps_append p n _ _ _).2]
  have hd : depositOps n (a (K + 1)) false = (List.range n).map fun l => LOp.dep l (a (K + 1) l) := by
    simp [depositOps]
  rw [hd, runOps_deps_s]

omit [Prec_gt_0 p] in
theorem accLevX_zero (a : ℕ → ℕ → ℝ) : accLevX p n a 0 = fun _ => 0 := rfl

/-! ### The casts -/

omit [Prec_gt_0 p] in
theorem cast_update (s : ℕ → ℚ) (m : ℕ) (v : ℚ) :
    (fun j => ((Function.update s m v j : ℚ) : ℝ)) = Function.update (fun j => (s j : ℝ)) m (v : ℝ) := by
  funext j
  simp only [Function.update_apply]
  split_ifs <;> rfl

/-- a dep on rationals of `F p`: its levels cast to those of the dep, and they stay in `F p` -/
theorem cast_depS (hp : 1 < p) : ∀ (k m : ℕ) (e : ℚ) (s : ℕ → ℚ), F p (e : ℝ) → (∀ j, F p (s j : ℝ)) →
    (fun j => ((depSQ p n k m e s j : ℚ) : ℝ)) = depS p n k m e (fun j => (s j : ℝ)) ∧
      ∀ j, F p (depSQ p n k m e s j : ℝ)
  | 0, _, e, s, _, hs => by
    have hr : ((rnQ p (s n + e) : ℚ) : ℝ) = RN p ((s n : ℝ) + e) := by
      rw [cast_rn]
      push_cast
      rfl
    refine ⟨?_, fun j => ?_⟩
    · simp only [depSQ, depS, cast_update, hr]
    · simp only [depSQ, Function.update_apply]
      split_ifs
      · rw [hr]
        exact F_RN p _
      · exact hs j
  | k + 1, m, e, s, he, hs => by
    have ht := cast_twoSum p hp (hs m) he
    have h1 : F p ((twoSumQ p (s m) e).1 : ℝ) := by
      have := F_twoSum_fst p (s m : ℝ) (e : ℝ)
      rwa [ht] at this
    have h2 : F p ((twoSumQ p (s m) e).2 : ℝ) := by
      have := F_twoSum_snd p (s m : ℝ) (e : ℝ)
      rwa [ht] at this
    have hs' : ∀ j, F p (Function.update s m (twoSumQ p (s m) e).1 j : ℝ) := fun j => by
      simp only [Function.update_apply]
      split_ifs
      · exact h1
      · exact hs j
    obtain ⟨c1, c2⟩ := cast_depS hp k (m + 1) (twoSumQ p (s m) e).2 (Function.update s m (twoSumQ p (s m) e).1) h2 hs'
    refine ⟨?_, c2⟩
    simp only [depSQ, depS]
    rw [c1, cast_update, ht]

/-- ADDX on rationals of `F p` -/
theorem cast_addx (hp : 1 < p) (t : ℕ → ℚ) (ht : ∀ l, F p (t l : ℝ)) : ∀ (ls : List ℕ) (s : ℕ → ℚ),
    (∀ j, F p (s j : ℝ)) →
    (fun j => ((ls.foldl (fun s l => depSQ p n (n - l) l (t l) s) s j : ℚ) : ℝ)) =
        ls.foldl (fun s l => depS p n (n - l) l ((t l : ℚ) : ℝ) s) (fun j => (s j : ℝ)) ∧
      ∀ j, F p (ls.foldl (fun s l => depSQ p n (n - l) l (t l) s) s j : ℝ)
  | [], _, hs => ⟨rfl, hs⟩
  | l :: ls, s, hs => by
    obtain ⟨c1, c2⟩ := cast_depS p n hp (n - l) l (t l) s (ht l) hs
    obtain ⟨d1, d2⟩ := cast_addx hp t ht ls (depSQ p n (n - l) l (t l) s) c2
    refine ⟨?_, d2⟩
    simp only [List.foldl_cons]
    rw [d1, c1]

/-- the accumulator's levels after the terms of a list, on rationals of `F p` -/
theorem cast_accRun (hp : 1 < p) : ∀ (ts : List (ℕ → ℚ)) (s : ℕ → ℚ), (∀ t ∈ ts, ∀ l, F p (t l : ℝ)) →
    (∀ j, F p (s j : ℝ)) →
    (fun j => ((accRunQ p n ts s j : ℚ) : ℝ)) =
        ts.foldl (fun s t => addxS p n (fun l => (t l : ℝ)) s) (fun j => (s j : ℝ)) ∧
      ∀ j, F p (accRunQ p n ts s j : ℝ)
  | [], _, _, hs => ⟨rfl, hs⟩
  | t :: ts, s, ht, hs => by
    obtain ⟨c1, c2⟩ := cast_addx p n hp t (ht t List.mem_cons_self) (List.range n) s hs
    obtain ⟨d1, d2⟩ := cast_accRun hp ts (addxQ p n t s) (fun t' h => ht t' (List.mem_cons_of_mem _ h)) c2
    refine ⟨?_, d2⟩
    unfold accRunQ at d1 ⊢
    simp only [List.foldl_cons]
    rw [d1]
    congr 1

/-- ADDF's carries on rationals of `F p` -/
theorem cast_addfE (hp : 1 < p) (a : ℕ → ℚ) (b : ℚ) (ha : ∀ m, F p (a m : ℝ)) (hb : F p (b : ℝ)) :
    ∀ m, ((addfEQ p a b m : ℚ) : ℝ) = addfE p (fun i => (a i : ℝ)) b m ∧ F p (addfEQ p a b m : ℝ)
  | 0 => ⟨rfl, hb⟩
  | m + 1 => by
    obtain ⟨i1, i2⟩ := cast_addfE hp a b ha hb m
    have ht := cast_twoSum p hp (ha m) i2
    have h2 : F p ((twoSumQ p (a m) (addfEQ p a b m)).2 : ℝ) := by
      have := F_twoSum_snd p (a m : ℝ) (addfEQ p a b m : ℝ)
      rwa [ht] at this
    refine ⟨?_, h2⟩
    simp only [addfEQ, addfE]
    rw [← i1, ht]

/-- ADDF's levels on rationals of `F p` -/
theorem cast_addfLevels (hp : 1 < p) (a : ℕ → ℚ) (b : ℚ) (ha : ∀ m, F p (a m : ℝ)) (hb : F p (b : ℝ)) (m : ℕ) :
    ((addfLevelsQ p n a b m : ℚ) : ℝ) = addfLevels p n (fun i => (a i : ℝ)) b m ∧
      F p (addfLevelsQ p n a b m : ℝ) := by
  have he := cast_addfE p hp a b ha hb
  unfold addfLevelsQ addfLevels
  split_ifs
  · have ht := cast_twoSum p hp (ha m) (he m).2
    have h1 : F p ((twoSumQ p (a m) (addfEQ p a b m)).1 : ℝ) := by
      have := F_twoSum_fst p (a m : ℝ) (addfEQ p a b m : ℝ)
      rwa [ht] at this
    refine ⟨?_, h1⟩
    rw [← (he m).1, ht]
  · exact he n
  · exact ⟨Rat.cast_zero, by rw [Rat.cast_zero]; exact F_zero p⟩

/-- VecSum on rationals of `F p` -/
theorem cast_vecSum (hp : 1 < p) : ∀ (m : ℕ) (c : ℕ → ℚ), (∀ i, F p (c i : ℝ)) →
    ∀ j, ((vecSumQ p m c j : ℚ) : ℝ) = vecSum p m (fun i => (c i : ℝ)) j ∧ F p (vecSumQ p m c j : ℝ)
  | 0, c, hc => fun j => by
    simp only [vecSumQ, vecSum]
    split_ifs
    · exact ⟨rfl, hc 0⟩
    · exact ⟨Rat.cast_zero, by rw [Rat.cast_zero]; exact F_zero p⟩
  | m + 1, c, hc => fun j => by
    have ih := cast_vecSum hp m (fun i => c (i + 1)) (fun i => hc (i + 1))
    have ht := cast_twoSum p hp (hc 0) (ih 0).2
    have h1 : F p ((twoSumQ p (c 0) (vecSumQ p m (fun i => c (i + 1)) 0)).1 : ℝ) := by
      have := F_twoSum_fst p (c 0 : ℝ) (vecSumQ p m (fun i => c (i + 1)) 0 : ℝ)
      rwa [ht] at this
    have h2 : F p ((twoSumQ p (c 0) (vecSumQ p m (fun i => c (i + 1)) 0)).2 : ℝ) := by
      have := F_twoSum_snd p (c 0 : ℝ) (vecSumQ p m (fun i => c (i + 1)) 0 : ℝ)
      rwa [ht] at this
    simp only [vecSumQ, vecSum]
    split_ifs
    · refine ⟨?_, h1⟩
      rw [← (ih 0).1, ht]
    · refine ⟨?_, h2⟩
      rw [← (ih 0).1, ht]
    · exact ih (j - 1)

/-- the second pass on rationals of `F p` -/
theorem cast_renPass (hp : 1 < p) : ∀ (vs : List ℚ) (b : ℕ) (acc : ℚ), F p (acc : ℝ) → (∀ v ∈ vs, F p (v : ℝ)) →
    (renPassQ p b acc vs).map (fun q : ℚ => (q : ℝ)) = renPass p b acc (vs.map fun q : ℚ => (q : ℝ)) ∧
      ∀ q ∈ renPassQ p b acc vs, F p (q : ℝ)
  | [], _, acc, ha, _ => by
    refine ⟨rfl, fun q hq => ?_⟩
    simp only [renPassQ, List.mem_singleton] at hq
    rw [hq]
    exact ha
  | v :: vs, b, acc, ha, hv => by
    have hvs : ∀ w ∈ vs, F p (w : ℝ) := fun w hw => hv w (List.mem_cons_of_mem _ hw)
    have ht := cast_twoSum p hp ha (hv v List.mem_cons_self)
    have h1 : F p ((twoSumQ p acc v).1 : ℝ) := by
      have := F_twoSum_fst p (acc : ℝ) (v : ℝ)
      rwa [ht] at this
    have h2 : F p ((twoSumQ p acc v).2 : ℝ) := by
      have := F_twoSum_snd p (acc : ℝ) (v : ℝ)
      rwa [ht] at this
    have hne : ((twoSumQ p acc v).2 ≠ 0) ↔ ((((twoSumQ p acc v).2 : ℚ) : ℝ) ≠ 0) := by
      rw [Ne, Ne, Rat.cast_eq_zero]
    simp only [renPassQ, List.map_cons, renPass, ht]
    by_cases hc : b ≠ 0 ∧ (twoSumQ p acc v).2 ≠ 0
    · have hc' : b ≠ 0 ∧ (((twoSumQ p acc v).2 : ℚ) : ℝ) ≠ 0 := ⟨hc.1, hne.mp hc.2⟩
      rw [ite_eq_left hc, ite_eq_left hc']
      obtain ⟨i1, i2⟩ := cast_renPass hp vs (b - 1) (twoSumQ p acc v).2 h2 hvs
      refine ⟨?_, fun q hq => ?_⟩
      · rw [List.map_cons, i1]
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact h1
        · exact i2 q hq
    · have hc' : ¬(b ≠ 0 ∧ (((twoSumQ p acc v).2 : ℚ) : ℝ) ≠ 0) := fun h => hc ⟨h.1, hne.mpr h.2⟩
      rw [ite_eq_right hc, ite_eq_right hc']
      exact cast_renPass hp vs b (twoSumQ p acc v).1 h1 hvs

/-- `Ren_n` on rationals of `F p` -/
theorem cast_ren (hp : 1 < p) (m : ℕ) (c : ℕ → ℚ) (hc : ∀ i, F p (c i : ℝ)) :
    (renQ p n m c).map (fun q : ℚ => (q : ℝ)) = ren p n m (fun i => (c i : ℝ)) ∧
      ∀ q ∈ renQ p n m c, F p (q : ℝ) := by
  have hv := cast_vecSum p hp m c hc
  have hvs : ∀ v ∈ (List.range m).map (fun j => vecSumQ p m c (j + 1)), F p (v : ℝ) := fun v hvm => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hvm
    exact (hv (j + 1)).2
  obtain ⟨i1, i2⟩ := cast_renPass p hp _ (n - 1) (vecSumQ p m c 0) (hv 0).2 hvs
  refine ⟨?_, i2⟩
  unfold renQ ren
  rw [i1, (hv 0).1, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  exact (hv (j + 1)).1

omit [Prec_gt_0 p] in
/-- a list's entries past its end read as zero, on both sides of the cast -/
theorem cast_getD (l : List ℚ) (i : ℕ) : ((l.getD i 0 : ℚ) : ℝ) = (l.map fun q : ℚ => (q : ℝ)).getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp

/-- FINISH on rationals of `F p`: each `r^{(l)}` casts to the paper's, and stays in `F p` -/
theorem cast_finishR (hp : 1 < p) (s : ℕ → ℚ) (hs : ∀ j, F p (s j : ℝ)) :
    ∀ l i, ((finishRQ p n s l i : ℚ) : ℝ) = finishR p n (fun j => (s j : ℝ)) l i ∧ F p (finishRQ p n s l i : ℝ)
  | 0, i => by
    simp only [finishRQ, finishR]
    split_ifs
    · exact ⟨rfl, hs 0⟩
    · exact ⟨Rat.cast_zero, by rw [Rat.cast_zero]; exact F_zero p⟩
  | l + 1, i => by
    have ih := cast_finishR hp s hs l
    have hr : (fun i => ((finishRQ p n s l i : ℚ) : ℝ)) = finishR p n (fun j => (s j : ℝ)) l :=
      funext fun i => (ih i).1
    have hlev := cast_addfLevels p n hp (finishRQ p n s l) (s (l + 1)) (fun m => (ih m).2) (hs (l + 1))
    have hc : (fun m => ((addfLevelsQ p n (finishRQ p n s l) (s (l + 1)) m : ℚ) : ℝ)) =
        addfLevels p n (finishR p n (fun j => (s j : ℝ)) l) (s (l + 1) : ℝ) := by
      funext m
      rw [(hlev m).1, hr]
    obtain ⟨r1, r2⟩ := cast_ren p n hp n (addfLevelsQ p n (finishRQ p n s l) (s (l + 1))) fun m => (hlev m).2
    rw [hc] at r1
    refine ⟨?_, ?_⟩
    · show (((addfOpQ p n (finishRQ p n s l) (s (l + 1))).getD i 0 : ℚ) : ℝ) =
        pt (addfOp p n (finishR p n (fun j => (s j : ℝ)) l) (s (l + 1) : ℝ)) i
      rw [cast_getD]
      unfold addfOpQ pt addfOp
      rw [r1]
    · show F p (((addfOpQ p n (finishRQ p n s l) (s (l + 1))).getD i 0 : ℚ) : ℝ)
      rw [List.getD_eq_getElem?_getD]
      cases hget : (addfOpQ p n (finishRQ p n s l) (s (l + 1)))[i]? with
      | none =>
        simp only [Option.getD_none, Rat.cast_zero]
        exact F_zero p
      | some q =>
        simp only [Option.getD_some]
        exact r2 q (List.mem_of_getElem? hget)

/-! ### A run on dyadic data -/

/-- `m/2^k` -/
def dyQ (mk : ℤ × ℕ) : ℚ := mk.1 / 2 ^ mk.2

/-- a list of dyadic rationals as a function, zero past its end -/
def dyFn (l : List (ℤ × ℕ)) : ℕ → ℚ := fun i => dyQ (l.getD i (0, 0))

omit [Prec_gt_0 p] in
theorem dyQ_zero : dyQ (0, 0) = 0 := by simp [dyQ]

omit [Prec_gt_0 p] in
theorem dyFn_of_le (l : List (ℤ × ℕ)) {i : ℕ} (h : l.length ≤ i) : dyFn l i = 0 := by
  unfold dyFn
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  simp only [Option.getD_none, dyQ_zero]

omit [Prec_gt_0 p] in
/-- a dep leaves the levels above `n` as they are -/
theorem depSQ_above : ∀ (k m : ℕ) (e : ℚ) (s : ℕ → ℚ) (j : ℕ), m + k = n → n < j → depSQ p n k m e s j = s j
  | 0, m, e, s, j, hm, hj => by
    simp only [depSQ]
    rw [Function.update_of_ne (by omega)]
  | k + 1, m, e, s, j, hm, hj => by
    simp only [depSQ]
    rw [depSQ_above k (m + 1) _ _ j (by omega) hj, Function.update_of_ne (by omega)]

omit [Prec_gt_0 p] in
theorem addxQ_above (t s : ℕ → ℚ) {j : ℕ} (hj : n < j) : addxQ p n t s j = s j := by
  have key : ∀ (ls : List ℕ) (s : ℕ → ℚ), (∀ l ∈ ls, l < n) →
      ls.foldl (fun s l => depSQ p n (n - l) l (t l) s) s j = s j := by
    intro ls
    induction ls with
    | nil => intro s _; rfl
    | cons l ls ih =>
      intro s hl
      have hln : l < n := hl l List.mem_cons_self
      rw [List.foldl_cons, ih _ fun l' h => hl l' (List.mem_cons_of_mem _ h),
        depSQ_above p n (n - l) l _ _ j (by omega) hj]
  exact key _ s fun l hl => List.mem_range.mp hl

omit [Prec_gt_0 p] in
theorem accRunQ_above (ts : List (ℕ → ℚ)) (s : ℕ → ℚ) {j : ℕ} (hj : n < j) : accRunQ p n ts s j = s j := by
  unfold accRunQ
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih => rw [List.foldl_cons, ih, addxQ_above p n t s hj]

omit [Prec_gt_0 p] in
/-- a run over two lists is the second from the levels the first leaves -/
theorem accRunQ_append (xs ys : List (ℕ → ℚ)) (s : ℕ → ℚ) :
    accRunQ p n (xs ++ ys) s = accRunQ p n ys (accRunQ p n xs s) := by
  unfold accRunQ
  rw [List.foldl_append]

omit [Prec_gt_0 p] in
/-- the levels after a run, from their values at `0, …, n`: a run from levels zero above `n` -/
theorem accRunQ_eq_dyFn (ts : List (ℕ → ℚ)) (s : ℕ → ℚ) (hs : ∀ j, n < j → s j = 0) (S' : List (ℤ × ℕ))
    (hS' : S'.length = n + 1) (h : (List.range (n + 1)).map (accRunQ p n ts s) = S'.map dyQ) :
    accRunQ p n ts s = dyFn S' := by
  funext j
  rcases Nat.lt_or_ge n j with hj | hj
  · rw [accRunQ_above p n ts s hj, hs j hj, dyFn_of_le S' (by omega)]
  · have hj' : j < n + 1 := by omega
    have hl : ((List.range (n + 1)).map (accRunQ p n ts s)).getD j 0 = accRunQ p n ts s j := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj']
      rfl
    have hr : (S'.map dyQ).getD j 0 = dyFn S' j := by
      unfold dyFn
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases S'[j]? <;> simp [dyQ_zero]
    rw [← hl, h, hr]

omit [Prec_gt_0 p] in
/-- the levels after `K` ADDX terms, as a fold over `0, …, K - 1` -/
theorem accLevX_range (a : ℕ → ℕ → ℝ) :
    ∀ K, accLevX p n a K = (List.range K).foldl (fun s j => addxS p n (a (j + 1)) s) fun _ => 0
  | 0 => rfl
  | K + 1 => by
    rw [accLevX_succ, accLevX_range a K, List.range_succ, List.foldl_append]
    rfl

omit [Prec_gt_0 p] in
/-- the levels after `K` terms depend on the first `K` terms only -/
theorem accLevX_congr (a b : ℕ → ℕ → ℝ) :
    ∀ K, (∀ k, 1 ≤ k → k ≤ K → a k = b k) → accLevX p n a K = accLevX p n b K
  | 0, _ => rfl
  | K + 1, h => by
    rw [accLevX_succ, accLevX_succ, accLevX_congr a b K fun k h1 h2 => h k h1 (by omega),
      h (K + 1) (by omega) le_rfl]

omit [Prec_gt_0 p] in
theorem map_range_getD {α : Type*} (T : List α) (d : α) : (List.range T.length).map (fun j => T.getD j d) = T := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- an entry of a list within its length is one of its members -/
theorem getD_mem {α : Type*} (T : List α) (d : α) {j : ℕ} (h : j < T.length) : T.getD j d ∈ T := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

/-- an entry of a list after its first is a member of its tail -/
theorem getD_mem_tail {α : Type*} (T : List α) (d : α) {k : ℕ} (h1 : 2 ≤ k) (h2 : k ≤ T.length) :
    T.getD (k - 1) d ∈ T.tail := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  cases T with
  | nil => simp at h2
  | cons a T' =>
    rw [List.tail_cons, show j + 2 - 1 = j + 1 by omega, List.getD_cons_succ]
    exact getD_mem T' d (by simpa using h2)

omit [Prec_gt_0 p] in
theorem sum_Icc_one (g : ℕ → ℝ) (K : ℕ) : ∑ k ∈ Icc 1 K, g k = ((List.range K).map fun j => g (j + 1)).sum := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, List.range_succ, List.map_append, List.sum_append]
    simp

/-- the terms of a list of dyadic data: term `k` is its `k`-th entry -/
noncomputable def dyTerms (T : List (List (ℤ × ℕ))) : ℕ → ℕ → ℝ := fun k i => ((dyFn (T.getD (k - 1) []) i : ℚ) : ℝ)

omit [Prec_gt_0 p] in
/-- the exact sum of the data's terms is the cast of the data's -/
theorem dyTerms_sum (T : List (List (ℤ × ℕ))) :
    ∑ k ∈ Icc 1 T.length, ∑ i ∈ range n, dyTerms T k i =
      (((T.map fun t => ∑ i ∈ range n, dyFn t i).sum : ℚ) : ℝ) := by
  rw [sum_Icc_one]
  conv_rhs => rw [← map_range_getD T []]
  rw [List.map_map, Rat.cast_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply, dyTerms, Nat.add_sub_cancel, Rat.cast_sum]

/-- the accumulator on a list of dyadic terms in `F p`: FINISH's parts and the exact sum are the casts of what the
rational run computes -/
theorem accRun_data (hp : 1 < p) (T : List (List (ℤ × ℕ))) (hF : ∀ t ∈ T, ∀ l, F p (dyFn t l : ℝ)) :
    (∀ i, finishR p n (accLevX p n (dyTerms T) T.length) n i =
        ((finishRQ p n (accRunQ p n (T.map dyFn) fun _ => 0) n i : ℚ) : ℝ)) ∧
      ∑ k ∈ Icc 1 T.length, ∑ i ∈ range n, dyTerms T k i =
        (((T.map fun t => ∑ i ∈ range n, dyFn t i).sum : ℚ) : ℝ) := by
  have h0 : ∀ j, F p (((fun _ => 0 : ℕ → ℚ) j : ℚ) : ℝ) := fun j => by
    rw [Rat.cast_zero]
    exact F_zero p
  obtain ⟨c1, c2⟩ := cast_accRun p n hp (T.map dyFn) (fun _ => 0) (fun t ht l => by
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    exact hF t' ht' l) h0
  have hlev : accLevX p n (dyTerms T) T.length =
      fun j => ((accRunQ p n (T.map dyFn) (fun _ => 0) j : ℚ) : ℝ) := by
    rw [c1, accLevX_range, List.foldl_map]
    conv_rhs => rw [← map_range_getD T []]
    rw [List.foldl_map]
    simp only [Rat.cast_zero]
    rfl
  constructor
  · intro i
    rw [hlev]
    exact ((cast_finishR p n hp _ c2 n i).1).symm
  · exact dyTerms_sum n T

/-- the first `K` terms of the data are the terms of its first `K` entries -/
theorem dyTerms_take (T : List (List (ℤ × ℕ))) {K k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ K) :
    dyTerms (T.take K) k = dyTerms T k := by
  funext i
  unfold dyTerms
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]

/-- `accRun_data` for the first `K` terms: FINISH after them and their exact sum -/
theorem accRun_prefix (hp : 1 < p) (T : List (List (ℤ × ℕ))) (hF : ∀ t ∈ T, ∀ l, F p (dyFn t l : ℝ)) {K : ℕ}
    (hK : K ≤ T.length) :
    (∀ i, finishR p n (accLevX p n (dyTerms T) K) n i =
        ((finishRQ p n (accRunQ p n ((T.take K).map dyFn) fun _ => 0) n i : ℚ) : ℝ)) ∧
      ∑ k ∈ Icc 1 K, ∑ i ∈ range n, dyTerms T k i =
        ((((T.take K).map fun t => ∑ i ∈ range n, dyFn t i).sum : ℚ) : ℝ) := by
  have hlen : (T.take K).length = K := by rw [List.length_take, min_eq_left hK]
  obtain ⟨c1, c2⟩ := accRun_data p n hp (T.take K) fun t ht l => hF t (List.mem_of_mem_take ht) l
  rw [hlen] at c1 c2
  constructor
  · intro i
    rw [← c1 i, accLevX_congr p n (dyTerms T) (dyTerms (T.take K)) K fun k h1 h2 => (dyTerms_take T h1 h2).symm]
  · rw [← c2]
    refine sum_congr rfl fun k hk => ?_
    obtain ⟨h1, h2⟩ := mem_Icc.mp hk
    rw [dyTerms_take T h1 h2]

/-- `W`, the sum of the leading parts' sizes, is the cast of the data's -/
theorem dyTerms_lead_sum (T : List (List (ℤ × ℕ))) :
    ∑ k ∈ Icc 1 T.length, |dyTerms T k 0| = (((T.map fun t => |dyFn t 0|).sum : ℚ) : ℝ) := by
  rw [sum_Icc_one]
  conv_rhs => rw [← map_range_getD T []]
  rw [List.map_map, Rat.cast_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply, dyTerms, Nat.add_sub_cancel, Rat.cast_abs]

omit [Prec_gt_0 p] in
/-- a part of size at most `2^(magQ q - p - 1)` is within half an ulp of `q`: the `e` of `q` and the three bounds -/
theorem half_ulp_cast {q r : ℚ} (hq : q ≠ 0) (h : |r| ≤ (2 : ℚ) ^ (magQ q - p - 1)) :
    ∃ e : ℤ, (2 : ℝ) ^ (e - 1) ≤ |(q : ℝ)| ∧ |(q : ℝ)| < (2 : ℝ) ^ e ∧ |(r : ℝ)| ≤ (2 : ℝ) ^ (e - p - 1) := by
  obtain ⟨lo, hi⟩ := magQ_spec hq
  refine ⟨magQ q, ?_, ?_, ?_⟩
  · have := (Rat.cast_le (K := ℝ)).mpr lo
    rwa [Rat.cast_abs, Rat.cast_zpow, Rat.cast_ofNat] at this
  · have := (Rat.cast_lt (K := ℝ)).mpr hi
    rwa [Rat.cast_abs, Rat.cast_zpow, Rat.cast_ofNat] at this
  · have := (Rat.cast_le (K := ℝ)).mpr h
    rwa [Rat.cast_abs, Rat.cast_zpow, Rat.cast_ofNat] at this

/-- dyadic data that `rnQ` leaves as it is lies in `F p`, as do the zeros past a term's end -/
theorem dyF_of_all (T : List (List (ℤ × ℕ))) (h : ∀ t ∈ T, ∀ q ∈ t, rnQ p (dyQ q) = dyQ q) :
    ∀ t ∈ T, ∀ l, F p (dyFn t l : ℝ) := by
  intro t ht l
  unfold dyFn
  rw [List.getD_eq_getElem?_getD]
  cases hq : t[l]? with
  | none =>
    simp only [Option.getD_none, dyQ_zero, Rat.cast_zero]
    exact F_zero p
  | some q =>
    simp only [Option.getD_some]
    exact (F_iff_rn p _).mpr (h t ht q (List.mem_of_getElem? hq))

/-- every part of every term of dyadic data in `F p` is in `F p` -/
theorem dyTerms_F (T : List (List (ℤ × ℕ))) (hF : ∀ t ∈ T, ∀ l, F p (dyFn t l : ℝ)) (k i : ℕ) :
    F p (dyTerms T k i) := by
  unfold dyTerms
  rw [List.getD_eq_getElem?_getD]
  cases ht : T[k - 1]? with
  | none =>
    simp only [Option.getD_none]
    rw [dyFn_of_le [] (Nat.zero_le _), Rat.cast_zero]
    exact F_zero p
  | some t =>
    simp only [Option.getD_some]
    exact hF t (List.mem_of_getElem? ht) i

omit [Prec_gt_0 p] in
/-- parts with `|a_{i+1}| ≤ u|a_i|` are on `H(1)` -/
theorem Htheta_of_steps (a : ℕ → ℝ) (h : ∀ i, i + 1 < n → |a (i + 1)| ≤ u p * |a i|) : Htheta p n 1 a := by
  have hu := u_pos p
  have key : ∀ i, i < n → |a i| ≤ u p ^ i * |a 0| := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      calc |a (i + 1)| ≤ u p * |a i| := h i hi
        _ ≤ u p * (u p ^ i * |a 0|) := mul_le_mul_of_nonneg_left (ih (by omega)) hu.le
        _ = u p ^ (i + 1) * |a 0| := by ring
  intro i _ hi
  rw [one_mul]
  exact key i hi

end ExpansionBounds
