import ExpansionBounds.Sharp
import ExpansionBounds.Acc

/-!
# Theorem 27: the accumulator

ADDPROD deposits MUL's levels, within `L_l u^l μ_k` by Theorem 14, and ADDX the parts of its operand, within
`ρ^l μ_k`; so the accumulator's lemma applies with `τ_l = max(L_l u^l, ρ^l)`. FINISH sets `r^{(0)} = (s_0, 0, …)` and
`r^{(l)} = ADDF(r^{(l-1)}, s_l)`. Each `r^{(l)}` is zero above index `l`, so for `l ≤ n - 1` the last level of the ADDF
is zero and the ADDF is exact; only the last ADDF loses, by Lemma 13 with the part bounds along FINISH.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) [Prec_gt_0 p]

/-- `TwoSum(0, e) = (e, 0)` for `e ∈ F` -/
theorem twoSum_zero_left (hp : 1 < p) {e : ℝ} (he : F p e) : twoSum p 0 e = (e, 0) := by
  obtain ⟨h1, -, h3⟩ := facts_a p hp (F_zero p) he
  have h2 : (twoSum p 0 e).2 = 0 := h3.mpr (by rwa [zero_add])
  exact Prod.ext (by linarith) h2

/-- VecSum of zero levels is zero -/
theorem vecSum_zeros : ∀ (m : ℕ) (c : ℕ → ℝ), (∀ i ≤ m, c i = 0) → ∀ i, vecSum p m c i = 0 := by
  intro m
  induction m with
  | zero => intro c hc i; simp [vecSum, hc 0 le_rfl]
  | succ m ih =>
    intro c hc i
    have h' := ih (fun i => c (i + 1)) (fun i hi => hc (i + 1) (by omega))
    have htw : twoSum p (c 0) (vecSum p m (fun i => c (i + 1)) 0) = (0, 0) := by
      rw [h' 0, hc 0 (by omega)]; exact twoSum_zero p (F_zero p)
    simp only [vecSum, htw]
    split_ifs <;> first | rfl | exact h' _

/-- VecSum of levels zero above `j` is zero above `j` -/
theorem vecSum_zero_above : ∀ (m : ℕ) (c : ℕ → ℝ) (j : ℕ), (∀ i ≤ m, F p (c i)) →
    (∀ i, j < i → i ≤ m → c i = 0) → ∀ i, j < i → vecSum p m c i = 0 := by
  intro m
  induction m with
  | zero =>
    intro c j _ _ i hi
    simp [vecSum, show i ≠ 0 by omega]
  | succ m ih =>
    intro c j hF hz i hi
    rcases Nat.lt_or_ge i 2 with hi2 | hi2
    · obtain rfl : i = 1 := by omega
      obtain rfl : j = 0 := by omega
      have h0 := vecSum_zeros p m (fun i => c (i + 1)) (fun i hi => hz (i + 1) (by omega) (by omega)) 0
      rw [vecSum_succ_one, h0, twoSum_zero p (hF 0 (by omega))]
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 + 1 := ⟨i - 2, by omega⟩
      rw [vecSum_succ_add_two]
      exact ih (fun i => c (i + 1)) (j - 1) (fun i hi => hF (i + 1) (by omega))
        (fun i hi1 hi2 => hz (i + 1) (by omega) (by omega)) (i' + 1) (by omega)

/-- the second pass with trailing zero terms emits nothing after them -/
theorem renPass_zeros (k : ℕ) : ∀ (b : ℕ) (acc : ℝ), F p acc → renPass p b acc (List.replicate k 0) = [acc] := by
  induction k with
  | zero => intro b acc _; rfl
  | succ k ih =>
    intro b acc ha
    rw [List.replicate_succ]
    simp only [renPass, twoSum_zero p ha, ne_eq, not_true_eq_false, and_false, ite_false]
    exact ih b acc ha

theorem renPass_len (k : ℕ) : ∀ (pre : List ℝ) (b : ℕ) (acc : ℝ), F p acc → (∀ v ∈ pre, F p v) →
    (renPass p b acc (pre ++ List.replicate k 0)).length ≤ pre.length + 1 := by
  intro pre
  induction pre with
  | nil => intro b acc ha _; simp [renPass_zeros p k b acc ha]
  | cons v pre ih =>
    intro b acc ha hv
    have hpre : ∀ w ∈ pre, F p w := fun w hw => hv w (List.mem_cons_of_mem _ hw)
    simp only [List.cons_append, renPass]
    split_ifs
    · simp only [List.length_cons]
      have := ih (b - 1) (twoSum p acc v).2 (F_twoSum_snd p _ _) hpre
      omega
    · have := ih b (twoSum p acc v).1 (F_twoSum_fst p _ _) hpre
      simp only [List.length_cons]
      omega

/-- `Ren_n` of levels zero above `j < n` has its parts zero above `j` -/
theorem ren_zero_above (n : ℕ) (c : ℕ → ℝ) (hc : ∀ i ≤ n, F p (c i)) (j : ℕ) (hj : j < n)
    (hz : ∀ i, j < i → i ≤ n → c i = 0) : ∀ i, j < i → (ren p n n c).getD i 0 = 0 := by
  have hv := vecSum_zero_above p n c j hc hz
  have hvF := vecSum_F p n c hc
  have hlist : (List.range n).map (fun i => vecSum p n c (i + 1)) =
      (List.range j).map (fun i => vecSum p n c (i + 1)) ++ List.replicate (n - j) 0 := by
    obtain ⟨d, hd⟩ : ∃ d, n = j + d := ⟨n - j, by omega⟩
    have hr : List.range n = List.range j ++ (List.range d).map (j + ·) := by rw [hd, List.range_add]
    rw [hr, List.map_append, List.map_map, show n - j = d by omega]
    congr 1
    rw [List.map_congr_left (g := fun _ => (0 : ℝ)) fun i _ => by
      simp only [Function.comp_apply]; exact hv _ (by omega)]
    rw [List.map_const', List.length_range]
  have hlen : (ren p n n c).length ≤ j + 1 := by
    unfold ren
    rw [hlist]
    refine (renPass_len p (n - j) _ _ _ (hvF 0) fun w hw => ?_).trans (by simp)
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hw
    exact hvF _
  intro i hi
  exact getD_of_le _ (by omega)

variable (n : ℕ)

/-- the carries of ADDF are in `F` -/
theorem addfE_F (a : ℕ → ℝ) (b : ℝ) (hb : F p b) : ∀ m, F p (addfE p a b m)
  | 0 => hb
  | _ + 1 => F_twoSum_snd p _ _

theorem addfLevels_F (a : ℕ → ℝ) (b : ℝ) (hb : F p b) : ∀ m, F p (addfLevels p n a b m) := by
  intro m
  unfold addfLevels
  split_ifs
  · exact F_twoSum_fst p _ _
  · exact addfE_F p a b hb n
  · exact F_zero p

/-- ADDF of `r`, zero from index `l < n` on, has levels zero above `l` -/
theorem addfLevels_zero_above (hp : 1 < p) (r : ℕ → ℝ) (b : ℝ) (hb : F p b) (l : ℕ) (hl : l < n)
    (hz : ∀ i, l ≤ i → i < n → r i = 0) : ∀ i, l < i → addfLevels p n r b i = 0 := by
  have he : ∀ i, l < i → i ≤ n → addfE p r b i = 0 := by
    intro i
    induction i with
    | zero => intro h; omega
    | succ i ih =>
      intro h1 h2
      simp only [addfE]
      rw [hz i (by omega) (by omega)]
      rcases Nat.lt_or_ge l i with hli | hli
      · rw [ih hli (by omega), twoSum_zero p (F_zero p)]
      · obtain rfl : i = l := by omega
        rw [twoSum_zero_left p hp (addfE_F p r b hb _)]
  intro i hi
  unfold addfLevels
  split_ifs with h1 h2
  · rw [hz i (by omega) h1, he i hi (by omega), twoSum_zero p (F_zero p)]
  · exact he n (by omega) le_rfl
  · rfl

/-- FINISH: `r^{(0)} = (s_0, 0, …, 0)` and `r^{(l)} = ADDF(r^{(l-1)}, s_l)` -/
noncomputable def finishR (s : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun i => if i = 0 then s 0 else 0
  | l + 1 => pt (addfOp p n (finishR s l) (s (l + 1)))

omit [Prec_gt_0 p] in
/-- the part bounds along FINISH: `(S_0, 0, …, 0)`, then `G_ADDF`'s with `λ_0` the first plus `S_l` and
`Z̄ = ∑_{m ≤ l} S_m` -/
noncomputable def finishP (S : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun i => if i = 0 then S 0 else 0
  | l + 1 => GaddfP p n (finishP S l) (S (l + 1)) (∑ m ∈ range (l + 2), S m)

/-- FINISH up to `r^{(n-1)}` is exact: `r^{(l)}` is in `F`, zero above `l`, sums to `∑_{m ≤ l} s_m`, and has parts
within `finishP` -/
theorem finish_exact (hp : 1 < p) (hn : 1 ≤ n) (s : ℕ → ℝ) (hs : ∀ m ≤ n, F p (s m)) (S : ℕ → ℝ)
    (hS : ∀ m ≤ n, |s m| ≤ S m) : ∀ l, l ≤ n - 1 →
      (∀ i < n, F p (finishR p n s l i)) ∧ (∀ i, l < i → finishR p n s l i = 0) ∧
        ∑ i ∈ range n, finishR p n s l i = ∑ m ∈ range (l + 1), s m ∧ ∀ i, |finishR p n s l i| ≤ finishP p n S l i := by
  intro l
  induction l with
  | zero =>
    intro _
    refine ⟨fun i _ => ?_, fun i hi => ?_, ?_, fun i => ?_⟩
    · simp only [finishR]; split_ifs
      · exact hs 0 (by omega)
      · exact F_zero p
    · simp [finishR, show i ≠ 0 by omega]
    · simp [finishR, show 0 < n by omega]
    · simp only [finishR, finishP]; split_ifs
      · exact hS 0 (by omega)
      · simp
  | succ l ih =>
    intro hl
    obtain ⟨i1, i2, i3, i4⟩ := ih (by omega)
    obtain ⟨r, hr⟩ : ∃ r, r = finishR p n s l := ⟨_, rfl⟩
    rw [← hr] at i1 i2 i3 i4
    have hsl : F p (s (l + 1)) := hs (l + 1) (by omega)
    have hZ : |∑ i ∈ range n, r i + s (l + 1)| ≤ ∑ m ∈ range (l + 2), S m := by
      rw [i3, ← sum_range_succ]
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => hS m (by rw [mem_range] at hm; omega))
    obtain ⟨g1, g2, g3, g4⟩ := addf_G p n hp hn r (s (l + 1)) (finishP p n S l) (S (l + 1)) i1 hsl
      (fun i _ => i4 i) (hS (l + 1) (by omega)) _ hZ
    -- the ADDF is exact: its last level is zero
    have hzr : ∀ i, l + 1 ≤ i → i < n → r i = 0 := fun i h1 _ => i2 i (by omega)
    have hlz := addfLevels_zero_above p n hp r (s (l + 1)) hsl (l + 1) (by omega) hzr
    have hcF := addfLevels_F p n r (s (l + 1)) hsl
    have hex := ren_exact_of_last p n hp hn (addfLevels p n r (s (l + 1))) (fun i _ => hcF i) (hlz n (by omega))
    obtain ⟨-, -, -, -, hlev⟩ := lemma13_addf p hp hn r (s (l + 1)) i1 hsl (fun i => |r i|) (fun _ _ => le_rfl) _
      le_rfl _ le_rfl
    have hval : finishR p n s (l + 1) = pt (addfOp p n r (s (l + 1))) := by rw [hr]; rfl
    rw [hval]
    refine ⟨fun i _ => g3 i, fun i hi => ?_, ?_, fun i => g2 i⟩
    · exact ren_zero_above p n _ (fun i _ => hcF i) (l + 1) (by omega)
        (fun i h1 _ => hlz i h1) i hi
    · show ∑ i ∈ range n, (addfOp p n r (s (l + 1))).getD i 0 = _
      rw [← list_sum_getD _ n g4]
      show (ren p n n (addfLevels p n r (s (l + 1)))).sum = _
      rw [hex, hlev, i3, sum_range_succ _ (l + 1)]

/-- a dep keeps the levels in `F` -/
theorem depRun_F : ∀ (k m : ℕ) (e : ℝ) (st : LState), (∀ j, F p (st.s j)) → ∀ j, F p ((depRun p n k m e st).2.s j) := by
  intro k
  induction k with
  | zero =>
    intro m e st hF j
    show F p (Function.update st.s n (RN p (st.s n + e)) j)
    rw [Function.update_apply]
    split_ifs
    · exact F_RN p _
    · exact hF j
  | succ k ih =>
    intro m e st hF
    refine ih (m + 1) _ (twoAt p m e st) fun j => ?_
    show F p (Function.update st.s m (twoSum p (st.s m) e).1 j)
    rw [Function.update_apply]
    split_ifs
    · exact F_twoSum_fst p _ _
    · exact hF j

/-- a run of deps and roundings keeps the levels in `F` -/
theorem runOps_F_noassign (ops : List LOp) (h : ∀ o ∈ ops, ∀ m y, o ≠ LOp.assign m y) :
    ∀ st : LState, (∀ j, F p (st.s j)) → ∀ j, F p ((runOps p n ops st).2.s j) := by
  induction ops with
  | nil => intro st hF; exact hF
  | cons o os ih =>
    intro st hF
    have hos : ∀ o' ∈ os, ∀ m y, o' ≠ LOp.assign m y := fun o' ho' => h o' (List.mem_cons_of_mem _ ho')
    refine ih hos _ ?_
    cases o with
    | assign m y => exact absurd rfl (h _ List.mem_cons_self m y)
    | dep l t => exact depRun_F p n _ _ _ _ hF
    | round y =>
      intro j
      show F p (Function.update st.s n (RN p (st.s n + y)) j)
      rw [Function.update_apply]
      split_ifs
      · exact F_RN p _
      · exact hF j

omit [Prec_gt_0 p] in
theorem accOps_noassign (t : ℕ → ℕ → ℝ) (top : ℕ → Bool) (K : ℕ) :
    ∀ o ∈ accOps n t top K, ∀ m y, o ≠ LOp.assign m y := by
  intro o ho m y heq
  subst heq
  simp only [accOps, depositOps, List.mem_flatMap, List.mem_append, List.mem_map] at ho
  obtain ⟨j, -, h⟩ := ho
  rcases h with ⟨l, -, hl⟩ | h
  · exact LOp.noConfusion hl
  · split_ifs at h <;> simp at h

omit [Prec_gt_0 p] in
/-- the last state of a run is the first or one it passed through -/
theorem runOps_last_mem' (ops : List LOp) (st : LState) : (runOps p n ops st).2 ∈ st :: (runOps p n ops st).1 := by
  by_cases h : ops = []
  · subst h; simp [runOps]
  · exact List.mem_cons_of_mem _ (runOps_last_mem p n ops h st)

/-- the `k`-th deposit: MUL's levels for ADDPROD, the parts of `a` for ADDX -/
noncomputable def accT (prod : ℕ → Bool) (a b : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun k => if prod k then (runOps p n (mulOps p n (a k) (b k)) LState.init).2.s else a k

omit [Prec_gt_0 p] in
/-- `μ_k = |a_0 b_0|` or `|a_0|` -/
noncomputable def accMu (prod : ℕ → Bool) (a b : ℕ → ℕ → ℝ) : ℕ → ℝ :=
  fun k => if prod k then |a k 0 * b k 0| else |a k 0|

omit [Prec_gt_0 p] in
/-- `τ_l = max(L_l u^l, ρ^l)` with MUL's `L_l` -/
noncomputable def accTau (θ : ℝ) : ℕ → ℝ := fun l => max (mulL p n θ l * u p ^ l) ((θ * u p) ^ l)

omit [Prec_gt_0 p] in
/-- `Z`, the exact sum of the terms -/
noncomputable def accZ (prod : ℕ → Bool) (a b : ℕ → ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 K, if prod k then (∑ i ∈ range n, a k i) * ∑ j ∈ range n, b k j else ∑ i ∈ range n, a k i

/-- the levels after the `K` terms -/
noncomputable def accLev (prod : ℕ → Bool) (a b : ℕ → ℕ → ℝ) (K : ℕ) : ℕ → ℝ :=
  (runOps p n (accOps n (accT p n prod a b) prod K) LState.init).2.s

omit [Prec_gt_0 p] in
/-- `S_m(K)` of the accumulator's lemma for these terms -/
noncomputable def accSK (θ : ℝ) (prod : ℕ → Bool) (a b : ℕ → ℕ → ℝ) (K : ℕ) (m : ℕ) : ℝ :=
  accSclosed (accTau p n θ) (∑ j ∈ Icc 1 K, accMu prod a b j) (1 / (1 - ((n : ℝ) + 1) * K * u p)) (u p) m K

/-- Theorem 27 (`thm:acc`): `K` terms, each ADDPROD or ADDX of operands on `H(θ)`, then FINISH, give
`|Z - x| ≤ u^n|Z| + (1 + u^n)(Ē_lev + E_prod) + Φ` -/
theorem thm27 (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (θ : ℝ) (hθ : 0 < θ) (K : ℕ)
    (hK1 : 1 ≤ K) (hK : ((n : ℝ) + 1) * K * u p < 1) (prod : ℕ → Bool) (a b : ℕ → ℕ → ℝ)
    (ha : ∀ k ∈ Icc 1 K, ∀ i < n, F p (a k i)) (hb : ∀ k ∈ Icc 1 K, prod k = true → ∀ j < n, F p (b k j))
    (hHa : ∀ k ∈ Icc 1 K, Htheta p n θ (a k)) (hHb : ∀ k ∈ Icc 1 K, prod k = true → Htheta p n θ (b k)) :
    |accZ n prod a b K - ∑ i ∈ range n, finishR p n (accLev p n prod a b K) n i| ≤
      u p ^ n * |accZ n prod a b K| +
        (1 + u p ^ n) * (accE (accTau p n θ) (∑ j ∈ Icc 1 K, accMu prod a b j)
            (1 / (1 - ((n : ℝ) + 1) * K * u p)) (u p) n K +
          (((n ^ 2 + n - 1 : ℕ) : ℝ) * mulL p n θ n + thmDelta p n θ) * u p ^ (n + 1) *
            ∑ j ∈ Icc 1 K, accMu prod a b j) +
        GaddfE p n (finishP p n (accSK p n θ prod a b K) (n - 1)) (accSK p n θ prod a b K n) 0 := by
  have hu := u_pos p
  obtain ⟨τ, hτd⟩ : ∃ τ, τ = accTau p n θ := ⟨_, rfl⟩
  obtain ⟨μ, hμd⟩ : ∃ μ, μ = accMu prod a b := ⟨_, rfl⟩
  obtain ⟨t, htd⟩ : ∃ t, t = accT p n prod a b := ⟨_, rfl⟩
  have hτ0 : ∀ l, 0 ≤ τ l := fun l => by rw [hτd]; exact le_max_of_le_right (by positivity)
  have hμ0 : ∀ k, 0 ≤ μ k := fun k => by rw [hμd]; unfold accMu; split_ifs <;> positivity
  have hL0 := mulL_nonneg p n hn hA3 θ hθ
  -- each deposit within `τ_l μ_k`
  have hprod : ∀ k ∈ Icc 1 K, prod k = true →
      (∀ m ≤ n, |t k m| ≤ mulL p n θ m * u p ^ m * μ k) ∧ (∀ m, F p (t k m)) ∧
      |(∑ i ∈ range n, a k i) * (∑ j ∈ range n, b k j) - ∑ m ∈ range (n + 1), t k m| ≤
        (((n ^ 2 + n - 1 : ℕ) : ℝ) * mulL p n θ n + thmDelta p n θ) * u p ^ (n + 1) * μ k := by
    intro k hk hpk
    obtain ⟨t1, t2, -, -⟩ := thm14_mul p n hp hn hA3 θ hθ (a k) (b k) (ha k hk) (hb k hk hpk) (hHa k hk) (hHb k hk hpk)
    obtain ⟨-, -, -, -, c5⟩ := mulOps_levels p n hp hn (a k) (b k) _ _ (ha k hk) (hb k hk hpk)
      (Htheta_le p n (hHa k hk)) (Htheta_le p n (hHb k hk hpk)) hA3
    have ht : t k = (runOps p n (mulOps p n (a k) (b k)) LState.init).2.s := by rw [htd]; simp [accT, hpk]
    have hm : μ k = |a k 0 * b k 0| := by rw [hμd]; simp [accMu, hpk]
    rw [ht, hm]
    exact ⟨t1 _ (runOps_last_mem' p n _ _), c5, t2⟩
  have hx : ∀ k ∈ Icc 1 K, prod k = false → t k = a k ∧ μ k = |a k 0| := fun k _ hpk => by
    rw [htd, hμd]; simp [accT, accMu, hpk]
  have ht : ∀ k ∈ Icc 1 K, ∀ l < n, F p (t k l) ∧ |t k l| ≤ τ l * μ k := by
    intro k hk l hl
    cases hpk : prod k with
    | true =>
      obtain ⟨h1, h2, -⟩ := hprod k hk hpk
      refine ⟨h2 l, (h1 l hl.le).trans (mul_le_mul_of_nonneg_right ?_ (hμ0 k))⟩
      rw [hτd]; exact le_max_left _ _
    | false =>
      obtain ⟨h1, h2⟩ := hx k hk hpk
      rw [h1, h2]
      refine ⟨ha k hk l hl, (Htheta_le p n (hHa k hk) l hl).trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))⟩
      rw [hτd]; exact le_max_right _ _
  have htop : ∀ k ∈ Icc 1 K, prod k = true → |t k n| ≤ τ n * μ k := fun k hk hpk =>
    ((hprod k hk hpk).1 n le_rfl).trans (mul_le_mul_of_nonneg_right (by rw [hτd]; exact le_max_left _ _) (hμ0 k))
  obtain ⟨A1, A2, A3⟩ := lemma_acc p n hp t prod K τ μ hτ0 hμ0 ht htop hK
  -- the levels, their bounds `S_m(K)` and their sum
  obtain ⟨s, hsd⟩ : ∃ s, s = accLev p n prod a b K := ⟨_, rfl⟩
  have hsrun : s = (runOps p n (accOps n t prod K) LState.init).2.s := by rw [hsd, htd]; rfl
  obtain ⟨S, hSd⟩ : ∃ S, S = accSK p n θ prod a b K := ⟨_, rfl⟩
  have hS : ∀ m ≤ n, |s m| ≤ S m := fun m hm => by
    have := A1 K (mem_Icc.mpr ⟨hK1, le_rfl⟩) _ (runOps_last_mem' p n _ _) m hm
    rw [hsrun, hSd]
    unfold accSK
    rw [← hτd, ← hμd]
    exact this
  have hsF : ∀ m ≤ n, F p (s m) := fun m _ => by
    rw [hsrun]
    exact runOps_F_noassign p n _ (accOps_noassign n t prod K) _ (fun j => F_zero p) m
  obtain ⟨W, hWd⟩ : ∃ W, W = ∑ j ∈ Icc 1 K, μ j := ⟨_, rfl⟩
  obtain ⟨C, hCd⟩ : ∃ C, C = (((n ^ 2 + n - 1 : ℕ) : ℝ) * mulL p n θ n + thmDelta p n θ) * u p ^ (n + 1) := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hCd]
    exact mul_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (hL0 n)) (thmDelta_nonneg p n θ hθ.le))
      (by positivity)
  -- `|Z - S| ≤ Ē + E_prod`
  obtain ⟨E, hEd⟩ : ∃ E, E = accE τ W (1 / (1 - ((n : ℝ) + 1) * K * u p)) (u p) n K := ⟨_, rfl⟩
  have hZS : |accZ n prod a b K - ∑ m ∈ range (n + 1), s m| ≤ E + C * W := by
    rw [hsrun, A2, accZ, hEd, hWd]
    have hterm : ∀ k ∈ Icc 1 K, |(if prod k then (∑ i ∈ range n, a k i) * ∑ j ∈ range n, b k j
        else ∑ i ∈ range n, a k i) - (∑ l ∈ range n, t k l + if prod k then t k n else 0)| ≤ C * μ k := by
      intro k hk
      cases hpk : prod k with
      | true =>
        simp only [ite_true]
        rw [← sum_range_succ, hCd]
        exact (hprod k hk hpk).2.2
      | false =>
        simp only [Bool.false_eq_true, ite_false, add_zero]
        rw [(hx k hk hpk).1, sub_self, abs_zero]
        exact mul_nonneg hC0 (hμ0 k)
    rw [show ∀ (X Y : ℕ → ℝ) (r : ℝ), ∑ k ∈ Icc 1 K, X k - (∑ k ∈ Icc 1 K, Y k - r) =
      ∑ k ∈ Icc 1 K, (X k - Y k) + r from fun X Y r => by rw [sum_sub_distrib]; ring]
    refine (abs_add_le _ _).trans ?_
    rw [mul_sum, add_comm]
    exact add_le_add A3 ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm))
  -- FINISH
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
  rw [← hsd, hxs, ← hSd, ← hτd, ← hμd, ← hWd, ← hEd]
  -- assemble
  have hSZ : |SS| ≤ |accZ n prod a b K| + (E + C * W) := by
    have := abs_sub_abs_le_abs_sub SS (accZ n prod a b K)
    rw [abs_sub_comm] at hZS
    linarith
  have h2 := mul_le_mul_of_nonneg_left hSZ (pow_nonneg hu.le n)
  rw [← hCd]
  calc |accZ n prod a b K - (addfOp p n r (s n)).sum|
      ≤ |accZ n prod a b K - SS| + |SS - (addfOp p n r (s n)).sum| := abs_sub_le _ _ _
    _ ≤ (E + C * W) + (u p ^ n * |SS| + GaddfE p n (finishP p n S (n - 1)) (S n) 0) := add_le_add hZS g1
    _ ≤ _ := by nlinarith

end ExpansionBounds
