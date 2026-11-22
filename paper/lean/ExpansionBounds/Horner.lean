import ExpansionBounds.MulOps

/-!
# Lemma `lem:horner`: Horner's rule on expansions

`p_d = F_d` and `p_k = ADD(F_k, MUL(z, p_{k+1}))` for `k = d - 1, …, k_0`, with the bounds of Lemma 13 applied in
turn: `G_MUL` and `G_ADD` give an operation's error and its result's part bounds from its operands' part bounds and
a bound `Z̄` on its exact result. The product may be any operation within `G_MUL`'s bounds up to a loss `η` per part,
as one formed on operands scaled exactly by powers of two and scaled back; MUL is the case `η = 0`.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) (n : ℕ)

theorem list_sum_getD (l : List ℝ) : ∀ N, l.length ≤ N → l.sum = ∑ i ∈ range N, l.getD i 0 := by
  induction l with
  | nil => intro N _; simp
  | cons a l ih =>
    intro N hN
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp at hN; omega⟩
    rw [sum_range_succ', List.sum_cons, ih N' (by simp at hN; omega)]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

theorem renPass_length (vs : List ℝ) : ∀ (b : ℕ) (acc : ℝ), (renPass p b acc vs).length ≤ b + 1 := by
  induction vs with
  | nil => intro b acc; simp [renPass]
  | cons v vs ih =>
    intro b acc
    simp only [renPass]
    split_ifs with hc
    · simp only [List.length_cons]
      have := ih (b - 1) (twoSum p acc v).2
      omega
    · exact ih b _

/-- the parts of a list, beyond its length zero -/
theorem getD_mem_or_zero (l : List ℝ) (i : ℕ) : l.getD i 0 ∈ l ∨ l.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : l[i]? with _ | x
  · right
    rfl
  · left
    exact List.mem_of_getElem? h

/-- a list's parts beyond its length are zero -/
theorem getD_of_le (l : List ℝ) {i : ℕ} (h : l.length ≤ i) : l.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

variable [Prec_gt_0 p]

theorem renPass_F (vs : List ℝ) : ∀ (b : ℕ) (acc : ℝ), F p acc → (∀ v ∈ vs, F p v) →
    ∀ x ∈ renPass p b acc vs, F p x := by
  induction vs with
  | nil => intro b acc hacc _ x hx; simp [renPass] at hx; rw [hx]; exact hacc
  | cons v vs ih =>
    intro b acc hacc hvs x hx
    have hvs' : ∀ w ∈ vs, F p w := fun w hw => hvs w (by simp [hw])
    simp only [renPass] at hx
    split_ifs at hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact F_twoSum_fst p _ _
      · exact ih _ _ (F_twoSum_snd p _ _) hvs' x hx
    · exact ih _ _ (F_twoSum_fst p _ _) hvs' x hx

/-- `Ren_n`'s result has at most `n` parts, each in `F p`, and its parts' sum is its value -/
theorem ren_spec (hn : 1 ≤ n) (c : ℕ → ℝ) (hc : ∀ i ≤ n, F p (c i)) :
    (ren p n n c).length ≤ n ∧ (∀ i, F p ((ren p n n c).getD i 0)) ∧
      (ren p n n c).sum = ∑ i ∈ range n, (ren p n n c).getD i 0 := by
  have hv := vecSum_F p n c hc
  have hlen : (ren p n n c).length ≤ n := by
    have := renPass_length p ((List.range n).map fun j => vecSum p n c (j + 1)) (n - 1) (vecSum p n c 0)
    unfold ren
    omega
  refine ⟨hlen, fun i => ?_, list_sum_getD _ n hlen⟩
  rcases getD_mem_or_zero (ren p n n c) i with h | h
  · exact renPass_F p _ _ _ (hv 0) (by simp; exact fun j _ => hv _) _ h
  · rw [h]
    exact F_zero p

omit [Prec_gt_0 p] in
/-- the part bounds of Lemma 13 (b) for level bounds `X`, `Z̄` and the levels' error `F` (the paper's `R + Δ`):
`π'_0 = (1 + u)(Z̄ + F + W_1)`, `π'_i = (1 + u)(uπ'_{i-1} + W_i)` for `1 ≤ i < n`, and zero beyond -/
noncomputable def gParts (X : ℕ → ℝ) (Zb Fb : ℝ) : ℕ → ℝ
  | 0 => (1 + u p) * (Zb + Fb + ∑ j ∈ Ioc 1 n, Vb p n X j)
  | i + 1 => if i + 1 < n then (1 + u p) * (u p * gParts X Zb Fb i + ∑ j ∈ Ioc (i + 1) n, Vb p n X j) else 0

omit [Prec_gt_0 p] in
/-- the error bound of Lemma 13 (a): `uⁿ Z̄ + (1 + uⁿ) F + ∑_{j=1}^n (uⁿ + u^{n+1-j}) V_j` -/
noncomputable def gErr (X : ℕ → ℝ) (Zb Fb : ℝ) : ℝ :=
  u p ^ n * Zb + (1 + u p ^ n) * Fb + ∑ j ∈ Ioc 0 n, (u p ^ n + u p ^ (n + 1 - j)) * Vb p n X j

omit [Prec_gt_0 p] in
/-- `G_MUL(α, β; Z̄)`'s error bound -/
noncomputable def GmulE (α β : ℕ → ℝ) (Zb : ℝ) : ℝ := gErr p n (mulX p n α β) Zb (mulR p n α β + mulDelta n α β)

omit [Prec_gt_0 p] in
/-- `G_MUL(α, β; Z̄)`'s part bounds -/
noncomputable def GmulP (α β : ℕ → ℝ) (Zb : ℝ) : ℕ → ℝ :=
  gParts p n (mulX p n α β) Zb (mulR p n α β + mulDelta n α β)

omit [Prec_gt_0 p] in
/-- `G_ADD(α, β; Z̄)`'s error bound, with `λ_m = α_m + β_m` -/
noncomputable def GaddE (α β : ℕ → ℝ) (Zb : ℝ) : ℝ :=
  gErr p n (pairX p n fun m => α m + β m) Zb (pairR p n fun m => α m + β m)

omit [Prec_gt_0 p] in
/-- `G_ADD(α, β; Z̄)`'s part bounds, with `λ_m = α_m + β_m` -/
noncomputable def GaddP (α β : ℕ → ℝ) (Zb : ℝ) : ℕ → ℝ :=
  gParts p n (pairX p n fun m => α m + β m) Zb (pairR p n fun m => α m + β m)

omit [Prec_gt_0 p] in
/-- Lemma 13 (b)'s part bounds, from the result's first part and each part after it -/
theorem gParts_le (X : ℕ → ℝ) (Zb Fb : ℝ) (x : List ℝ) (hlen : x.length ≤ n)
    (h0 : |x.getD 0 0| ≤ (1 + u p) * (Zb + Fb + ∑ j ∈ Ioc 1 n, Vb p n X j))
    (hi : ∀ i, 1 ≤ i → i ≤ n - 1 → |x.getD i 0| ≤ (1 + u p) * (u p * |x.getD (i - 1) 0| + ∑ j ∈ Ioc i n, Vb p n X j)) :
    ∀ i, |x.getD i 0| ≤ gParts p n X Zb Fb i := by
  have hu := u_pos p
  intro i
  induction i with
  | zero => exact h0
  | succ i ih =>
    simp only [gParts]
    split_ifs with hlt
    · refine (hi (i + 1) (by omega) (by omega)).trans ?_
      rw [Nat.add_sub_cancel]
      exact mul_le_mul_of_nonneg_left (add_le_add_left (mul_le_mul_of_nonneg_left ih hu.le) _) (by linarith)
    · rw [getD_of_le x (by omega), abs_zero]

/-- `G_MUL` bounds MUL: for operands with part bounds `α` and `β` and `|ab| ≤ Z̄` -/
theorem mul_G (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (a b α β : ℕ → ℝ)
    (ha : ∀ i < n, F p (a i)) (hb : ∀ j < n, F p (b j)) (hα : ∀ i < n, |a i| ≤ α i) (hβ : ∀ j < n, |b j| ≤ β j)
    (Zb : ℝ) (hZ : |(∑ i ∈ range n, a i) * ∑ j ∈ range n, b j| ≤ Zb) :
    |(∑ i ∈ range n, a i) * (∑ j ∈ range n, b j) - (mulOp p n a b).sum| ≤ GmulE p n α β Zb ∧
      (∀ i, |(mulOp p n a b).getD i 0| ≤ GmulP p n α β Zb i) ∧ (∀ i, F p ((mulOp p n a b).getD i 0)) ∧
      (mulOp p n a b).length ≤ n := by
  rw [sum_mul_sum] at hZ ⊢
  obtain ⟨r1, r2, r3, -, -, -, -⟩ := lemma13_mul p n hp hn a b α β ha hb hα hβ hA3 Zb hZ
  obtain ⟨-, -, -, -, c5⟩ := mulOps_levels p n hp hn a b α β ha hb hα hβ hA3
  obtain ⟨l1, l2, -⟩ := ren_spec p n hn _ (fun i _ => c5 i)
  exact ⟨r1, gParts_le p n _ _ _ _ l1 r2 r3, l2, l1⟩

/-- `G_ADD` bounds ADD: for operands with part bounds `α` and `β` and `|a + b| ≤ Z̄` -/
theorem add_G (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (a b α β : ℕ → ℝ)
    (ha : ∀ i < n, F p (a i)) (hb : ∀ j < n, F p (b j)) (hα : ∀ i < n, |a i| ≤ α i) (hβ : ∀ j < n, |b j| ≤ β j)
    (Zb : ℝ) (hZ : |∑ i ∈ range n, a i + ∑ i ∈ range n, b i| ≤ Zb) :
    |(∑ i ∈ range n, a i + ∑ i ∈ range n, b i) - (addOp p n a b).sum| ≤ GaddE p n α β Zb ∧
      (∀ i, |(addOp p n a b).getD i 0| ≤ GaddP p n α β Zb i) ∧ (∀ i, F p ((addOp p n a b).getD i 0)) ∧
      (addOp p n a b).length ≤ n := by
  rw [← sum_add_distrib] at hZ ⊢
  have hlam : ∀ m < n, |a m + b m| ≤ α m + β m := fun m hm => (abs_add_le _ _).trans (add_le_add (hα m hm) (hβ m hm))
  obtain ⟨r1, r2, r3, -, -, -, -⟩ := lemma13_add p n hp hn a b ha hb _ hlam hA3 Zb hZ
  have hF : ∀ m, F p (addLevels p n a b m) := by
    have hfa : ∀ i < n, _ := fun i hi => facts_a p hp (ha i hi) (hb i hi)
    exact (pairOps_levels p n hp hn _ _ (fun i _ => ⟨F_twoSum_fst p _ _, F_twoSum_snd p _ _⟩)
      (fun i hi => (abs_RN_le p _).trans (mul_le_mul_of_nonneg_left (hlam i hi) (by linarith [u_pos p])))
      (fun i hi => ((hfa i hi).2.1.trans (min_le_right _ _)).trans
        ((mul_le_mul_of_nonneg_right (us_le_u p) (abs_nonneg _)).trans
          (mul_le_mul_of_nonneg_left (hlam i hi) (u_pos p).le))) hA3).2.2.2.2
  obtain ⟨l1, l2, -⟩ := ren_spec p n hn _ (fun i _ => hF i)
  exact ⟨r1, gParts_le p n _ _ _ _ l1 r2 r3, l2, l1⟩

omit [Prec_gt_0 p] in
/-- a product operation `M` within `G_MUL`'s bounds up to `nη` on the error and `η` per part -/
def MulWithin (M : (ℕ → ℝ) → (ℕ → ℝ) → List ℝ) (η : ℝ) : Prop :=
  ∀ (a b α β : ℕ → ℝ) (Zb : ℝ), (∀ i < n, F p (a i)) → (∀ j < n, F p (b j)) → (∀ i < n, |a i| ≤ α i) →
    (∀ j < n, |b j| ≤ β j) → |(∑ i ∈ range n, a i) * ∑ j ∈ range n, b j| ≤ Zb →
    |(∑ i ∈ range n, a i) * (∑ j ∈ range n, b j) - (M a b).sum| ≤ GmulE p n α β Zb + n * η ∧
      (∀ i, |(M a b).getD i 0| ≤ GmulP p n α β Zb i + η) ∧ (∀ i, F p ((M a b).getD i 0)) ∧ (M a b).length ≤ n

/-- MUL is within `G_MUL`'s bounds -/
theorem mulOp_within (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) :
    MulWithin p n (mulOp p n) 0 := by
  intro a b α β Zb ha hb hα hβ hZ
  obtain ⟨r1, r2, r3, r4⟩ := mul_G p n hp hn hA3 a b α β ha hb hα hβ Zb hZ
  exact ⟨by simpa using r1, fun i => by simpa using r2 i, r3, r4⟩

omit [Prec_gt_0 p] in
theorem pairOps_congr (hn : 1 ≤ n) {g g' : ℕ → ℝ × ℝ} (h : ∀ i < n, g i = g' i) :
    pairOps n g = pairOps n g' := by
  unfold pairOps
  rw [List.map_congr_left fun i hi => by rw [h i (List.mem_range.mp hi)], h (n - 1) (by omega),
    List.map_congr_left (l := List.range (n - 1)) fun l hl => by
      rw [h l (by have := List.mem_range.mp hl; omega)]]

/-- ADD's operands commute: `TwoSum(a, b)` and `TwoSum(b, a)` return the same sum and, both being exact, the same
error -/
theorem addOp_comm (hp : 1 < p) (hn : 1 ≤ n) (a b : ℕ → ℝ) (ha : ∀ i < n, F p (a i)) (hb : ∀ i < n, F p (b i)) :
    addOp p n a b = addOp p n b a := by
  have h : ∀ i < n, twoSum p (a i) (b i) = twoSum p (b i) (a i) := by
    intro i hi
    have h1 := twoSum_add p hp (ha i hi) (hb i hi)
    have h2 := twoSum_add p hp (hb i hi) (ha i hi)
    have hs : (twoSum p (a i) (b i)).1 = (twoSum p (b i) (a i)).1 := by
      show RN p (a i + b i) = RN p (b i + a i)
      rw [add_comm]
    exact Prod.ext hs (by linarith)
  unfold addOp addLevels addOps
  rw [pairOps_congr n hn h]

omit [Prec_gt_0 p] in
/-- Horner's rule with the product `M`: `hornerP j` holds the parts of `p_{d-j}`, with `p_d = F_d` and
`p_k = ADD(F_k, M(z, p_{k+1}))` -/
noncomputable def hornerP (M : (ℕ → ℝ) → (ℕ → ℝ) → List ℝ) (z : ℕ → ℝ) (Fk : ℕ → ℕ → ℝ) (d : ℕ) : ℕ → ℕ → ℝ
  | 0 => Fk d
  | j + 1 => fun i =>
    (addOp p n (Fk (d - (j + 1))) fun i' => (M z (hornerP M z Fk d j)).getD i' 0).getD i 0

omit [Prec_gt_0 p] in
/-- the bounds `(e_{d-j}, π^{(d-j)})` of Lemma `lem:horner`: `e_d = φ_d` and `π^{(d)} = |F_d|`, then
`(ε^p_k, μ_k) = G_MUL(π^z, π^{(k+1)}; (1 + ε_z) z̄ (v_{k+1} + e_{k+1}))` with `nη` and `η` added,
`D_k = (1 + ε_z) z̄ e_{k+1} + ε_z z̄ v_{k+1} + φ_k + ε^p_k`, `(ε^a_k, π^{(k)}) = G_ADD(|F_k|, μ_k; v_k + D_k)`
and `e_k = D_k + ε^a_k` -/
noncomputable def hornerB (πz : ℕ → ℝ) (zb εz η : ℝ) (Fk : ℕ → ℕ → ℝ) (φ v : ℕ → ℝ) (d : ℕ) :
    ℕ → ℝ × (ℕ → ℝ)
  | 0 => (φ d, fun i => |Fk d i|)
  | j + 1 =>
    let k := d - (j + 1)
    let e1 := (hornerB πz zb εz η Fk φ v d j).1
    let π1 := (hornerB πz zb εz η Fk φ v d j).2
    let Zm := (1 + εz) * zb * (v (k + 1) + e1)
    let μ := fun i => GmulP p n πz π1 Zm i + η
    let D := (1 + εz) * zb * e1 + εz * zb * v (k + 1) + φ k + (GmulE p n πz π1 Zm + n * η)
    (D + GaddE p n (fun i => |Fk k i|) μ (v k + D), GaddP p n (fun i => |Fk k i|) μ (v k + D))

omit [Prec_gt_0 p] in
/-- the exact sums `p^e_k = ∑_{l=k}^d F^e_l z_e^{l-k}`, indexed by `l - k` -/
noncomputable def hornerE (Fe : ℕ → ℝ) (ze : ℝ) (d k : ℕ) : ℝ := ∑ l ∈ range (d + 1 - k), Fe (k + l) * ze ^ l

omit [Prec_gt_0 p] in
theorem hornerE_succ (Fe : ℕ → ℝ) (ze : ℝ) (d k : ℕ) (hk : k < d) :
    hornerE Fe ze d k = Fe k + ze * hornerE Fe ze d (k + 1) := by
  unfold hornerE
  rw [show d + 1 - k = d + 1 - (k + 1) + 1 by omega, sum_range_succ', mul_sum, add_comm]
  congr 1
  · simp
  · exact sum_congr rfl fun i _ => by rw [show k + (i + 1) = k + 1 + i by ring, pow_succ]; ring

/-- Lemma `lem:horner`, by steps: `|p_{d-j} - p^e_{d-j}| ≤ e_{d-j}`, and `p_{d-j}` has part bounds
`π^{(d-j)}` and its parts in `F p` -/
theorem horner_step (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1)
    {M : (ℕ → ℝ) → (ℕ → ℝ) → List ℝ} {η : ℝ} (hM : MulWithin p n M η)
    (z : ℕ → ℝ) (hz : ∀ i < n, F p (z i)) (πz : ℕ → ℝ) (hπz : ∀ i < n, |z i| ≤ πz i) (ze zb εz : ℝ)
    (hzb : |ze| ≤ zb) (hεz : 0 ≤ εz) (hze : |∑ i ∈ range n, z i - ze| ≤ εz * zb) (Fk : ℕ → ℕ → ℝ)
    (hF : ∀ k, ∀ i < n, F p (Fk k i)) (Fe φ v : ℕ → ℝ) (hφ : ∀ k, |∑ i ∈ range n, Fk k i - Fe k| ≤ φ k)
    (d k0 : ℕ) (hv : ∀ k, k0 ≤ k → k ≤ d → |hornerE Fe ze d k| ≤ v k) :
    ∀ j, j ≤ d - k0 →
      |∑ i ∈ range n, hornerP p n M z Fk d j i - hornerE Fe ze d (d - j)| ≤ (hornerB p n πz zb εz η Fk φ v d j).1 ∧
        (∀ i < n, |hornerP p n M z Fk d j i| ≤ (hornerB p n πz zb εz η Fk φ v d j).2 i) ∧
        ∀ i < n, F p (hornerP p n M z Fk d j i) := by
  have hzb0 : 0 ≤ zb := (abs_nonneg _).trans hzb
  have hzsum : |∑ i ∈ range n, z i| ≤ (1 + εz) * zb := by
    have := abs_sub_abs_le_abs_sub (∑ i ∈ range n, z i) ze
    nlinarith
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨?_, fun i _ => le_rfl, fun i hi => hF d i hi⟩
    simpa [hornerP, hornerB, hornerE] using hφ d
  | succ j ih =>
    intro hj
    obtain ⟨i1, i2, i3⟩ := ih (by omega)
    set k := d - (j + 1) with hk
    have hk1 : d - j = k + 1 := by omega
    rw [hk1] at i1
    set P := hornerP p n M z Fk d j
    set e1 := (hornerB p n πz zb εz η Fk φ v d j).1
    set π1 := (hornerB p n πz zb εz η Fk φ v d j).2
    have hvk1 := hv (k + 1) (by omega) (by omega)
    have he1 : 0 ≤ e1 := (abs_nonneg _).trans i1
    have hPsum : |∑ i ∈ range n, P i| ≤ v (k + 1) + e1 := by
      have := abs_sub_abs_le_abs_sub (∑ i ∈ range n, P i) (hornerE Fe ze d (k + 1))
      linarith
    set Zm := (1 + εz) * zb * (v (k + 1) + e1)
    have hZm : |(∑ i ∈ range n, z i) * ∑ i ∈ range n, P i| ≤ Zm := by
      rw [abs_mul]
      exact mul_le_mul hzsum hPsum (abs_nonneg _) (by positivity)
    obtain ⟨m1, m2, m3, m4⟩ := hM z P πz π1 Zm hz i3 hπz i2 hZm
    set mpart := fun i => (M z P).getD i 0
    have hmsum : (M z P).sum = ∑ i ∈ range n, mpart i := list_sum_getD _ n m4
    set D := (1 + εz) * zb * e1 + εz * zb * v (k + 1) + φ k + (GmulE p n πz π1 Zm + n * η)
    have hpe := hornerE_succ Fe ze d k (by omega)
    have hS : |(∑ i ∈ range n, Fk k i + ∑ i ∈ range n, mpart i) - hornerE Fe ze d k| ≤ D := by
      rw [hpe, ← hmsum]
      have hsplit : (∑ i ∈ range n, Fk k i + (M z P).sum) - (Fe k + ze * hornerE Fe ze d (k + 1)) =
          (∑ i ∈ range n, Fk k i - Fe k) + ((M z P).sum - (∑ i ∈ range n, z i) * ∑ i ∈ range n, P i) +
            (∑ i ∈ range n, z i) * (∑ i ∈ range n, P i - hornerE Fe ze d (k + 1)) +
            (∑ i ∈ range n, z i - ze) * hornerE Fe ze d (k + 1) := by ring
      rw [hsplit]
      have t1 := hφ k
      have t2 : |(M z P).sum - (∑ i ∈ range n, z i) * ∑ i ∈ range n, P i| ≤ GmulE p n πz π1 Zm + n * η := by
        rw [abs_sub_comm]
        exact m1
      have t3 : |(∑ i ∈ range n, z i) * (∑ i ∈ range n, P i - hornerE Fe ze d (k + 1))| ≤ (1 + εz) * zb * e1 := by
        rw [abs_mul]
        exact mul_le_mul hzsum i1 (abs_nonneg _) (by positivity)
      have t4 : |(∑ i ∈ range n, z i - ze) * hornerE Fe ze d (k + 1)| ≤ εz * zb * v (k + 1) := by
        rw [abs_mul]
        exact mul_le_mul hze hvk1 (abs_nonneg _) (by positivity)
      calc _ ≤ |∑ i ∈ range n, Fk k i - Fe k| + |(M z P).sum - (∑ i ∈ range n, z i) * ∑ i ∈ range n, P i| +
            |(∑ i ∈ range n, z i) * (∑ i ∈ range n, P i - hornerE Fe ze d (k + 1))| +
            |(∑ i ∈ range n, z i - ze) * hornerE Fe ze d (k + 1)| := by
            refine (abs_add_le _ _).trans (add_le_add_left ((abs_add_le _ _).trans
              (add_le_add_left (abs_add_le _ _) _)) _)
        _ ≤ D := by simp only [D]; linarith
    have hSb : |∑ i ∈ range n, Fk k i + ∑ i ∈ range n, mpart i| ≤ v k + D := by
      have := abs_sub_abs_le_abs_sub (∑ i ∈ range n, Fk k i + ∑ i ∈ range n, mpart i) (hornerE Fe ze d k)
      linarith [hv k (by omega) (by omega)]
    obtain ⟨a1, a2, a3, a4⟩ := add_G p n hp hn hA3 (Fk k) mpart (fun i => |Fk k i|)
      (fun i => GmulP p n πz π1 Zm i + η) (hF k) (fun i _ => m3 i) (fun i _ => le_rfl) (fun i _ => m2 i)
      (v k + D) hSb
    have hval : ∑ i ∈ range n, hornerP p n M z Fk d (j + 1) i =
        (addOp p n (Fk k) mpart).sum := (list_sum_getD _ n a4).symm
    refine ⟨?_, fun i _ => a2 i, fun i _ => a3 i⟩
    rw [hval]
    show _ ≤ D + GaddE p n (fun i => |Fk k i|) (fun i => GmulP p n πz π1 Zm i + η) (v k + D)
    have := abs_sub_le_add ((addOp p n (Fk k) mpart).sum - (∑ i ∈ range n, Fk k i + ∑ i ∈ range n, mpart i))
      (hornerE Fe ze d k - (∑ i ∈ range n, Fk k i + ∑ i ∈ range n, mpart i))
    rw [abs_sub_comm] at a1
    calc |(addOp p n (Fk k) mpart).sum - hornerE Fe ze d k|
        = |((addOp p n (Fk k) mpart).sum - (∑ i ∈ range n, Fk k i + ∑ i ∈ range n, mpart i)) +
            ((∑ i ∈ range n, Fk k i + ∑ i ∈ range n, mpart i) - hornerE Fe ze d k)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (by linarith)

/-- Lemma 33 (`lem:horner`). With `p_d = F_d` and `p_k = ADD(F_k, M(z, p_{k+1}))` for `k = d - 1, …, k_0`, where
`|z_e| ≤ z̄`, `|z - z_e| ≤ ε_z z̄`, `|F_k - F^e_k| ≤ φ_k` and `v_k ≥ |p^e_k|`: `|p_k - p^e_k| ≤ e_k`, and `p_k`
has part bounds `π^{(k)}`. The product `M` is within `G_MUL`'s bounds up to `nη` on the error and `η` per part,
which covers products formed on operands scaled exactly by powers of two and scaled back with a loss of at most
`η` per part; MUL is the case `η = 0` (`mulOp_within`). ADD's operands may come in either order (`addOp_comm`). -/
theorem lemma_horner (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1)
    {M : (ℕ → ℝ) → (ℕ → ℝ) → List ℝ} {η : ℝ} (hM : MulWithin p n M η)
    (z : ℕ → ℝ) (hz : ∀ i < n, F p (z i)) (πz : ℕ → ℝ) (hπz : ∀ i < n, |z i| ≤ πz i) (ze zb εz : ℝ)
    (hzb : |ze| ≤ zb) (hεz : 0 ≤ εz) (hze : |∑ i ∈ range n, z i - ze| ≤ εz * zb) (Fk : ℕ → ℕ → ℝ)
    (hF : ∀ k, ∀ i < n, F p (Fk k i)) (Fe φ v : ℕ → ℝ) (hφ : ∀ k, |∑ i ∈ range n, Fk k i - Fe k| ≤ φ k)
    (d k0 : ℕ) (hv : ∀ k, k0 ≤ k → k ≤ d → |hornerE Fe ze d k| ≤ v k) :
    ∀ k, k0 ≤ k → k ≤ d →
      |∑ i ∈ range n, hornerP p n M z Fk d (d - k) i - hornerE Fe ze d k| ≤
          (hornerB p n πz zb εz η Fk φ v d (d - k)).1 ∧
        ∀ i < n, |hornerP p n M z Fk d (d - k) i| ≤ (hornerB p n πz zb εz η Fk φ v d (d - k)).2 i := by
  intro k hk0 hkd
  obtain ⟨h1, h2, -⟩ := horner_step p n hp hn hA3 hM z hz πz hπz ze zb εz hzb hεz hze Fk hF Fe φ v hφ d k0 hv
    (d - k) (by omega)
  rw [show d - (d - k) = k by omega] at h1
  exact ⟨h1, h2⟩

end ExpansionBounds
