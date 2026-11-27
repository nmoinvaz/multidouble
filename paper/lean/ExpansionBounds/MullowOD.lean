import ExpansionBounds.Acc8
import ExpansionBounds.MullowCode

/-!
# `series::mullow` at octo-double: the read-out and an output index
-/

/-!
## `series::parts_of`: an integer as eight 53-bit parts

The integer `V = σN`, `σ = ±1`, `2^{h_b} ≤ N < 2^{h_b+1}`, times `2^e`, as parts `σ c_j 2^{b_j + e}`, where
`b_j = h_b - 52 - 53j` and `c_j`, bits `b_j..b_j + 52` of `N`, is `⌊N/2^{b_j}⌋ mod 2^{53}` (`chunk_mod`). The first
`n + 1` chunks are `N` truncated below bit `b_n` (`chunk_sum`), within `2^{b_n}` of it (`chT_trunc`); at `n = 7` the
eight parts are within `2^{-423}|V| 2^e` of `V 2^e` (`rd_sum`), each a float (`rd_F`) and at most `(2u)^j` times
the first (`rd_H`).
-/

namespace ExpansionBounds

open Finset

/-- the chunks' exponents `b_j = h_b - 52 - 53j` -/
def chB (hb j : ℕ) : ℤ := (hb : ℤ) - 52 - 53 * j

/-- `N` truncated below bit `b_j`, in units of `2^{b_j}` -/
noncomputable def chT (N hb j : ℕ) : ℤ := ⌊(N : ℝ) / 2 ^ chB hb j⌋

/-- chunk `j`: bits `b_j..b_j + 52` of `N` -/
noncomputable def chunk (N hb : ℕ) : ℕ → ℤ
  | 0 => chT N hb 0
  | j + 1 => chT N hb (j + 1) - 2 ^ 53 * chT N hb j

theorem chT_div (N hb j : ℕ) : (N : ℝ) / 2 ^ chB hb j = (N : ℝ) / 2 ^ chB hb (j + 1) / 2 ^ 53 := by
  rw [div_div, show chB hb j = chB hb (j + 1) + 53 by unfold chB; push_cast; ring, zpow_add₀ two_ne_zero]
  norm_num

/-- a chunk past the first is in `[0, 2^{53})`, and the remainder of `⌊N/2^{b_j}⌋` modulo `2^{53}` -/
theorem chunk_succ (N hb j : ℕ) : 0 ≤ chunk N hb (j + 1) ∧ chunk N hb (j + 1) < 2 ^ 53 := by
  set x : ℝ := (N : ℝ) / 2 ^ chB hb (j + 1)
  have hx : chT N hb j = ⌊x / 2 ^ 53⌋ := by rw [chT, chT_div]
  have h1 : ((2 ^ 53 * ⌊x / 2 ^ 53⌋ : ℤ) : ℝ) ≤ x := by
    push_cast
    have := Int.floor_le (x / 2 ^ 53)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have h2 : x < ((2 ^ 53 * ⌊x / 2 ^ 53⌋ + 2 ^ 53 : ℤ) : ℝ) := by
    push_cast
    have := Int.lt_floor_add_one (x / 2 ^ 53)
    rw [div_lt_iff₀ (by positivity)] at this
    linarith
  have h3 : 2 ^ 53 * ⌊x / 2 ^ 53⌋ ≤ ⌊x⌋ := Int.le_floor.mpr h1
  have h4 : ⌊x⌋ < 2 ^ 53 * ⌊x / 2 ^ 53⌋ + 2 ^ 53 := Int.floor_lt.mpr h2
  have hx' : chT N hb (j + 1) = ⌊x⌋ := rfl
  simp only [chunk]
  rw [hx, hx']
  omega

/-- the code's chunk: `⌊N/2^{b_j}⌋ mod 2^{53}` -/
theorem chunk_mod (N hb j : ℕ) : chunk N hb (j + 1) = chT N hb (j + 1) % 2 ^ 53 := by
  obtain ⟨h0, h1⟩ := chunk_succ N hb j
  have e : chT N hb (j + 1) = chunk N hb (j + 1) + 2 ^ 53 * chT N hb j := by simp only [chunk]; ring
  rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt h0 h1]

/-- the first chunk holds the top bit: `2^{52} ≤ c_0 < 2^{53}` -/
theorem chunk_zero {N hb : ℕ} (h1 : 2 ^ hb ≤ N) (h2 : N < 2 ^ (hb + 1)) :
    2 ^ 52 ≤ chunk N hb 0 ∧ chunk N hb 0 < 2 ^ 53 := by
  have hS : (0 : ℝ) < 2 ^ chB hb 0 := by positivity
  have e1 : (2 : ℝ) ^ hb = 2 ^ 52 * 2 ^ chB hb 0 := by
    rw [chB, ← zpow_natCast, ← zpow_natCast 2 52, ← zpow_add₀ two_ne_zero]; congr 1; push_cast; ring
  have hN1 : (2 : ℝ) ^ hb ≤ N := by exact_mod_cast h1
  have hN2 : (N : ℝ) < 2 ^ (hb + 1) := by exact_mod_cast h2
  rw [pow_succ, e1] at hN2
  rw [e1] at hN1
  simp only [chunk, chT]
  constructor
  · refine Int.le_floor.mpr ?_
    rw [le_div_iff₀ hS]; push_cast; linarith
  · refine Int.floor_lt.mpr ?_
    rw [div_lt_iff₀ hS]; push_cast; nlinarith

/-- the first `n + 1` chunks are `N` truncated below bit `b_n` -/
theorem chunk_sum (N hb n : ℕ) :
    ∑ j ∈ range (n + 1), (chunk N hb j : ℝ) * 2 ^ chB hb j = chT N hb n * 2 ^ chB hb n := by
  induction n with
  | zero => simp [chunk]
  | succ n ih =>
    rw [sum_range_succ, ih]
    simp only [chunk]
    push_cast
    rw [show chB hb n = chB hb (n + 1) + 53 by unfold chB; push_cast; ring, zpow_add₀ two_ne_zero]
    norm_num
    ring

/-- the truncation loses less than `2^{b_n}` -/
theorem chT_trunc (N hb n : ℕ) :
    0 ≤ (N : ℝ) - chT N hb n * 2 ^ chB hb n ∧ (N : ℝ) - chT N hb n * 2 ^ chB hb n < 2 ^ chB hb n := by
  have hS : (0 : ℝ) < 2 ^ chB hb n := by positivity
  have h1 := Int.floor_le ((N : ℝ) / 2 ^ chB hb n)
  have h2 := Int.lt_floor_add_one ((N : ℝ) / 2 ^ chB hb n)
  rw [le_div_iff₀ hS] at h1
  rw [div_lt_iff₀ hS] at h2
  unfold chT
  constructor <;> nlinarith

/-- the parts of `σN 2^e` -/
noncomputable def rdPart (sg : ℝ) (N hb : ℕ) (e : ℤ) (j : ℕ) : ℝ := sg * chunk N hb j * 2 ^ (chB hb j + e)

/-- the eight parts are within `2^{-423} N 2^e` of `σN 2^e` -/
theorem rd_sum {sg : ℝ} (hsg : |sg| = 1) {N hb : ℕ} (h1 : 2 ^ hb ≤ N) (e : ℤ) :
    |sg * N * 2 ^ e - ∑ j ∈ range 8, rdPart sg N hb e j| ≤ 2 ^ (-423 : ℤ) * N * 2 ^ e := by
  have hE : (0 : ℝ) < 2 ^ e := by positivity
  have hs : ∑ j ∈ range 8, rdPart sg N hb e j = sg * 2 ^ e * (chT N hb 7 * 2 ^ chB hb 7) := by
    rw [← chunk_sum N hb 7, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [rdPart, zpow_add₀ two_ne_zero]; ring
  rw [hs, show sg * N * 2 ^ e - sg * 2 ^ e * (chT N hb 7 * 2 ^ chB hb 7) =
    sg * 2 ^ e * (N - chT N hb 7 * 2 ^ chB hb 7) by ring, abs_mul, abs_mul, hsg, abs_of_pos hE, one_mul]
  obtain ⟨t1, t2⟩ := chT_trunc N hb 7
  rw [abs_of_nonneg t1]
  -- `2^{b_7} = 2^{h_b - 423} ≤ 2^{-423} N`
  have hb7 : (2 : ℝ) ^ chB hb 7 ≤ 2 ^ (-423 : ℤ) * N := by
    have : (2 : ℝ) ^ chB hb 7 = 2 ^ (-423 : ℤ) * 2 ^ hb := by
      rw [chB, ← zpow_natCast, ← zpow_add₀ two_ne_zero]; congr 1; push_cast; ring
    rw [this]
    gcongr
    exact_mod_cast h1
  calc 2 ^ e * ((N : ℝ) - chT N hb 7 * 2 ^ chB hb 7) ≤ 2 ^ e * 2 ^ chB hb 7 := by gcongr
    _ ≤ 2 ^ e * (2 ^ (-423 : ℤ) * N) := by gcongr
    _ = 2 ^ (-423 : ℤ) * N * 2 ^ e := by ring

variable (p : ℤ) [Prec_gt_0 p]

/-- each part is a float -/
theorem rd_F (hp : p = 53) {sg : ℝ} (hsg : |sg| = 1) {N hb : ℕ} (h1 : 2 ^ hb ≤ N) (h2 : N < 2 ^ (hb + 1)) (e : ℤ)
    (j : ℕ) : F p (rdPart sg N hb e j) := by
  have hc : 0 ≤ chunk N hb j ∧ chunk N hb j < 2 ^ 53 := by
    rcases j with _ | j
    · have := chunk_zero h1 h2; omega
    · exact chunk_succ N hb j
  obtain ⟨s, hs⟩ : ∃ s : ℤ, (s : ℝ) = sg := by
    rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp hsg with h | h
    exacts [⟨1, by simp [h]⟩, ⟨-1, by simp [h]⟩]
  have hS : (0 : ℝ) < 2 ^ (chB hb j + e) := zpow_pos (by norm_num) _
  refine F_of_mult_le p (E := chB hb j + e) ⟨s * chunk N hb j, by rw [rdPart, ← hs]; push_cast; ring⟩ ?_
  have hc1 : |(chunk N hb j : ℝ)| ≤ 2 ^ 53 := by
    rw [abs_of_nonneg (by exact_mod_cast hc.1)]
    exact_mod_cast hc.2.le
  have e1 : (2 : ℝ) ^ (chB hb j + e + p) = 2 ^ 53 * 2 ^ (chB hb j + e) := by
    rw [hp, zpow_add₀ two_ne_zero, mul_comm]; norm_num
  rw [rdPart, abs_mul, abs_mul, hsg, one_mul, abs_of_pos hS, e1]
  exact mul_le_mul_of_nonneg_right hc1 hS.le

omit [Prec_gt_0 p] in
/-- each part past the first is at most `(2u)^j` times the first -/
theorem rd_H {sg : ℝ} (hsg : |sg| = 1) {N hb : ℕ} (h1 : 2 ^ hb ≤ N) (h2 : N < 2 ^ (hb + 1)) (hp : p = 53) (e : ℤ)
    {j : ℕ} (hj : 1 ≤ j) : |rdPart sg N hb e j| ≤ (2 * u p) ^ j * |rdPart sg N hb e 0| := by
  obtain ⟨c1, -⟩ := chunk_zero h1 h2
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  obtain ⟨hc0, hc⟩ := chunk_succ N hb i
  have hSj : (0 : ℝ) < 2 ^ (chB hb (i + 1) + e) := zpow_pos (by norm_num) _
  have hS0 : (0 : ℝ) < 2 ^ (chB hb 0 + e) := zpow_pos (by norm_num) _
  simp only [rdPart, abs_mul, hsg, one_mul]
  rw [abs_of_nonneg (by exact_mod_cast hc0 : (0 : ℝ) ≤ chunk N hb (i + 1)),
    abs_of_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ chunk N hb 0) : (0 : ℝ) ≤ chunk N hb 0),
    abs_of_pos hSj, abs_of_pos hS0]
  have hcR : (chunk N hb (i + 1) : ℝ) ≤ 2 ^ 53 := by exact_mod_cast hc.le
  have hc0R : (2 : ℝ) ^ 52 ≤ chunk N hb 0 := by exact_mod_cast c1
  -- `2u = 2^{-52}`, and `53 + b_{i+1} ≤ -52(i + 1) + 52 + b_0`
  have h2u : 2 * u p = 2 ^ (-52 : ℤ) := by
    rw [u, hp, show (-52 : ℤ) = 1 + -53 by norm_num, zpow_add₀ two_ne_zero]; norm_num
  have key : (2 : ℝ) ^ 53 * 2 ^ (chB hb (i + 1) + e) ≤ (2 * u p) ^ (i + 1) * (2 ^ 52 * 2 ^ (chB hb 0 + e)) := by
    rw [h2u, ← zpow_natCast ((2 : ℝ) ^ (-52 : ℤ)) (i + 1), ← zpow_mul, ← zpow_natCast (2 : ℝ) 53,
      ← zpow_natCast (2 : ℝ) 52, ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero]
    exact zpow_le_zpow_right₀ (by norm_num) (by unfold chB; push_cast; omega)
  have hup : 0 ≤ (2 * u p) ^ (i + 1) := by rw [h2u]; positivity
  calc (chunk N hb (i + 1) : ℝ) * 2 ^ (chB hb (i + 1) + e) ≤ 2 ^ 53 * 2 ^ (chB hb (i + 1) + e) := by gcongr
    _ ≤ (2 * u p) ^ (i + 1) * (2 ^ 52 * 2 ^ (chB hb 0 + e)) := key
    _ ≤ (2 * u p) ^ (i + 1) * ((chunk N hb 0 : ℝ) * 2 ^ (chB hb 0 + e)) := by gcongr

end ExpansionBounds

/-!
## `series::mullow` at octo-double: an output index

The accumulator of an output index receives `K ≤ 50` terms, each a pair's eight parts (ADDX) or a product of two
coefficients (ADDPROD), on `H(2)`. When each term is within `δ A_k` of its share `T_k` of `c_m` and its `μ_k` at
most `c A_k`, the accumulator's result is within `2^{-424}|∑T_k| + (δ + 2^{-424}(δ + c)) ∑A_k` of `∑ T_k`
(`od_index`). A pair whose integer `V` times `2^e` is within `ρ A` of its terms `T`, `|T| ≤ A`, gives parts within
`(ρ + 2^{-423}(1 + ρ)) A` of `T`, with `μ ≤ (1 + ρ) A` (`pair_term`).
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) [Prec_gt_0 p]

/-- an output index: the accumulator's result against the terms' shares -/
theorem od_index (hp : p = 53) (K : ℕ) (hK1 : 1 ≤ K) (hK : K ≤ 50) (prod : ℕ → Bool) (x y : ℕ → ℕ → ℝ)
    (hx : ∀ k ∈ Icc 1 K, ∀ i < 8, F p (x k i)) (hy : ∀ k ∈ Icc 1 K, prod k = true → ∀ j < 8, F p (y k j))
    (hHx : ∀ k ∈ Icc 1 K, Htheta p 8 2 (x k)) (hHy : ∀ k ∈ Icc 1 K, prod k = true → Htheta p 8 2 (y k))
    {T A : ℕ → ℝ} {δ c : ℝ}
    (hT : ∀ k ∈ Icc 1 K, |(if prod k then (∑ i ∈ range 8, x k i) * ∑ j ∈ range 8, y k j else ∑ i ∈ range 8, x k i) -
      T k| ≤ δ * A k)
    (hmu : ∀ k ∈ Icc 1 K, accMu prod x y k ≤ c * A k) :
    |∑ k ∈ Icc 1 K, T k - ∑ i ∈ range 8, finishR p 8 (accLev p 8 prod x y K) 8 i| ≤
      (2 : ℝ) ^ (-424 : ℝ) * |∑ k ∈ Icc 1 K, T k| +
        (δ + (2 : ℝ) ^ (-424 : ℝ) * (δ + c)) * ∑ k ∈ Icc 1 K, A k := by
  have h := (acc8 p hp K hK1 hK prod x y hx hy hHx hHy).1
  set Z := accZ 8 prod x y K
  set R := ∑ i ∈ range 8, finishR p 8 (accLev p 8 prod x y K) 8 i
  have hZT : |Z - ∑ k ∈ Icc 1 K, T k| ≤ δ * ∑ k ∈ Icc 1 K, A k := by
    rw [mul_sum, show Z - ∑ k ∈ Icc 1 K, T k = ∑ k ∈ Icc 1 K,
      ((if prod k then (∑ i ∈ range 8, x k i) * ∑ j ∈ range 8, y k j else ∑ i ∈ range 8, x k i) - T k) by
        rw [sum_sub_distrib]; rfl]
    exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum hT)
  have hW : ∑ j ∈ Icc 1 K, accMu prod x y j ≤ c * ∑ k ∈ Icc 1 K, A k := by
    rw [mul_sum]; exact sum_le_sum hmu
  have hZ : |Z| ≤ |∑ k ∈ Icc 1 K, T k| + δ * ∑ k ∈ Icc 1 K, A k := by
    have := abs_add_le (Z - ∑ k ∈ Icc 1 K, T k) (∑ k ∈ Icc 1 K, T k)
    rw [sub_add_cancel] at this
    linarith
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-424 : ℝ) := by positivity
  have h3 := mul_le_mul_of_nonneg_left (add_le_add hZ hW) h2
  calc |∑ k ∈ Icc 1 K, T k - R| ≤ |∑ k ∈ Icc 1 K, T k - Z| + |Z - R| := abs_sub_le _ _ _
    _ ≤ δ * ∑ k ∈ Icc 1 K, A k + (2 : ℝ) ^ (-424 : ℝ) * (|Z| + ∑ j ∈ Icc 1 K, accMu prod x y j) := by
        rw [abs_sub_comm]; exact add_le_add hZT h
    _ ≤ _ := by nlinarith

omit [Prec_gt_0 p] in
/-- the parts of `σN 2^e` sum to at most `N 2^e` in their first part -/
theorem rd_first {sg : ℝ} (hsg : |sg| = 1) (N hb : ℕ) (e : ℤ) : |rdPart sg N hb e 0| ≤ N * 2 ^ e := by
  have hS : (0 : ℝ) < 2 ^ chB hb 0 := by positivity
  have h1 := Int.floor_le ((N : ℝ) / 2 ^ chB hb 0)
  rw [le_div_iff₀ hS] at h1
  have h0 : (0 : ℝ) ≤ chunk N hb 0 := by
    simp only [chunk, chT]; exact_mod_cast Int.floor_nonneg.mpr (by positivity)
  rw [rdPart, abs_mul, abs_mul, hsg, one_mul, abs_of_nonneg h0, abs_of_pos (by positivity), zpow_add₀ two_ne_zero,
    ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (by simpa [chunk, chT] using h1) (by positivity)

/-- an FFT pair's term: its eight parts against its terms `T`, from `|V 2^e - T| ≤ ρA` and `|T| ≤ A` -/
theorem pair_term (hp : p = 53) (V : ℤ) (e : ℤ) {T A ρ : ℝ} (hρ : 0 ≤ ρ) (hV : |(V : ℝ) * 2 ^ e - T| ≤ ρ * A)
    (hTA : |T| ≤ A) :
    let sg : ℝ := if V < 0 then -1 else 1
    let x := rdPart sg V.natAbs (Nat.log 2 V.natAbs) e
    (∀ i < 8, F p (x i)) ∧ Htheta p 8 2 x ∧ |∑ i ∈ range 8, x i - T| ≤ (ρ + 2 ^ (-423 : ℤ) * (1 + ρ)) * A ∧
      |x 0| ≤ (1 + ρ) * A := by
  intro sg x
  have hsg : |sg| = 1 := by simp only [sg]; split_ifs <;> norm_num
  have hVs : (V : ℝ) = sg * V.natAbs := by
    simp only [sg]
    split_ifs with h
    · have : (V.natAbs : ℝ) = -V := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast h)]
      rw [this]; ring
    · have : (V.natAbs : ℝ) = V := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast not_lt.mp h)]
      rw [this]; ring
  have hE : (0 : ℝ) < 2 ^ e := by positivity
  have hA : 0 ≤ A := (abs_nonneg _).trans hTA
  have hVA : (V.natAbs : ℝ) * 2 ^ e ≤ (1 + ρ) * A := by
    have h1 : (V.natAbs : ℝ) * 2 ^ e = |(V : ℝ) * 2 ^ e| := by
      rw [abs_mul, abs_of_pos hE, Nat.cast_natAbs, Int.cast_abs]
    have := abs_add_le ((V : ℝ) * 2 ^ e - T) T
    rw [sub_add_cancel] at this
    rw [h1]; linarith
  rcases Nat.eq_zero_or_pos V.natAbs with h0 | hpos
  · -- `V = 0`: all parts are zero
    have hz : ∀ i, x i = 0 := fun i => by
      simp only [x, rdPart, h0]
      rcases i with _ | i <;> simp [chunk, chT]
    have hV0 : (V : ℝ) = 0 := by rw [hVs, h0]; simp
    refine ⟨fun i _ => by rw [hz]; exact F_zero p, fun i _ _ => by simp [hz], ?_, by rw [hz]; simp; positivity⟩
    rw [sum_congr rfl fun i _ => hz i, sum_const_zero, zero_sub, abs_neg]
    rw [hV0, zero_mul, zero_sub, abs_neg] at hV
    have : 0 ≤ 2 ^ (-423 : ℤ) * (1 + ρ) * A := by positivity
    nlinarith
  · set N := V.natAbs
    set hb := Nat.log 2 N
    have h1 : 2 ^ hb ≤ N := Nat.pow_log_le_self 2 (by omega)
    have h2 : N < 2 ^ (hb + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
    refine ⟨fun i _ => rd_F p hp hsg h1 h2 e i, fun i hi _ => rd_H p hsg h1 h2 hp e hi, ?_,
      (rd_first hsg N hb e).trans hVA⟩
    have hr := rd_sum hsg h1 e
    rw [← hVs] at hr
    have h4 : (2 : ℝ) ^ (-423 : ℤ) * N * 2 ^ e ≤ 2 ^ (-423 : ℤ) * ((1 + ρ) * A) := by
      rw [mul_assoc]; gcongr
    calc |∑ i ∈ range 8, x i - T| ≤ |(V : ℝ) * 2 ^ e - ∑ i ∈ range 8, x i| + |(V : ℝ) * 2 ^ e - T| := by
          have := abs_sub_le (∑ i ∈ range 8, x i) ((V : ℝ) * 2 ^ e) T
          rwa [abs_sub_comm (∑ i ∈ range 8, x i) ((V : ℝ) * 2 ^ e)] at this
      _ ≤ 2 ^ (-423 : ℤ) * ((1 + ρ) * A) + ρ * A := add_le_add (hr.trans h4) hV
      _ = (ρ + 2 ^ (-423 : ℤ) * (1 + ρ)) * A := by ring

end ExpansionBounds

/-!
## `series::mullow` at octo-double: the bound of an output index

An output index's accumulator receives `K ≤ 50` terms: block pairs' eight parts, each within `ρ A_k`,
`ρ = 1.13 · 2^{-424}`, of its share `T_k` (what `pair_value` and `plan_rho` give, the FFT's exactness assumed), and
products of two octo-doubles formed term by term. Then the result is within `2^{-424}|c_m| + 4.15 · 2^{-424} ∑|a_i
b_j|` of `c_m = ∑ T_k` (`mullow_od`).
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) [Prec_gt_0 p]

omit [Prec_gt_0 p] in
/-- parts each at most `u` times the one before are on `H(2)` -/
theorem htheta_of_ord {x : ℕ → ℝ} (hord : ∀ i, |x (i + 1)| ≤ u p * |x i|) : Htheta p 8 2 x := by
  have hu : 0 ≤ u p := by unfold u; positivity
  have h : ∀ i, |x i| ≤ u p ^ i * |x 0| := fun i => by
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ]; nlinarith [hord i, abs_nonneg (x i)]
  intro i _ _
  refine (h i).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu (by linarith) i) (abs_nonneg _))

omit [Prec_gt_0 p] in
/-- the first of such parts is at most `1/(1 - 2u)` times their sum -/
theorem first_le_sum {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ 1 / 4) {x : ℕ → ℝ} (hord : ∀ i, |x (i + 1)| ≤ v * |x i|) :
    |x 0| * (1 - 2 * v) ≤ |∑ i ∈ range 8, x i| := by
  have hT := abs_parts_le hv0 hord 7
  have h3 := abs_tail_le hv0 hord 7
  have e := sum_range_succ' (fun i => |x i|) 7
  have h1 : |∑ i ∈ range 7, x (i + 1)| ≤ ∑ i ∈ range 7, |x (i + 1)| := abs_sum_le_sum_abs _ _
  have h4 : ∑ i ∈ range 8, |x i| ≤ 2 * |x 0| := by nlinarith [abs_nonneg (x 0)]
  have hs : ∑ i ∈ range 8, x i = ∑ i ∈ range 7, x (i + 1) + x 0 := sum_range_succ' _ 7
  have := abs_sub_abs_le_abs_sub (x 0) (-∑ i ∈ range 7, x (i + 1))
  rw [abs_neg, sub_neg_eq_add, add_comm, ← hs] at this
  nlinarith [abs_nonneg (x 0)]

/-- an output index of `mullow` at octo-double -/
theorem mullow_od (hp : p = 53) (K : ℕ) (hK1 : 1 ≤ K) (hK : K ≤ 50) (prod : ℕ → Bool) (x y : ℕ → ℕ → ℝ)
    {T A : ℕ → ℝ}
    (hpair : ∀ k ∈ Icc 1 K, prod k = false → ∃ (V : ℤ) (e : ℤ),
      x k = rdPart (if V < 0 then -1 else 1) V.natAbs (Nat.log 2 V.natAbs) e ∧
        |(V : ℝ) * 2 ^ e - T k| ≤ 113 / 100 * 2 ^ (-424 : ℤ) * A k ∧ |T k| ≤ A k)
    (hprod : ∀ k ∈ Icc 1 K, prod k = true → (∀ i < 8, F p (x k i)) ∧ (∀ j < 8, F p (y k j)) ∧
      (∀ i, |x k (i + 1)| ≤ u p * |x k i|) ∧ (∀ j, |y k (j + 1)| ≤ u p * |y k j|) ∧
      T k = (∑ i ∈ range 8, x k i) * ∑ j ∈ range 8, y k j ∧ A k = |∑ i ∈ range 8, x k i| * |∑ j ∈ range 8, y k j|) :
    |∑ k ∈ Icc 1 K, T k - ∑ i ∈ range 8, finishR p 8 (accLev p 8 prod x y K) 8 i| ≤
      2 ^ (-424 : ℤ) * |∑ k ∈ Icc 1 K, T k| + 83 / 20 * 2 ^ (-424 : ℤ) * ∑ k ∈ Icc 1 K, A k := by
  set v : ℝ := 2 ^ (-424 : ℤ) with hv
  have hv0 : 0 < v := by positivity
  have hv1 : v ≤ 1 / 10 ^ 6 := by
    rw [hv, zpow_neg, zpow_ofNat, ← one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
    calc (10 : ℝ) ^ 6 ≤ 2 ^ 20 := by norm_num
      _ ≤ 2 ^ 424 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hu : u p = 2 ^ (-53 : ℤ) := by rw [u, hp]
  have hu1 : u p ≤ 1 / 2 ^ 50 := by
    rw [hu]; norm_num
  have hu0 : 0 ≤ u p := by rw [hu]; positivity
  have h423 : (2 : ℝ) ^ (-423 : ℤ) = 2 * v := by
    rw [hv, show (-423 : ℤ) = 1 + -424 by norm_num, zpow_add₀ two_ne_zero]; norm_num
  have hrp : (2 : ℝ) ^ (-424 : ℝ) = v := by
    rw [hv, show (-424 : ℝ) = ((-424 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
  set ρ : ℝ := 113 / 100 * v
  set δ : ℝ := ρ + 2 ^ (-423 : ℤ) * (1 + ρ)
  have hδ0 : 0 ≤ δ := by simp only [δ, ρ]; positivity
  -- every term is within `δ A_k` of its share, with `μ_k ≤ 1.0001 A_k`
  have hA0 : ∀ k ∈ Icc 1 K, 0 ≤ A k := fun k hk => by
    cases hb : prod k
    · obtain ⟨V, e, -, -, hTA⟩ := hpair k hk hb; exact (abs_nonneg _).trans hTA
    · obtain ⟨-, -, -, -, -, hA⟩ := hprod k hk hb; rw [hA]; positivity
  have hterm : ∀ k ∈ Icc 1 K, (∀ i < 8, F p (x k i)) ∧ (prod k = true → ∀ j < 8, F p (y k j)) ∧
      Htheta p 8 2 (x k) ∧ (prod k = true → Htheta p 8 2 (y k)) ∧
      |(if prod k then (∑ i ∈ range 8, x k i) * ∑ j ∈ range 8, y k j else ∑ i ∈ range 8, x k i) - T k| ≤ δ * A k ∧
      accMu prod x y k ≤ 10001 / 10000 * A k := fun k hk => by
    cases hb : prod k
    · obtain ⟨V, e, hx, hV, hTA⟩ := hpair k hk hb
      obtain ⟨hF, hH, hs, hm⟩ := pair_term p hp V e (by positivity) hV hTA
      rw [hx]
      refine ⟨hF, fun h => absurd h (by simp), hH, fun h => absurd h (by simp), ?_, ?_⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact hs
      · simp only [accMu, hb, Bool.false_eq_true, ↓reduceIte]
        rw [hx]
        refine hm.trans (mul_le_mul_of_nonneg_right ?_ ((abs_nonneg _).trans hTA))
        show 1 + 113 / 100 * v ≤ 10001 / 10000
        linarith
    · obtain ⟨hFx, hFy, hox, hoy, hT, hA⟩ := hprod k hk hb
      refine ⟨hFx, fun _ => hFy, htheta_of_ord p hox, fun _ => htheta_of_ord p hoy, ?_, ?_⟩
      · simp only [↓reduceIte, hT, sub_self, abs_zero]; exact mul_nonneg hδ0 (hA0 k hk)
      · simp only [accMu, hb, ↓reduceIte]
        rw [hA, abs_mul]
        have h1 := first_le_sum hu0 (by linarith) hox
        have h2 := first_le_sum hu0 (by linarith) hoy
        have hc : (10001 / 10000 : ℝ) * (1 - 2 * u p) * (1 - 2 * u p) ≥ 1 := by nlinarith
        have := mul_le_mul h1 h2 (by nlinarith [abs_nonneg (y k 0)]) (abs_nonneg _)
        nlinarith [abs_nonneg (x k 0), abs_nonneg (y k 0), mul_nonneg (abs_nonneg (x k 0)) (abs_nonneg (y k 0))]
  have h := od_index p hp K hK1 hK prod x y (fun k hk => (hterm k hk).1) (fun k hk => (hterm k hk).2.1)
    (fun k hk => (hterm k hk).2.2.1) (fun k hk => (hterm k hk).2.2.2.1) (fun k hk => (hterm k hk).2.2.2.2.1)
    (fun k hk => (hterm k hk).2.2.2.2.2)
  rw [hrp] at h
  have hsA : 0 ≤ ∑ k ∈ Icc 1 K, A k := sum_nonneg hA0
  -- `δ + v(δ + 1.0001) ≤ 4.15 v`
  have hc : δ + v * (δ + 10001 / 10000) ≤ 83 / 20 * v := by
    have e : δ + v * (δ + 10001 / 10000) = 41301 / 10000 * v + 539 / 100 * v ^ 2 + 113 / 50 * v ^ 3 := by
      simp only [δ, ρ, h423]; ring
    have hv2 : v ^ 2 ≤ v / 10 ^ 6 := by nlinarith
    have hv3 : v ^ 3 ≤ v / 10 ^ 6 := by nlinarith
    rw [e]; nlinarith
  calc _ ≤ v * |∑ k ∈ Icc 1 K, T k| + (δ + v * (δ + 10001 / 10000)) * ∑ k ∈ Icc 1 K, A k := h
    _ ≤ v * |∑ k ∈ Icc 1 K, T k| + 83 / 20 * v * ∑ k ∈ Icc 1 K, A k := by gcongr

end ExpansionBounds
