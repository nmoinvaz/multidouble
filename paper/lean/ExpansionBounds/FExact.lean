import ExpansionBounds.SinCos
import FloatSpec.src.Prop.Sterbenz

/-!
# Lemma 41: `φ = x' - 1` exactly

LOG's step (3) forms `φ = ADDF(x', -1)`. For `x'_0 ∈ [1/2, 2]` its first `TwoSum(x'_0, -1)` is exact by Sterbenz, each
later one is `TwoSum(x'_i, 0) = (x'_i, 0)`, and the level `s_n` is zero; then VecSum's last error is zero, and by
Theorem 9 (a) the renormalization loses nothing. The range of `x'_0` is the lemma's first step, from Lemma 38 (a),
Theorem 42's bound on `e_0` and (eq:a0), which rest on binary64's exponent range; here it is the hypothesis.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) [Prec_gt_0 p] (n : ℕ)

theorem twoSum_zero {a : ℝ} (ha : F p a) : twoSum p a 0 = (a, 0) := by
  have h0 : RN p 0 = 0 := RN_of_F p (F_zero p)
  simp [twoSum, RN_of_F p ha, h0]

omit [Prec_gt_0 p] in
/-- VecSum's last output is the error of `TwoSum(c_{m}, c_{m+1})` -/
theorem vecSum_last (m : ℕ) : ∀ c : ℕ → ℝ, vecSum p (m + 1) c (m + 1) = (twoSum p (c m) (c (m + 1))).2 := by
  induction m with
  | zero => intro c; simp [vecSum]
  | succ m ih =>
    intro c
    rw [vecSum_succ_add_two, ih]

/-- Theorem 9 (a) with a zero last term: `Ren_n(c_0, …, c_n)` is exact when `c_n = 0` -/
theorem ren_exact_of_last (hp : 1 < p) (hn : 1 ≤ n) (c : ℕ → ℝ) (hc : ∀ i ≤ n, F p (c i)) (hl : c n = 0) :
    (ren p n n c).sum = ∑ i ∈ range (n + 1), c i := by
  by_contra h
  have hE : renErr p n c ≠ 0 := fun h' => h (by unfold renErr at h'; linarith)
  obtain ⟨-, -, h3⟩ := renErr_eq_accChain p hp n hn c hc hE
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hv : vecSum p (m + 1) c (m + 1) = 0 := by rw [vecSum_last, hl, twoSum_zero p (hc m (by omega))]
  have hacc : accChain p (vecSum p (m + 1) c) (m + 1) = 0 := by
    simp only [accChain]
    rw [hv, twoSum_zero p (accChain_F p _ (vecSum_F p (m + 1) c hc 0) m)]
  exact hE (h3.trans hacc)

/-- Lemma 41 (`lem:fexact`): for `x'` with `x'_0 ∈ [1/2, 2]`, `ADDF(x', -1) = x' - 1` exactly -/
theorem lemma_fexact (hp : 1 < p) (hn : 1 ≤ n) (x : ℕ → ℝ) (hx : ∀ i < n, F p (x i)) (h0 : 1 / 2 ≤ x 0)
    (h2 : x 0 ≤ 2) : (addfOp p n x (-1)).sum = ∑ i ∈ range n, x i - 1 := by
  have h1 : F p 1 := by simpa using F_two_zpow p 0
  have hm1 : F p (-1) := F_neg p h1
  have hs : F p (x 0 - 1) :=
    sterbenz 2 (FloatSpec.Core.FLX.FLX_exp p) (x 0) 1 (hx 0 hn) h1 (by norm_num) ⟨by linarith, by linarith⟩
  -- the carries after the first `TwoSum` are zero
  have he : ∀ m, 1 ≤ m → m ≤ n → addfE p x (-1) m = 0 := by
    intro m hm1' hmn
    induction m with
    | zero => omega
    | succ m ih =>
      simp only [addfE]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · have := twoSum_add p hp (hx 0 hn) hm1
        have hs1 : (twoSum p (x 0) (-1)).1 = x 0 - 1 := by
          show RN p (x 0 + -1) = _
          rw [← sub_eq_add_neg, RN_of_F p hs]
        simp only [addfE] at this ⊢
        linarith
      · rw [ih hm (by omega), twoSum_zero p (hx m (by omega))]
  have hl : addfLevels p n x (-1) n = 0 := by simp [addfLevels, he n hn le_rfl]
  have hlev : ∀ i ≤ n, F p (addfLevels p n x (-1) i) := by
    intro i hi
    rcases Nat.lt_or_ge i n with hlt | hge
    · simp only [addfLevels, hlt, ite_true]
      exact F_twoSum_fst p _ _
    · obtain rfl : i = n := by omega
      rw [hl]
      exact F_zero p
  have hsum := (lemma13_addf p hp hn x (-1) hx hm1 (fun i => |x i|) (fun _ _ => le_rfl) _ le_rfl _ le_rfl).2.2.2.2
  unfold addfOp
  rw [ren_exact_of_last p n hp hn _ hlev hl, hsum]
  ring

end ExpansionBounds
