import ExpansionBounds.Closure
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Corollary 18 (`cor:closure`): closure at `n = 8` and `p = 53`

Theorem 17 with its constants evaluated in rational arithmetic: on `H(2)` operands MUL returns a result on
`H(1 + 4.032·10^{-7})`, `1 + 4.032·10^{-7} ≤ 1 + 2^{-21.2}`, and MULF, and ADD and ADDF with leading parts of one sign,
results on `H(1 + 2^{-36})`. Each `i`-th root is bounded through `(1 + δ)^i ≥ 1 + iδ`.
-/

namespace ExpansionBounds

open Finset

/-- the check of Theorem 17's `θ'` at one `i`, with `Λ ≤ Λ̄` and `ξ ≥ ξ̲` -/
theorem cor18_check {n i : ℕ} {u Λ ξ ΛU ξL δ : ℝ} (hu0 : 0 ≤ u) (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ ΛU) (hξL : 0 < ξL) (hξ : ξL ≤ ξ)
    (hδ : 0 ≤ δ) (hnum : (1 + u) ^ i + i * u * (1 + u) ^ (n + i - 1) * ΛU / ξL ≤ 1 + i * δ) :
    (1 + u) ^ i + i * u * (1 + u) ^ (n + i - 1) * Λ / ξ ≤ (1 + δ) ^ i := by
  refine le_trans ?_ (hnum.trans (one_add_mul_le_pow (by linarith) i))
  refine add_le_add le_rfl ?_
  have hc : 0 ≤ (i : ℝ) * u * (1 + u) ^ (n + i - 1) := by positivity
  exact div_le_div₀ (mul_nonneg hc (hΛ0.trans hΛ))
    (mul_le_mul_of_nonneg_left hΛ hc) hξL hξ

variable (p : ℤ) [Prec_gt_0 p]

omit [Prec_gt_0 p] in
theorem u_53 (hp : p = 53) : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num

omit [Prec_gt_0 p] in
/-- `θ ≤ θ'` carries `H(θ)` to `H(θ')` -/
theorem Htheta_mono {n : ℕ} {θ θ' : ℝ} (hθ : 0 ≤ θ) (h : θ ≤ θ') {a : ℕ → ℝ} (hH : Htheta p n θ a) :
    Htheta p n θ' a := fun i h1 h2 =>
  (hH i h1 h2).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg hθ (u_pos p).le)
    (mul_le_mul_of_nonneg_right h (u_pos p).le) i) (abs_nonneg _))

/-- MUL on `H(2)` operands returns a result with the part bounds of `H(1 + δ)` given bounds `Λ̄`, `L̄_n` and `Δ̄` on its
constants and `ξ̲` on `ξ` with `(1 + u)^i + iu(1 + u)^{n+i-1}Λ̄/ξ̲ ≤ 1 + iδ`; `Htheta` checks only the part bounds, so
the paper's `H(1 + δ)` also needs `1 + δ ≤ 1/(4u)`, which the caller checks -/
theorem mul_closure (hp : p = 53) (n : ℕ) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {ΛU LU DU ξL δ : ℝ}
    (hΛ0 : 0 ≤ ∑ m ∈ range (n + 1), mulL p n 2 m) (hΛ : ∑ m ∈ range (n + 1), mulL p n 2 m ≤ ΛU)
    (hL : mulL p n 2 n ≤ LU) (hD : thmDelta p n 2 ≤ DU) (hξL : 0 < ξL)
    (hξ : ξL ≤ (((1 - 2 * (2 * u p)) / (1 - 2 * u p)) ^ 2 - (((n ^ 2 + n - 1 : ℕ) : ℝ) * LU + DU) * u p ^ (n + 1) -
      u p ^ 2 * (1 + u p) ^ (n - 1) * ΛU) / (1 + u p)) (hδ : 0 ≤ δ)
    (hchk : ∀ i : ℕ, 1 ≤ i → i < n → (1 + u p) ^ i + i * u p * (1 + u p) ^ (n + i - 1) * ΛU / ξL ≤ 1 + i * δ)
    (a b : ℕ → ℝ) (ha : ∀ i < n, F p (a i)) (hb : ∀ j < n, F p (b j)) (hHa : Htheta p n 2 a)
    (hHb : Htheta p n 2 b) : Htheta p n (1 + δ) fun i => (mulOp p n a b).getD i 0 := by
  have hu := u_53 p hp
  have hu0 := u_pos p
  obtain ⟨-, h2⟩ := thm17_mul p n (by omega) hn hA3 2 (by norm_num) a b ha hb hHa hHb
  have hρ : 2 * (2 * u p) < 1 := by rw [hu]; norm_num
  have hζ := zeta_mul p n hn 2 (by norm_num) hρ a b hHa hHb
  have hξ' : ξL ≤ (((1 - 2 * (2 * u p)) / (1 - 2 * u p)) ^ 2 - (((n ^ 2 + n - 1 : ℕ) : ℝ) * mulL p n 2 n +
      thmDelta p n 2) * u p ^ (n + 1) - u p ^ 2 * (1 + u p) ^ (n - 1) * ∑ m ∈ range (n + 1), mulL p n 2 m) /
        (1 + u p) := by
    refine hξ.trans (div_le_div_of_nonneg_right ?_ (by linarith))
    have h1 : (((n ^ 2 + n - 1 : ℕ) : ℝ) * mulL p n 2 n + thmDelta p n 2) * u p ^ (n + 1) ≤
        (((n ^ 2 + n - 1 : ℕ) : ℝ) * LU + DU) * u p ^ (n + 1) :=
      mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg _)) hD)
        (pow_nonneg hu0.le _)
    have h2 : u p ^ 2 * (1 + u p) ^ (n - 1) * ∑ m ∈ range (n + 1), mulL p n 2 m ≤ u p ^ 2 * (1 + u p) ^ (n - 1) * ΛU :=
      mul_le_mul_of_nonneg_left hΛ (by positivity)
    linarith
  obtain ⟨-, h3⟩ := h2 _ hζ (lt_of_lt_of_le hξL hξ')
  exact h3 _ fun i hi1 hi2 => cor18_check hu0.le hΛ0 hΛ hξL hξ' hδ (hchk i hi1 hi2)

omit [Prec_gt_0 p] in
/-- `4.032·10^{-7} ≤ 2^{-21.2}`, as `(4.032·10^{-7})^5 ≤ 2^{-106}` -/
theorem cor18_root : (4032 / 10 ^ 10 : ℝ) ≤ (2 : ℝ) ^ (-21.2 : ℝ) := by
  rw [← pow_le_pow_iff_left₀ (by norm_num) (by positivity) (by norm_num : 5 ≠ 0),
    ← Real.rpow_natCast ((2 : ℝ) ^ (-21.2 : ℝ)) 5,
    ← Real.rpow_mul (by norm_num), show (-21.2 : ℝ) * ((5 : ℕ) : ℝ) = -((106 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg (by norm_num), Real.rpow_natCast]
  norm_num

/-- Corollary 18 (`cor:closure`) for MUL at `n = 8`, `p = 53`: `H(2)` operands give a result on
`H(1 + 4.032·10^{-7})`, within `H(1 + 2^{-21.2})` and `H(2)` -/
theorem cor18_mul (hp : p = 53) (a b : ℕ → ℝ) (ha : ∀ i < 8, F p (a i)) (hb : ∀ j < 8, F p (b j))
    (hHa : Htheta p 8 2 a) (hHb : Htheta p 8 2 b) :
    Htheta p 8 (1 + 4032 / 10 ^ 10) (fun i => (mulOp p 8 a b).getD i 0) ∧
      Htheta p 8 (1 + (2 : ℝ) ^ (-21.2 : ℝ)) (fun i => (mulOp p 8 a b).getD i 0) ∧
        Htheta p 8 2 (fun i => (mulOp p 8 a b).getD i 0) := by
  have hu := u_53 p hp
  have h := mul_closure p hp 8 (by norm_num) (by rw [hu]; norm_num) (ΛU := 3630959978) (LU := 3565717250)
    (DU := 3074) (ξL := 999999 / 1000000) (δ := 4032 / 10 ^ 10)
    (by simp only [mulL, thmL, thmD, hatAmul, mulT, sum_range_succ, sum_range_zero, hu]; norm_num)
    (by simp only [mulL, thmL, thmD, hatAmul, mulT, sum_range_succ, sum_range_zero, hu]; norm_num)
    (by simp only [mulL, thmL, thmD, hatAmul, mulT, hu]; norm_num)
    (by simp only [thmDelta, Finset.sum_Ico_eq_sum_range, sum_range_succ, sum_range_zero, hu]; norm_num)
    (by norm_num) (by rw [hu]; norm_num) (by norm_num)
    (fun i h1 h2 => by interval_cases i <;> rw [hu] <;> norm_num) a b ha hb hHa hHb
  refine ⟨h, Htheta_mono p (by positivity) (by linarith [cor18_root]) h, Htheta_mono p (by positivity) ?_ h⟩
  norm_num

/-- the closure of Corollary 18 for MUL on `H(2)` holds for `n ≤ 11` at `p = 53`; at `n = 1` it holds vacuously, as
`Htheta` bounds only the parts `1 ≤ i < n` -/
theorem cor18_mul_le11 (hp : p = 53) (n : ℕ) (hn : 1 ≤ n) (hn11 : n ≤ 11) (a b : ℕ → ℝ)
    (ha : ∀ i < n, F p (a i)) (hb : ∀ j < n, F p (b j)) (hHa : Htheta p n 2 a) (hHb : Htheta p n 2 b) :
    Htheta p n 2 fun i => (mulOp p n a b).getD i 0 := by
  have hu := u_53 p hp
  rw [show (2 : ℝ) = 1 + 1 by norm_num]
  interval_cases n
  · exact fun i h1 h2 => absurd h2 (by omega)
  · exact mul_closure p hp 2 (by norm_num) (by rw [hu]; norm_num) (ΛU := 26) (LU := 20)
      (DU := 1) (ξL := 99 / 100) (δ := 1)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, hu]; norm_num)
      (by simp only [thmDelta, Finset.sum_Ico_eq_sum_range, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by norm_num) (by rw [hu]; norm_num) (by norm_num)
      (fun i h1 h2 => by interval_cases i; rw [hu]; norm_num) a b ha hb hHa hHb
  · exact mul_closure p hp 3 (by norm_num) (by rw [hu]; norm_num) (ΛU := 218) (LU := 186)
      (DU := 17) (ξL := 99 / 100) (δ := 1)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, hu]; norm_num)
      (by simp only [thmDelta, Finset.sum_Ico_eq_sum_range, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by norm_num) (by rw [hu]; norm_num) (by norm_num)
      (fun i h1 h2 => by interval_cases i <;> rw [hu] <;> norm_num) a b ha hb hHa hHb
  · exact mul_closure p hp 4 (by norm_num) (by rw [hu]; norm_num) (ΛU := 2714) (LU := 2482)
      (DU := 66) (ξL := 99 / 100) (δ := 1)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, hu]; norm_num)
      (by simp only [thmDelta, Finset.sum_Ico_eq_sum_range, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by norm_num) (by rw [hu]; norm_num) (by norm_num)
      (fun i h1 h2 => by interval_cases i <;> rw [hu] <;> norm_num) a b ha hb hHa hHb
  · exact mul_closure p hp 5 (by norm_num) (by rw [hu]; norm_num) (ΛU := 53194) (LU := 50450)
      (DU := 194) (ξL := 99 / 100) (δ := 1)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, hu]; norm_num)
      (by simp only [thmDelta, Finset.sum_Ico_eq_sum_range, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by norm_num) (by rw [hu]; norm_num) (by norm_num)
      (fun i h1 h2 => by interval_cases i <;> rw [hu] <;> norm_num) a b ha hb hHa hHb
  · exact mul_closure p hp 6 (by norm_num) (by rw [hu]; norm_num) (ΛU := 1569130) (LU := 1515874)
      (DU := 514) (ξL := 99 / 100) (δ := 1)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, hu]; norm_num)
      (by simp only [thmDelta, Finset.sum_Ico_eq_sum_range, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by norm_num) (by rw [hu]; norm_num) (by norm_num)
      (fun i h1 h2 => by interval_cases i <;> rw [hu] <;> norm_num) a b ha hb hHa hHb
  · exact mul_closure p hp 7 (by norm_num) (by rw [hu]; norm_num) (ΛU := 65242474) (LU := 63673218)
      (DU := 1282) (ξL := 99 / 100) (δ := 1)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, hu]; norm_num)
      (by simp only [thmDelta, Finset.sum_Ico_eq_sum_range, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by norm_num) (by rw [hu]; norm_num) (by norm_num)
      (fun i h1 h2 => by interval_cases i <;> rw [hu] <;> norm_num) a b ha hb hHa hHb
  · exact mul_closure p hp 8 (by norm_num) (by rw [hu]; norm_num) (ΛU := 3630959978) (LU := 3565717250)
      (DU := 3074) (ξL := 99 / 100) (δ := 1)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, hu]; norm_num)
      (by simp only [thmDelta, Finset.sum_Ico_eq_sum_range, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by norm_num) (by rw [hu]; norm_num) (by norm_num)
      (fun i h1 h2 => by interval_cases i <;> rw [hu] <;> norm_num) a b ha hb hHa hHb
  · exact mul_closure p hp 9 (by norm_num) (by rw [hu]; norm_num) (ΛU := 260362645610) (LU := 256731685122)
      (DU := 7170) (ξL := 99 / 100) (δ := 1)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, hu]; norm_num)
      (by simp only [thmDelta, Finset.sum_Ico_eq_sum_range, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by norm_num) (by rw [hu]; norm_num) (by norm_num)
      (fun i h1 h2 => by interval_cases i <;> rw [hu] <;> norm_num) a b ha hb hHa hHb
  · exact mul_closure p hp 10 (by norm_num) (by rw [hu]; norm_num) (ΛU := 23366214413931) (LU := 23105851767299)
      (DU := 16386) (ξL := 99 / 100) (δ := 1)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, hu]; norm_num)
      (by simp only [thmDelta, Finset.sum_Ico_eq_sum_range, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by norm_num) (by rw [hu]; norm_num) (by norm_num)
      (fun i h1 h2 => by interval_cases i <;> rw [hu] <;> norm_num) a b ha hb hHa hHb
  · exact mul_closure p hp 11 (by norm_num) (by rw [hu]; norm_num) (ΛU := 2565009909075723) (LU := 2541643694659746)
      (DU := 36866) (ξL := 99 / 100) (δ := 1)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by simp only [mulL, thmL, thmD, hatAmul, mulT, hu]; norm_num)
      (by simp only [thmDelta, Finset.sum_Ico_eq_sum_range, sum_range_succ, sum_range_zero, hu]; norm_num)
      (by norm_num) (by rw [hu]; norm_num) (by norm_num)
      (fun i h1 h2 => by interval_cases i <;> rw [hu] <;> norm_num) a b ha hb hHa hHb

/-- Corollary 18 for ADD at `n = 8`, `p = 53`: `H(2)` operands with leading parts of one sign give a result on
`H(1 + 2^{-36})` and `H(2)` -/
theorem cor18_add (hp : p = 53) (a b : ℕ → ℝ) (ha : ∀ i < 8, F p (a i))
    (hb : ∀ i < 8, F p (b i)) (hHa : Htheta p 8 2 a) (hHb : Htheta p 8 2 b) (hs : 0 ≤ a 0 * b 0) :
    Htheta p 8 (1 + 1 / 2 ^ 36) (fun i => (addOp p 8 a b).getD i 0) ∧
      Htheta p 8 2 (fun i => (addOp p 8 a b).getD i 0) := by
  have hu := u_53 p hp
  have hu0 := u_pos p
  have hΛ0 : 0 ≤ ∑ m ∈ range (8 + 1), pairL p 8 2 m := by
    simp only [pairL, thmL, thmD, hatApair, sum_range_succ, sum_range_zero, hu]; norm_num
  have hΛ : ∑ m ∈ range (8 + 1), pairL p 8 2 m ≤ 130511 := by
    simp only [pairL, thmL, thmD, hatApair, sum_range_succ, sum_range_zero, hu]; norm_num
  have hL : pairL p 8 2 8 ≤ 111346 := by simp only [pairL, thmL, thmD, hatApair, hu]; norm_num
  obtain ⟨-, h2⟩ := thm17_add p 8 (by omega) (by norm_num) (by rw [hu]; norm_num) 2 (by norm_num) a b ha hb hHa hHb
  have hζ := zeta_add p 8 (by norm_num) 2 (by norm_num) (by rw [hu]; norm_num) a b hHa hHb hs
  have hξ : 999999 / 1000000 ≤ ((1 - 2 * (2 * u p)) / (1 - 2 * u p) -
      ((8 - 1 : ℕ) : ℝ) * pairL p 8 2 8 * u p ^ (8 + 1) -
      u p ^ 2 * (1 + u p) ^ (8 - 1) * ∑ m ∈ range (8 + 1), pairL p 8 2 m) / (1 + u p) := by
    rw [le_div_iff₀ (by linarith), hu] at *
    norm_num at hΛ ⊢
    linarith
  obtain ⟨-, h3⟩ := h2 _ hζ (lt_of_lt_of_le (by norm_num) hξ)
  have h := h3 (1 + 1 / 2 ^ 36) fun i hi1 hi2 =>
    cor18_check hu0.le hΛ0 hΛ (by norm_num) hξ (by positivity) (by interval_cases i <;> rw [hu] <;> norm_num)
  exact ⟨h, Htheta_mono p (by positivity) (by norm_num) h⟩

/-- Corollary 18 for MULF at `n = 8`, `p = 53`: `H(2)` operands give a result on
`H(1 + 2^{-36})` and `H(2)` -/
theorem cor18_mulf (hp : p = 53) (a : ℕ → ℝ) (b : ℝ) (ha : ∀ i < 8, F p (a i))
    (hb : F p b) (hHa : Htheta p 8 2 a) :
    Htheta p 8 (1 + 1 / 2 ^ 36) (fun i => (mulfOp p 8 a b).getD i 0) ∧
      Htheta p 8 2 (fun i => (mulfOp p 8 a b).getD i 0) := by
  have hu := u_53 p hp
  have hu0 := u_pos p
  have hΛ0 : 0 ≤ ∑ m ∈ range (8 + 1), pairL p 8 2 m := by
    simp only [pairL, thmL, thmD, hatApair, sum_range_succ, sum_range_zero, hu]; norm_num
  have hΛ : ∑ m ∈ range (8 + 1), pairL p 8 2 m ≤ 130511 := by
    simp only [pairL, thmL, thmD, hatApair, sum_range_succ, sum_range_zero, hu]; norm_num
  have hL : pairL p 8 2 8 ≤ 111346 := by simp only [pairL, thmL, thmD, hatApair, hu]; norm_num
  obtain ⟨-, h2⟩ := thm17_mulf p 8 (by omega) (by norm_num) (by rw [hu]; norm_num) 2 (by norm_num) a b ha hb hHa
  have hζ := zeta_mulf p 8 (by norm_num) 2 (by norm_num) (by rw [hu]; norm_num) a b hHa
  have hξ : 999999 / 1000000 ≤ ((1 - 2 * (2 * u p)) / (1 - 2 * u p) -
      ((8 - 1 : ℕ) : ℝ) * pairL p 8 2 8 * u p ^ (8 + 1) -
      u p ^ 2 * (1 + u p) ^ (8 - 1) * ∑ m ∈ range (8 + 1), pairL p 8 2 m) / (1 + u p) := by
    rw [le_div_iff₀ (by linarith), hu] at *
    norm_num at hΛ ⊢
    linarith
  obtain ⟨-, h3⟩ := h2 _ hζ (lt_of_lt_of_le (by norm_num) hξ)
  have h := h3 (1 + 1 / 2 ^ 36) fun i hi1 hi2 =>
    cor18_check hu0.le hΛ0 hΛ (by norm_num) hξ (by positivity) (by interval_cases i <;> rw [hu] <;> norm_num)
  exact ⟨h, Htheta_mono p (by positivity) (by norm_num) h⟩

/-- Corollary 18 for ADDF at `n = 8`, `p = 53`: `H(2)` operands with leading parts of one sign give a result on
`H(1 + 2^{-36})` and `H(2)` -/
theorem cor18_addf (hp : p = 53) (a : ℕ → ℝ) (b : ℝ) (ha : ∀ i < 8, F p (a i))
    (hb : F p b) (hHa : Htheta p 8 2 a) (hs : 0 ≤ a 0 * b) :
    Htheta p 8 (1 + 1 / 2 ^ 36) (fun i => (addfOp p 8 a b).getD i 0) ∧
      Htheta p 8 2 (fun i => (addfOp p 8 a b).getD i 0) := by
  have hu := u_53 p hp
  have hu0 := u_pos p
  have hΛ0 : 0 ≤ ∑ m ∈ range (8 + 1), addfL p 8 2 m := by
    simp only [addfL, sum_range_succ, sum_range_zero, hu]; norm_num
  have hΛ : ∑ m ∈ range (8 + 1), addfL p 8 2 m ≤ 759 := by
    simp only [addfL, sum_range_succ, sum_range_zero, hu]; norm_num
  obtain ⟨-, h2⟩ := thm17_addf p 8 (by omega) (by norm_num) 2 (by norm_num) a b ha hb hHa
  have hζ := zeta_addf p 8 (by norm_num) 2 (by norm_num) (by rw [hu]; norm_num) a b hHa hs
  have hξ : 999999 / 1000000 ≤ ((1 - 2 * (2 * u p)) / (1 - 2 * u p) -
      0 * u p ^ (8 + 1) -
      u p ^ 2 * (1 + u p) ^ (8 - 1) * ∑ m ∈ range (8 + 1), addfL p 8 2 m) / (1 + u p) := by
    rw [le_div_iff₀ (by linarith), hu] at *
    norm_num at hΛ ⊢
    linarith
  obtain ⟨-, h3⟩ := h2 _ hζ (lt_of_lt_of_le (by norm_num) hξ)
  have h := h3 (1 + 1 / 2 ^ 36) fun i hi1 hi2 =>
    cor18_check hu0.le hΛ0 hΛ (by norm_num) hξ (by positivity) (by interval_cases i <;> rw [hu] <;> norm_num)
  exact ⟨h, Htheta_mono p (by positivity) (by norm_num) h⟩

end ExpansionBounds
