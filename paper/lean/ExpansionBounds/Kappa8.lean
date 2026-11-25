import ExpansionBounds.Cor18

/-!
# Table IV (`tab:kappa`): Theorem 15's `κ` at `n = 8` and `p = 53`

Theorem 15's `κ` evaluated in rational arithmetic, as `constants.py` computes it, for MUL, ADD, MULF and ADDF on
`H(1)` and `H(2)`: `κ ≤ 2^{36.41}`, `2^{17.97}`, `2^{17.97}` and `2^{6.46}` for `θ = 1`, and `2^{37.93}`, `2^{19.99}`,
`2^{19.99}` and `2^{10.57}` for `θ = 2`. Each power of two is bounded below through `c^{100} ≤ 2^{100x}`. For `θ = 2`
the bounds read `2^{-424}|Z| + κu^9M` with `κu^9` at most `2^{-439.07}`, `2^{-457.01}`, `2^{-457.01}` and
`2^{-466.43}`.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) [Prec_gt_0 p]

omit [Prec_gt_0 p] in
/-- `m/d ≤ 2^x` from `m^K ≤ 2^{Kx}d^K`, checked in `ℕ` -/
theorem le_two_rpow {m d N K : ℕ} {x : ℝ} (hd : 0 < d) (hK : K ≠ 0) (hN : x * K = N) (h : m ^ K ≤ 2 ^ N * d ^ K) :
    (m : ℝ) / d ≤ (2 : ℝ) ^ x := by
  have hc : (0 : ℝ) ≤ (m : ℝ) / d := by positivity
  rw [← pow_le_pow_iff_left₀ hc (by positivity) hK, ← Real.rpow_natCast ((2 : ℝ) ^ x) K, ← Real.rpow_mul (by norm_num),
    hN, Real.rpow_natCast, div_pow, div_le_iff₀ (by positivity)]
  exact_mod_cast h

omit [Prec_gt_0 p] in
/-- `u^8 = 2^{-424}` at `p = 53` -/
theorem u8_53 (hp : p = 53) : u p ^ 8 = (2 : ℝ) ^ (-424 : ℝ) := by
  rw [u_53 p hp, show (-424 : ℝ) = -((424 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num), Real.rpow_natCast,
    show (424 : ℕ) = 53 * 8 from rfl, pow_mul]
  norm_num

omit [Prec_gt_0 p] in
/-- `u = 2^{-53}` as the cast of a rational -/
theorem u_53_rat (hp : p = 53) : ((1 / 9007199254740992 : ℚ) : ℝ) = u p := by
  rw [u_53 p hp]
  norm_num

omit [Prec_gt_0 p] in
/-- `κ ≤ 2^x` gives `κu^9 ≤ 2^{x - 477}` at `p = 53` -/
theorem kappa_u9 (hp : p = 53) {κ x : ℝ} (h : κ ≤ (2 : ℝ) ^ x) : κ * u p ^ 9 ≤ (2 : ℝ) ^ (x - 477) := by
  have h9 : u p ^ 9 = ((2 : ℝ) ^ (477 : ℝ))⁻¹ := by
    rw [u_53 p hp, show (477 : ℝ) = ((477 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, show (477 : ℕ) = 53 * 9 from rfl,
      pow_mul]
    norm_num
  rw [Real.rpow_sub (by norm_num), div_eq_mul_inv, h9]
  exact mul_le_mul_of_nonneg_right h (by positivity)

omit [Prec_gt_0 p] in
/-- Table IV for MUL: `κ ≤ 2^{36.41}` on `H(1)` and `κ ≤ 2^{37.93}` on `H(2)` -/
theorem kappa8_mul (hp : p = 53) :
    thmKappa p 8 (mulL p 8 1) (((8 ^ 2 + 8 - 1 : ℕ) : ℝ) * mulL p 8 1 8 + thmDelta p 8 1) ≤ (2 : ℝ) ^ (36.41 : ℝ) ∧
      thmKappa p 8 (mulL p 8 2) (((8 ^ 2 + 8 - 1 : ℕ) : ℝ) * mulL p 8 2 8 + thmDelta p 8 2) ≤
        (2 : ℝ) ^ (37.93 : ℝ) := by
  have hu := u_53 p hp
  constructor
  · refine le_trans ?_
      (le_two_rpow (m := 91300000000) (d := 1) (N := 3641) (K := 100) (by norm_num) (by norm_num) (by norm_num)
        (by decide +kernel))
    simp only [thmKappa, mulL, thmL, thmD, hatAmul, mulT, thmDelta, sum_Ico_eq_sum_range, sum_range_succ,
      sum_range_zero, hu]
    norm_num
  · refine le_trans ?_
      (le_two_rpow (m := 260500000000) (d := 1) (N := 3793) (K := 100) (by norm_num) (by norm_num) (by norm_num)
        (by decide +kernel))
    simp only [thmKappa, mulL, thmL, thmD, hatAmul, mulT, thmDelta, sum_Ico_eq_sum_range, sum_range_succ,
      sum_range_zero, hu]
    norm_num

omit [Prec_gt_0 p] in
/-- Table IV for ADD and MULF: `κ ≤ 2^{17.97}` on `H(1)` and `κ ≤ 2^{19.99}` on `H(2)` -/
theorem kappa8_pair (hp : p = 53) :
    thmKappa p 8 (pairL p 8 1) (((8 - 1 : ℕ) : ℝ) * pairL p 8 1 8) ≤ (2 : ℝ) ^ (17.97 : ℝ) ∧
      thmKappa p 8 (pairL p 8 2) (((8 - 1 : ℕ) : ℝ) * pairL p 8 2 8) ≤ (2 : ℝ) ^ (19.99 : ℝ) := by
  have hu := u_53 p hp
  constructor
  · refine le_trans ?_
      (le_two_rpow (m := 256500) (d := 1) (N := 1797) (K := 100) (by norm_num) (by norm_num) (by norm_num)
        (by decide +kernel))
    simp only [thmKappa, pairL, thmL, thmD, hatApair, id, sum_range_succ, sum_range_zero, hu]
    norm_num
  · refine le_trans ?_
      (le_two_rpow (m := 1041000) (d := 1) (N := 1999) (K := 100) (by norm_num) (by norm_num) (by norm_num)
        (by decide +kernel))
    simp only [thmKappa, pairL, thmL, thmD, hatApair, id, sum_range_succ, sum_range_zero, hu]
    norm_num

omit [Prec_gt_0 p] in
/-- Table IV for ADDF: `κ ≤ 2^{6.46}` on `H(1)` and `κ ≤ 2^{10.57}` on `H(2)` -/
theorem kappa8_addf (hp : p = 53) :
    thmKappa p 8 (addfL p 8 1) 0 ≤ (2 : ℝ) ^ (6.46 : ℝ) ∧ thmKappa p 8 (addfL p 8 2) 0 ≤ (2 : ℝ) ^ (10.57 : ℝ) := by
  have hu := u_53 p hp
  constructor
  · refine le_trans ?_
      (le_two_rpow (m := 8802) (d := 100) (N := 646) (K := 100) (by norm_num) (by norm_num) (by norm_num)
        (by decide +kernel))
    simp only [thmKappa, addfL, sum_range_succ, sum_range_zero, hu]
    norm_num
  · refine le_trans ?_
      (le_two_rpow (m := 1520) (d := 1) (N := 1057) (K := 100) (by norm_num) (by norm_num) (by norm_num)
        (by decide +kernel))
    simp only [thmKappa, addfL, sum_range_succ, sum_range_zero, hu]
    norm_num

/-- Table IV's MUL row on `H(2)`: `|ab - x| ≤ 2^{-424}|ab| + 2^{-439.07}|a_0b_0|` -/
theorem table4_mul (hp : p = 53) (a b : ℕ → ℝ) (ha : ∀ i < 8, F p (a i)) (hb : ∀ j < 8, F p (b j))
    (hHa : Htheta p 8 2 a) (hHb : Htheta p 8 2 b) :
    |(∑ i ∈ range 8, a i) * (∑ j ∈ range 8, b j) - (mulOp p 8 a b).sum| ≤
      (2 : ℝ) ^ (-424 : ℝ) * |(∑ i ∈ range 8, a i) * (∑ j ∈ range 8, b j)| +
        (2 : ℝ) ^ (-439.07 : ℝ) * |a 0 * b 0| := by
  have hu := u_53 p hp
  have h := thm15_mul p 8 (by rw [hp]; norm_num) (by norm_num) (by rw [hu]; norm_num) 2 (by norm_num) a b ha hb hHa hHb
  have hk := kappa_u9 p hp (kappa8_mul p hp).2
  rw [show (37.93 : ℝ) - 477 = -439.07 by norm_num] at hk
  rw [u8_53 p hp] at h
  refine h.trans (add_le_add le_rfl ?_)
  exact mul_le_mul_of_nonneg_right hk (abs_nonneg _)

/-- Table IV's ADD row on `H(2)`: `|a + b - x| ≤ 2^{-424}|a + b| + 2^{-457.01}(|a_0| + |b_0|)` -/
theorem table4_add (hp : p = 53) (a b : ℕ → ℝ) (ha : ∀ i < 8, F p (a i)) (hb : ∀ j < 8, F p (b j))
    (hHa : Htheta p 8 2 a) (hHb : Htheta p 8 2 b) :
    |(∑ i ∈ range 8, a i + ∑ i ∈ range 8, b i) - (addOp p 8 a b).sum| ≤
      (2 : ℝ) ^ (-424 : ℝ) * |∑ i ∈ range 8, a i + ∑ i ∈ range 8, b i| +
        (2 : ℝ) ^ (-457.01 : ℝ) * (|a 0| + |b 0|) := by
  have hu := u_53 p hp
  have h := thm15_add p 8 (by rw [hp]; norm_num) (by norm_num) (by rw [hu]; norm_num) 2 (by norm_num) a b ha hb hHa hHb
  have hk := kappa_u9 p hp (kappa8_pair p hp).2
  rw [show (19.99 : ℝ) - 477 = -457.01 by norm_num] at hk
  rw [u8_53 p hp] at h
  refine h.trans (add_le_add le_rfl ?_)
  exact mul_le_mul_of_nonneg_right hk (by positivity)

/-- Table IV's MULF row on `H(2)`: `|ab - x| ≤ 2^{-424}|ab| + 2^{-457.01}|a_0b|` -/
theorem table4_mulf (hp : p = 53) (a : ℕ → ℝ) (b : ℝ) (ha : ∀ i < 8, F p (a i)) (hb : F p b)
    (hHa : Htheta p 8 2 a) :
    |(∑ i ∈ range 8, a i) * b - (mulfOp p 8 a b).sum| ≤
      (2 : ℝ) ^ (-424 : ℝ) * |(∑ i ∈ range 8, a i) * b| + (2 : ℝ) ^ (-457.01 : ℝ) * |a 0 * b| := by
  have hu := u_53 p hp
  have h := thm15_mulf p 8 (by rw [hp]; norm_num) (by norm_num) (by rw [hu]; norm_num) 2 (by norm_num) a b ha hb hHa
  have hk := kappa_u9 p hp (kappa8_pair p hp).2
  rw [show (19.99 : ℝ) - 477 = -457.01 by norm_num] at hk
  rw [u8_53 p hp] at h
  refine h.trans (add_le_add le_rfl ?_)
  exact mul_le_mul_of_nonneg_right hk (abs_nonneg _)

/-- Table IV's ADDF row on `H(2)`: `|a + b - x| ≤ 2^{-424}|a + b| + 2^{-466.43}(|a_0| + |b|)` -/
theorem table4_addf (hp : p = 53) (a : ℕ → ℝ) (b : ℝ) (ha : ∀ i < 8, F p (a i)) (hb : F p b)
    (hHa : Htheta p 8 2 a) :
    |(∑ i ∈ range 8, a i + b) - (addfOp p 8 a b).sum| ≤
      (2 : ℝ) ^ (-424 : ℝ) * |∑ i ∈ range 8, a i + b| + (2 : ℝ) ^ (-466.43 : ℝ) * (|a 0| + |b|) := by
  have h := thm15_addf p 8 (by rw [hp]; norm_num) (by norm_num) 2 (by norm_num) a b ha hb hHa
  have hk := kappa_u9 p hp (kappa8_addf p hp).2
  rw [show (10.57 : ℝ) - 477 = -466.43 by norm_num] at hk
  rw [u8_53 p hp] at h
  refine h.trans (add_le_add le_rfl ?_)
  exact mul_le_mul_of_nonneg_right hk (by positivity)

end ExpansionBounds
