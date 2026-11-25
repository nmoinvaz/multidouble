import ExpansionBounds.Eval
import ExpansionBounds.KappaN

/-!
# Table III (`tab:dot`): Theorem 27 at `n = 8` and `p = 53`

Theorem 27's second term `c_K W` for terms on `H(2)`, evaluated in rational arithmetic as `acc_bound.py` computes it:
`c_K ≤ 2^{-14.9}u^8`, `2^{-14.2}u^8`, `2^{-10.5}u^8`, `2^{-4.7}u^8`, `2^{2.7}u^8`, `2^{10.9}u^8` and `2^{37.2}u^8` at
`K = 1`, `4`, `16`, `32`, `64`, `128` and `1024`. It is at most `u^8/8` for every `K ≤ 38` and above it at `K = 39`,
and at most `u^8` for every `K ≤ 50` and above it at `K = 51`. `Φ`, the bound of FINISH's last ADDF, is evaluated
once, at `K = 1024`, where it is at most `2^{-47}u^8`, by the kernel on its rational mirror (`Eval.lean`); it grows
with `K`, as `c_K` does, so the value serves every smaller `K`. Each power of two is bounded below through
`c^{10} ≤ 2^{10x}`.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ)

/-- `(n + 1)Ku < 1` at `n = 8` and `p = 53` for `K ≤ 1024` -/
theorem acc8_hK (hp : p = 53) {K : ℕ} (hK : K ≤ 1024) : (((8 : ℕ) : ℝ) + 1) * K * u p < 1 := by
  have hK' : (K : ℝ) ≤ 1024 := by exact_mod_cast hK
  rw [u_53 p hp]
  push_cast
  linarith

/-- `u^8/8 = 2^{-427}` at `p = 53` -/
theorem u8_div8_53 (hp : p = 53) : u p ^ 8 / 8 = (2 : ℝ) ^ (-427 : ℝ) := by
  rw [u8_53 p hp, show (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) by norm_num, ← Real.rpow_sub (by norm_num)]
  norm_num

/-- `c ≤ (m/d)u^9` and `m^K ≤ 2^{K(x + 53)}d^K` give `c ≤ 2^x u^8` at `p = 53` -/
theorem le_two_rpow_u8 (hp : p = 53) {c x : ℝ} {m d N K : ℕ} (hd : 0 < d) (hK : K ≠ 0) (hN : (x + 53) * K = N)
    (h : m ^ K ≤ 2 ^ N * d ^ K) (hc : c ≤ (m : ℝ) / d * u p ^ 9) : c ≤ (2 : ℝ) ^ x * u p ^ 8 := by
  have h1 := kappa_u_le p hp hd hK hN h (le_refl ((m : ℝ) / d))
  calc c ≤ (m : ℝ) / d * u p ^ 9 := hc
    _ = (m : ℝ) / d * u p * u p ^ 8 := by ring
    _ ≤ (2 : ℝ) ^ x * u p ^ 8 := mul_le_mul_of_nonneg_right h1 (pow_nonneg (u_pos p).le 8)

/-- `Φ ≤ 2^{-47}u^8` at `K = 1024` on `H(2)`: the kernel evaluates the rational mirror `accPhiQ` -/
theorem accPhi8_1024 (hp : p = 53) : accPhi p 8 2 1024 ≤ u p ^ 8 / 2 ^ 47 := by
  have h := u_53_rat p hp
  have hq : accPhiQ (1 / 9007199254740992) 8 2 1024 ≤ (1 / 9007199254740992) ^ 8 / 2 ^ 47 := by decide +kernel
  have hc := cast_accPhi p 8 h 2 1024
  push_cast at hc
  rw [← h, ← hc]
  exact_mod_cast hq

/-- `Φ ≤ 2^{-47}u^8` for `K ≤ 1024` on `H(2)`, as `Φ` grows with `K` -/
theorem accPhi8 (hp : p = 53) {K : ℕ} (hK : K ≤ 1024) : accPhi p 8 2 K ≤ u p ^ 8 / 2 ^ 47 :=
  (accPhi_mono p 8 (by norm_num) hK (acc8_hK p hp le_rfl)).trans (accPhi8_1024 p hp)

/-- `c_K ≤ (1 + u^8)(Ē_lev + E_prod) + 2^{-47}u^8` for `K ≤ 1024` -/
theorem accC8_le (hp : p = 53) {K : ℕ} (hK : K ≤ 1024) :
    accC p 8 2 K ≤ (1 + u p ^ 8) * accLevProd p 8 2 K + u p ^ 8 / 2 ^ 47 := by
  unfold accC
  exact add_le_add le_rfl (accPhi8 p hp hK)

/-- `(1 + u^8)(Ē_lev + E_prod) ≤ c_K` for `K ≤ 1024` -/
theorem accC8_ge (hp : p = 53) {K : ℕ} (hK : K ≤ 1024) : (1 + u p ^ 8) * accLevProd p 8 2 K ≤ accC p 8 2 K := by
  unfold accC
  exact le_add_of_nonneg_right (accPhi_nonneg p 8 (by norm_num) (acc8_hK p hp hK))

/-- Table III: `c_K ≤ 2^{-14.9}u^8`, `2^{-14.2}u^8`, `2^{-10.5}u^8`, `2^{-4.7}u^8`, `2^{2.7}u^8`, `2^{10.9}u^8` and
`2^{37.2}u^8` at `K = 1`, `4`, `16`, `32`, `64`, `128` and `1024` -/
theorem table3 (hp : p = 53) :
    accC p 8 2 1 ≤ (2 : ℝ) ^ (-14.9 : ℝ) * u p ^ 8 ∧ accC p 8 2 4 ≤ (2 : ℝ) ^ (-14.2 : ℝ) * u p ^ 8 ∧
      accC p 8 2 16 ≤ (2 : ℝ) ^ (-10.5 : ℝ) * u p ^ 8 ∧ accC p 8 2 32 ≤ (2 : ℝ) ^ (-4.7 : ℝ) * u p ^ 8 ∧
      accC p 8 2 64 ≤ (2 : ℝ) ^ (2.7 : ℝ) * u p ^ 8 ∧ accC p 8 2 128 ≤ (2 : ℝ) ^ (10.9 : ℝ) * u p ^ 8 ∧
      accC p 8 2 1024 ≤ (2 : ℝ) ^ (37.2 : ℝ) * u p ^ 8 := by
  have hu := u_53 p hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine le_two_rpow_u8 p hp (m := 290900000000) (d := 1) (N := 381) (K := 10) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel) ((accC8_le p hp (by norm_num)).trans ?_)
    norm_num [accLevProd, accE, accGamma, accTau, mulL, thmL, thmD, hatAmul, mulT, thmDelta, rise, hu,
      sum_Ico_eq_sum_range, sum_range_succ, prod_range_succ, max_def, Nat.choose]
  · refine le_two_rpow_u8 p hp (m := 452100000000) (d := 1) (N := 388) (K := 10) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel) ((accC8_le p hp (by norm_num)).trans ?_)
    norm_num [accLevProd, accE, accGamma, accTau, mulL, thmL, thmD, hatAmul, mulT, thmDelta, rise, hu,
      sum_Ico_eq_sum_range, sum_range_succ, prod_range_succ, max_def, Nat.choose]
  · refine le_two_rpow_u8 p hp (m := 6020000000000) (d := 1) (N := 425) (K := 10) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel) ((accC8_le p hp (by norm_num)).trans ?_)
    norm_num [accLevProd, accE, accGamma, accTau, mulL, thmL, thmD, hatAmul, mulT, thmDelta, rise, hu,
      sum_Ico_eq_sum_range, sum_range_succ, prod_range_succ, max_def, Nat.choose]
  · refine le_two_rpow_u8 p hp (m := 329100000000000) (d := 1) (N := 483) (K := 10) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel) ((accC8_le p hp (by norm_num)).trans ?_)
    norm_num [accLevProd, accE, accGamma, accTau, mulL, thmL, thmD, hatAmul, mulT, thmDelta, rise, hu,
      sum_Ico_eq_sum_range, sum_range_succ, prod_range_succ, max_def, Nat.choose]
  · refine le_two_rpow_u8 p hp (m := 57860000000000000) (d := 1) (N := 557) (K := 10) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel) ((accC8_le p hp (by norm_num)).trans ?_)
    norm_num [accLevProd, accE, accGamma, accTau, mulL, thmL, thmD, hatAmul, mulT, thmDelta, rise, hu,
      sum_Ico_eq_sum_range, sum_range_succ, prod_range_succ, max_def, Nat.choose]
  · refine le_two_rpow_u8 p hp (m := 16890000000000000000) (d := 1) (N := 639) (K := 10) (by norm_num)
      (by norm_num) (by norm_num) (by decide +kernel) ((accC8_le p hp (by norm_num)).trans ?_)
    norm_num [accLevProd, accE, accGamma, accTau, mulL, thmL, thmD, hatAmul, mulT, thmDelta, rise, hu,
      sum_Ico_eq_sum_range, sum_range_succ, prod_range_succ, max_def, Nat.choose]
  · refine le_two_rpow_u8 p hp (m := 1340000000000000000000000000) (d := 1) (N := 902) (K := 10) (by norm_num)
      (by norm_num) (by norm_num) (by decide +kernel) ((accC8_le p hp (by norm_num)).trans ?_)
    norm_num [accLevProd, accE, accGamma, accTau, mulL, thmL, thmD, hatAmul, mulT, thmDelta, rise, hu,
      sum_Ico_eq_sum_range, sum_range_succ, prod_range_succ, max_def, Nat.choose]

/-- the second term is at most `u^8 W/8` for `K ≤ 38` -/
theorem accC8_eighth (hp : p = 53) {K : ℕ} (hK : K ≤ 38) : accC p 8 2 K ≤ u p ^ 8 / 8 := by
  have hu := u_53 p hp
  refine (accC_mono p 8 (by norm_num) hK (acc8_hK p hp (by norm_num))).trans
    ((accC8_le p hp (by norm_num)).trans ?_)
  norm_num [accLevProd, accE, accGamma, accTau, mulL, thmL, thmD, hatAmul, mulT, thmDelta, rise, hu,
    sum_Ico_eq_sum_range, sum_range_succ, prod_range_succ, max_def, Nat.choose]

/-- the second term is at most `u^8 W` for `K ≤ 50` -/
theorem accC8_one (hp : p = 53) {K : ℕ} (hK : K ≤ 50) : accC p 8 2 K ≤ u p ^ 8 := by
  have hu := u_53 p hp
  refine (accC_mono p 8 (by norm_num) hK (acc8_hK p hp (by norm_num))).trans
    ((accC8_le p hp (by norm_num)).trans ?_)
  norm_num [accLevProd, accE, accGamma, accTau, mulL, thmL, thmD, hatAmul, mulT, thmDelta, rise, hu,
    sum_Ico_eq_sum_range, sum_range_succ, prod_range_succ, max_def, Nat.choose]

/-- `38` and `50` are the largest such `K`: the second term exceeds `u^8 W/8` at `K = 39` and `u^8 W` at `K = 51` -/
theorem accC8_sharp (hp : p = 53) : u p ^ 8 / 8 < accC p 8 2 39 ∧ u p ^ 8 < accC p 8 2 51 := by
  have hu := u_53 p hp
  constructor
  · refine lt_of_lt_of_le ?_ (accC8_ge p hp (by norm_num))
    norm_num [accLevProd, accE, accGamma, accTau, mulL, thmL, thmD, hatAmul, mulT, thmDelta, rise, hu,
      sum_Ico_eq_sum_range, sum_range_succ, prod_range_succ, max_def, Nat.choose]
  · refine lt_of_lt_of_le ?_ (accC8_ge p hp (by norm_num))
    norm_num [accLevProd, accE, accGamma, accTau, mulL, thmL, thmD, hatAmul, mulT, thmDelta, rise, hu,
      sum_Ico_eq_sum_range, sum_range_succ, prod_range_succ, max_def, Nat.choose]

variable [Prec_gt_0 p]

/-- Theorem 27 at `n = 8`, `p = 53`: `K ≤ 50` terms, each ADDPROD or ADDX of operands on `H(2)`, then FINISH, give
`|Z - x| ≤ 2^{-424}(|Z| + W)`, and `K ≤ 38` terms `|Z - x| ≤ 2^{-424}|Z| + 2^{-427}W` -/
theorem acc8 (hp : p = 53) (K : ℕ) (hK1 : 1 ≤ K) (hK : K ≤ 50) (prod : ℕ → Bool) (a b : ℕ → ℕ → ℝ)
    (ha : ∀ k ∈ Icc 1 K, ∀ i < 8, F p (a k i)) (hb : ∀ k ∈ Icc 1 K, prod k = true → ∀ j < 8, F p (b k j))
    (hHa : ∀ k ∈ Icc 1 K, Htheta p 8 2 (a k)) (hHb : ∀ k ∈ Icc 1 K, prod k = true → Htheta p 8 2 (b k)) :
    |accZ 8 prod a b K - ∑ i ∈ range 8, finishR p 8 (accLev p 8 prod a b K) 8 i| ≤
        (2 : ℝ) ^ (-424 : ℝ) * (|accZ 8 prod a b K| + ∑ j ∈ Icc 1 K, accMu prod a b j) ∧
      (K ≤ 38 → |accZ 8 prod a b K - ∑ i ∈ range 8, finishR p 8 (accLev p 8 prod a b K) 8 i| ≤
        (2 : ℝ) ^ (-424 : ℝ) * |accZ 8 prod a b K| + (2 : ℝ) ^ (-427 : ℝ) * ∑ j ∈ Icc 1 K, accMu prod a b j) := by
  have hu := u_53 p hp
  have h := thm27_scaled p 8 (by rw [hp]; norm_num) (by norm_num) (by rw [hu]; norm_num) 2 (by norm_num) K hK1
    (acc8_hK p hp (by omega)) prod a b ha hb hHa hHb
  have hW : 0 ≤ ∑ j ∈ Icc 1 K, accMu prod a b j :=
    sum_nonneg fun k _ => by unfold accMu; split_ifs <;> exact abs_nonneg _
  refine ⟨?_, fun hK38 => ?_⟩
  · rw [← u8_53 p hp]
    have h1 := mul_le_mul_of_nonneg_right (accC8_one p hp hK) hW
    linarith
  · rw [← u8_53 p hp, ← u8_div8_53 p hp]
    have h1 := mul_le_mul_of_nonneg_right (accC8_eighth p hp hK38) hW
    linarith

end ExpansionBounds
