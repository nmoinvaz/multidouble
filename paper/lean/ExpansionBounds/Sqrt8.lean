import ExpansionBounds.SqrtDD8Delta

/-!
# Theorem 21 (`thm:t7`) at `n = 8` and `p = 53`: `δ_4`

SQRT_{8,4}'s `δ_4` evaluated by the kernel on its rational mirror, as `sqrt_consts.py` computes it:
`δ_4 ≤ 3.0000319u^8` on `H(2)` and `3.0000198u^8` on `H(1)`, the bounds of SQRT^DD (Theorem 22). On `H(2)` the error
before the last step is `E_3 ≤ 1.12·10^6u^8`, and the bound exceeds `3u^8` by at most `2^{-14.93}u^8`, as the remark
after Theorem 22 says.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ)

/-- `2^x ≤ m` from `2^{Kx} ≤ m^K`, checked in `ℕ` -/
theorem two_rpow_le {m N K : ℕ} {x : ℝ} (hK : K ≠ 0) (hN : x * K = N) (h : 2 ^ N ≤ m ^ K) : (2 : ℝ) ^ x ≤ m := by
  rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) hK, ← Real.rpow_natCast ((2 : ℝ) ^ x) K,
    ← Real.rpow_mul (by norm_num), hN, Real.rpow_natCast]
  exact_mod_cast h

/-- `(E_k, π^{(k)})` of SQRT_{n,J} on `H(θ)` at `p = 53`: `E_k` is the cast of its rational mirror -/
theorem sqrtBk_53 (hp : p = 53) (n : ℕ) (θ : ℚ) (k : ℕ) :
    (sqrtBk p n (θ * u p) k).1 =
      (((sqrtBkQ (1 / 9007199254740992) n (θ * (1 / 9007199254740992)) k).1 : ℚ) : ℝ) := by
  have h := u_53_rat p hp
  have hρ : ((θ * (1 / 9007199254740992) : ℚ) : ℝ) = θ * u p := by
    rw [← h]
    exact Rat.cast_mul _ _
  rw [(cast_sqrtBk p n h (θ * (1 / 9007199254740992)) k).1, hρ]

/-- `δ_J` on `H(θ)` at `p = 53` is the cast of its rational mirror -/
theorem sqrtDelta_53 (hp : p = 53) (n : ℕ) (θ : ℚ) (J : ℕ) :
    sqrtDelta p n (θ * u p) J =
      ((sqrtDeltaQ (1 / 9007199254740992) n (θ * (1 / 9007199254740992)) J : ℚ) : ℝ) := by
  have h := u_53_rat p hp
  have hρ : ((θ * (1 / 9007199254740992) : ℚ) : ℝ) = θ * u p := by
    rw [← h]
    exact Rat.cast_mul _ _
  rw [cast_sqrtDelta p n h, hρ]

set_option maxHeartbeats 4000000 in
/-- Theorem 21 at `n = 8` and `J = 4`: `δ_4 ≤ 3.0000319u^8` on `H(2)` and `3.0000198u^8` on `H(1)` -/
theorem sqrtDelta8 (hp : p = 53) :
    sqrtDelta p 8 (2 * u p) 4 ≤ 3.0000319 * u p ^ 8 ∧ sqrtDelta p 8 (1 * u p) 4 ≤ 3.0000198 * u p ^ 8 := by
  constructor
  · have hc := sqrtDelta_53 p hp 8 2 4
    rw [Rat.cast_ofNat] at hc
    have hq : sqrtDeltaQ (1 / 9007199254740992) 8 (2 * (1 / 9007199254740992)) 4 ≤
        30000319 / 10000000 * (1 / 9007199254740992) ^ 8 := by decide +kernel
    rw [hc, ← u_53_rat p hp, show (3.0000319 : ℝ) = ((30000319 / 10000000 : ℚ) : ℝ) by norm_num]
    exact_mod_cast hq
  · have hc := sqrtDelta_53 p hp 8 1 4
    rw [Rat.cast_one] at hc
    have hq : sqrtDeltaQ (1 / 9007199254740992) 8 (1 * (1 / 9007199254740992)) 4 ≤
        30000198 / 10000000 * (1 / 9007199254740992) ^ 8 := by decide +kernel
    rw [hc, ← u_53_rat p hp, show (3.0000198 : ℝ) = ((30000198 / 10000000 : ℚ) : ℝ) by norm_num]
    exact_mod_cast hq

set_option maxHeartbeats 4000000 in
/-- the remark after Theorem 22: `E_3 ≤ 1.12·10^6u^8` for SQRT_{8,4} on `H(2)` -/
theorem sqrtE3_8 (hp : p = 53) : (sqrtBk p 8 (2 * u p) 3).1 ≤ 1120000 * u p ^ 8 := by
  have hc := sqrtBk_53 p hp 8 2 3
  rw [Rat.cast_ofNat] at hc
  have hq : (sqrtBkQ (1 / 9007199254740992) 8 (2 * (1 / 9007199254740992)) 3).1 ≤
      1120000 * (1 / 9007199254740992) ^ 8 := by decide +kernel
  rw [hc, ← u_53_rat p hp]
  exact_mod_cast hq

/-- the remark after Theorem 22: `δ_4` exceeds `3u^8` by at most `2^{-14.93}u^8` on `H(2)` -/
theorem sqrtDelta8_excess (hp : p = 53) : sqrtDelta p 8 (2 * u p) 4 ≤ (3 + (2 : ℝ) ^ (-14.93 : ℝ)) * u p ^ 8 := by
  have h2 : (2 : ℝ) ^ (14.93 : ℝ) ≤ (31347 : ℕ) :=
    two_rpow_le (N := 1493) (K := 100) (by norm_num) (by norm_num) (by decide +kernel)
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (14.93 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have h3 : (0.0000319 : ℝ) ≤ (2 : ℝ) ^ (-14.93 : ℝ) := by
    rw [Real.rpow_neg (by norm_num), le_inv_comm₀ (by norm_num) hpos]
    exact h2.trans (by norm_num)
  refine (sqrtDelta8 p hp).1.trans (mul_le_mul_of_nonneg_right ?_ (pow_nonneg (u_pos p).le 8))
  linarith

variable [Prec_gt_0 p]

/-- Theorem 21 at `n = 8`, `p = 53` and `J = 4`: SQRT_{8,4} of `x` on `H(2)` is within `3.0000319u^8√x` of `√x` -/
theorem sqrt8 (hp : p = 53) (x : ℕ → ℝ) (hx : ∀ i < 8, F p (x i)) (hH : Htheta p 8 2 x) (hx0 : 0 < x 0) :
    |Real.sqrt (∑ i ∈ range 8, x i) - (sqrtOp p 8 4 x).sum| ≤
      3.0000319 * u p ^ 8 * Real.sqrt (∑ i ∈ range 8, x i) := by
  have hu := u_53 p hp
  exact (thm21 p 8 (by rw [hp]; norm_num) (by norm_num) (by rw [hu]; norm_num) (θ := 2) (by norm_num)
    (by rw [hu]; norm_num) x hx hH hx0 4).trans
    (mul_le_mul_of_nonneg_right (sqrtDelta8 p hp).1 (Real.sqrt_nonneg _))

end ExpansionBounds
