import ExpansionBounds.Div8
import ExpansionBounds.KappaN

/-!
# Theorem 19 (`thm:t6`) at `p = 53`: `κ_DIV u < 1` for `n ≤ 13`

`κ_DIV` on `H(2)` evaluated by the kernel on its rational mirror, as `div_consts.py` computes it, for each `n` from
`2` to `14`: `κ_DIV u < 1` for `n ≤ 13`, with `κ_DIV u ≤ 2^{-8.1}` at `n = 12` and `2^{-3.4}` at `n = 13`, and
`κ_DIV u > 1` at `n = 14`. So long division of `H(2)` operands errs by at most `2u^n|a/b|` up to thirteen parts.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ)

/-- `κ_DIV` on `H(2)` at `p = 53` is the cast of its rational mirror -/
theorem kdiv_two_53 (hp : p = 53) (n : ℕ) :
    kdiv p n (2 * u p) = ((kdivQ (1 / 9007199254740992) n (2 * (1 / 9007199254740992)) : ℚ) : ℝ) := by
  have h := kdiv_53 p hp n 2
  rwa [Rat.cast_ofNat] at h

set_option maxHeartbeats 4000000 in
/-- on `H(2)`, `κ_DIV u < 1` for `2 ≤ n ≤ 13` -/
theorem kdiv_u_lt_one (hp : p = 53) {n : ℕ} (h2 : 2 ≤ n) (h13 : n ≤ 13) : kdiv p n (2 * u p) * u p < 1 := by
  have key : ∀ m : ℕ,
      kdivQ (1 / 9007199254740992) m (2 * (1 / 9007199254740992)) * (1 / 9007199254740992) < 1 →
        kdiv p m (2 * u p) * u p < 1 := fun m hq => by
    rw [kdiv_two_53 p hp m, ← u_53_rat p hp]
    exact_mod_cast hq
  interval_cases n <;> exact key _ (by decide +kernel)

set_option maxHeartbeats 4000000 in
/-- on `H(2)`, `κ_DIV u ≤ 2^{-8.1}` at `n = 12` and `2^{-3.4}` at `n = 13`, and `κ_DIV u > 1` at `n = 14` -/
theorem kdiv_u_12_13_14 (hp : p = 53) :
    kdiv p 12 (2 * u p) * u p ≤ (2 : ℝ) ^ (-8.1 : ℝ) ∧ kdiv p 13 (2 * u p) * u p ≤ (2 : ℝ) ^ (-3.4 : ℝ) ∧
      1 < kdiv p 14 (2 * u p) * u p := by
  refine ⟨?_, ?_, ?_⟩
  · have hq : kdivQ (1 / 9007199254740992) 12 (2 * (1 / 9007199254740992)) ≤ 32130000000000 := by decide +kernel
    refine kappa_u_le p hp (m := 32130000000000) (d := 1) (N := 449) (K := 10) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel) ?_
    rw [kdiv_two_53 p hp 12, Nat.cast_one, div_one]
    exact_mod_cast hq
  · have hq : kdivQ (1 / 9007199254740992) 13 (2 * (1 / 9007199254740992)) ≤ 837000000000000 := by decide +kernel
    refine kappa_u_le p hp (m := 837000000000000) (d := 1) (N := 496) (K := 10) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel) ?_
    rw [kdiv_two_53 p hp 13, Nat.cast_one, div_one]
    exact_mod_cast hq
  · have hq : 1 < kdivQ (1 / 9007199254740992) 14 (2 * (1 / 9007199254740992)) * (1 / 9007199254740992) := by
      decide +kernel
    rw [kdiv_two_53 p hp 14, ← u_53_rat p hp]
    exact_mod_cast hq

variable [Prec_gt_0 p]

/-- Theorem 19 at `p = 53` for `2 ≤ n ≤ 13`: DIV of `H(2)` operands errs by at most `2u^n|a/b|` -/
theorem div_le_two (hp : p = 53) {n : ℕ} (h2 : 2 ≤ n) (h13 : n ≤ 13) (a b : ℕ → ℝ) (ha : ∀ i < n, F p (a i))
    (hb : ∀ i < n, F p (b i)) (haH : Htheta p n 2 a) (hbH : Htheta p n 2 b) (hb0 : b 0 ≠ 0) :
    |(∑ i ∈ range n, a i) / (∑ i ∈ range n, b i) - (divOp p n a b).sum| ≤
      2 * u p ^ n * |(∑ i ∈ range n, a i) / ∑ i ∈ range n, b i| := by
  have hu := u_53 p hp
  have hQ : ((2 * n - 1 : ℕ) : ℝ) * u p < 1 := by
    have h25 : ((2 * n - 1 : ℕ) : ℝ) ≤ 25 := by exact_mod_cast (by omega : 2 * n - 1 ≤ 25)
    rw [hu]
    linarith
  have h := thm19 p n (by rw [hp]; norm_num) (by omega) hQ (θ := 2) (by norm_num) (by rw [hu]; norm_num) a b ha hb
    haH hbH hb0
  have hk := kdiv_u_lt_one p hp h2 h13
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
  have hn0 : 0 ≤ u p ^ n := pow_nonneg (u_pos p).le n
  calc u p ^ n + kdiv p n (2 * u p) * u p ^ (n + 1) = u p ^ n * (1 + kdiv p n (2 * u p) * u p) := by ring
    _ ≤ u p ^ n * 2 := mul_le_mul_of_nonneg_left (by linarith) hn0
    _ = 2 * u p ^ n := by ring

end ExpansionBounds
