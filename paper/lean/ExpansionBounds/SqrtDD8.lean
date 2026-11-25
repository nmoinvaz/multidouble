import ExpansionBounds.SqrtEval
import ExpansionBounds.Kappa8

/-!
# Theorem 22 (`thm:t8`) at `n = 8` and `p = 53`: the start

SQRT^DD's start constants evaluated in rational arithmetic, as `sqrt_consts.py` computes them: the double-word start
is within `E_0 ≤ 22.125u² + 72u³` on `H(2)` and `19.125u² + 58u³` on `H(1)`, and the second-order step leaves
`E_1 ≤ 2^{-303}` on both. The kernel evaluates `E_1` on its rational mirror `ddE1Q` (`SqrtEval.lean`).
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ)

/-- `u^5/2^{38} = 2^{-303}` at `p = 53` -/
theorem u5_div_two38 (hp : p = 53) : u p ^ 5 / 2 ^ 38 = (2 : ℝ) ^ (-303 : ℤ) := by
  rw [u_53 p hp, zpow_neg, show (303 : ℤ) = ((53 * 5 + 38 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_add, pow_mul]
  norm_num

/-- Theorem 22 at `n = 8`: `E_0 ≤ 22.125u² + 72u³` on `H(2)` and `E_0 ≤ 19.125u² + 58u³` on `H(1)` -/
theorem ddE0_8 (hp : p = 53) :
    ddE0 p (2 * u p) ≤ 22.125 * u p ^ 2 + 72 * u p ^ 3 ∧ ddE0 p (1 * u p) ≤ 19.125 * u p ^ 2 + 58 * u p ^ 3 := by
  have hu := u_53 p hp
  constructor <;> norm_num [ddE0, ddEta1, ddEta2, ddEta3, hu, max_def]

/-- `E_1` of SQRT^DD on `H(θ)` at `p = 53` is the cast of its rational mirror -/
theorem ddE1_53 (hp : p = 53) (n : ℕ) (θ : ℚ) :
    (sqrtB2 p n (fun i => abar ((θ : ℝ) * u p) i / 2) (ddE0 p (θ * u p)) (ddPi0 p (θ * u p))).1 =
      ((ddE1Q (1 / 9007199254740992) n (θ * (1 / 9007199254740992)) : ℚ) : ℝ) := by
  have h := u_53_rat p hp
  have hρ : ((θ * (1 / 9007199254740992) : ℚ) : ℝ) = θ * u p := by
    rw [← h]
    exact Rat.cast_mul _ _
  rw [cast_ddE1 p n h, hρ]

/-- Theorem 22 at `n = 8`: the second-order step leaves `E_1 ≤ 2^{-303}` on `H(2)` -/
theorem ddE1_8_two (hp : p = 53) :
    (sqrtB2 p 8 (fun i => abar (2 * u p) i / 2) (ddE0 p (2 * u p)) (ddPi0 p (2 * u p))).1 ≤ (2 : ℝ) ^ (-303 : ℤ) := by
  have hc := ddE1_53 p hp 8 2
  rw [Rat.cast_ofNat] at hc
  have hq : ddE1Q (1 / 9007199254740992) 8 (2 * (1 / 9007199254740992)) ≤ (1 / 9007199254740992) ^ 5 / 2 ^ 38 := by
    decide +kernel
  rw [← u5_div_two38 p hp, hc, ← u_53_rat p hp]
  exact_mod_cast hq

/-- Theorem 22 at `n = 8`: the second-order step leaves `E_1 ≤ 2^{-303}` on `H(1)` -/
theorem ddE1_8_one (hp : p = 53) :
    (sqrtB2 p 8 (fun i => abar (1 * u p) i / 2) (ddE0 p (1 * u p)) (ddPi0 p (1 * u p))).1 ≤ (2 : ℝ) ^ (-303 : ℤ) := by
  have hc := ddE1_53 p hp 8 1
  rw [Rat.cast_one] at hc
  have hq : ddE1Q (1 / 9007199254740992) 8 (1 * (1 / 9007199254740992)) ≤ (1 / 9007199254740992) ^ 5 / 2 ^ 38 := by
    decide +kernel
  rw [← u5_div_two38 p hp, hc, ← u_53_rat p hp]
  exact_mod_cast hq

end ExpansionBounds
