import ExpansionBounds.SqrtDD
import ExpansionBounds.Cor18

/-!
# Theorem 22 (`thm:t8`) at `n = 8` and `p = 53`: the start

SQRT^DD's start constants evaluated in rational arithmetic, as `sqrt_consts.py` computes them: the double-word start
is within `E_0 ≤ 22.125u² + 72u³` on `H(2)` and `19.125u² + 58u³` on `H(1)`, and the second-order step leaves
`E_1 ≤ 2^{-303}` on both. The step's six `G` bounds are evaluated once each through simp's cache.
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

set_option maxHeartbeats 20000000 in
/-- Theorem 22 at `n = 8`: the second-order step leaves `E_1 ≤ 2^{-303}` on `H(2)` -/
theorem ddE1_8_two (hp : p = 53) :
    (sqrtB2 p 8 (fun i => abar (2 * u p) i / 2) (ddE0 p (2 * u p)) (ddPi0 p (2 * u p))).1 ≤ (2 : ℝ) ^ (-303 : ℤ) := by
  have hu := u_53 p hp
  rw [← u5_div_two38 p hp]
  norm_num (config := { maxSteps := 20000000 }) [sqrtB2, sqrtEm, sqrtEg, sqrtPg, sqrtZc, sqrtL0, sqrtEc, sqrtChi,
    ddE0, ddEta1, ddEta2, ddEta3, ddPi0, abar, GmulE, GmulP, GaddE, GaddP, GaddfE', GaddfP', gErr, gParts, mulX, mulR,
    mulDelta, mulA, mulP, mulT, levX, levD, pairX, pairR, pairA, addfX, addfEps, Vb, sigmaX, us, id, hu,
    ← Finset.Ico_add_one_add_one_eq_Ioc, sum_Ico_eq_sum_range, sum_range_succ, min_def, max_def]

set_option maxHeartbeats 20000000 in
/-- Theorem 22 at `n = 8`: the second-order step leaves `E_1 ≤ 2^{-303}` on `H(1)` -/
theorem ddE1_8_one (hp : p = 53) :
    (sqrtB2 p 8 (fun i => abar (1 * u p) i / 2) (ddE0 p (1 * u p)) (ddPi0 p (1 * u p))).1 ≤ (2 : ℝ) ^ (-303 : ℤ) := by
  have hu := u_53 p hp
  rw [← u5_div_two38 p hp]
  norm_num (config := { maxSteps := 20000000 }) [sqrtB2, sqrtEm, sqrtEg, sqrtPg, sqrtZc, sqrtL0, sqrtEc, sqrtChi,
    ddE0, ddEta1, ddEta2, ddEta3, ddPi0, abar, GmulE, GmulP, GaddE, GaddP, GaddfE', GaddfP', gErr, gParts, mulX, mulR,
    mulDelta, mulA, mulP, mulT, levX, levD, pairX, pairR, pairA, addfX, addfEps, Vb, sigmaX, us, id, hu,
    ← Finset.Ico_add_one_add_one_eq_Ioc, sum_Ico_eq_sum_range, sum_range_succ, min_def, max_def]

end ExpansionBounds
