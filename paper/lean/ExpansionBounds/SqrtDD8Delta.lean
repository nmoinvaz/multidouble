import ExpansionBounds.SqrtDD8

/-!
# Theorem 22 (`thm:t8`) at `n = 8` and `p = 53`: `δ^DD`

SQRT^DD's `δ^DD` evaluated in rational arithmetic, as `sqrt_consts.py` computes it: `δ^DD ≤ 3.0000319u^8` on `H(2)`
and `3.0000198u^8` on `H(1)`, so SQRT^DD of `H(2)` operands is within `3.0000319u^8√x`. The second-order step, one
step of SQRT_{n,J} and the final `G_MUL` take about 37 minutes per `θ`, so `ExpansionBounds.lean` does not import this
module: `lake build ExpansionBounds.SqrtDD8Delta` checks it.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) [Prec_gt_0 p]

omit [Prec_gt_0 p] in
set_option maxHeartbeats 0 in
/-- Theorem 22 at `n = 8` on `H(2)`: `δ^DD ≤ 3.0000319u^8` -/
theorem ddDelta8_two (hp : p = 53) : ddDelta p 8 (2 * u p) ≤ 3.0000319 * u p ^ 8 := by
  have hu := u_53 p hp
  norm_num (config := { maxSteps := 40000000 }) [ddDelta, sqrtB, sqrtB2, sqrtEm, sqrtEg, sqrtPg, sqrtZc, sqrtL0,
    sqrtEc, sqrtChi, ddE0, ddEta1, ddEta2, ddEta3, ddPi0, abar, GmulE, GmulP, GaddE, GaddP, GaddfE', GaddfP', gErr,
    gParts, mulX, mulR, mulDelta, mulA, mulP, mulT, levX, levD, pairX, pairR, pairA, addfX, addfEps, Vb, sigmaX, us,
    id, hu, ← Finset.Ico_add_one_add_one_eq_Ioc, sum_Ico_eq_sum_range, sum_range_succ, min_def, max_def]

omit [Prec_gt_0 p] in
set_option maxHeartbeats 0 in
/-- Theorem 22 at `n = 8` on `H(1)`: `δ^DD ≤ 3.0000198u^8` -/
theorem ddDelta8_one (hp : p = 53) : ddDelta p 8 (1 * u p) ≤ 3.0000198 * u p ^ 8 := by
  have hu := u_53 p hp
  norm_num (config := { maxSteps := 40000000 }) [ddDelta, sqrtB, sqrtB2, sqrtEm, sqrtEg, sqrtPg, sqrtZc, sqrtL0,
    sqrtEc, sqrtChi, ddE0, ddEta1, ddEta2, ddEta3, ddPi0, abar, GmulE, GmulP, GaddE, GaddP, GaddfE', GaddfP', gErr,
    gParts, mulX, mulR, mulDelta, mulA, mulP, mulT, levX, levD, pairX, pairR, pairA, addfX, addfEps, Vb, sigmaX, us,
    id, hu, ← Finset.Ico_add_one_add_one_eq_Ioc, sum_Ico_eq_sum_range, sum_range_succ, min_def, max_def]

/-- Theorem 22 at `n = 8`, `p = 53`: SQRT^DD of `x` on `H(2)`, from a double-word start within the published bounds,
is within `3.0000319u^8√x` of `√x` -/
theorem sqrtdd8 (hp : p = 53) (x : ℕ → ℝ) (hx : ∀ i < 8, F p (x i)) (hH : Htheta p 8 2 x) (hx0 : 0 < x 0)
    (v r0 r1 : ℝ) (hr0 : F p r0) (hr1 : F p r1)
    (hv : |v - Real.sqrt (sqrtA p x 0 + sqrtA p x 1)| ≤ ddEta1 p * Real.sqrt (sqrtA p x 0 + sqrtA p x 1))
    (hrv : |(r0 + r1) * v - 1| ≤ ddEta2 p) (hr01 : |r1| ≤ u p * |r0|) :
    |Real.sqrt (∑ i ∈ range 8, x i) - (sqrtDDOp p 8 x r0 r1).sum| ≤
      3.0000319 * u p ^ 8 * Real.sqrt (∑ i ∈ range 8, x i) := by
  have hu := u_53 p hp
  exact (thm22 p 8 (by rw [hp]; norm_num) (by norm_num) (by rw [hu]; norm_num) (θ := 2) (by norm_num)
    (by rw [hu]; norm_num) x hx hH hx0 v r0 r1 hr0 hr1 hv hrv hr01).trans
    (mul_le_mul_of_nonneg_right (ddDelta8_two p hp) (Real.sqrt_nonneg _))

end ExpansionBounds
