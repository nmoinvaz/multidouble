import ExpansionBounds.Trig2.All
import ExpansionBounds.TrigN

/-!
# Theorem 35 at `n = 2` and `p = 53`: sine and cosine within `3.168701u^2`, tangent within `6.452138u^2`

The remark after Theorem 35 at `n = 2`: SIN and COS with the coefficients and series lengths of
`Trig2/Data.lean`, on `x` in `F`, on `H(2)` and with `|x_0| ≤ 2^52`, are within `3.168701u^2` of `sin x` and
`cos x`, relatively, plus `5E_π`, and TAN, for `x` at least `2^{2p-1074}` away from the nonzero multiples
of `π/2`, within `6.452138u^2 + 5E_π/|sin x cos x|` of `tan x`, relatively. The kernel checks the tables,
`κ_DIV` on the quotient's two ladders, the bounds below the last bucket and, in `Trig2/Run0.lean` on, every
run of buckets; `thm35_sincos_tab` and `thm35_tan_tab` do the rest. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

open Finset

theorem trig2_tab : trig2Tab.TabOk := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig2_tiny : trig2Tab.TinyOk trig2C := by decide +kernel

variable (p : ℤ) [Prec_gt_0 p]

/-- the remark after Theorem 35 at `n = 2`: the sine and the cosine are within `3.168701u^2` of `sin x` and
`cos x`, relatively, plus `5E_π` -/
theorem thm35_sincos_2 (hp : p = 53) (x : ℕ → ℝ) (hx : ∀ i < 2, F p (x i)) (hH : Htheta p 2 2 x)
    (hx0 : |x 0| ≤ 2 ^ 52) (es : ℝ → ℤ) :
    |∑ i ∈ range 2, sinN p 2 es trig2Tab.Ks trig2Tab.Kc trig2Tab.FsR trig2Tab.FcR x i -
          Real.sin (∑ i ∈ range 2, x i)| ≤
        3168701 / 1000000 * u p ^ 2 * |Real.sin (∑ i ∈ range 2, x i)| +
          5 * (|(redK p 2 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) ∧
      |∑ i ∈ range 2, cosN p 2 es trig2Tab.Ks trig2Tab.Kc trig2Tab.FsR trig2Tab.FcR x i -
          Real.cos (∑ i ∈ range 2, x i)| ≤
        3168701 / 1000000 * u p ^ 2 * |Real.cos (∑ i ∈ range 2, x i)| +
          5 * (|(redK p 2 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) := by
  have h := thm35_sincos_tab p trig2Tab trig2C (by decide) (by decide) ⟨_, _, rfl⟩ trig2_tab trig2_tiny
    trig2_all hp x hx hH hx0 es
  rw [show ((trig2C : ℚ) : ℝ) = 3168701 / 1000000 by unfold trig2C; norm_num] at h
  exact h

omit [Prec_gt_0 p] in
set_option maxHeartbeats 4000000 in
theorem trig2_kdiv : trig2Tab.KdivOk trig2Kd0 trig2Kd3 := by decide +kernel

omit [Prec_gt_0 p] in
set_option maxHeartbeats 4000000 in
theorem tan2_tiny : trig2Tab.TanTinyOk trig2Ct trig2Kd3 := by decide +kernel

/-- the remark after Theorem 35 at `n = 2`: for `x` at least `2^{2p-1074}` away from the nonzero multiples of `π/2`,
the tangent is within `6.452138u^2 + 5E_π/|sin x cos x|` of `tan x`, relatively -/
theorem thm35_tan_2 (hp : p = 53) (x : ℕ → ℝ) (hx : ∀ i < 2, F p (x i)) (hH : Htheta p 2 2 x)
    (hx0 : |x 0| ≤ 2 ^ 52) (es et : ℝ → ℤ)
    (hfar : redK p 2 x ≠ 0 →
      (2 : ℝ) ^ (p * (2 : ℕ) - 1074) ≤ |∑ i ∈ range 2, x i - redK p 2 x * (Real.pi / 2)|) :
    |∑ i ∈ range 2, tanN p 2 es et trig2Tab.Ks trig2Tab.Kc trig2Tab.FsR trig2Tab.FcR x i -
        Real.tan (∑ i ∈ range 2, x i)| ≤
      (6452138 / 1000000 * u p ^ 2 + 5 * (|(redK p 2 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) /
        |Real.sin (∑ i ∈ range 2, x i) * Real.cos (∑ i ∈ range 2, x i)|) * |Real.tan (∑ i ∈ range 2, x i)| := by
  have h := thm35_tan_tab p trig2Tab trig2Ct trig2Kd0 trig2Kd3 (by decide) (by decide) ⟨_, _, rfl⟩ trig2_tab
    trig2_kdiv tan2_tiny tan2_all hp x hx hH hx0 es et hfar
  rw [show ((trig2Ct : ℚ) : ℝ) = 6452138 / 1000000 by unfold trig2Ct; norm_num] at h
  exact h

end ExpansionBounds
