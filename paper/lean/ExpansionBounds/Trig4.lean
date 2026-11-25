import ExpansionBounds.Trig4.All
import ExpansionBounds.TrigN

/-!
# Theorem 35 at `n = 4` and `p = 53`: the sine and the cosine within `3.164155u^4`, the tangent within `6.426155u^4`

The remark after Theorem 35 at `n = 4`: SIN and COS with the coefficients and series lengths of
`Trig4/Data.lean`, on `x` in `F`, on `H(2)` and with `|x_0| ≤ 2^52`, are within `3.164155u^4` of `sin x` and
`cos x`, relatively, plus `5E_π`, and TAN, for `x` at least `2^{4p-1074}` away from the nonzero multiples
of `π/2`, within `6.426155u^4 + 5E_π/|sin x cos x|` of `tan x`, relatively. The kernel checks the tables,
`κ_DIV` on the quotient's two ladders, the bounds below the last bucket and, in `Trig4/Run0.lean` on, every
run of buckets; `thm35_sincos_tab` and `thm35_tan_tab` do the rest. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

open Finset

theorem trig4_tab : trig4Tab.TabOk := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig4_tiny : trig4Tab.TinyOk trig4C := by decide +kernel

variable (p : ℤ) [Prec_gt_0 p]

/-- the remark after Theorem 35 at `n = 4`: the sine and the cosine are within `3.164155u^4` of `sin x` and `cos x`,
relatively, plus `5E_π` -/
theorem thm35_sincos_4 (hp : p = 53) (x : ℕ → ℝ) (hx : ∀ i < 4, F p (x i)) (hH : Htheta p 4 2 x)
    (hx0 : |x 0| ≤ 2 ^ 52) (es : ℝ → ℤ) :
    |∑ i ∈ range 4, sinN p 4 es trig4Tab.Ks trig4Tab.Kc trig4Tab.FsR trig4Tab.FcR x i -
          Real.sin (∑ i ∈ range 4, x i)| ≤
        3164155 / 1000000 * u p ^ 4 * |Real.sin (∑ i ∈ range 4, x i)| +
          5 * (|(redK p 4 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) ∧
      |∑ i ∈ range 4, cosN p 4 es trig4Tab.Ks trig4Tab.Kc trig4Tab.FsR trig4Tab.FcR x i -
          Real.cos (∑ i ∈ range 4, x i)| ≤
        3164155 / 1000000 * u p ^ 4 * |Real.cos (∑ i ∈ range 4, x i)| +
          5 * (|(redK p 4 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) := by
  have h := thm35_sincos_tab p trig4Tab trig4C (by decide) (by decide) ⟨_, _, rfl⟩ trig4_tab trig4_tiny
    trig4_all hp x hx hH hx0 es
  rw [show ((trig4C : ℚ) : ℝ) = 3164155 / 1000000 by unfold trig4C; norm_num] at h
  exact h

omit [Prec_gt_0 p] in
set_option maxHeartbeats 4000000 in
theorem trig4_kdiv : trig4Tab.KdivOk trig4Kd0 trig4Kd3 := by decide +kernel

omit [Prec_gt_0 p] in
set_option maxHeartbeats 4000000 in
theorem tan4_tiny : trig4Tab.TanTinyOk trig4Ct trig4Kd3 := by decide +kernel

/-- the remark after Theorem 35 at `n = 4`: for `x` at least `2^{4p-1074}` away from the nonzero multiples of `π/2`,
the tangent is within `6.426155u^4 + 5E_π/|sin x cos x|` of `tan x`, relatively -/
theorem thm35_tan_4 (hp : p = 53) (x : ℕ → ℝ) (hx : ∀ i < 4, F p (x i)) (hH : Htheta p 4 2 x)
    (hx0 : |x 0| ≤ 2 ^ 52) (es et : ℝ → ℤ)
    (hfar : redK p 4 x ≠ 0 →
      (2 : ℝ) ^ (p * (4 : ℕ) - 1074) ≤ |∑ i ∈ range 4, x i - redK p 4 x * (Real.pi / 2)|) :
    |∑ i ∈ range 4, tanN p 4 es et trig4Tab.Ks trig4Tab.Kc trig4Tab.FsR trig4Tab.FcR x i -
        Real.tan (∑ i ∈ range 4, x i)| ≤
      (6426155 / 1000000 * u p ^ 4 + 5 * (|(redK p 4 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) /
        |Real.sin (∑ i ∈ range 4, x i) * Real.cos (∑ i ∈ range 4, x i)|) * |Real.tan (∑ i ∈ range 4, x i)| := by
  have h := thm35_tan_tab p trig4Tab trig4Ct trig4Kd0 trig4Kd3 (by decide) (by decide) ⟨_, _, rfl⟩ trig4_tab
    trig4_kdiv tan4_tiny tan4_all hp x hx hH hx0 es et hfar
  rw [show ((trig4Ct : ℚ) : ℝ) = 6426155 / 1000000 by unfold trig4Ct; norm_num] at h
  exact h

end ExpansionBounds
