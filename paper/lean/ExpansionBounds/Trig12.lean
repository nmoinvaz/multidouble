import ExpansionBounds.Trig12.All
import ExpansionBounds.TrigN

/-!
# Theorem 35 at `n = 12` and `p = 53`: sine and cosine within `3582.787311u^12`, tangent within `4929.367335u^12`

The remark after Theorem 35 at `n = 12`: SIN and COS with the coefficients and series lengths of
`Trig12/Data.lean`, on `x` in `F`, on `H(2)` and with `|x_0| ≤ 2^52`, are within `3582.787311u^12` of `sin x` and
`cos x`, relatively, plus `5E_π`, and TAN, for `x` at least `2^{12p-1074}` away from the nonzero multiples
of `π/2`, within `4929.367335u^12 + 5E_π/|sin x cos x|` of `tan x`, relatively. The kernel checks the tables,
`κ_DIV` on the quotient's two ladders, the bounds below the last bucket and, in `Trig12/G0.lean` on, every
run of buckets; `thm35_sincos_tab` and `thm35_tan_tab` do the rest. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

open Finset

theorem trig12_tab : trig12Tab.TabOk := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_tiny : trig12Tab.TinyOk trig12C := by decide +kernel

variable (p : ℤ) [Prec_gt_0 p]

/-- the remark after Theorem 35 at `n = 12`: the sine and the cosine are within `3582.787311u^12` of `sin x` and
`cos x`, relatively, plus `5E_π` -/
theorem thm35_sincos_12 (hp : p = 53) (x : ℕ → ℝ) (hx : ∀ i < 12, F p (x i)) (hH : Htheta p 12 2 x)
    (hx0 : |x 0| ≤ 2 ^ 52) (es : ℝ → ℤ) :
    |∑ i ∈ range 12, sinN p 12 es trig12Tab.Ks trig12Tab.Kc trig12Tab.FsR trig12Tab.FcR x i -
          Real.sin (∑ i ∈ range 12, x i)| ≤
        3582787311 / 1000000 * u p ^ 12 * |Real.sin (∑ i ∈ range 12, x i)| +
          5 * (|(redK p 12 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) ∧
      |∑ i ∈ range 12, cosN p 12 es trig12Tab.Ks trig12Tab.Kc trig12Tab.FsR trig12Tab.FcR x i -
          Real.cos (∑ i ∈ range 12, x i)| ≤
        3582787311 / 1000000 * u p ^ 12 * |Real.cos (∑ i ∈ range 12, x i)| +
          5 * (|(redK p 12 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) := by
  have h := thm35_sincos_tab p trig12Tab trig12C (by decide) (by decide) ⟨_, _, rfl⟩ trig12_tab trig12_tiny
    trig12_all hp x hx hH hx0 es
  rw [show ((trig12C : ℚ) : ℝ) = 3582787311 / 1000000 by unfold trig12C; norm_num] at h
  exact h

omit [Prec_gt_0 p] in
set_option maxHeartbeats 4000000 in
theorem trig12_kdiv : trig12Tab.KdivOk trig12Kd0 trig12Kd3 := by decide +kernel

omit [Prec_gt_0 p] in
set_option maxHeartbeats 4000000 in
theorem tan12_tiny : trig12Tab.TanTinyOk trig12Ct trig12Kd3 := by decide +kernel

/-- the remark after Theorem 35 at `n = 12`: for `x` at least `2^{12p-1074}` away from the nonzero multiples of `π/2`,
the tangent is within `4929.367335u^12 + 5E_π/|sin x cos x|` of `tan x`, relatively -/
theorem thm35_tan_12 (hp : p = 53) (x : ℕ → ℝ) (hx : ∀ i < 12, F p (x i)) (hH : Htheta p 12 2 x)
    (hx0 : |x 0| ≤ 2 ^ 52) (es et : ℝ → ℤ)
    (hfar : redK p 12 x ≠ 0 →
      (2 : ℝ) ^ (p * (12 : ℕ) - 1074) ≤ |∑ i ∈ range 12, x i - redK p 12 x * (Real.pi / 2)|) :
    |∑ i ∈ range 12, tanN p 12 es et trig12Tab.Ks trig12Tab.Kc trig12Tab.FsR trig12Tab.FcR x i -
        Real.tan (∑ i ∈ range 12, x i)| ≤
      (4929367335 / 1000000 * u p ^ 12 + 5 * (|(redK p 12 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) /
        |Real.sin (∑ i ∈ range 12, x i) * Real.cos (∑ i ∈ range 12, x i)|) * |Real.tan (∑ i ∈ range 12, x i)| := by
  have h := thm35_tan_tab p trig12Tab trig12Ct trig12Kd0 trig12Kd3 (by decide) (by decide) ⟨_, _, rfl⟩ trig12_tab
    trig12_kdiv tan12_tiny tan12_all hp x hx hH hx0 es et hfar
  rw [show ((trig12Ct : ℚ) : ℝ) = 4929367335 / 1000000 by unfold trig12Ct; norm_num] at h
  exact h

end ExpansionBounds
