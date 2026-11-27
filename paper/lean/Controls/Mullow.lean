import ExpansionBounds.MullowOD

/-!
# Controls of the bounds of `series::mullow`

`magic_rnd` needs `|x| < 2^{51}`: at `x = 2^{51} + 1` the rounding returns `2^{51}`, off by 1, which the kernel
proves. `plan_rho` needs its bound on `q_0`: one weight more below it puts the pair's `ρ` far above
`1.13 · 2^{-prec}`.
-/

namespace ExpansionBounds

/-- at `x = 2^{51} + 1`, `RN(RN(x + M) - M)` with `M = 3 · 2^{51}` is `2^{51}` -/
example : rnQ 53 (rnQ 53 (2 ^ 51 + 1 + 6755399441055744) - 6755399441055744) = 2 ^ 51 := by decide +kernel

/-- at `t = 2`, `h_a = h_b = 0`, `prec = 11` and `t ≤ 2^1`, the plan allows `q_0 ≤ 2`; at `q_0 = 3` the pair's `ρ`
exceeds `1.13 · 2^{-11}` -/
example : ¬ ((1 / (1 - 2 ^ (-53 : ℤ))) / (2 ^ 29 * (1 - 2 * 2 ^ (-53 : ℤ))) +
    (1 / (1 - 2 ^ (-53 : ℤ))) / (2 ^ 29 * (1 - 2 * 2 ^ (-53 : ℤ))) +
    (1 / (1 - 2 ^ (-53 : ℤ))) ^ 2 / ((2 ^ 29 * (1 - 2 * 2 ^ (-53 : ℤ))) * (2 ^ 29 * (1 - 2 * 2 ^ (-53 : ℤ)))) +
    2 * 2 ^ 30 * (∑ q ∈ Finset.range 3, (2 : ℝ) ^ (16 * q)) /
      ((2 ^ 29 * (1 - 2 * 2 ^ (-53 : ℤ))) * (2 ^ 29 * (1 - 2 * 2 ^ (-53 : ℤ)))) ≤ 113 / 100 / 2 ^ 11) := by
  norm_num [Finset.sum_range_succ]

end ExpansionBounds
