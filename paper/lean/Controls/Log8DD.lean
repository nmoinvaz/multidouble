import ExpansionBounds.Log8DD

/-!
# Controls of the start of Theorem 42 at `n = 8`

Each claim below is one of the kernel's checks of `Log8DD.lean` on a wrong number, and the kernel proves its
negation.
-/

namespace ExpansionBounds

/-- with four times its trailing part, the double-double `ln 2` is not a double word -/
example : ¬ rnQ 53 (dyQ log8CL0 + 4 * dyQ log8CL1) = dyQ log8CL0 := by
  decide +kernel

/-- `δ_0` is not below `2^{-104}` -/
example : ¬ log8D0 ≤ 1 / 2 ^ 104 := by
  decide +kernel

end ExpansionBounds
