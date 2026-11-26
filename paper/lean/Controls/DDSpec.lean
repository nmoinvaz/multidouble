import ExpansionBounds.DDSpec

/-!
# Controls of Proposition 44 on the four double-word algorithms

`DDSpec.lean` has one check by the kernel, `ddl_delta_top`: the reduction's `δ` at the top of `|r|` for `k ≠ 0`
is at most `2^{-106}`. The claim below is that check with a wrong number, and the kernel proves its negation.
-/

namespace ExpansionBounds

/-- the reduction's `δ` at the top of `|r|` for `k ≠ 0` is not within `2^{-107}` -/
example : ¬ ddlDelta (dyQ ddlTop1S + dyQ ddlDStarS) ≤ 1 / 2 ^ 107 := by decide +kernel

end ExpansionBounds
