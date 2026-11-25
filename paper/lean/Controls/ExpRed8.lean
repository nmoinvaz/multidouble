import ExpansionBounds.ExpRed8

/-!
# Controls of Lemma 38 at `n = 8`

Each claim below is one of the kernel's checks of `ExpRed8.lean` with a bound moved by one unit or a constant
changed, and the kernel proves its negation.
-/

namespace ExpansionBounds

/-- the lower bound of `ln 2`, four units up, is not below the series' partial sum -/
example : ¬ ln2A + 4 / 2 ^ 600 ≤ 2 / 3 * atSQ (1 / 9) 200 := by decide +kernel

/-- the upper bound of `ln 2`, four units down, is not above the series' sum with its remainder -/
example : ¬ 2 / 3 * atSQ (1 / 9) 200 + 2 / 3 * ((1 / 9) ^ 200 / ((2 * 200 + 1) * (8 / 9))) ≤ ln2B - 4 / 2 ^ 600 := by
  decide +kernel

/-- a part with 54 bits is not in `F` -/
example : ¬ rnQ 53 ((2 ^ 53 + 1) / 2 ^ 60) = (2 ^ 53 + 1) / 2 ^ 60 := by decide +kernel

/-- the next float above `c_r` is not `RN(1/ln 2)` -/
example : ¬ |cr8 + 1 / 2 ^ 52 - 1 / ln2B| < 1 / 2 ^ 53 := by decide +kernel

/-- `|r_e|`'s bound is above `0.346573` -/
example : ¬ red8RMax ≤ 346573 / 10 ^ 6 := by decide +kernel

/-- `δ`'s is above `0.346573u^8` -/
example : ¬ red8Delta red8RMax ≤ 346573 / 10 ^ 6 * red8U ^ 8 := by decide +kernel

/-- the parts' bounds are not all within `0.346573u^i` -/
example : ¬ ∀ i < 8, red8Pi red8RMax i ≤ 346573 / 10 ^ 6 * red8U ^ i := by decide +kernel

/-- `α_0` is not below `1/4` -/
example : ¬ red8A0 < 1 / 4 := by decide +kernel

end ExpansionBounds
