import ExpansionBounds.Recip

/-!
# Controls of the greedy constants

The greedy pair of `1/191516586041457763` is no double word, so `greedy_dd` needs its two-sum. The kernel proves
it.
-/

namespace ExpansionBounds

/-- the greedy pair of `1/191516586041457763` sums to a tie that rounds away from its first part -/
example : rnQ 53 (rnQ 53 (1 / 191516586041457763) + rnQ 53 (1 / 191516586041457763 -
    rnQ 53 (1 / 191516586041457763))) ≠ rnQ 53 (1 / 191516586041457763) := by
  decide +kernel

end ExpansionBounds
