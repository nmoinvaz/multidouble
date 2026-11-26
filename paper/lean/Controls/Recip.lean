import ExpansionBounds.Recip
import ExpansionBounds.Relaxed

/-!
# Controls of the greedy constants and of the relaxed squares

The greedy pair of `1/191516586041457763` is no double word, so `greedy_dd` needs its two-sum; and without the
transposes the squares of `Relaxed` miss a term that `relaxed_cover` places in one. The kernel proves both.
-/

namespace ExpansionBounds

/-- the greedy pair of `1/191516586041457763` sums to a tie that rounds away from its first part -/
example : rnQ 53 (rnQ 53 (1 / 191516586041457763) + rnQ 53 (1 / 191516586041457763 -
    rnQ 53 (1 / 191516586041457763))) ≠ rnQ 53 (1 / 191516586041457763) := by
  decide +kernel

/-- without the transposes, no square of the first 20 steps holds the term `(2, 5)` for `s_0 = 1` -/
example : ¬ ∃ e < 20, ∃ q ∈ (relStep 0 e).filter (fun q => !q.2.2), relCovers q 2 5 := by
  decide +kernel

/-- the same search with the transposes finds it -/
example : ∃ e < 20, ∃ q ∈ relStep 0 e, relCovers q 2 5 := by
  decide +kernel

end ExpansionBounds
