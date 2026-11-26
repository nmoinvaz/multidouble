import ExpansionBounds.DDExp2.Defs

/-!
# Proposition 44, `DD::exp` at `p = 53`: the kernel's checks, part 1

`DD2Group` for each group: its intervals follow each other, and each has `DD2Bin`.
This file is written by `ddexp_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
/-- the group of degree 12 -/
theorem dd2_g6 : DD2Group false dd2G6 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the group of degree 11 -/
theorem dd2_g7 : DD2Group false dd2G7 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the group of degree 10 -/
theorem dd2_g8 : DD2Group false dd2G8 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the group of degree 9 -/
theorem dd2_g9 : DD2Group false dd2G9 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the group of degree 8 -/
theorem dd2_g10 : DD2Group false dd2G10 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the group of degree 7 -/
theorem dd2_g11 : DD2Group false dd2G11 := by decide +kernel

end ExpansionBounds
