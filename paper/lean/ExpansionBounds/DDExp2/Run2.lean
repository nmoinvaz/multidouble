import ExpansionBounds.DDExp2.Defs

/-!
# Proposition 44, `DD::exp` at `p = 53`: the kernel's checks, part 2

`DD2Group` for each group: its intervals follow each other, and each has `DD2Bin`.
This file is written by `ddexp_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
/-- the group of degree 6 -/
theorem dd2_g12 : DD2Group false dd2G12 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the group of degree 5 -/
theorem dd2_g13 : DD2Group false dd2G13 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the group of degree 4 -/
theorem dd2_g14 : DD2Group false dd2G14 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the group of degree 3 -/
theorem dd2_g15 : DD2Group false dd2G15 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the group of degree 2 -/
theorem dd2_g16 : DD2Group false dd2G16 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the last group -/
theorem dd2_last : DD2Group true dd2Last := by decide +kernel

end ExpansionBounds
