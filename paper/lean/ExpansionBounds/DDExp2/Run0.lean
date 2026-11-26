import ExpansionBounds.DDExp2.Defs

/-!
# Proposition 44, `DD::exp` at `p = 53`: the kernel's checks, part 0

`DD2Group` for each group: its intervals follow each other, and each has `DD2Bin`.
This file is written by `ddexp_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
/-- the group of degree 27 -/
theorem dd2_g0 : DD2Group false dd2G0 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the group of degree 24 -/
theorem dd2_g1 : DD2Group false dd2G1 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the group of degree 20 -/
theorem dd2_g2 : DD2Group false dd2G2 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the group of degree 17 -/
theorem dd2_g3 : DD2Group false dd2G3 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the group of degree 15 -/
theorem dd2_g4 : DD2Group false dd2G4 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the group of degree 14 -/
theorem dd2_g5 : DD2Group false dd2G5 := by decide +kernel

end ExpansionBounds
