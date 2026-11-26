import ExpansionBounds.DDLog2.Defs

/-!
# Proposition 44, `DD::ln` at `p = 53`: the kernel's checks, part 5

The chords of each group: for `k = 0`, `DDL0Lin` or `DDL0Small`; for `k ≠ 0`, `DDL1Group`.
This file is written by `ddlog_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
/-- `k ≠ 0`, the group of degree 12 -/
theorem ddl1_g6 : DDL1Group false ddl1G6 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k ≠ 0`, the group of degree 11 -/
theorem ddl1_g7 : DDL1Group false ddl1G7 := by decide +kernel

end ExpansionBounds
