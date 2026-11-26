import ExpansionBounds.DDLog2.Defs

/-!
# Proposition 44, `DD::ln` at `p = 53`: the kernel's checks, part 0

The chords of each group: for `k = 0`, `DDL0Lin` or `DDL0Small`; for `k ≠ 0`, `DDL1Group`.
This file is written by `ddlog_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
/-- `k = 0`, the group of degree 27 -/
theorem ddl0_g0 : DDL0Lin ddl0G0 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k = 0`, the group of degree 24 -/
theorem ddl0_g1 : DDL0Lin ddl0G1 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k = 0`, the group of degree 20 -/
theorem ddl0_g2 : DDL0Lin ddl0G2 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k = 0`, the group of degree 17 -/
theorem ddl0_g3 : DDL0Lin ddl0G3 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k = 0`, the group of degree 15 -/
theorem ddl0_g4 : DDL0Lin ddl0G4 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k = 0`, the group of degree 14 -/
theorem ddl0_g5 : DDL0Lin ddl0G5 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k = 0`, the group of degree 12 -/
theorem ddl0_g6 : DDL0Lin ddl0G6 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k = 0`, the group of degree 11 -/
theorem ddl0_g7 : DDL0Lin ddl0G7 := by decide +kernel

end ExpansionBounds
