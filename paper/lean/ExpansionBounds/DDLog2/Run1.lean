import ExpansionBounds.DDLog2.Defs

/-!
# Proposition 44, `DD::ln` at `p = 53`: the kernel's checks, part 1

The chords of each group: for `k = 0`, `DDL0Lin` or `DDL0Small`; for `k ≠ 0`, `DDL1Group`.
This file is written by `ddlog_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
/-- `k = 0`, the group of degree 10 -/
theorem ddl0_g8 : DDL0Lin ddl0G8 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k = 0`, the group of degree 9 -/
theorem ddl0_g9 : DDL0Lin ddl0G9 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k = 0`, the group of degree 8 -/
theorem ddl0_g10 : DDL0Lin ddl0G10 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k = 0`, the group of degree 7 -/
theorem ddl0_g11 : DDL0Lin ddl0G11 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k = 0`, the group of degree 6 -/
theorem ddl0_g12 : DDL0Lin ddl0G12 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k = 0`, the group of degree 5 -/
theorem ddl0_g13 : DDL0Lin ddl0G13 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k = 0`, the group of degree 4 -/
theorem ddl0_g14 : DDL0Lin ddl0G14 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k = 0`, the group of degree 3 -/
theorem ddl0_g15 : DDL0Lin ddl0G15 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k = 0`, the group of degree 2 -/
theorem ddl0_s : DDL0Small false ddl0S := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k = 0`, the last group -/
theorem ddl0_last : DDL0Small true ddl0Last := by decide +kernel

end ExpansionBounds
