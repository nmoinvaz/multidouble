import ExpansionBounds.DDLog2.Defs

/-!
# Proposition 44, `DD::ln` at `p = 53`: the kernel's checks, part 6

The chords of each group: for `k = 0`, `DDL0Lin` or `DDL0Small`; for `k ≠ 0`, `DDL1Group`.
This file is written by `ddlog_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
/-- `k ≠ 0`, the group of degree 10 -/
theorem ddl1_g8 : DDL1Group false ddl1G8 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k ≠ 0`, the group of degree 9 -/
theorem ddl1_g9 : DDL1Group false ddl1G9 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k ≠ 0`, the group of degree 8 -/
theorem ddl1_g10 : DDL1Group false ddl1G10 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k ≠ 0`, the group of degree 7 -/
theorem ddl1_g11 : DDL1Group false ddl1G11 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k ≠ 0`, the group of degree 6 -/
theorem ddl1_g12 : DDL1Group false ddl1G12 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k ≠ 0`, the group of degree 5 -/
theorem ddl1_g13 : DDL1Group false ddl1G13 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k ≠ 0`, the group of degree 4 -/
theorem ddl1_g14 : DDL1Group false ddl1G14 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k ≠ 0`, the group of degree 3 -/
theorem ddl1_g15 : DDL1Group false ddl1G15 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k ≠ 0`, the group of degree 2 -/
theorem ddl1_g16 : DDL1Group false ddl1G16 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `k ≠ 0`, the last group -/
theorem ddl1_last : DDL1Group true ddl1Last := by decide +kernel

end ExpansionBounds
