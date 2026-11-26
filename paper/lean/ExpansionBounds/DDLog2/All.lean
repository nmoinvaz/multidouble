import ExpansionBounds.DDLog2.Run0
import ExpansionBounds.DDLog2.Run1
import ExpansionBounds.DDLog2.Run2
import ExpansionBounds.DDLog2.Run3
import ExpansionBounds.DDLog2.Run4
import ExpansionBounds.DDLog2.Run5
import ExpansionBounds.DDLog2.Run6

/-!
# Proposition 44, `DD::ln` at `p = 53`: every group

The kernel's checks hold for each group of exponents, for `k = 0` and for `k ≠ 0`.
This file is written by `ddlog_lean.py`.
-/

namespace ExpansionBounds

/-- `k = 0`: every group on the linear piece -/
theorem ddl0_all : ∀ g ∈ ddl0Lin, DDL0Lin g := by
  intro g hg
  simp only [ddl0Lin, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ddl0_g0
  · exact ddl0_g1
  · exact ddl0_g2
  · exact ddl0_g3
  · exact ddl0_g4
  · exact ddl0_g5
  · exact ddl0_g6
  · exact ddl0_g7
  · exact ddl0_g8
  · exact ddl0_g9
  · exact ddl0_g10
  · exact ddl0_g11
  · exact ddl0_g12
  · exact ddl0_g13
  · exact ddl0_g14
  · exact ddl0_g15

/-- `k ≠ 0`: every group but the last -/
theorem ddl1_all : ∀ g ∈ ddl1Grp, DDL1Group false g := by
  intro g hg
  simp only [ddl1Grp, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ddl1_g0
  · exact ddl1_g1
  · exact ddl1_g2
  · exact ddl1_g3
  · exact ddl1_g4
  · exact ddl1_g5
  · exact ddl1_g6
  · exact ddl1_g7
  · exact ddl1_g8
  · exact ddl1_g9
  · exact ddl1_g10
  · exact ddl1_g11
  · exact ddl1_g12
  · exact ddl1_g13
  · exact ddl1_g14
  · exact ddl1_g15
  · exact ddl1_g16

end ExpansionBounds
