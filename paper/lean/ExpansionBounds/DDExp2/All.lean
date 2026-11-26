import ExpansionBounds.DDExp2.Run0
import ExpansionBounds.DDExp2.Run1
import ExpansionBounds.DDExp2.Run2

/-!
# Proposition 44, `DD::exp` at `p = 53`: every group

`DD2Group` holds for each group of exponents. This file is written by `ddexp_lean.py`.
-/

namespace ExpansionBounds

/-- every group but the last -/
theorem dd2_all : ∀ g ∈ dd2Grp, DD2Group false g := by
  intro g hg
  simp only [dd2Grp, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact dd2_g0
  · exact dd2_g1
  · exact dd2_g2
  · exact dd2_g3
  · exact dd2_g4
  · exact dd2_g5
  · exact dd2_g6
  · exact dd2_g7
  · exact dd2_g8
  · exact dd2_g9
  · exact dd2_g10
  · exact dd2_g11
  · exact dd2_g12
  · exact dd2_g13
  · exact dd2_g14
  · exact dd2_g15
  · exact dd2_g16

end ExpansionBounds
