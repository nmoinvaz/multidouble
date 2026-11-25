import ExpansionBounds.Trig2.Run0

/-!
# Theorem 35 at `n = 2` and `p = 53`: every bucket

`TrigTab.Group` and `TrigTab.TanGroup` hold for each run of buckets with the same series lengths. This file is
written by `trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig2_all : ∀ g ∈ trig2Tab.groups, trig2Tab.Group trig2C g := by
  intro g hg
  change g ∈ trig2Groups at hg
  simp only [trig2Groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact trig2_g0
  · exact trig2_g1
  · exact trig2_g2
  · exact trig2_g3
  · exact trig2_g4
  · exact trig2_g5
  · exact trig2_g6
  · exact trig2_g7
  · exact trig2_g8
  · exact trig2_g10
  · exact trig2_g13
  · exact trig2_g18
  · exact trig2_g28

theorem tan2_all : ∀ g ∈ trig2Tab.groups, trig2Tab.TanGroup trig2Ct trig2Kd0 trig2Kd3 g := by
  intro g hg
  change g ∈ trig2Groups at hg
  simp only [trig2Groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tan2_g0
  · exact tan2_g1
  · exact tan2_g2
  · exact tan2_g3
  · exact tan2_g4
  · exact tan2_g5
  · exact tan2_g6
  · exact tan2_g7
  · exact tan2_g8
  · exact tan2_g10
  · exact tan2_g13
  · exact tan2_g18
  · exact tan2_g28

end ExpansionBounds
