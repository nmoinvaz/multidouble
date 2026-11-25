import ExpansionBounds.Trig4.Run0
import ExpansionBounds.Trig4.Run1

/-!
# Theorem 35 at `n = 4` and `p = 53`: every bucket

`TrigTab.Group` and `TrigTab.TanGroup` hold for each run of buckets with the same series lengths. This file is
written by `trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig4_all : ∀ g ∈ trig4Tab.groups, trig4Tab.Group trig4C g := by
  intro g hg
  change g ∈ trig4Groups at hg
  simp only [trig4Groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact trig4_g0
  · exact trig4_g1
  · exact trig4_g2
  · exact trig4_g3
  · exact trig4_g4
  · exact trig4_g5
  · exact trig4_g6
  · exact trig4_g7
  · exact trig4_g8
  · exact trig4_g9
  · exact trig4_g10
  · exact trig4_g11
  · exact trig4_g12
  · exact trig4_g13
  · exact trig4_g14
  · exact trig4_g16
  · exact trig4_g17
  · exact trig4_g20
  · exact trig4_g21
  · exact trig4_g26
  · exact trig4_g35
  · exact trig4_g36
  · exact trig4_g54
  · exact trig4_g55

theorem tan4_all : ∀ g ∈ trig4Tab.groups, trig4Tab.TanGroup trig4Ct trig4Kd0 trig4Kd3 g := by
  intro g hg
  change g ∈ trig4Groups at hg
  simp only [trig4Groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact tan4_g0
  · exact tan4_g1
  · exact tan4_g2
  · exact tan4_g3
  · exact tan4_g4
  · exact tan4_g5
  · exact tan4_g6
  · exact tan4_g7
  · exact tan4_g8
  · exact tan4_g9
  · exact tan4_g10
  · exact tan4_g11
  · exact tan4_g12
  · exact tan4_g13
  · exact tan4_g14
  · exact tan4_g16
  · exact tan4_g17
  · exact tan4_g20
  · exact tan4_g21
  · exact tan4_g26
  · exact tan4_g35
  · exact tan4_g36
  · exact tan4_g54
  · exact tan4_g55

end ExpansionBounds
