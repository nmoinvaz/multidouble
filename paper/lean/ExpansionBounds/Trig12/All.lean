import ExpansionBounds.Trig12.G0
import ExpansionBounds.Trig12.G1
import ExpansionBounds.Trig12.G2
import ExpansionBounds.Trig12.G3
import ExpansionBounds.Trig12.G4
import ExpansionBounds.Trig12.G5
import ExpansionBounds.Trig12.G6
import ExpansionBounds.Trig12.G7
import ExpansionBounds.Trig12.G8
import ExpansionBounds.Trig12.G9
import ExpansionBounds.Trig12.G10
import ExpansionBounds.Trig12.G11
import ExpansionBounds.Trig12.G12
import ExpansionBounds.Trig12.G13
import ExpansionBounds.Trig12.G14
import ExpansionBounds.Trig12.G15
import ExpansionBounds.Trig12.G16
import ExpansionBounds.Trig12.G17
import ExpansionBounds.Trig12.G18
import ExpansionBounds.Trig12.G20
import ExpansionBounds.Trig12.G22
import ExpansionBounds.Trig12.G24
import ExpansionBounds.Trig12.G26
import ExpansionBounds.Trig12.G27
import ExpansionBounds.Trig12.G30
import ExpansionBounds.Trig12.G33
import ExpansionBounds.Trig12.G38
import ExpansionBounds.Trig12.G44
import ExpansionBounds.Trig12.G52
import ExpansionBounds.Trig12.G63
import ExpansionBounds.Trig12.G79
import ExpansionBounds.Trig12.G106
import ExpansionBounds.Trig12.G107
import ExpansionBounds.Trig12.G160
import ExpansionBounds.Trig12.G161

/-!
# Theorem 35 at `n = 12` and `p = 53`: every bucket

`TrigTab.Group` and `TrigTab.TanGroup` hold for each run of buckets with the same series lengths. This file is
written by `trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_all : ∀ g ∈ trig12Tab.groups, trig12Tab.Group trig12C g := by
  intro g hg
  change g ∈ trig12Groups at hg
  simp only [trig12Groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact trig12_g0
  · exact trig12_g1
  · exact trig12_g2
  · exact trig12_g3
  · exact trig12_g4
  · exact trig12_g5
  · exact trig12_g6
  · exact trig12_g7
  · exact trig12_g8
  · exact trig12_g9
  · exact trig12_g10
  · exact trig12_g11
  · exact trig12_g12
  · exact trig12_g13
  · exact trig12_g14
  · exact trig12_g15
  · exact trig12_g16
  · exact trig12_g17
  · exact trig12_g18
  · exact trig12_g20
  · exact trig12_g22
  · exact trig12_g24
  · exact trig12_g26
  · exact trig12_g27
  · exact trig12_g30
  · exact trig12_g33
  · exact trig12_g38
  · exact trig12_g44
  · exact trig12_g52
  · exact trig12_g63
  · exact trig12_g79
  · exact trig12_g106
  · exact trig12_g107
  · exact trig12_g160
  · exact trig12_g161

theorem tan12_all : ∀ g ∈ trig12Tab.groups, trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 g := by
  intro g hg
  change g ∈ trig12Groups at hg
  simp only [trig12Groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tan12_g0
  · exact tan12_g1
  · exact tan12_g2
  · exact tan12_g3
  · exact tan12_g4
  · exact tan12_g5
  · exact tan12_g6
  · exact tan12_g7
  · exact tan12_g8
  · exact tan12_g9
  · exact tan12_g10
  · exact tan12_g11
  · exact tan12_g12
  · exact tan12_g13
  · exact tan12_g14
  · exact tan12_g15
  · exact tan12_g16
  · exact tan12_g17
  · exact tan12_g18
  · exact tan12_g20
  · exact tan12_g22
  · exact tan12_g24
  · exact tan12_g26
  · exact tan12_g27
  · exact tan12_g30
  · exact tan12_g33
  · exact tan12_g38
  · exact tan12_g44
  · exact tan12_g52
  · exact tan12_g63
  · exact tan12_g79
  · exact tan12_g106
  · exact tan12_g107
  · exact tan12_g160
  · exact tan12_g161

end ExpansionBounds
