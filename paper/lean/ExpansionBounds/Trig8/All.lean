import ExpansionBounds.Trig8.Run0
import ExpansionBounds.Trig8.Run1
import ExpansionBounds.Trig8.Run2
import ExpansionBounds.Trig8.Run3
import ExpansionBounds.Trig8.Run4
import ExpansionBounds.Trig8.Run5
import ExpansionBounds.Trig8.Run6
import ExpansionBounds.Trig8.Run7

/-!
# Theorem 35 at `n = 8` and `p = 53`: every bucket

`Trig8Group` holds for each run of buckets with the same series lengths. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig8_all : ∀ g ∈ trig8Groups, Trig8Group g := by
  intro g hg
  simp only [trig8Groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact trig8_g0
  · exact trig8_g1
  · exact trig8_g2
  · exact trig8_g3
  · exact trig8_g4
  · exact trig8_g5
  · exact trig8_g6
  · exact trig8_g7
  · exact trig8_g8
  · exact trig8_g9
  · exact trig8_g10
  · exact trig8_g11
  · exact trig8_g12
  · exact trig8_g13
  · exact trig8_g14
  · exact trig8_g15
  · exact trig8_g17
  · exact trig8_g19
  · exact trig8_g21
  · exact trig8_g22
  · exact trig8_g25
  · exact trig8_g29
  · exact trig8_g34
  · exact trig8_g41
  · exact trig8_g42
  · exact trig8_g52
  · exact trig8_g53
  · exact trig8_g71
  · exact trig8_g107
  · exact trig8_g108

end ExpansionBounds
