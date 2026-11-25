import ExpansionBounds.Tan8.Run0
import ExpansionBounds.Tan8.Run1
import ExpansionBounds.Tan8.Run2
import ExpansionBounds.Tan8.Run3

/-!
# Theorem 35 for the tangent at `n = 8` and `p = 53`: every bucket

`Tan8Group` holds for each run of buckets with the same series lengths. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

theorem tan8_all : ∀ g ∈ trig8Groups, Tan8Group g := by
  intro g hg
  simp only [trig8Groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tan8_g0
  · exact tan8_g1
  · exact tan8_g2
  · exact tan8_g3
  · exact tan8_g4
  · exact tan8_g5
  · exact tan8_g6
  · exact tan8_g7
  · exact tan8_g8
  · exact tan8_g9
  · exact tan8_g10
  · exact tan8_g11
  · exact tan8_g12
  · exact tan8_g13
  · exact tan8_g14
  · exact tan8_g15
  · exact tan8_g17
  · exact tan8_g19
  · exact tan8_g21
  · exact tan8_g22
  · exact tan8_g25
  · exact tan8_g29
  · exact tan8_g34
  · exact tan8_g41
  · exact tan8_g42
  · exact tan8_g52
  · exact tan8_g53
  · exact tan8_g71
  · exact tan8_g107
  · exact tan8_g108

end ExpansionBounds
