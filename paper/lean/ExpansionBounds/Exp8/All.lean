import ExpansionBounds.Exp8.Run0
import ExpansionBounds.Exp8.Run1
import ExpansionBounds.Exp8.Run2
import ExpansionBounds.Exp8.Run3
import ExpansionBounds.Exp8.Run4
import ExpansionBounds.Exp8.Run5
import ExpansionBounds.Exp8.Run6
import ExpansionBounds.Exp8.Run7
import ExpansionBounds.Exp8.Run8
import ExpansionBounds.Exp8.Run9
import ExpansionBounds.Exp8.Run10
import ExpansionBounds.Exp8.Run11

/-!
# Theorem 40 at `n = 8` and `p = 53`: every group

`Exp8Group` holds for each group of exponents, for `k = 0` and for `k ≠ 0`. This file is written by `exp_lean.py`.
-/

namespace ExpansionBounds

theorem exp8_all0 : ∀ g ∈ exp8Grp0, Exp8Group true g := by
  intro g hg
  simp only [exp8Grp0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact exp8_z0
  · exact exp8_z1
  · exact exp8_z2
  · exact exp8_z3
  · exact exp8_z4
  · exact exp8_z5
  · exact exp8_z6
  · exact exp8_z7
  · exact exp8_z8
  · exact exp8_z9
  · exact exp8_z10
  · exact exp8_z11
  · exact exp8_z12
  · exact exp8_z13
  · exact exp8_z14
  · exact exp8_z15
  · exact exp8_z16
  · exact exp8_z17
  · exact exp8_z18
  · exact exp8_z19
  · exact exp8_z20
  · exact exp8_z21
  · exact exp8_z22
  · exact exp8_z23
  · exact exp8_z24
  · exact exp8_z25
  · exact exp8_z26
  · exact exp8_z27
  · exact exp8_z28
  · exact exp8_z29
  · exact exp8_z30
  · exact exp8_z31
  · exact exp8_z32
  · exact exp8_z33
  · exact exp8_z34
  · exact exp8_z35

theorem exp8_last0 : Exp8Group true exp8Last0 :=
  exp8_z36

theorem exp8_all1 : ∀ g ∈ exp8Grp1, Exp8Group false g := by
  intro g hg
  simp only [exp8Grp1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact exp8_n0
  · exact exp8_n1
  · exact exp8_n2
  · exact exp8_n3
  · exact exp8_n4
  · exact exp8_n5
  · exact exp8_n6
  · exact exp8_n7
  · exact exp8_n8
  · exact exp8_n9
  · exact exp8_n10
  · exact exp8_n11
  · exact exp8_n12
  · exact exp8_n13
  · exact exp8_n14
  · exact exp8_n15
  · exact exp8_n16
  · exact exp8_n17
  · exact exp8_n18
  · exact exp8_n19
  · exact exp8_n20
  · exact exp8_n21
  · exact exp8_n22
  · exact exp8_n23
  · exact exp8_n24
  · exact exp8_n25
  · exact exp8_n26
  · exact exp8_n27
  · exact exp8_n28
  · exact exp8_n29
  · exact exp8_n30
  · exact exp8_n31
  · exact exp8_n32
  · exact exp8_n33
  · exact exp8_n34
  · exact exp8_n35

theorem exp8_last1 : Exp8Group false exp8Last1 :=
  exp8_n36

end ExpansionBounds
