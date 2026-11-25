import ExpansionBounds.Tan8.Defs

/-!
# Theorem 35 for the tangent at `n = 8` and `p = 53`: the buckets 0, 4, 8, 12, 17, 25, 42, 107

`tan8Ok` on the last states of Horner's runs, which `Trig8/Run0.lean` to `Run7.lean` check. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem tan8_ok0 : tan8Ok 0 41 41 (dySt trig8_s0_39) (dySt trig8_c0_39) := by
  decide +kernel

theorem tan8_g0 : Tan8Group (0, 41, 41) :=
  ⟨_, _, trig8_s0, trig8_c0, tan8_ok0⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok4 : tan8Ok 4 26 27 (dySt trig8_s4_24) (dySt trig8_c4_25) := by
  decide +kernel

theorem tan8_g4 : Tan8Group (4, 26, 27) :=
  ⟨_, _, trig8_s4, trig8_c4, tan8_ok4⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok8 : tan8Ok 8 19 19 (dySt trig8_s8_17) (dySt trig8_c8_17) := by
  decide +kernel

theorem tan8_g8 : Tan8Group (8, 19, 19) :=
  ⟨_, _, trig8_s8, trig8_c8, tan8_ok8⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok12 : tan8Ok 12 14 15 (dySt trig8_s12_12) (dySt trig8_c12_13) := by
  decide +kernel

theorem tan8_g12 : Tan8Group (12, 14, 15) :=
  ⟨_, _, trig8_s12, trig8_c12, tan8_ok12⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok17 : tan8Ok 17 11 11 (dySt trig8_s17_9) (dySt trig8_c17_9) := by
  decide +kernel

theorem tan8_g17 : Tan8Group (17, 11, 11) :=
  ⟨_, _, trig8_s17, trig8_c17, tan8_ok17⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok25 : tan8Ok 25 8 8 (dySt trig8_s25_6) (dySt trig8_c25_6) := by
  decide +kernel

theorem tan8_g25 : Tan8Group (25, 8, 8) :=
  ⟨_, _, trig8_s25, trig8_c25, tan8_ok25⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok42 : tan8Ok 42 5 5 (dySt trig8_s42_3) (dySt trig8_c42_3) := by
  decide +kernel

theorem tan8_g42 : Tan8Group (42, 5, 5) :=
  ⟨_, _, trig8_s42, trig8_c42, tan8_ok42⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok107 : tan8Ok 107 2 3 (trig8Init sinCQ trig8FsQ 1) (dySt trig8_c107_1) := by
  decide +kernel

theorem tan8_g107 : Tan8Group (107, 2, 3) :=
  ⟨_, _, trig8_s107, trig8_c107, tan8_ok107⟩

end ExpansionBounds
