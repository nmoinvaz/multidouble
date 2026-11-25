import ExpansionBounds.Tan8.Defs

/-!
# Theorem 35 for the tangent at `n = 8` and `p = 53`: the buckets 1, 5, 9, 13, 19, 29, 52, 108

`tan8Ok` on the last states of Horner's runs, which `Trig8/Run0.lean` to `Run7.lean` check. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem tan8_ok1 : tan8Ok 1 37 38 (dySt trig8_s1_35) (dySt trig8_c1_36) := by
  decide +kernel

theorem tan8_g1 : Tan8Group (1, 37, 38) :=
  ⟨_, _, trig8_s1, trig8_c1, tan8_ok1⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok5 : tan8Ok 5 24 24 (dySt trig8_s5_22) (dySt trig8_c5_22) := by
  decide +kernel

theorem tan8_g5 : Tan8Group (5, 24, 24) :=
  ⟨_, _, trig8_s5, trig8_c5, tan8_ok5⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok9 : tan8Ok 9 17 18 (dySt trig8_s9_15) (dySt trig8_c9_16) := by
  decide +kernel

theorem tan8_g9 : Tan8Group (9, 17, 18) :=
  ⟨_, _, trig8_s9, trig8_c9, tan8_ok9⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok13 : tan8Ok 13 14 14 (dySt trig8_s13_12) (dySt trig8_c13_12) := by
  decide +kernel

theorem tan8_g13 : Tan8Group (13, 14, 14) :=
  ⟨_, _, trig8_s13, trig8_c13, tan8_ok13⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok19 : tan8Ok 19 10 10 (dySt trig8_s19_8) (dySt trig8_c19_8) := by
  decide +kernel

theorem tan8_g19 : Tan8Group (19, 10, 10) :=
  ⟨_, _, trig8_s19, trig8_c19, tan8_ok19⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok29 : tan8Ok 29 7 7 (dySt trig8_s29_5) (dySt trig8_c29_5) := by
  decide +kernel

theorem tan8_g29 : Tan8Group (29, 7, 7) :=
  ⟨_, _, trig8_s29, trig8_c29, tan8_ok29⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok52 : tan8Ok 52 4 5 (dySt trig8_s52_2) (dySt trig8_c52_3) := by
  decide +kernel

theorem tan8_g52 : Tan8Group (52, 4, 5) :=
  ⟨_, _, trig8_s52, trig8_c52, tan8_ok52⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok108 : tan8Ok 108 2 2 (trig8Init sinCQ trig8FsQ 1) (trig8Init cosCQ trig8FcQ 1) := by
  decide +kernel

theorem tan8_g108 : Tan8Group (108, 2, 2) :=
  ⟨_, _, trig8_s108, trig8_c108, tan8_ok108⟩

end ExpansionBounds
