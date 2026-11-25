import ExpansionBounds.Tan8.Defs

/-!
# Theorem 35 for the tangent at `n = 8` and `p = 53`: the buckets 3, 7, 11, 15, 22, 41, 71

`tan8Ok` on the last states of Horner's runs, which `Trig8/Run0.lean` to `Run7.lean` check. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem tan8_ok3 : tan8Ok 3 29 29 (dySt trig8_s3_27) (dySt trig8_c3_27) := by
  decide +kernel

theorem tan8_g3 : Tan8Group (3, 29, 29) :=
  ⟨_, _, trig8_s3, trig8_c3, tan8_ok3⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok7 : tan8Ok 7 20 20 (dySt trig8_s7_18) (dySt trig8_c7_18) := by
  decide +kernel

theorem tan8_g7 : Tan8Group (7, 20, 20) :=
  ⟨_, _, trig8_s7, trig8_c7, tan8_ok7⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok11 : tan8Ok 11 15 15 (dySt trig8_s11_13) (dySt trig8_c11_13) := by
  decide +kernel

theorem tan8_g11 : Tan8Group (11, 15, 15) :=
  ⟨_, _, trig8_s11, trig8_c11, tan8_ok11⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok15 : tan8Ok 15 12 12 (dySt trig8_s15_10) (dySt trig8_c15_10) := by
  decide +kernel

theorem tan8_g15 : Tan8Group (15, 12, 12) :=
  ⟨_, _, trig8_s15, trig8_c15, tan8_ok15⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok22 : tan8Ok 22 9 9 (dySt trig8_s22_7) (dySt trig8_c22_7) := by
  decide +kernel

theorem tan8_g22 : Tan8Group (22, 9, 9) :=
  ⟨_, _, trig8_s22, trig8_c22, tan8_ok22⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok41 : tan8Ok 41 5 6 (dySt trig8_s41_3) (dySt trig8_c41_4) := by
  decide +kernel

theorem tan8_g41 : Tan8Group (41, 5, 6) :=
  ⟨_, _, trig8_s41, trig8_c41, tan8_ok41⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok71 : tan8Ok 71 3 3 (dySt trig8_s71_1) (dySt trig8_c71_1) := by
  decide +kernel

theorem tan8_g71 : Tan8Group (71, 3, 3) :=
  ⟨_, _, trig8_s71, trig8_c71, tan8_ok71⟩

end ExpansionBounds
