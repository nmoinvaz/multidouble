import ExpansionBounds.Tan8.Defs

/-!
# Theorem 35 for the tangent at `n = 8` and `p = 53`: the buckets 2, 6, 10, 14, 21, 34, 53

`tan8Ok` on the last states of Horner's runs, which `Trig8/Run0.lean` to `Run7.lean` check. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem tan8_ok2 : tan8Ok 2 33 33 (dySt trig8_s2_31) (dySt trig8_c2_31) := by
  decide +kernel

theorem tan8_g2 : Tan8Group (2, 33, 33) :=
  ⟨_, _, trig8_s2, trig8_c2, tan8_ok2⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok6 : tan8Ok 6 22 22 (dySt trig8_s6_20) (dySt trig8_c6_20) := by
  decide +kernel

theorem tan8_g6 : Tan8Group (6, 22, 22) :=
  ⟨_, _, trig8_s6, trig8_c6, tan8_ok6⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok10 : tan8Ok 10 16 16 (dySt trig8_s10_14) (dySt trig8_c10_14) := by
  decide +kernel

theorem tan8_g10 : Tan8Group (10, 16, 16) :=
  ⟨_, _, trig8_s10, trig8_c10, tan8_ok10⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok14 : tan8Ok 14 13 13 (dySt trig8_s14_11) (dySt trig8_c14_11) := by
  decide +kernel

theorem tan8_g14 : Tan8Group (14, 13, 13) :=
  ⟨_, _, trig8_s14, trig8_c14, tan8_ok14⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok21 : tan8Ok 21 9 10 (dySt trig8_s21_7) (dySt trig8_c21_8) := by
  decide +kernel

theorem tan8_g21 : Tan8Group (21, 9, 10) :=
  ⟨_, _, trig8_s21, trig8_c21, tan8_ok21⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok34 : tan8Ok 34 6 6 (dySt trig8_s34_4) (dySt trig8_c34_4) := by
  decide +kernel

theorem tan8_g34 : Tan8Group (34, 6, 6) :=
  ⟨_, _, trig8_s34, trig8_c34, tan8_ok34⟩

set_option maxHeartbeats 4000000 in
theorem tan8_ok53 : tan8Ok 53 4 4 (dySt trig8_s53_2) (dySt trig8_c53_2) := by
  decide +kernel

theorem tan8_g53 : Tan8Group (53, 4, 4) :=
  ⟨_, _, trig8_s53, trig8_c53, tan8_ok53⟩

end ExpansionBounds
