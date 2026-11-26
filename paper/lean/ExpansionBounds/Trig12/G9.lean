import ExpansionBounds.Trig12.R9_0
import ExpansionBounds.Trig12.R9_1

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 9

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s9 : trig12Tab.run sinCQ trig12Tab.FsQ 9 24 0 23 (trig12Tab.init sinCQ trig12Tab.FsQ 24) =
    dySt trig12_s9_23 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 9 24 _ 2 21 trig12_s9_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 9 24 _ 2 19 trig12_s9_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 9 24 _ 2 17 trig12_s9_4_6
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 9 24 _ 2 15 trig12_s9_6_8
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 9 24 _ 2 13 trig12_s9_8_10
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 9 24 _ 2 11 trig12_s9_10_12
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 9 24 _ 2 9 trig12_s9_12_14
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 9 24 _ 2 7 trig12_s9_14_16
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 9 24 _ 2 5 trig12_s9_16_18
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 9 24 _ 2 3 trig12_s9_18_20
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 9 24 _ 2 1 trig12_s9_20_22
    (trig12_s9_22_23)))))))))))

theorem trig12_c9 : trig12Tab.run cosCQ trig12Tab.FcQ 9 24 0 23 (trig12Tab.init cosCQ trig12Tab.FcQ 24) =
    dySt trig12_c9_23 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 9 24 _ 2 21 trig12_c9_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 9 24 _ 2 19 trig12_c9_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 9 24 _ 2 17 trig12_c9_4_6
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 9 24 _ 2 15 trig12_c9_6_8
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 9 24 _ 2 13 trig12_c9_8_10
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 9 24 _ 2 11 trig12_c9_10_12
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 9 24 _ 2 9 trig12_c9_12_14
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 9 24 _ 2 7 trig12_c9_14_16
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 9 24 _ 2 5 trig12_c9_16_18
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 9 24 _ 2 3 trig12_c9_18_20
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 9 24 _ 2 1 trig12_c9_20_22
    (trig12_c9_22_23)))))))))))

set_option maxHeartbeats 4000000 in
theorem trig12_ok9 : trig12Tab.Ok trig12C 9 25 25 (dySt trig12_s9_23) (dySt trig12_c9_23) := by
  decide +kernel

theorem trig12_g9 : trig12Tab.Group trig12C (9, 25, 25) :=
  ⟨_, _, trig12_s9, trig12_c9, trig12_ok9⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok9 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 9 25 25 (dySt trig12_s9_23) (dySt trig12_c9_23) := by
  decide +kernel

theorem tan12_g9 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (9, 25, 25) :=
  ⟨_, _, trig12_s9, trig12_c9, tan12_ok9⟩

end ExpansionBounds
