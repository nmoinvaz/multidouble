import ExpansionBounds.Trig12.R6_0
import ExpansionBounds.Trig12.R6_1
import ExpansionBounds.Trig12.R6_2

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 6

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s6 : trig12Tab.run sinCQ trig12Tab.FsQ 6 30 0 29 (trig12Tab.init sinCQ trig12Tab.FsQ 30) =
    dySt trig12_s6_29 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 6 30 _ 2 27 trig12_s6_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 6 30 _ 2 25 trig12_s6_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 6 30 _ 2 23 trig12_s6_4_6
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 6 30 _ 2 21 trig12_s6_6_8
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 6 30 _ 2 19 trig12_s6_8_10
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 6 30 _ 2 17 trig12_s6_10_12
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 6 30 _ 2 15 trig12_s6_12_14
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 6 30 _ 2 13 trig12_s6_14_16
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 6 30 _ 2 11 trig12_s6_16_18
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 6 30 _ 2 9 trig12_s6_18_20
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 6 30 _ 2 7 trig12_s6_20_22
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 6 30 _ 2 5 trig12_s6_22_24
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 6 30 _ 2 3 trig12_s6_24_26
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 6 30 _ 2 1 trig12_s6_26_28
    (trig12_s6_28_29))))))))))))))

theorem trig12_c6 : trig12Tab.run cosCQ trig12Tab.FcQ 6 30 0 29 (trig12Tab.init cosCQ trig12Tab.FcQ 30) =
    dySt trig12_c6_29 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 6 30 _ 2 27 trig12_c6_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 6 30 _ 2 25 trig12_c6_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 6 30 _ 2 23 trig12_c6_4_6
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 6 30 _ 2 21 trig12_c6_6_8
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 6 30 _ 2 19 trig12_c6_8_10
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 6 30 _ 2 17 trig12_c6_10_12
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 6 30 _ 2 15 trig12_c6_12_14
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 6 30 _ 2 13 trig12_c6_14_16
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 6 30 _ 2 11 trig12_c6_16_18
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 6 30 _ 2 9 trig12_c6_18_20
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 6 30 _ 2 7 trig12_c6_20_22
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 6 30 _ 2 5 trig12_c6_22_24
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 6 30 _ 2 3 trig12_c6_24_26
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 6 30 _ 2 1 trig12_c6_26_28
    (trig12_c6_28_29))))))))))))))

set_option maxHeartbeats 4000000 in
theorem trig12_ok6 : trig12Tab.Ok trig12C 6 31 31 (dySt trig12_s6_29) (dySt trig12_c6_29) := by
  decide +kernel

theorem trig12_g6 : trig12Tab.Group trig12C (6, 31, 31) :=
  ⟨_, _, trig12_s6, trig12_c6, trig12_ok6⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok6 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 6 31 31 (dySt trig12_s6_29) (dySt trig12_c6_29) := by
  decide +kernel

theorem tan12_g6 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (6, 31, 31) :=
  ⟨_, _, trig12_s6, trig12_c6, tan12_ok6⟩

end ExpansionBounds
