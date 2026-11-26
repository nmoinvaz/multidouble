import ExpansionBounds.Trig12.R7_0
import ExpansionBounds.Trig12.R7_1
import ExpansionBounds.Trig12.R7_2

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 7

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s7 : trig12Tab.run sinCQ trig12Tab.FsQ 7 27 0 26 (trig12Tab.init sinCQ trig12Tab.FsQ 27) =
    dySt trig12_s7_26 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 7 27 _ 2 24 trig12_s7_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 7 27 _ 2 22 trig12_s7_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 7 27 _ 2 20 trig12_s7_4_6
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 7 27 _ 2 18 trig12_s7_6_8
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 7 27 _ 2 16 trig12_s7_8_10
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 7 27 _ 2 14 trig12_s7_10_12
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 7 27 _ 2 12 trig12_s7_12_14
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 7 27 _ 2 10 trig12_s7_14_16
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 7 27 _ 2 8 trig12_s7_16_18
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 7 27 _ 2 6 trig12_s7_18_20
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 7 27 _ 2 4 trig12_s7_20_22
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 7 27 _ 2 2 trig12_s7_22_24
    (trig12_s7_24_26))))))))))))

theorem trig12_c7 : trig12Tab.run cosCQ trig12Tab.FcQ 7 28 0 27 (trig12Tab.init cosCQ trig12Tab.FcQ 28) =
    dySt trig12_c7_27 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 7 28 _ 2 25 trig12_c7_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 7 28 _ 2 23 trig12_c7_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 7 28 _ 2 21 trig12_c7_4_6
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 7 28 _ 2 19 trig12_c7_6_8
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 7 28 _ 2 17 trig12_c7_8_10
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 7 28 _ 2 15 trig12_c7_10_12
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 7 28 _ 2 13 trig12_c7_12_14
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 7 28 _ 2 11 trig12_c7_14_16
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 7 28 _ 2 9 trig12_c7_16_18
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 7 28 _ 2 7 trig12_c7_18_20
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 7 28 _ 2 5 trig12_c7_20_22
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 7 28 _ 2 3 trig12_c7_22_24
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 7 28 _ 2 1 trig12_c7_24_26
    (trig12_c7_26_27)))))))))))))

set_option maxHeartbeats 4000000 in
theorem trig12_ok7 : trig12Tab.Ok trig12C 7 28 29 (dySt trig12_s7_26) (dySt trig12_c7_27) := by
  decide +kernel

theorem trig12_g7 : trig12Tab.Group trig12C (7, 28, 29) :=
  ⟨_, _, trig12_s7, trig12_c7, trig12_ok7⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok7 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 7 28 29 (dySt trig12_s7_26) (dySt trig12_c7_27) := by
  decide +kernel

theorem tan12_g7 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (7, 28, 29) :=
  ⟨_, _, trig12_s7, trig12_c7, tan12_ok7⟩

end ExpansionBounds
