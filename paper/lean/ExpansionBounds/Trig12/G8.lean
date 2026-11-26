import ExpansionBounds.Trig12.R8_0
import ExpansionBounds.Trig12.R8_1
import ExpansionBounds.Trig12.R8_2

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 8

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s8 : trig12Tab.run sinCQ trig12Tab.FsQ 8 25 0 24 (trig12Tab.init sinCQ trig12Tab.FsQ 25) =
    dySt trig12_s8_24 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 8 25 _ 2 22 trig12_s8_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 8 25 _ 2 20 trig12_s8_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 8 25 _ 2 18 trig12_s8_4_6
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 8 25 _ 2 16 trig12_s8_6_8
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 8 25 _ 2 14 trig12_s8_8_10
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 8 25 _ 2 12 trig12_s8_10_12
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 8 25 _ 2 10 trig12_s8_12_14
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 8 25 _ 2 8 trig12_s8_14_16
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 8 25 _ 2 6 trig12_s8_16_18
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 8 25 _ 2 4 trig12_s8_18_20
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 8 25 _ 2 2 trig12_s8_20_22
    (trig12_s8_22_24)))))))))))

theorem trig12_c8 : trig12Tab.run cosCQ trig12Tab.FcQ 8 26 0 25 (trig12Tab.init cosCQ trig12Tab.FcQ 26) =
    dySt trig12_c8_25 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 8 26 _ 2 23 trig12_c8_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 8 26 _ 2 21 trig12_c8_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 8 26 _ 2 19 trig12_c8_4_6
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 8 26 _ 2 17 trig12_c8_6_8
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 8 26 _ 2 15 trig12_c8_8_10
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 8 26 _ 2 13 trig12_c8_10_12
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 8 26 _ 2 11 trig12_c8_12_14
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 8 26 _ 2 9 trig12_c8_14_16
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 8 26 _ 2 7 trig12_c8_16_18
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 8 26 _ 2 5 trig12_c8_18_20
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 8 26 _ 2 3 trig12_c8_20_22
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 8 26 _ 2 1 trig12_c8_22_24
    (trig12_c8_24_25))))))))))))

set_option maxHeartbeats 4000000 in
theorem trig12_ok8 : trig12Tab.Ok trig12C 8 26 27 (dySt trig12_s8_24) (dySt trig12_c8_25) := by
  decide +kernel

theorem trig12_g8 : trig12Tab.Group trig12C (8, 26, 27) :=
  ⟨_, _, trig12_s8, trig12_c8, trig12_ok8⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok8 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 8 26 27 (dySt trig12_s8_24) (dySt trig12_c8_25) := by
  decide +kernel

theorem tan12_g8 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (8, 26, 27) :=
  ⟨_, _, trig12_s8, trig12_c8, tan12_ok8⟩

end ExpansionBounds
