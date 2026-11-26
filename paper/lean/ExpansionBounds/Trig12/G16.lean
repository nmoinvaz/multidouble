import ExpansionBounds.Trig12.R16_0
import ExpansionBounds.Trig12.R16_1

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 16

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s16 : trig12Tab.run sinCQ trig12Tab.FsQ 16 16 0 15 (trig12Tab.init sinCQ trig12Tab.FsQ 16) =
    dySt trig12_s16_15 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 16 16 _ 2 13 trig12_s16_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 16 16 _ 2 11 trig12_s16_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 16 16 _ 2 9 trig12_s16_4_6
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 16 16 _ 2 7 trig12_s16_6_8
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 16 16 _ 2 5 trig12_s16_8_10
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 16 16 _ 2 3 trig12_s16_10_12
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 16 16 _ 2 1 trig12_s16_12_14
    (trig12_s16_14_15)))))))

theorem trig12_c16 : trig12Tab.run cosCQ trig12Tab.FcQ 16 16 0 15 (trig12Tab.init cosCQ trig12Tab.FcQ 16) =
    dySt trig12_c16_15 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 16 16 _ 2 13 trig12_c16_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 16 16 _ 2 11 trig12_c16_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 16 16 _ 2 9 trig12_c16_4_6
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 16 16 _ 2 7 trig12_c16_6_8
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 16 16 _ 2 5 trig12_c16_8_10
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 16 16 _ 2 3 trig12_c16_10_12
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 16 16 _ 2 1 trig12_c16_12_14
    (trig12_c16_14_15)))))))

set_option maxHeartbeats 4000000 in
theorem trig12_ok16 : trig12Tab.Ok trig12C 16 17 17 (dySt trig12_s16_15) (dySt trig12_c16_15) := by
  decide +kernel

theorem trig12_g16 : trig12Tab.Group trig12C (16, 17, 17) :=
  ⟨_, _, trig12_s16, trig12_c16, trig12_ok16⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok16 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 16 17 17 (dySt trig12_s16_15) (dySt trig12_c16_15) := by
  decide +kernel

theorem tan12_g16 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (16, 17, 17) :=
  ⟨_, _, trig12_s16, trig12_c16, tan12_ok16⟩

end ExpansionBounds
