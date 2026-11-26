import ExpansionBounds.Trig12.R5_0
import ExpansionBounds.Trig12.R5_1
import ExpansionBounds.Trig12.R5_2

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 5

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s5 : trig12Tab.run sinCQ trig12Tab.FsQ 5 33 0 32 (trig12Tab.init sinCQ trig12Tab.FsQ 33) =
    dySt trig12_s5_32 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 5 33 _ 2 30 trig12_s5_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 5 33 _ 2 28 trig12_s5_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 5 33 _ 2 26 trig12_s5_4_6
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 5 33 _ 2 24 trig12_s5_6_8
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 5 33 _ 2 22 trig12_s5_8_10
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 5 33 _ 2 20 trig12_s5_10_12
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 5 33 _ 2 18 trig12_s5_12_14
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 5 33 _ 2 16 trig12_s5_14_16
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 5 33 _ 2 14 trig12_s5_16_18
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 5 33 _ 2 12 trig12_s5_18_20
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 5 33 _ 2 10 trig12_s5_20_22
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 5 33 _ 2 8 trig12_s5_22_24
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 5 33 _ 2 6 trig12_s5_24_26
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 5 33 _ 2 4 trig12_s5_26_28
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 5 33 _ 2 2 trig12_s5_28_30
    (trig12_s5_30_32)))))))))))))))

theorem trig12_c5 : trig12Tab.run cosCQ trig12Tab.FcQ 5 33 0 32 (trig12Tab.init cosCQ trig12Tab.FcQ 33) =
    dySt trig12_c5_32 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 5 33 _ 2 30 trig12_c5_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 5 33 _ 2 28 trig12_c5_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 5 33 _ 2 26 trig12_c5_4_6
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 5 33 _ 2 24 trig12_c5_6_8
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 5 33 _ 2 22 trig12_c5_8_10
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 5 33 _ 2 20 trig12_c5_10_12
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 5 33 _ 2 18 trig12_c5_12_14
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 5 33 _ 2 16 trig12_c5_14_16
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 5 33 _ 2 14 trig12_c5_16_18
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 5 33 _ 2 12 trig12_c5_18_20
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 5 33 _ 2 10 trig12_c5_20_22
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 5 33 _ 2 8 trig12_c5_22_24
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 5 33 _ 2 6 trig12_c5_24_26
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 5 33 _ 2 4 trig12_c5_26_28
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 5 33 _ 2 2 trig12_c5_28_30
    (trig12_c5_30_32)))))))))))))))

set_option maxHeartbeats 4000000 in
theorem trig12_ok5 : trig12Tab.Ok trig12C 5 34 34 (dySt trig12_s5_32) (dySt trig12_c5_32) := by
  decide +kernel

theorem trig12_g5 : trig12Tab.Group trig12C (5, 34, 34) :=
  ⟨_, _, trig12_s5, trig12_c5, trig12_ok5⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok5 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 5 34 34 (dySt trig12_s5_32) (dySt trig12_c5_32) := by
  decide +kernel

theorem tan12_g5 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (5, 34, 34) :=
  ⟨_, _, trig12_s5, trig12_c5, tan12_ok5⟩

end ExpansionBounds
