import ExpansionBounds.Trig12.R14_0
import ExpansionBounds.Trig12.R14_1

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 14

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s14 : trig12Tab.run sinCQ trig12Tab.FsQ 14 17 0 16 (trig12Tab.init sinCQ trig12Tab.FsQ 17) =
    dySt trig12_s14_16 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 14 17 _ 2 14 trig12_s14_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 14 17 _ 2 12 trig12_s14_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 14 17 _ 2 10 trig12_s14_4_6
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 14 17 _ 2 8 trig12_s14_6_8
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 14 17 _ 2 6 trig12_s14_8_10
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 14 17 _ 2 4 trig12_s14_10_12
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 14 17 _ 2 2 trig12_s14_12_14
    (trig12_s14_14_16)))))))

theorem trig12_c14 : trig12Tab.run cosCQ trig12Tab.FcQ 14 18 0 17 (trig12Tab.init cosCQ trig12Tab.FcQ 18) =
    dySt trig12_c14_17 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 14 18 _ 2 15 trig12_c14_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 14 18 _ 2 13 trig12_c14_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 14 18 _ 2 11 trig12_c14_4_6
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 14 18 _ 2 9 trig12_c14_6_8
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 14 18 _ 2 7 trig12_c14_8_10
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 14 18 _ 2 5 trig12_c14_10_12
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 14 18 _ 2 3 trig12_c14_12_14
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 14 18 _ 2 1 trig12_c14_14_16
    (trig12_c14_16_17))))))))

set_option maxHeartbeats 4000000 in
theorem trig12_ok14 : trig12Tab.Ok trig12C 14 18 19 (dySt trig12_s14_16) (dySt trig12_c14_17) := by
  decide +kernel

theorem trig12_g14 : trig12Tab.Group trig12C (14, 18, 19) :=
  ⟨_, _, trig12_s14, trig12_c14, trig12_ok14⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok14 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 14 18 19 (dySt trig12_s14_16) (dySt trig12_c14_17) := by
  decide +kernel

theorem tan12_g14 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (14, 18, 19) :=
  ⟨_, _, trig12_s14, trig12_c14, tan12_ok14⟩

end ExpansionBounds
