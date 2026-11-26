import ExpansionBounds.Trig12.R13_0
import ExpansionBounds.Trig12.R13_1

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 13

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s13 : trig12Tab.run sinCQ trig12Tab.FsQ 13 18 0 17 (trig12Tab.init sinCQ trig12Tab.FsQ 18) =
    dySt trig12_s13_17 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 13 18 _ 2 15 trig12_s13_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 13 18 _ 2 13 trig12_s13_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 13 18 _ 2 11 trig12_s13_4_6
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 13 18 _ 2 9 trig12_s13_6_8
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 13 18 _ 2 7 trig12_s13_8_10
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 13 18 _ 2 5 trig12_s13_10_12
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 13 18 _ 2 3 trig12_s13_12_14
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 13 18 _ 2 1 trig12_s13_14_16
    (trig12_s13_16_17))))))))

theorem trig12_c13 : trig12Tab.run cosCQ trig12Tab.FcQ 13 19 0 18 (trig12Tab.init cosCQ trig12Tab.FcQ 19) =
    dySt trig12_c13_18 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 13 19 _ 2 16 trig12_c13_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 13 19 _ 2 14 trig12_c13_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 13 19 _ 2 12 trig12_c13_4_6
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 13 19 _ 2 10 trig12_c13_6_8
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 13 19 _ 2 8 trig12_c13_8_10
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 13 19 _ 2 6 trig12_c13_10_12
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 13 19 _ 2 4 trig12_c13_12_14
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 13 19 _ 2 2 trig12_c13_14_16
    (trig12_c13_16_18))))))))

set_option maxHeartbeats 4000000 in
theorem trig12_ok13 : trig12Tab.Ok trig12C 13 19 20 (dySt trig12_s13_17) (dySt trig12_c13_18) := by
  decide +kernel

theorem trig12_g13 : trig12Tab.Group trig12C (13, 19, 20) :=
  ⟨_, _, trig12_s13, trig12_c13, trig12_ok13⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok13 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 13 19 20 (dySt trig12_s13_17) (dySt trig12_c13_18) := by
  decide +kernel

theorem tan12_g13 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (13, 19, 20) :=
  ⟨_, _, trig12_s13, trig12_c13, tan12_ok13⟩

end ExpansionBounds
