import ExpansionBounds.Trig12.R15_0
import ExpansionBounds.Trig12.R15_1

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 15

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s15 : trig12Tab.run sinCQ trig12Tab.FsQ 15 17 0 16 (trig12Tab.init sinCQ trig12Tab.FsQ 17) =
    dySt trig12_s15_16 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 15 17 _ 2 14 trig12_s15_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 15 17 _ 2 12 trig12_s15_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 15 17 _ 2 10 trig12_s15_4_6
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 15 17 _ 2 8 trig12_s15_6_8
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 15 17 _ 2 6 trig12_s15_8_10
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 15 17 _ 2 4 trig12_s15_10_12
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 15 17 _ 2 2 trig12_s15_12_14
    (trig12_s15_14_16)))))))

theorem trig12_c15 : trig12Tab.run cosCQ trig12Tab.FcQ 15 17 0 16 (trig12Tab.init cosCQ trig12Tab.FcQ 17) =
    dySt trig12_c15_16 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 15 17 _ 2 14 trig12_c15_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 15 17 _ 2 12 trig12_c15_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 15 17 _ 2 10 trig12_c15_4_6
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 15 17 _ 2 8 trig12_c15_6_8
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 15 17 _ 2 6 trig12_c15_8_10
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 15 17 _ 2 4 trig12_c15_10_12
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 15 17 _ 2 2 trig12_c15_12_14
    (trig12_c15_14_16)))))))

set_option maxHeartbeats 4000000 in
theorem trig12_ok15 : trig12Tab.Ok trig12C 15 18 18 (dySt trig12_s15_16) (dySt trig12_c15_16) := by
  decide +kernel

theorem trig12_g15 : trig12Tab.Group trig12C (15, 18, 18) :=
  ⟨_, _, trig12_s15, trig12_c15, trig12_ok15⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok15 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 15 18 18 (dySt trig12_s15_16) (dySt trig12_c15_16) := by
  decide +kernel

theorem tan12_g15 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (15, 18, 18) :=
  ⟨_, _, trig12_s15, trig12_c15, tan12_ok15⟩

end ExpansionBounds
