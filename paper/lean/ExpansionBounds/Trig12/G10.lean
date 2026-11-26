import ExpansionBounds.Trig12.R10_0
import ExpansionBounds.Trig12.R10_1

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 10

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s10 : trig12Tab.run sinCQ trig12Tab.FsQ 10 22 0 21 (trig12Tab.init sinCQ trig12Tab.FsQ 22) =
    dySt trig12_s10_21 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 10 22 _ 2 19 trig12_s10_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 10 22 _ 2 17 trig12_s10_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 10 22 _ 2 15 trig12_s10_4_6
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 10 22 _ 2 13 trig12_s10_6_8
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 10 22 _ 2 11 trig12_s10_8_10
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 10 22 _ 2 9 trig12_s10_10_12
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 10 22 _ 2 7 trig12_s10_12_14
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 10 22 _ 2 5 trig12_s10_14_16
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 10 22 _ 2 3 trig12_s10_16_18
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 10 22 _ 2 1 trig12_s10_18_20
    (trig12_s10_20_21))))))))))

theorem trig12_c10 : trig12Tab.run cosCQ trig12Tab.FcQ 10 22 0 21 (trig12Tab.init cosCQ trig12Tab.FcQ 22) =
    dySt trig12_c10_21 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 10 22 _ 2 19 trig12_c10_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 10 22 _ 2 17 trig12_c10_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 10 22 _ 2 15 trig12_c10_4_6
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 10 22 _ 2 13 trig12_c10_6_8
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 10 22 _ 2 11 trig12_c10_8_10
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 10 22 _ 2 9 trig12_c10_10_12
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 10 22 _ 2 7 trig12_c10_12_14
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 10 22 _ 2 5 trig12_c10_14_16
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 10 22 _ 2 3 trig12_c10_16_18
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 10 22 _ 2 1 trig12_c10_18_20
    (trig12_c10_20_21))))))))))

set_option maxHeartbeats 4000000 in
theorem trig12_ok10 : trig12Tab.Ok trig12C 10 23 23 (dySt trig12_s10_21) (dySt trig12_c10_21) := by
  decide +kernel

theorem trig12_g10 : trig12Tab.Group trig12C (10, 23, 23) :=
  ⟨_, _, trig12_s10, trig12_c10, trig12_ok10⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok10 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 10 23 23 (dySt trig12_s10_21) (dySt trig12_c10_21) := by
  decide +kernel

theorem tan12_g10 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (10, 23, 23) :=
  ⟨_, _, trig12_s10, trig12_c10, tan12_ok10⟩

end ExpansionBounds
