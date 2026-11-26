import ExpansionBounds.Trig12.R12_0
import ExpansionBounds.Trig12.R12_1

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 12

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s12 : trig12Tab.run sinCQ trig12Tab.FsQ 12 20 0 19 (trig12Tab.init sinCQ trig12Tab.FsQ 20) =
    dySt trig12_s12_19 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 12 20 _ 2 17 trig12_s12_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 12 20 _ 2 15 trig12_s12_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 12 20 _ 2 13 trig12_s12_4_6
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 12 20 _ 2 11 trig12_s12_6_8
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 12 20 _ 2 9 trig12_s12_8_10
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 12 20 _ 2 7 trig12_s12_10_12
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 12 20 _ 2 5 trig12_s12_12_14
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 12 20 _ 2 3 trig12_s12_14_16
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 12 20 _ 2 1 trig12_s12_16_18
    (trig12_s12_18_19)))))))))

theorem trig12_c12 : trig12Tab.run cosCQ trig12Tab.FcQ 12 20 0 19 (trig12Tab.init cosCQ trig12Tab.FcQ 20) =
    dySt trig12_c12_19 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 12 20 _ 2 17 trig12_c12_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 12 20 _ 2 15 trig12_c12_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 12 20 _ 2 13 trig12_c12_4_6
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 12 20 _ 2 11 trig12_c12_6_8
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 12 20 _ 2 9 trig12_c12_8_10
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 12 20 _ 2 7 trig12_c12_10_12
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 12 20 _ 2 5 trig12_c12_12_14
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 12 20 _ 2 3 trig12_c12_14_16
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 12 20 _ 2 1 trig12_c12_16_18
    (trig12_c12_18_19)))))))))

set_option maxHeartbeats 4000000 in
theorem trig12_ok12 : trig12Tab.Ok trig12C 12 21 21 (dySt trig12_s12_19) (dySt trig12_c12_19) := by
  decide +kernel

theorem trig12_g12 : trig12Tab.Group trig12C (12, 21, 21) :=
  ⟨_, _, trig12_s12, trig12_c12, trig12_ok12⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok12 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 12 21 21 (dySt trig12_s12_19) (dySt trig12_c12_19) := by
  decide +kernel

theorem tan12_g12 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (12, 21, 21) :=
  ⟨_, _, trig12_s12, trig12_c12, tan12_ok12⟩

end ExpansionBounds
