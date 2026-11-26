import ExpansionBounds.Trig12.R17_0
import ExpansionBounds.Trig12.R17_1

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 17

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s17 : trig12Tab.run sinCQ trig12Tab.FsQ 17 15 0 14 (trig12Tab.init sinCQ trig12Tab.FsQ 15) =
    dySt trig12_s17_14 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 17 15 _ 2 12 trig12_s17_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 17 15 _ 2 10 trig12_s17_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 17 15 _ 2 8 trig12_s17_4_6
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 17 15 _ 2 6 trig12_s17_6_8
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 17 15 _ 2 4 trig12_s17_8_10
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 17 15 _ 2 2 trig12_s17_10_12
    (trig12_s17_12_14))))))

theorem trig12_c17 : trig12Tab.run cosCQ trig12Tab.FcQ 17 15 0 14 (trig12Tab.init cosCQ trig12Tab.FcQ 15) =
    dySt trig12_c17_14 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 17 15 _ 2 12 trig12_c17_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 17 15 _ 2 10 trig12_c17_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 17 15 _ 2 8 trig12_c17_4_6
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 17 15 _ 2 6 trig12_c17_6_8
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 17 15 _ 2 4 trig12_c17_8_10
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 17 15 _ 2 2 trig12_c17_10_12
    (trig12_c17_12_14))))))

set_option maxHeartbeats 4000000 in
theorem trig12_ok17 : trig12Tab.Ok trig12C 17 16 16 (dySt trig12_s17_14) (dySt trig12_c17_14) := by
  decide +kernel

theorem trig12_g17 : trig12Tab.Group trig12C (17, 16, 16) :=
  ⟨_, _, trig12_s17, trig12_c17, trig12_ok17⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok17 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 17 16 16 (dySt trig12_s17_14) (dySt trig12_c17_14) := by
  decide +kernel

theorem tan12_g17 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (17, 16, 16) :=
  ⟨_, _, trig12_s17, trig12_c17, tan12_ok17⟩

end ExpansionBounds
