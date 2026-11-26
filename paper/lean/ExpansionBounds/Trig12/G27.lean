import ExpansionBounds.Trig12.R27_0

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 27

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s27 : trig12Tab.run sinCQ trig12Tab.FsQ 27 10 0 9 (trig12Tab.init sinCQ trig12Tab.FsQ 10) =
    dySt trig12_s27_9 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 27 10 _ 2 7 trig12_s27_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 27 10 _ 2 5 trig12_s27_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 27 10 _ 2 3 trig12_s27_4_6
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 27 10 _ 2 1 trig12_s27_6_8
    (trig12_s27_8_9))))

theorem trig12_c27 : trig12Tab.run cosCQ trig12Tab.FcQ 27 10 0 9 (trig12Tab.init cosCQ trig12Tab.FcQ 10) =
    dySt trig12_c27_9 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 27 10 _ 2 7 trig12_c27_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 27 10 _ 2 5 trig12_c27_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 27 10 _ 2 3 trig12_c27_4_6
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 27 10 _ 2 1 trig12_c27_6_8
    (trig12_c27_8_9))))

set_option maxHeartbeats 4000000 in
theorem trig12_ok27 : trig12Tab.Ok trig12C 27 11 11 (dySt trig12_s27_9) (dySt trig12_c27_9) := by
  decide +kernel

theorem trig12_g27 : trig12Tab.Group trig12C (27, 11, 11) :=
  ⟨_, _, trig12_s27, trig12_c27, trig12_ok27⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok27 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 27 11 11 (dySt trig12_s27_9) (dySt trig12_c27_9) := by
  decide +kernel

theorem tan12_g27 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (27, 11, 11) :=
  ⟨_, _, trig12_s27, trig12_c27, tan12_ok27⟩

end ExpansionBounds
