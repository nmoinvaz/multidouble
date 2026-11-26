import ExpansionBounds.Trig12.R26_0

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 26

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s26 : trig12Tab.run sinCQ trig12Tab.FsQ 26 10 0 9 (trig12Tab.init sinCQ trig12Tab.FsQ 10) =
    dySt trig12_s26_9 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 26 10 _ 2 7 trig12_s26_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 26 10 _ 2 5 trig12_s26_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 26 10 _ 2 3 trig12_s26_4_6
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 26 10 _ 2 1 trig12_s26_6_8
    (trig12_s26_8_9))))

theorem trig12_c26 : trig12Tab.run cosCQ trig12Tab.FcQ 26 11 0 10 (trig12Tab.init cosCQ trig12Tab.FcQ 11) =
    dySt trig12_c26_10 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 26 11 _ 2 8 trig12_c26_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 26 11 _ 2 6 trig12_c26_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 26 11 _ 2 4 trig12_c26_4_6
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 26 11 _ 2 2 trig12_c26_6_8
    (trig12_c26_8_10))))

set_option maxHeartbeats 4000000 in
theorem trig12_ok26 : trig12Tab.Ok trig12C 26 11 12 (dySt trig12_s26_9) (dySt trig12_c26_10) := by
  decide +kernel

theorem trig12_g26 : trig12Tab.Group trig12C (26, 11, 12) :=
  ⟨_, _, trig12_s26, trig12_c26, trig12_ok26⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok26 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 26 11 12 (dySt trig12_s26_9) (dySt trig12_c26_10) := by
  decide +kernel

theorem tan12_g26 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (26, 11, 12) :=
  ⟨_, _, trig12_s26, trig12_c26, tan12_ok26⟩

end ExpansionBounds
