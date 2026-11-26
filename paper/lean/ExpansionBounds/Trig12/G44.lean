import ExpansionBounds.Trig12.R44_0

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 44

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s44 : trig12Tab.run sinCQ trig12Tab.FsQ 44 6 0 5 (trig12Tab.init sinCQ trig12Tab.FsQ 6) =
    dySt trig12_s44_5 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 44 6 _ 2 3 trig12_s44_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 44 6 _ 2 1 trig12_s44_2_4
    (trig12_s44_4_5))

theorem trig12_c44 : trig12Tab.run cosCQ trig12Tab.FcQ 44 6 0 5 (trig12Tab.init cosCQ trig12Tab.FcQ 6) =
    dySt trig12_c44_5 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 44 6 _ 2 3 trig12_c44_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 44 6 _ 2 1 trig12_c44_2_4
    (trig12_c44_4_5))

set_option maxHeartbeats 4000000 in
theorem trig12_ok44 : trig12Tab.Ok trig12C 44 7 7 (dySt trig12_s44_5) (dySt trig12_c44_5) := by
  decide +kernel

theorem trig12_g44 : trig12Tab.Group trig12C (44, 7, 7) :=
  ⟨_, _, trig12_s44, trig12_c44, trig12_ok44⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok44 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 44 7 7 (dySt trig12_s44_5) (dySt trig12_c44_5) := by
  decide +kernel

theorem tan12_g44 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (44, 7, 7) :=
  ⟨_, _, trig12_s44, trig12_c44, tan12_ok44⟩

end ExpansionBounds
