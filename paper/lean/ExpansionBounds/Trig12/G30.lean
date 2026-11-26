import ExpansionBounds.Trig12.R30_0

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 30

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s30 : trig12Tab.run sinCQ trig12Tab.FsQ 30 9 0 8 (trig12Tab.init sinCQ trig12Tab.FsQ 9) =
    dySt trig12_s30_8 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 30 9 _ 2 6 trig12_s30_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 30 9 _ 2 4 trig12_s30_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 30 9 _ 2 2 trig12_s30_4_6
    (trig12_s30_6_8)))

theorem trig12_c30 : trig12Tab.run cosCQ trig12Tab.FcQ 30 9 0 8 (trig12Tab.init cosCQ trig12Tab.FcQ 9) =
    dySt trig12_c30_8 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 30 9 _ 2 6 trig12_c30_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 30 9 _ 2 4 trig12_c30_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 30 9 _ 2 2 trig12_c30_4_6
    (trig12_c30_6_8)))

set_option maxHeartbeats 4000000 in
theorem trig12_ok30 : trig12Tab.Ok trig12C 30 10 10 (dySt trig12_s30_8) (dySt trig12_c30_8) := by
  decide +kernel

theorem trig12_g30 : trig12Tab.Group trig12C (30, 10, 10) :=
  ⟨_, _, trig12_s30, trig12_c30, trig12_ok30⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok30 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 30 10 10 (dySt trig12_s30_8) (dySt trig12_c30_8) := by
  decide +kernel

theorem tan12_g30 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (30, 10, 10) :=
  ⟨_, _, trig12_s30, trig12_c30, tan12_ok30⟩

end ExpansionBounds
