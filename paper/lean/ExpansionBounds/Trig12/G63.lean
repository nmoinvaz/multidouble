import ExpansionBounds.Trig12.R63_0

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 63

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s63 : trig12Tab.run sinCQ trig12Tab.FsQ 63 4 0 3 (trig12Tab.init sinCQ trig12Tab.FsQ 4) =
    dySt trig12_s63_3 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 63 4 _ 2 1 trig12_s63_0_2
    (trig12_s63_2_3)

theorem trig12_c63 : trig12Tab.run cosCQ trig12Tab.FcQ 63 4 0 3 (trig12Tab.init cosCQ trig12Tab.FcQ 4) =
    dySt trig12_c63_3 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 63 4 _ 2 1 trig12_c63_0_2
    (trig12_c63_2_3)

set_option maxHeartbeats 4000000 in
theorem trig12_ok63 : trig12Tab.Ok trig12C 63 5 5 (dySt trig12_s63_3) (dySt trig12_c63_3) := by
  decide +kernel

theorem trig12_g63 : trig12Tab.Group trig12C (63, 5, 5) :=
  ⟨_, _, trig12_s63, trig12_c63, trig12_ok63⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok63 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 63 5 5 (dySt trig12_s63_3) (dySt trig12_c63_3) := by
  decide +kernel

theorem tan12_g63 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (63, 5, 5) :=
  ⟨_, _, trig12_s63, trig12_c63, tan12_ok63⟩

end ExpansionBounds
