import ExpansionBounds.Trig12.R79_0

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 79

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s79 : trig12Tab.run sinCQ trig12Tab.FsQ 79 3 0 2 (trig12Tab.init sinCQ trig12Tab.FsQ 3) =
    dySt trig12_s79_2 :=
  trig12_s79_0_2

theorem trig12_c79 : trig12Tab.run cosCQ trig12Tab.FcQ 79 3 0 2 (trig12Tab.init cosCQ trig12Tab.FcQ 3) =
    dySt trig12_c79_2 :=
  trig12_c79_0_2

set_option maxHeartbeats 4000000 in
theorem trig12_ok79 : trig12Tab.Ok trig12C 79 4 4 (dySt trig12_s79_2) (dySt trig12_c79_2) := by
  decide +kernel

theorem trig12_g79 : trig12Tab.Group trig12C (79, 4, 4) :=
  ⟨_, _, trig12_s79, trig12_c79, trig12_ok79⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok79 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 79 4 4 (dySt trig12_s79_2) (dySt trig12_c79_2) := by
  decide +kernel

theorem tan12_g79 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (79, 4, 4) :=
  ⟨_, _, trig12_s79, trig12_c79, tan12_ok79⟩

end ExpansionBounds
