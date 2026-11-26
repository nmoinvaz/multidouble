import ExpansionBounds.Trig12.R106_0

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 106

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s106 : trig12Tab.run sinCQ trig12Tab.FsQ 106 2 0 1 (trig12Tab.init sinCQ trig12Tab.FsQ 2) =
    dySt trig12_s106_1 :=
  trig12_s106_0_1

theorem trig12_c106 : trig12Tab.run cosCQ trig12Tab.FcQ 106 3 0 2 (trig12Tab.init cosCQ trig12Tab.FcQ 3) =
    dySt trig12_c106_2 :=
  trig12_c106_0_2

set_option maxHeartbeats 4000000 in
theorem trig12_ok106 : trig12Tab.Ok trig12C 106 3 4 (dySt trig12_s106_1) (dySt trig12_c106_2) := by
  decide +kernel

theorem trig12_g106 : trig12Tab.Group trig12C (106, 3, 4) :=
  ⟨_, _, trig12_s106, trig12_c106, trig12_ok106⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok106 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 106 3 4 (dySt trig12_s106_1) (dySt trig12_c106_2) := by
  decide +kernel

theorem tan12_g106 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (106, 3, 4) :=
  ⟨_, _, trig12_s106, trig12_c106, tan12_ok106⟩

end ExpansionBounds
