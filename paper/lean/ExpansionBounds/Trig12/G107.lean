import ExpansionBounds.Trig12.R107_0

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 107

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s107 : trig12Tab.run sinCQ trig12Tab.FsQ 107 2 0 1 (trig12Tab.init sinCQ trig12Tab.FsQ 2) =
    dySt trig12_s107_1 :=
  trig12_s107_0_1

theorem trig12_c107 : trig12Tab.run cosCQ trig12Tab.FcQ 107 2 0 1 (trig12Tab.init cosCQ trig12Tab.FcQ 2) =
    dySt trig12_c107_1 :=
  trig12_c107_0_1

set_option maxHeartbeats 4000000 in
theorem trig12_ok107 : trig12Tab.Ok trig12C 107 3 3 (dySt trig12_s107_1) (dySt trig12_c107_1) := by
  decide +kernel

theorem trig12_g107 : trig12Tab.Group trig12C (107, 3, 3) :=
  ⟨_, _, trig12_s107, trig12_c107, trig12_ok107⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok107 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 107 3 3 (dySt trig12_s107_1) (dySt trig12_c107_1) := by
  decide +kernel

theorem tan12_g107 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (107, 3, 3) :=
  ⟨_, _, trig12_s107, trig12_c107, tan12_ok107⟩

end ExpansionBounds
