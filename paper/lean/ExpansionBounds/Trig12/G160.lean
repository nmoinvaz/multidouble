import ExpansionBounds.Trig12.R160_0

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 160

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s160 : trig12Tab.run sinCQ trig12Tab.FsQ 160 1 0 0 (trig12Tab.init sinCQ trig12Tab.FsQ 1) =
    trig12Tab.init sinCQ trig12Tab.FsQ 1 := rfl

theorem trig12_c160 : trig12Tab.run cosCQ trig12Tab.FcQ 160 2 0 1 (trig12Tab.init cosCQ trig12Tab.FcQ 2) =
    dySt trig12_c160_1 :=
  trig12_c160_0_1

set_option maxHeartbeats 4000000 in
theorem trig12_ok160 : trig12Tab.Ok trig12C 160 2 3 (trig12Tab.init sinCQ trig12Tab.FsQ 1) (dySt trig12_c160_1) := by
  decide +kernel

theorem trig12_g160 : trig12Tab.Group trig12C (160, 2, 3) :=
  ⟨_, _, trig12_s160, trig12_c160, trig12_ok160⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok160 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 160 2 3 (trig12Tab.init sinCQ trig12Tab.FsQ 1) (dySt trig12_c160_1) := by
  decide +kernel

theorem tan12_g160 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (160, 2, 3) :=
  ⟨_, _, trig12_s160, trig12_c160, tan12_ok160⟩

end ExpansionBounds
