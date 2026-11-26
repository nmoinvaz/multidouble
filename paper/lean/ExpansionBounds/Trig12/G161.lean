import ExpansionBounds.Trig12.S161

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 161

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s161 : trig12Tab.run sinCQ trig12Tab.FsQ 161 1 0 0 (trig12Tab.init sinCQ trig12Tab.FsQ 1) =
    trig12Tab.init sinCQ trig12Tab.FsQ 1 := rfl

theorem trig12_c161 : trig12Tab.run cosCQ trig12Tab.FcQ 161 1 0 0 (trig12Tab.init cosCQ trig12Tab.FcQ 1) =
    trig12Tab.init cosCQ trig12Tab.FcQ 1 := rfl

set_option maxHeartbeats 4000000 in
theorem trig12_ok161 : trig12Tab.Ok trig12C 161 2 2 (trig12Tab.init sinCQ trig12Tab.FsQ 1) (trig12Tab.init cosCQ trig12Tab.FcQ 1) := by
  decide +kernel

theorem trig12_g161 : trig12Tab.Group trig12C (161, 2, 2) :=
  ⟨_, _, trig12_s161, trig12_c161, trig12_ok161⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok161 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 161 2 2 (trig12Tab.init sinCQ trig12Tab.FsQ 1) (trig12Tab.init cosCQ trig12Tab.FcQ 1) := by
  decide +kernel

theorem tan12_g161 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (161, 2, 2) :=
  ⟨_, _, trig12_s161, trig12_c161, tan12_ok161⟩

end ExpansionBounds
