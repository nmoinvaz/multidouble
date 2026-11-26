import ExpansionBounds.Trig12.R52_0

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 52

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s52 : trig12Tab.run sinCQ trig12Tab.FsQ 52 5 0 4 (trig12Tab.init sinCQ trig12Tab.FsQ 5) =
    dySt trig12_s52_4 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 52 5 _ 2 2 trig12_s52_0_2
    (trig12_s52_2_4)

theorem trig12_c52 : trig12Tab.run cosCQ trig12Tab.FcQ 52 5 0 4 (trig12Tab.init cosCQ trig12Tab.FcQ 5) =
    dySt trig12_c52_4 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 52 5 _ 2 2 trig12_c52_0_2
    (trig12_c52_2_4)

set_option maxHeartbeats 4000000 in
theorem trig12_ok52 : trig12Tab.Ok trig12C 52 6 6 (dySt trig12_s52_4) (dySt trig12_c52_4) := by
  decide +kernel

theorem trig12_g52 : trig12Tab.Group trig12C (52, 6, 6) :=
  ⟨_, _, trig12_s52, trig12_c52, trig12_ok52⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok52 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 52 6 6 (dySt trig12_s52_4) (dySt trig12_c52_4) := by
  decide +kernel

theorem tan12_g52 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (52, 6, 6) :=
  ⟨_, _, trig12_s52, trig12_c52, tan12_ok52⟩

end ExpansionBounds
