import ExpansionBounds.Trig12.R38_0

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 38

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s38 : trig12Tab.run sinCQ trig12Tab.FsQ 38 7 0 6 (trig12Tab.init sinCQ trig12Tab.FsQ 7) =
    dySt trig12_s38_6 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 38 7 _ 2 4 trig12_s38_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 38 7 _ 2 2 trig12_s38_2_4
    (trig12_s38_4_6))

theorem trig12_c38 : trig12Tab.run cosCQ trig12Tab.FcQ 38 7 0 6 (trig12Tab.init cosCQ trig12Tab.FcQ 7) =
    dySt trig12_c38_6 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 38 7 _ 2 4 trig12_c38_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 38 7 _ 2 2 trig12_c38_2_4
    (trig12_c38_4_6))

set_option maxHeartbeats 4000000 in
theorem trig12_ok38 : trig12Tab.Ok trig12C 38 8 8 (dySt trig12_s38_6) (dySt trig12_c38_6) := by
  decide +kernel

theorem trig12_g38 : trig12Tab.Group trig12C (38, 8, 8) :=
  ⟨_, _, trig12_s38, trig12_c38, trig12_ok38⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok38 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 38 8 8 (dySt trig12_s38_6) (dySt trig12_c38_6) := by
  decide +kernel

theorem tan12_g38 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (38, 8, 8) :=
  ⟨_, _, trig12_s38, trig12_c38, tan12_ok38⟩

end ExpansionBounds
