import ExpansionBounds.Trig12.R33_0

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 33

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s33 : trig12Tab.run sinCQ trig12Tab.FsQ 33 8 0 7 (trig12Tab.init sinCQ trig12Tab.FsQ 8) =
    dySt trig12_s33_7 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 33 8 _ 2 5 trig12_s33_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 33 8 _ 2 3 trig12_s33_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 33 8 _ 2 1 trig12_s33_4_6
    (trig12_s33_6_7)))

theorem trig12_c33 : trig12Tab.run cosCQ trig12Tab.FcQ 33 8 0 7 (trig12Tab.init cosCQ trig12Tab.FcQ 8) =
    dySt trig12_c33_7 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 33 8 _ 2 5 trig12_c33_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 33 8 _ 2 3 trig12_c33_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 33 8 _ 2 1 trig12_c33_4_6
    (trig12_c33_6_7)))

set_option maxHeartbeats 4000000 in
theorem trig12_ok33 : trig12Tab.Ok trig12C 33 9 9 (dySt trig12_s33_7) (dySt trig12_c33_7) := by
  decide +kernel

theorem trig12_g33 : trig12Tab.Group trig12C (33, 9, 9) :=
  ⟨_, _, trig12_s33, trig12_c33, trig12_ok33⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok33 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 33 9 9 (dySt trig12_s33_7) (dySt trig12_c33_7) := by
  decide +kernel

theorem tan12_g33 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (33, 9, 9) :=
  ⟨_, _, trig12_s33, trig12_c33, tan12_ok33⟩

end ExpansionBounds
