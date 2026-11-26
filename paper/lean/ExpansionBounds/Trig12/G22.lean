import ExpansionBounds.Trig12.R22_0

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 22

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s22 : trig12Tab.run sinCQ trig12Tab.FsQ 22 12 0 11 (trig12Tab.init sinCQ trig12Tab.FsQ 12) =
    dySt trig12_s22_11 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 22 12 _ 2 9 trig12_s22_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 22 12 _ 2 7 trig12_s22_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 22 12 _ 2 5 trig12_s22_4_6
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 22 12 _ 2 3 trig12_s22_6_8
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 22 12 _ 2 1 trig12_s22_8_10
    (trig12_s22_10_11)))))

theorem trig12_c22 : trig12Tab.run cosCQ trig12Tab.FcQ 22 12 0 11 (trig12Tab.init cosCQ trig12Tab.FcQ 12) =
    dySt trig12_c22_11 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 22 12 _ 2 9 trig12_c22_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 22 12 _ 2 7 trig12_c22_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 22 12 _ 2 5 trig12_c22_4_6
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 22 12 _ 2 3 trig12_c22_6_8
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 22 12 _ 2 1 trig12_c22_8_10
    (trig12_c22_10_11)))))

set_option maxHeartbeats 4000000 in
theorem trig12_ok22 : trig12Tab.Ok trig12C 22 13 13 (dySt trig12_s22_11) (dySt trig12_c22_11) := by
  decide +kernel

theorem trig12_g22 : trig12Tab.Group trig12C (22, 13, 13) :=
  ⟨_, _, trig12_s22, trig12_c22, trig12_ok22⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok22 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 22 13 13 (dySt trig12_s22_11) (dySt trig12_c22_11) := by
  decide +kernel

theorem tan12_g22 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (22, 13, 13) :=
  ⟨_, _, trig12_s22, trig12_c22, tan12_ok22⟩

end ExpansionBounds
