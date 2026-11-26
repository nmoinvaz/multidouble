import ExpansionBounds.Trig12.R20_0

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 20

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s20 : trig12Tab.run sinCQ trig12Tab.FsQ 20 13 0 12 (trig12Tab.init sinCQ trig12Tab.FsQ 13) =
    dySt trig12_s20_12 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 20 13 _ 2 10 trig12_s20_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 20 13 _ 2 8 trig12_s20_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 20 13 _ 2 6 trig12_s20_4_6
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 20 13 _ 2 4 trig12_s20_6_8
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 20 13 _ 2 2 trig12_s20_8_10
    (trig12_s20_10_12)))))

theorem trig12_c20 : trig12Tab.run cosCQ trig12Tab.FcQ 20 13 0 12 (trig12Tab.init cosCQ trig12Tab.FcQ 13) =
    dySt trig12_c20_12 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 20 13 _ 2 10 trig12_c20_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 20 13 _ 2 8 trig12_c20_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 20 13 _ 2 6 trig12_c20_4_6
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 20 13 _ 2 4 trig12_c20_6_8
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 20 13 _ 2 2 trig12_c20_8_10
    (trig12_c20_10_12)))))

set_option maxHeartbeats 4000000 in
theorem trig12_ok20 : trig12Tab.Ok trig12C 20 14 14 (dySt trig12_s20_12) (dySt trig12_c20_12) := by
  decide +kernel

theorem trig12_g20 : trig12Tab.Group trig12C (20, 14, 14) :=
  ⟨_, _, trig12_s20, trig12_c20, trig12_ok20⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok20 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 20 14 14 (dySt trig12_s20_12) (dySt trig12_c20_12) := by
  decide +kernel

theorem tan12_g20 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (20, 14, 14) :=
  ⟨_, _, trig12_s20, trig12_c20, tan12_ok20⟩

end ExpansionBounds
