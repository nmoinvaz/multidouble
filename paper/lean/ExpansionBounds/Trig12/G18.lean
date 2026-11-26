import ExpansionBounds.Trig12.R18_0
import ExpansionBounds.Trig12.R18_1

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 18

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s18 : trig12Tab.run sinCQ trig12Tab.FsQ 18 14 0 13 (trig12Tab.init sinCQ trig12Tab.FsQ 14) =
    dySt trig12_s18_13 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 18 14 _ 2 11 trig12_s18_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 18 14 _ 2 9 trig12_s18_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 18 14 _ 2 7 trig12_s18_4_6
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 18 14 _ 2 5 trig12_s18_6_8
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 18 14 _ 2 3 trig12_s18_8_10
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 18 14 _ 2 1 trig12_s18_10_12
    (trig12_s18_12_13))))))

theorem trig12_c18 : trig12Tab.run cosCQ trig12Tab.FcQ 18 14 0 13 (trig12Tab.init cosCQ trig12Tab.FcQ 14) =
    dySt trig12_c18_13 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 18 14 _ 2 11 trig12_c18_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 18 14 _ 2 9 trig12_c18_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 18 14 _ 2 7 trig12_c18_4_6
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 18 14 _ 2 5 trig12_c18_6_8
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 18 14 _ 2 3 trig12_c18_8_10
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 18 14 _ 2 1 trig12_c18_10_12
    (trig12_c18_12_13))))))

set_option maxHeartbeats 4000000 in
theorem trig12_ok18 : trig12Tab.Ok trig12C 18 15 15 (dySt trig12_s18_13) (dySt trig12_c18_13) := by
  decide +kernel

theorem trig12_g18 : trig12Tab.Group trig12C (18, 15, 15) :=
  ⟨_, _, trig12_s18, trig12_c18, trig12_ok18⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok18 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 18 15 15 (dySt trig12_s18_13) (dySt trig12_c18_13) := by
  decide +kernel

theorem tan12_g18 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (18, 15, 15) :=
  ⟨_, _, trig12_s18, trig12_c18, tan12_ok18⟩

end ExpansionBounds
