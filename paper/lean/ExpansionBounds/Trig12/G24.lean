import ExpansionBounds.Trig12.R24_0

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 24

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s24 : trig12Tab.run sinCQ trig12Tab.FsQ 24 11 0 10 (trig12Tab.init sinCQ trig12Tab.FsQ 11) =
    dySt trig12_s24_10 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 24 11 _ 2 8 trig12_s24_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 24 11 _ 2 6 trig12_s24_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 24 11 _ 2 4 trig12_s24_4_6
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 24 11 _ 2 2 trig12_s24_6_8
    (trig12_s24_8_10))))

theorem trig12_c24 : trig12Tab.run cosCQ trig12Tab.FcQ 24 11 0 10 (trig12Tab.init cosCQ trig12Tab.FcQ 11) =
    dySt trig12_c24_10 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 24 11 _ 2 8 trig12_c24_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 24 11 _ 2 6 trig12_c24_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 24 11 _ 2 4 trig12_c24_4_6
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 24 11 _ 2 2 trig12_c24_6_8
    (trig12_c24_8_10))))

set_option maxHeartbeats 4000000 in
theorem trig12_ok24 : trig12Tab.Ok trig12C 24 12 12 (dySt trig12_s24_10) (dySt trig12_c24_10) := by
  decide +kernel

theorem trig12_g24 : trig12Tab.Group trig12C (24, 12, 12) :=
  ⟨_, _, trig12_s24, trig12_c24, trig12_ok24⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok24 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 24 12 12 (dySt trig12_s24_10) (dySt trig12_c24_10) := by
  decide +kernel

theorem tan12_g24 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (24, 12, 12) :=
  ⟨_, _, trig12_s24, trig12_c24, tan12_ok24⟩

end ExpansionBounds
