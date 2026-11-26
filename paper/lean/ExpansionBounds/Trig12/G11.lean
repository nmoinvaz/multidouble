import ExpansionBounds.Trig12.R11_0
import ExpansionBounds.Trig12.R11_1

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 11

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s11 : trig12Tab.run sinCQ trig12Tab.FsQ 11 21 0 20 (trig12Tab.init sinCQ trig12Tab.FsQ 21) =
    dySt trig12_s11_20 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 11 21 _ 2 18 trig12_s11_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 11 21 _ 2 16 trig12_s11_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 11 21 _ 2 14 trig12_s11_4_6
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 11 21 _ 2 12 trig12_s11_6_8
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 11 21 _ 2 10 trig12_s11_8_10
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 11 21 _ 2 8 trig12_s11_10_12
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 11 21 _ 2 6 trig12_s11_12_14
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 11 21 _ 2 4 trig12_s11_14_16
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 11 21 _ 2 2 trig12_s11_16_18
    (trig12_s11_18_20)))))))))

theorem trig12_c11 : trig12Tab.run cosCQ trig12Tab.FcQ 11 21 0 20 (trig12Tab.init cosCQ trig12Tab.FcQ 21) =
    dySt trig12_c11_20 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 11 21 _ 2 18 trig12_c11_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 11 21 _ 2 16 trig12_c11_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 11 21 _ 2 14 trig12_c11_4_6
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 11 21 _ 2 12 trig12_c11_6_8
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 11 21 _ 2 10 trig12_c11_8_10
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 11 21 _ 2 8 trig12_c11_10_12
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 11 21 _ 2 6 trig12_c11_12_14
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 11 21 _ 2 4 trig12_c11_14_16
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 11 21 _ 2 2 trig12_c11_16_18
    (trig12_c11_18_20)))))))))

set_option maxHeartbeats 4000000 in
theorem trig12_ok11 : trig12Tab.Ok trig12C 11 22 22 (dySt trig12_s11_20) (dySt trig12_c11_20) := by
  decide +kernel

theorem trig12_g11 : trig12Tab.Group trig12C (11, 22, 22) :=
  ⟨_, _, trig12_s11, trig12_c11, trig12_ok11⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok11 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 11 22 22 (dySt trig12_s11_20) (dySt trig12_c11_20) := by
  decide +kernel

theorem tan12_g11 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (11, 22, 22) :=
  ⟨_, _, trig12_s11, trig12_c11, tan12_ok11⟩

end ExpansionBounds
