import ExpansionBounds.Trig12.R2_0
import ExpansionBounds.Trig12.R2_1
import ExpansionBounds.Trig12.R2_2
import ExpansionBounds.Trig12.R2_3

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 2

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s2 : trig12Tab.run sinCQ trig12Tab.FsQ 2 45 0 44 (trig12Tab.init sinCQ trig12Tab.FsQ 45) =
    dySt trig12_s2_44 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 2 45 _ 2 42 trig12_s2_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 2 45 _ 2 40 trig12_s2_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 2 45 _ 2 38 trig12_s2_4_6
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 2 45 _ 2 36 trig12_s2_6_8
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 2 45 _ 2 34 trig12_s2_8_10
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 2 45 _ 2 32 trig12_s2_10_12
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 2 45 _ 2 30 trig12_s2_12_14
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 2 45 _ 2 28 trig12_s2_14_16
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 2 45 _ 2 26 trig12_s2_16_18
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 2 45 _ 2 24 trig12_s2_18_20
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 2 45 _ 2 22 trig12_s2_20_22
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 2 45 _ 2 20 trig12_s2_22_24
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 2 45 _ 2 18 trig12_s2_24_26
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 2 45 _ 2 16 trig12_s2_26_28
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 2 45 _ 2 14 trig12_s2_28_30
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 2 45 _ 2 12 trig12_s2_30_32
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 2 45 _ 2 10 trig12_s2_32_34
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 2 45 _ 2 8 trig12_s2_34_36
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 2 45 _ 2 6 trig12_s2_36_38
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 2 45 _ 2 4 trig12_s2_38_40
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 2 45 _ 2 2 trig12_s2_40_42
    (trig12_s2_42_44)))))))))))))))))))))

theorem trig12_c2 : trig12Tab.run cosCQ trig12Tab.FcQ 2 45 0 44 (trig12Tab.init cosCQ trig12Tab.FcQ 45) =
    dySt trig12_c2_44 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 2 45 _ 2 42 trig12_c2_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 2 45 _ 2 40 trig12_c2_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 2 45 _ 2 38 trig12_c2_4_6
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 2 45 _ 2 36 trig12_c2_6_8
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 2 45 _ 2 34 trig12_c2_8_10
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 2 45 _ 2 32 trig12_c2_10_12
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 2 45 _ 2 30 trig12_c2_12_14
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 2 45 _ 2 28 trig12_c2_14_16
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 2 45 _ 2 26 trig12_c2_16_18
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 2 45 _ 2 24 trig12_c2_18_20
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 2 45 _ 2 22 trig12_c2_20_22
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 2 45 _ 2 20 trig12_c2_22_24
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 2 45 _ 2 18 trig12_c2_24_26
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 2 45 _ 2 16 trig12_c2_26_28
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 2 45 _ 2 14 trig12_c2_28_30
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 2 45 _ 2 12 trig12_c2_30_32
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 2 45 _ 2 10 trig12_c2_32_34
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 2 45 _ 2 8 trig12_c2_34_36
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 2 45 _ 2 6 trig12_c2_36_38
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 2 45 _ 2 4 trig12_c2_38_40
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 2 45 _ 2 2 trig12_c2_40_42
    (trig12_c2_42_44)))))))))))))))))))))

set_option maxHeartbeats 4000000 in
theorem trig12_ok2 : trig12Tab.Ok trig12C 2 46 46 (dySt trig12_s2_44) (dySt trig12_c2_44) := by
  decide +kernel

theorem trig12_g2 : trig12Tab.Group trig12C (2, 46, 46) :=
  ⟨_, _, trig12_s2, trig12_c2, trig12_ok2⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok2 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 2 46 46 (dySt trig12_s2_44) (dySt trig12_c2_44) := by
  decide +kernel

theorem tan12_g2 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (2, 46, 46) :=
  ⟨_, _, trig12_s2, trig12_c2, tan12_ok2⟩

end ExpansionBounds
