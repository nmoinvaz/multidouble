import ExpansionBounds.Trig12.R0_0
import ExpansionBounds.Trig12.R0_1
import ExpansionBounds.Trig12.R0_2
import ExpansionBounds.Trig12.R0_3
import ExpansionBounds.Trig12.R0_4

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 0

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s0 : trig12Tab.run sinCQ trig12Tab.FsQ 0 55 0 54 (trig12Tab.init sinCQ trig12Tab.FsQ 55) =
    dySt trig12_s0_54 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 52 trig12_s0_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 50 trig12_s0_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 48 trig12_s0_4_6
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 46 trig12_s0_6_8
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 44 trig12_s0_8_10
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 42 trig12_s0_10_12
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 40 trig12_s0_12_14
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 38 trig12_s0_14_16
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 36 trig12_s0_16_18
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 34 trig12_s0_18_20
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 32 trig12_s0_20_22
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 30 trig12_s0_22_24
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 28 trig12_s0_24_26
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 26 trig12_s0_26_28
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 24 trig12_s0_28_30
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 22 trig12_s0_30_32
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 20 trig12_s0_32_34
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 18 trig12_s0_34_36
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 16 trig12_s0_36_38
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 14 trig12_s0_38_40
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 12 trig12_s0_40_42
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 10 trig12_s0_42_44
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 8 trig12_s0_44_46
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 6 trig12_s0_46_48
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 4 trig12_s0_48_50
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 0 55 _ 2 2 trig12_s0_50_52
    (trig12_s0_52_54))))))))))))))))))))))))))

theorem trig12_c0 : trig12Tab.run cosCQ trig12Tab.FcQ 0 56 0 55 (trig12Tab.init cosCQ trig12Tab.FcQ 56) =
    dySt trig12_c0_55 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 53 trig12_c0_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 51 trig12_c0_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 49 trig12_c0_4_6
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 47 trig12_c0_6_8
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 45 trig12_c0_8_10
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 43 trig12_c0_10_12
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 41 trig12_c0_12_14
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 39 trig12_c0_14_16
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 37 trig12_c0_16_18
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 35 trig12_c0_18_20
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 33 trig12_c0_20_22
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 31 trig12_c0_22_24
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 29 trig12_c0_24_26
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 27 trig12_c0_26_28
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 25 trig12_c0_28_30
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 23 trig12_c0_30_32
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 21 trig12_c0_32_34
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 19 trig12_c0_34_36
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 17 trig12_c0_36_38
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 15 trig12_c0_38_40
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 13 trig12_c0_40_42
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 11 trig12_c0_42_44
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 9 trig12_c0_44_46
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 7 trig12_c0_46_48
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 5 trig12_c0_48_50
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 3 trig12_c0_50_52
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 0 56 _ 2 1 trig12_c0_52_54
    (trig12_c0_54_55)))))))))))))))))))))))))))

set_option maxHeartbeats 4000000 in
theorem trig12_ok0 : trig12Tab.Ok trig12C 0 56 57 (dySt trig12_s0_54) (dySt trig12_c0_55) := by
  decide +kernel

theorem trig12_g0 : trig12Tab.Group trig12C (0, 56, 57) :=
  ⟨_, _, trig12_s0, trig12_c0, trig12_ok0⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok0 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 0 56 57 (dySt trig12_s0_54) (dySt trig12_c0_55) := by
  decide +kernel

theorem tan12_g0 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (0, 56, 57) :=
  ⟨_, _, trig12_s0, trig12_c0, tan12_ok0⟩

end ExpansionBounds
