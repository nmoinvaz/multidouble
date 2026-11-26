import ExpansionBounds.Trig12.R1_0
import ExpansionBounds.Trig12.R1_1
import ExpansionBounds.Trig12.R1_2
import ExpansionBounds.Trig12.R1_3
import ExpansionBounds.Trig12.R1_4

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 1

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s1 : trig12Tab.run sinCQ trig12Tab.FsQ 1 50 0 49 (trig12Tab.init sinCQ trig12Tab.FsQ 50) =
    dySt trig12_s1_49 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 1 50 _ 2 47 trig12_s1_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 1 50 _ 2 45 trig12_s1_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 1 50 _ 2 43 trig12_s1_4_6
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 1 50 _ 2 41 trig12_s1_6_8
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 1 50 _ 2 39 trig12_s1_8_10
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 1 50 _ 2 37 trig12_s1_10_12
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 1 50 _ 2 35 trig12_s1_12_14
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 1 50 _ 2 33 trig12_s1_14_16
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 1 50 _ 2 31 trig12_s1_16_18
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 1 50 _ 2 29 trig12_s1_18_20
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 1 50 _ 2 27 trig12_s1_20_22
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 1 50 _ 2 25 trig12_s1_22_24
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 1 50 _ 2 23 trig12_s1_24_26
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 1 50 _ 2 21 trig12_s1_26_28
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 1 50 _ 2 19 trig12_s1_28_30
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 1 50 _ 2 17 trig12_s1_30_32
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 1 50 _ 2 15 trig12_s1_32_34
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 1 50 _ 2 13 trig12_s1_34_36
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 1 50 _ 2 11 trig12_s1_36_38
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 1 50 _ 2 9 trig12_s1_38_40
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 1 50 _ 2 7 trig12_s1_40_42
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 1 50 _ 2 5 trig12_s1_42_44
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 1 50 _ 2 3 trig12_s1_44_46
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 1 50 _ 2 1 trig12_s1_46_48
    (trig12_s1_48_49))))))))))))))))))))))))

theorem trig12_c1 : trig12Tab.run cosCQ trig12Tab.FcQ 1 51 0 50 (trig12Tab.init cosCQ trig12Tab.FcQ 51) =
    dySt trig12_c1_50 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 1 51 _ 2 48 trig12_c1_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 1 51 _ 2 46 trig12_c1_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 1 51 _ 2 44 trig12_c1_4_6
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 1 51 _ 2 42 trig12_c1_6_8
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 1 51 _ 2 40 trig12_c1_8_10
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 1 51 _ 2 38 trig12_c1_10_12
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 1 51 _ 2 36 trig12_c1_12_14
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 1 51 _ 2 34 trig12_c1_14_16
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 1 51 _ 2 32 trig12_c1_16_18
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 1 51 _ 2 30 trig12_c1_18_20
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 1 51 _ 2 28 trig12_c1_20_22
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 1 51 _ 2 26 trig12_c1_22_24
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 1 51 _ 2 24 trig12_c1_24_26
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 1 51 _ 2 22 trig12_c1_26_28
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 1 51 _ 2 20 trig12_c1_28_30
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 1 51 _ 2 18 trig12_c1_30_32
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 1 51 _ 2 16 trig12_c1_32_34
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 1 51 _ 2 14 trig12_c1_34_36
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 1 51 _ 2 12 trig12_c1_36_38
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 1 51 _ 2 10 trig12_c1_38_40
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 1 51 _ 2 8 trig12_c1_40_42
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 1 51 _ 2 6 trig12_c1_42_44
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 1 51 _ 2 4 trig12_c1_44_46
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 1 51 _ 2 2 trig12_c1_46_48
    (trig12_c1_48_50))))))))))))))))))))))))

set_option maxHeartbeats 4000000 in
theorem trig12_ok1 : trig12Tab.Ok trig12C 1 51 52 (dySt trig12_s1_49) (dySt trig12_c1_50) := by
  decide +kernel

theorem trig12_g1 : trig12Tab.Group trig12C (1, 51, 52) :=
  ⟨_, _, trig12_s1, trig12_c1, trig12_ok1⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok1 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 1 51 52 (dySt trig12_s1_49) (dySt trig12_c1_50) := by
  decide +kernel

theorem tan12_g1 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (1, 51, 52) :=
  ⟨_, _, trig12_s1, trig12_c1, tan12_ok1⟩

end ExpansionBounds
