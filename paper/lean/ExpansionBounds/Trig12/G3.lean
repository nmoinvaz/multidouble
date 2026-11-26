import ExpansionBounds.Trig12.R3_0
import ExpansionBounds.Trig12.R3_1
import ExpansionBounds.Trig12.R3_2
import ExpansionBounds.Trig12.R3_3

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 3

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s3 : trig12Tab.run sinCQ trig12Tab.FsQ 3 40 0 39 (trig12Tab.init sinCQ trig12Tab.FsQ 40) =
    dySt trig12_s3_39 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 3 40 _ 2 37 trig12_s3_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 3 40 _ 2 35 trig12_s3_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 3 40 _ 2 33 trig12_s3_4_6
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 3 40 _ 2 31 trig12_s3_6_8
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 3 40 _ 2 29 trig12_s3_8_10
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 3 40 _ 2 27 trig12_s3_10_12
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 3 40 _ 2 25 trig12_s3_12_14
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 3 40 _ 2 23 trig12_s3_14_16
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 3 40 _ 2 21 trig12_s3_16_18
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 3 40 _ 2 19 trig12_s3_18_20
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 3 40 _ 2 17 trig12_s3_20_22
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 3 40 _ 2 15 trig12_s3_22_24
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 3 40 _ 2 13 trig12_s3_24_26
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 3 40 _ 2 11 trig12_s3_26_28
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 3 40 _ 2 9 trig12_s3_28_30
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 3 40 _ 2 7 trig12_s3_30_32
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 3 40 _ 2 5 trig12_s3_32_34
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 3 40 _ 2 3 trig12_s3_34_36
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 3 40 _ 2 1 trig12_s3_36_38
    (trig12_s3_38_39)))))))))))))))))))

theorem trig12_c3 : trig12Tab.run cosCQ trig12Tab.FcQ 3 40 0 39 (trig12Tab.init cosCQ trig12Tab.FcQ 40) =
    dySt trig12_c3_39 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 3 40 _ 2 37 trig12_c3_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 3 40 _ 2 35 trig12_c3_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 3 40 _ 2 33 trig12_c3_4_6
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 3 40 _ 2 31 trig12_c3_6_8
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 3 40 _ 2 29 trig12_c3_8_10
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 3 40 _ 2 27 trig12_c3_10_12
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 3 40 _ 2 25 trig12_c3_12_14
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 3 40 _ 2 23 trig12_c3_14_16
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 3 40 _ 2 21 trig12_c3_16_18
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 3 40 _ 2 19 trig12_c3_18_20
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 3 40 _ 2 17 trig12_c3_20_22
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 3 40 _ 2 15 trig12_c3_22_24
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 3 40 _ 2 13 trig12_c3_24_26
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 3 40 _ 2 11 trig12_c3_26_28
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 3 40 _ 2 9 trig12_c3_28_30
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 3 40 _ 2 7 trig12_c3_30_32
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 3 40 _ 2 5 trig12_c3_32_34
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 3 40 _ 2 3 trig12_c3_34_36
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 3 40 _ 2 1 trig12_c3_36_38
    (trig12_c3_38_39)))))))))))))))))))

set_option maxHeartbeats 4000000 in
theorem trig12_ok3 : trig12Tab.Ok trig12C 3 41 41 (dySt trig12_s3_39) (dySt trig12_c3_39) := by
  decide +kernel

theorem trig12_g3 : trig12Tab.Group trig12C (3, 41, 41) :=
  ⟨_, _, trig12_s3, trig12_c3, trig12_ok3⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok3 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 3 41 41 (dySt trig12_s3_39) (dySt trig12_c3_39) := by
  decide +kernel

theorem tan12_g3 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (3, 41, 41) :=
  ⟨_, _, trig12_s3, trig12_c3, tan12_ok3⟩

end ExpansionBounds
