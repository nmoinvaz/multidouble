import ExpansionBounds.Trig12.R4_0
import ExpansionBounds.Trig12.R4_1
import ExpansionBounds.Trig12.R4_2

/-!
# Theorem 35 at `n = 12` and `p = 53`: bucket 4

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig12_s4 : trig12Tab.run sinCQ trig12Tab.FsQ 4 36 0 35 (trig12Tab.init sinCQ trig12Tab.FsQ 36) =
    dySt trig12_s4_35 :=
  TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 4 36 _ 2 33 trig12_s4_0_2
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 4 36 _ 2 31 trig12_s4_2_4
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 4 36 _ 2 29 trig12_s4_4_6
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 4 36 _ 2 27 trig12_s4_6_8
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 4 36 _ 2 25 trig12_s4_8_10
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 4 36 _ 2 23 trig12_s4_10_12
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 4 36 _ 2 21 trig12_s4_12_14
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 4 36 _ 2 19 trig12_s4_14_16
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 4 36 _ 2 17 trig12_s4_16_18
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 4 36 _ 2 15 trig12_s4_18_20
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 4 36 _ 2 13 trig12_s4_20_22
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 4 36 _ 2 11 trig12_s4_22_24
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 4 36 _ 2 9 trig12_s4_24_26
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 4 36 _ 2 7 trig12_s4_26_28
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 4 36 _ 2 5 trig12_s4_28_30
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 4 36 _ 2 3 trig12_s4_30_32
    (TrigTab.run_cut trig12Tab sinCQ trig12Tab.FsQ 4 36 _ 2 1 trig12_s4_32_34
    (trig12_s4_34_35)))))))))))))))))

theorem trig12_c4 : trig12Tab.run cosCQ trig12Tab.FcQ 4 36 0 35 (trig12Tab.init cosCQ trig12Tab.FcQ 36) =
    dySt trig12_c4_35 :=
  TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 4 36 _ 2 33 trig12_c4_0_2
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 4 36 _ 2 31 trig12_c4_2_4
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 4 36 _ 2 29 trig12_c4_4_6
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 4 36 _ 2 27 trig12_c4_6_8
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 4 36 _ 2 25 trig12_c4_8_10
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 4 36 _ 2 23 trig12_c4_10_12
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 4 36 _ 2 21 trig12_c4_12_14
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 4 36 _ 2 19 trig12_c4_14_16
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 4 36 _ 2 17 trig12_c4_16_18
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 4 36 _ 2 15 trig12_c4_18_20
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 4 36 _ 2 13 trig12_c4_20_22
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 4 36 _ 2 11 trig12_c4_22_24
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 4 36 _ 2 9 trig12_c4_24_26
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 4 36 _ 2 7 trig12_c4_26_28
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 4 36 _ 2 5 trig12_c4_28_30
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 4 36 _ 2 3 trig12_c4_30_32
    (TrigTab.run_cut trig12Tab cosCQ trig12Tab.FcQ 4 36 _ 2 1 trig12_c4_32_34
    (trig12_c4_34_35)))))))))))))))))

set_option maxHeartbeats 4000000 in
theorem trig12_ok4 : trig12Tab.Ok trig12C 4 37 37 (dySt trig12_s4_35) (dySt trig12_c4_35) := by
  decide +kernel

theorem trig12_g4 : trig12Tab.Group trig12C (4, 37, 37) :=
  ⟨_, _, trig12_s4, trig12_c4, trig12_ok4⟩

set_option maxHeartbeats 4000000 in
theorem tan12_ok4 :
    trig12Tab.TanOk trig12Ct trig12Kd0 trig12Kd3 4 37 37 (dySt trig12_s4_35) (dySt trig12_c4_35) := by
  decide +kernel

theorem tan12_g4 : trig12Tab.TanGroup trig12Ct trig12Kd0 trig12Kd3 (4, 37, 37) :=
  ⟨_, _, trig12_s4, trig12_c4, tan12_ok4⟩

end ExpansionBounds
