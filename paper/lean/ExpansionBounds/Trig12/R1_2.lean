import ExpansionBounds.Trig12.S1

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 1

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s1_48_49 :
    trig12Tab.run sinCQ trig12Tab.FsQ 1 50 48 1 (dySt trig12_s1_48) = dySt trig12_s1_49 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c1_0_2 :
    trig12Tab.run cosCQ trig12Tab.FcQ 1 51 0 2 (trig12Tab.init cosCQ trig12Tab.FcQ 51) = dySt trig12_c1_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c1_2_4 :
    trig12Tab.run cosCQ trig12Tab.FcQ 1 51 2 2 (dySt trig12_c1_2) = dySt trig12_c1_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c1_4_6 :
    trig12Tab.run cosCQ trig12Tab.FcQ 1 51 4 2 (dySt trig12_c1_4) = dySt trig12_c1_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c1_6_8 :
    trig12Tab.run cosCQ trig12Tab.FcQ 1 51 6 2 (dySt trig12_c1_6) = dySt trig12_c1_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c1_8_10 :
    trig12Tab.run cosCQ trig12Tab.FcQ 1 51 8 2 (dySt trig12_c1_8) = dySt trig12_c1_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c1_10_12 :
    trig12Tab.run cosCQ trig12Tab.FcQ 1 51 10 2 (dySt trig12_c1_10) = dySt trig12_c1_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c1_12_14 :
    trig12Tab.run cosCQ trig12Tab.FcQ 1 51 12 2 (dySt trig12_c1_12) = dySt trig12_c1_14 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c1_14_16 :
    trig12Tab.run cosCQ trig12Tab.FcQ 1 51 14 2 (dySt trig12_c1_14) = dySt trig12_c1_16 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c1_16_18 :
    trig12Tab.run cosCQ trig12Tab.FcQ 1 51 16 2 (dySt trig12_c1_16) = dySt trig12_c1_18 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c1_18_20 :
    trig12Tab.run cosCQ trig12Tab.FcQ 1 51 18 2 (dySt trig12_c1_18) = dySt trig12_c1_20 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c1_20_22 :
    trig12Tab.run cosCQ trig12Tab.FcQ 1 51 20 2 (dySt trig12_c1_20) = dySt trig12_c1_22 := by
  decide +kernel

end ExpansionBounds
