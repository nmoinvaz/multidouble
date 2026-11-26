import ExpansionBounds.Trig12.S10

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 10

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_c10_2_4 :
    trig12Tab.run cosCQ trig12Tab.FcQ 10 22 2 2 (dySt trig12_c10_2) = dySt trig12_c10_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c10_4_6 :
    trig12Tab.run cosCQ trig12Tab.FcQ 10 22 4 2 (dySt trig12_c10_4) = dySt trig12_c10_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c10_6_8 :
    trig12Tab.run cosCQ trig12Tab.FcQ 10 22 6 2 (dySt trig12_c10_6) = dySt trig12_c10_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c10_8_10 :
    trig12Tab.run cosCQ trig12Tab.FcQ 10 22 8 2 (dySt trig12_c10_8) = dySt trig12_c10_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c10_10_12 :
    trig12Tab.run cosCQ trig12Tab.FcQ 10 22 10 2 (dySt trig12_c10_10) = dySt trig12_c10_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c10_12_14 :
    trig12Tab.run cosCQ trig12Tab.FcQ 10 22 12 2 (dySt trig12_c10_12) = dySt trig12_c10_14 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c10_14_16 :
    trig12Tab.run cosCQ trig12Tab.FcQ 10 22 14 2 (dySt trig12_c10_14) = dySt trig12_c10_16 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c10_16_18 :
    trig12Tab.run cosCQ trig12Tab.FcQ 10 22 16 2 (dySt trig12_c10_16) = dySt trig12_c10_18 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c10_18_20 :
    trig12Tab.run cosCQ trig12Tab.FcQ 10 22 18 2 (dySt trig12_c10_18) = dySt trig12_c10_20 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c10_20_21 :
    trig12Tab.run cosCQ trig12Tab.FcQ 10 22 20 1 (dySt trig12_c10_20) = dySt trig12_c10_21 := by
  decide +kernel

end ExpansionBounds
