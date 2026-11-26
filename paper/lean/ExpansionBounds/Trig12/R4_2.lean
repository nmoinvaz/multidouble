import ExpansionBounds.Trig12.S4

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 4

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_c4_12_14 :
    trig12Tab.run cosCQ trig12Tab.FcQ 4 36 12 2 (dySt trig12_c4_12) = dySt trig12_c4_14 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c4_14_16 :
    trig12Tab.run cosCQ trig12Tab.FcQ 4 36 14 2 (dySt trig12_c4_14) = dySt trig12_c4_16 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c4_16_18 :
    trig12Tab.run cosCQ trig12Tab.FcQ 4 36 16 2 (dySt trig12_c4_16) = dySt trig12_c4_18 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c4_18_20 :
    trig12Tab.run cosCQ trig12Tab.FcQ 4 36 18 2 (dySt trig12_c4_18) = dySt trig12_c4_20 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c4_20_22 :
    trig12Tab.run cosCQ trig12Tab.FcQ 4 36 20 2 (dySt trig12_c4_20) = dySt trig12_c4_22 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c4_22_24 :
    trig12Tab.run cosCQ trig12Tab.FcQ 4 36 22 2 (dySt trig12_c4_22) = dySt trig12_c4_24 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c4_24_26 :
    trig12Tab.run cosCQ trig12Tab.FcQ 4 36 24 2 (dySt trig12_c4_24) = dySt trig12_c4_26 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c4_26_28 :
    trig12Tab.run cosCQ trig12Tab.FcQ 4 36 26 2 (dySt trig12_c4_26) = dySt trig12_c4_28 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c4_28_30 :
    trig12Tab.run cosCQ trig12Tab.FcQ 4 36 28 2 (dySt trig12_c4_28) = dySt trig12_c4_30 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c4_30_32 :
    trig12Tab.run cosCQ trig12Tab.FcQ 4 36 30 2 (dySt trig12_c4_30) = dySt trig12_c4_32 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c4_32_34 :
    trig12Tab.run cosCQ trig12Tab.FcQ 4 36 32 2 (dySt trig12_c4_32) = dySt trig12_c4_34 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c4_34_35 :
    trig12Tab.run cosCQ trig12Tab.FcQ 4 36 34 1 (dySt trig12_c4_34) = dySt trig12_c4_35 := by
  decide +kernel

end ExpansionBounds
