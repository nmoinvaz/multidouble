import ExpansionBounds.Trig12.S5

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 5

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_c5_16_18 :
    trig12Tab.run cosCQ trig12Tab.FcQ 5 33 16 2 (dySt trig12_c5_16) = dySt trig12_c5_18 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c5_18_20 :
    trig12Tab.run cosCQ trig12Tab.FcQ 5 33 18 2 (dySt trig12_c5_18) = dySt trig12_c5_20 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c5_20_22 :
    trig12Tab.run cosCQ trig12Tab.FcQ 5 33 20 2 (dySt trig12_c5_20) = dySt trig12_c5_22 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c5_22_24 :
    trig12Tab.run cosCQ trig12Tab.FcQ 5 33 22 2 (dySt trig12_c5_22) = dySt trig12_c5_24 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c5_24_26 :
    trig12Tab.run cosCQ trig12Tab.FcQ 5 33 24 2 (dySt trig12_c5_24) = dySt trig12_c5_26 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c5_26_28 :
    trig12Tab.run cosCQ trig12Tab.FcQ 5 33 26 2 (dySt trig12_c5_26) = dySt trig12_c5_28 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c5_28_30 :
    trig12Tab.run cosCQ trig12Tab.FcQ 5 33 28 2 (dySt trig12_c5_28) = dySt trig12_c5_30 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c5_30_32 :
    trig12Tab.run cosCQ trig12Tab.FcQ 5 33 30 2 (dySt trig12_c5_30) = dySt trig12_c5_32 := by
  decide +kernel

end ExpansionBounds
