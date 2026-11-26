import ExpansionBounds.Trig12.S0

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 0

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_c0_18_20 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 18 2 (dySt trig12_c0_18) = dySt trig12_c0_20 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_20_22 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 20 2 (dySt trig12_c0_20) = dySt trig12_c0_22 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_22_24 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 22 2 (dySt trig12_c0_22) = dySt trig12_c0_24 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_24_26 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 24 2 (dySt trig12_c0_24) = dySt trig12_c0_26 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_26_28 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 26 2 (dySt trig12_c0_26) = dySt trig12_c0_28 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_28_30 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 28 2 (dySt trig12_c0_28) = dySt trig12_c0_30 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_30_32 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 30 2 (dySt trig12_c0_30) = dySt trig12_c0_32 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_32_34 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 32 2 (dySt trig12_c0_32) = dySt trig12_c0_34 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_34_36 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 34 2 (dySt trig12_c0_34) = dySt trig12_c0_36 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_36_38 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 36 2 (dySt trig12_c0_36) = dySt trig12_c0_38 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_38_40 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 38 2 (dySt trig12_c0_38) = dySt trig12_c0_40 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_40_42 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 40 2 (dySt trig12_c0_40) = dySt trig12_c0_42 := by
  decide +kernel

end ExpansionBounds
