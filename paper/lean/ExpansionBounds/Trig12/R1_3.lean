import ExpansionBounds.Trig12.S1

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 1

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_c1_22_24 :
    trig12Tab.run cosCQ trig12Tab.FcQ 1 51 22 2 (dySt trig12_c1_22) = dySt trig12_c1_24 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c1_24_26 :
    trig12Tab.run cosCQ trig12Tab.FcQ 1 51 24 2 (dySt trig12_c1_24) = dySt trig12_c1_26 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c1_26_28 :
    trig12Tab.run cosCQ trig12Tab.FcQ 1 51 26 2 (dySt trig12_c1_26) = dySt trig12_c1_28 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c1_28_30 :
    trig12Tab.run cosCQ trig12Tab.FcQ 1 51 28 2 (dySt trig12_c1_28) = dySt trig12_c1_30 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c1_30_32 :
    trig12Tab.run cosCQ trig12Tab.FcQ 1 51 30 2 (dySt trig12_c1_30) = dySt trig12_c1_32 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c1_32_34 :
    trig12Tab.run cosCQ trig12Tab.FcQ 1 51 32 2 (dySt trig12_c1_32) = dySt trig12_c1_34 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c1_34_36 :
    trig12Tab.run cosCQ trig12Tab.FcQ 1 51 34 2 (dySt trig12_c1_34) = dySt trig12_c1_36 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c1_36_38 :
    trig12Tab.run cosCQ trig12Tab.FcQ 1 51 36 2 (dySt trig12_c1_36) = dySt trig12_c1_38 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c1_38_40 :
    trig12Tab.run cosCQ trig12Tab.FcQ 1 51 38 2 (dySt trig12_c1_38) = dySt trig12_c1_40 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c1_40_42 :
    trig12Tab.run cosCQ trig12Tab.FcQ 1 51 40 2 (dySt trig12_c1_40) = dySt trig12_c1_42 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c1_42_44 :
    trig12Tab.run cosCQ trig12Tab.FcQ 1 51 42 2 (dySt trig12_c1_42) = dySt trig12_c1_44 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c1_44_46 :
    trig12Tab.run cosCQ trig12Tab.FcQ 1 51 44 2 (dySt trig12_c1_44) = dySt trig12_c1_46 := by
  decide +kernel

end ExpansionBounds
