import ExpansionBounds.Trig12.S2

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 2

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_c2_28_30 :
    trig12Tab.run cosCQ trig12Tab.FcQ 2 45 28 2 (dySt trig12_c2_28) = dySt trig12_c2_30 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c2_30_32 :
    trig12Tab.run cosCQ trig12Tab.FcQ 2 45 30 2 (dySt trig12_c2_30) = dySt trig12_c2_32 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c2_32_34 :
    trig12Tab.run cosCQ trig12Tab.FcQ 2 45 32 2 (dySt trig12_c2_32) = dySt trig12_c2_34 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c2_34_36 :
    trig12Tab.run cosCQ trig12Tab.FcQ 2 45 34 2 (dySt trig12_c2_34) = dySt trig12_c2_36 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c2_36_38 :
    trig12Tab.run cosCQ trig12Tab.FcQ 2 45 36 2 (dySt trig12_c2_36) = dySt trig12_c2_38 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c2_38_40 :
    trig12Tab.run cosCQ trig12Tab.FcQ 2 45 38 2 (dySt trig12_c2_38) = dySt trig12_c2_40 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c2_40_42 :
    trig12Tab.run cosCQ trig12Tab.FcQ 2 45 40 2 (dySt trig12_c2_40) = dySt trig12_c2_42 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c2_42_44 :
    trig12Tab.run cosCQ trig12Tab.FcQ 2 45 42 2 (dySt trig12_c2_42) = dySt trig12_c2_44 := by
  decide +kernel

end ExpansionBounds
