import ExpansionBounds.Trig12.S3

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 3

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_c3_32_34 :
    trig12Tab.run cosCQ trig12Tab.FcQ 3 40 32 2 (dySt trig12_c3_32) = dySt trig12_c3_34 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c3_34_36 :
    trig12Tab.run cosCQ trig12Tab.FcQ 3 40 34 2 (dySt trig12_c3_34) = dySt trig12_c3_36 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c3_36_38 :
    trig12Tab.run cosCQ trig12Tab.FcQ 3 40 36 2 (dySt trig12_c3_36) = dySt trig12_c3_38 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c3_38_39 :
    trig12Tab.run cosCQ trig12Tab.FcQ 3 40 38 1 (dySt trig12_c3_38) = dySt trig12_c3_39 := by
  decide +kernel

end ExpansionBounds
