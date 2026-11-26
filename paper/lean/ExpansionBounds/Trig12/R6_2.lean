import ExpansionBounds.Trig12.S6

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 6

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_c6_18_20 :
    trig12Tab.run cosCQ trig12Tab.FcQ 6 30 18 2 (dySt trig12_c6_18) = dySt trig12_c6_20 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c6_20_22 :
    trig12Tab.run cosCQ trig12Tab.FcQ 6 30 20 2 (dySt trig12_c6_20) = dySt trig12_c6_22 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c6_22_24 :
    trig12Tab.run cosCQ trig12Tab.FcQ 6 30 22 2 (dySt trig12_c6_22) = dySt trig12_c6_24 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c6_24_26 :
    trig12Tab.run cosCQ trig12Tab.FcQ 6 30 24 2 (dySt trig12_c6_24) = dySt trig12_c6_26 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c6_26_28 :
    trig12Tab.run cosCQ trig12Tab.FcQ 6 30 26 2 (dySt trig12_c6_26) = dySt trig12_c6_28 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c6_28_29 :
    trig12Tab.run cosCQ trig12Tab.FcQ 6 30 28 1 (dySt trig12_c6_28) = dySt trig12_c6_29 := by
  decide +kernel

end ExpansionBounds
