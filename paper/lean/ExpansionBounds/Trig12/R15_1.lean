import ExpansionBounds.Trig12.S15

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 15

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_c15_8_10 :
    trig12Tab.run cosCQ trig12Tab.FcQ 15 17 8 2 (dySt trig12_c15_8) = dySt trig12_c15_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c15_10_12 :
    trig12Tab.run cosCQ trig12Tab.FcQ 15 17 10 2 (dySt trig12_c15_10) = dySt trig12_c15_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c15_12_14 :
    trig12Tab.run cosCQ trig12Tab.FcQ 15 17 12 2 (dySt trig12_c15_12) = dySt trig12_c15_14 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c15_14_16 :
    trig12Tab.run cosCQ trig12Tab.FcQ 15 17 14 2 (dySt trig12_c15_14) = dySt trig12_c15_16 := by
  decide +kernel

end ExpansionBounds
