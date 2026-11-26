import ExpansionBounds.Trig12.S16

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 16

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_c16_8_10 :
    trig12Tab.run cosCQ trig12Tab.FcQ 16 16 8 2 (dySt trig12_c16_8) = dySt trig12_c16_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c16_10_12 :
    trig12Tab.run cosCQ trig12Tab.FcQ 16 16 10 2 (dySt trig12_c16_10) = dySt trig12_c16_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c16_12_14 :
    trig12Tab.run cosCQ trig12Tab.FcQ 16 16 12 2 (dySt trig12_c16_12) = dySt trig12_c16_14 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c16_14_15 :
    trig12Tab.run cosCQ trig12Tab.FcQ 16 16 14 1 (dySt trig12_c16_14) = dySt trig12_c16_15 := by
  decide +kernel

end ExpansionBounds
