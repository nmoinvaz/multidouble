import ExpansionBounds.Trig12.S14

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 14

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_c14_8_10 :
    trig12Tab.run cosCQ trig12Tab.FcQ 14 18 8 2 (dySt trig12_c14_8) = dySt trig12_c14_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c14_10_12 :
    trig12Tab.run cosCQ trig12Tab.FcQ 14 18 10 2 (dySt trig12_c14_10) = dySt trig12_c14_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c14_12_14 :
    trig12Tab.run cosCQ trig12Tab.FcQ 14 18 12 2 (dySt trig12_c14_12) = dySt trig12_c14_14 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c14_14_16 :
    trig12Tab.run cosCQ trig12Tab.FcQ 14 18 14 2 (dySt trig12_c14_14) = dySt trig12_c14_16 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c14_16_17 :
    trig12Tab.run cosCQ trig12Tab.FcQ 14 18 16 1 (dySt trig12_c14_16) = dySt trig12_c14_17 := by
  decide +kernel

end ExpansionBounds
