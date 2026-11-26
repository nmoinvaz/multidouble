import ExpansionBounds.Trig12.S12

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 12

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_c12_4_6 :
    trig12Tab.run cosCQ trig12Tab.FcQ 12 20 4 2 (dySt trig12_c12_4) = dySt trig12_c12_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c12_6_8 :
    trig12Tab.run cosCQ trig12Tab.FcQ 12 20 6 2 (dySt trig12_c12_6) = dySt trig12_c12_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c12_8_10 :
    trig12Tab.run cosCQ trig12Tab.FcQ 12 20 8 2 (dySt trig12_c12_8) = dySt trig12_c12_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c12_10_12 :
    trig12Tab.run cosCQ trig12Tab.FcQ 12 20 10 2 (dySt trig12_c12_10) = dySt trig12_c12_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c12_12_14 :
    trig12Tab.run cosCQ trig12Tab.FcQ 12 20 12 2 (dySt trig12_c12_12) = dySt trig12_c12_14 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c12_14_16 :
    trig12Tab.run cosCQ trig12Tab.FcQ 12 20 14 2 (dySt trig12_c12_14) = dySt trig12_c12_16 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c12_16_18 :
    trig12Tab.run cosCQ trig12Tab.FcQ 12 20 16 2 (dySt trig12_c12_16) = dySt trig12_c12_18 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c12_18_19 :
    trig12Tab.run cosCQ trig12Tab.FcQ 12 20 18 1 (dySt trig12_c12_18) = dySt trig12_c12_19 := by
  decide +kernel

end ExpansionBounds
