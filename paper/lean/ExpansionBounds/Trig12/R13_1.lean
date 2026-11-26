import ExpansionBounds.Trig12.S13

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 13

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_c13_6_8 :
    trig12Tab.run cosCQ trig12Tab.FcQ 13 19 6 2 (dySt trig12_c13_6) = dySt trig12_c13_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c13_8_10 :
    trig12Tab.run cosCQ trig12Tab.FcQ 13 19 8 2 (dySt trig12_c13_8) = dySt trig12_c13_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c13_10_12 :
    trig12Tab.run cosCQ trig12Tab.FcQ 13 19 10 2 (dySt trig12_c13_10) = dySt trig12_c13_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c13_12_14 :
    trig12Tab.run cosCQ trig12Tab.FcQ 13 19 12 2 (dySt trig12_c13_12) = dySt trig12_c13_14 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c13_14_16 :
    trig12Tab.run cosCQ trig12Tab.FcQ 13 19 14 2 (dySt trig12_c13_14) = dySt trig12_c13_16 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c13_16_18 :
    trig12Tab.run cosCQ trig12Tab.FcQ 13 19 16 2 (dySt trig12_c13_16) = dySt trig12_c13_18 := by
  decide +kernel

end ExpansionBounds
