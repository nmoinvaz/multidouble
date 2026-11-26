import ExpansionBounds.Trig12.S7

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 7

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_c7_22_24 :
    trig12Tab.run cosCQ trig12Tab.FcQ 7 28 22 2 (dySt trig12_c7_22) = dySt trig12_c7_24 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c7_24_26 :
    trig12Tab.run cosCQ trig12Tab.FcQ 7 28 24 2 (dySt trig12_c7_24) = dySt trig12_c7_26 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c7_26_27 :
    trig12Tab.run cosCQ trig12Tab.FcQ 7 28 26 1 (dySt trig12_c7_26) = dySt trig12_c7_27 := by
  decide +kernel

end ExpansionBounds
