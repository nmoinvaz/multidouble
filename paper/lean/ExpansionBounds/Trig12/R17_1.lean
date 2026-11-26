import ExpansionBounds.Trig12.S17

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 17

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_c17_10_12 :
    trig12Tab.run cosCQ trig12Tab.FcQ 17 15 10 2 (dySt trig12_c17_10) = dySt trig12_c17_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c17_12_14 :
    trig12Tab.run cosCQ trig12Tab.FcQ 17 15 12 2 (dySt trig12_c17_12) = dySt trig12_c17_14 := by
  decide +kernel

end ExpansionBounds
