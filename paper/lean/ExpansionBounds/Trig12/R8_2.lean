import ExpansionBounds.Trig12.S8

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 8

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_c8_24_25 :
    trig12Tab.run cosCQ trig12Tab.FcQ 8 26 24 1 (dySt trig12_c8_24) = dySt trig12_c8_25 := by
  decide +kernel

end ExpansionBounds
