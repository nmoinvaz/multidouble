import ExpansionBounds.Trig12.S160

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 160

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_c160_0_1 :
    trig12Tab.run cosCQ trig12Tab.FcQ 160 2 0 1 (trig12Tab.init cosCQ trig12Tab.FcQ 2) = dySt trig12_c160_1 := by
  decide +kernel

end ExpansionBounds
