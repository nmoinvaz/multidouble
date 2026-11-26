import ExpansionBounds.Trig12.S18

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 18

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_c18_10_12 :
    trig12Tab.run cosCQ trig12Tab.FcQ 18 14 10 2 (dySt trig12_c18_10) = dySt trig12_c18_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c18_12_13 :
    trig12Tab.run cosCQ trig12Tab.FcQ 18 14 12 1 (dySt trig12_c18_12) = dySt trig12_c18_13 := by
  decide +kernel

end ExpansionBounds
