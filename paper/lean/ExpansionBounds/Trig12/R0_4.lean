import ExpansionBounds.Trig12.S0

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 0

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_c0_42_44 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 42 2 (dySt trig12_c0_42) = dySt trig12_c0_44 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_44_46 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 44 2 (dySt trig12_c0_44) = dySt trig12_c0_46 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_46_48 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 46 2 (dySt trig12_c0_46) = dySt trig12_c0_48 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_48_50 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 48 2 (dySt trig12_c0_48) = dySt trig12_c0_50 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_50_52 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 50 2 (dySt trig12_c0_50) = dySt trig12_c0_52 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_52_54 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 52 2 (dySt trig12_c0_52) = dySt trig12_c0_54 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_54_55 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 54 1 (dySt trig12_c0_54) = dySt trig12_c0_55 := by
  decide +kernel

end ExpansionBounds
