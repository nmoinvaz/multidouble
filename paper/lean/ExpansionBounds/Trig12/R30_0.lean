import ExpansionBounds.Trig12.S30

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 30

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s30_0_2 :
    trig12Tab.run sinCQ trig12Tab.FsQ 30 9 0 2 (trig12Tab.init sinCQ trig12Tab.FsQ 9) = dySt trig12_s30_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s30_2_4 :
    trig12Tab.run sinCQ trig12Tab.FsQ 30 9 2 2 (dySt trig12_s30_2) = dySt trig12_s30_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s30_4_6 :
    trig12Tab.run sinCQ trig12Tab.FsQ 30 9 4 2 (dySt trig12_s30_4) = dySt trig12_s30_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s30_6_8 :
    trig12Tab.run sinCQ trig12Tab.FsQ 30 9 6 2 (dySt trig12_s30_6) = dySt trig12_s30_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c30_0_2 :
    trig12Tab.run cosCQ trig12Tab.FcQ 30 9 0 2 (trig12Tab.init cosCQ trig12Tab.FcQ 9) = dySt trig12_c30_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c30_2_4 :
    trig12Tab.run cosCQ trig12Tab.FcQ 30 9 2 2 (dySt trig12_c30_2) = dySt trig12_c30_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c30_4_6 :
    trig12Tab.run cosCQ trig12Tab.FcQ 30 9 4 2 (dySt trig12_c30_4) = dySt trig12_c30_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c30_6_8 :
    trig12Tab.run cosCQ trig12Tab.FcQ 30 9 6 2 (dySt trig12_c30_6) = dySt trig12_c30_8 := by
  decide +kernel

end ExpansionBounds
