import ExpansionBounds.Trig12.S4

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 4

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s4_24_26 :
    trig12Tab.run sinCQ trig12Tab.FsQ 4 36 24 2 (dySt trig12_s4_24) = dySt trig12_s4_26 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s4_26_28 :
    trig12Tab.run sinCQ trig12Tab.FsQ 4 36 26 2 (dySt trig12_s4_26) = dySt trig12_s4_28 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s4_28_30 :
    trig12Tab.run sinCQ trig12Tab.FsQ 4 36 28 2 (dySt trig12_s4_28) = dySt trig12_s4_30 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s4_30_32 :
    trig12Tab.run sinCQ trig12Tab.FsQ 4 36 30 2 (dySt trig12_s4_30) = dySt trig12_s4_32 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s4_32_34 :
    trig12Tab.run sinCQ trig12Tab.FsQ 4 36 32 2 (dySt trig12_s4_32) = dySt trig12_s4_34 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s4_34_35 :
    trig12Tab.run sinCQ trig12Tab.FsQ 4 36 34 1 (dySt trig12_s4_34) = dySt trig12_s4_35 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c4_0_2 :
    trig12Tab.run cosCQ trig12Tab.FcQ 4 36 0 2 (trig12Tab.init cosCQ trig12Tab.FcQ 36) = dySt trig12_c4_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c4_2_4 :
    trig12Tab.run cosCQ trig12Tab.FcQ 4 36 2 2 (dySt trig12_c4_2) = dySt trig12_c4_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c4_4_6 :
    trig12Tab.run cosCQ trig12Tab.FcQ 4 36 4 2 (dySt trig12_c4_4) = dySt trig12_c4_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c4_6_8 :
    trig12Tab.run cosCQ trig12Tab.FcQ 4 36 6 2 (dySt trig12_c4_6) = dySt trig12_c4_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c4_8_10 :
    trig12Tab.run cosCQ trig12Tab.FcQ 4 36 8 2 (dySt trig12_c4_8) = dySt trig12_c4_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c4_10_12 :
    trig12Tab.run cosCQ trig12Tab.FcQ 4 36 10 2 (dySt trig12_c4_10) = dySt trig12_c4_12 := by
  decide +kernel

end ExpansionBounds
