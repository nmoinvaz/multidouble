import ExpansionBounds.Trig12.S6

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 6

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s6_24_26 :
    trig12Tab.run sinCQ trig12Tab.FsQ 6 30 24 2 (dySt trig12_s6_24) = dySt trig12_s6_26 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s6_26_28 :
    trig12Tab.run sinCQ trig12Tab.FsQ 6 30 26 2 (dySt trig12_s6_26) = dySt trig12_s6_28 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s6_28_29 :
    trig12Tab.run sinCQ trig12Tab.FsQ 6 30 28 1 (dySt trig12_s6_28) = dySt trig12_s6_29 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c6_0_2 :
    trig12Tab.run cosCQ trig12Tab.FcQ 6 30 0 2 (trig12Tab.init cosCQ trig12Tab.FcQ 30) = dySt trig12_c6_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c6_2_4 :
    trig12Tab.run cosCQ trig12Tab.FcQ 6 30 2 2 (dySt trig12_c6_2) = dySt trig12_c6_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c6_4_6 :
    trig12Tab.run cosCQ trig12Tab.FcQ 6 30 4 2 (dySt trig12_c6_4) = dySt trig12_c6_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c6_6_8 :
    trig12Tab.run cosCQ trig12Tab.FcQ 6 30 6 2 (dySt trig12_c6_6) = dySt trig12_c6_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c6_8_10 :
    trig12Tab.run cosCQ trig12Tab.FcQ 6 30 8 2 (dySt trig12_c6_8) = dySt trig12_c6_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c6_10_12 :
    trig12Tab.run cosCQ trig12Tab.FcQ 6 30 10 2 (dySt trig12_c6_10) = dySt trig12_c6_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c6_12_14 :
    trig12Tab.run cosCQ trig12Tab.FcQ 6 30 12 2 (dySt trig12_c6_12) = dySt trig12_c6_14 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c6_14_16 :
    trig12Tab.run cosCQ trig12Tab.FcQ 6 30 14 2 (dySt trig12_c6_14) = dySt trig12_c6_16 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c6_16_18 :
    trig12Tab.run cosCQ trig12Tab.FcQ 6 30 16 2 (dySt trig12_c6_16) = dySt trig12_c6_18 := by
  decide +kernel

end ExpansionBounds
