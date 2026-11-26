import ExpansionBounds.Trig12.S0

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 0

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s0_48_50 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 48 2 (dySt trig12_s0_48) = dySt trig12_s0_50 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s0_50_52 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 50 2 (dySt trig12_s0_50) = dySt trig12_s0_52 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s0_52_54 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 52 2 (dySt trig12_s0_52) = dySt trig12_s0_54 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_0_2 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 0 2 (trig12Tab.init cosCQ trig12Tab.FcQ 56) = dySt trig12_c0_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_2_4 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 2 2 (dySt trig12_c0_2) = dySt trig12_c0_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_4_6 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 4 2 (dySt trig12_c0_4) = dySt trig12_c0_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_6_8 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 6 2 (dySt trig12_c0_6) = dySt trig12_c0_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_8_10 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 8 2 (dySt trig12_c0_8) = dySt trig12_c0_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_10_12 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 10 2 (dySt trig12_c0_10) = dySt trig12_c0_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_12_14 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 12 2 (dySt trig12_c0_12) = dySt trig12_c0_14 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_14_16 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 14 2 (dySt trig12_c0_14) = dySt trig12_c0_16 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c0_16_18 :
    trig12Tab.run cosCQ trig12Tab.FcQ 0 56 16 2 (dySt trig12_c0_16) = dySt trig12_c0_18 := by
  decide +kernel

end ExpansionBounds
