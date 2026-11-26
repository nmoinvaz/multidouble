import ExpansionBounds.Trig12.S5

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 5

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s5_24_26 :
    trig12Tab.run sinCQ trig12Tab.FsQ 5 33 24 2 (dySt trig12_s5_24) = dySt trig12_s5_26 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s5_26_28 :
    trig12Tab.run sinCQ trig12Tab.FsQ 5 33 26 2 (dySt trig12_s5_26) = dySt trig12_s5_28 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s5_28_30 :
    trig12Tab.run sinCQ trig12Tab.FsQ 5 33 28 2 (dySt trig12_s5_28) = dySt trig12_s5_30 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s5_30_32 :
    trig12Tab.run sinCQ trig12Tab.FsQ 5 33 30 2 (dySt trig12_s5_30) = dySt trig12_s5_32 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c5_0_2 :
    trig12Tab.run cosCQ trig12Tab.FcQ 5 33 0 2 (trig12Tab.init cosCQ trig12Tab.FcQ 33) = dySt trig12_c5_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c5_2_4 :
    trig12Tab.run cosCQ trig12Tab.FcQ 5 33 2 2 (dySt trig12_c5_2) = dySt trig12_c5_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c5_4_6 :
    trig12Tab.run cosCQ trig12Tab.FcQ 5 33 4 2 (dySt trig12_c5_4) = dySt trig12_c5_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c5_6_8 :
    trig12Tab.run cosCQ trig12Tab.FcQ 5 33 6 2 (dySt trig12_c5_6) = dySt trig12_c5_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c5_8_10 :
    trig12Tab.run cosCQ trig12Tab.FcQ 5 33 8 2 (dySt trig12_c5_8) = dySt trig12_c5_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c5_10_12 :
    trig12Tab.run cosCQ trig12Tab.FcQ 5 33 10 2 (dySt trig12_c5_10) = dySt trig12_c5_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c5_12_14 :
    trig12Tab.run cosCQ trig12Tab.FcQ 5 33 12 2 (dySt trig12_c5_12) = dySt trig12_c5_14 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c5_14_16 :
    trig12Tab.run cosCQ trig12Tab.FcQ 5 33 14 2 (dySt trig12_c5_14) = dySt trig12_c5_16 := by
  decide +kernel

end ExpansionBounds
