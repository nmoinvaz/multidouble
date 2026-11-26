import ExpansionBounds.Trig12.S1

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 1

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s1_0_2 :
    trig12Tab.run sinCQ trig12Tab.FsQ 1 50 0 2 (trig12Tab.init sinCQ trig12Tab.FsQ 50) = dySt trig12_s1_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s1_2_4 :
    trig12Tab.run sinCQ trig12Tab.FsQ 1 50 2 2 (dySt trig12_s1_2) = dySt trig12_s1_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s1_4_6 :
    trig12Tab.run sinCQ trig12Tab.FsQ 1 50 4 2 (dySt trig12_s1_4) = dySt trig12_s1_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s1_6_8 :
    trig12Tab.run sinCQ trig12Tab.FsQ 1 50 6 2 (dySt trig12_s1_6) = dySt trig12_s1_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s1_8_10 :
    trig12Tab.run sinCQ trig12Tab.FsQ 1 50 8 2 (dySt trig12_s1_8) = dySt trig12_s1_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s1_10_12 :
    trig12Tab.run sinCQ trig12Tab.FsQ 1 50 10 2 (dySt trig12_s1_10) = dySt trig12_s1_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s1_12_14 :
    trig12Tab.run sinCQ trig12Tab.FsQ 1 50 12 2 (dySt trig12_s1_12) = dySt trig12_s1_14 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s1_14_16 :
    trig12Tab.run sinCQ trig12Tab.FsQ 1 50 14 2 (dySt trig12_s1_14) = dySt trig12_s1_16 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s1_16_18 :
    trig12Tab.run sinCQ trig12Tab.FsQ 1 50 16 2 (dySt trig12_s1_16) = dySt trig12_s1_18 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s1_18_20 :
    trig12Tab.run sinCQ trig12Tab.FsQ 1 50 18 2 (dySt trig12_s1_18) = dySt trig12_s1_20 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s1_20_22 :
    trig12Tab.run sinCQ trig12Tab.FsQ 1 50 20 2 (dySt trig12_s1_20) = dySt trig12_s1_22 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s1_22_24 :
    trig12Tab.run sinCQ trig12Tab.FsQ 1 50 22 2 (dySt trig12_s1_22) = dySt trig12_s1_24 := by
  decide +kernel

end ExpansionBounds
