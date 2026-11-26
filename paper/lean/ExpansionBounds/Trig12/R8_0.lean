import ExpansionBounds.Trig12.S8

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 8

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s8_0_2 :
    trig12Tab.run sinCQ trig12Tab.FsQ 8 25 0 2 (trig12Tab.init sinCQ trig12Tab.FsQ 25) = dySt trig12_s8_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s8_2_4 :
    trig12Tab.run sinCQ trig12Tab.FsQ 8 25 2 2 (dySt trig12_s8_2) = dySt trig12_s8_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s8_4_6 :
    trig12Tab.run sinCQ trig12Tab.FsQ 8 25 4 2 (dySt trig12_s8_4) = dySt trig12_s8_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s8_6_8 :
    trig12Tab.run sinCQ trig12Tab.FsQ 8 25 6 2 (dySt trig12_s8_6) = dySt trig12_s8_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s8_8_10 :
    trig12Tab.run sinCQ trig12Tab.FsQ 8 25 8 2 (dySt trig12_s8_8) = dySt trig12_s8_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s8_10_12 :
    trig12Tab.run sinCQ trig12Tab.FsQ 8 25 10 2 (dySt trig12_s8_10) = dySt trig12_s8_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s8_12_14 :
    trig12Tab.run sinCQ trig12Tab.FsQ 8 25 12 2 (dySt trig12_s8_12) = dySt trig12_s8_14 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s8_14_16 :
    trig12Tab.run sinCQ trig12Tab.FsQ 8 25 14 2 (dySt trig12_s8_14) = dySt trig12_s8_16 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s8_16_18 :
    trig12Tab.run sinCQ trig12Tab.FsQ 8 25 16 2 (dySt trig12_s8_16) = dySt trig12_s8_18 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s8_18_20 :
    trig12Tab.run sinCQ trig12Tab.FsQ 8 25 18 2 (dySt trig12_s8_18) = dySt trig12_s8_20 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s8_20_22 :
    trig12Tab.run sinCQ trig12Tab.FsQ 8 25 20 2 (dySt trig12_s8_20) = dySt trig12_s8_22 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s8_22_24 :
    trig12Tab.run sinCQ trig12Tab.FsQ 8 25 22 2 (dySt trig12_s8_22) = dySt trig12_s8_24 := by
  decide +kernel

end ExpansionBounds
