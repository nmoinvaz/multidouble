import ExpansionBounds.Trig12.S0

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 0

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s0_0_2 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 0 2 (trig12Tab.init sinCQ trig12Tab.FsQ 55) = dySt trig12_s0_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s0_2_4 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 2 2 (dySt trig12_s0_2) = dySt trig12_s0_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s0_4_6 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 4 2 (dySt trig12_s0_4) = dySt trig12_s0_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s0_6_8 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 6 2 (dySt trig12_s0_6) = dySt trig12_s0_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s0_8_10 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 8 2 (dySt trig12_s0_8) = dySt trig12_s0_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s0_10_12 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 10 2 (dySt trig12_s0_10) = dySt trig12_s0_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s0_12_14 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 12 2 (dySt trig12_s0_12) = dySt trig12_s0_14 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s0_14_16 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 14 2 (dySt trig12_s0_14) = dySt trig12_s0_16 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s0_16_18 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 16 2 (dySt trig12_s0_16) = dySt trig12_s0_18 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s0_18_20 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 18 2 (dySt trig12_s0_18) = dySt trig12_s0_20 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s0_20_22 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 20 2 (dySt trig12_s0_20) = dySt trig12_s0_22 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s0_22_24 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 22 2 (dySt trig12_s0_22) = dySt trig12_s0_24 := by
  decide +kernel

end ExpansionBounds
