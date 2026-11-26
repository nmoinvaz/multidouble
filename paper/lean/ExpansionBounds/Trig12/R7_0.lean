import ExpansionBounds.Trig12.S7

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 7

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s7_0_2 :
    trig12Tab.run sinCQ trig12Tab.FsQ 7 27 0 2 (trig12Tab.init sinCQ trig12Tab.FsQ 27) = dySt trig12_s7_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s7_2_4 :
    trig12Tab.run sinCQ trig12Tab.FsQ 7 27 2 2 (dySt trig12_s7_2) = dySt trig12_s7_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s7_4_6 :
    trig12Tab.run sinCQ trig12Tab.FsQ 7 27 4 2 (dySt trig12_s7_4) = dySt trig12_s7_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s7_6_8 :
    trig12Tab.run sinCQ trig12Tab.FsQ 7 27 6 2 (dySt trig12_s7_6) = dySt trig12_s7_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s7_8_10 :
    trig12Tab.run sinCQ trig12Tab.FsQ 7 27 8 2 (dySt trig12_s7_8) = dySt trig12_s7_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s7_10_12 :
    trig12Tab.run sinCQ trig12Tab.FsQ 7 27 10 2 (dySt trig12_s7_10) = dySt trig12_s7_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s7_12_14 :
    trig12Tab.run sinCQ trig12Tab.FsQ 7 27 12 2 (dySt trig12_s7_12) = dySt trig12_s7_14 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s7_14_16 :
    trig12Tab.run sinCQ trig12Tab.FsQ 7 27 14 2 (dySt trig12_s7_14) = dySt trig12_s7_16 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s7_16_18 :
    trig12Tab.run sinCQ trig12Tab.FsQ 7 27 16 2 (dySt trig12_s7_16) = dySt trig12_s7_18 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s7_18_20 :
    trig12Tab.run sinCQ trig12Tab.FsQ 7 27 18 2 (dySt trig12_s7_18) = dySt trig12_s7_20 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s7_20_22 :
    trig12Tab.run sinCQ trig12Tab.FsQ 7 27 20 2 (dySt trig12_s7_20) = dySt trig12_s7_22 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s7_22_24 :
    trig12Tab.run sinCQ trig12Tab.FsQ 7 27 22 2 (dySt trig12_s7_22) = dySt trig12_s7_24 := by
  decide +kernel

end ExpansionBounds
