import ExpansionBounds.Trig12.S4

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 4

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s4_0_2 :
    trig12Tab.run sinCQ trig12Tab.FsQ 4 36 0 2 (trig12Tab.init sinCQ trig12Tab.FsQ 36) = dySt trig12_s4_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s4_2_4 :
    trig12Tab.run sinCQ trig12Tab.FsQ 4 36 2 2 (dySt trig12_s4_2) = dySt trig12_s4_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s4_4_6 :
    trig12Tab.run sinCQ trig12Tab.FsQ 4 36 4 2 (dySt trig12_s4_4) = dySt trig12_s4_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s4_6_8 :
    trig12Tab.run sinCQ trig12Tab.FsQ 4 36 6 2 (dySt trig12_s4_6) = dySt trig12_s4_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s4_8_10 :
    trig12Tab.run sinCQ trig12Tab.FsQ 4 36 8 2 (dySt trig12_s4_8) = dySt trig12_s4_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s4_10_12 :
    trig12Tab.run sinCQ trig12Tab.FsQ 4 36 10 2 (dySt trig12_s4_10) = dySt trig12_s4_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s4_12_14 :
    trig12Tab.run sinCQ trig12Tab.FsQ 4 36 12 2 (dySt trig12_s4_12) = dySt trig12_s4_14 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s4_14_16 :
    trig12Tab.run sinCQ trig12Tab.FsQ 4 36 14 2 (dySt trig12_s4_14) = dySt trig12_s4_16 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s4_16_18 :
    trig12Tab.run sinCQ trig12Tab.FsQ 4 36 16 2 (dySt trig12_s4_16) = dySt trig12_s4_18 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s4_18_20 :
    trig12Tab.run sinCQ trig12Tab.FsQ 4 36 18 2 (dySt trig12_s4_18) = dySt trig12_s4_20 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s4_20_22 :
    trig12Tab.run sinCQ trig12Tab.FsQ 4 36 20 2 (dySt trig12_s4_20) = dySt trig12_s4_22 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s4_22_24 :
    trig12Tab.run sinCQ trig12Tab.FsQ 4 36 22 2 (dySt trig12_s4_22) = dySt trig12_s4_24 := by
  decide +kernel

end ExpansionBounds
