import ExpansionBounds.Trig12.S9

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 9

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s9_0_2 :
    trig12Tab.run sinCQ trig12Tab.FsQ 9 24 0 2 (trig12Tab.init sinCQ trig12Tab.FsQ 24) = dySt trig12_s9_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s9_2_4 :
    trig12Tab.run sinCQ trig12Tab.FsQ 9 24 2 2 (dySt trig12_s9_2) = dySt trig12_s9_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s9_4_6 :
    trig12Tab.run sinCQ trig12Tab.FsQ 9 24 4 2 (dySt trig12_s9_4) = dySt trig12_s9_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s9_6_8 :
    trig12Tab.run sinCQ trig12Tab.FsQ 9 24 6 2 (dySt trig12_s9_6) = dySt trig12_s9_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s9_8_10 :
    trig12Tab.run sinCQ trig12Tab.FsQ 9 24 8 2 (dySt trig12_s9_8) = dySt trig12_s9_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s9_10_12 :
    trig12Tab.run sinCQ trig12Tab.FsQ 9 24 10 2 (dySt trig12_s9_10) = dySt trig12_s9_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s9_12_14 :
    trig12Tab.run sinCQ trig12Tab.FsQ 9 24 12 2 (dySt trig12_s9_12) = dySt trig12_s9_14 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s9_14_16 :
    trig12Tab.run sinCQ trig12Tab.FsQ 9 24 14 2 (dySt trig12_s9_14) = dySt trig12_s9_16 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s9_16_18 :
    trig12Tab.run sinCQ trig12Tab.FsQ 9 24 16 2 (dySt trig12_s9_16) = dySt trig12_s9_18 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s9_18_20 :
    trig12Tab.run sinCQ trig12Tab.FsQ 9 24 18 2 (dySt trig12_s9_18) = dySt trig12_s9_20 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s9_20_22 :
    trig12Tab.run sinCQ trig12Tab.FsQ 9 24 20 2 (dySt trig12_s9_20) = dySt trig12_s9_22 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s9_22_23 :
    trig12Tab.run sinCQ trig12Tab.FsQ 9 24 22 1 (dySt trig12_s9_22) = dySt trig12_s9_23 := by
  decide +kernel

end ExpansionBounds
