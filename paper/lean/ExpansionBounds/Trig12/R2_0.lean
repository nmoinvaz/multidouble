import ExpansionBounds.Trig12.S2

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 2

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s2_0_2 :
    trig12Tab.run sinCQ trig12Tab.FsQ 2 45 0 2 (trig12Tab.init sinCQ trig12Tab.FsQ 45) = dySt trig12_s2_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s2_2_4 :
    trig12Tab.run sinCQ trig12Tab.FsQ 2 45 2 2 (dySt trig12_s2_2) = dySt trig12_s2_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s2_4_6 :
    trig12Tab.run sinCQ trig12Tab.FsQ 2 45 4 2 (dySt trig12_s2_4) = dySt trig12_s2_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s2_6_8 :
    trig12Tab.run sinCQ trig12Tab.FsQ 2 45 6 2 (dySt trig12_s2_6) = dySt trig12_s2_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s2_8_10 :
    trig12Tab.run sinCQ trig12Tab.FsQ 2 45 8 2 (dySt trig12_s2_8) = dySt trig12_s2_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s2_10_12 :
    trig12Tab.run sinCQ trig12Tab.FsQ 2 45 10 2 (dySt trig12_s2_10) = dySt trig12_s2_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s2_12_14 :
    trig12Tab.run sinCQ trig12Tab.FsQ 2 45 12 2 (dySt trig12_s2_12) = dySt trig12_s2_14 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s2_14_16 :
    trig12Tab.run sinCQ trig12Tab.FsQ 2 45 14 2 (dySt trig12_s2_14) = dySt trig12_s2_16 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s2_16_18 :
    trig12Tab.run sinCQ trig12Tab.FsQ 2 45 16 2 (dySt trig12_s2_16) = dySt trig12_s2_18 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s2_18_20 :
    trig12Tab.run sinCQ trig12Tab.FsQ 2 45 18 2 (dySt trig12_s2_18) = dySt trig12_s2_20 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s2_20_22 :
    trig12Tab.run sinCQ trig12Tab.FsQ 2 45 20 2 (dySt trig12_s2_20) = dySt trig12_s2_22 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s2_22_24 :
    trig12Tab.run sinCQ trig12Tab.FsQ 2 45 22 2 (dySt trig12_s2_22) = dySt trig12_s2_24 := by
  decide +kernel

end ExpansionBounds
