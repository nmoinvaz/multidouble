import ExpansionBounds.Trig12.S5

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 5

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s5_0_2 :
    trig12Tab.run sinCQ trig12Tab.FsQ 5 33 0 2 (trig12Tab.init sinCQ trig12Tab.FsQ 33) = dySt trig12_s5_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s5_2_4 :
    trig12Tab.run sinCQ trig12Tab.FsQ 5 33 2 2 (dySt trig12_s5_2) = dySt trig12_s5_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s5_4_6 :
    trig12Tab.run sinCQ trig12Tab.FsQ 5 33 4 2 (dySt trig12_s5_4) = dySt trig12_s5_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s5_6_8 :
    trig12Tab.run sinCQ trig12Tab.FsQ 5 33 6 2 (dySt trig12_s5_6) = dySt trig12_s5_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s5_8_10 :
    trig12Tab.run sinCQ trig12Tab.FsQ 5 33 8 2 (dySt trig12_s5_8) = dySt trig12_s5_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s5_10_12 :
    trig12Tab.run sinCQ trig12Tab.FsQ 5 33 10 2 (dySt trig12_s5_10) = dySt trig12_s5_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s5_12_14 :
    trig12Tab.run sinCQ trig12Tab.FsQ 5 33 12 2 (dySt trig12_s5_12) = dySt trig12_s5_14 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s5_14_16 :
    trig12Tab.run sinCQ trig12Tab.FsQ 5 33 14 2 (dySt trig12_s5_14) = dySt trig12_s5_16 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s5_16_18 :
    trig12Tab.run sinCQ trig12Tab.FsQ 5 33 16 2 (dySt trig12_s5_16) = dySt trig12_s5_18 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s5_18_20 :
    trig12Tab.run sinCQ trig12Tab.FsQ 5 33 18 2 (dySt trig12_s5_18) = dySt trig12_s5_20 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s5_20_22 :
    trig12Tab.run sinCQ trig12Tab.FsQ 5 33 20 2 (dySt trig12_s5_20) = dySt trig12_s5_22 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s5_22_24 :
    trig12Tab.run sinCQ trig12Tab.FsQ 5 33 22 2 (dySt trig12_s5_22) = dySt trig12_s5_24 := by
  decide +kernel

end ExpansionBounds
