import ExpansionBounds.Trig12.S13

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 13

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s13_0_2 :
    trig12Tab.run sinCQ trig12Tab.FsQ 13 18 0 2 (trig12Tab.init sinCQ trig12Tab.FsQ 18) = dySt trig12_s13_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s13_2_4 :
    trig12Tab.run sinCQ trig12Tab.FsQ 13 18 2 2 (dySt trig12_s13_2) = dySt trig12_s13_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s13_4_6 :
    trig12Tab.run sinCQ trig12Tab.FsQ 13 18 4 2 (dySt trig12_s13_4) = dySt trig12_s13_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s13_6_8 :
    trig12Tab.run sinCQ trig12Tab.FsQ 13 18 6 2 (dySt trig12_s13_6) = dySt trig12_s13_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s13_8_10 :
    trig12Tab.run sinCQ trig12Tab.FsQ 13 18 8 2 (dySt trig12_s13_8) = dySt trig12_s13_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s13_10_12 :
    trig12Tab.run sinCQ trig12Tab.FsQ 13 18 10 2 (dySt trig12_s13_10) = dySt trig12_s13_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s13_12_14 :
    trig12Tab.run sinCQ trig12Tab.FsQ 13 18 12 2 (dySt trig12_s13_12) = dySt trig12_s13_14 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s13_14_16 :
    trig12Tab.run sinCQ trig12Tab.FsQ 13 18 14 2 (dySt trig12_s13_14) = dySt trig12_s13_16 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s13_16_17 :
    trig12Tab.run sinCQ trig12Tab.FsQ 13 18 16 1 (dySt trig12_s13_16) = dySt trig12_s13_17 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c13_0_2 :
    trig12Tab.run cosCQ trig12Tab.FcQ 13 19 0 2 (trig12Tab.init cosCQ trig12Tab.FcQ 19) = dySt trig12_c13_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c13_2_4 :
    trig12Tab.run cosCQ trig12Tab.FcQ 13 19 2 2 (dySt trig12_c13_2) = dySt trig12_c13_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c13_4_6 :
    trig12Tab.run cosCQ trig12Tab.FcQ 13 19 4 2 (dySt trig12_c13_4) = dySt trig12_c13_6 := by
  decide +kernel

end ExpansionBounds
