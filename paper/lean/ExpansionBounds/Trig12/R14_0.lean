import ExpansionBounds.Trig12.S14

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 14

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s14_0_2 :
    trig12Tab.run sinCQ trig12Tab.FsQ 14 17 0 2 (trig12Tab.init sinCQ trig12Tab.FsQ 17) = dySt trig12_s14_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s14_2_4 :
    trig12Tab.run sinCQ trig12Tab.FsQ 14 17 2 2 (dySt trig12_s14_2) = dySt trig12_s14_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s14_4_6 :
    trig12Tab.run sinCQ trig12Tab.FsQ 14 17 4 2 (dySt trig12_s14_4) = dySt trig12_s14_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s14_6_8 :
    trig12Tab.run sinCQ trig12Tab.FsQ 14 17 6 2 (dySt trig12_s14_6) = dySt trig12_s14_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s14_8_10 :
    trig12Tab.run sinCQ trig12Tab.FsQ 14 17 8 2 (dySt trig12_s14_8) = dySt trig12_s14_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s14_10_12 :
    trig12Tab.run sinCQ trig12Tab.FsQ 14 17 10 2 (dySt trig12_s14_10) = dySt trig12_s14_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s14_12_14 :
    trig12Tab.run sinCQ trig12Tab.FsQ 14 17 12 2 (dySt trig12_s14_12) = dySt trig12_s14_14 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s14_14_16 :
    trig12Tab.run sinCQ trig12Tab.FsQ 14 17 14 2 (dySt trig12_s14_14) = dySt trig12_s14_16 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c14_0_2 :
    trig12Tab.run cosCQ trig12Tab.FcQ 14 18 0 2 (trig12Tab.init cosCQ trig12Tab.FcQ 18) = dySt trig12_c14_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c14_2_4 :
    trig12Tab.run cosCQ trig12Tab.FcQ 14 18 2 2 (dySt trig12_c14_2) = dySt trig12_c14_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c14_4_6 :
    trig12Tab.run cosCQ trig12Tab.FcQ 14 18 4 2 (dySt trig12_c14_4) = dySt trig12_c14_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c14_6_8 :
    trig12Tab.run cosCQ trig12Tab.FcQ 14 18 6 2 (dySt trig12_c14_6) = dySt trig12_c14_8 := by
  decide +kernel

end ExpansionBounds
