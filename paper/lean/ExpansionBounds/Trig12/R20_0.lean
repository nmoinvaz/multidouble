import ExpansionBounds.Trig12.S20

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 20

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s20_0_2 :
    trig12Tab.run sinCQ trig12Tab.FsQ 20 13 0 2 (trig12Tab.init sinCQ trig12Tab.FsQ 13) = dySt trig12_s20_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s20_2_4 :
    trig12Tab.run sinCQ trig12Tab.FsQ 20 13 2 2 (dySt trig12_s20_2) = dySt trig12_s20_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s20_4_6 :
    trig12Tab.run sinCQ trig12Tab.FsQ 20 13 4 2 (dySt trig12_s20_4) = dySt trig12_s20_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s20_6_8 :
    trig12Tab.run sinCQ trig12Tab.FsQ 20 13 6 2 (dySt trig12_s20_6) = dySt trig12_s20_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s20_8_10 :
    trig12Tab.run sinCQ trig12Tab.FsQ 20 13 8 2 (dySt trig12_s20_8) = dySt trig12_s20_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s20_10_12 :
    trig12Tab.run sinCQ trig12Tab.FsQ 20 13 10 2 (dySt trig12_s20_10) = dySt trig12_s20_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c20_0_2 :
    trig12Tab.run cosCQ trig12Tab.FcQ 20 13 0 2 (trig12Tab.init cosCQ trig12Tab.FcQ 13) = dySt trig12_c20_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c20_2_4 :
    trig12Tab.run cosCQ trig12Tab.FcQ 20 13 2 2 (dySt trig12_c20_2) = dySt trig12_c20_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c20_4_6 :
    trig12Tab.run cosCQ trig12Tab.FcQ 20 13 4 2 (dySt trig12_c20_4) = dySt trig12_c20_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c20_6_8 :
    trig12Tab.run cosCQ trig12Tab.FcQ 20 13 6 2 (dySt trig12_c20_6) = dySt trig12_c20_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c20_8_10 :
    trig12Tab.run cosCQ trig12Tab.FcQ 20 13 8 2 (dySt trig12_c20_8) = dySt trig12_c20_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c20_10_12 :
    trig12Tab.run cosCQ trig12Tab.FcQ 20 13 10 2 (dySt trig12_c20_10) = dySt trig12_c20_12 := by
  decide +kernel

end ExpansionBounds
