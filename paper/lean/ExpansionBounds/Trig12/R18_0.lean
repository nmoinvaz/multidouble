import ExpansionBounds.Trig12.S18

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 18

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s18_0_2 :
    trig12Tab.run sinCQ trig12Tab.FsQ 18 14 0 2 (trig12Tab.init sinCQ trig12Tab.FsQ 14) = dySt trig12_s18_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s18_2_4 :
    trig12Tab.run sinCQ trig12Tab.FsQ 18 14 2 2 (dySt trig12_s18_2) = dySt trig12_s18_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s18_4_6 :
    trig12Tab.run sinCQ trig12Tab.FsQ 18 14 4 2 (dySt trig12_s18_4) = dySt trig12_s18_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s18_6_8 :
    trig12Tab.run sinCQ trig12Tab.FsQ 18 14 6 2 (dySt trig12_s18_6) = dySt trig12_s18_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s18_8_10 :
    trig12Tab.run sinCQ trig12Tab.FsQ 18 14 8 2 (dySt trig12_s18_8) = dySt trig12_s18_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s18_10_12 :
    trig12Tab.run sinCQ trig12Tab.FsQ 18 14 10 2 (dySt trig12_s18_10) = dySt trig12_s18_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s18_12_13 :
    trig12Tab.run sinCQ trig12Tab.FsQ 18 14 12 1 (dySt trig12_s18_12) = dySt trig12_s18_13 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c18_0_2 :
    trig12Tab.run cosCQ trig12Tab.FcQ 18 14 0 2 (trig12Tab.init cosCQ trig12Tab.FcQ 14) = dySt trig12_c18_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c18_2_4 :
    trig12Tab.run cosCQ trig12Tab.FcQ 18 14 2 2 (dySt trig12_c18_2) = dySt trig12_c18_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c18_4_6 :
    trig12Tab.run cosCQ trig12Tab.FcQ 18 14 4 2 (dySt trig12_c18_4) = dySt trig12_c18_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c18_6_8 :
    trig12Tab.run cosCQ trig12Tab.FcQ 18 14 6 2 (dySt trig12_c18_6) = dySt trig12_c18_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c18_8_10 :
    trig12Tab.run cosCQ trig12Tab.FcQ 18 14 8 2 (dySt trig12_c18_8) = dySt trig12_c18_10 := by
  decide +kernel

end ExpansionBounds
