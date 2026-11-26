import ExpansionBounds.Trig12.S26

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 26

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s26_0_2 :
    trig12Tab.run sinCQ trig12Tab.FsQ 26 10 0 2 (trig12Tab.init sinCQ trig12Tab.FsQ 10) = dySt trig12_s26_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s26_2_4 :
    trig12Tab.run sinCQ trig12Tab.FsQ 26 10 2 2 (dySt trig12_s26_2) = dySt trig12_s26_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s26_4_6 :
    trig12Tab.run sinCQ trig12Tab.FsQ 26 10 4 2 (dySt trig12_s26_4) = dySt trig12_s26_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s26_6_8 :
    trig12Tab.run sinCQ trig12Tab.FsQ 26 10 6 2 (dySt trig12_s26_6) = dySt trig12_s26_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s26_8_9 :
    trig12Tab.run sinCQ trig12Tab.FsQ 26 10 8 1 (dySt trig12_s26_8) = dySt trig12_s26_9 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c26_0_2 :
    trig12Tab.run cosCQ trig12Tab.FcQ 26 11 0 2 (trig12Tab.init cosCQ trig12Tab.FcQ 11) = dySt trig12_c26_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c26_2_4 :
    trig12Tab.run cosCQ trig12Tab.FcQ 26 11 2 2 (dySt trig12_c26_2) = dySt trig12_c26_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c26_4_6 :
    trig12Tab.run cosCQ trig12Tab.FcQ 26 11 4 2 (dySt trig12_c26_4) = dySt trig12_c26_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c26_6_8 :
    trig12Tab.run cosCQ trig12Tab.FcQ 26 11 6 2 (dySt trig12_c26_6) = dySt trig12_c26_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c26_8_10 :
    trig12Tab.run cosCQ trig12Tab.FcQ 26 11 8 2 (dySt trig12_c26_8) = dySt trig12_c26_10 := by
  decide +kernel

end ExpansionBounds
