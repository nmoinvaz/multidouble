import ExpansionBounds.Trig12.S27

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 27

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s27_0_2 :
    trig12Tab.run sinCQ trig12Tab.FsQ 27 10 0 2 (trig12Tab.init sinCQ trig12Tab.FsQ 10) = dySt trig12_s27_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s27_2_4 :
    trig12Tab.run sinCQ trig12Tab.FsQ 27 10 2 2 (dySt trig12_s27_2) = dySt trig12_s27_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s27_4_6 :
    trig12Tab.run sinCQ trig12Tab.FsQ 27 10 4 2 (dySt trig12_s27_4) = dySt trig12_s27_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s27_6_8 :
    trig12Tab.run sinCQ trig12Tab.FsQ 27 10 6 2 (dySt trig12_s27_6) = dySt trig12_s27_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s27_8_9 :
    trig12Tab.run sinCQ trig12Tab.FsQ 27 10 8 1 (dySt trig12_s27_8) = dySt trig12_s27_9 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c27_0_2 :
    trig12Tab.run cosCQ trig12Tab.FcQ 27 10 0 2 (trig12Tab.init cosCQ trig12Tab.FcQ 10) = dySt trig12_c27_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c27_2_4 :
    trig12Tab.run cosCQ trig12Tab.FcQ 27 10 2 2 (dySt trig12_c27_2) = dySt trig12_c27_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c27_4_6 :
    trig12Tab.run cosCQ trig12Tab.FcQ 27 10 4 2 (dySt trig12_c27_4) = dySt trig12_c27_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c27_6_8 :
    trig12Tab.run cosCQ trig12Tab.FcQ 27 10 6 2 (dySt trig12_c27_6) = dySt trig12_c27_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c27_8_9 :
    trig12Tab.run cosCQ trig12Tab.FcQ 27 10 8 1 (dySt trig12_c27_8) = dySt trig12_c27_9 := by
  decide +kernel

end ExpansionBounds
