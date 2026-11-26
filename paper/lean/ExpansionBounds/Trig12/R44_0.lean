import ExpansionBounds.Trig12.S44

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 44

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s44_0_2 :
    trig12Tab.run sinCQ trig12Tab.FsQ 44 6 0 2 (trig12Tab.init sinCQ trig12Tab.FsQ 6) = dySt trig12_s44_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s44_2_4 :
    trig12Tab.run sinCQ trig12Tab.FsQ 44 6 2 2 (dySt trig12_s44_2) = dySt trig12_s44_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s44_4_5 :
    trig12Tab.run sinCQ trig12Tab.FsQ 44 6 4 1 (dySt trig12_s44_4) = dySt trig12_s44_5 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c44_0_2 :
    trig12Tab.run cosCQ trig12Tab.FcQ 44 6 0 2 (trig12Tab.init cosCQ trig12Tab.FcQ 6) = dySt trig12_c44_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c44_2_4 :
    trig12Tab.run cosCQ trig12Tab.FcQ 44 6 2 2 (dySt trig12_c44_2) = dySt trig12_c44_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c44_4_5 :
    trig12Tab.run cosCQ trig12Tab.FcQ 44 6 4 1 (dySt trig12_c44_4) = dySt trig12_c44_5 := by
  decide +kernel

end ExpansionBounds
