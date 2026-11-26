import ExpansionBounds.Trig12.S38

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 38

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s38_0_2 :
    trig12Tab.run sinCQ trig12Tab.FsQ 38 7 0 2 (trig12Tab.init sinCQ trig12Tab.FsQ 7) = dySt trig12_s38_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s38_2_4 :
    trig12Tab.run sinCQ trig12Tab.FsQ 38 7 2 2 (dySt trig12_s38_2) = dySt trig12_s38_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s38_4_6 :
    trig12Tab.run sinCQ trig12Tab.FsQ 38 7 4 2 (dySt trig12_s38_4) = dySt trig12_s38_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c38_0_2 :
    trig12Tab.run cosCQ trig12Tab.FcQ 38 7 0 2 (trig12Tab.init cosCQ trig12Tab.FcQ 7) = dySt trig12_c38_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c38_2_4 :
    trig12Tab.run cosCQ trig12Tab.FcQ 38 7 2 2 (dySt trig12_c38_2) = dySt trig12_c38_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c38_4_6 :
    trig12Tab.run cosCQ trig12Tab.FcQ 38 7 4 2 (dySt trig12_c38_4) = dySt trig12_c38_6 := by
  decide +kernel

end ExpansionBounds
