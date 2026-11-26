import ExpansionBounds.Trig12.S2

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 2

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s2_24_26 :
    trig12Tab.run sinCQ trig12Tab.FsQ 2 45 24 2 (dySt trig12_s2_24) = dySt trig12_s2_26 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s2_26_28 :
    trig12Tab.run sinCQ trig12Tab.FsQ 2 45 26 2 (dySt trig12_s2_26) = dySt trig12_s2_28 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s2_28_30 :
    trig12Tab.run sinCQ trig12Tab.FsQ 2 45 28 2 (dySt trig12_s2_28) = dySt trig12_s2_30 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s2_30_32 :
    trig12Tab.run sinCQ trig12Tab.FsQ 2 45 30 2 (dySt trig12_s2_30) = dySt trig12_s2_32 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s2_32_34 :
    trig12Tab.run sinCQ trig12Tab.FsQ 2 45 32 2 (dySt trig12_s2_32) = dySt trig12_s2_34 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s2_34_36 :
    trig12Tab.run sinCQ trig12Tab.FsQ 2 45 34 2 (dySt trig12_s2_34) = dySt trig12_s2_36 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s2_36_38 :
    trig12Tab.run sinCQ trig12Tab.FsQ 2 45 36 2 (dySt trig12_s2_36) = dySt trig12_s2_38 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s2_38_40 :
    trig12Tab.run sinCQ trig12Tab.FsQ 2 45 38 2 (dySt trig12_s2_38) = dySt trig12_s2_40 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s2_40_42 :
    trig12Tab.run sinCQ trig12Tab.FsQ 2 45 40 2 (dySt trig12_s2_40) = dySt trig12_s2_42 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s2_42_44 :
    trig12Tab.run sinCQ trig12Tab.FsQ 2 45 42 2 (dySt trig12_s2_42) = dySt trig12_s2_44 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c2_0_2 :
    trig12Tab.run cosCQ trig12Tab.FcQ 2 45 0 2 (trig12Tab.init cosCQ trig12Tab.FcQ 45) = dySt trig12_c2_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c2_2_4 :
    trig12Tab.run cosCQ trig12Tab.FcQ 2 45 2 2 (dySt trig12_c2_2) = dySt trig12_c2_4 := by
  decide +kernel

end ExpansionBounds
