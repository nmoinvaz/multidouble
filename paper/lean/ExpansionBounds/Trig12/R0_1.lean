import ExpansionBounds.Trig12.S0

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 0

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s0_24_26 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 24 2 (dySt trig12_s0_24) = dySt trig12_s0_26 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s0_26_28 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 26 2 (dySt trig12_s0_26) = dySt trig12_s0_28 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s0_28_30 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 28 2 (dySt trig12_s0_28) = dySt trig12_s0_30 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s0_30_32 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 30 2 (dySt trig12_s0_30) = dySt trig12_s0_32 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s0_32_34 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 32 2 (dySt trig12_s0_32) = dySt trig12_s0_34 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s0_34_36 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 34 2 (dySt trig12_s0_34) = dySt trig12_s0_36 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s0_36_38 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 36 2 (dySt trig12_s0_36) = dySt trig12_s0_38 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s0_38_40 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 38 2 (dySt trig12_s0_38) = dySt trig12_s0_40 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s0_40_42 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 40 2 (dySt trig12_s0_40) = dySt trig12_s0_42 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s0_42_44 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 42 2 (dySt trig12_s0_42) = dySt trig12_s0_44 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s0_44_46 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 44 2 (dySt trig12_s0_44) = dySt trig12_s0_46 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s0_46_48 :
    trig12Tab.run sinCQ trig12Tab.FsQ 0 55 46 2 (dySt trig12_s0_46) = dySt trig12_s0_48 := by
  decide +kernel

end ExpansionBounds
