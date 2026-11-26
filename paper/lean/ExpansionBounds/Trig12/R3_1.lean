import ExpansionBounds.Trig12.S3

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 3

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s3_24_26 :
    trig12Tab.run sinCQ trig12Tab.FsQ 3 40 24 2 (dySt trig12_s3_24) = dySt trig12_s3_26 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s3_26_28 :
    trig12Tab.run sinCQ trig12Tab.FsQ 3 40 26 2 (dySt trig12_s3_26) = dySt trig12_s3_28 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s3_28_30 :
    trig12Tab.run sinCQ trig12Tab.FsQ 3 40 28 2 (dySt trig12_s3_28) = dySt trig12_s3_30 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s3_30_32 :
    trig12Tab.run sinCQ trig12Tab.FsQ 3 40 30 2 (dySt trig12_s3_30) = dySt trig12_s3_32 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s3_32_34 :
    trig12Tab.run sinCQ trig12Tab.FsQ 3 40 32 2 (dySt trig12_s3_32) = dySt trig12_s3_34 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s3_34_36 :
    trig12Tab.run sinCQ trig12Tab.FsQ 3 40 34 2 (dySt trig12_s3_34) = dySt trig12_s3_36 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s3_36_38 :
    trig12Tab.run sinCQ trig12Tab.FsQ 3 40 36 2 (dySt trig12_s3_36) = dySt trig12_s3_38 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s3_38_39 :
    trig12Tab.run sinCQ trig12Tab.FsQ 3 40 38 1 (dySt trig12_s3_38) = dySt trig12_s3_39 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c3_0_2 :
    trig12Tab.run cosCQ trig12Tab.FcQ 3 40 0 2 (trig12Tab.init cosCQ trig12Tab.FcQ 40) = dySt trig12_c3_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c3_2_4 :
    trig12Tab.run cosCQ trig12Tab.FcQ 3 40 2 2 (dySt trig12_c3_2) = dySt trig12_c3_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c3_4_6 :
    trig12Tab.run cosCQ trig12Tab.FcQ 3 40 4 2 (dySt trig12_c3_4) = dySt trig12_c3_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_c3_6_8 :
    trig12Tab.run cosCQ trig12Tab.FcQ 3 40 6 2 (dySt trig12_c3_6) = dySt trig12_c3_8 := by
  decide +kernel

end ExpansionBounds
