import ExpansionBounds.Trig12.S3

/-!
# Theorem 35 at `n = 12` and `p = 53`: pieces of Horner's runs in bucket 3

Each piece of at most 2 steps is checked by the kernel, from the state before it to the state after it. A module
holds at most 12 of them: at `n = 12` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem trig12_s3_0_2 :
    trig12Tab.run sinCQ trig12Tab.FsQ 3 40 0 2 (trig12Tab.init sinCQ trig12Tab.FsQ 40) = dySt trig12_s3_2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s3_2_4 :
    trig12Tab.run sinCQ trig12Tab.FsQ 3 40 2 2 (dySt trig12_s3_2) = dySt trig12_s3_4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s3_4_6 :
    trig12Tab.run sinCQ trig12Tab.FsQ 3 40 4 2 (dySt trig12_s3_4) = dySt trig12_s3_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s3_6_8 :
    trig12Tab.run sinCQ trig12Tab.FsQ 3 40 6 2 (dySt trig12_s3_6) = dySt trig12_s3_8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s3_8_10 :
    trig12Tab.run sinCQ trig12Tab.FsQ 3 40 8 2 (dySt trig12_s3_8) = dySt trig12_s3_10 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s3_10_12 :
    trig12Tab.run sinCQ trig12Tab.FsQ 3 40 10 2 (dySt trig12_s3_10) = dySt trig12_s3_12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s3_12_14 :
    trig12Tab.run sinCQ trig12Tab.FsQ 3 40 12 2 (dySt trig12_s3_12) = dySt trig12_s3_14 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s3_14_16 :
    trig12Tab.run sinCQ trig12Tab.FsQ 3 40 14 2 (dySt trig12_s3_14) = dySt trig12_s3_16 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s3_16_18 :
    trig12Tab.run sinCQ trig12Tab.FsQ 3 40 16 2 (dySt trig12_s3_16) = dySt trig12_s3_18 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s3_18_20 :
    trig12Tab.run sinCQ trig12Tab.FsQ 3 40 18 2 (dySt trig12_s3_18) = dySt trig12_s3_20 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s3_20_22 :
    trig12Tab.run sinCQ trig12Tab.FsQ 3 40 20 2 (dySt trig12_s3_20) = dySt trig12_s3_22 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig12_s3_22_24 :
    trig12Tab.run sinCQ trig12Tab.FsQ 3 40 22 2 (dySt trig12_s3_22) = dySt trig12_s3_24 := by
  decide +kernel

end ExpansionBounds
