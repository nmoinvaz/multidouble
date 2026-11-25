import ExpansionBounds.Trig2
import ExpansionBounds.Trig4

/-!
# Controls of the remark after Theorem 35: the bounds at `n = 2` and `4`

Each claim below is one of the kernel's checks of `Trig2.lean` and `Trig4.lean` with a bound one unit lower in its
last digit, in the run of buckets where it is largest, or with a bound on `κ_DIV` one unit lower, and the kernel
proves its negation. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

open Finset

set_option maxHeartbeats 4000000 in
/-- at `n = 2`, `C` in bucket 0 is not below `3.168700u^2` -/
example : ¬ trigCQ trig8U 2 (sinDeltaL trig8U 2 (upQ 200) trig8Ab (trig8Rb 0) 15 (dySt trig2_s0_13))
    (cosDeltaL trig8U 2 (upQ 200) trig8Ab (trig8Rb 0) 15 (dySt trig2_c0_13)) (trig8Rb 0) ≤
      3168700 / 1000000 * trig8U ^ 2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- at `n = 2`, the tangent's check in bucket 0 fails with `6.452137u^2` -/
example : ¬ trig2Tab.TanOk (6452137 / 1000000) trig2Kd0 trig2Kd3 0 15 15 (dySt trig2_s0_13)
    (dySt trig2_c0_13) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- at `n = 2`, `κ_DIV(1.4143u)` is not within `197` -/
example : ¬ trig2Tab.KdivOk 197 trig2Kd3 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- at `n = 2`, `κ_DIV(3u)` is not within `498` -/
example : ¬ trig2Tab.KdivOk trig2Kd0 498 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- at `n = 4`, `C` in bucket 0 is not below `3.164154u^4` -/
example : ¬ trigCQ trig8U 4 (sinDeltaL trig8U 4 (upQ 200) trig8Ab (trig8Rb 0) 24 (dySt trig4_s0_22))
    (cosDeltaL trig8U 4 (upQ 200) trig8Ab (trig8Rb 0) 25 (dySt trig4_c0_23)) (trig8Rb 0) ≤
      3164154 / 1000000 * trig8U ^ 4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- at `n = 4`, the tangent's check in bucket 0 fails with `6.426154u^4` -/
example : ¬ trig4Tab.TanOk (6426154 / 1000000) trig4Kd0 trig4Kd3 0 24 25 (dySt trig4_s0_22)
    (dySt trig4_c0_23) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- at `n = 4`, `κ_DIV(1.4143u)` is not within `8933` -/
example : ¬ trig4Tab.KdivOk 8933 trig4Kd3 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- at `n = 4`, `κ_DIV(3u)` is not within `35874` -/
example : ¬ trig4Tab.KdivOk trig4Kd0 35874 := by
  decide +kernel

end ExpansionBounds
