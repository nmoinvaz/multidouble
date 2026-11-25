import ExpansionBounds.Tan8

/-!
# Controls of Theorem 35's constant for the tangent

Each claim below is one of the kernel's checks of `Tan8.lean` with a wrong number or a narrower ladder, and the
kernel proves its negation.
-/

namespace ExpansionBounds

open Finset

set_option maxHeartbeats 4000000 in
/-- the top bucket's `C^T` is not below `6.41835052u^8` -/
example : ¬ tanCTQ trig8U 8 (sinDeltaL trig8U 8 (upQ 200) trig8Ab (trig8Rb 0) 41 (dySt trig8_s0_39))
    (cosDeltaL trig8U 8 (upQ 200) trig8Ab (trig8Rb 0) 41 (dySt trig8_c0_39))
    (trig8U ^ 8 + 103232124 * trig8U ^ 9) (trig8Rb 0) ≤ 641835052 / 100000000 * trig8U ^ 8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the computed sine and cosine of the top bucket are not on `H(1)` -/
example : ¬ tan8Chk (trig8Rb 0) (sinDeltaL trig8U 8 (upQ 200) trig8Ab (trig8Rb 0) 41 (dySt trig8_s0_39))
    (cosDeltaL trig8U 8 (upQ 200) trig8Ab (trig8Rb 0) 41 (dySt trig8_c0_39))
    (sinPsiL trig8U 8 (upQ 200) trig8Ab (trig8Rb 0) 41 (dySt trig8_s0_39))
    (cosPsiL trig8U 8 (upQ 200) trig8Ab (trig8Rb 0) 41 (dySt trig8_c0_39)) 1 103232124 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- `κ_DIV` at `θ = 1.4143` is above `103232123` -/
example : ¬ kdivQ trig8U 8 (14143 / 10000 * trig8U) ≤ 103232123 := by
  decide +kernel

/-- below the last bucket `r` over its lower bound is not on `H(2)` -/
example : ¬ tan8Chk trig8T (trig8T ^ 2 / (6 - trig8T ^ 2)) (trig8T ^ 2 / (2 * cosLoQ trig8T))
    (fun i => if i < 8 then trig8Ab i else 0) (fun i => if i = 0 then 1 else 0) 2 461400803 := by
  decide +kernel

/-- the early return is not within `u^8/4` -/
example : ¬ tanHiQ trig8T / trig8T - 1 ≤ 1 / 4 * trig8U ^ 8 := by
  decide +kernel

/-! ### The buckets below the top one -/

set_option maxHeartbeats 4000000 in
/-- the top bucket's `C^T` is not within the bound of the buckets with `|r_0| < 1/2` -/
example : ¬ tan8CtLe (tan8Low 1) 0 41 41 (dySt trig8_s0_39) (dySt trig8_c0_39) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- `C^T` of the bucket from `1/4` to `1/2` is not below `4.800525u^8` -/
example : ¬ tan8CtLe (4800525 / 1000000) 1 37 38 (dySt trig8_s1_35) (dySt trig8_c1_36) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- nor within the bound of the buckets with `|r_0| < 2^{-5}` -/
example : ¬ tan8CtLe (tan8Low 5) 1 37 38 (dySt trig8_s1_35) (dySt trig8_c1_36) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- `C^T` of bucket 5 is not below `4.002770u^8` -/
example : ¬ tan8CtLe (4002770 / 1000000) 5 24 24 (dySt trig8_s5_22) (dySt trig8_c5_22) := by
  decide +kernel

end ExpansionBounds
