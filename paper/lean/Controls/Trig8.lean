import ExpansionBounds.Trig8

/-!
# Controls of Theorem 35's constant for the sine and the cosine

Each claim below is one of the kernel's checks of `Trig8.lean` with a wrong number, a wrong state or the wrong
coefficients, and the kernel proves its negation.
-/

namespace ExpansionBounds

open Finset

set_option maxHeartbeats 4000000 in
/-- the top bucket's `C` is not below `3.163167392u^8` -/
example : ¬ trigCQ trig8U 8 (sinDeltaL trig8U 8 (upQ 200) trig8Ab (trig8Rb 0) 41 (dySt trig8_s0_39))
    (cosDeltaL trig8U 8 (upQ 200) trig8Ab (trig8Rb 0) 41 (dySt trig8_c0_39)) (trig8Rb 0) ≤
      3163167392 / 1000000000 * trig8U ^ 8 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- two steps of Horner's run from the state after two steps do not give the state after six -/
example : ¬ trig8Run sinCQ trig8FsQ 0 40 2 2 (dySt trig8_s0_2) = dySt trig8_s0_6 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the sine's steps on the cosine's coefficients do not give the sine's state -/
example : ¬ trig8Run sinCQ trig8FcQ 0 40 0 2 (trig8Init sinCQ trig8FcQ 40) = dySt trig8_s0_2 := by
  decide +kernel

/-- below the last bucket SINR is not within `u^8/7` -/
example : ¬ trig8T ^ 2 / (6 - trig8T ^ 2) ≤ 1 / 7 * trig8U ^ 8 := by
  decide +kernel

/-- rounding `1/3` up to 200 bits raises it -/
example : ¬ upQ 200 (1 / 3) ≤ 1 / 3 := by
  decide +kernel

/-- a coefficient with a part of 54 bits is not in `F` -/
example : ¬ rnQ 53 (dyQ (9007199254740993, 60)) = dyQ (9007199254740993, 60) := by
  decide +kernel

/-- the series do not have three terms in every bucket -/
example : ¬ ∀ g ∈ trig8Groups, 3 ≤ g.2.1 := by
  decide +kernel

/-! ### The buckets below the top one -/

set_option maxHeartbeats 4000000 in
/-- the top bucket's `C` is not within the bound of the buckets with `|r_0| < 1/2` -/
example : ¬ trig8CLe (trig8Low 1) 0 41 41 (dySt trig8_s0_39) (dySt trig8_c0_39) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- `C` of the bucket from `1/4` to `1/2` is not below `2.175821u^8` -/
example : ¬ trig8CLe (2175821 / 1000000) 1 37 38 (dySt trig8_s1_35) (dySt trig8_c1_36) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- nor within the bound of the buckets with `|r_0| < 2^{-5}` -/
example : ¬ trig8CLe (trig8Low 5) 1 37 38 (dySt trig8_s1_35) (dySt trig8_c1_36) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- `C` of bucket 52 is not below `2.000705u^8` -/
example : ¬ trig8CLe (2000705 / 1000000) 52 4 5 (dySt trig8_s52_2) (dySt trig8_c52_3) := by
  decide +kernel

end ExpansionBounds
