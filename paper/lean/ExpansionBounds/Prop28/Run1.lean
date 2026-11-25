import ExpansionBounds.Prop28.Data

/-!
# Proposition 28 (`prop:acc-low`): the accumulator's run on the terms 257 to 512

The kernel runs the accumulator on each chunk of 16 terms from the levels before it and checks the levels after it.
This file is written by `accumulator/acc_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 257 to 272 -/
theorem acc28_c16 :
    (List.range 9).map (accRunQ 53 8 (acc28T16.map dyFn) (dyFn acc28S16)) = acc28S17.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 273 to 288 -/
theorem acc28_c17 :
    (List.range 9).map (accRunQ 53 8 (acc28T17.map dyFn) (dyFn acc28S17)) = acc28S18.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 289 to 304 -/
theorem acc28_c18 :
    (List.range 9).map (accRunQ 53 8 (acc28T18.map dyFn) (dyFn acc28S18)) = acc28S19.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 305 to 320 -/
theorem acc28_c19 :
    (List.range 9).map (accRunQ 53 8 (acc28T19.map dyFn) (dyFn acc28S19)) = acc28S20.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 321 to 336 -/
theorem acc28_c20 :
    (List.range 9).map (accRunQ 53 8 (acc28T20.map dyFn) (dyFn acc28S20)) = acc28S21.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 337 to 352 -/
theorem acc28_c21 :
    (List.range 9).map (accRunQ 53 8 (acc28T21.map dyFn) (dyFn acc28S21)) = acc28S22.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 353 to 368 -/
theorem acc28_c22 :
    (List.range 9).map (accRunQ 53 8 (acc28T22.map dyFn) (dyFn acc28S22)) = acc28S23.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 369 to 384 -/
theorem acc28_c23 :
    (List.range 9).map (accRunQ 53 8 (acc28T23.map dyFn) (dyFn acc28S23)) = acc28S24.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 385 to 400 -/
theorem acc28_c24 :
    (List.range 9).map (accRunQ 53 8 (acc28T24.map dyFn) (dyFn acc28S24)) = acc28S25.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 401 to 416 -/
theorem acc28_c25 :
    (List.range 9).map (accRunQ 53 8 (acc28T25.map dyFn) (dyFn acc28S25)) = acc28S26.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 417 to 432 -/
theorem acc28_c26 :
    (List.range 9).map (accRunQ 53 8 (acc28T26.map dyFn) (dyFn acc28S26)) = acc28S27.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 433 to 448 -/
theorem acc28_c27 :
    (List.range 9).map (accRunQ 53 8 (acc28T27.map dyFn) (dyFn acc28S27)) = acc28S28.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 449 to 464 -/
theorem acc28_c28 :
    (List.range 9).map (accRunQ 53 8 (acc28T28.map dyFn) (dyFn acc28S28)) = acc28S29.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 465 to 480 -/
theorem acc28_c29 :
    (List.range 9).map (accRunQ 53 8 (acc28T29.map dyFn) (dyFn acc28S29)) = acc28S30.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 481 to 496 -/
theorem acc28_c30 :
    (List.range 9).map (accRunQ 53 8 (acc28T30.map dyFn) (dyFn acc28S30)) = acc28S31.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 497 to 512 -/
theorem acc28_c31 :
    (List.range 9).map (accRunQ 53 8 (acc28T31.map dyFn) (dyFn acc28S31)) = acc28S32.map dyQ := by
  decide +kernel

end ExpansionBounds
