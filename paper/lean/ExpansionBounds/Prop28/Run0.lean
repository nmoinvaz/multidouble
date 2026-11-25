import ExpansionBounds.Prop28.Data

/-!
# Proposition 28 (`prop:acc-low`): the accumulator's run on the terms 1 to 256

The kernel runs the accumulator on each chunk of 16 terms from the levels before it and checks the levels after it.
This file is written by `accumulator/acc_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1 to 16 -/
theorem acc28_c0 :
    (List.range 9).map (accRunQ 53 8 (acc28T0.map dyFn) fun _ => 0) = acc28S1.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 17 to 32 -/
theorem acc28_c1 :
    (List.range 9).map (accRunQ 53 8 (acc28T1.map dyFn) (dyFn acc28S1)) = acc28S2.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 33 to 48 -/
theorem acc28_c2 :
    (List.range 9).map (accRunQ 53 8 (acc28T2.map dyFn) (dyFn acc28S2)) = acc28S3.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 49 to 64 -/
theorem acc28_c3 :
    (List.range 9).map (accRunQ 53 8 (acc28T3.map dyFn) (dyFn acc28S3)) = acc28S4.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 65 to 80 -/
theorem acc28_c4 :
    (List.range 9).map (accRunQ 53 8 (acc28T4.map dyFn) (dyFn acc28S4)) = acc28S5.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 81 to 96 -/
theorem acc28_c5 :
    (List.range 9).map (accRunQ 53 8 (acc28T5.map dyFn) (dyFn acc28S5)) = acc28S6.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 97 to 112 -/
theorem acc28_c6 :
    (List.range 9).map (accRunQ 53 8 (acc28T6.map dyFn) (dyFn acc28S6)) = acc28S7.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 113 to 128 -/
theorem acc28_c7 :
    (List.range 9).map (accRunQ 53 8 (acc28T7.map dyFn) (dyFn acc28S7)) = acc28S8.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 129 to 144 -/
theorem acc28_c8 :
    (List.range 9).map (accRunQ 53 8 (acc28T8.map dyFn) (dyFn acc28S8)) = acc28S9.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 145 to 160 -/
theorem acc28_c9 :
    (List.range 9).map (accRunQ 53 8 (acc28T9.map dyFn) (dyFn acc28S9)) = acc28S10.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 161 to 176 -/
theorem acc28_c10 :
    (List.range 9).map (accRunQ 53 8 (acc28T10.map dyFn) (dyFn acc28S10)) = acc28S11.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 177 to 192 -/
theorem acc28_c11 :
    (List.range 9).map (accRunQ 53 8 (acc28T11.map dyFn) (dyFn acc28S11)) = acc28S12.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 193 to 208 -/
theorem acc28_c12 :
    (List.range 9).map (accRunQ 53 8 (acc28T12.map dyFn) (dyFn acc28S12)) = acc28S13.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 209 to 224 -/
theorem acc28_c13 :
    (List.range 9).map (accRunQ 53 8 (acc28T13.map dyFn) (dyFn acc28S13)) = acc28S14.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 225 to 240 -/
theorem acc28_c14 :
    (List.range 9).map (accRunQ 53 8 (acc28T14.map dyFn) (dyFn acc28S14)) = acc28S15.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 241 to 256 -/
theorem acc28_c15 :
    (List.range 9).map (accRunQ 53 8 (acc28T15.map dyFn) (dyFn acc28S15)) = acc28S16.map dyQ := by
  decide +kernel

end ExpansionBounds
