import ExpansionBounds.Prop28.Data

/-!
# Proposition 28 (`prop:acc-low`): the accumulator's run on the terms 1025 to 1280

The kernel runs the accumulator on each chunk of 16 terms from the levels before it and checks the levels after it.
This file is written by `accumulator/acc_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1025 to 1040 -/
theorem acc28_c64 :
    (List.range 9).map (accRunQ 53 8 (acc28T64.map dyFn) (dyFn acc28S64)) = acc28S65.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1041 to 1056 -/
theorem acc28_c65 :
    (List.range 9).map (accRunQ 53 8 (acc28T65.map dyFn) (dyFn acc28S65)) = acc28S66.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1057 to 1072 -/
theorem acc28_c66 :
    (List.range 9).map (accRunQ 53 8 (acc28T66.map dyFn) (dyFn acc28S66)) = acc28S67.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1073 to 1088 -/
theorem acc28_c67 :
    (List.range 9).map (accRunQ 53 8 (acc28T67.map dyFn) (dyFn acc28S67)) = acc28S68.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1089 to 1104 -/
theorem acc28_c68 :
    (List.range 9).map (accRunQ 53 8 (acc28T68.map dyFn) (dyFn acc28S68)) = acc28S69.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1105 to 1120 -/
theorem acc28_c69 :
    (List.range 9).map (accRunQ 53 8 (acc28T69.map dyFn) (dyFn acc28S69)) = acc28S70.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1121 to 1136 -/
theorem acc28_c70 :
    (List.range 9).map (accRunQ 53 8 (acc28T70.map dyFn) (dyFn acc28S70)) = acc28S71.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1137 to 1152 -/
theorem acc28_c71 :
    (List.range 9).map (accRunQ 53 8 (acc28T71.map dyFn) (dyFn acc28S71)) = acc28S72.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1153 to 1168 -/
theorem acc28_c72 :
    (List.range 9).map (accRunQ 53 8 (acc28T72.map dyFn) (dyFn acc28S72)) = acc28S73.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1169 to 1184 -/
theorem acc28_c73 :
    (List.range 9).map (accRunQ 53 8 (acc28T73.map dyFn) (dyFn acc28S73)) = acc28S74.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1185 to 1200 -/
theorem acc28_c74 :
    (List.range 9).map (accRunQ 53 8 (acc28T74.map dyFn) (dyFn acc28S74)) = acc28S75.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1201 to 1216 -/
theorem acc28_c75 :
    (List.range 9).map (accRunQ 53 8 (acc28T75.map dyFn) (dyFn acc28S75)) = acc28S76.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1217 to 1232 -/
theorem acc28_c76 :
    (List.range 9).map (accRunQ 53 8 (acc28T76.map dyFn) (dyFn acc28S76)) = acc28S77.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1233 to 1248 -/
theorem acc28_c77 :
    (List.range 9).map (accRunQ 53 8 (acc28T77.map dyFn) (dyFn acc28S77)) = acc28S78.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1249 to 1264 -/
theorem acc28_c78 :
    (List.range 9).map (accRunQ 53 8 (acc28T78.map dyFn) (dyFn acc28S78)) = acc28S79.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1265 to 1280 -/
theorem acc28_c79 :
    (List.range 9).map (accRunQ 53 8 (acc28T79.map dyFn) (dyFn acc28S79)) = acc28S80.map dyQ := by
  decide +kernel

end ExpansionBounds
