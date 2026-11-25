import ExpansionBounds.Prop28.Data

/-!
# Proposition 28 (`prop:acc-low`): the accumulator's run on the terms 1281 to 1536

The kernel runs the accumulator on each chunk of 16 terms from the levels before it and checks the levels after it.
This file is written by `accumulator/acc_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1281 to 1296 -/
theorem acc28_c80 :
    (List.range 9).map (accRunQ 53 8 (acc28T80.map dyFn) (dyFn acc28S80)) = acc28S81.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1297 to 1312 -/
theorem acc28_c81 :
    (List.range 9).map (accRunQ 53 8 (acc28T81.map dyFn) (dyFn acc28S81)) = acc28S82.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1313 to 1328 -/
theorem acc28_c82 :
    (List.range 9).map (accRunQ 53 8 (acc28T82.map dyFn) (dyFn acc28S82)) = acc28S83.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1329 to 1344 -/
theorem acc28_c83 :
    (List.range 9).map (accRunQ 53 8 (acc28T83.map dyFn) (dyFn acc28S83)) = acc28S84.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1345 to 1360 -/
theorem acc28_c84 :
    (List.range 9).map (accRunQ 53 8 (acc28T84.map dyFn) (dyFn acc28S84)) = acc28S85.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1361 to 1376 -/
theorem acc28_c85 :
    (List.range 9).map (accRunQ 53 8 (acc28T85.map dyFn) (dyFn acc28S85)) = acc28S86.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1377 to 1392 -/
theorem acc28_c86 :
    (List.range 9).map (accRunQ 53 8 (acc28T86.map dyFn) (dyFn acc28S86)) = acc28S87.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1393 to 1408 -/
theorem acc28_c87 :
    (List.range 9).map (accRunQ 53 8 (acc28T87.map dyFn) (dyFn acc28S87)) = acc28S88.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1409 to 1424 -/
theorem acc28_c88 :
    (List.range 9).map (accRunQ 53 8 (acc28T88.map dyFn) (dyFn acc28S88)) = acc28S89.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1425 to 1440 -/
theorem acc28_c89 :
    (List.range 9).map (accRunQ 53 8 (acc28T89.map dyFn) (dyFn acc28S89)) = acc28S90.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1441 to 1456 -/
theorem acc28_c90 :
    (List.range 9).map (accRunQ 53 8 (acc28T90.map dyFn) (dyFn acc28S90)) = acc28S91.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1457 to 1472 -/
theorem acc28_c91 :
    (List.range 9).map (accRunQ 53 8 (acc28T91.map dyFn) (dyFn acc28S91)) = acc28S92.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1473 to 1488 -/
theorem acc28_c92 :
    (List.range 9).map (accRunQ 53 8 (acc28T92.map dyFn) (dyFn acc28S92)) = acc28S93.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1489 to 1504 -/
theorem acc28_c93 :
    (List.range 9).map (accRunQ 53 8 (acc28T93.map dyFn) (dyFn acc28S93)) = acc28S94.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1505 to 1520 -/
theorem acc28_c94 :
    (List.range 9).map (accRunQ 53 8 (acc28T94.map dyFn) (dyFn acc28S94)) = acc28S95.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1521 to 1536 -/
theorem acc28_c95 :
    (List.range 9).map (accRunQ 53 8 (acc28T95.map dyFn) (dyFn acc28S95)) = acc28S96.map dyQ := by
  decide +kernel

end ExpansionBounds
