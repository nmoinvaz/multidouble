import ExpansionBounds.Prop28.Data

/-!
# Proposition 28 (`prop:acc-low`): the accumulator's run on the terms 1537 to 1792

The kernel runs the accumulator on each chunk of 16 terms from the levels before it and checks the levels after it.
This file is written by `accumulator/acc_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1537 to 1552 -/
theorem acc28_c96 :
    (List.range 9).map (accRunQ 53 8 (acc28T96.map dyFn) (dyFn acc28S96)) = acc28S97.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1553 to 1568 -/
theorem acc28_c97 :
    (List.range 9).map (accRunQ 53 8 (acc28T97.map dyFn) (dyFn acc28S97)) = acc28S98.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1569 to 1584 -/
theorem acc28_c98 :
    (List.range 9).map (accRunQ 53 8 (acc28T98.map dyFn) (dyFn acc28S98)) = acc28S99.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1585 to 1600 -/
theorem acc28_c99 :
    (List.range 9).map (accRunQ 53 8 (acc28T99.map dyFn) (dyFn acc28S99)) = acc28S100.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1601 to 1616 -/
theorem acc28_c100 :
    (List.range 9).map (accRunQ 53 8 (acc28T100.map dyFn) (dyFn acc28S100)) = acc28S101.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1617 to 1632 -/
theorem acc28_c101 :
    (List.range 9).map (accRunQ 53 8 (acc28T101.map dyFn) (dyFn acc28S101)) = acc28S102.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1633 to 1648 -/
theorem acc28_c102 :
    (List.range 9).map (accRunQ 53 8 (acc28T102.map dyFn) (dyFn acc28S102)) = acc28S103.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1649 to 1664 -/
theorem acc28_c103 :
    (List.range 9).map (accRunQ 53 8 (acc28T103.map dyFn) (dyFn acc28S103)) = acc28S104.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1665 to 1680 -/
theorem acc28_c104 :
    (List.range 9).map (accRunQ 53 8 (acc28T104.map dyFn) (dyFn acc28S104)) = acc28S105.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1681 to 1696 -/
theorem acc28_c105 :
    (List.range 9).map (accRunQ 53 8 (acc28T105.map dyFn) (dyFn acc28S105)) = acc28S106.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1697 to 1712 -/
theorem acc28_c106 :
    (List.range 9).map (accRunQ 53 8 (acc28T106.map dyFn) (dyFn acc28S106)) = acc28S107.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1713 to 1728 -/
theorem acc28_c107 :
    (List.range 9).map (accRunQ 53 8 (acc28T107.map dyFn) (dyFn acc28S107)) = acc28S108.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1729 to 1744 -/
theorem acc28_c108 :
    (List.range 9).map (accRunQ 53 8 (acc28T108.map dyFn) (dyFn acc28S108)) = acc28S109.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1745 to 1760 -/
theorem acc28_c109 :
    (List.range 9).map (accRunQ 53 8 (acc28T109.map dyFn) (dyFn acc28S109)) = acc28S110.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1761 to 1776 -/
theorem acc28_c110 :
    (List.range 9).map (accRunQ 53 8 (acc28T110.map dyFn) (dyFn acc28S110)) = acc28S111.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1777 to 1792 -/
theorem acc28_c111 :
    (List.range 9).map (accRunQ 53 8 (acc28T111.map dyFn) (dyFn acc28S111)) = acc28S112.map dyQ := by
  decide +kernel

end ExpansionBounds
