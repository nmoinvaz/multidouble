import ExpansionBounds.Prop28.Data

/-!
# Proposition 28 (`prop:acc-low`): the accumulator's run on the terms 769 to 1024

The kernel runs the accumulator on each chunk of 16 terms from the levels before it and checks the levels after it.
This file is written by `accumulator/acc_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 769 to 784 -/
theorem acc28_c48 :
    (List.range 9).map (accRunQ 53 8 (acc28T48.map dyFn) (dyFn acc28S48)) = acc28S49.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 785 to 800 -/
theorem acc28_c49 :
    (List.range 9).map (accRunQ 53 8 (acc28T49.map dyFn) (dyFn acc28S49)) = acc28S50.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 801 to 816 -/
theorem acc28_c50 :
    (List.range 9).map (accRunQ 53 8 (acc28T50.map dyFn) (dyFn acc28S50)) = acc28S51.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 817 to 832 -/
theorem acc28_c51 :
    (List.range 9).map (accRunQ 53 8 (acc28T51.map dyFn) (dyFn acc28S51)) = acc28S52.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 833 to 848 -/
theorem acc28_c52 :
    (List.range 9).map (accRunQ 53 8 (acc28T52.map dyFn) (dyFn acc28S52)) = acc28S53.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 849 to 864 -/
theorem acc28_c53 :
    (List.range 9).map (accRunQ 53 8 (acc28T53.map dyFn) (dyFn acc28S53)) = acc28S54.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 865 to 880 -/
theorem acc28_c54 :
    (List.range 9).map (accRunQ 53 8 (acc28T54.map dyFn) (dyFn acc28S54)) = acc28S55.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 881 to 896 -/
theorem acc28_c55 :
    (List.range 9).map (accRunQ 53 8 (acc28T55.map dyFn) (dyFn acc28S55)) = acc28S56.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 897 to 912 -/
theorem acc28_c56 :
    (List.range 9).map (accRunQ 53 8 (acc28T56.map dyFn) (dyFn acc28S56)) = acc28S57.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 913 to 928 -/
theorem acc28_c57 :
    (List.range 9).map (accRunQ 53 8 (acc28T57.map dyFn) (dyFn acc28S57)) = acc28S58.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 929 to 944 -/
theorem acc28_c58 :
    (List.range 9).map (accRunQ 53 8 (acc28T58.map dyFn) (dyFn acc28S58)) = acc28S59.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 945 to 960 -/
theorem acc28_c59 :
    (List.range 9).map (accRunQ 53 8 (acc28T59.map dyFn) (dyFn acc28S59)) = acc28S60.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 961 to 976 -/
theorem acc28_c60 :
    (List.range 9).map (accRunQ 53 8 (acc28T60.map dyFn) (dyFn acc28S60)) = acc28S61.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 977 to 992 -/
theorem acc28_c61 :
    (List.range 9).map (accRunQ 53 8 (acc28T61.map dyFn) (dyFn acc28S61)) = acc28S62.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 993 to 1008 -/
theorem acc28_c62 :
    (List.range 9).map (accRunQ 53 8 (acc28T62.map dyFn) (dyFn acc28S62)) = acc28S63.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1009 to 1024 -/
theorem acc28_c63 :
    (List.range 9).map (accRunQ 53 8 (acc28T63.map dyFn) (dyFn acc28S63)) = acc28S64.map dyQ := by
  decide +kernel

end ExpansionBounds
