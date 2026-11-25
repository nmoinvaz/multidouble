import ExpansionBounds.Prop28.Data

/-!
# Proposition 28 (`prop:acc-low`): the accumulator's run on the terms 1793 to 2048

The kernel runs the accumulator on each chunk of 16 terms from the levels before it and checks the levels after it.
This file is written by `accumulator/acc_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1793 to 1808 -/
theorem acc28_c112 :
    (List.range 9).map (accRunQ 53 8 (acc28T112.map dyFn) (dyFn acc28S112)) = acc28S113.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1809 to 1824 -/
theorem acc28_c113 :
    (List.range 9).map (accRunQ 53 8 (acc28T113.map dyFn) (dyFn acc28S113)) = acc28S114.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1825 to 1840 -/
theorem acc28_c114 :
    (List.range 9).map (accRunQ 53 8 (acc28T114.map dyFn) (dyFn acc28S114)) = acc28S115.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1841 to 1856 -/
theorem acc28_c115 :
    (List.range 9).map (accRunQ 53 8 (acc28T115.map dyFn) (dyFn acc28S115)) = acc28S116.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1857 to 1872 -/
theorem acc28_c116 :
    (List.range 9).map (accRunQ 53 8 (acc28T116.map dyFn) (dyFn acc28S116)) = acc28S117.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1873 to 1888 -/
theorem acc28_c117 :
    (List.range 9).map (accRunQ 53 8 (acc28T117.map dyFn) (dyFn acc28S117)) = acc28S118.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1889 to 1904 -/
theorem acc28_c118 :
    (List.range 9).map (accRunQ 53 8 (acc28T118.map dyFn) (dyFn acc28S118)) = acc28S119.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1905 to 1920 -/
theorem acc28_c119 :
    (List.range 9).map (accRunQ 53 8 (acc28T119.map dyFn) (dyFn acc28S119)) = acc28S120.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1921 to 1936 -/
theorem acc28_c120 :
    (List.range 9).map (accRunQ 53 8 (acc28T120.map dyFn) (dyFn acc28S120)) = acc28S121.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1937 to 1952 -/
theorem acc28_c121 :
    (List.range 9).map (accRunQ 53 8 (acc28T121.map dyFn) (dyFn acc28S121)) = acc28S122.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1953 to 1968 -/
theorem acc28_c122 :
    (List.range 9).map (accRunQ 53 8 (acc28T122.map dyFn) (dyFn acc28S122)) = acc28S123.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1969 to 1984 -/
theorem acc28_c123 :
    (List.range 9).map (accRunQ 53 8 (acc28T123.map dyFn) (dyFn acc28S123)) = acc28S124.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 1985 to 2000 -/
theorem acc28_c124 :
    (List.range 9).map (accRunQ 53 8 (acc28T124.map dyFn) (dyFn acc28S124)) = acc28S125.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 2001 to 2016 -/
theorem acc28_c125 :
    (List.range 9).map (accRunQ 53 8 (acc28T125.map dyFn) (dyFn acc28S125)) = acc28S126.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 2017 to 2032 -/
theorem acc28_c126 :
    (List.range 9).map (accRunQ 53 8 (acc28T126.map dyFn) (dyFn acc28S126)) = acc28S127.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 2033 to 2048 -/
theorem acc28_c127 :
    (List.range 9).map (accRunQ 53 8 (acc28T127.map dyFn) (dyFn acc28S127)) = acc28S128.map dyQ := by
  decide +kernel

end ExpansionBounds
