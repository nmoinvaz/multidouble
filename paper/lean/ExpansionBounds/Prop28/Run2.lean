import ExpansionBounds.Prop28.Data

/-!
# Proposition 28 (`prop:acc-low`): the accumulator's run on the terms 513 to 768

The kernel runs the accumulator on each chunk of 16 terms from the levels before it and checks the levels after it.
This file is written by `accumulator/acc_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 513 to 528 -/
theorem acc28_c32 :
    (List.range 9).map (accRunQ 53 8 (acc28T32.map dyFn) (dyFn acc28S32)) = acc28S33.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 529 to 544 -/
theorem acc28_c33 :
    (List.range 9).map (accRunQ 53 8 (acc28T33.map dyFn) (dyFn acc28S33)) = acc28S34.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 545 to 560 -/
theorem acc28_c34 :
    (List.range 9).map (accRunQ 53 8 (acc28T34.map dyFn) (dyFn acc28S34)) = acc28S35.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 561 to 576 -/
theorem acc28_c35 :
    (List.range 9).map (accRunQ 53 8 (acc28T35.map dyFn) (dyFn acc28S35)) = acc28S36.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 577 to 592 -/
theorem acc28_c36 :
    (List.range 9).map (accRunQ 53 8 (acc28T36.map dyFn) (dyFn acc28S36)) = acc28S37.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 593 to 608 -/
theorem acc28_c37 :
    (List.range 9).map (accRunQ 53 8 (acc28T37.map dyFn) (dyFn acc28S37)) = acc28S38.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 609 to 624 -/
theorem acc28_c38 :
    (List.range 9).map (accRunQ 53 8 (acc28T38.map dyFn) (dyFn acc28S38)) = acc28S39.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 625 to 640 -/
theorem acc28_c39 :
    (List.range 9).map (accRunQ 53 8 (acc28T39.map dyFn) (dyFn acc28S39)) = acc28S40.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 641 to 656 -/
theorem acc28_c40 :
    (List.range 9).map (accRunQ 53 8 (acc28T40.map dyFn) (dyFn acc28S40)) = acc28S41.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 657 to 672 -/
theorem acc28_c41 :
    (List.range 9).map (accRunQ 53 8 (acc28T41.map dyFn) (dyFn acc28S41)) = acc28S42.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 673 to 688 -/
theorem acc28_c42 :
    (List.range 9).map (accRunQ 53 8 (acc28T42.map dyFn) (dyFn acc28S42)) = acc28S43.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 689 to 704 -/
theorem acc28_c43 :
    (List.range 9).map (accRunQ 53 8 (acc28T43.map dyFn) (dyFn acc28S43)) = acc28S44.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 705 to 720 -/
theorem acc28_c44 :
    (List.range 9).map (accRunQ 53 8 (acc28T44.map dyFn) (dyFn acc28S44)) = acc28S45.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 721 to 736 -/
theorem acc28_c45 :
    (List.range 9).map (accRunQ 53 8 (acc28T45.map dyFn) (dyFn acc28S45)) = acc28S46.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 737 to 752 -/
theorem acc28_c46 :
    (List.range 9).map (accRunQ 53 8 (acc28T46.map dyFn) (dyFn acc28S46)) = acc28S47.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the levels after the terms 753 to 768 -/
theorem acc28_c47 :
    (List.range 9).map (accRunQ 53 8 (acc28T47.map dyFn) (dyFn acc28S47)) = acc28S48.map dyQ := by
  decide +kernel

end ExpansionBounds
