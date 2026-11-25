import ExpansionBounds.Prop28

/-!
# Controls of Proposition 28

Each claim below is one of the kernel's checks of `Prop28.lean` with a wrong number, a wrong state or a wrong prefix,
and the kernel proves its negation. A check that passed for another reason than the one meant, or that the kernel
could not evaluate, would pass on these as well, and this file would not build.
-/

namespace ExpansionBounds

open Finset

/-! ### The error of the 2048 terms -/

/-- the error does not reach `14675798u^8|Z|` -/
example : ¬ 14675798 * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ acc28Z| ≤ |dyQ acc28Z - (acc28X.map dyQ).sum| := by
  decide +kernel

/-- the error is not below `14675797u^8|Z|` -/
example : ¬ |dyQ acc28Z - (acc28X.map dyQ).sum| ≤ 14675797 * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ acc28Z| := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the second chunk, run from empty levels, does not give the stored levels -/
example : ¬ (List.range 9).map (accRunQ 53 8 (acc28T1.map dyFn) fun _ => 0) = acc28S2.map dyQ := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- FINISH on the levels one chunk early does not give the stored parts -/
example : ¬ ∑ i ∈ range 8, finishRQ 53 8 (dyFn acc28S127) 8 i = (acc28X.map dyQ).sum := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the terms are not on a ladder half as wide -/
example : ¬ ∀ t ∈ acc28T, ∀ i < 7, |dyFn t (i + 1)| ≤ 1 / 18014398509481984 * |dyFn t i| := by
  decide +kernel

/-- the terms do not sum to `Z` plus one unit of its last place -/
example : ¬ (acc28ZS.map dyQ).sum = dyQ (acc28Z.1 + 1, acc28Z.2) := by
  decide +kernel

/-! ### `W` and the terms -/

set_option maxHeartbeats 4000000 in
/-- `W` is not above `|Z|(1 - 2^{-97})` -/
example : ¬ |dyQ acc28Z| * (1 - 1 / 2 ^ 97) < (acc28T.map fun t => |dyFn t 0|).sum := by
  rw [acc28T]
  simp only [List.map_append, List.sum_append]
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- `W` does not reach `|Z|` -/
example : ¬ |dyQ acc28Z| ≤ (acc28T.map fun t => |dyFn t 0|).sum := by
  rw [acc28T]
  simp only [List.map_append, List.sum_append]
  decide +kernel

/-- the leading parts are not all above `(1 - 2^{-43})u` -/
example : ¬ ∀ t ∈ acc28T.tail, (1 - 1 / 2 ^ 43) * (1 / 9007199254740992 : ℚ) ≤ dyFn t 0 := by decide +kernel

/-- the leading parts are not all at most `(1 - 2^{-52})u` -/
example : ¬ ∀ t ∈ acc28T.tail, dyFn t 0 ≤ (1 - 1 / 2 ^ 52) * (1 / 9007199254740992 : ℚ) := by decide +kernel

/-- the first term's leading part is not below `u` -/
example : ¬ ∀ t ∈ acc28T, dyFn t 0 < 1 / 9007199254740992 := by decide +kernel

/-- the parts are not within a quarter of an ulp of the one before -/
example : ¬ ∀ t ∈ acc28T, ∀ i < 7,
    dyFn t (i + 1) = 0 ∨ dyFn t i ≠ 0 ∧ |dyFn t (i + 1)| ≤ (2 : ℚ) ^ (magQ (dyFn t i) - 53 - 2) := by decide +kernel

/-- the second term is not `1` -/
example : ¬ dyFn (acc28T.getD 1 []) 0 = 1 := by decide +kernel

/-! ### The prefixes -/

/-- the error of the first 256 terms is not at least `0.1030u^8|Z|` -/
example : ¬ 1030 / 10000 * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ acc28Z256| ≤
    |dyQ acc28Z256 - (acc28X256.map dyQ).sum| := by decide +kernel

/-- nor at most `0.1029u^8|Z|` -/
example : ¬ |dyQ acc28Z256 - (acc28X256.map dyQ).sum| ≤
    1029 / 10000 * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ acc28Z256| := by decide +kernel

/-- the error of the first 512 terms is not at least `36.40u^8|Z|` -/
example : ¬ 3640 / 100 * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ acc28Z512| ≤
    |dyQ acc28Z512 - (acc28X512.map dyQ).sum| := by decide +kernel

/-- nor at most `36.39u^8|Z|` -/
example : ¬ |dyQ acc28Z512 - (acc28X512.map dyQ).sum| ≤
    3639 / 100 * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ acc28Z512| := by decide +kernel

/-- the error of the first 1024 terms is not at least `11806u^8|Z|` -/
example : ¬ 11806 * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ acc28Z1024| ≤
    |dyQ acc28Z1024 - (acc28X1024.map dyQ).sum| := by decide +kernel

/-- nor at most `11805u^8|Z|` -/
example : ¬ |dyQ acc28Z1024 - (acc28X1024.map dyQ).sum| ≤
    11805 * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ acc28Z1024| := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- FINISH one chunk late does not give the parts of the first 256 terms -/
example : ¬ ∑ i ∈ range 8, finishRQ 53 8 (dyFn acc28S17) 8 i = (acc28X256.map dyQ).sum := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- one term more does not have the sum of the first 256 -/
example : ¬ ((acc28T.take 257).map fun t => ∑ i ∈ range 8, dyFn t i).sum = dyQ acc28Z256 := by decide +kernel

/-- a prefix is not its first chunk and a later one -/
example : ¬ acc28T.take 32 = acc28T0 ++ acc28T2 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the first 512 terms do not have the sum of the first 256 -/
example : ¬ ((acc28T.take 512).map fun t => ∑ i ∈ range 8, dyFn t i).sum = dyQ acc28Z256 := by
  rw [acc28_take512]
  simp only [List.map_append, List.sum_append]
  decide +kernel

end ExpansionBounds
