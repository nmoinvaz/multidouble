import ExpansionBounds.Trig8.All

/-!
# Theorem 35 for the sine and the cosine at `n = 8` and `p = 53`: the buckets below the top one

`C` is at most `2.175822u^8` in the runs of buckets with `|r_0| < 1/2` and at most `2.000706u^8` in those with
`|r_0| < 2^{-5}`, on the last states of Horner's runs, which `Trig8/Run0.lean` to `Run7.lean` check. This file is
written by `trig_lean.py`.
-/

namespace ExpansionBounds

/-- `C ≤ c u^8` in bucket `j`, from the last states of Horner's runs for the sine and the cosine -/
def trig8CLe (c : ℚ) (j Ks Kc : ℕ) (sS sC : ℚ × List ℚ) : Prop :=
  trigCQ trig8U 8 (sinDeltaL trig8U 8 (upQ 200) trig8Ab (trig8Rb j) Ks sS)
    (cosDeltaL trig8U 8 (upQ 200) trig8Ab (trig8Rb j) Kc sC) (trig8Rb j) ≤ c * trig8U ^ 8

instance (c : ℚ) (j Ks Kc : ℕ) (sS sC : ℚ × List ℚ) : Decidable (trig8CLe c j Ks Kc sS sC) := by
  unfold trig8CLe
  infer_instance

/-- the bound of a run of buckets that starts at `j ≥ 1`: `2.175822` below `j = 5` and `2.000706` from there on -/
def trig8Low (j : ℕ) : ℚ := if j < 5 then 2175822 / 1000000 else 2000706 / 1000000

/-- a run of buckets from `j ≥ 1`: Horner's runs end in states on which `C ≤ trig8Low j u^8` -/
def Trig8Low (g : ℕ × ℕ × ℕ) : Prop :=
  ∃ sS sC, trig8Run sinCQ trig8FsQ g.1 (g.2.1 - 1) 0 (g.2.1 - 2) (trig8Init sinCQ trig8FsQ (g.2.1 - 1)) = sS ∧
    trig8Run cosCQ trig8FcQ g.1 (g.2.2 - 1) 0 (g.2.2 - 2) (trig8Init cosCQ trig8FcQ (g.2.2 - 1)) = sC ∧
    trig8CLe (trig8Low g.1) g.1 g.2.1 g.2.2 sS sC

set_option maxHeartbeats 4000000 in
theorem trig8_low1 : trig8CLe (trig8Low 1) 1 37 38 (dySt trig8_s1_35)
    (dySt trig8_c1_36) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low2 : trig8CLe (trig8Low 2) 2 33 33 (dySt trig8_s2_31)
    (dySt trig8_c2_31) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low3 : trig8CLe (trig8Low 3) 3 29 29 (dySt trig8_s3_27)
    (dySt trig8_c3_27) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low4 : trig8CLe (trig8Low 4) 4 26 27 (dySt trig8_s4_24)
    (dySt trig8_c4_25) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low5 : trig8CLe (trig8Low 5) 5 24 24 (dySt trig8_s5_22)
    (dySt trig8_c5_22) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low6 : trig8CLe (trig8Low 6) 6 22 22 (dySt trig8_s6_20)
    (dySt trig8_c6_20) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low7 : trig8CLe (trig8Low 7) 7 20 20 (dySt trig8_s7_18)
    (dySt trig8_c7_18) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low8 : trig8CLe (trig8Low 8) 8 19 19 (dySt trig8_s8_17)
    (dySt trig8_c8_17) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low9 : trig8CLe (trig8Low 9) 9 17 18 (dySt trig8_s9_15)
    (dySt trig8_c9_16) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low10 : trig8CLe (trig8Low 10) 10 16 16 (dySt trig8_s10_14)
    (dySt trig8_c10_14) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low11 : trig8CLe (trig8Low 11) 11 15 15 (dySt trig8_s11_13)
    (dySt trig8_c11_13) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low12 : trig8CLe (trig8Low 12) 12 14 15 (dySt trig8_s12_12)
    (dySt trig8_c12_13) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low13 : trig8CLe (trig8Low 13) 13 14 14 (dySt trig8_s13_12)
    (dySt trig8_c13_12) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low14 : trig8CLe (trig8Low 14) 14 13 13 (dySt trig8_s14_11)
    (dySt trig8_c14_11) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low15 : trig8CLe (trig8Low 15) 15 12 12 (dySt trig8_s15_10)
    (dySt trig8_c15_10) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low17 : trig8CLe (trig8Low 17) 17 11 11 (dySt trig8_s17_9)
    (dySt trig8_c17_9) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low19 : trig8CLe (trig8Low 19) 19 10 10 (dySt trig8_s19_8)
    (dySt trig8_c19_8) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low21 : trig8CLe (trig8Low 21) 21 9 10 (dySt trig8_s21_7)
    (dySt trig8_c21_8) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low22 : trig8CLe (trig8Low 22) 22 9 9 (dySt trig8_s22_7)
    (dySt trig8_c22_7) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low25 : trig8CLe (trig8Low 25) 25 8 8 (dySt trig8_s25_6)
    (dySt trig8_c25_6) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low29 : trig8CLe (trig8Low 29) 29 7 7 (dySt trig8_s29_5)
    (dySt trig8_c29_5) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low34 : trig8CLe (trig8Low 34) 34 6 6 (dySt trig8_s34_4)
    (dySt trig8_c34_4) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low41 : trig8CLe (trig8Low 41) 41 5 6 (dySt trig8_s41_3)
    (dySt trig8_c41_4) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low42 : trig8CLe (trig8Low 42) 42 5 5 (dySt trig8_s42_3)
    (dySt trig8_c42_3) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low52 : trig8CLe (trig8Low 52) 52 4 5 (dySt trig8_s52_2)
    (dySt trig8_c52_3) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low53 : trig8CLe (trig8Low 53) 53 4 4 (dySt trig8_s53_2)
    (dySt trig8_c53_2) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low71 : trig8CLe (trig8Low 71) 71 3 3 (dySt trig8_s71_1)
    (dySt trig8_c71_1) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low107 : trig8CLe (trig8Low 107) 107 2 3 (trig8Init sinCQ trig8FsQ 1)
    (dySt trig8_c107_1) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig8_low108 : trig8CLe (trig8Low 108) 108 2 2 (trig8Init sinCQ trig8FsQ 1)
    (trig8Init cosCQ trig8FcQ 1) := by
  decide +kernel

/-- every run of buckets from `j = 1` on -/
theorem trig8_low : ∀ g ∈ trig8Groups, 1 ≤ g.1 → Trig8Low g := by
  intro g hg h1
  simp only [trig8Groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd h1 (by decide)
  · exact ⟨_, _, trig8_s1, trig8_c1, trig8_low1⟩
  · exact ⟨_, _, trig8_s2, trig8_c2, trig8_low2⟩
  · exact ⟨_, _, trig8_s3, trig8_c3, trig8_low3⟩
  · exact ⟨_, _, trig8_s4, trig8_c4, trig8_low4⟩
  · exact ⟨_, _, trig8_s5, trig8_c5, trig8_low5⟩
  · exact ⟨_, _, trig8_s6, trig8_c6, trig8_low6⟩
  · exact ⟨_, _, trig8_s7, trig8_c7, trig8_low7⟩
  · exact ⟨_, _, trig8_s8, trig8_c8, trig8_low8⟩
  · exact ⟨_, _, trig8_s9, trig8_c9, trig8_low9⟩
  · exact ⟨_, _, trig8_s10, trig8_c10, trig8_low10⟩
  · exact ⟨_, _, trig8_s11, trig8_c11, trig8_low11⟩
  · exact ⟨_, _, trig8_s12, trig8_c12, trig8_low12⟩
  · exact ⟨_, _, trig8_s13, trig8_c13, trig8_low13⟩
  · exact ⟨_, _, trig8_s14, trig8_c14, trig8_low14⟩
  · exact ⟨_, _, trig8_s15, trig8_c15, trig8_low15⟩
  · exact ⟨_, _, trig8_s17, trig8_c17, trig8_low17⟩
  · exact ⟨_, _, trig8_s19, trig8_c19, trig8_low19⟩
  · exact ⟨_, _, trig8_s21, trig8_c21, trig8_low21⟩
  · exact ⟨_, _, trig8_s22, trig8_c22, trig8_low22⟩
  · exact ⟨_, _, trig8_s25, trig8_c25, trig8_low25⟩
  · exact ⟨_, _, trig8_s29, trig8_c29, trig8_low29⟩
  · exact ⟨_, _, trig8_s34, trig8_c34, trig8_low34⟩
  · exact ⟨_, _, trig8_s41, trig8_c41, trig8_low41⟩
  · exact ⟨_, _, trig8_s42, trig8_c42, trig8_low42⟩
  · exact ⟨_, _, trig8_s52, trig8_c52, trig8_low52⟩
  · exact ⟨_, _, trig8_s53, trig8_c53, trig8_low53⟩
  · exact ⟨_, _, trig8_s71, trig8_c71, trig8_low71⟩
  · exact ⟨_, _, trig8_s107, trig8_c107, trig8_low107⟩
  · exact ⟨_, _, trig8_s108, trig8_c108, trig8_low108⟩

end ExpansionBounds
