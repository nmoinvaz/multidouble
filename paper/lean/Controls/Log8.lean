import ExpansionBounds.Log8.Run0
import ExpansionBounds.Log8.StartHalf

/-!
# Controls of Theorem 42's constant

Each claim below is one of the kernel's checks of `Log8/Run0.lean`, or of the files that use them, with a wrong
number, a wrong state or a wrong bound, and the kernel proves its negation. The case is the tight one: `k ≠ 0`,
`m = 5`, `d' = 43`, `r ≤ 0`, the top interval of `|r|`, at the lower end `ℓ_k^-`. The last ones are of the tables'
checks (`Log8/Checks.lean`), of the parts of `t` (`Log8/PsiAll.lean`) and of the start's constants
(`Log8/Start.lean`, `Log8/StartHalf.lean`).
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
/-- the tight case's bound is not within `9.925818u^8 ℓ` -/
example : ¬ logEndL red8U 8 (log8PiY log8_g0nm3e0_v.2.2.2) log8_g0nm3e0_v.2.2.2
    (logPL red8U 8 (upQ 200) exp8Eta (fun i => (dySt log8_g0nm3e0_c4).2.getD i 0)
      (log8_g0nm3e0_x.2.2.1 + (dySt log8_g0nm3e0_c4).1) (dySt log8_g0nm3e0_c4).1 (dySt log8SH).1
      (dyStW log8HH).1.1 (dyStW log8HH).1.2 4 436 (dySt log8GG)) ≤
    9925818 / 1000000 * red8U ^ 8 * log8_g0nm3e0_v.2.2.2 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- two steps of Horner's run do not give the state after four -/
example : ¬ log8Run log8_h0_pq log8_h0_bp 43 0 2 (hornerInitL 8 exp8F exp8Phi 43) = dySt log8_h0_s4 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the group's part bounds halved do not bound the case's `π'` -/
example : ¬ Log8Leaf false false 5 log8_g0nm3e0_v.1 log8_g0nm3e0_v.2.1 log8_g0nm3e0_v.2.2.1 log8_g0nm3e0_v.2.2.2
    log8_h0_bp (log8_h0_pq.map (· / 2)) log8_g0nm3e0_x.1 log8_g0nm3e0_x.2.1 log8_g0nm3e0_x.2.2.1
    log8_g0nm3e0_x.2.2.2 log8_g0nm3e0_ph := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the reduction's `δ` is not zero for `k ≠ 0` -/
example : ¬ Log8Leaf false false 5 log8_g0nm3e0_v.1 log8_g0nm3e0_v.2.1 0 log8_g0nm3e0_v.2.2.2
    log8_h0_bp log8_h0_pq log8_g0nm3e0_x.1 log8_g0nm3e0_x.2.1 log8_g0nm3e0_x.2.2.1
    log8_g0nm3e0_x.2.2.2 log8_g0nm3e0_ph := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- one squaring does not give the state after two -/
example : ¬ log8Sq false 5 log8_g0nm3e0_v.1 log8_g0nm3e0_v.2.1 0 (dySt log8_h0_tm) = dySt log8_g0nm3e0_s2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- step (4)'s second piece does not follow from the first piece of the other end -/
example : ¬ log8C4b false 5 log8_g0nm3e0_v.2.1 log8_g0nm3e0_x.1 log8_g0nm3e0_x.2.2.1 log8_g0nm3e0_x.2.2.2
    log8_g0nm3e0_ph (dySt log8_g0nm3e0_s5) (dySt4 log8_g0nm3e1_sa) = dySt log8_g0nm3e0_c4 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the series' state does not follow from Horner's rule with one step left out -/
example : ¬ hornerRunLC red8U 8 (upQ 200) (dyFn log8ChiM) (dyQ log8CM) 0 exp8Eta log8F log8Phi
    (logVQ (dyQ log8CM) 4) 4 0 1 (hornerInitL 8 log8F log8Phi 4) = dySt log8SH := by decide +kernel

/-- a table of the series with a part of 54 bits is not in `F` -/
example : ¬ ∀ q ∈ [((2 : ℤ) ^ 53 + 1, 60)], rnQ 53 (dyQ q) = dyQ q := by decide +kernel

/-- the start's `e₀` is not below `2^{-103}`: it is about `2^{-102.09}` -/
example : ¬ log8E0 ≤ 1 / 2 ^ 103 := by decide +kernel

/-- `ln 2` is not known to be at least `3/4` -/
example : ¬ (3 / 4 : ℚ) ≤ ln2A := by decide +kernel

/-- a group's part bounds are not all negative -/
example : ¬ ∀ q ∈ log8_h0_pq, q ≤ 0 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the groups of `k = 0` do not cover the exponent `-437` -/
example : ¬ ∀ e : ℤ, -437 ≤ e → e ≤ -2 → ∃ g ∈ log8Grp0, g.elo ≤ e ∧ e ≤ g.ehi := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the groups of `k = 0` do not start at `|r| = 0`, as the last does -/
example : ¬ ∀ g ∈ log8Grp0, Log8G0Ok true g := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the lower ends of `|r|` for `k ≠ 0` do not hold with the tail's bound doubled -/
example : ¬ ∀ g ∈ log8Grp1, Log8G1Ok log8Top1 (2 * log8Tail1) false g := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the intervals of `|r|` for `k ≠ 0` do not reach a bound of `|r|` twice as large -/
example : ¬ ∀ g ∈ log8Grp1, Log8G1Ok (2 * log8Top1) log8Tail1 false g := by decide +kernel

/-- the exponent `e = -2` is selected for `k = 0` -/
example : ¬ log8Top0 < (2 : ℚ) ^ (-2 : ℤ) * (1 - 1 / 2 ^ 46) * (1 - red8U) / (1 + red8U) := by decide +kernel

/-- `ℓ_k^-` is not smaller by `2^{-190}` -/
example : ¬ (log8Lk + 1 / 2 ^ 190) * (1 + log8E1) + log8E0 ≤ (1 - red8U) / (2 * cr8 * (1 + red8U)) := by
  decide +kernel

/-- Lemma 38's `X` at `|ln x| = 745.2` is above `745.2` -/
example : ¬ (log8X + log8Eq log8X) / (1 - red8U) ≤ 7452 / 10 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the bound of `|r|` for `k ≠ 0` is not smaller by `2^{-190}` -/
example : ¬ log8RMax log8X + log8DeltaS log8X ≤ log8Top1 - 1 / 2 ^ 190 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the bound of `∑_{i ≥ 1}|r_i|` for `k ≠ 0` is not half as large -/
example : ¬ ∑ i ∈ Finset.Ico 1 8, log8PiR log8X log8Top1 i ≤ log8Tail1 / 2 := by decide +kernel

/-- the part bounds of `t` after the squarings do not sum below `2/5` for the largest `r ≥ 0` of `k = 0`: the sum is
about `e^{(ln 2)/2} - 1 = 0.4142` -/
example : ¬ ∑ i ∈ Finset.range 8, (dySt log8_g0zp0e1_s5).2.getD i 0 ≤ 2 / 5 := by decide +kernel

/-- the start's `e₀` does not hold twice `δ_0`: `δ_0` is about `12u²` and `e₀` about `15u²` -/
example : ¬ log8EpsDW * log8D0 + 2 * log8D0 + 1 / 2 ^ 1071 ≤ log8E0 := by decide +kernel

/-- the start's `e₁` is not twice `ε_DW` -/
example : ¬ 2 * log8EpsDW ≤ log8E1 := by decide +kernel

/-- `ε_DW X + e₀` at `X = 745.2` is not below `2^{-93}` -/
example : ¬ log8EpsDW * (7452 / 10) + log8E0 ≤ 1 / 2 ^ 93 := by decide +kernel

/-- the halved double word's `w_h/(1 - w_h)` is not within `δ_0 + 2^{-2100}`: the halving's roundings cost about
`2^{-2094}` -/
example : ¬ log8Wh / (1 - log8Wh) ≤ log8D0 + 1 / 2 ^ 2100 := by decide +kernel

end ExpansionBounds
