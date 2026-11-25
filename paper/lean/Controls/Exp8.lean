import ExpansionBounds.Exp8

/-!
# Controls of Theorem 40's constant

Each claim below is one of the kernel's checks of `Exp8.lean` with a wrong number, a wrong state, a wrong group or
a bin left out, and the kernel proves its negation.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
/-- the worst case's bound is not within `3.660u^8` -/
example : ¬ expEpsL red8U 8 (upQ 200 (expUpQ (-exp8_n0_b7.1.1)))
    (expLoQ (-exp8_n0_b7.1.2 - exp8Delta false)) (expUpQ (exp8Delta false) - 1)
    ((dySt exp8_n0_tm :: exp8_n0_b7.2.2.2).getD 5 (0, [])) ≤ 3660 / 1000 * red8U ^ 8 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- two steps of Horner's run do not give the state after four -/
example : ¬ exp8Run exp8_n0_pq exp8_n0_bp 43 0 2 (hornerInitL 8 exp8F exp8Phi 43) = dySt exp8_n0_s4 := by
  decide +kernel

/-- a group with the wrong degree is not accepted -/
example : ¬ Exp8GrpOk false (5, 42, -2, -2, (0, 0), (1, 1)) := by decide +kernel

/-- the bound of the exponent `-2` does not rule out `-1` -/
example : ¬ exp8Top true < (2 : ℚ) ^ (-2 : ℤ) * (1 - 1 / 2 ^ 46) - 2 * exp8Tail true := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the part bounds halved do not bound `π'` -/
example : ¬ Exp8Par false 5 (-2) (dyQ exp8Top1) (exp8_n0_pq.map (· / 2)) exp8_n0_bp := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- a squaring does not check against the state of the next -/
example : ¬ exp8SqChk false ((2 : ℚ) ^ (-(5 : ℤ)) * exp8_n0_b7.1.1) exp8_n0_b7.2.1 0 (dySt exp8_n0_tm)
    (exp8_n0_b7.2.2.2.drop 1) = true := by decide +kernel

/-- a table with a part of 54 bits is not in `F` -/
example : ¬ ∀ q ∈ [((2 : ℤ) ^ 53 + 1, 60)], rnQ 53 (dyQ q) = dyQ q := by decide +kernel

/-- the intervals do not follow each other when one is left out -/
example : ¬ exp8ChainB exp8_n0_b0.1.1 exp8_n0_b7.1.2 ([exp8_n0_b0, exp8_n0_b2, exp8_n0_b7].map Prod.fst) = true := by
  decide +kernel

end ExpansionBounds
