import ExpansionBounds.DDTrig2

/-!
# Controls of the kernel's checks for the double-double sine, cosine and tangent

Each is the negation of a check of `DDTrig2.lean` on a wrong number, which the kernel proves: the bounds one unit of
the last decimal lower in the top bucket, a cosine series one term short, a sine series one term short for the
tangent, a row that is not a double word, below the last bucket `C` against `u²/2` and `C^T` against `u²/3`, and the
early returns' own errors, conjuncts of those checks, against `u²/2` for the cosine and `u²/3` for the tangent.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
/-- the top bucket's `C` exceeds `7.841411u²` -/
theorem dd_ctl_c : ¬ DDOk (7841411 / 1000000) (0, 15, 15) := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the top bucket's `C^T` exceeds `28.414065u²` -/
theorem dd_ctl_ct : ¬ DDTanOk (28414065 / 1000000) (0, 15, 15) := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- a cosine series one term short breaks the bound -/
theorem dd_ctl_kc : ¬ DDOk ddC (0, 15, 14) := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- a sine series one term short breaks the tangent's bound -/
theorem dd_ctl_ks : ¬ DDTanOk ddCt (0, 14, 15) := by decide +kernel

/-- `(1, 3·2^{-54})` is not a double word -/
theorem dd_ctl_row : ¬ DDRows [[(1, 0), (3, 54)]] := by decide +kernel

/-- below the last bucket `C` exceeds `u²/2` -/
theorem dd_ctl_tiny : ¬ DDTinyOk (1 / 2) := by decide +kernel

/-- the cosine's early return errs by more than `u²/2` -/
theorem dd_ctl_tiny_cos : ¬ ddTiny ^ 2 / (2 * cosLoQ ddTiny) ≤ 1 / 2 * trig8U ^ 2 := by decide +kernel

/-- below the last bucket `C^T` exceeds `u²/3` -/
theorem dd_ctl_tan_tiny : ¬ DDTanTinyOk (1 / 3) := by decide +kernel

/-- the tangent's early return errs by more than `u²/3` -/
theorem dd_ctl_tan_tiny_ret : ¬ tanHiQ ddTiny / ddTiny - 1 ≤ 1 / 3 * trig8U ^ 2 := by decide +kernel

end ExpansionBounds
