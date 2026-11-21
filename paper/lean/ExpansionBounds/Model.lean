import FloatSpec.src.Compat
import FloatSpec.src.Core.FLX

/-!
# The floating-point model of Assumption `as:fp`

`F p` is the set of binary floating-point numbers of precision `p` with an unbounded exponent range, (A1) with
(A2), and `RN p` rounds to nearest with ties to even. Each operation of the algorithms rounds its exact result once
with `RN p`, which is (A2): it returns what it would return with an unbounded exponent range.
-/

namespace ExpansionBounds

/-- ties to even: between `t` and `t + 1`, round up when `t` is odd -/
def tieEven (t : ℤ) : Bool := decide (t % 2 = 1)

variable (p : ℤ)

/-- the binary floating-point numbers of precision `p`, with an unbounded exponent range -/
def F (x : ℝ) : Prop :=
  FloatSpec.Core.Generic_fmt.generic_format 2 (FloatSpec.Core.FLX.FLX_exp p) x

/-- rounding to nearest in `F p`, ties to even -/
noncomputable def RN (x : ℝ) : ℝ :=
  FloatSpec.Core.Generic_fmt.roundR 2 (FloatSpec.Core.FLX.FLX_exp p)
    (FloatSpec.Core.Generic_fmt.Znearest tieEven) x

/-- the unit roundoff `u = 2⁻ᵖ` -/
noncomputable def u : ℝ := (2 : ℝ) ^ (-p)

/-- `ū = u / (1 + u)`, the bound on the relative error of `RN` -/
noncomputable def us : ℝ := u p / (1 + u p)

/-- TwoSum: `s = RN(a + b)`, `b' = RN(s - a)` and `e = RN(RN(a - RN(s - b')) + RN(b - b'))` -/
noncomputable def twoSum (a b : ℝ) : ℝ × ℝ :=
  let s := RN p (a + b)
  let b' := RN p (s - a)
  (s, RN p (RN p (a - RN p (s - b')) + RN p (b - b')))

/-- FastTwoSum: `s = RN(a + b)` and `e = RN(b - RN(s - a))` -/
noncomputable def fastTwoSum (a b : ℝ) : ℝ × ℝ :=
  let s := RN p (a + b)
  (s, RN p (b - RN p (s - a)))

/-- TwoProd by one fused multiply-add: `q = RN(ab)` and `e = RN(ab - q)` -/
noncomputable def twoProd (a b : ℝ) : ℝ × ℝ :=
  let q := RN p (a * b)
  (q, RN p (a * b - q))

end ExpansionBounds
