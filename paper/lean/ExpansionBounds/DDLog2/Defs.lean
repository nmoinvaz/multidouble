import ExpansionBounds.DDLogChord
import ExpansionBounds.DDExp2
import ExpansionBounds.DDLog2.Data

/-!
# Proposition 44, `DD::ln` at `p = 53`: what the kernel evaluates

`DD::ln` is LOG with `s = 1`, `d = 27` and `q = 3` on double words, `B = 118`, from the start `y_0`, one float within
`E(ℓ)` of `ln x`: `E(ℓ) = e_1ℓ + e_0` (`ddlE`, Lemma 43 and `prop44_start`) or `ℓ(u(1 + ℓ) + ℓ)` for
`ℓ < u(1 - u)/2` (`ddlEs`). For a case the bound of the convex mode is evaluated on its rational mirror
(`ddLogBoundCQ`) at the two ends of an interval of `ℓ`, and `DDLChord` (ratio `15.351u²` at both ends) or
`DDLChord0` (`2^{-1071}` at `ℓ = 0` and `15.351u²ℓ + 2^{-1071}` at the upper end) is what the kernel checks for one
sign, with `C ≤ 2^{-40}` at the upper end and the floor of EXP's scaling back.

* `k = 0`: `r = -y_0`, `δ = 0` and `b = ℓ + E(ℓ)`. A group of exponents with one degree selects
  `|y_0| ∈ [a, hi]`, so `ℓ ∈ [ℓ₁, ℓ₂]` with `(1 + e_1)ℓ₁ + e_0 ≤ a` and `hi + e_0 ≤ (1 - e_1)ℓ₂` (`DDL0Lin`); the
  groups whose `ℓ₂` is below `u(1 - u)/2` take the start's second piece from `ℓ = 0` (`DDL0Small`).
* `k ≠ 0`: an interval `[a, b]` of `|r|` with the reduction's `δ` at `r̄ = b + δ*` (`ddlDelta`), from the least `ℓ`
  with `k ≠ 0` to `745.2` (`DDL1Bin`, `DDL1Group`).
-/

namespace ExpansionBounds

open Finset

/-- `F'_i`, the first two parts of the greedy expansion of `(-1)^{i+1}/i`, for `i = 2, 3` -/
def ddlFQ (i : ℕ) : ℚ × ℚ := [(0, 0), (0, 0), (dyQ (-1, 1), 0), (dyQ ddlF3S.1, dyQ ddlF3S.2)].getD i (0, 0)

/-- `φ'_i = |F'_i - (-1)^{i+1}/i|` -/
def ddlPhi (i : ℕ) : ℚ := |(ddlFQ i).1 + (ddlFQ i).2 - (-1) ^ (i + 1) / i|

/-- Lemma 43's `η_b = 5.915u` -/
def ddlEtaB : ℚ := 5915 / 1000 * red8U

/-- the start's `e_1 = η_b + u(1 + η_b)` -/
def ddlE1 : ℚ := ddlEtaB + red8U * (1 + ddlEtaB)

/-- the start's `e_0 = η_bδ_1 + u² + η_0 + u²/(2(1 - u)) + u((1 + η_b)δ_1 + u(1 + u) + η_0)`, `δ_1 = u/(1 - u)` -/
def ddlE0 : ℚ := ddlEtaB * (red8U / (1 - red8U)) + red8U ^ 2 + dd2Eta + red8U ^ 2 / (2 * (1 - red8U)) +
  red8U * ((1 + ddlEtaB) * (red8U / (1 - red8U)) + red8U * (1 + red8U) + dd2Eta)

/-- the start's error `E(ℓ) = e_1ℓ + e_0` -/
def ddlE (l : ℚ) : ℚ := ddlE1 * l + ddlE0

/-- the start's error `ℓ(u(1 + ℓ) + ℓ)` for `ℓ < u(1 - u)/2` -/
def ddlEs (l : ℚ) : ℚ := l * (red8U * (1 + l) + l)

/-- `ȳ = X + E(X)` at `X = 745.2`, a bound of `|y_0|` -/
def ddlYB : ℚ := red8X + ddlE red8X

/-- `r̄_max` of the reduction of `(-y_0, 0)`: `X = ȳ` and a zero low part -/
def ddlRMax : ℚ := (1 / 2 + ddlYB * (red8Dl + red8U * cr8)) * ln2B

/-- `α_0` of that reduction -/
def ddlA0 : ℚ := ddlRMax + 1075 * max |ch8 - ln2A| |ch8 - ln2B|

/-- `ε_q = e_F(k̄|c_ℓ| + ε_1)` for a zero low part -/
def ddlEq : ℚ := eFQ red8U * (1075 * dd2C + dd2E1)

/-- the reduction's `δ` at `r̄` for a zero low part -/
def ddlDelta (rb : ℚ) : ℚ := dd2E1 + ddlEq + eFQ red8U * (rb + 1075 * dd2EtaL + dd2E1 + ddlEq) + 1075 * dd2EtaL

/-- the least `|v|` of a `v` whose exponent is at least `-B - 13 = -131`: `2^{-131}(1 - 2^{-46})` -/
def ddlLow : ℚ := 1 / 2 ^ 131 * (1 - 1 / 2 ^ 46)

/-- a bound of every case's `C` -/
def ddlCg : ℚ := 1 / 2 ^ 40

/-- the lower bound `l_v` of Horner's iterates -/
def ddlLv : ℚ := 1 / 4

/-- `ε_DW = 15.351u²` -/
def ddlEps : ℚ := 15351 / 1000 * red8U ^ 2

/-- `Φ_DW = 2^{-1071}` -/
def ddlFl : ℚ := 1 / 2 ^ 1071

/-- the mirror of the bound of a case at `(ℓ, E, b, δ)` -/
def ddlBQ (pos : Bool) (d : ℕ) (a l E b δ : ℚ) : ℚ :=
  ddLogBoundCQ red8U dd2Eta (2 * dd2Eta) (2 * dd2Eta) dd2Eta l E pos a b δ dd2Phi d ddlPhi 3 118

/-- the mirror of `C` of a case at `(E, b, δ)` -/
def ddlCQ (pos : Bool) (d : ℕ) (a E b δ : ℚ) : ℚ :=
  ddLogCCQ red8U dd2Eta (2 * dd2Eta) (2 * dd2Eta) E pos a b δ dd2Phi d 118

/-- an end of a chord: the sizes for the enclosures and `C < 1` -/
def DDLEnd (pos : Bool) (d : ℕ) (a l E b δ : ℚ) : Prop :=
  DDLogEnd red8U dd2Eta (2 * dd2Eta) (2 * dd2Eta) l E pos a b δ dd2Phi d 118

instance (pos : Bool) (d : ℕ) (a l E b δ : ℚ) : Decidable (DDLEnd pos d a l E b δ) := by
  unfold DDLEnd
  infer_instance

/-- the floor of EXP's scaling back, at the largest `b` of the case and the convex mode's `t̄` -/
def DDLFloor (pos : Bool) (d : ℕ) (a b : ℚ) : Prop :=
  d ≠ 1 → dd2Floor * (1 + red8U) ≤ a / (1 + a) - ddCoreEQ red8U (ddTbCQ pos b) 0 b dd2Phi d

instance (pos : Bool) (d : ℕ) (a b : ℚ) : Decidable (DDLFloor pos d a b) := by
  unfold DDLFloor
  infer_instance

/-- the sizes at the upper end that keep `t` below 1: `b ≤ 1/2` and `E_0 ≤ 1/4` -/
def DDLSize (pos : Bool) (d : ℕ) (b : ℚ) : Prop :=
  b ≤ 1 / 2 ∧ ddCoreEQ red8U (ddTbCQ pos b) dd2Eta b dd2Phi d ≤ 1 / 4

instance (pos : Bool) (d : ℕ) (b : ℚ) : Decidable (DDLSize pos d b) := by
  unfold DDLSize
  infer_instance

/-- a chord from `ℓ₁` to `ℓ₂` for one sign: both ends, the mirror within `15.351u²ℓ` at each, `C ≤ 2^{-40}` at
`ℓ₂`, and the floor and the sizes at `ℓ₂` -/
def DDLChord (pos : Bool) (d : ℕ) (a l₁ E1 b1 l₂ E2 b2 δ : ℚ) : Prop :=
  DDLEnd pos d a l₁ E1 b1 δ ∧ DDLEnd pos d a l₂ E2 b2 δ ∧ ddlBQ pos d a l₁ E1 b1 δ ≤ ddlEps * l₁ ∧
    ddlBQ pos d a l₂ E2 b2 δ ≤ ddlEps * l₂ ∧ ddlCQ pos d a E2 b2 δ ≤ ddlCg ∧ DDLFloor pos d a b2 ∧
    DDLSize pos d b2

instance (pos : Bool) (d : ℕ) (a l₁ E1 b1 l₂ E2 b2 δ : ℚ) : Decidable (DDLChord pos d a l₁ E1 b1 l₂ E2 b2 δ) := by
  unfold DDLChord
  infer_instance

/-- a chord from `0` to `ℓ₂` for one sign, with `E = b = δ = 0` at `0`: the mirror within `2^{-1071}` at `0` and
within `15.351u²ℓ₂ + 2^{-1071}` at `ℓ₂` -/
def DDLChord0 (pos : Bool) (d : ℕ) (a l₂ E2 b2 : ℚ) : Prop :=
  DDLEnd pos d a 0 0 0 0 ∧ DDLEnd pos d a l₂ E2 b2 0 ∧ ddlBQ pos d a 0 0 0 0 ≤ ddlFl ∧
    ddlBQ pos d a l₂ E2 b2 0 ≤ ddlEps * l₂ + ddlFl ∧ ddlCQ pos d a E2 b2 0 ≤ ddlCg ∧ DDLFloor pos d a b2 ∧
    DDLSize pos d b2

instance (pos : Bool) (d : ℕ) (a l₂ E2 b2 : ℚ) : Decidable (DDLChord0 pos d a l₂ E2 b2) := by
  unfold DDLChord0
  infer_instance

/-- `k = 0`, a group `(d', e_lo, e_hi, ℓ₁, ℓ₂)` on the start's linear piece: its exponents have the degree `d'`,
they select `|y_0| ∈ [a, hi]` with `a = 2^{e_lo}(1 - 2^{-46})` and `hi = min(top, 2^{e_hi+1})`, so
`ℓ ∈ [ℓ₁, ℓ₂]`, and the chord holds for both signs with `b = ℓ + E(ℓ)` -/
def DDL0Lin (g : ℕ × ℤ × ℤ × (ℤ × ℕ) × (ℤ × ℕ)) : Prop :=
  (∀ e : ℤ, g.2.1 ≤ e → e ≤ g.2.2.1 → g.1 = ddDeg e) ∧ 1 ≤ g.1 ∧ 0 ≤ dyQ g.2.2.2.1 ∧
    (1 + ddlE1) * dyQ g.2.2.2.1 + ddlE0 ≤ (2 : ℚ) ^ g.2.1 * (1 - 1 / 2 ^ 46) ∧
    min (dyQ ddlTop0S) ((2 : ℚ) ^ (g.2.2.1 + 1)) + ddlE0 ≤ (1 - ddlE1) * dyQ g.2.2.2.2 ∧
    DDLChord true g.1 ((2 : ℚ) ^ g.2.1 * (1 - 1 / 2 ^ 46)) (dyQ g.2.2.2.1) (ddlE (dyQ g.2.2.2.1))
      (dyQ g.2.2.2.1 + ddlE (dyQ g.2.2.2.1)) (dyQ g.2.2.2.2) (ddlE (dyQ g.2.2.2.2))
      (dyQ g.2.2.2.2 + ddlE (dyQ g.2.2.2.2)) 0 ∧
    DDLChord false g.1 ((2 : ℚ) ^ g.2.1 * (1 - 1 / 2 ^ 46)) (dyQ g.2.2.2.1) (ddlE (dyQ g.2.2.2.1))
      (dyQ g.2.2.2.1 + ddlE (dyQ g.2.2.2.1)) (dyQ g.2.2.2.2) (ddlE (dyQ g.2.2.2.2))
      (dyQ g.2.2.2.2 + ddlE (dyQ g.2.2.2.2)) 0

instance (g : ℕ × ℤ × ℤ × (ℤ × ℕ) × (ℤ × ℕ)) : Decidable (DDL0Lin g) := by
  unfold DDL0Lin
  infer_instance

/-- `k = 0`, a group `(d', e_lo, e_hi, ℓ₂)` on the start's second piece: `ℓ ≤ ℓ₂ < u(1 - u)/2`, and the chord from
`0` holds for both signs with `E = ℓ(u(1 + ℓ) + ℓ)` and `b = ℓ + E`; `a = 0` for the last group -/
def DDL0Small (last : Bool) (g : ℕ × ℤ × ℤ × (ℤ × ℕ)) : Prop :=
  (∀ e : ℤ, g.2.1 ≤ e → e ≤ g.2.2.1 → g.1 = ddDeg e) ∧ 1 ≤ g.1 ∧
    min (dyQ ddlTop0S) ((2 : ℚ) ^ (g.2.2.1 + 1)) + ddlE0 ≤ (1 - ddlE1) * dyQ g.2.2.2 ∧
    dyQ g.2.2.2 < red8U * (1 - red8U) / 2 ∧
    DDLChord0 true g.1 (if last then 0 else (2 : ℚ) ^ g.2.1 * (1 - 1 / 2 ^ 46)) (dyQ g.2.2.2) (ddlEs (dyQ g.2.2.2))
      (dyQ g.2.2.2 + ddlEs (dyQ g.2.2.2)) ∧
    DDLChord0 false g.1 (if last then 0 else (2 : ℚ) ^ g.2.1 * (1 - 1 / 2 ^ 46)) (dyQ g.2.2.2) (ddlEs (dyQ g.2.2.2))
      (dyQ g.2.2.2 + ddlEs (dyQ g.2.2.2))

instance (last : Bool) (g : ℕ × ℤ × ℤ × (ℤ × ℕ)) : Decidable (DDL0Small last g) := by
  unfold DDL0Small
  infer_instance

/-- `k ≠ 0`, an interval `[a, b]` of `|r|` of degree `d'`: the chord from the least `ℓ` with `k ≠ 0` to `745.2`
for both signs, with `δ` at `r̄ = b + δ*` -/
def DDL1Bin (d : ℕ) (a b : ℚ) : Prop :=
  DDLChord true d a (dyQ ddlLkS) (ddlE (dyQ ddlLkS)) b red8X (ddlE red8X) b (ddlDelta (b + dyQ ddlDStarS)) ∧
    DDLChord false d a (dyQ ddlLkS) (ddlE (dyQ ddlLkS)) b red8X (ddlE red8X) b (ddlDelta (b + dyQ ddlDStarS))

instance (d : ℕ) (a b : ℚ) : Decidable (DDL1Bin d a b) := by
  unfold DDL1Bin
  infer_instance

/-- `k ≠ 0`, a group `(d', e_lo, e_hi, bins)`: its exponents have the degree `d' ≥ 1`, and its intervals, at least
one, follow each other from `2^{e_lo}(1 - 2^{-46})`, or from `0` for the last group, to `min(top, 2^{e_hi+1})`, each
with `DDL1Bin` -/
def DDL1Group (last : Bool) (g : ℕ × ℤ × ℤ × List ((ℤ × ℕ) × (ℤ × ℕ))) : Prop :=
  (∀ e : ℤ, g.2.1 ≤ e → e ≤ g.2.2.1 → g.1 = ddDeg e) ∧ 1 ≤ g.1 ∧ g.2.2.2 ≠ [] ∧
    exp8ChainB (if last then 0 else (2 : ℚ) ^ g.2.1 * (1 - 1 / 2 ^ 46))
      (min (dyQ ddlTop1S) ((2 : ℚ) ^ (g.2.2.1 + 1))) (g.2.2.2.map fun ab => (dyQ ab.1, dyQ ab.2)) = true ∧
    ∀ ab ∈ g.2.2.2, DDL1Bin g.1 (dyQ ab.1) (dyQ ab.2)

instance (last : Bool) (g : ℕ × ℤ × ℤ × List ((ℤ × ℕ) × (ℤ × ℕ))) : Decidable (DDL1Group last g) := by
  unfold DDL1Group
  infer_instance

end ExpansionBounds
