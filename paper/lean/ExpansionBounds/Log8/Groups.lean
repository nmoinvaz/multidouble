import ExpansionBounds.Log8.K1

/-!
# Theorem 42 at `n = 8` and `p = 53`: the groups of cases

The cases of the proof's paragraph "The cases", as the tables of `Log8/Table.lean` hold them. For `k = 0` a group
`Log8G0` is the exponents `e_lo ≤ e ≤ e_hi` of step (2)'s `U` that share `m` and the degree `d'`: `|r| = |y_0|` lies
in `[a, hi]`, so `|ln x|` in `[ℓ₁, ℓ₂]`, and `b` is `ȳ(ℓ)` or the constant `hi`. For `k ≠ 0` a group `Log8G1` has
intervals `[a, b]` of `|r|` for each sign that cover `[lo, hi]`, each on `[ℓ_k^-, X]`. `Log8G0Ok` and `Log8G1Ok` are
what the kernel checks of a group's numbers, and `Log8Group0` and `Log8Group1` its evaluations (`Log8Eval`) at the
two ends, for each sign.
-/

namespace ExpansionBounds

open Finset

/-- a group of `k = 0`: `m`, `d'`, the exponents `e_lo ≤ e ≤ e_hi`, `|r| ∈ [a, hi]`, `|ln x| ∈ [ℓ₁, ℓ₂]`, whether
`b` is the constant `hi`, whether the interval starts at zero, and the bounds of `b` at the two ends -/
structure Log8G0 where
  /-- the number of squarings -/
  m : ℕ
  /-- the degree -/
  d : ℕ
  /-- the least exponent -/
  elo : ℤ
  /-- the largest exponent -/
  ehi : ℤ
  /-- a lower bound of `|r|` -/
  a : ℚ
  /-- an upper bound of `|r|` -/
  hi : ℚ
  /-- the lower end of `|ln x|` -/
  l₁ : ℚ
  /-- the upper end of `|ln x|` -/
  l₂ : ℚ
  /-- whether `b` is the constant `hi` -/
  cst : Bool
  /-- whether the interval starts at zero -/
  zero : Bool
  /-- `b` at the lower end -/
  b₁ : ℚ
  /-- `b` at the upper end -/
  b₂ : ℚ

/-- a group of `k ≠ 0`: `m`, `d'`, the exponents, `|r| ∈ [lo, hi]`, and for each sign the intervals `[a, b]` of `|r|`
with the bounds of `δ` at the two ends, `(a, b, δ₁, δ₂)` -/
structure Log8G1 where
  /-- the number of squarings -/
  m : ℕ
  /-- the degree -/
  d : ℕ
  /-- the least exponent -/
  elo : ℤ
  /-- the largest exponent -/
  ehi : ℤ
  /-- a lower bound of `|r|` -/
  lo : ℚ
  /-- an upper bound of `|r|` -/
  hi : ℚ
  /-- the intervals for `r ≥ 0` -/
  binsP : List (ℚ × ℚ × ℚ × ℚ)
  /-- the intervals for `r ≤ 0` -/
  binsN : List (ℚ × ℚ × ℚ × ℚ)

/-- the largest `|ln x|` -/
def log8X : ℚ := 3726 / 5

/-- a bound of `|y_0|` for `k = 0`: `|y_h| < 1/(2c_r)` and `|y_0| ≤ |y_h|(1 + u)` -/
def log8Top0 : ℚ := 1 / (2 * cr8) * (1 + red8U)

/-- intervals `[a, b]` whose lower ends are at most the upper end before them, from `lo`, and that reach `hi` -/
def log8CoverB : ℚ → ℚ → List (ℚ × ℚ) → Bool
  | lo, hi, [] => decide (hi ≤ lo)
  | lo, hi, ab :: rest => decide (ab.1 ≤ lo) && log8CoverB ab.2 hi rest

/-- Such intervals cover `[lo, hi]`. -/
theorem log8Cover_cover : ∀ (l : List (ℚ × ℚ)) (lo hi : ℚ), log8CoverB lo hi l = true → l ≠ [] →
    ∀ y : ℝ, ((lo : ℚ) : ℝ) ≤ y → y ≤ ((hi : ℚ) : ℝ) → ∃ ab ∈ l, ((ab.1 : ℚ) : ℝ) ≤ y ∧ y ≤ ((ab.2 : ℚ) : ℝ)
  | [], _, _, _, hne, _, _, _ => absurd rfl hne
  | ab :: rest, lo, hi, hc, _, y, hlo, hhi => by
    simp only [log8CoverB, Bool.and_eq_true, decide_eq_true_eq] at hc
    by_cases hy : y ≤ ((ab.2 : ℚ) : ℝ)
    · exact ⟨ab, List.mem_cons_self, (Rat.cast_le.mpr hc.1).trans hlo, hy⟩
    · rcases rest with _ | ⟨ab', rest'⟩
      · simp only [log8CoverB, decide_eq_true_eq] at hc
        exact absurd (hhi.trans (Rat.cast_le.mpr hc.2)) hy
      · obtain ⟨c, hcm, hc1, hc2⟩ := log8Cover_cover (ab' :: rest') ab.2 hi hc.2 (by simp) y
          (le_of_lt (not_le.mp hy)) hhi
        exact ⟨c, List.mem_cons_of_mem _ hcm, hc1, hc2⟩

/-- what the kernel checks of the numbers of a group of `k = 0`: its exponents have its `m` and degree; `a` is at
most the least `|y_0|` they select and `hi` at least the largest; `|ln x|` then lies in `[ℓ₁, ℓ₂]`; the bounds of `b`
at the ends are those of `ȳ` or of the constant `hi`; and `b + E ≤ 3/5` at `ℓ₂` -/
def Log8G0Ok (last : Bool) (g : Log8G0) : Prop :=
  (∀ e : ℤ, g.elo ≤ e → e ≤ g.ehi → g.m = (e + 7).toNat ∧ g.d = exp8Deg (e - g.m)) ∧ 1 ≤ g.d ∧ 0 ≤ g.a ∧
    (if last then g.a = 0 else
      g.a ≤ (2 : ℚ) ^ g.elo * (1 - 1 / 2 ^ 46) * (1 - red8U) / (1 + red8U)) ∧
    min log8Top0 ((2 : ℚ) ^ (g.ehi + 1)) ≤ g.hi ∧ 0 ≤ g.l₁ ∧
    (g.l₁ = 0 ∨ g.l₁ * (1 + log8E1) + log8E0 ≤ g.a) ∧ g.hi + log8E0 ≤ g.l₂ * (1 - log8E1) ∧
    (if g.cst then g.hi ≤ g.b₁ ∧ g.hi ≤ g.b₂ else g.l₁ + log8Eq g.l₁ ≤ g.b₁ ∧ g.l₂ + log8Eq g.l₂ ≤ g.b₂) ∧
    g.b₂ + log8Eq g.l₂ ≤ 3 / 5

instance (last : Bool) (g : Log8G0) : Decidable (Log8G0Ok last g) := by
  unfold Log8G0Ok
  infer_instance

/-- the kernel's evaluations of a group of `k = 0`: for each sign, at the two ends -/
def Log8Group0 (g : Log8G0) : Prop :=
  ∀ pos : Bool, Log8Eval true pos g.m g.d g.a g.l₁ g.zero g.b₁ 0 ∧
    Log8Eval true pos g.m g.d g.a g.l₂ g.zero g.b₂ 0

/-- the kernel's evaluations of an interval of `|r|` for `k ≠ 0` and a sign, at `ℓ_k^-` and at `X` -/
def Log8Bin1 (lk : ℚ) (pos : Bool) (m d : ℕ) (bn : ℚ × ℚ × ℚ × ℚ) : Prop :=
  Log8Eval false pos m d bn.1 lk false bn.2.1 bn.2.2.1 ∧ Log8Eval false pos m d bn.1 log8X false bn.2.1 bn.2.2.2

/-- the kernel's evaluations of a group of `k ≠ 0`: every interval of each sign -/
def Log8Group1 (lk : ℚ) (g : Log8G1) : Prop :=
  (∀ bn ∈ g.binsP, Log8Bin1 lk true g.m g.d bn) ∧ ∀ bn ∈ g.binsN, Log8Bin1 lk false g.m g.d bn

/-- what the kernel checks of the numbers of a group of `k ≠ 0`: its exponents have its `m` and degree; `lo` is at
most the least `|r|` they select, by the tail `∑_{i≥1}|r_i|`, and `hi` at least the largest; the intervals of each
sign cover `[lo, hi]`; and `b + E + δ ≤ 3/5` at `X` on each -/
def Log8G1Ok (top tail : ℚ) (last : Bool) (g : Log8G1) : Prop :=
  (∀ e : ℤ, g.elo ≤ e → e ≤ g.ehi → g.m = (e + 7).toNat ∧ g.d = exp8Deg (e - g.m)) ∧ 1 ≤ g.d ∧
    (if last then g.lo = 0 else g.lo ≤ max 0 ((2 : ℚ) ^ g.elo * (1 - 1 / 2 ^ 46) - 2 * tail)) ∧
    min top ((2 : ℚ) ^ (g.ehi + 1)) ≤ g.hi ∧ g.binsP ≠ [] ∧ g.binsN ≠ [] ∧
    log8CoverB g.lo g.hi (g.binsP.map fun bn => (bn.1, bn.2.1)) = true ∧
    log8CoverB g.lo g.hi (g.binsN.map fun bn => (bn.1, bn.2.1)) = true ∧
    (∀ bn ∈ g.binsP, bn.2.1 + log8Eq log8X + bn.2.2.2 ≤ 3 / 5) ∧
    ∀ bn ∈ g.binsN, bn.2.1 + log8Eq log8X + bn.2.2.2 ≤ 3 / 5

instance (top tail : ℚ) (last : Bool) (g : Log8G1) : Decidable (Log8G1Ok top tail last g) := by
  unfold Log8G1Ok
  infer_instance

end ExpansionBounds
