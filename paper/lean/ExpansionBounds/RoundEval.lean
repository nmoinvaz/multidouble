import ExpansionBounds.SharpMul

/-!
# `RN` on the rationals

`rnQ p q` computes `RN p q` for a rational `q`: with `2^{e-1} ≤ |q| < 2^e`, the scaled mantissa `q 2^{p-e}` is
rounded to the nearest integer, ties to even, and scaled back. `cast_rn` shows that its value, cast to `ℝ`, is
`RN p q`, from the definitions of FloatSpec: the magnitude, the canonical exponent and `Znearest`. So the kernel can
round, and `F p q` is decided by `rnQ p q = q`. `TwoSum` on rationals of `F p` follows: its sum is `rnQ p (a + b)` and
its error what is left.
-/

namespace ExpansionBounds

variable (p : ℤ)

/-- `RN` at `x` with `2^{e-1} ≤ |x| < 2^e`: the nearest integer to `x 2^{p-e}`, times `2^{e-p}` -/
theorem RN_of_mag {x : ℝ} {e : ℤ} (hlo : (2 : ℝ) ^ (e - 1) ≤ |x|) (hhi : |x| < (2 : ℝ) ^ e) :
    RN p x = ((FloatSpec.Core.Generic_fmt.Znearest tieEven (x * (2 : ℝ) ^ (-(e - p))) : ℤ) : ℝ) * (2 : ℝ) ^ (e - p) := by
  have hm : FloatSpec.Core.Raux.mag 2 x = e := by
    have h := FloatSpec.Core.Raux.mag_unique 2 x e (by norm_num) (by push_cast; exact hlo) (by push_cast; exact hhi) trivial
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, pure] using h
  have hc : FloatSpec.Core.Generic_fmt.cexp 2 (FloatSpec.Core.FLX.FLX_exp p) x = e - p := by
    show FloatSpec.Core.FLX.FLX_exp p (FloatSpec.Core.Raux.mag 2 x) = _
    rw [hm]
    rfl
  unfold RN FloatSpec.Core.Generic_fmt.roundR FloatSpec.Core.Generic_fmt.scaled_mantissa
  simp only []
  rw [hc]
  simp only [Int.cast_ofNat]

/-- the nearest integer with ties to even, from the floor -/
theorem Znearest_tieEven (s : ℝ) :
    FloatSpec.Core.Generic_fmt.Znearest tieEven s =
      if s - ⌊s⌋ < 1 / 2 then ⌊s⌋ else if 1 / 2 < s - ⌊s⌋ then ⌊s⌋ + 1 else if ⌊s⌋ % 2 = 1 then ⌊s⌋ + 1 else ⌊s⌋ := by
  have hfl : FloatSpec.Core.Raux.Zfloor s = ⌊s⌋ := rfl
  have hceil : 0 < s - ⌊s⌋ → FloatSpec.Core.Raux.Zceil s = ⌊s⌋ + 1 := fun h => by
    show ⌈s⌉ = ⌊s⌋ + 1
    rw [Int.ceil_eq_iff]
    constructor
    · push_cast
      linarith
    · push_cast
      linarith [Int.lt_floor_add_one s]
  split_ifs with h1 h2 h3
  · rw [FloatSpec.Core.Generic_fmt.Znearest_eq_floor_of_lt_half _ _ (by rw [hfl]; exact h1), hfl]
  · rw [FloatSpec.Core.Generic_fmt.Znearest_eq_ceil_of_half_lt _ _ (by rw [hfl]; exact h2), hceil (by linarith)]
  · have hmid : s - ⌊s⌋ = 1 / 2 := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
    rw [FloatSpec.Core.Generic_fmt.Znearest_eq_choice_of_eq_half _ _ (by rw [hfl]; exact hmid), hfl, hceil (by linarith)]
    simp [tieEven, h3]
  · have hmid : s - ⌊s⌋ = 1 / 2 := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
    rw [FloatSpec.Core.Generic_fmt.Znearest_eq_choice_of_eq_half _ _ (by rw [hfl]; exact hmid), hfl]
    simp [tieEven, h3]

/-- the nearest integer to a rational, ties to even -/
def nearQ (s : ℚ) : ℤ :=
  if s - ⌊s⌋ < 1 / 2 then ⌊s⌋ else if 1 / 2 < s - ⌊s⌋ then ⌊s⌋ + 1 else if ⌊s⌋ % 2 = 1 then ⌊s⌋ + 1 else ⌊s⌋

theorem Znearest_cast (s : ℚ) : FloatSpec.Core.Generic_fmt.Znearest tieEven (s : ℝ) = nearQ s := by
  have hd : (s : ℝ) - ((⌊s⌋ : ℤ) : ℝ) = ((s - ((⌊s⌋ : ℤ) : ℚ) : ℚ) : ℝ) := by push_cast; rfl
  have hh : (1 : ℝ) / 2 = (((1 : ℚ) / 2 : ℚ) : ℝ) := by norm_num
  have h1 : ((s : ℝ) - ((⌊s⌋ : ℤ) : ℝ) < 1 / 2) ↔ (s - ((⌊s⌋ : ℤ) : ℚ) < 1 / 2) := by
    rw [hd, hh, Rat.cast_lt]
  have h2 : ((1 : ℝ) / 2 < (s : ℝ) - ((⌊s⌋ : ℤ) : ℝ)) ↔ ((1 : ℚ) / 2 < s - ((⌊s⌋ : ℤ) : ℚ)) := by
    rw [hd, hh, Rat.cast_lt]
  rw [Znearest_tieEven, Rat.floor_cast]
  unfold nearQ
  simp only [h1, h2]

/-- the `e` with `2^{e-1} ≤ |q| < 2^e`, for `q ≠ 0`: from the lengths of the numerator and the denominator -/
def magQ (q : ℚ) : ℤ :=
  if (2 : ℚ) ^ ((Nat.log2 q.num.natAbs : ℤ) - (Nat.log2 q.den : ℤ)) ≤ |q| then
    (Nat.log2 q.num.natAbs : ℤ) - (Nat.log2 q.den : ℤ) + 1
  else (Nat.log2 q.num.natAbs : ℤ) - (Nat.log2 q.den : ℤ)

theorem magQ_spec {q : ℚ} (hq : q ≠ 0) : (2 : ℚ) ^ (magQ q - 1) ≤ |q| ∧ |q| < (2 : ℚ) ^ magQ q := by
  obtain ⟨N, hN⟩ : ∃ N, N = q.num.natAbs := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = q.den := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by
    rw [hN]
    exact Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hq)
  have hD0 : D ≠ 0 := by rw [hD]; exact q.den_nz
  have hNpos : (0 : ℚ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  have hDpos : (0 : ℚ) < D := by exact_mod_cast Nat.pos_of_ne_zero hD0
  have hq' : |q| = (N : ℚ) / D := by
    rw [hN, hD, ← Rat.num_div_den q, abs_div, Nat.abs_cast, ← Int.cast_abs, Int.abs_eq_natAbs]
    simp [Rat.num_div_den]
  -- `2^a ≤ N < 2^{a+1}` and `2^b ≤ D < 2^{b+1}`
  have a1 : ((2 : ℚ) ^ (Nat.log2 N : ℤ)) ≤ N := by
    rw [zpow_natCast]
    exact_mod_cast Nat.log2_self_le hN0
  have a2 : (N : ℚ) < (2 : ℚ) ^ ((Nat.log2 N : ℤ) + 1) := by
    rw [show ((Nat.log2 N : ℤ) + 1) = ((Nat.log2 N + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    exact_mod_cast Nat.lt_log2_self
  have b1 : ((2 : ℚ) ^ (Nat.log2 D : ℤ)) ≤ D := by
    rw [zpow_natCast]
    exact_mod_cast Nat.log2_self_le hD0
  have b2 : (D : ℚ) < (2 : ℚ) ^ ((Nat.log2 D : ℤ) + 1) := by
    rw [show ((Nat.log2 D : ℤ) + 1) = ((Nat.log2 D + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    exact_mod_cast Nat.lt_log2_self
  have h2 : (0 : ℚ) < 2 := by norm_num
  -- `2^{a-b-1} < |q| < 2^{a-b+1}`
  have lo : (2 : ℚ) ^ ((Nat.log2 N : ℤ) - (Nat.log2 D : ℤ) - 1) < |q| := by
    rw [hq', lt_div_iff₀ hDpos]
    calc (2 : ℚ) ^ ((Nat.log2 N : ℤ) - (Nat.log2 D : ℤ) - 1) * D
        < (2 : ℚ) ^ ((Nat.log2 N : ℤ) - (Nat.log2 D : ℤ) - 1) * (2 : ℚ) ^ ((Nat.log2 D : ℤ) + 1) :=
          mul_lt_mul_of_pos_left b2 (zpow_pos h2 _)
      _ = (2 : ℚ) ^ (Nat.log2 N : ℤ) := by rw [← zpow_add₀ h2.ne']; congr 1; ring
      _ ≤ N := a1
  have hi : |q| < (2 : ℚ) ^ ((Nat.log2 N : ℤ) - (Nat.log2 D : ℤ) + 1) := by
    rw [hq', div_lt_iff₀ hDpos]
    calc (N : ℚ) < (2 : ℚ) ^ ((Nat.log2 N : ℤ) + 1) := a2
      _ = (2 : ℚ) ^ ((Nat.log2 N : ℤ) - (Nat.log2 D : ℤ) + 1) * (2 : ℚ) ^ (Nat.log2 D : ℤ) := by
        rw [← zpow_add₀ h2.ne']; congr 1; ring
      _ ≤ (2 : ℚ) ^ ((Nat.log2 N : ℤ) - (Nat.log2 D : ℤ) + 1) * D :=
        mul_le_mul_of_nonneg_left b1 (zpow_pos h2 _).le
  unfold magQ
  rw [← hN, ← hD]
  split_ifs with h
  · exact ⟨by rw [add_sub_cancel_right]; exact h, hi⟩
  · exact ⟨lo.le, not_le.mp h⟩

/-- `RN` on the rationals: the scaled mantissa rounded to the nearest integer, ties to even, and scaled back -/
def rnQ (q : ℚ) : ℚ :=
  if q = 0 then 0 else (nearQ (q * (2 : ℚ) ^ (-(magQ q - p))) : ℚ) * (2 : ℚ) ^ (magQ q - p)

/-- `rnQ`, cast to `ℝ`, is `RN` -/
theorem cast_rn (q : ℚ) : ((rnQ p q : ℚ) : ℝ) = RN p q := by
  by_cases hq : q = 0
  · simp [rnQ, hq, RN_zero]
  obtain ⟨hlo, hhi⟩ := magQ_spec hq
  have hlo' : (2 : ℝ) ^ (magQ q - 1) ≤ |(q : ℝ)| := by
    have h := (Rat.cast_le (K := ℝ)).mpr hlo
    simpa using h
  have hhi' : |(q : ℝ)| < (2 : ℝ) ^ magQ q := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hhi
    simpa using h
  have hs : (q : ℝ) * (2 : ℝ) ^ (-(magQ q - p)) = ((q * (2 : ℚ) ^ (-(magQ q - p)) : ℚ) : ℝ) := by
    push_cast
    rfl
  rw [RN_of_mag p hlo' hhi', hs, Znearest_cast]
  simp only [rnQ, hq, ↓reduceIte]
  push_cast
  rfl

/-- the rationals of `F p` are those that `rnQ` leaves as they are -/
theorem F_iff_rn [Prec_gt_0 p] (q : ℚ) : F p (q : ℝ) ↔ rnQ p q = q := by
  constructor
  · intro h
    have h1 := RN_of_F p h
    rw [← cast_rn] at h1
    exact_mod_cast h1
  · intro h
    have h1 := F_RN p (q : ℝ)
    rwa [← cast_rn, h] at h1

/-- TwoSum on rationals: the rounded sum and what is left -/
def twoSumQ (a b : ℚ) : ℚ × ℚ := (rnQ p (a + b), a + b - rnQ p (a + b))

/-- `twoSumQ`, cast to `ℝ`, is TwoSum on `F p` -/
theorem cast_twoSum [Prec_gt_0 p] (hp : 1 < p) {a b : ℚ} (ha : F p (a : ℝ)) (hb : F p (b : ℝ)) :
    twoSum p a b = (((twoSumQ p a b).1 : ℝ), ((twoSumQ p a b).2 : ℝ)) := by
  obtain ⟨h1, -, -⟩ := facts_a p hp ha hb
  have hs : (twoSum p a b).1 = RN p ((a : ℝ) + b) := rfl
  have hr : ((rnQ p (a + b) : ℚ) : ℝ) = RN p ((a : ℝ) + b) := by
    rw [cast_rn]
    push_cast
    rfl
  refine Prod.ext ?_ ?_
  · show (twoSum p a b).1 = ((rnQ p (a + b) : ℚ) : ℝ)
    rw [hr, hs]
  · show (twoSum p a b).2 = ((a + b - rnQ p (a + b) : ℚ) : ℝ)
    push_cast
    rw [hr, ← hs]
    linarith

end ExpansionBounds
