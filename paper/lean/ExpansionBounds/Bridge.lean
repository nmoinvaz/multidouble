import ExpansionBounds.Rounding
import FloatSpec.src.Core.FLT

/-!
# From a bounded exponent range to the unbounded one

FloatSpec states TwoSum and FastTwoSum for `FLT`, the format with a least exponent `emin`. On integer multiples of
`2^emin` the rounding of `FLT` is that of `FLX`, the unbounded format of (A2): above `2^(emin + p - 1)` the two
canonical exponents agree, and below it both roundings return their argument. The steps of TwoSum and FastTwoSum
on multiples of `2^E` stay multiples of `2^E`, so on inputs in `F p` their `FLT` results with `emin = E` are those
of `F p`.
-/

namespace ExpansionBounds

open FloatSpec.Core.Defs
open FloatSpec.Core.Generic_fmt (roundR scaled_mantissa)

/-- `z` is an integer multiple of `2^E` -/
def Mult (E : ℤ) (z : ℝ) : Prop := ∃ k : ℤ, z = k * (2 : ℝ) ^ E

namespace Mult

variable {E : ℤ} {x y : ℝ}

theorem add (hx : Mult E x) (hy : Mult E y) : Mult E (x + y) := by
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨l, rfl⟩ := hy
  exact ⟨k + l, by push_cast; ring⟩

theorem sub (hx : Mult E x) (hy : Mult E y) : Mult E (x - y) := by
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨l, rfl⟩ := hy
  exact ⟨k - l, by push_cast; ring⟩

/-- `2^(E + n) = 2^n 2^E` for a natural `n = E' - E`, as the integer factor of a multiple -/
theorem pow_split {E E' : ℤ} (h : E ≤ E') : ∃ n : ℕ, (2 : ℝ) ^ E' = (2 : ℝ) ^ n * (2 : ℝ) ^ E := by
  refine ⟨(E' - E).toNat, ?_⟩
  rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]
  congr 1
  omega

theorem mono {E' : ℤ} (hx : Mult E' x) (h : E ≤ E') : Mult E x := by
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨n, hn⟩ := pow_split h
  exact ⟨k * 2 ^ n, by rw [hn]; push_cast; ring⟩

end Mult

variable (p : ℤ)

/-- an element of `F p` is a multiple of `2` to its canonical exponent -/
theorem F_mult {x : ℝ} (hx : F p x) :
    Mult (FloatSpec.Core.Generic_fmt.cexp 2 (FloatSpec.Core.FLX.FLX_exp p) x) x := by
  refine ⟨FloatSpec.Core.Raux.Ztrunc (scaled_mantissa 2 (FloatSpec.Core.FLX.FLX_exp p) x), ?_⟩
  unfold F FloatSpec.Core.Generic_fmt.generic_format at hx
  dsimp only at hx
  conv_lhs => rw [hx]
  norm_num

section Rounding

variable (fexp : ℤ → ℤ) (rnd : ℝ → ℤ) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd]

theorem roundR_zero : roundR 2 fexp rnd 0 = 0 := by
  have h := FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_IZR (rnd := rnd) 0
  simp only [Int.cast_zero] at h
  simp [roundR, scaled_mantissa, h]

/-- a multiple of `2^E` whose canonical exponent is at most `E` is returned by any rounding -/
theorem roundR_eq_of_le {E : ℤ} {z : ℝ} (hz : Mult E z) (hc : FloatSpec.Core.Generic_fmt.cexp 2 fexp z ≤ E) :
    roundR 2 fexp rnd z = z := by
  obtain ⟨n, hn⟩ := Mult.pow_split hc
  simp only [roundR, scaled_mantissa]
  generalize FloatSpec.Core.Generic_fmt.cexp 2 fexp z = c at hn ⊢
  obtain ⟨k, rfl⟩ := hz
  have hsm : (k : ℝ) * 2 ^ E * ((2 : ℤ) : ℝ) ^ (-c) = ((k * 2 ^ n : ℤ) : ℝ) := by
    rw [hn, zpow_neg]
    push_cast
    field_simp
  rw [hsm, FloatSpec.Core.Generic_fmt.Valid_rnd.Zrnd_IZR (rnd := rnd) (k * 2 ^ n), hn]
  push_cast
  ring

/-- any rounding of a multiple of `2^E` is a multiple of `2^E` -/
theorem roundR_mult {E : ℤ} {z : ℝ} (hz : Mult E z) : Mult E (roundR 2 fexp rnd z) := by
  by_cases hc : FloatSpec.Core.Generic_fmt.cexp 2 fexp z ≤ E
  · rw [roundR_eq_of_le fexp rnd hz hc]
    exact hz
  · refine Mult.mono ⟨rnd (scaled_mantissa 2 fexp z), ?_⟩ (le_of_lt (not_le.mp hc))
    simp only [roundR]
    push_cast
    rfl

end Rounding

theorem RN_mult {E : ℤ} {z : ℝ} (hz : Mult E z) : Mult E (RN p z) := roundR_mult _ _ hz

variable [Prec_gt_0 p]

/-- on multiples of `2^E`, rounding in `FLT` with `emin = E` is rounding in `FLX` -/
theorem roundR_FLT_eq_FLX (rnd : ℝ → ℤ) [FloatSpec.Core.Generic_fmt.Valid_rnd rnd] {E : ℤ} {z : ℝ} (hz : Mult E z) :
    roundR 2 (FloatSpec.Core.FLT.FLT_exp p E) rnd z = roundR 2 (FloatSpec.Core.FLX.FLX_exp p) rnd z := by
  by_cases hbig : (2 : ℝ) ^ (E + p - 1) ≤ |z|
  · exact FloatSpec.Core.FLT.round_FLT_FLX (prec := p) (emin := E) 2 rnd z (by exact_mod_cast hbig)
  · by_cases hz0 : z = 0
    · subst hz0
      rw [roundR_zero, roundR_zero]
    · have hmag : FloatSpec.Core.Raux.mag 2 z ≤ E + p - 1 := by
        have h := FloatSpec.Core.Raux.mag_le_bpow 2 z (E + p - 1) (by norm_num) hz0
          (by exact_mod_cast not_le.mp hbig) trivial
        simpa [Std.Do.wp, Std.Do.PostCond.noThrow, pure] using h
      rw [roundR_eq_of_le _ rnd hz, roundR_eq_of_le _ rnd hz]
      · show FloatSpec.Core.FLX.FLX_exp p (FloatSpec.Core.Raux.mag 2 z) ≤ E
        unfold FloatSpec.Core.FLX.FLX_exp
        omega
      · show FloatSpec.Core.FLT.FLT_exp p E (FloatSpec.Core.Raux.mag 2 z) ≤ E
        unfold FloatSpec.Core.FLT.FLT_exp
        exact max_le (by omega) le_rfl

/-- an element of `F p` whose canonical exponent is at least `E` is in `FLT` with `emin = E` -/
theorem FLT_of_F {E : ℤ} {x : ℝ} (hx : F p x)
    (hE : E ≤ FloatSpec.Core.Generic_fmt.cexp 2 (FloatSpec.Core.FLX.FLX_exp p) x) :
    FloatSpec.Core.Generic_fmt.generic_format 2 (FloatSpec.Core.FLT.FLT_exp p E) x := by
  have h := FloatSpec.Core.Generic_fmt.generic_format_round 2 (FloatSpec.Core.FLT.FLT_exp p E)
    (FloatSpec.Core.Generic_fmt.Znearest tieEven) x
  have hx' : roundR 2 (FloatSpec.Core.FLT.FLT_exp p E) (FloatSpec.Core.Generic_fmt.Znearest tieEven) x = x := by
    rw [roundR_FLT_eq_FLX p _ ((F_mult p hx).mono hE)]
    exact RN_of_F p hx
  rwa [FloatSpec.Core.Generic_fmt.round_to_generic_int_eq_roundR, hx'] at h

end ExpansionBounds
