import ExpansionBounds.Bridge
import FloatSpec.src.Pff.Pff2Flocq
import FloatSpec.src.Prop.Mult_error

/-!
# Lemma `lem:facts`

Under Assumption `as:fp`:
(a) `TwoSum(a, b) = (s, e)` satisfies `s + e = a + b` and `|e| ≤ min(|a|, |b|, ū|a + b|)`; `e = 0` if and only if
`a + b ∈ 𝔽`.
(b) If `|a| ≥ |b|`, `FastTwoSum(a, b)` returns the `s` and `e` of `TwoSum(a, b)`.
(c) `TwoProd(a, b) = (q, e)` satisfies `q + e = ab`, `|e| ≤ ū|ab|` and `|q| ≤ (1 + u)|ab|`.

The paper's "up to the sign of a zero `e`" in (b) has no counterpart here: the model's values are reals.
-/

namespace ExpansionBounds

open FloatSpec.Core.Defs
open FloatSpec.Core.Generic_fmt (roundR)

variable (p : ℤ) [Prec_gt_0 p]

/-- a scale `E ≤ 0` of which `a` and `b` are multiples, and at which both are in `FLT` with `emin = E` -/
private theorem scale {a b : ℝ} (ha : F p a) (hb : F p b) :
    ∃ E : ℤ, E ≤ 0 ∧ Mult E a ∧ Mult E b ∧
      FloatSpec.Core.Generic_fmt.generic_format 2 (FloatSpec.Core.FLT.FLT_exp p E) a ∧
      FloatSpec.Core.Generic_fmt.generic_format 2 (FloatSpec.Core.FLT.FLT_exp p E) b := by
  set ea := FloatSpec.Core.Generic_fmt.cexp 2 (FloatSpec.Core.FLX.FLX_exp p) a
  set eb := FloatSpec.Core.Generic_fmt.cexp 2 (FloatSpec.Core.FLX.FLX_exp p) b
  have hEa : min (min ea eb) 0 ≤ ea := le_trans (min_le_left _ _) (min_le_left _ _)
  have hEb : min (min ea eb) 0 ≤ eb := le_trans (min_le_left _ _) (min_le_right _ _)
  exact ⟨min (min ea eb) 0, min_le_right _ _, (F_mult p ha).mono hEa, (F_mult p hb).mono hEb,
    FLT_of_F p ha hEa, FLT_of_F p hb hEb⟩

/-- TwoSum is exact: `s + e = a + b` (Møller, Knuth), from FloatSpec's `TwoSum_correct` -/
theorem twoSum_add (hp : 1 < p) {a b : ℝ} (ha : F p a) (hb : F p b) :
    (twoSum p a b).1 + (twoSum p a b).2 = a + b := by
  obtain ⟨E, hE0, hma, hmb, haF, hbF⟩ := scale p ha hb
  have hR : ∀ z, Mult E z →
      roundR 2 (FloatSpec.Core.FLT.FLT_exp p E) (FloatSpec.Core.Generic_fmt.Znearest tieEven) z = RN p z :=
    fun z hz => roundR_FLT_eq_FLX p _ hz
  have hpre : precisionNotZero p ∧ E ≤ 0 ∧ (∀ t : ℤ, tieEven t = !tieEven (-(t + 1))) ∧
      FloatSpec.Core.Generic_fmt.generic_format 2 (FLT_exp E p) a ∧
      FloatSpec.Core.Generic_fmt.generic_format 2 (FLT_exp E p) b :=
    ⟨hp, hE0, tieEven_symm, haF, hbF⟩
  have H : TwoSum_result E p tieEven a b := by
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, pure, TwoSum_correct_check] using
      TwoSum_correct E p tieEven a b hpre
  simp only [TwoSum_result, TwoSum_round] at H
  have h1 : Mult E (a + b) := hma.add hmb
  rw [hR _ h1] at H
  have hs := RN_mult p h1
  have h2 : Mult E (RN p (a + b) - a) := hs.sub hma
  rw [hR _ h2] at H
  have hb' := RN_mult p h2
  have h3 : Mult E (RN p (a + b) - RN p (RN p (a + b) - a)) := hs.sub hb'
  rw [hR _ h3] at H
  have h4 : Mult E (a - RN p (RN p (a + b) - RN p (RN p (a + b) - a))) := hma.sub (RN_mult p h3)
  rw [hR _ h4] at H
  have h5 : Mult E (b - RN p (RN p (a + b) - a)) := hmb.sub hb'
  rw [hR _ h5] at H
  rw [hR _ ((RN_mult p h4).add (RN_mult p h5))] at H
  exact H

/-- FastTwoSum is exact when `|b| ≤ |a|`: `s + e = a + b` (Dekker), from FloatSpec's `Fast2Sum_correct` -/
theorem fastTwoSum_add (hp : 1 < p) {a b : ℝ} (ha : F p a) (hb : F p b) (hba : |b| ≤ |a|) :
    (fastTwoSum p a b).1 + (fastTwoSum p a b).2 = a + b := by
  obtain ⟨E, hE0, hma, hmb, haF, hbF⟩ := scale p ha hb
  have hR : ∀ z, Mult E z →
      roundR 2 (FloatSpec.Core.FLT.FLT_exp p E) (FloatSpec.Core.Generic_fmt.Znearest tieEven) z = RN p z :=
    fun z hz => roundR_FLT_eq_FLX p _ hz
  have hpre : precisionNotZero p ∧ E ≤ 0 ∧ (∀ t : ℤ, tieEven t = !tieEven (-(t + 1))) ∧
      FloatSpec.Core.Generic_fmt.generic_format 2 (FLT_exp E p) a ∧
      FloatSpec.Core.Generic_fmt.generic_format 2 (FLT_exp E p) b ∧ |b| ≤ |a| :=
    ⟨hp, hE0, tieEven_symm, haF, hbF, hba⟩
  have H : Fast2Sum_result E p tieEven a b := by
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, pure, Fast2Sum_correct_check] using
      Fast2Sum_correct E p tieEven a b hpre
  simp only [Fast2Sum_result, Fast2Sum_round] at H
  have h1 : Mult E (a + b) := hma.add hmb
  rw [hR _ h1] at H
  have h2 : Mult E (a - RN p (a + b)) := hma.sub (RN_mult p h1)
  rw [hR _ h2] at H
  rw [hR _ (hmb.add (RN_mult p h2))] at H
  have hneg : RN p (a - RN p (a + b)) = -RN p (RN p (a + b) - a) := by
    rw [← RN_neg]
    congr 1
    ring
  rw [hneg, ← sub_eq_add_neg] at H
  exact H

/-- Lemma `lem:facts` (a) -/
theorem facts_a (hp : 1 < p) {a b : ℝ} (ha : F p a) (hb : F p b) :
    (twoSum p a b).1 + (twoSum p a b).2 = a + b ∧
      |(twoSum p a b).2| ≤ min (min |a| |b|) (us p * |a + b|) ∧
      ((twoSum p a b).2 = 0 ↔ F p (a + b)) := by
  have hadd := twoSum_add p hp ha hb
  have hs : (twoSum p a b).1 = RN p (a + b) := rfl
  -- the error is the rounding error of the sum
  have he : |(twoSum p a b).2| = |RN p (a + b) - (a + b)| := by
    rw [abs_sub_comm, ← hs]
    congr 1
    linarith
  have hN := (RN_nearest p (a + b)).2
  refine ⟨hadd, ?_, ?_⟩
  · rw [he]
    refine le_min (le_min ?_ ?_) (abs_RN_sub_le_us p _)
    · calc |RN p (a + b) - (a + b)| ≤ |b - (a + b)| := hN b hb
        _ = |a| := by rw [show b - (a + b) = -a by ring, abs_neg]
    · calc |RN p (a + b) - (a + b)| ≤ |a - (a + b)| := hN a ha
        _ = |b| := by rw [show a - (a + b) = -b by ring, abs_neg]
  · constructor
    · intro h0
      have h : RN p (a + b) = a + b := by rw [← hs]; linarith
      rw [← h]
      exact F_RN p _
    · intro h
      have h' : (twoSum p a b).1 = a + b := hs.trans (RN_of_F p h)
      linarith

/-- Lemma `lem:facts` (b) -/
theorem facts_b (hp : 1 < p) {a b : ℝ} (ha : F p a) (hb : F p b) (hba : |b| ≤ |a|) :
    fastTwoSum p a b = twoSum p a b := by
  have h1 := fastTwoSum_add p hp ha hb hba
  have h2 := twoSum_add p hp ha hb
  have hs : (fastTwoSum p a b).1 = (twoSum p a b).1 := rfl
  exact Prod.ext hs (by linarith)

/-- Lemma `lem:facts` (c): under (A2) the error `ab - q` is in `𝔽`, so the fused multiply-add returns it exactly -/
theorem facts_c {a b : ℝ} (ha : F p a) (hb : F p b) :
    (twoProd p a b).1 + (twoProd p a b).2 = a * b ∧
      |(twoProd p a b).2| ≤ us p * |a * b| ∧ |(twoProd p a b).1| ≤ (1 + u p) * |a * b| := by
  have hF : F p (a * b - RN p (a * b)) := by
    have h := mult_error_FLX (beta := 2) (prec := p) (rnd := FloatSpec.Core.Generic_fmt.Znearest tieEven) a b
      (by norm_num) ha hb
    have h' := F_neg p h
    rwa [neg_sub] at h'
  have he : (twoProd p a b).2 = a * b - RN p (a * b) := RN_of_F p hF
  have hq : (twoProd p a b).1 = RN p (a * b) := rfl
  refine ⟨by rw [he, hq]; ring, ?_, hq ▸ abs_RN_le p _⟩
  rw [he, abs_sub_comm]
  exact abs_RN_sub_le_us p _

end ExpansionBounds
