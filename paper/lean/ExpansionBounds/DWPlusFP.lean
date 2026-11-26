import ExpansionBounds.DDHorner
import ExpansionBounds.SharpDiv

/-!
# DWPlusFP, the sum of a double word and a float

Algorithm 4 of Joldes, Muller and Popescu (2017), the ADDF of `DD::exp` and `DD::ln`:

  `(s_h, s_ℓ) = TwoSum(x_h, y)`, `v = RN(x_ℓ + s_ℓ)`, `(z_h, z_ℓ) = FastTwoSum(s_h, v)`.

This file has the algorithm (`dwPlusFP`), Theorem 2.2 of that paper with its result a double word (`dwPlusFP_good`:
for `p ≥ 3`, a double word `x` and a float `y`, the result is a double word within `2u²` of `x + y`, relatively),
and Lemma 41 on double words, which Proposition 44's logarithm uses as `hφex`: for a double word `x` with
`x_h ∈ [1/2, 2]`, `DWPlusFP(x, -1) = x - 1` exactly (`dwPlusFP_sub_one`). `x_h - 1` is exact by Sterbenz's lemma, so
`s_ℓ = 0` and `v = x_ℓ`; and `x_h - 1`, a multiple of the spacing of the floats at `x_h`, is zero or at least
`|x_ℓ|`, so the last FastTwoSum is exact.

The paper states Theorem 2.2 with no condition on `p`. Its proof takes the last FastTwoSum as exact from
`s_h ≥ 1/2 > 3u ≥ |v|`, which needs `u ≤ 1/8`; the theorem here assumes `p ≥ 3`.
-/

namespace ExpansionBounds

variable (p : ℤ)

/-- DWPlusFP: `(s_h, s_ℓ) = TwoSum(x_h, y)`, `v = RN(x_ℓ + s_ℓ)` and `(z_h, z_ℓ) = FastTwoSum(s_h, v)` -/
noncomputable def dwPlusFP (x : ℝ × ℝ) (y : ℝ) : ℝ × ℝ :=
  fastTwoSum p (twoSum p x.1 y).1 (RN p (x.2 + (twoSum p x.1 y).2))

variable [Prec_gt_0 p]

/-- a FastTwoSum that is exact returns a double word -/
theorem fastTwoSum_dw {a b : ℝ} (h : (fastTwoSum p a b).1 + (fastTwoSum p a b).2 = a + b) :
    DW p (fastTwoSum p a b) := by
  refine ⟨F_RN p _, F_RN p _, ?_⟩
  rw [h]
  rfl

/-- Lemma 41 (`lem:fexact`) on double words: for `x_h ∈ [1/2, 2]`, `DWPlusFP(x, -1) = x - 1` exactly, and the
result is a double word -/
theorem dwPlusFP_sub_one (hp : 1 < p) {x : ℝ × ℝ} (hx : DW p x) (h1 : 1 / 2 ≤ x.1) (h2 : x.1 ≤ 2) :
    dwVal (dwPlusFP p x (-1)) = dwVal x - 1 ∧ DW p (dwPlusFP p x (-1)) := by
  have hu := u_pos p
  have hF1 : F p (1 : ℝ) := F_one p
  -- `x_h - 1` is in `F`, by Sterbenz's lemma on either side
  have hs : F p (x.1 + -1) := by
    rw [← sub_eq_add_neg]
    rcases le_total x.1 (3 / 2) with h | h
    · have := F_sub_of_near p hF1 hx.1 (by
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 1), abs_le]
        constructor <;> linarith)
      rw [show x.1 - 1 = -(1 - x.1) by ring]
      exact F_neg p this
    · exact F_sub_of_near p hx.1 hF1 (by
        rw [abs_of_pos (by linarith : (0 : ℝ) < x.1), abs_le]
        constructor <;> linarith)
  -- so `TwoSum(x_h, -1) = (x_h - 1, 0)` and `v = x_ℓ`
  have hF1' : F p (-1 : ℝ) := F_neg p hF1
  have hts1 : (twoSum p x.1 (-1)).1 = x.1 + -1 := RN_of_F p hs
  have hts2 : (twoSum p x.1 (-1)).2 = 0 := by
    have := twoSum_add p hp hx.1 hF1'
    rw [hts1] at this
    linarith
  have hd : dwPlusFP p x (-1) = fastTwoSum p (x.1 + -1) x.2 := by
    unfold dwPlusFP
    rw [hts1, hts2, add_zero, RN_of_F p hx.2.1]
  rw [hd]
  -- `x_h - 1` is zero or at least `|x_ℓ|`
  have hxl := dw_lo_le_u p hx.2.2
  have hadd : (fastTwoSum p (x.1 + -1) x.2).1 + (fastTwoSum p (x.1 + -1) x.2).2 = x.1 + -1 + x.2 := by
    by_cases h0 : x.1 + -1 = 0
    · rw [h0]
      have hz : RN p (0 : ℝ) = 0 := RN_of_F p (F_zero p)
      simp [fastTwoSum, RN_of_F p hx.2.1, hz]
    · refine fastTwoSum_add p hp hs hx.2.1 ?_
      have e1 : (2 : ℝ) ^ (1 - p) = 2 * u p := by
        unfold u
        rw [show (1 : ℤ) - p = 1 + -p by ring, zpow_add₀ two_ne_zero, zpow_one]
      have e2 : (2 : ℝ) ^ (-p) = u p := rfl
      rcases lt_trichotomy x.1 1 with hlt | heq | hgt
      · -- `x_h ∈ [1/2, 1)`: a multiple of `u`, so `1 - x_h ≥ u > |x_ℓ|`
        have hm : Mult (-p) x.1 := mult_of_F p hx.1 (by
          rw [show (-p + p - 1 : ℤ) = -1 by ring, abs_of_pos (by linarith)]
          norm_num
          linarith)
        have hm1 : Mult (-p) (1 : ℝ) := by
          have := Mult.zpow (E := -p) (e := 0) (by omega)
          rwa [zpow_zero] at this
        have := Mult.le_sub hm hm1 hlt
        rw [e2] at this
        rw [abs_of_nonpos (by linarith : x.1 + -1 ≤ 0), abs_of_pos (by linarith : (0 : ℝ) < x.1)] at *
        nlinarith
      · exact absurd (by rw [heq]; norm_num) h0
      · -- `x_h ∈ (1, 2]`: a multiple of `2u`, so `x_h - 1 ≥ 2u ≥ |x_ℓ|`
        have hm : Mult (1 - p) x.1 := mult_of_one_le p hx.1 hgt.le
        have hm1 : Mult (1 - p) (1 : ℝ) := by
          have := Mult.zpow (E := 1 - p) (e := 0) (by omega)
          rwa [zpow_zero] at this
        have := Mult.le_sub hm1 hm hgt
        rw [e1] at this
        rw [abs_of_pos (by linarith : (0 : ℝ) < x.1 + -1), abs_of_pos (by linarith : (0 : ℝ) < x.1)] at *
        nlinarith
  refine ⟨?_, fastTwoSum_dw p hadd⟩
  unfold dwVal
  rw [hadd]
  ring

omit [Prec_gt_0 p] in
/-- TwoSum commutes with a scaling by a power of two -/
theorem twoSum_scale (k : ℤ) (a b : ℝ) : twoSum p ((2 : ℝ) ^ k * a) ((2 : ℝ) ^ k * b) =
    ((2 : ℝ) ^ k * (twoSum p a b).1, (2 : ℝ) ^ k * (twoSum p a b).2) := by
  unfold twoSum
  simp only [← mul_add, RN_zpow_mul, ← mul_sub]

omit [Prec_gt_0 p] in
/-- DWPlusFP commutes with a scaling by a power of two -/
theorem dwPlusFP_scale (k : ℤ) (x : ℝ × ℝ) (y : ℝ) :
    dwPlusFP p ((2 : ℝ) ^ k * x.1, (2 : ℝ) ^ k * x.2) ((2 : ℝ) ^ k * y) =
      ((2 : ℝ) ^ k * (dwPlusFP p x y).1, (2 : ℝ) ^ k * (dwPlusFP p x y).2) := by
  unfold dwPlusFP
  simp only [twoSum_scale, ← mul_add, RN_zpow_mul, fastTwoSum_scale]

/-- DWPlusFP commutes with negation -/
theorem dwPlusFP_neg (x : ℝ × ℝ) (y : ℝ) :
    dwPlusFP p (-x.1, -x.2) (-y) = (-(dwPlusFP p x y).1, -(dwPlusFP p x y).2) := by
  unfold dwPlusFP
  simp only [twoSum_neg, ← neg_add, RN_neg, fastTwoSum_neg]

/-! ### Theorem 2.2 of JMP17

The proof takes the larger of `x_h` and `y` in magnitude as `b` and the other as `c`, since TwoSum does not see
their order, and scales `b` into `[1, 2)`. The pair of `x_ℓ` with the larger one need not be a double word, so the
normalized statement asks only what the proof uses: `|x_ℓ| ≤ u`, and `x_ℓ ≥ -u/2` where `b = 1` and `|c| ≤ 1/2`. -/

omit [Prec_gt_0 p] in
/-- `u ≤ 1/8` from `p ≥ 3` -/
theorem u_le_eighth (hp : 3 ≤ p) : u p ≤ 1 / 8 := by
  unfold u
  calc (2 : ℝ) ^ (-p) ≤ (2 : ℝ) ^ (-3 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ = 1 / 8 := by norm_num

omit [Prec_gt_0 p] in
/-- FastTwoSum from a zero first operand returns the second -/
theorem fastTwoSum_zero_left {v : ℝ} (hv : F p v) : fastTwoSum p 0 v = (v, 0) := by
  unfold fastTwoSum
  simp only [zero_add, sub_zero, RN_of_F p hv, sub_self, RN_zero]

/-- TwoSum of two floats does not see their order -/
theorem twoSum_comm (hp : 1 < p) {a b : ℝ} (ha : F p a) (hb : F p b) : twoSum p a b = twoSum p b a := by
  have h1 := twoSum_add p hp ha hb
  have h2 := twoSum_add p hp hb ha
  have e : (twoSum p a b).1 = (twoSum p b a).1 := by
    show RN p (a + b) = RN p (b + a)
    rw [add_comm]
  exact Prod.ext e (by linarith)

/-- DWPlusFP does not see the order of `x_h` and `y` -/
theorem dwPlusFP_swap (hp : 1 < p) {b c : ℝ} (hb : F p b) (hc : F p c) (ℓ : ℝ) :
    dwPlusFP p (b, ℓ) c = dwPlusFP p (c, ℓ) b := by
  unfold dwPlusFP
  simp only [twoSum_comm p hp hb hc]

/-- the low part of a double word whose high part is below `2` in magnitude is at most `u` -/
theorem dw_lo_le_of_lt_two {a ℓ : ℝ} (hdw : RN p (a + ℓ) = a) (ha : |a| < 2) : |ℓ| ≤ u p := by
  have h2F : RN p 2 = 2 := RN_of_F p (by have := F_two_zpow p 1; rwa [zpow_one] at this)
  obtain ⟨ha1, ha2⟩ := abs_lt.mp ha
  have hle : |a + ℓ| ≤ (2 : ℝ) ^ (1 : ℤ) := by
    rw [zpow_one, abs_le]
    constructor
    · by_contra h
      have := RN_mono p (not_le.mp h).le
      rw [RN_neg, h2F, hdw] at this
      linarith
    · by_contra h
      have := RN_mono p (not_le.mp h).le
      rw [h2F, hdw] at this
      linarith
  have := RN_grid p 1 hle
  rw [hdw, zpow_one, show a - (a + ℓ) = -ℓ by ring, abs_neg] at this
  linarith

/-- the low part of a double word whose high part is `1` is at least `-u/2`: the float below `1` is `1 - u` -/
theorem dw_lo_ge_of_one (hp : 1 < p) {ℓ : ℝ} (hdw : RN p (1 + ℓ) = 1) : -(u p / 2) ≤ ℓ := by
  have hu := u_pos p
  have hu1 : u p ≤ 1 / 2 := by
    unfold u
    calc (2 : ℝ) ^ (-p) ≤ (2 : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = 1 / 2 := by norm_num
  have hmu : Mult (-p) (u p) := by unfold u; exact Mult.zpow le_rfl
  have hm1 : Mult (-p) (1 : ℝ) := by
    have := Mult.zpow (E := -p) (e := 0) (by omega)
    rwa [zpow_zero] at this
  have hF : F p (1 - u p) := F_of_mult_le p (hm1.sub hmu) (by
    rw [show (-p + p : ℤ) = 0 by ring, zpow_zero, abs_of_pos (by linarith)]
    linarith)
  have hn := (RN_nearest p (1 + ℓ)).2
  rw [hdw] at hn
  have h := hn _ hF
  rw [show (1 : ℝ) - (1 + ℓ) = -ℓ by ring, abs_neg, show 1 - u p - (1 + ℓ) = -(u p + ℓ) by ring, abs_neg] at h
  by_contra hc
  have hc' := not_le.mp hc
  rcases abs_cases ℓ with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases (u p + ℓ) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> linarith

/-- a pair whose scaling by a power of two is a double word is a double word -/
theorem DW.of_scale {z : ℝ × ℝ} (k : ℤ) (h : DW p ((2 : ℝ) ^ k * z.1, (2 : ℝ) ^ k * z.2)) : DW p z := by
  have hd := DW.scale p h (-k)
  have e : ∀ t : ℝ, (2 : ℝ) ^ (-k) * ((2 : ℝ) ^ k * t) = t := fun t => by
    rw [← mul_assoc, ← zpow_add₀ two_ne_zero, neg_add_cancel, zpow_zero, one_mul]
  simp only [e] at hd
  exact hd

/-- a pair whose negation is a double word is a double word -/
theorem DW.of_neg {z : ℝ × ℝ} (h : DW p (-z.1, -z.2)) : DW p z := by
  obtain ⟨f1, f2, f3⟩ := h
  refine ⟨by simpa using F_neg p f1, by simpa using F_neg p f2, ?_⟩
  have f3' : RN p (-z.1 + -z.2) = -z.1 := f3
  rw [← neg_add, RN_neg] at f3'
  exact neg_injective f3'

/-- the conclusion of Theorem 2.2 of JMP17 at the high part `b`, the low part `ℓ` and the float `c`: the result is
a double word within `2u²` of `b + ℓ + c`, relatively -/
def PlusFPGood (b ℓ c : ℝ) : Prop :=
  DW p (dwPlusFP p (b, ℓ) c) ∧ |dwVal (dwPlusFP p (b, ℓ) c) - (b + ℓ + c)| ≤ 2 * u p ^ 2 * |b + ℓ + c|

/-- `PlusFPGood` passes from an input scaled by a power of two -/
theorem PlusFPGood.of_scale {b ℓ c : ℝ} (k : ℤ)
    (h : PlusFPGood p ((2 : ℝ) ^ k * b) ((2 : ℝ) ^ k * ℓ) ((2 : ℝ) ^ k * c)) : PlusFPGood p b ℓ c := by
  have hK : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hs : dwPlusFP p ((2 : ℝ) ^ k * b, (2 : ℝ) ^ k * ℓ) ((2 : ℝ) ^ k * c) =
      ((2 : ℝ) ^ k * (dwPlusFP p (b, ℓ) c).1, (2 : ℝ) ^ k * (dwPlusFP p (b, ℓ) c).2) := dwPlusFP_scale p k (b, ℓ) c
  unfold PlusFPGood at h ⊢
  rw [hs] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · have hd := DW.scale p h1 (-k)
    have e : ∀ z : ℝ, (2 : ℝ) ^ (-k) * ((2 : ℝ) ^ k * z) = z := fun z => by
      rw [← mul_assoc, ← zpow_add₀ two_ne_zero, neg_add_cancel, zpow_zero, one_mul]
    simp only [e] at hd
    exact hd
  · have h3 : |(2 : ℝ) ^ k * (dwVal (dwPlusFP p (b, ℓ) c) - (b + ℓ + c))| ≤
        2 * u p ^ 2 * |(2 : ℝ) ^ k * (b + ℓ + c)| := by
      have e1 : (2 : ℝ) ^ k * (dwVal (dwPlusFP p (b, ℓ) c) - (b + ℓ + c)) =
          dwVal ((2 : ℝ) ^ k * (dwPlusFP p (b, ℓ) c).1, (2 : ℝ) ^ k * (dwPlusFP p (b, ℓ) c).2) -
            ((2 : ℝ) ^ k * b + (2 : ℝ) ^ k * ℓ + (2 : ℝ) ^ k * c) := by
        unfold dwVal
        ring
      rw [e1, mul_add, mul_add]
      exact h2
    rw [abs_mul, abs_mul, abs_of_pos hK] at h3
    exact le_of_mul_le_mul_left (by linarith) hK

/-- `PlusFPGood` passes from the negated input -/
theorem PlusFPGood.of_neg {b ℓ c : ℝ} (h : PlusFPGood p (-b) (-ℓ) (-c)) : PlusFPGood p b ℓ c := by
  have hs : dwPlusFP p (-b, -ℓ) (-c) = (-(dwPlusFP p (b, ℓ) c).1, -(dwPlusFP p (b, ℓ) c).2) :=
    dwPlusFP_neg p (b, ℓ) c
  unfold PlusFPGood at h ⊢
  rw [hs] at h
  obtain ⟨⟨f1, f2, f3⟩, h2⟩ := h
  constructor
  · refine ⟨by simpa using F_neg p f1, by simpa using F_neg p f2, ?_⟩
    have f3' : RN p (-(dwPlusFP p (b, ℓ) c).1 + -(dwPlusFP p (b, ℓ) c).2) = -(dwPlusFP p (b, ℓ) c).1 := f3
    rw [← neg_add, RN_neg] at f3'
    exact neg_injective f3'
  · have e1 : dwVal (-(dwPlusFP p (b, ℓ) c).1, -(dwPlusFP p (b, ℓ) c).2) - (-b + -ℓ + -c) =
        -(dwVal (dwPlusFP p (b, ℓ) c) - (b + ℓ + c)) := by
      unfold dwVal
      ring
    rw [e1, abs_neg, show -b + -ℓ + -c = -(b + ℓ + c) by ring, abs_neg] at h2
    exact h2

/-- DWPlusFP where its last FastTwoSum is exact, `|v| ≤ |s_h|`: the result is a double word, and it differs from
`x + y` by the rounding error of `v = RN(x_ℓ + s_ℓ)` alone -/
theorem dwPlusFP_of_le (hp : 1 < p) {b ℓ c : ℝ} (hb : F p b) (hc : F p c)
    (hv : |RN p (ℓ + (twoSum p b c).2)| ≤ |(twoSum p b c).1|) :
    dwVal (dwPlusFP p (b, ℓ) c) - (b + ℓ + c) = RN p (ℓ + (twoSum p b c).2) - (ℓ + (twoSum p b c).2) ∧
      DW p (dwPlusFP p (b, ℓ) c) := by
  have hts := twoSum_add p hp hb hc
  have hadd := fastTwoSum_add p hp (F_twoSum_fst p b c) (F_RN p (ℓ + (twoSum p b c).2)) hv
  refine ⟨?_, fastTwoSum_dw p hadd⟩
  show (fastTwoSum p (twoSum p b c).1 (RN p (ℓ + (twoSum p b c).2))).1 +
    (fastTwoSum p (twoSum p b c).1 (RN p (ℓ + (twoSum p b c).2))).2 - (b + ℓ + c) = _
  rw [hadd]
  linarith

/-- DWPlusFP at `y = -x_h`: the result is `(x_ℓ, 0)` -/
theorem dwPlusFP_cancel (hp : 1 < p) {b ℓ : ℝ} (hb : F p b) (hℓ : F p ℓ) : dwPlusFP p (b, ℓ) (-b) = (ℓ, 0) := by
  have h1 : (twoSum p b (-b)).1 = 0 := by
    show RN p (b + -b) = 0
    rw [add_neg_cancel, RN_zero]
  have h2 : (twoSum p b (-b)).2 = 0 := by
    have := twoSum_add p hp hb (F_neg p hb)
    rw [h1] at this
    linarith
  show fastTwoSum p (twoSum p b (-b)).1 (RN p (ℓ + (twoSum p b (-b)).2)) = (ℓ, 0)
  rw [h1, h2, add_zero, RN_of_F p hℓ]
  exact fastTwoSum_zero_left p hℓ

/-- DWPlusFP where `x_h + y` is a float at least `|x_ℓ|`: the sum is exact -/
theorem dwPlusFP_exact (hp : 1 < p) {b ℓ c : ℝ} (hb : F p b) (hc : F p c) (hℓ : F p ℓ) (hs : F p (b + c))
    (hl : |ℓ| ≤ |b + c|) : PlusFPGood p b ℓ c := by
  have h1 : (twoSum p b c).1 = b + c := RN_of_F p hs
  have h2 : (twoSum p b c).2 = 0 := by
    have := twoSum_add p hp hb hc
    rw [h1] at this
    linarith
  have hd : dwPlusFP p (b, ℓ) c = fastTwoSum p (b + c) ℓ := by
    show fastTwoSum p (twoSum p b c).1 (RN p (ℓ + (twoSum p b c).2)) = _
    rw [h1, h2, add_zero, RN_of_F p hℓ]
  have hadd := fastTwoSum_add p hp hs hℓ hl
  have hu := u_pos p
  unfold PlusFPGood
  rw [hd]
  refine ⟨fastTwoSum_dw p hadd, ?_⟩
  rw [show dwVal (fastTwoSum p (b + c) ℓ) - (b + ℓ + c) = 0 by unfold dwVal; rw [hadd]; ring, abs_zero]
  positivity

/-- the regular case of DWPlusFP: `|s_h| ≥ 2^k/4`, `|x_ℓ + s_ℓ| ≤ 2^k u` and `|x + y| ≥ 2^k/4`, so the last
FastTwoSum is exact and `v` is within `2^k u²/2 ≤ 2u²|x + y|` of `x_ℓ + s_ℓ` -/
theorem dwPlusFP_reg (hp : 3 ≤ p) {b ℓ c : ℝ} (hb : F p b) (hc : F p c) (k : ℤ)
    (hs : (2 : ℝ) ^ k / 4 ≤ |(twoSum p b c).1|) (hle : |ℓ + (twoSum p b c).2| ≤ (2 : ℝ) ^ k * u p)
    (hX : (2 : ℝ) ^ k / 4 ≤ |b + ℓ + c|) : PlusFPGood p b ℓ c := by
  have hu := u_pos p
  have hu8 := u_le_eighth p hp
  have hK : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hε := RN_grid p (k - p) (z := ℓ + (twoSum p b c).2) (by rw [two_zpow_sub_p]; exact hle)
  rw [two_zpow_sub_p] at hε
  have hv : |RN p (ℓ + (twoSum p b c).2)| ≤ |(twoSum p b c).1| := by
    have h1 := abs_add_le (RN p (ℓ + (twoSum p b c).2) - (ℓ + (twoSum p b c).2)) (ℓ + (twoSum p b c).2)
    rw [sub_add_cancel] at h1
    have h2 : u p * u p / 2 + u p ≤ 1 / 4 := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left h2 hK.le
    linarith
  obtain ⟨he, hdw⟩ := dwPlusFP_of_le p (by omega) hb hc hv
  unfold PlusFPGood
  refine ⟨hdw, ?_⟩
  rw [he]
  calc |RN p (ℓ + (twoSum p b c).2) - (ℓ + (twoSum p b c).2)| ≤ (2 : ℝ) ^ k * u p * u p / 2 := hε
    _ = 2 * u p ^ 2 * ((2 : ℝ) ^ k / 4) := by ring
    _ ≤ 2 * u p ^ 2 * |b + ℓ + c| := mul_le_mul_of_nonneg_left hX (by positivity)

/-- a float above `-1/2` is at least `-(1/2 - u/2)` -/
theorem ge_of_neg_half_lt (hp : 3 ≤ p) {c : ℝ} (hc : F p c) (h : -(1 / 2) < c) : -(1 / 2 - u p / 2) ≤ c := by
  have hu8 := u_le_eighth p hp
  rcases le_or_gt (-(1 / 4)) c with hq | hq
  · linarith
  · have hmc : Mult (-1 - p) (-c) := mult_of_F p (F_neg p hc) (by
      rw [show (-1 - p + p - 1 : ℤ) = -2 by ring, abs_of_pos (by linarith)]
      norm_num
      linarith)
    have hmh : Mult (-1 - p) (1 / 2 : ℝ) := by
      have := Mult.zpow (E := -1 - p) (e := -1) (by omega)
      rwa [show ((2 : ℝ) ^ (-1 : ℤ)) = 1 / 2 by norm_num] at this
    have := Mult.le_sub hmc hmh (by linarith)
    rw [two_zpow_sub_p, show ((2 : ℝ) ^ (-1 : ℤ)) = 1 / 2 by norm_num] at this
    linarith

/-- Theorem 2.2 of JMP17 on normalized operands: `b ∈ [1, 2)`, `|c| ≤ b`, `|ℓ| ≤ u`, and `ℓ ≥ -u/2` where `b = 1`
and `|c| ≤ 1/2`. For `c ≤ -b/2` the sum `b + c` is exact (Sterbenz) and zero or at least `u`; otherwise
`s_h ≥ 1/2`, with `|s_ℓ| ≤ u` and `x + y ≥ 1/2` for `b + c ≤ 2`, and `|s_ℓ| ≤ 2u` and `x + y ≥ 1` above -/
theorem dwPlusFP_norm (hp : 3 ≤ p) {b ℓ c : ℝ} (hb : F p b) (hc : F p c) (hℓ : F p ℓ) (h1 : 1 ≤ b) (h2 : b < 2)
    (hcb : |c| ≤ b) (hl : |ℓ| ≤ u p) (hl2 : b = 1 → |c| ≤ 1 / 2 → -(u p / 2) ≤ ℓ) : PlusFPGood p b ℓ c := by
  have hu := u_pos p
  have hu8 := u_le_eighth p hp
  have hp1 : 1 < p := by omega
  obtain ⟨hc1, hc2⟩ := abs_le.mp hcb
  obtain ⟨hl1, hl3⟩ := abs_le.mp hl
  rcases le_or_gt c (-(b / 2)) with hS | hS
  · rcases eq_or_lt_of_le hc1 with h0 | h0
    · -- `c = -b`
      rw [← h0]
      unfold PlusFPGood
      rw [dwPlusFP_cancel p hp1 hb hℓ]
      refine ⟨DW.of_F p hℓ, ?_⟩
      rw [show dwVal (ℓ, 0) - (b + ℓ + -b) = 0 by unfold dwVal; ring, abs_zero]
      positivity
    · -- `-b < c ≤ -b/2`: `b + c` is a float, and a positive multiple of `u`
      have hs : F p (b + c) := by
        have := F_sub_of_near p hb (F_neg p hc) (by
          rw [abs_of_pos (by linarith : (0 : ℝ) < b), abs_le]
          constructor <;> linarith)
        rwa [sub_neg_eq_add] at this
      have hmb : Mult (-p) b := (mult_of_one_le p hb h1).mono (by omega)
      have hmc : Mult (-p) c := mult_of_F p hc (by
        rw [show (-p + p - 1 : ℤ) = -1 by ring, abs_of_neg (by linarith)]
        norm_num
        linarith)
      have hge : u p ≤ b + c := by
        have := Mult.le_sub (E := -p) ⟨0, by simp⟩ (hmb.add hmc) (by linarith : (0 : ℝ) < b + c)
        have e : (2 : ℝ) ^ (-p) = u p := rfl
        rw [e] at this
        linarith
      exact dwPlusFP_exact p hp1 hb hc hℓ hs (by rw [abs_of_pos (by linarith : (0 : ℝ) < b + c)]; linarith)
  · have hts := twoSum_add p hp1 hb hc
    have hs1 : (twoSum p b c).1 = RN p (b + c) := rfl
    have he : (twoSum p b c).2 = -(RN p (b + c) - (b + c)) := by rw [← hs1]; linarith
    have e4 : (2 : ℝ) ^ (2 : ℤ) = 4 := by norm_num
    rcases le_or_gt (b + c) 2 with hle | hgt
    · -- `1/2 < b + c ≤ 2`
      have hX : 1 / 2 ≤ b + ℓ + c := by
        rcases eq_or_lt_of_le h1 with hb1 | hb1
        · rcases le_or_gt |c| (1 / 2) with hch | hch
          · have hlo := hl2 hb1.symm hch
            have hcge := ge_of_neg_half_lt p hp hc (by linarith)
            linarith
          · have : 1 / 2 < c := by
              rcases abs_cases c with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
            linarith
        · -- `b ≥ 1 + 2u`
          have hm1 : Mult (1 - p) (1 : ℝ) := by
            have := Mult.zpow (E := 1 - p) (e := 0) (by omega)
            rwa [zpow_zero] at this
          have := Mult.le_sub hm1 (mult_of_one_le p hb h1) hb1
          rw [two_zpow_sub_p, zpow_one] at this
          linarith
      refine dwPlusFP_reg p hp hb hc 1 ?_ ?_ ?_
      · have := RN_mono p (by linarith : (1 / 2 : ℝ) ≤ b + c)
        have hF : F p (1 / 2 : ℝ) := by
          have h := F_two_zpow p (-1)
          rwa [zpow_neg, zpow_one, ← one_div] at h
        rw [RN_of_F p hF] at this
        rw [hs1, abs_of_pos (by linarith), zpow_one]
        linarith
      · have hg := RN_grid p 1 (z := b + c) (by rw [zpow_one, abs_of_pos (by linarith)]; exact hle)
        rw [zpow_one] at hg ⊢
        rw [he]
        have := abs_add_le ℓ (-(RN p (b + c) - (b + c)))
        rw [abs_neg] at this
        linarith
      · rw [zpow_one, abs_of_pos (by linarith)]
        linarith
    · -- `2 < b + c < 4`
      have h2F : RN p 2 = 2 := RN_of_F p (by have := F_two_zpow p 1; rwa [zpow_one] at this)
      refine dwPlusFP_reg p hp hb hc 2 ?_ ?_ ?_
      · have := RN_mono p hgt.le
        rw [h2F] at this
        rw [hs1, abs_of_pos (by linarith), e4]
        linarith
      · have hg := RN_grid p 2 (z := b + c) (by rw [e4, abs_of_pos (by linarith)]; linarith)
        rw [e4] at hg ⊢
        rw [he]
        have := abs_add_le ℓ (-(RN p (b + c) - (b + c)))
        rw [abs_neg] at this
        linarith
      · rw [e4, abs_of_pos (by linarith)]
        linarith

/-- Theorem 2.2 of JMP17 for a positive `b ≥ |c|`, where `(b, ℓ)` or `(c, ℓ)` is a double word: `b` scaled into
`[1, 2)` -/
theorem dwPlusFP_pos (hp : 3 ≤ p) {b ℓ c : ℝ} (hb : F p b) (hc : F p c) (hℓ : F p ℓ) (hb0 : 0 < b) (hcb : |c| ≤ b)
    (hdw : RN p (b + ℓ) = b ∨ RN p (c + ℓ) = c) : PlusFPGood p b ℓ c := by
  have hu := u_pos p
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hb0 (by norm_num : (1 : ℝ) < 2)
  have ha : (0 : ℝ) < (2 : ℝ) ^ (-n) := by positivity
  have s1 : (2 : ℝ) ^ (-n) * (2 : ℝ) ^ n = 1 := by rw [← zpow_add₀ two_ne_zero, neg_add_cancel, zpow_zero]
  have s2 : (2 : ℝ) ^ (-n) * (2 : ℝ) ^ (n + 1) = 2 := by
    rw [← zpow_add₀ two_ne_zero, show -n + (n + 1) = 1 by ring, zpow_one]
  have h1 : 1 ≤ (2 : ℝ) ^ (-n) * b := by
    have := mul_le_mul_of_nonneg_left hn1 ha.le
    rwa [s1] at this
  have h2 : (2 : ℝ) ^ (-n) * b < 2 := by
    have := mul_lt_mul_of_pos_left hn2 ha
    rwa [s2] at this
  have hcb' : |(2 : ℝ) ^ (-n) * c| ≤ (2 : ℝ) ^ (-n) * b := by
    rw [abs_mul, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left hcb ha.le
  have hdw' : RN p ((2 : ℝ) ^ (-n) * b + (2 : ℝ) ^ (-n) * ℓ) = (2 : ℝ) ^ (-n) * b ∨
      RN p ((2 : ℝ) ^ (-n) * c + (2 : ℝ) ^ (-n) * ℓ) = (2 : ℝ) ^ (-n) * c := by
    rcases hdw with h | h
    · left; rw [← mul_add, RN_zpow_mul, h]
    · right; rw [← mul_add, RN_zpow_mul, h]
  refine PlusFPGood.of_scale p (-n) (dwPlusFP_norm p hp (F_zpow_mul p (-n) hb) (F_zpow_mul p (-n) hc)
    (F_zpow_mul p (-n) hℓ) h1 h2 hcb' ?_ ?_)
  · rcases hdw' with h | h
    · exact dw_lo_le_of_lt_two p h (by rw [abs_of_pos (by linarith)]; exact h2)
    · exact dw_lo_le_of_lt_two p h (lt_of_le_of_lt hcb' h2)
  · intro hb1 hc12
    rcases hdw' with h | h
    · rw [hb1] at h
      exact dw_lo_ge_of_one p (by omega) h
    · have h3 := (dw_lo_le_u p h).trans (mul_le_mul_of_nonneg_left hc12 hu.le)
      linarith [(abs_le.mp h3).1]

/-- Theorem 2.2 of JMP17 for floats `b ≠ 0` and `c` with `|c| ≤ |b|`, where `(b, ℓ)` or `(c, ℓ)` is a double word -/
theorem dwPlusFP_gen (hp : 3 ≤ p) {b ℓ c : ℝ} (hb : F p b) (hc : F p c) (hℓ : F p ℓ) (hb0 : b ≠ 0)
    (hcb : |c| ≤ |b|) (hdw : RN p (b + ℓ) = b ∨ RN p (c + ℓ) = c) : PlusFPGood p b ℓ c := by
  rcases lt_or_gt_of_ne hb0 with h | h
  · refine PlusFPGood.of_neg p (dwPlusFP_pos p hp (F_neg p hb) (F_neg p hc) (F_neg p hℓ) (by linarith) ?_ ?_)
    · rw [abs_neg]
      rwa [abs_of_neg h] at hcb
    · rcases hdw with h' | h'
      · left; rw [← neg_add, RN_neg, h']
      · right; rw [← neg_add, RN_neg, h']
  · exact dwPlusFP_pos p hp hb hc hℓ h (by rwa [abs_of_pos h] at hcb) hdw

/-- Theorem 2.2 of JMP17, with its result a double word: for `p ≥ 3`, a double word `x` and a float `y`,
`DWPlusFP(x, y)` is a double word within `2u²` of `x + y`, relatively -/
theorem dwPlusFP_good (hp : 3 ≤ p) {x : ℝ × ℝ} (hx : DW p x) {y : ℝ} (hy : F p y) :
    DW p (dwPlusFP p x y) ∧ |dwVal (dwPlusFP p x y) - (dwVal x + y)| ≤ 2 * u p ^ 2 * |dwVal x + y| := by
  obtain ⟨xh, xl⟩ := x
  obtain ⟨hxh, hxl, hdw⟩ := hx
  have hxh' : F p xh := hxh
  have hxl' : F p xl := hxl
  have hdw' : RN p (xh + xl) = xh := hdw
  show PlusFPGood p xh xl y
  rcases le_or_gt |y| |xh| with h | h
  · by_cases h0 : xh = 0
    · -- `x = 0` and `y = 0`
      have hy0 : y = 0 := by
        rw [h0, abs_zero] at h
        exact abs_eq_zero.mp (le_antisymm h (abs_nonneg y))
      have hl0 : xl = 0 := RN_eq_zero p (by rw [h0, zero_add] at hdw'; exact hdw')
      have hz := dwPlusFP_cancel p (by omega) (F_zero p) (F_zero p)
      rw [neg_zero] at hz
      unfold PlusFPGood
      rw [h0, hy0, hl0, hz]
      exact ⟨DW.of_F p (F_zero p), by simp [dwVal]⟩
    · exact dwPlusFP_gen p hp hxh' hy hxl' h0 h (Or.inl hdw')
  · -- `|x_h| < |y|`: the roles of `x_h` and `y` exchanged
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at h
      exact absurd h (not_lt.mpr (abs_nonneg _))
    have hg := dwPlusFP_gen p hp hy hxh' hxl' hy0 h.le (Or.inr hdw')
    unfold PlusFPGood at hg ⊢
    rw [dwPlusFP_swap p (by omega) hy hxh', show y + xl + xh = xh + xl + y by ring] at hg
    exact hg

/-- Theorem 2.2 of JMP17: for `p ≥ 3`, DWPlusFP of a double word `x` and a float `y` is within `2u²` of `x + y`,
relatively -/
theorem dwPlusFP_err (hp : 3 ≤ p) {x : ℝ × ℝ} (hx : DW p x) {y : ℝ} (hy : F p y) :
    |dwVal (dwPlusFP p x y) - (dwVal x + y)| ≤ 2 * u p ^ 2 * |dwVal x + y| := (dwPlusFP_good p hp hx hy).2

/-- the result of DWPlusFP is a double word: its last FastTwoSum is exact -/
theorem dwPlusFP_dw (hp : 3 ≤ p) {x : ℝ × ℝ} (hx : DW p x) {y : ℝ} (hy : F p y) : DW p (dwPlusFP p x y) :=
  (dwPlusFP_good p hp hx hy).1

end ExpansionBounds
