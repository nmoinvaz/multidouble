import ExpansionBounds.Exp8.All
import ExpansionBounds.Trig8

/-!
# Theorem 40 (`thm:exp`) at `n = 8` and `p = 53`

`EXP_{8,6,43}` with multidouble's constants: for `x` in `F` on `H(2)` with `|x_0| ≤ 745.2`, the result is within
`3.661u^8 e^x + 8·2^{-1074}` of `e^x`. The scalings round below `2^{-1022}` as binary64 does. The model has no largest
finite value, so nothing overflows: the bound is the paper's, which takes a finite result. A run falls in a group of exponents `e` of step (2), which share `m` and the
degree `d'`, and in an interval `[a, b]` of `|r|`; the kernel checked the bound of each (`Exp8/Run0.lean` to
`Run11.lean`), and `expEps_cert` carries it to the paper's `ε`.
-/

namespace ExpansionBounds

open Finset

/-- the constants of `Exp8/Data.lean` are bounds of what they stand for, and `e ≥ -1` selects no `|r|` -/
theorem exp8_consts : red8RMax ≤ dyQ exp8RMaxS ∧ red8Delta red8RMax ≤ dyQ exp8DeltaS ∧
    dyQ exp8RMaxS + dyQ exp8DeltaS ≤ dyQ exp8Top1 ∧ 1 / (2 * cr8 * (1 - 2 * red8U)) ≤ dyQ exp8Top0 ∧
    ∑ i ∈ Ico 1 8, abarQ (2 * red8U) i * dyQ exp8Top0 ≤ dyQ exp8Tail0 ∧
    ∑ i ∈ Ico 1 8, red8Pi red8RMax i ≤ dyQ exp8Tail1 ∧ 0 ≤ dyQ exp8DeltaS ∧ 0 < cr8 ∧
    (∀ k0 : Bool, exp8Top k0 < (2 : ℚ) ^ (-1 : ℤ) * (1 - 1 / 2 ^ 46) - 2 * exp8Tail k0) ∧
    (1 + red8U) ^ 8 ≤ 1 + 1 / 2 ^ 48 ∧ 1 - 1 / 2 ^ 46 ≤ 1 / ((1 + red8U) ^ 8 * (1 + 1 / 2 ^ 48)) := by
  decide +kernel

/-- the groups of `k = 0` or of `k ≠ 0`, but the last -/
def exp8Grp (k0 : Bool) : List (ℕ × ℕ × ℤ × ℤ × (ℤ × ℕ) × (ℤ × ℕ)) := if k0 then exp8Grp0 else exp8Grp1

/-- the last group -/
def exp8Last (k0 : Bool) : ℕ × ℕ × ℤ × ℤ × (ℤ × ℕ) × (ℤ × ℕ) := if k0 then exp8Last0 else exp8Last1

/-- a group's exponents have its `m` and its degree, which is at least 1, and select `|r|` in `[lo, hi]` -/
def Exp8GrpOk (k0 : Bool) (g : ℕ × ℕ × ℤ × ℤ × (ℤ × ℕ) × (ℤ × ℕ)) : Prop :=
  (∀ e : ℤ, g.2.2.1 ≤ e → e ≤ g.2.2.2.1 → g.1 = (e + 7).toNat ∧ g.2.1 = exp8Deg (e - g.1)) ∧ 1 ≤ g.2.1 ∧
    dyQ g.2.2.2.2.1 ≤ max 0 ((2 : ℚ) ^ g.2.2.1 * (1 - 1 / 2 ^ 46) - 2 * exp8Tail k0) ∧
    dyQ g.2.2.2.2.2 = min (exp8Top k0) ((2 : ℚ) ^ (g.2.2.2.1 + 1))

instance (k0 : Bool) (g : ℕ × ℕ × ℤ × ℤ × (ℤ × ℕ) × (ℤ × ℕ)) : Decidable (Exp8GrpOk k0 g) := by
  unfold Exp8GrpOk
  infer_instance

set_option maxHeartbeats 4000000 in
/-- the groups cover the exponents `-436 ≤ e ≤ -2`, and the last is every `e ≤ -437` -/
theorem exp8_grps : ∀ k0 : Bool, (∀ g ∈ exp8Grp k0, Exp8GrpOk k0 g) ∧
    (∀ e : ℤ, -436 ≤ e → e ≤ -2 → ∃ g ∈ exp8Grp k0, g.2.2.1 ≤ e ∧ e ≤ g.2.2.2.1) ∧
    (exp8Last k0).1 = 0 ∧ (exp8Last k0).2.1 = 1 ∧ (exp8Last k0).2.2.2.1 = -437 ∧ dyQ (exp8Last k0).2.2.2.2.1 = 0 ∧
    dyQ (exp8Last k0).2.2.2.2.2 = min (exp8Top k0) ((2 : ℚ) ^ (-436 : ℤ)) := by
  decide +kernel

/-- multidouble's table: at most eight parts to a coefficient, each in `F` -/
theorem exp8_table : (∀ t ∈ exp8Fact, t.length ≤ 8) ∧ ∀ t ∈ exp8Fact, ∀ q ∈ t, rnQ 53 (dyQ q) = dyQ q := by
  decide +kernel

theorem exp8_all (k0 : Bool) : (∀ g ∈ exp8Grp k0, Exp8Group k0 g) ∧ Exp8Group k0 (exp8Last k0) := by
  cases k0
  · exact ⟨exp8_all1, exp8_last1⟩
  · exact ⟨exp8_all0, exp8_last0⟩

theorem exp8Deg_small {e : ℤ} (he : e ≤ -437) : exp8Deg e = 1 := by
  rcases lt_or_eq_of_le he with h | h
  · simp [exp8Deg, h]
  · subst h
    decide

variable (p : ℤ) [Prec_gt_0 p]

/-- step (1)'s `r` with multidouble's constants -/
noncomputable def exp8R (x : ℕ → ℝ) : ℕ → ℝ := expR p 8 x ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ))

/-- `|RN(z)| < 1/2` only if `|z| < 1/2` -/
theorem abs_lt_half_of_RN {z : ℝ} (h : |RN p z| < 1 / 2) : |z| < 1 / 2 := by
  have hF := F_half p
  have h1 : RN p (1 / 2) = 1 / 2 := RN_of_F p hF
  have h2 : RN p (-(1 / 2)) = -(1 / 2) := RN_of_F p (F_neg p hF)
  obtain ⟨ha, hb⟩ := abs_lt.mp h
  rw [abs_lt]
  constructor
  · by_contra hc
    have := RN_mono p (not_lt.mp hc)
    rw [h2] at this
    linarith
  · by_contra hc
    have := RN_mono p (not_lt.mp hc)
    rw [h1] at this
    linarith

/-- the facts of a run that the cases use: the parts of `r` are in `F`, `r` is within `δ` of `r_e`, `|r|` and the
sum of its lower parts are bounded, and its parts are bounded from a bound of `|r|` -/
theorem exp8_run (hp : p = 53) (x : ℕ → ℝ) (hx : ∀ i < 8, F p (x i)) (hH : Htheta p 8 2 x)
    (hx0 : |x 0| ≤ 7452 / 10) :
    ∃ k0 : Bool, (∀ i < 8, F p (exp8R p x i)) ∧
      |∑ i ∈ range 8, exp8R p x i - (∑ i ∈ range 8, x i - expK p (x 0) * Real.log 2)| ≤
        ((exp8Delta k0 : ℚ) : ℝ) ∧
      |∑ i ∈ range 8, exp8R p x i| ≤ ((exp8Top k0 : ℚ) : ℝ) ∧
      ∑ i ∈ Ico 1 8, |exp8R p x i| ≤ ((exp8Tail k0 : ℚ) : ℝ) ∧
      ∀ hi : ℚ, |∑ i ∈ range 8, exp8R p x i| ≤ ((hi : ℚ) : ℝ) →
        ∀ i < 8, |exp8R p x i| ≤ ((exp8Pi k0 hi i : ℚ) : ℝ) := by
  have hu : ((red8U : ℚ) : ℝ) = u p := by unfold red8U; exact u_53_rat p hp
  have hu53 : u p = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  have hup := u_pos p
  have hp1 : 1 < p := by omega
  have hA3 : (((8 : ℕ) : ℝ) ^ 2 + (8 : ℕ)) * u p < 1 := by rw [hu53]; norm_num
  obtain ⟨cR1, cD1, cT1, cT0, cTl0, cTl1, cD0, ccr, -, -, -⟩ := exp8_consts
  obtain ⟨a1, a2, a3⟩ := lemma38_8 p hp x hx hH hx0
  by_cases hk0 : expK p (x 0) = 0
  · -- `k = 0`: `r = x`
    refine ⟨true, ?_⟩
    have hrx : exp8R p x = x := by
      unfold exp8R expR
      simp only [hk0, ↓reduceIte]
    rw [hrx]
    have hρ : (2 : ℝ) * (2 * u p) < 1 := by rw [hu53]; norm_num
    have hρ1 : (2 : ℝ) * u p < 1 := by linarith
    have ht := Htheta_tail p 8 (by norm_num) 2 (by norm_num) hρ1 x hH
    have ha0 := Htheta_a0 p 8 (by norm_num) 2 (by norm_num) hρ x hH
    obtain ⟨X, hX⟩ : ∃ X, X = ∑ i ∈ range 8, x i := ⟨_, rfl⟩
    rw [← hX] at ht ha0 ⊢
    -- `|x_0| c_r < 1/2`
    have hc : |x 0| * ((cr8 : ℚ) : ℝ) < 1 / 2 := by
      have h1 := abs_lt_half_of_RN p (roundAway_eq_zero hk0)
      rw [cR_eq p hp, abs_mul, abs_of_pos (by exact_mod_cast ccr : (0 : ℝ) < ((cr8 : ℚ) : ℝ))] at h1
      exact h1
    have hcr : (0 : ℝ) < ((cr8 : ℚ) : ℝ) := by exact_mod_cast ccr
    have hx0b : |x 0| < 1 / (2 * ((cr8 : ℚ) : ℝ)) := by
      rw [lt_div_iff₀ (by positivity)]
      linarith
    -- `|x| ≤ |x_0|/(1 - 2u)`
    have hXb : |X| ≤ ((exp8Top true : ℚ) : ℝ) := by
      have h1 : |X| ≤ |x 0| + |X - x 0| := by
        have := abs_add_le (x 0) (X - x 0)
        rwa [add_sub_cancel] at this
      have hne : (1 : ℝ) - 2 * u p ≠ 0 := ne_of_gt (by linarith)
      have h2 : |x 0| + 2 * u p / (1 - 2 * u p) * |x 0| = |x 0| / (1 - 2 * u p) := by
        field_simp
        ring
      have h3 : |x 0| / (1 - 2 * u p) ≤ 1 / (2 * ((cr8 : ℚ) : ℝ)) / (1 - 2 * u p) :=
        div_le_div_of_nonneg_right hx0b.le (by linarith)
      have h4 : (1 : ℝ) / (2 * ((cr8 : ℚ) : ℝ)) / (1 - 2 * u p) = ((1 / (2 * cr8 * (1 - 2 * red8U)) : ℚ) : ℝ) := by
        rw [div_div]
        push_cast
        rw [hu]
      have h5 : ((1 / (2 * cr8 * (1 - 2 * red8U)) : ℚ) : ℝ) ≤ ((exp8Top true : ℚ) : ℝ) := by
        simp only [exp8Top, ↓reduceIte]
        exact Rat.cast_le.mpr cT0
      linarith
    -- the parts on `H(2)`
    have hpart : ∀ i < 8, |x i| ≤ ((abarQ (2 * red8U) i : ℚ) : ℝ) * |X| := fun i hi => by
      have h1 := Htheta_le p 8 hH i hi
      have h2 : ((abarQ (2 * red8U) i : ℚ) : ℝ) = (2 * u p) ^ i * ((1 - 2 * u p) / (1 - 2 * (2 * u p))) := by
        simp only [abarQ]
        push_cast
        rw [hu]
      rw [h2, mul_assoc]
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact ha0
    have hab0 : ∀ i, (0 : ℝ) ≤ ((abarQ (2 * red8U) i : ℚ) : ℝ) := fun i => by
      have : (0 : ℚ) ≤ abarQ (2 * red8U) i := by
        unfold abarQ red8U
        exact mul_nonneg (pow_nonneg (by norm_num) i) (by norm_num)
      exact_mod_cast this
    refine ⟨hx, ?_, hXb, ?_, fun hi hhi i hi8 => ?_⟩
    · simp [hk0, exp8Delta]
    · have h1 : ∑ i ∈ Ico 1 8, |x i| ≤ ∑ i ∈ Ico 1 8, ((abarQ (2 * red8U) i : ℚ) : ℝ) * ((exp8Top true : ℚ) : ℝ) :=
        sum_le_sum fun i hi => (hpart i (mem_Ico.mp hi).2).trans
          (mul_le_mul_of_nonneg_left hXb (hab0 i))
      have h2 : ∑ i ∈ Ico 1 8, ((abarQ (2 * red8U) i : ℚ) : ℝ) * ((exp8Top true : ℚ) : ℝ) =
          ((∑ i ∈ Ico 1 8, abarQ (2 * red8U) i * dyQ exp8Top0 : ℚ) : ℝ) := by
        simp only [exp8Top, ↓reduceIte]
        push_cast
        rfl
      have h3 : ((∑ i ∈ Ico 1 8, abarQ (2 * red8U) i * dyQ exp8Top0 : ℚ) : ℝ) ≤ ((exp8Tail true : ℚ) : ℝ) := by
        simp only [exp8Tail, ↓reduceIte]
        exact Rat.cast_le.mpr cTl0
      linarith
    · simp only [exp8Pi, ↓reduceIte]
      push_cast
      exact (hpart i hi8).trans (mul_le_mul_of_nonneg_left hhi (hab0 i))
  · -- `k ≠ 0`: Lemma 38 (b)
    refine ⟨false, ?_⟩
    obtain ⟨hF0, hb⟩ := a3 hk0
    obtain ⟨c1, c2⟩ := hb red8RMax a2
    obtain ⟨R, hR⟩ : ∃ R, R = ∑ i ∈ range 8, exp8R p x i := ⟨_, rfl⟩
    obtain ⟨re, hre⟩ : ∃ re, re = ∑ i ∈ range 8, x i - expK p (x 0) * Real.log 2 := ⟨_, rfl⟩
    have hRd : R = ∑ i ∈ range 8, expR p 8 x ((ch8 : ℚ) : ℝ) (fun i => ((cl8 i : ℚ) : ℝ)) i := hR
    rw [← hRd, ← hre] at c1
    rw [← hre] at a2 hb
    rw [← hR, ← hre]
    have hδs : ((red8Delta red8RMax : ℚ) : ℝ) ≤ ((dyQ exp8DeltaS : ℚ) : ℝ) := Rat.cast_le.mpr cD1
    have hD0 : (0 : ℝ) ≤ ((dyQ exp8DeltaS : ℚ) : ℝ) := by exact_mod_cast cD0
    have hRre : |R - re| ≤ ((dyQ exp8DeltaS : ℚ) : ℝ) := c1.trans hδs
    have hreR : ∀ {t : ℝ}, |R| ≤ t → |re| ≤ t + ((dyQ exp8DeltaS : ℚ) : ℝ) := fun {t} ht => by
      have := abs_sub_abs_le_abs_sub re R
      rw [abs_sub_comm re R] at this
      linarith
    -- the parts of `r` are in `F`
    have hrF : ∀ i < 8, F p (exp8R p x i) := by
      intro i _
      obtain ⟨k, hkd⟩ : ∃ k, k = expK p (x 0) := ⟨_, rfl⟩
      rw [← hkd] at hk0 a1 hF0
      have hkb' : |(k : ℝ)| ≤ 1075 := by rw [← Int.cast_abs]; exact_mod_cast a1
      have hkF : F p (-(k : ℝ)) := by
        refine F_of_mult p (E := 0) ⟨-k, by push_cast; ring⟩ ?_
        rw [abs_neg, zero_add, hp]
        calc |(k : ℝ)| ≤ 1075 := hkb'
          _ < (2 : ℝ) ^ (53 : ℤ) := by norm_num
      obtain ⟨-, -, m3, -⟩ := mulf_G p 8 hp1 (by norm_num) hA3 (fun i => ((cl8 i : ℚ) : ℝ)) (-(k : ℝ))
        (fun i => |((cl8 i : ℚ) : ℝ)|) |(-(k : ℝ))| (fun i _ => cl8_F p hp i) hkF (fun _ _ => le_rfl) le_rfl _
        le_rfl
      have hxF : ∀ i < 8, F p (xRed p x ((ch8 : ℚ) : ℝ) i) := fun i hi => by
        unfold xRed
        split_ifs with h0
        · rw [← hkd]; exact hF0
        · exact hx i hi
      have := F_addOp p 8 hp1 (by norm_num) hA3 (xRed p x ((ch8 : ℚ) : ℝ))
        (pt (mulfOp p 8 (fun i => ((cl8 i : ℚ) : ℝ)) (-(k : ℝ)))) hxF (fun j _ => m3 j) i
      unfold exp8R expR
      rw [← hkd]
      simp only [hk0, ↓reduceIte]
      exact this
    have hRtop : |R| ≤ ((exp8Top false : ℚ) : ℝ) := by
      have h1 := abs_sub_abs_le_abs_sub R re
      have h2 : ((red8RMax : ℚ) : ℝ) ≤ ((dyQ exp8RMaxS : ℚ) : ℝ) := Rat.cast_le.mpr cR1
      have h3 : ((dyQ exp8RMaxS + dyQ exp8DeltaS : ℚ) : ℝ) ≤ ((dyQ exp8Top1 : ℚ) : ℝ) := Rat.cast_le.mpr cT1
      simp only [exp8Top, Bool.false_eq_true, ↓reduceIte]
      push_cast at h3
      linarith
    refine ⟨hrF, ?_, hRtop, ?_, fun hi hhi i _ => ?_⟩
    · simpa [exp8Delta] using hRre
    · have h1 : ∑ i ∈ Ico 1 8, |exp8R p x i| ≤ ∑ i ∈ Ico 1 8, ((red8Pi red8RMax i : ℚ) : ℝ) :=
        sum_le_sum fun i _ => c2 i
      have h2 : ((∑ i ∈ Ico 1 8, red8Pi red8RMax i : ℚ) : ℝ) ≤ ((exp8Tail false : ℚ) : ℝ) := by
        simp only [exp8Tail, Bool.false_eq_true, ↓reduceIte]
        exact Rat.cast_le.mpr cTl1
      push_cast at h2
      linarith
    · obtain ⟨-, d2⟩ := hb (hi + dyQ exp8DeltaS) (by push_cast; exact hreR hhi)
      simp only [exp8Pi, Bool.false_eq_true, ↓reduceIte]
      exact d2 i

/-- the parts of `F_k` over `ℝ` -/
noncomputable def exp8FR (k i : ℕ) : ℝ := ((exp8F k i : ℚ) : ℝ)

omit [Prec_gt_0 p] in
theorem cast_exp8Eta : ((exp8Eta : ℚ) : ℝ) = (2 : ℝ) ^ (-1075 : ℤ) := by
  unfold exp8Eta
  rw [show (-1075 : ℤ) = -((1075 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast, ← one_div]
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat]

omit [Prec_gt_0 p] in
theorem cast_exp8Eta1 (m : ℕ) : ((exp8Eta1 m : ℚ) : ℝ) = eta0m m := by
  unfold exp8Eta1 eta0m
  split_ifs
  · exact Rat.cast_zero
  · exact cast_exp8Eta

omit [Prec_gt_0 p] in
theorem exp8Pi_nonneg (k0 : Bool) {hi : ℚ} (hhi : 0 ≤ hi) (i : ℕ) : 0 ≤ exp8Pi k0 hi i := by
  obtain ⟨-, -, -, -, -, -, cD0, -, -, -, -⟩ := exp8_consts
  cases k0 with
  | true =>
    simp only [exp8Pi, ↓reduceIte]
    refine mul_nonneg ?_ hhi
    unfold abarQ red8U
    exact mul_nonneg (pow_nonneg (by norm_num) i) (by norm_num)
  | false =>
    simp only [exp8Pi, Bool.false_eq_true, ↓reduceIte]
    have hu : ((red8U : ℚ) : ℝ) = u (53 : ℤ) := by unfold red8U; exact u_53_rat 53 rfl
    have hu53 : u (53 : ℤ) = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
    have hA3 : (((8 : ℕ) : ℝ) ^ 2 + (8 : ℕ)) * u (53 : ℤ) < 1 := by rw [hu53]; norm_num
    obtain ⟨kA, kA0, -, kE⟩ := red8_check
    -- `α`, `μ` and `Z̄` are nonnegative, so `G_ADD`'s part bounds are
    have hα0 : ∀ i, (0 : ℝ) ≤ ((red8Alpha i : ℚ) : ℝ) := fun i => by
      have : (0 : ℚ) ≤ red8Alpha i := by
        unfold red8Alpha
        split_ifs
        · have h1 : (0 : ℚ) ≤ red8RMax := by
            unfold red8RMax red8Xt red8X red8U
            have := mul_nonneg (add_nonneg (by norm_num : (0 : ℚ) ≤ 1 / 2) kE) kA.le
            have h2 : ln2A ≤ ln2B := by decide +kernel
            nlinarith [mul_nonneg (add_nonneg (by norm_num : (0 : ℚ) ≤ 1 / 2) kE) (kA.le.trans h2)]
          unfold red8A0
          have h3 : (0 : ℚ) ≤ red8Xt := by unfold red8Xt red8X red8U; norm_num
          have : (0 : ℚ) ≤ max |ch8 - ln2A| |ch8 - ln2B| := le_max_of_le_left (abs_nonneg _)
          linarith
        · unfold red8X red8U
          positivity
      exact_mod_cast this
    have hcl0 : ∀ m, (0 : ℝ) ≤ (fun m => |((cl8 m : ℚ) : ℝ)| * 1075) m := fun m => by positivity
    have hX := pairX_nonneg (53 : ℤ) 8 hA3 (lam := fun m => |((cl8 m : ℚ) : ℝ)| * 1075) hcl0
    have hR : 0 ≤ pairR (53 : ℤ) 8 (fun m => |((cl8 m : ℚ) : ℝ)| * 1075) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (u_pos 53).le) (hX 8)
    have hμ0 : ∀ j, (0 : ℝ) ≤ ((red8Mu j : ℚ) : ℝ) := fun j => by
      unfold red8Mu
      rw [cast_GmulfP 53 8 hu]
      exact gParts_nonneg 53 8 (by simpa using hX) (by positivity) (by simpa using hR) j
    have hE10 : (0 : ℝ) ≤ ((red8E1 : ℚ) : ℝ) := by
      unfold red8E1
      rw [cast_GmulfE 53 8 hu]
      exact gErr_nonneg 53 8 (by simpa using hX) (by positivity) (by simpa using hR)
    have hEta0 : (0 : ℚ) ≤ red8Eta := by
      unfold red8Eta
      exact le_max_of_le_left (abs_nonneg _)
    have hZ0 : (0 : ℝ) ≤ ((red8Z (hi + dyQ exp8DeltaS) : ℚ) : ℝ) := by
      unfold red8Z
      push_cast
      have h1 : (0 : ℝ) ≤ ((hi : ℚ) : ℝ) := by exact_mod_cast hhi
      have h2 : (0 : ℝ) ≤ ((dyQ exp8DeltaS : ℚ) : ℝ) := by exact_mod_cast cD0
      have h3 : (0 : ℝ) ≤ ((red8Eta : ℚ) : ℝ) := by exact_mod_cast hEta0
      linarith
    have hg := (Gadd_nonneg (53 : ℤ) 8 hA3 hα0 hμ0 hZ0).2 i
    unfold red8Pi
    rw [← cast_GaddP 53 8 hu] at hg
    exact_mod_cast hg

/-- Theorem 40 (`thm:exp`) at `n = 8` and `p = 53`, for `EXP_{8,6,43}` with multidouble's constants and binary64's
subnormals, without overflow (the model has no largest finite value, and the paper's theorem takes a finite result):
for `x` in `F` on `H(2)` with `|x_0| ≤ 745.2`, with `e` the exponent of step (2)'s `U` (`-1023` where
`U < 2^{-1022}`), `m = max(0, e + 7)` and the degree `d'` of step (3), the core's scaling of `r' = 2^{-m}r` up by
`2^{m-e}` exact, as in Lemma 33, and the scaling by `2^{-m}`, the scaling back and the last scaling rounded by `S`,
which keeps a value or rounds one below `2^{-1022}` to a multiple of `2^{-1074}`, the last in two steps, `2^{k₁}` then
`2^{k₂}` with `k₂ ≤ 0`: `|y - e^x| ≤ 3.661u^8 e^x + 8·2^{-1074}`. multidouble takes `k₁ = k/2`, rounded toward zero, so
`k₂ > 0` where `k > 0`; both steps then scale up, which binary64 does exactly, and the value is that of the split
`(k, 0)`. For binary64 the run must also meet the paper's (A2′): every product, fused multiply-add and quotient returns
what it would with an unbounded exponent range, as in the model, but those that only select `k` or an exponent, which
the paper exempts -/
theorem thm40_8 (hp : p = 53) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℕ → ℝ) (hx : ∀ i < 8, F p (x i)) (hH : Htheta p 8 2 x) (hx0 : |x 0| ≤ 7452 / 10) (k₁ k₂ : ℤ)
    (hk : k₁ + k₂ = expK p (x 0)) (hk2 : k₂ ≤ 0) (e : ℤ)
    (hsel : ((2 : ℝ) ^ e ≤ expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (exp8R p x) ∧
        expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (exp8R p x) < (2 : ℝ) ^ (e + 1)) ∨
      (expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (exp8R p x) < (2 : ℝ) ^ (-1022 : ℤ) ∧ e = -1023)) :
    |∑ i ∈ range 8, S ((2 : ℝ) ^ k₂ * S ((2 : ℝ) ^ k₁ * (addfOp p 8 (expCore p 8
        (if (e + 7).toNat = 0 then id else S) S e (e + 7).toNat (exp8R p x) exp8FR
        (exp8Deg (e - (e + 7).toNat))) 1).getD i 0)) - Real.exp (∑ i ∈ range 8, x i)| ≤
      3661 / 1000 * u p ^ 8 * Real.exp (∑ i ∈ range 8, x i) + 8 * (2 : ℝ) ^ (-1074 : ℤ) := by
  have hu : ((red8U : ℚ) : ℝ) = u p := by unfold red8U; exact u_53_rat p hp
  have hu53 : u p = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  have hup := u_pos p
  have hA3 : (((8 : ℕ) : ℝ) ^ 2 + (8 : ℕ)) * u p < 1 := by rw [hu53]; norm_num
  obtain ⟨-, -, -, -, -, -, cD0, -, cTop, cγ, cC⟩ := exp8_consts
  obtain ⟨k0, hrF, hδ, hRtop, htail, hparts⟩ := exp8_run p hp x hx hH hx0
  obtain ⟨r, hr⟩ : ∃ r, r = exp8R p x := ⟨_, rfl⟩
  rw [← hr] at hrF hδ hRtop htail hparts hsel ⊢
  obtain ⟨R, hR⟩ : ∃ R, R = ∑ i ∈ range 8, r i := ⟨_, rfl⟩
  rw [← hR] at hδ hRtop hparts
  obtain ⟨X, hX⟩ : ∃ X, X = ∑ i ∈ range 8, x i := ⟨_, rfl⟩
  rw [← hX] at hδ ⊢
  obtain ⟨U, hUd⟩ : ∃ U, U = expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) r := ⟨_, rfl⟩
  rw [← hUd] at hsel
  -- `∑|r_i| ≤ U`, so `∑|r_i| < 2^{e+1}`
  have hγ : (1 + u p) ^ 8 ≤ 1 + (2 : ℝ) ^ (-48 : ℤ) := by
    have h1 := (Rat.cast_le (K := ℝ)).mpr cγ
    push_cast at h1
    rw [hu] at h1
    exact h1.trans_eq (by norm_num)
  have hSU : ∑ i ∈ range 8, |r i| ≤ U := by rw [hUd]; exact expU_ge p 8 (by norm_num) _ hγ r
  have hU : ∑ i ∈ range 8, |r i| < (2 : ℝ) ^ (e + 1) := by
    rcases hsel with ⟨-, h2⟩ | ⟨h2, he⟩
    · exact hSU.trans_lt h2
    · rw [he]
      exact (hSU.trans_lt h2).trans_eq (by norm_num)
  have hRS : |R| ≤ ∑ i ∈ range 8, |r i| := by rw [hR]; exact abs_sum_le_sum_abs _ _
  -- the lower end of the `|r|` that select `e`
  have hlow : (2 : ℝ) ^ e ≤ U → (2 : ℝ) ^ e * (1 - 1 / 2 ^ 46) - 2 * ((exp8Tail k0 : ℚ) : ℝ) ≤ |R| := by
    intro h2
    rw [hUd] at h2
    have h3 := abs_ge_of_expU p 8 (by norm_num) ((2 : ℝ) ^ (-48 : ℤ)) (by positivity) r (fun i => |r i|)
      (fun _ _ => le_rfl) e h2
    rw [← hR] at h3
    have h4 : (1 : ℝ) - 1 / 2 ^ 46 ≤ 1 / ((1 + u p) ^ 8 * (1 + (2 : ℝ) ^ (-48 : ℤ))) := by
      have h1 := (Rat.cast_le (K := ℝ)).mpr cC
      push_cast at h1
      rw [hu] at h1
      exact h1.trans_eq (by norm_num)
    have h5 : (2 : ℝ) ^ e * (1 - 1 / 2 ^ 46) ≤ (2 : ℝ) ^ e / ((1 + u p) ^ 8 * (1 + (2 : ℝ) ^ (-48 : ℤ))) :=
      (mul_le_mul_of_nonneg_left h4 (by positivity)).trans_eq (mul_one_div _ _)
    linarith
  -- `e ≤ -2`
  have he2 : e ≤ -2 := by
    by_contra hcon
    rcases hsel with ⟨h1, -⟩ | ⟨-, he⟩
    · have hl := hlow h1
      have h6 : (2 : ℝ) ^ (-1 : ℤ) ≤ (2 : ℝ) ^ e := zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h7 := (Rat.cast_lt (K := ℝ)).mpr (cTop k0)
      push_cast at h7
      have h8 := mul_le_mul_of_nonneg_right h6 (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2 ^ 46)
      linarith
    · omega
  -- the group of `e`
  obtain ⟨hgAll, hgLast⟩ := exp8_all k0
  obtain ⟨gOk, gCov, gL1, gL2, gL3, gL4, gL5⟩ := exp8_grps k0
  obtain ⟨m, hm⟩ : ∃ m, m = (e + 7).toNat := ⟨_, rfl⟩
  rw [← hm]
  have hR0 : 0 ≤ |R| := abs_nonneg R
  have hcap : ∀ eH : ℤ, e ≤ eH → |R| ≤ (((min (exp8Top k0) ((2 : ℚ) ^ (eH + 1)) : ℚ)) : ℝ) := fun eH heH => by
    push_cast
    exact le_min hRtop ((hRS.trans hU.le).trans (zpow_le_zpow_right₀ (by norm_num) (by omega)))
  obtain ⟨g, hgG, hgm, hgd, hge, hgd1, hglo, hghi⟩ : ∃ g : ℕ × ℕ × ℤ × ℤ × (ℤ × ℕ) × (ℤ × ℕ),
      Exp8Group k0 g ∧ g.1 = m ∧ g.2.1 = exp8Deg (e - m) ∧ e ≤ g.2.2.2.1 ∧ 1 ≤ g.2.1 ∧
        ((dyQ g.2.2.2.2.1 : ℚ) : ℝ) ≤ |R| ∧ |R| ≤ ((dyQ g.2.2.2.2.2 : ℚ) : ℝ) := by
    by_cases he436 : -436 ≤ e
    · obtain ⟨g, hg, hg1, hg2⟩ := gCov e he436 he2
      obtain ⟨o1, o2, o3, o4⟩ := gOk g hg
      obtain ⟨o1a, o1b⟩ := o1 e hg1 hg2
      refine ⟨g, hgAll g hg, by rw [hm]; exact o1a, by rw [hm, ← o1a]; exact o1b, hg2, o2, ?_, ?_⟩
      · have h1 : (2 : ℝ) ^ e ≤ U := by
          rcases hsel with ⟨h1, -⟩ | ⟨-, he⟩
          · exact h1
          · omega
        have hl := hlow h1
        have h3 := (Rat.cast_le (K := ℝ)).mpr o3
        push_cast at h3
        refine h3.trans (max_le hR0 ?_)
        have h6 : (2 : ℝ) ^ g.2.2.1 ≤ (2 : ℝ) ^ e := zpow_le_zpow_right₀ (by norm_num) hg1
        have h8 := mul_le_mul_of_nonneg_right h6 (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2 ^ 46)
        linarith
      · rw [o4]
        exact hcap _ hg2
    · have he437 : e ≤ -437 := by omega
      have hm0 : m = 0 := by rw [hm]; omega
      refine ⟨exp8Last k0, hgLast, by rw [gL1, hm0], ?_, by rw [gL3]; exact he437, by rw [gL2], ?_, ?_⟩
      · rw [gL2, hm0]
        simpa using (exp8Deg_small he437).symm
      · rw [gL4, Rat.cast_zero]
        exact hR0
      · rw [gL5]
        have := hcap (-437) he437
        norm_num at this ⊢
        exact this
  obtain ⟨pq, bpT, sp, sn, bins, hpar, hhp, hhn, hne, hchain, hbins⟩ := hgG
  obtain ⟨d', hd'⟩ : ∃ d', d' = exp8Deg (e - m) := ⟨_, rfl⟩
  rw [← hd'] at hgd ⊢
  -- the interval of `|r|` and the sign of `r`
  obtain ⟨ab, hab, hab1, hab2⟩ := exp8Chain_cover _ _ _ hchain (by simpa using hne) |R| hglo hghi
  obtain ⟨bn, hbn, rfl⟩ := List.mem_map.mp hab
  obtain ⟨hbp, hbm⟩ := hbins bn hbn
  obtain ⟨pos, hpos⟩ : ∃ pos : Bool, if pos then 0 ≤ R else R ≤ 0 := by
    rcases le_total 0 R with h | h
    · exact ⟨true, by simpa using h⟩
    · exact ⟨false, by simpa using h⟩
  obtain ⟨st0, l, hhead, hbin⟩ : ∃ (st0 : ℚ × List ℚ) (l : List (ℚ × List ℚ)),
      Exp8Head pos g.1 g.2.1 pq bpT st0 ∧
        Exp8Bin pos g.1 g.2.2.2.1 (exp8Delta k0) bn.1.1 bn.1.2 bn.2.1 bpT st0 l := by
    cases pos
    · exact ⟨sn, _, hhn, hbm⟩
    · exact ⟨sp, _, hhp, hbp⟩
  rw [hgm, hgd] at hhead
  rw [hgm] at hbin hpar
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := hbin
  obtain ⟨p1, p2, p3, p4⟩ := hpar
  set aq := bn.1.1 with haq
  set bq := bn.1.2 with hbq
  set bpB := bn.2.1 with hbpB
  set eH := g.2.2.2.1 with heH
  set hiq := dyQ g.2.2.2.2.2 with hhiq
  have hbq0 : (0 : ℚ) ≤ bq := b2.trans b3
  have hhiq0 : (0 : ℚ) ≤ hiq := by exact_mod_cast hR0.trans hghi
  -- `b'` at `e` is at most its bound at the group's largest exponent
  have hc0 : (0 : ℝ) < (2 : ℝ) ^ (-(m : ℤ)) := by positivity
  have hcapE : (2 : ℝ) ^ (e + 1) ≤ (2 : ℝ) ^ (eH + 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hcoreB : coreBp 8 e m ((bq : ℚ) : ℝ) ((exp8Eta1 m : ℚ) : ℝ) ≤ ((bpB : ℚ) : ℝ) := by
    have h1 := (Rat.cast_le (K := ℝ)).mpr b5
    push_cast at h1
    unfold coreBp
    have h2 := mul_le_mul_of_nonneg_left (min_le_min_left ((bq : ℚ) : ℝ) hcapE) hc0.le
    push_cast
    linarith
  have hcoreB0 : 0 ≤ coreBp 8 e m ((bq : ℚ) : ℝ) ((exp8Eta1 m : ℚ) : ℝ) := by
    unfold coreBp
    have h1 : (0 : ℝ) ≤ min ((bq : ℚ) : ℝ) ((2 : ℝ) ^ (e + 1)) := le_min (by exact_mod_cast hbq0) (by positivity)
    have h2 : (0 : ℝ) ≤ ((exp8Eta1 m : ℚ) : ℝ) := by
      have : (0 : ℚ) ≤ exp8Eta1 m := by unfold exp8Eta1 exp8Eta; split_ifs <;> positivity
      exact_mod_cast this
    have := mul_nonneg hc0.le h1
    positivity
  have hBT : ((bpB : ℚ) : ℝ) ≤ ((bpT : ℚ) : ℝ) := Rat.cast_le.mpr b6
  have hT1 : ((bpT : ℚ) : ℝ) < 1 := by exact_mod_cast p4
  -- the part bounds
  have hπ : ∀ i < 8, |r i| ≤ ((exp8Pi k0 hiq i : ℚ) : ℝ) := hparts hiq hghi
  have hpq : ∀ i < 8, corePi e m (fun i => ((exp8Pi k0 hiq i : ℚ) : ℝ)) ((exp8Eta1 m : ℚ) : ℝ) i ≤
      ((pq.getD i 0 : ℚ) : ℝ) := fun i hi => by
    have h1 := (Rat.cast_le (K := ℝ)).mpr (p1 i hi)
    push_cast at h1
    unfold corePi
    have h2 := mul_le_mul_of_nonneg_left (min_le_min_left ((exp8Pi k0 hiq i : ℚ) : ℝ) hcapE) hc0.le
    linarith
  have hpq0 : ∀ i, 0 ≤ pq.getD i 0 := fun i => by
    rw [List.getD_eq_getElem?_getD]
    cases hq : pq[i]? with
    | none => simp
    | some q => exact p2 q (List.mem_of_getElem? hq)
  -- Theorem 40 for the case
  obtain ⟨tF1, tF2⟩ := exp8_table
  have hF : ∀ k, ∀ i < 8, F p (exp8FR k i) := fun k i _ =>
    dyFn_getD_F p exp8Fact (dyF_of_all p exp8Fact (by rw [hp]; exact tF2)) k i
  have hφ : ∀ k, |∑ i ∈ range 8, exp8FR k i - invF k| ≤ ((exp8Phi k : ℚ) : ℝ) := fun k => by
    unfold exp8Phi exp8FR invF
    push_cast
    exact le_rfl
  have hd1 : 1 ≤ d' := by rw [← hgd]; exact hgd1
  have hexp : Real.exp (1 / 2) ≤ 2 := by
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  have hthm := thm40_case_sub p 8 hp (by norm_num) hA3 S hS r hrF X k₁ k₂ hk2 ((exp8Delta k0 : ℚ) : ℝ)
    (by rw [hk, ← hR]; exact hδ) ((aq : ℚ) : ℝ) ((bq : ℚ) : ℝ) (by rw [← hR]; exact hab1) (by rw [← hR]; exact hab2)
    (fun i => ((exp8Pi k0 hiq i : ℚ) : ℝ)) hπ e hU m d' hd1
    (by
      rw [← cast_exp8Eta1]
      have : (1 : ℝ) ≤ (d' : ℝ) := by exact_mod_cast hd1
      linarith)
    (fun hm0 => by
      rw [← cast_exp8Eta1]
      have h1 : (2 : ℝ) * ((bpB : ℚ) : ℝ) ≤ 1 := by
        have h2 := (Rat.cast_le (K := ℝ)).mpr b7
        push_cast at h2
        have h3 : (2 : ℝ) ≤ (2 : ℝ) ^ m := by
          calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
            _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm0
        nlinarith [hcoreB0.trans hcoreB]
      exact (Real.exp_le_exp.mpr (by linarith)).trans hexp)
    exp8FR hF (fun k => ((exp8Phi k : ℚ) : ℝ)) hφ pos (by rw [← hR]; exact hpos)
  -- the kernel's bound of the case
  have hstep := exp8SqChk_spec pos ((2 : ℚ) ^ (-(m : ℤ)) * aq) bpB l 0 st0 b8
  have hcert := expEps_cert p 8 hu (le_upQ 200) (by norm_num) hA3 pos e m d' aq bq (exp8Delta k0) (exp8Eta1 m)
    exp8Eta (fun i => ((exp8Pi k0 hiq i : ℚ) : ℝ)) exp8F
    (fun k i hi => dyFn_getD_zero exp8Fact tF1 k hi) exp8Phi (fun k => abs_nonneg _)
    (by unfold exp8Eta1 exp8Eta; split_ifs <;> positivity) (by unfold exp8Eta; positivity) b2 b3
    (by unfold exp8Delta; split_ifs; exacts [le_rfl, cD0]) b4
    (fun i => by exact_mod_cast exp8Pi_nonneg k0 hhiq0 i) pq bpT hpq hpq0 (hcoreB.trans hBT) p4 st0
    (by
      unfold Exp8Head Exp8HeadH exp8Run at hhead
      exact hhead)
    bpB hcoreB b7 (fun j => (st0 :: l).getD j (0, [])) (by simp)
    (fun j hj => by
      have := hstep j (by rw [b1]; exact hj)
      simpa using this)
    (3661 / 1000 * red8U ^ 8) b9 b10
  rw [cast_exp8Eta1, cast_exp8Eta] at hcert
  refine hthm.trans ?_
  have hε : ((3661 / 1000 * red8U ^ 8 : ℚ) : ℝ) = 3661 / 1000 * u p ^ 8 := by push_cast; rw [hu]
  rw [hε] at hcert
  have hX0 := (Real.exp_pos X).le
  have h8 : (((8 : ℕ) : ℝ)) * (2 : ℝ) ^ (-1074 : ℤ) = 8 * (2 : ℝ) ^ (-1074 : ℤ) := by norm_num
  rw [h8]
  exact add_le_add (mul_le_mul_of_nonneg_right hcert hX0) le_rfl

end ExpansionBounds
