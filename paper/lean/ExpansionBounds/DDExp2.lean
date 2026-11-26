import ExpansionBounds.DDExp2.All
import ExpansionBounds.Exp8

/-!
# Proposition 44 (`prop:ddexplog`): `DD::exp` within `5.465u²e^x + 2^{-1073}`

`DD::exp` at `p = 53`: EXP with `s = 1` and `d = 27` on double words, with multidouble's constants (`c_h`, `ln 2` to
42 bits, the first two parts of `c_ℓ` and of each `F_k`, and `c_r = RN(1/ln 2)`) and binary64's subnormals. The four
double-word operations are those of `DDOps.lean`, with their published bounds as hypotheses (`DWSpec`).

The reduction is Lemma 38 read with `n = 2` (`DDExpRed.lean`) at `X = 745.2` and `x̄_t = uX`: its bounds are
evaluated on their rational mirrors (`dd2RMax`, `dd2A0`, `dd2Delta`), with `ln 2` enclosed by `log_two_600`. The
run's `|r|` is at most `dd2TopS < 2^{-1}(1 - 2^{-46})`, so step (2)'s exponent is at most `-2` and there is no
squaring. From `2^e ≤ U`, `|r| ≥ 2^e(1 - 2^{-46})`: the two roundings of `U`, its factor `1 + 2^{-48}` and the low
part of `r` cost `(1 - u)/((1 + u)³(1 + 2^{-48})) ≥ 1 - 2^{-46}`, which the kernel checks. The proof then finds the
group of `e` and the interval of `|r|` (`DDExp2/Data.lean`), whose bound the kernel checked (`DDExp2/Run0.lean` to
`Run2.lean`), and `ddExpEps_le` carries it to the bound `ε` of the case (`dd_thm40_case_sub`).
-/

namespace ExpansionBounds

open Finset

/-- `x̄_t = uX`: `|x_l| ≤ u|x_h|` for a double word -/
def dd2Xt : ℚ := red8U * red8X

/-- `r̄_max = (1/2 + ε_k) ln 2 + x̄_t`, with `ln 2` at its upper end -/
def dd2RMax : ℚ := (1 / 2 + red8EpsK) * ln2B + dd2Xt

/-- `α_0 = r̄_max + x̄_t + k̄|ln 2 - c_h|` -/
def dd2A0 : ℚ := dd2RMax + dd2Xt + 1075 * max |ch8 - ln2A| |ch8 - ln2B|

/-- `|c_ℓ|` for the first two parts -/
def dd2C : ℚ := |cl8 0 + cl8 1|

/-- `η_ℓ`'s bound, `ln 2` at either end -/
def dd2EtaL : ℚ := max |ch8 + (cl8 0 + cl8 1) - ln2A| |ch8 + (cl8 0 + cl8 1) - ln2B|

/-- `ε_1 = e_M k̄|c_ℓ|` -/
def dd2E1 : ℚ := eFQ red8U * (1075 * dd2C)

/-- `ε_q = e_F(k̄|c_ℓ| + ε_1 + x̄_t)` -/
def dd2Eq : ℚ := eFQ red8U * (1075 * dd2C + dd2E1 + dd2Xt)

/-- the reduction's `δ = ε_1 + ε_q + e_F(r̄ + k̄η_ℓ + ε_1 + ε_q) + k̄η_ℓ` -/
def dd2Delta (rb : ℚ) : ℚ := dd2E1 + dd2Eq + eFQ red8U * (rb + 1075 * dd2EtaL + dd2E1 + dd2Eq) + 1075 * dd2EtaL

set_option maxHeartbeats 4000000 in
/-- the constants of `DDExp2/Data.lean` are bounds of what they stand for; `α_0 < 1/2`; `e ≥ -1` selects no `|r|`;
and what `U`'s roundings and the low part of `r` cost is within `2^{-46}` -/
theorem dd2_consts : dd2A0 < 1 / 2 ∧ dd2Delta dd2RMax ≤ dyQ dd2DeltaS ∧ (1 + red8U) / (2 * cr8) ≤ dyQ dd2TopS ∧
    dd2RMax + dyQ dd2DeltaS ≤ dyQ dd2TopS ∧ dyQ dd2TopS < (2 : ℚ) ^ (-1 : ℤ) * (1 - 1 / 2 ^ 46) ∧
    0 ≤ dyQ dd2DeltaS ∧ 0 < cr8 ∧ (1 + red8U) ^ 2 ≤ 1 + 1 / 2 ^ 48 ∧
    (1 - 1 / 2 ^ 46) * ((1 + red8U) * ((1 + red8U) ^ 2 * (1 + 1 / 2 ^ 48))) ≤ 1 - red8U := by
  decide +kernel

/-- the groups cover the exponents `-118 ≤ e ≤ -2`, and the last, of degree 1, ends at `-119` -/
theorem dd2_grps : (∀ e : ℤ, -118 ≤ e → e ≤ -2 → ∃ g ∈ dd2Grp, g.2.1 ≤ e ∧ e ≤ g.2.2.1) ∧ dd2Last.1 = 1 ∧
    dd2Last.2.2.1 = -119 := by
  decide +kernel

/-- the first two parts of `c_ℓ` and of each `F_k` are double words: the high part is the rounded sum -/
theorem dd2_table : rnQ 53 (cl8 0 + cl8 1) = cl8 0 ∧ (∀ t ∈ exp8Fact, rnQ 53 (dyFn t 0 + dyFn t 1) = dyFn t 0) ∧
    rnQ 53 (dyFn [] 0 + dyFn [] 1) = dyFn [] 0 := by
  decide +kernel

/-- the degree is 1 from `e = -119` down -/
theorem ddDeg_small {e : ℤ} (he : e ≤ -119) : ddDeg e = 1 := by
  rcases lt_or_eq_of_le he with h | h
  · simp [ddDeg, h]
  · subst h
    decide

/-- the rounded sum of the first two parts of `F_k` is the first -/
theorem dd2F_rn (k : ℕ) : rnQ 53 (exp8F k 0 + exp8F k 1) = exp8F k 0 := by
  unfold exp8F
  by_cases hk : k < exp8Fact.length
  · have hm : exp8Fact.getD k [] ∈ exp8Fact := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      exact List.getElem_mem hk
    exact dd2_table.2.1 _ hm
  · have e : exp8Fact.getD k [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [e]
    exact dd2_table.2.2

/-- `F_k` as a pair: the first two parts of multidouble's table -/
noncomputable def dd2F (k : ℕ) : ℝ × ℝ := (((exp8F k 0 : ℚ) : ℝ), ((exp8F k 1 : ℚ) : ℝ))

/-- `c_ℓ` as a pair: its first two parts -/
noncomputable def dd2Cl : ℝ × ℝ := (((cl8 0 : ℚ) : ℝ), ((cl8 1 : ℚ) : ℝ))

variable (p : ℤ) [Prec_gt_0 p]

/-- step (1)'s `r` with multidouble's constants -/
noncomputable def dd2R (O : DWOps) (x : ℝ × ℝ) : ℝ × ℝ := ddExpR p O x ((ch8 : ℚ) : ℝ) dd2Cl

/-- step (2)'s `U = RN(RN(|r_h| + |r_l|)(1 + 2^{-48}))` -/
noncomputable def dd2U (r : ℝ × ℝ) : ℝ := expU p 2 ((2 : ℝ) ^ (-48 : ℤ)) fun i => if i = 0 then r.1 else r.2

/-- each `F_k` is a double word -/
theorem dd2F_dw (hp : p = 53) (k : ℕ) : DW p (dd2F k) := by
  have hF : ∀ i, F p ((exp8F k i : ℚ) : ℝ) := fun i =>
    dyFn_getD_F p exp8Fact (dyF_of_all p exp8Fact (by rw [hp]; exact exp8_table.2)) k i
  refine ⟨hF 0, hF 1, ?_⟩
  show RN p (((exp8F k 0 : ℚ) : ℝ) + ((exp8F k 1 : ℚ) : ℝ)) = ((exp8F k 0 : ℚ) : ℝ)
  rw [← Rat.cast_add, ← cast_rn, hp, dd2F_rn]

/-- `c_ℓ` is a double word -/
theorem dd2Cl_dw (hp : p = 53) : DW p dd2Cl := by
  refine ⟨cl8_F p hp 0, cl8_F p hp 1, ?_⟩
  show RN p (((cl8 0 : ℚ) : ℝ) + ((cl8 1 : ℚ) : ℝ)) = ((cl8 0 : ℚ) : ℝ)
  rw [← Rat.cast_add, ← cast_rn, hp, dd2_table.1]

/-- the facts of a run that the cases use: `r` is a double word within `δ*` of `r_e`, and `|r|` is bounded -/
theorem dd2_run (hp : p = 53) {O : DWOps} (hO : DWSpec p O) (x : ℝ × ℝ) (hx : DW p x)
    (hx0 : |x.1| ≤ 7452 / 10) :
    DW p (dd2R p O x) ∧
      |dwVal (dd2R p O x) - (dwVal x - expK p x.1 * Real.log 2)| ≤ ((dyQ dd2DeltaS : ℚ) : ℝ) ∧
      |dwVal (dd2R p O x)| ≤ ((dyQ dd2TopS : ℚ) : ℝ) := by
  have hu : ((red8U : ℚ) : ℝ) = u p := by unfold red8U; exact u_53_rat p hp
  have hu53 : u p = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  have hup := u_pos p
  have hp14 : 14 ≤ p := by omega
  obtain ⟨cA0, cD, cT0, cT1, -, cD0, ccr, -, -⟩ := dd2_consts
  obtain ⟨lA, lB⟩ := log_two_600
  obtain ⟨kA, -, kX, kE⟩ := red8_check
  have hApos : (0 : ℝ) < ((ln2A : ℚ) : ℝ) := by exact_mod_cast kA
  have hL0 : 0 < Real.log 2 := lt_of_lt_of_le hApos lA
  -- the constants' distances from `ln 2` and `1/ln 2`
  have hinv1 : 1 / ((ln2B : ℚ) : ℝ) ≤ 1 / Real.log 2 := one_div_le_one_div_of_le hL0 lB
  have hinv2 : 1 / Real.log 2 ≤ 1 / ((ln2A : ℚ) : ℝ) := one_div_le_one_div_of_le hApos lA
  have hDl : |cR p - 1 / Real.log 2| ≤ ((red8Dl : ℚ) : ℝ) := by
    rw [cR_eq p hp]
    have h := abs_sub_le_max (c := ((cr8 : ℚ) : ℝ)) hinv1 hinv2
    simpa [red8Dl] using h
  have hXnn : (0 : ℝ) ≤ ((red8X : ℚ) : ℝ) := Rat.cast_nonneg.mpr (by decide +kernel)
  have hEps : epsK p ((red8X : ℚ) : ℝ) ≤ ((red8EpsK : ℚ) : ℝ) := by
    unfold epsK
    rw [show ((red8EpsK : ℚ) : ℝ) = (red8X : ℝ) * ((red8Dl : ℝ) + u p * cR p) by
      rw [cR_eq p hp, ← hu]; simp [red8EpsK]]
    exact mul_le_mul_of_nonneg_left (by linarith) hXnn
  have hRM : rMax p ((red8X : ℚ) : ℝ) ((dd2Xt : ℚ) : ℝ) ≤ ((dd2RMax : ℚ) : ℝ) := by
    unfold rMax
    rw [show ((dd2RMax : ℚ) : ℝ) = (1 / 2 + (red8EpsK : ℝ)) * (ln2B : ℝ) + (dd2Xt : ℝ) by simp [dd2RMax]]
    have hE0 : (0 : ℝ) ≤ 1 / 2 + ((red8EpsK : ℚ) : ℝ) := by
      have : (0 : ℝ) ≤ ((red8EpsK : ℚ) : ℝ) := Rat.cast_nonneg.mpr kE
      linarith
    linarith [mul_le_mul (add_le_add (le_refl (1 / 2 : ℝ)) hEps) lB hL0.le hE0]
  have hDe : |Real.log 2 - ((ch8 : ℚ) : ℝ)| ≤ ((max |ch8 - ln2A| |ch8 - ln2B| : ℚ) : ℝ) := by
    rw [abs_sub_comm]
    have h := abs_sub_le_max (c := ((ch8 : ℚ) : ℝ)) lA lB
    simpa using h
  have hA0 : expA0 p ((red8X : ℚ) : ℝ) ((dd2Xt : ℚ) : ℝ) ((ch8 : ℚ) : ℝ) ≤ ((dd2A0 : ℚ) : ℝ) := by
    unfold expA0
    rw [show ((dd2A0 : ℚ) : ℝ) = (dd2RMax : ℝ) + (dd2Xt : ℝ) +
      1075 * ((max |ch8 - ln2A| |ch8 - ln2B| : ℚ) : ℝ) by simp [dd2A0]]
    linarith
  have hXe : ((red8X : ℚ) : ℝ) = 7452 / 10 := by simp [red8X]
  have hX0 : |x.1| ≤ ((red8X : ℚ) : ℝ) := by rw [hXe]; exact hx0
  have hX1 : ((red8X : ℚ) : ℝ) ≤ 745.3 := by rw [hXe]; norm_num
  have hxl := (DW.parts p hx).1
  have hxt : |x.2| ≤ ((dd2Xt : ℚ) : ℝ) := by
    rw [show ((dd2Xt : ℚ) : ℝ) = u p * (red8X : ℝ) by rw [← hu]; simp [dd2Xt]]
    exact hxl.trans (mul_le_mul_of_nonneg_left hX0 hup.le)
  have hA0lt : expA0 p ((red8X : ℚ) : ℝ) ((dd2Xt : ℚ) : ℝ) ((ch8 : ℚ) : ℝ) < 1 / 2 :=
    hA0.trans_lt (lt_of_lt_of_eq (Rat.cast_lt.mpr cA0) (by norm_num))
  obtain ⟨-, a2, -, -⟩ := dd_expred_a p hp14 x hx.1 _ _ _ hX0 hX1 hxt (ch8_mult p hp) hA0lt
  have hD0 : (0 : ℝ) ≤ ((dyQ dd2DeltaS : ℚ) : ℝ) := Rat.cast_nonneg.mpr cD0
  by_cases hk0 : expK p x.1 = 0
  · -- `k = 0`: `r = x`, and `|x_h| c_r < 1/2`
    have hrx : dd2R p O x = x := by
      unfold dd2R ddExpR
      simp only [hk0, ↓reduceIte]
    rw [hrx, hk0]
    refine ⟨hx, by simpa using hD0, ?_⟩
    have hcr : (0 : ℝ) < ((cr8 : ℚ) : ℝ) := by exact_mod_cast ccr
    have hc : |x.1| * ((cr8 : ℚ) : ℝ) < 1 / 2 := by
      have h1 := abs_lt_half_of_RN p (roundAway_eq_zero hk0)
      rw [cR_eq p hp, abs_mul, abs_of_pos hcr] at h1
      exact h1
    have hT := (Rat.cast_le (K := ℝ)).mpr cT0
    rw [Rat.cast_div, Rat.cast_add, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat, hu, div_le_iff₀ (by positivity)] at hT
    have h1 : |dwVal x| ≤ (1 + u p) * |x.1| := by
      calc |dwVal x| ≤ |x.1| + |x.2| := abs_add_le _ _
        _ ≤ (1 + u p) * |x.1| := by linarith
    have h2 : (1 + u p) * |x.1| * (2 * ((cr8 : ℚ) : ℝ)) ≤ 1 + u p := by nlinarith
    have h3 : |dwVal x| * (2 * ((cr8 : ℚ) : ℝ)) ≤ ((dyQ dd2TopS : ℚ) : ℝ) * (2 * ((cr8 : ℚ) : ℝ)) :=
      (mul_le_mul_of_nonneg_right h1 (by positivity)).trans (h2.trans hT)
    exact le_of_mul_le_mul_right h3 (by positivity)
  · -- `k ≠ 0`: the reduction, with its bounds on their mirrors
    obtain ⟨b1, b2⟩ := dd_expred_b p hp14 hO x hx _ _ _ dd2Cl (dd2Cl_dw p hp) hX0 hX1 hxt (ch8_mult p hp) hA0lt
      hk0 _ (a2.trans hRM)
    have hcF := cast_eFQ p hu
    have hC : |dwVal dd2Cl| = ((dd2C : ℚ) : ℝ) := by simp [dd2C, dd2Cl, dwVal]
    have hEta : ddEtaL ((ch8 : ℚ) : ℝ) dd2Cl ≤ ((dd2EtaL : ℚ) : ℝ) := by
      unfold ddEtaL
      rw [show Real.log 2 - ((ch8 : ℚ) : ℝ) - dwVal dd2Cl = -((((ch8 : ℚ) : ℝ) + dwVal dd2Cl) - Real.log 2) by ring,
        abs_neg]
      have h := abs_sub_le_max (c := ((ch8 : ℚ) : ℝ) + dwVal dd2Cl) lA lB
      simpa [dd2EtaL, dd2Cl, dwVal] using h
    have hE1 : ddRedE1 p dd2Cl = ((dd2E1 : ℚ) : ℝ) := by
      unfold ddRedE1 dd2E1
      rw [hC, Rat.cast_mul, Rat.cast_mul, hcF]
      simp [eM, eF]
    have hEq : ddRedEq p dd2Cl ((dd2Xt : ℚ) : ℝ) = ((dd2Eq : ℚ) : ℝ) := by
      unfold ddRedEq dd2Eq
      rw [hC, hE1, Rat.cast_mul, hcF]
      push_cast
      ring
    have hDel : ddRedDelta p ((ch8 : ℚ) : ℝ) dd2Cl ((dd2Xt : ℚ) : ℝ) ((dd2RMax : ℚ) : ℝ) ≤
        ((dd2Delta dd2RMax : ℚ) : ℝ) := by
      unfold ddRedDelta ddRedE2 dd2Delta
      rw [hE1, hEq]
      push_cast
      rw [hcF]
      nlinarith [eF_nonneg p]
    have hδ := b1.trans (hDel.trans (Rat.cast_le.mpr cD))
    refine ⟨b2, hδ, ?_⟩
    have hT := (Rat.cast_le (K := ℝ)).mpr cT1
    rw [Rat.cast_add] at hT
    have h1 := abs_sub_abs_le_abs_sub (dwVal (dd2R p O x)) (dwVal x - expK p x.1 * Real.log 2)
    unfold dd2R at h1 ⊢
    linarith [a2.trans hRM]

/-- Proposition 44 (`prop:ddexplog`) for `DD::exp`, at `p = 53` with multidouble's constants and binary64's
subnormals: for a double word `x` with `|x_h| ≤ 745.2`, with `e` the exponent of step (2)'s `U` (`-1023` where
`U < 2^{-1022}`), the degree `d'` of step (3), the core's scaling of `r` up by `2^{-e}` exact, as in Lemma 33, and its
scaling back and the last scaling rounded by `S`, the last in two steps, `2^{k₁}` then `2^{k₂}` with `k₂ ≤ 0`:
`|y - e^x| ≤ 5.465u² e^x + 2^{-1073}`.

What remains assumed: the four published bounds of the double-word operations (`DWSpec`: AccurateDWPlusDW,
DWPlusFP, DWTimesFP3 and DWTimesDW2 return double words within `e_A`, `e_F`, `e_M` and `e_P` of their exact
results); the rounding rule of a scaling (`hS`: a value is kept, or it is below `2^{-1022}` and is rounded to a
multiple of `2^{-1074}` within `2^{-1075}`); and no overflow, the model having no largest finite value. The floors
of the scaling back are not assumed: the kernel checks them for each case. multidouble takes `k₁ = k/2`, rounded
toward zero, so `k₂ > 0` where `k > 0`; both steps then scale up, which binary64 does exactly, and the value is that
of the split `(k, 0)`.
For binary64 the run must also meet the paper's (A2′): every product, fused multiply-add and quotient returns what it
would with an unbounded exponent range, as in the model, but those that only select `k` or an exponent, which the paper
exempts -/
theorem prop44_exp (hp : p = 53) {O : DWOps} (hO : DWSpec p O) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℝ × ℝ) (hx : DW p x) (hx0 : |x.1| ≤ 7452 / 10) (k₁ k₂ : ℤ) (hk : k₁ + k₂ = expK p x.1) (hk2 : k₂ ≤ 0)
    (e : ℤ)
    (hsel : ((2 : ℝ) ^ e ≤ dd2U p (dd2R p O x) ∧ dd2U p (dd2R p O x) < (2 : ℝ) ^ (e + 1)) ∨
      (dd2U p (dd2R p O x) < (2 : ℝ) ^ (-1022 : ℤ) ∧ e = -1023)) :
    |S ((2 : ℝ) ^ k₂ * S ((2 : ℝ) ^ k₁ *
          (O.addF (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O x) dd2F (ddDeg e)) 1).1)) +
        S ((2 : ℝ) ^ k₂ * S ((2 : ℝ) ^ k₁ *
          (O.addF (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O x) dd2F (ddDeg e)) 1).2)) -
        Real.exp (dwVal x)| ≤
      5465 / 1000 * u p ^ 2 * Real.exp (dwVal x) + (2 : ℝ) ^ (-1073 : ℤ) := by
  have hu : ((red8U : ℚ) : ℝ) = u p := by unfold red8U; exact u_53_rat p hp
  have hu53 : u p = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  have hup := u_pos p
  have h4u : 4 * u p < 1 := by rw [hu53]; norm_num
  obtain ⟨-, -, -, -, cTop, cD0, -, cγ, cC⟩ := dd2_consts
  obtain ⟨hrdw, hδ, hRtop⟩ := dd2_run p hp hO x hx hx0
  obtain ⟨r, hr⟩ : ∃ r, r = dd2R p O x := ⟨_, rfl⟩
  rw [← hr] at hrdw hδ hRtop hsel ⊢
  obtain ⟨R, hR⟩ : ∃ R, R = dwVal r := ⟨_, rfl⟩
  obtain ⟨U, hUd⟩ : ∃ U, U = dd2U p r := ⟨_, rfl⟩
  rw [← hUd] at hsel
  -- `|r_h| + |r_l| ≤ U`, so `|r_h| + |r_l| < 2^{e+1}`
  have hsum : ∑ i ∈ range 2, |(fun i : ℕ => if i = 0 then r.1 else r.2) i| = |r.1| + |r.2| := by
    simp [sum_range_succ]
  have hγ : (1 + u p) ^ 2 ≤ 1 + (2 : ℝ) ^ (-48 : ℤ) := by
    have h1 := (Rat.cast_le (K := ℝ)).mpr cγ
    push_cast at h1
    rw [hu] at h1
    exact h1.trans_eq (by norm_num)
  have hSU : |r.1| + |r.2| ≤ U := by
    rw [hUd, ← hsum]
    exact expU_ge p 2 (by norm_num) _ hγ _
  have hU : |r.1| + |r.2| < (2 : ℝ) ^ (e + 1) := by
    rcases hsel with ⟨-, h2⟩ | ⟨h2, he⟩
    · exact hSU.trans_lt h2
    · rw [he]
      exact (hSU.trans_lt h2).trans_eq (by norm_num)
  have hRS : |R| ≤ |r.1| + |r.2| := by rw [hR]; exact abs_add_le _ _
  have hrl := (DW.parts p hrdw).1
  -- the lower end of the `|r|` that select `e`
  have hlow : (2 : ℝ) ^ e ≤ U → (2 : ℝ) ^ e * (1 - 1 / 2 ^ 46) ≤ |R| := by
    intro h2
    have h3 := expU_le p 2 (by norm_num) ((2 : ℝ) ^ (-48 : ℤ)) (by positivity) fun i => if i = 0 then r.1 else r.2
    rw [hsum] at h3
    have h3' : U ≤ (1 + u p) ^ 2 * (1 + (2 : ℝ) ^ (-48 : ℤ)) * (|r.1| + |r.2|) := by rw [hUd]; exact h3
    have h4 : (1 - 1 / 2 ^ 46 : ℝ) * ((1 + u p) * ((1 + u p) ^ 2 * (1 + (2 : ℝ) ^ (-48 : ℤ)))) ≤ 1 - u p := by
      have h1 := (Rat.cast_le (K := ℝ)).mpr cC
      push_cast at h1
      rw [hu] at h1
      exact (le_of_eq (by norm_num)).trans h1
    -- `(1 - u)(|r_h| + |r_l|) ≤ (1 + u)|r|`
    have h5 : (1 - u p) * (|r.1| + |r.2|) ≤ (1 + u p) * |R| := by
      have h6 : |r.1| - |r.2| ≤ |R| := by
        have := abs_sub_abs_le_abs_sub r.1 (-r.2)
        rw [abs_neg, sub_neg_eq_add] at this
        rw [hR]
        exact this
      nlinarith [abs_nonneg r.1, abs_nonneg r.2]
    have hK2 : (0 : ℝ) < (1 + u p) ^ 2 * (1 + (2 : ℝ) ^ (-48 : ℤ)) := by positivity
    have he0 : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
    obtain ⟨K, hKd⟩ : ∃ K, K = (1 + u p) * ((1 + u p) ^ 2 * (1 + (2 : ℝ) ^ (-48 : ℤ))) := ⟨_, rfl⟩
    have hK : 0 < K := by rw [hKd]; positivity
    rw [← hKd] at h4
    have h7 : (2 : ℝ) ^ e * (1 - u p) ≤ K * |R| := by
      have h8 : (2 : ℝ) ^ e * (1 - u p) ≤
          (1 + u p) ^ 2 * (1 + (2 : ℝ) ^ (-48 : ℤ)) * (|r.1| + |r.2|) * (1 - u p) :=
        mul_le_mul_of_nonneg_right (h2.trans h3') (by linarith)
      have h9 : (1 + u p) ^ 2 * (1 + (2 : ℝ) ^ (-48 : ℤ)) * ((1 - u p) * (|r.1| + |r.2|)) ≤
          (1 + u p) ^ 2 * (1 + (2 : ℝ) ^ (-48 : ℤ)) * ((1 + u p) * |R|) := mul_le_mul_of_nonneg_left h5 hK2.le
      calc (2 : ℝ) ^ e * (1 - u p) ≤ (1 + u p) ^ 2 * (1 + (2 : ℝ) ^ (-48 : ℤ)) * (|r.1| + |r.2|) * (1 - u p) := h8
        _ = (1 + u p) ^ 2 * (1 + (2 : ℝ) ^ (-48 : ℤ)) * ((1 - u p) * (|r.1| + |r.2|)) := by ring
        _ ≤ (1 + u p) ^ 2 * (1 + (2 : ℝ) ^ (-48 : ℤ)) * ((1 + u p) * |R|) := h9
        _ = K * |R| := by rw [hKd]; ring
    have h10 : (2 : ℝ) ^ e * ((1 - 1 / 2 ^ 46) * K) ≤ (2 : ℝ) ^ e * (1 - u p) :=
      mul_le_mul_of_nonneg_left h4 he0.le
    refine le_of_mul_le_mul_right ?_ hK
    calc (2 : ℝ) ^ e * (1 - 1 / 2 ^ 46) * K = (2 : ℝ) ^ e * ((1 - 1 / 2 ^ 46) * K) := by ring
      _ ≤ (2 : ℝ) ^ e * (1 - u p) := h10
      _ ≤ K * |R| := h7
      _ = |R| * K := by ring
  have hTop := (Rat.cast_lt (K := ℝ)).mpr cTop
  push_cast at hTop
  rw [← hR] at hRtop hδ
  -- `e ≤ -2`
  have he2 : e ≤ -2 := by
    by_contra hcon
    rcases hsel with ⟨h1, -⟩ | ⟨-, he⟩
    · have hl := hlow h1
      have h6 : (2 : ℝ) ^ (-1 : ℤ) ≤ (2 : ℝ) ^ e := zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h8 := mul_le_mul_of_nonneg_right h6 (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2 ^ 46)
      linarith
    · omega
  have hR0 : 0 ≤ |R| := abs_nonneg R
  -- the group of `e` and the interval of `|r|`
  obtain ⟨gCov, gL1, gL2⟩ := dd2_grps
  obtain ⟨d', hd'⟩ : ∃ d', d' = ddDeg e := ⟨_, rfl⟩
  rw [← hd']
  obtain ⟨aq, bq, hd1, hbin, hab1, hab2⟩ : ∃ aq bq : ℚ, 1 ≤ d' ∧ DD2Bin d' aq bq ∧ ((aq : ℚ) : ℝ) ≤ |R| ∧
      |R| ≤ ((bq : ℚ) : ℝ) := by
    by_cases he118 : -118 ≤ e
    · obtain ⟨g, hg, hg1, hg2⟩ := gCov e he118 he2
      obtain ⟨o1, o2, o3, o4, o5⟩ := dd2_all g hg
      have h1 : (2 : ℝ) ^ e ≤ U := by
        rcases hsel with ⟨h1, -⟩ | ⟨-, he⟩
        · exact h1
        · omega
      have hlo : (((if false = true then 0 else (2 : ℚ) ^ g.2.1 * (1 - 1 / 2 ^ 46) : ℚ)) : ℝ) ≤ |R| := by
        simp only [Bool.false_eq_true, ↓reduceIte]
        push_cast
        have h6 : (2 : ℝ) ^ g.2.1 ≤ (2 : ℝ) ^ e := zpow_le_zpow_right₀ (by norm_num) hg1
        have h8 := mul_le_mul_of_nonneg_right h6 (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2 ^ 46)
        linarith [hlow h1]
      have hhi : |R| ≤ (((min (dyQ dd2TopS) ((2 : ℚ) ^ (g.2.2.1 + 1)) : ℚ)) : ℝ) := by
        push_cast
        exact le_min hRtop ((hRS.trans hU.le).trans (zpow_le_zpow_right₀ (by norm_num) (by omega)))
      obtain ⟨ab, hab, hab1, hab2⟩ := exp8Chain_cover _ _ _ o4 (by simpa using o3) |R| hlo hhi
      obtain ⟨bn, hbn, rfl⟩ := List.mem_map.mp hab
      exact ⟨_, _, by rw [hd', ← o1 e hg1 hg2]; exact o2, by rw [hd', ← o1 e hg1 hg2]; exact o5 bn hbn, hab1, hab2⟩
    · have he119 : e ≤ -119 := by omega
      obtain ⟨-, o2, o3, o4, o5⟩ := dd2_last
      have hdl : d' = dd2Last.1 := by rw [hd', gL1, ddDeg_small he119]
      have hlo : (((if true = true then 0 else (2 : ℚ) ^ dd2Last.2.1 * (1 - 1 / 2 ^ 46) : ℚ)) : ℝ) ≤ |R| := by
        simp only [↓reduceIte, Rat.cast_zero]
        exact hR0
      have hhi : |R| ≤ (((min (dyQ dd2TopS) ((2 : ℚ) ^ (dd2Last.2.2.1 + 1)) : ℚ)) : ℝ) := by
        rw [gL2]
        push_cast
        exact le_min hRtop ((hRS.trans hU.le).trans (zpow_le_zpow_right₀ (by norm_num) (by omega)))
      obtain ⟨ab, hab, hab1, hab2⟩ := exp8Chain_cover _ _ _ o4 (by simpa using o3) |R| hlo hhi
      obtain ⟨bn, hbn, rfl⟩ := List.mem_map.mp hab
      exact ⟨_, _, by rw [hdl]; exact o2, by rw [hdl]; exact o5 bn hbn, hab1, hab2⟩
  obtain ⟨pos, hpos⟩ : ∃ pos : Bool, if pos then 0 ≤ R else R ≤ 0 := by
    rcases le_total 0 R with h | h
    · exact ⟨true, by simpa using h⟩
    · exact ⟨false, by simpa using h⟩
  obtain ⟨b1, b2, b3, b4, b5⟩ := hbin
  obtain ⟨s1, s2, s3, s4⟩ : DD2Sign pos d' aq bq := by
    cases pos
    · exact b5
    · exact b4
  have hbq0 : (0 : ℚ) ≤ bq := b1.trans b2
  have hbq1 : bq ≤ 1 := by linarith
  -- Theorem 40 for the case
  have hφ : ∀ k, |dwVal (dd2F k) - invF k| ≤ ((dd2Phi k : ℚ) : ℝ) := fun k => by
    unfold dd2Phi dd2F dwVal invF
    push_cast
    exact le_rfl
  have hfl : ((dd2Floor : ℚ) : ℝ) = (2 : ℝ) ^ (-967 : ℤ) := by
    unfold dd2Floor
    rw [show (-967 : ℤ) = -((967 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast, ← one_div]
    simp only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat]
  have heta : ((dd2Eta : ℚ) : ℝ) = (2 : ℝ) ^ (-1075 : ℤ) := cast_exp8Eta
  have hthm := dd_thm40_case_sub p hp hO S hS r hrdw (dwVal x) k₁ k₂ hk2 ((dyQ dd2DeltaS : ℚ) : ℝ)
    (by rw [hk, ← hR]; exact hδ) ((aq : ℚ) : ℝ) ((bq : ℚ) : ℝ) (by exact_mod_cast b1) (by rw [← hR]; exact hab1)
    (by rw [← hR]; exact hab2) e d' hd1
    (by
      have h1 : ((bq : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hbq1
      have h2 : (1 : ℝ) ≤ (d' : ℝ) := by exact_mod_cast hd1
      linarith)
    dd2F (dd2F_dw p hp) (fun k => ((dd2Phi k : ℚ) : ℝ)) hφ pos (by rw [← hR]; exact hpos)
    (fun hd => by
      rw [← hfl]
      exact ddFloor_le p hu h4u pos hbq0 hbq1 dd2Phi d' (s1 hd))
  -- the kernel's bound of the case
  have hcert := ddExpEps_le p hu h4u pos b1 b2 cD0 b3 dd2Phi d' s2 s3
  rw [heta] at hcert
  have hε : ((5465 / 1000 * red8U ^ 2 : ℚ) : ℝ) = 5465 / 1000 * u p ^ 2 := by push_cast; rw [hu]
  have hcert2 := hcert.trans ((Rat.cast_le (K := ℝ)).mpr s4)
  rw [hε] at hcert2
  exact hthm.trans (add_le_add (mul_le_mul_of_nonneg_right hcert2 (Real.exp_pos _).le) le_rfl)

end ExpansionBounds
