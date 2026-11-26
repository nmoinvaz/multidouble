import ExpansionBounds.Log8
import ExpansionBounds.DDSpec

/-!
# Theorem 42 at `n = 8` and `p = 53` with its start computed

`thm42_8_both` takes the bounds of the start `y_0` as hypotheses. Here `y_0` is computed as step (1) of LOG does:
the double-double logarithm of the double word `x̃`, or, where `x_0 ≥ 2^{1023}`, that of the halved `x̃_h` plus the
double-double `ln 2` by AccurateDWPlusDW. Proposition 44 on its four algorithms (`prop44_ln_dd`, `prop44_ln_dd_dw`)
and Theorem 3.1 of Joldes, Muller and Popescu (`accDWPlusDW_good`) give those bounds, so `thm42_8_dd` proves the start's
bounds instead of taking them as hypotheses: the logarithm is within `9.926u^8|ln x| + 2^{-509}`, with what the run of
`DD::ln` still assumes, the computed quotient `w` of its start (`hw0`, `hw1`) and the exponents it selects (`hrun`).
-/

namespace ExpansionBounds

open Finset

/-- the double-double `ln 2` is a double word, and `δ_0 ≤ 1/10` -/
theorem ln8CL_consts : rnQ 53 (dyQ log8CL0) = dyQ log8CL0 ∧ rnQ 53 (dyQ log8CL1) = dyQ log8CL1 ∧
    rnQ 53 (dyQ log8CL0 + dyQ log8CL1) = dyQ log8CL0 ∧ log8D0 ≤ 1 / 10 := by
  decide +kernel

variable (p : ℤ) [Prec_gt_0 p]

/-- a pair as an expansion of two parts -/
def pairExp (v : ℝ × ℝ) (i : ℕ) : ℝ := if i = 0 then v.1 else if i = 1 then v.2 else 0

/-- the double-double `ln 2` that the start adds where it halves `x` -/
noncomputable def ln8CL : ℝ × ℝ := (((dyQ log8CL0 : ℚ) : ℝ), ((dyQ log8CL1 : ℚ) : ℝ))

/-- step (1)'s double word: `x̃` where `x_0 < 2^{1023}`, the halved `x̃_h` otherwise -/
noncomputable def ln8Xs (S : ℝ → ℝ) (x : ℕ → ℝ) : ℝ × ℝ :=
  if x 0 < (2 : ℝ) ^ (1023 : ℤ) then ln8Xt p x else ln8Xh p S x

/-- step (1)'s start `y_0`: `DD::ln` of `ln8Xs`, with its quotient `w` and the exponents of its run, and where `x`
was halved, AccurateDWPlusDW of it and the double-double `ln 2` -/
noncomputable def ln8Start (S : ℝ → ℝ) (x : ℕ → ℝ) (w : ℝ) (j₁ j₂ f fφ ft fc : ℤ) : ℝ × ℝ :=
  if x 0 < (2 : ℝ) ^ (1023 : ℤ) then
    ddLn p (ddOps p) S (ln8Xs p S x) (ddLnY0 p (ln8Xs p S x) w) j₁ j₂ f fφ ft fc
  else accDWPlusDW p (ddLn p (ddOps p) S (ln8Xs p S x) (ddLnY0 p (ln8Xs p S x) w) j₁ j₂ f fφ ft fc) ln8CL

omit [Prec_gt_0 p] in
theorem two_zpow_neg_1071 : (2 : ℝ) ^ (-1071 : ℤ) = 1 / 2 ^ 1071 := by
  rw [show (-1071 : ℤ) = -((1071 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast, one_div]

/-- the double-double `ln 2` is a double word -/
theorem ln8CL_dw (hp : p = 53) : DW p ln8CL := by
  subst hp
  obtain ⟨c0, c1, c01, -⟩ := ln8CL_consts
  refine ⟨?_, ?_, ?_⟩
  · have h := F_RN 53 ((dyQ log8CL0 : ℚ) : ℝ)
    rw [← cast_rn, c0] at h
    exact h
  · have h := F_RN 53 ((dyQ log8CL1 : ℚ) : ℝ)
    rw [← cast_rn, c1] at h
    exact h
  · show RN 53 (((dyQ log8CL0 : ℚ) : ℝ) + ((dyQ log8CL1 : ℚ) : ℝ)) = ((dyQ log8CL0 : ℚ) : ℝ)
    rw [← Rat.cast_add, ← cast_rn, c01]

/-- a double word's parts as an expansion: in `F`, with `RN(y_0 + y_1) = y_0` and zeros after -/
theorem pairExp_dw {v : ℝ × ℝ} (hv : DW p v) :
    (∀ i < 8, F p (pairExp v i)) ∧ RN p (pairExp v 0 + pairExp v 1) = pairExp v 0 ∧ ∀ i, 2 ≤ i → pairExp v i = 0 := by
  obtain ⟨h1, h2, h3⟩ := hv
  refine ⟨fun i _ => ?_, h3, fun i hi => ?_⟩
  · unfold pairExp
    split_ifs
    · exact h1
    · exact h2
    · exact F_zero p
  · unfold pairExp
    simp only [show i ≠ 0 by omega, show i ≠ 1 by omega, ↓reduceIte]

/-- Theorem 42 (`thm:log`) at `n = 8` and `p = 53` with the start computed: for `x > 0` in `F` on `H(2)` with
`|ln x| ≤ 745.1`, and `y_0` the double-double logarithm of step (1)'s double word (plus the double-double `ln 2`
where `x_0 ≥ 2^{1023}`), `|y - ln x| ≤ 9.926u^8|ln x| + 2^{-509}`. What remains assumed: binary64's rounding `S`
of a scaling; the quotient `w` of `DD::ln`'s start within `u|x_l/x_h| + 2^{-1075}` and exact for `x_h = 1`; the
exponents that the two runs select (`hrun` for `DD::ln`, `hk`, `hsel`, `hUφ`, `hselt`, `hUc` for LOG); and no overflow,
the model having no largest number. Each run scales by its `2^k` in two steps, with `k₂ ≤ 0`; multidouble takes
`k₁ = k/2`, rounded toward zero, so `k₂ > 0` where `k > 0`; both steps then scale up, which binary64 does exactly, and
the value is that of the split `(k, 0)`. For binary64 the runs must also meet the paper's (A2′): every product, fused
multiply-add and quotient returns what it would with an unbounded exponent range, as in the model, but the quotient
`x_l/x_h` of `DD::ln`'s start, whose error a hypothesis bounds, and those that only select `k`, an exponent or a branch,
which the paper exempts -/
theorem thm42_8_dd (hp : p = 53) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℕ → ℝ) (hx : ∀ i < 8, F p (x i)) (hH : Htheta p 8 2 x) (hX0 : 0 < ∑ i ∈ range 8, x i)
    (hX : |Real.log (∑ i ∈ range 8, x i)| ≤ 7451 / 10) (w : ℝ)
    (hw0 : |w - (ln8Xs p S x).2 / (ln8Xs p S x).1| ≤
      u p * |(ln8Xs p S x).2 / (ln8Xs p S x).1| + (2 : ℝ) ^ (-1075 : ℤ))
    (hw1 : (ln8Xs p S x).1 = 1 → w = (ln8Xs p S x).2) (j₁ j₂ f fφ ft fc : ℤ)
    (hrun : DDLnRun p (ddOps p) S (ln8Xs p S x) (ddLnY0 p (ln8Xs p S x) w) j₁ j₂ f fφ ft fc) (y0 : ℕ → ℝ)
    (hy : y0 = pairExp (ln8Start p S x w j₁ j₂ f fφ ft fc))
    (k₁ k₂ : ℤ) (hk : k₁ + k₂ = expK p (-y0 0)) (hk2 : k₂ ≤ 0) (e : ℤ)
    (hsel : ((2 : ℝ) ^ e ≤ expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8R p y0) ∧
        expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8R p y0) < (2 : ℝ) ^ (e + 1)) ∨
      (expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8R p y0) < (2 : ℝ) ^ (-1022 : ℤ) ∧ e = -1023))
    (eφ et ec : ℤ) (hUφ : ∑ i ∈ range 8, |ln8Phi p S k₁ k₂ x i| < (2 : ℝ) ^ (eφ + 1))
    (hselt : ((2 : ℝ) ^ et ≤ expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8T p S y0 e) ∧
        expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8T p S y0 e) < (2 : ℝ) ^ (et + 1)) ∨
      (expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8T p S y0 e) < (2 : ℝ) ^ (-1022 : ℤ) ∧ et = -1023))
    (hUc : ∑ i ∈ range 8, |ln8C p S eφ et (ln8Phi p S k₁ k₂ x) (ln8T p S y0 e) i| < (2 : ℝ) ^ (ec + 1)) :
    |(ln8 p S y0 x k₁ k₂ e eφ et ec).sum - Real.log (∑ i ∈ range 8, x i)| ≤
      9926 / 1000 * u p ^ 8 * |Real.log (∑ i ∈ range 8, x i)| + 1 / 2 ^ 509 := by
  have hX' : |Real.log (∑ i ∈ range 8, x i)| ≤ 7452 / 10 := hX.trans (by norm_num)
  have hD : ((log8D0 : ℚ) : ℝ) ≤ 1 / 10 := by
    have := (Rat.cast_le (K := ℝ)).mpr ln8CL_consts.2.2.2
    push_cast at this
    exact this
  obtain ⟨hX1, hX2⟩ := abs_le.mp hX
  by_cases hlt : x 0 < (2 : ℝ) ^ (1023 : ℤ)
  · -- the start is `DD::ln` of `x̃`
    have exs : ln8Xs p S x = ln8Xt p x := by simp only [ln8Xs, hlt, ↓reduceIte]
    have est : ln8Start p S x w j₁ j₂ f fφ ft fc =
        ddLn p (ddOps p) S (ln8Xt p x) (ddLnY0 p (ln8Xt p x) w) j₁ j₂ f fφ ft fc := by
      simp only [ln8Start, hlt, ↓reduceIte, exs]
    rw [exs] at hw0 hw1 hrun
    obtain ⟨hF1, hF2, hRN, hpos, hlog⟩ := ln8Xt_spec p hp x hx hH hX0
    have hdw : DW p (ln8Xt p x) := ⟨hF1, hF2, hRN⟩
    obtain ⟨l1, l2⟩ := abs_le.mp hlog
    have hXt : |Real.log (dwVal (ln8Xt p x))| ≤ 7452 / 10 := by
      show |Real.log ((ln8Xt p x).1 + (ln8Xt p x).2)| ≤ 7452 / 10
      rw [abs_le]
      constructor <;> linarith
    have hb := prop44_ln_dd p hp S hS (ln8Xt p x) hdw hpos hXt w hw0 hw1 j₁ j₂ f fφ ft fc hrun
    have hL := prop44_ln_dd_dw p hp S hS (ln8Xt p x) hdw hpos hXt w hw0 hw1 j₁ j₂ f fφ ft fc hrun
    rw [← est] at hb hL
    obtain ⟨hy0, hyd, hy2⟩ := pairExp_dw p hL
    rw [← hy] at hy0 hyd hy2
    have hDW : |y0 0 + y0 1 - Real.log ((ln8Xt p x).1 + (ln8Xt p x).2)| ≤
        15351 / 1000 * u p ^ 2 * |Real.log ((ln8Xt p x).1 + (ln8Xt p x).2)| + 1 / 2 ^ 1071 := by
      rw [two_zpow_neg_1071] at hb
      rw [hy]
      exact hb
    exact thm42_8_both p hp S hS x hx hH hX0 hX' y0 hy0 hyd hy2 (Or.inl ⟨hlt, hDW⟩) k₁ k₂ hk hk2 e hsel eφ et ec hUφ
      hselt hUc
  · -- the start is `DD::ln` of the halved `x̃_h`, plus the double-double `ln 2`
    have hbig : (2 : ℝ) ^ (1023 : ℤ) ≤ x 0 := not_lt.mp hlt
    have exs : ln8Xs p S x = ln8Xh p S x := by simp only [ln8Xs, hlt, ↓reduceIte]
    have est : ln8Start p S x w j₁ j₂ f fφ ft fc =
        accDWPlusDW p (ddLn p (ddOps p) S (ln8Xh p S x) (ddLnY0 p (ln8Xh p S x) w) j₁ j₂ f fφ ft fc) (ln8CL) := by
      simp only [ln8Start, hlt, ↓reduceIte, exs]
    rw [exs] at hw0 hw1 hrun
    obtain ⟨hF1, hF2, hRN, hpos, hlog, hln2⟩ := ln8Xh_spec p hp S hS x hx hH hX0 hbig
    have hdw : DW p (ln8Xh p S x) := ⟨hF1, hF2, hRN⟩
    have h2 := Real.log_two_gt_d9
    have hsmall : (1 : ℝ) / 2 ^ 2000 ≤ 1 / 100 :=
      one_div_le_one_div_of_le (by norm_num) (by
        calc (100 : ℝ) ≤ 2 ^ 7 := by norm_num
          _ ≤ 2 ^ 2000 := pow_le_pow_right₀ (by norm_num) (by norm_num))
    -- `2^{-2000}` as one term, which `linarith` does not evaluate
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 1 / 2 ^ 2000 := ⟨_, rfl⟩
    rw [← ht] at hlog hsmall
    obtain ⟨l1, l2⟩ := abs_le.mp hlog
    have hXt : |Real.log (dwVal (ln8Xh p S x))| ≤ 7452 / 10 := by
      show |Real.log ((ln8Xh p S x).1 + (ln8Xh p S x).2)| ≤ 7452 / 10
      rw [abs_le]
      constructor <;> linarith
    have hb := prop44_ln_dd p hp S hS (ln8Xh p S x) hdw hpos hXt w hw0 hw1 j₁ j₂ f fφ ft fc hrun
    have hL := prop44_ln_dd_dw p hp S hS (ln8Xh p S x) hdw hpos hXt w hw0 hw1 j₁ j₂ f fφ ft fc hrun
    obtain ⟨hAdw, hAerr⟩ := accDWPlusDW_good p (by omega) hL (ln8CL_dw p hp)
    rw [← est] at hAdw hAerr
    obtain ⟨hy0, hyd, hy2⟩ := pairExp_dw p hAdw
    rw [← hy] at hy0 hyd hy2
    rw [two_zpow_neg_1071] at hb
    refine thm42_8_both p hp S hS x hx hH hX0 hX' y0 hy0 hyd hy2 (Or.inr ⟨hbig, _, _, hb, ?_⟩) k₁ k₂ hk hk2 e hsel
      eφ et ec hUφ hselt hUc
    rw [hy]
    exact hAerr

end ExpansionBounds
