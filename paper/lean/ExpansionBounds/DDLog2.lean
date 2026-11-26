import ExpansionBounds.DDLog2.All
import ExpansionBounds.DDLogCase
import ExpansionBounds.DDLogDW

/-!
# Proposition 44 (`prop:ddexplog`): `DD::ln` within `15.351u²|ln x| + 2^{-1071}`

`DD::ln` at `p = 53`: LOG with `s = 1`, `d = 27` and `q = 3` on double words, with multidouble's constants and
binary64's subnormals, from the start `y_0 = RN(ln_b(x_h) + w)`, `w` the computed quotient `x_l/x_h`. The four
double-word operations are those of `DDOps.lean`, with their published bounds as hypotheses (`DWSpec`).

This file has the pieces of the proof that do not depend on the case: the constants (`ddl_consts`), the
coefficients `F'_i` as double words (`ddlF_dw`), the bounds of step (2)'s `U` for a double word (`dd2U_ge`,
`dd2U_low`, `dd2U_lt`), the floors of step (5) at any `C ≤ 2^{-40}` (`ddl_floor5`), and the reduction of
`(-y_0, 0)` (`ddl_run`).
-/

namespace ExpansionBounds

open Finset

set_option maxHeartbeats 4000000 in
/-- the constants of `DDLog2/Data.lean` are bounds of what they stand for; `α_0 < 1/2` and `ȳ ≤ 745.3` for the
reduction of `(-y_0, 0)`; `e = -1` selects no `|r|`; the least `ℓ` with `k ≠ 0`; and the signs -/
theorem ddl_consts : ddlA0 < 1 / 2 ∧ ddlYB ≤ 7453 / 10 ∧ ddlDelta ddlRMax ≤ dyQ ddlDStarS ∧
    ddlRMax + dyQ ddlDStarS ≤ dyQ ddlTop1S ∧ 1 / (2 * cr8) ≤ dyQ ddlTop0S ∧
    dyQ ddlTop0S < (2 : ℚ) ^ (-1 : ℤ) * (1 - 1 / 2 ^ 46) ∧ dyQ ddlTop1S < (2 : ℚ) ^ (-1 : ℤ) * (1 - 1 / 2 ^ 46) ∧
    (1 + ddlE1) * dyQ ddlLkS + ddlE0 ≤ 1 / (2 * cr8 * (1 + red8U)) ∧ 0 ≤ dyQ ddlLkS ∧ dyQ ddlLkS ≤ red8X ∧
    0 ≤ ddlE1 ∧ ddlE1 < 1 ∧ 0 ≤ ddlE0 ∧ 0 ≤ dyQ ddlDStarS ∧ 0 ≤ red8EpsK := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the floors of steps (4) and (5), checked once: the products of two factors of magnitude at least
`2^{-131}(1 - 2^{-46})`, or of one and `l_v = 1/4`, or of one and `(1 - e_F)(1 - h̄)` at `C = 2^{-40}`, are above
`2^{-967}`; and `l_v ≤ 1/j - C v_{j+1} - e_j` at `C = 2^{-40}` for `j = 2, 3` -/
theorem ddl_floors : dd2Floor * (1 + red8U) ≤ (1 - ePQ red8U) * (ddlLow * ddlLow) ∧
    dd2Floor * (1 + red8U) ≤ (1 - ePQ red8U) * (ddlLow * ddlLv) ∧
    dd2Floor * (1 + red8U) ≤ (1 - ePQ red8U) * (ddlLow * ((1 - eFQ red8U) *
      (1 - ddLogHbQ red8U (2 * dd2Eta) ddlCg ddlPhi 3))) ∧
    (∀ j : ℕ, 2 ≤ j → j ≤ 3 → ddlLv ≤ 1 / (j : ℚ) - (ddlCg * ddLogVQ ddlCg 3 (j + 1) +
      ddHornerBQ red8U ddlCg (2 * dd2Eta) ddlPhi (ddLogVQ ddlCg 3) 3 (3 - j))) ∧
    ddlCg < 1 ∧ 0 ≤ ddlLow := by
  decide +kernel

/-- the pairs `F'_i` are double words: each part is a float and the high part is the rounded sum -/
theorem ddl_table : ∀ i : ℕ, i < 4 → rnQ 53 (ddlFQ i).1 = (ddlFQ i).1 ∧ rnQ 53 (ddlFQ i).2 = (ddlFQ i).2 ∧
    rnQ 53 ((ddlFQ i).1 + (ddlFQ i).2) = (ddlFQ i).1 := by
  decide +kernel

/-- `F'_i` as a pair of reals -/
noncomputable def ddlF (i : ℕ) : ℝ × ℝ := (((ddlFQ i).1 : ℝ), ((ddlFQ i).2 : ℝ))

/-- past the table the pair is zero -/
theorem ddlFQ_of_le {i : ℕ} (h : 4 ≤ i) : ddlFQ i = (0, 0) := by
  unfold ddlFQ
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using h)]
  rfl

variable (p : ℤ) [Prec_gt_0 p]

/-- each `F'_i` is a double word -/
theorem ddlF_dw (hp : p = 53) (i : ℕ) : DW p (ddlF i) := by
  subst hp
  rcases Nat.lt_or_ge i 4 with h | h
  · obtain ⟨t1, t2, t3⟩ := ddl_table i h
    refine ⟨?_, ?_, ?_⟩
    · show F 53 (((ddlFQ i).1 : ℚ) : ℝ)
      rw [F_iff_rn]
      exact t1
    · show F 53 (((ddlFQ i).2 : ℚ) : ℝ)
      rw [F_iff_rn]
      exact t2
    · show RN 53 ((((ddlFQ i).1 : ℚ) : ℝ) + (((ddlFQ i).2 : ℚ) : ℝ)) = (((ddlFQ i).1 : ℚ) : ℝ)
      rw [← Rat.cast_add, ← cast_rn, t3]
  · have h0 : ddlF i = (0, 0) := by
      unfold ddlF
      rw [ddlFQ_of_le h]
      simp
    rw [h0]
    exact DW.of_F 53 (F_zero 53)

omit [Prec_gt_0 p] in
/-- `F'_i` is within `φ'_i` of `(-1)^{i+1}/i` -/
theorem ddlF_err (i : ℕ) : |dwVal (ddlF i) - logFe i| ≤ ((ddlPhi i : ℚ) : ℝ) := by
  unfold ddlPhi ddlF dwVal logFe
  push_cast
  exact le_rfl

/-- `|v_h| + |v_l| ≤ U` for step (2)'s `U` of a pair -/
theorem dd2U_ge (hp : p = 53) (v : ℝ × ℝ) : |v.1| + |v.2| ≤ dd2U p v := by
  have hu := red8U_cast p hp
  obtain ⟨-, -, -, -, -, -, -, cγ, -⟩ := dd2_consts
  have hsum : ∑ i ∈ range 2, |(fun i : ℕ => if i = 0 then v.1 else v.2) i| = |v.1| + |v.2| := by
    simp [sum_range_succ]
  have hγ : (1 + u p) ^ 2 ≤ 1 + (2 : ℝ) ^ (-48 : ℤ) := by
    have h1 := (Rat.cast_le (K := ℝ)).mpr cγ
    push_cast at h1
    rw [hu] at h1
    exact h1.trans_eq (by norm_num)
  unfold dd2U
  rw [← hsum]
  exact expU_ge p 2 (by norm_num) _ hγ _

/-- the exponent `e` of `U` bounds the pair: `|v_h| + |v_l| < 2^{e+1}`, also where `U < 2^{-1022}` and
`e = -1023` -/
theorem dd2U_lt (hp : p = 53) (v : ℝ × ℝ) {e : ℤ}
    (hsel : ((2 : ℝ) ^ e ≤ dd2U p v ∧ dd2U p v < (2 : ℝ) ^ (e + 1)) ∨
      (dd2U p v < (2 : ℝ) ^ (-1022 : ℤ) ∧ e = -1023)) : |v.1| + |v.2| < (2 : ℝ) ^ (e + 1) := by
  have hSU := dd2U_ge p hp v
  rcases hsel with ⟨-, h2⟩ | ⟨h2, he⟩
  · exact hSU.trans_lt h2
  · rw [he]
    exact (hSU.trans_lt h2).trans_eq (by norm_num)

/-- the lower end of the double words `v` whose `U` is at least `2^e`: `|v| ≥ 2^e(1 - 2^{-46})`, from the two
roundings of `U`, its factor `1 + 2^{-48}` and `|v_l| ≤ u|v_h|` -/
theorem dd2U_low (hp : p = 53) {v : ℝ × ℝ} (hv : DW p v) {e : ℤ} (h2 : (2 : ℝ) ^ e ≤ dd2U p v) :
    (2 : ℝ) ^ e * (1 - 1 / 2 ^ 46) ≤ |dwVal v| := by
  have hu := red8U_cast p hp
  have hup := u_pos p
  have hu53 := u_53 p hp
  obtain ⟨-, -, -, -, -, -, -, -, cC⟩ := dd2_consts
  have hsum : ∑ i ∈ range 2, |(fun i : ℕ => if i = 0 then v.1 else v.2) i| = |v.1| + |v.2| := by
    simp [sum_range_succ]
  have hrl := (DW.parts p hv).1
  have h3 := expU_le p 2 (by norm_num) ((2 : ℝ) ^ (-48 : ℤ)) (by positivity) fun i => if i = 0 then v.1 else v.2
  rw [hsum] at h3
  have h3' : dd2U p v ≤ (1 + u p) ^ 2 * (1 + (2 : ℝ) ^ (-48 : ℤ)) * (|v.1| + |v.2|) := h3
  have h5 : (1 - u p) * (|v.1| + |v.2|) ≤ (1 + u p) * |dwVal v| := by
    have h6 : |v.1| - |v.2| ≤ |dwVal v| := by
      have := abs_sub_abs_le_abs_sub v.1 (-v.2)
      rw [abs_neg, sub_neg_eq_add] at this
      exact this
    nlinarith [abs_nonneg v.1, abs_nonneg v.2]
  have hK2 : (0 : ℝ) < (1 + u p) ^ 2 * (1 + (2 : ℝ) ^ (-48 : ℤ)) := by positivity
  have he0 : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  obtain ⟨K, hKd⟩ : ∃ K, K = (1 + u p) * ((1 + u p) ^ 2 * (1 + (2 : ℝ) ^ (-48 : ℤ))) := ⟨_, rfl⟩
  have hK : 0 < K := by rw [hKd]; positivity
  have h4 : (1 - 1 / 2 ^ 46 : ℝ) * K ≤ 1 - u p := by
    have h1 := (Rat.cast_le (K := ℝ)).mpr cC
    push_cast at h1
    rw [hu] at h1
    rw [hKd]
    exact (le_of_eq (by norm_num)).trans h1
  have h7 : (2 : ℝ) ^ e * (1 - u p) ≤ K * |dwVal v| := by
    have h8 : (2 : ℝ) ^ e * (1 - u p) ≤
        (1 + u p) ^ 2 * (1 + (2 : ℝ) ^ (-48 : ℤ)) * (|v.1| + |v.2|) * (1 - u p) :=
      mul_le_mul_of_nonneg_right (h2.trans h3') (by rw [hu53]; norm_num)
    have h9 : (1 + u p) ^ 2 * (1 + (2 : ℝ) ^ (-48 : ℤ)) * ((1 - u p) * (|v.1| + |v.2|)) ≤
        (1 + u p) ^ 2 * (1 + (2 : ℝ) ^ (-48 : ℤ)) * ((1 + u p) * |dwVal v|) := mul_le_mul_of_nonneg_left h5 hK2.le
    calc (2 : ℝ) ^ e * (1 - u p) ≤ (1 + u p) ^ 2 * (1 + (2 : ℝ) ^ (-48 : ℤ)) * (|v.1| + |v.2|) * (1 - u p) := h8
      _ = (1 + u p) ^ 2 * (1 + (2 : ℝ) ^ (-48 : ℤ)) * ((1 - u p) * (|v.1| + |v.2|)) := by ring
      _ ≤ (1 + u p) ^ 2 * (1 + (2 : ℝ) ^ (-48 : ℤ)) * ((1 + u p) * |dwVal v|) := h9
      _ = K * |dwVal v| := by rw [hKd]; ring
  have h10 : (2 : ℝ) ^ e * ((1 - 1 / 2 ^ 46) * K) ≤ (2 : ℝ) ^ e * (1 - u p) :=
    mul_le_mul_of_nonneg_left h4 he0.le
  refine le_of_mul_le_mul_right ?_ hK
  calc (2 : ℝ) ^ e * (1 - 1 / 2 ^ 46) * K = (2 : ℝ) ^ e * ((1 - 1 / 2 ^ 46) * K) := by ring
    _ ≤ (2 : ℝ) ^ e * (1 - u p) := h10
    _ ≤ K * |dwVal v| := h7
    _ = |dwVal v| * K := by ring

omit [Prec_gt_0 p] in
/-- `2^{-967}` and `η_0 = 2^{-1075}` as casts -/
theorem ddl_casts : ((dd2Floor : ℚ) : ℝ) = (2 : ℝ) ^ (-967 : ℤ) ∧ ((dd2Eta : ℚ) : ℝ) = (2 : ℝ) ^ (-1075 : ℤ) ∧
    ((2 * dd2Eta : ℚ) : ℝ) = 2 * (2 : ℝ) ^ (-1075 : ℤ) := by
  have hfl : ((dd2Floor : ℚ) : ℝ) = (2 : ℝ) ^ (-967 : ℤ) := by
    unfold dd2Floor
    rw [show (-967 : ℤ) = -((967 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast, ← one_div]
    simp only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat]
  have heta : ((dd2Eta : ℚ) : ℝ) = (2 : ℝ) ^ (-1075 : ℤ) := cast_exp8Eta
  refine ⟨hfl, heta, ?_⟩
  rw [Rat.cast_mul, heta, Rat.cast_ofNat]

omit [Prec_gt_0 p] in
/-- the floors of steps (4) and (5) at any `0 ≤ C ≤ 2^{-40}`, with `l_φ = l_t = l_c = 2^{-131}(1 - 2^{-46})` and
`l_v = 1/4`: Horner's iterates are at least `l_v`, and each scaled-back product keeps its high part above
`2^{-967}` -/
theorem ddl_floor5 (hp : p = 53) {C : ℝ} (hC0 : 0 ≤ C) (hC : C ≤ ((ddlCg : ℚ) : ℝ)) :
    (∀ j : ℕ, 2 ≤ j → j ≤ 3 → ((ddlLv : ℚ) : ℝ) ≤ 1 / (j : ℝ) - C * logV C 3 (j + 1) -
      ddHornerB p C (2 * (2 : ℝ) ^ (-1075 : ℤ)) (fun k => ddlPhi k) (logV C 3) 3 (3 - j)) ∧
      (2 : ℝ) ^ (-967 : ℤ) * (1 + u p) ≤ (1 - eP p) * (((ddlLow : ℚ) : ℝ) * ((ddlLv : ℚ) : ℝ)) ∧
      (2 : ℝ) ^ (-967 : ℤ) * (1 + u p) ≤ (1 - eP p) * (((ddlLow : ℚ) : ℝ) *
        ((1 - eF p) * (1 - ddLogHb p (2 * (2 : ℝ) ^ (-1075 : ℤ)) C (fun k => ddlPhi k) 3))) ∧
      (2 : ℝ) ^ (-967 : ℤ) * (1 + u p) ≤ (1 - eP p) * (((ddlLow : ℚ) : ℝ) * ((ddlLow : ℚ) : ℝ)) := by
  have hu := red8U_cast p hp
  have h4 := four_u_lt p hp
  obtain ⟨hfl, -, heta2⟩ := ddl_casts
  obtain ⟨f1, f2, f3, f4, -, f6⟩ := ddl_floors
  have hφ' : ∀ k, (0 : ℝ) ≤ ((ddlPhi k : ℚ) : ℝ) := fun k => by
    have : (0 : ℚ) ≤ ddlPhi k := abs_nonneg _
    exact_mod_cast this
  have hD : (0 : ℝ) ≤ 2 * (2 : ℝ) ^ (-1075 : ℤ) := by positivity
  have hLow : (0 : ℝ) ≤ ((ddlLow : ℚ) : ℝ) := by exact_mod_cast f6
  have h1eP : 0 ≤ 1 - eP p := by linarith [eP_le_one p h4]
  have h1eF : 0 ≤ 1 - eF p := by linarith [eF_le_one p h4]
  have hv : (fun k => ((ddLogVQ ddlCg 3 k : ℚ) : ℝ)) = logV ((ddlCg : ℚ) : ℝ) 3 :=
    funext fun k => cast_ddLogVQ ddlCg 3 k
  refine ⟨fun j hj2 hj3 => ?_, ?_, ?_, ?_⟩
  · have h1 := (Rat.cast_le (K := ℝ)).mpr (f4 j hj2 hj3)
    rw [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_add, Rat.cast_mul, cast_ddLogVQ,
      cast_ddHornerBQ p hu, hv, heta2] at h1
    have h2 := ddLogLv_mono p h4 hC0 hC hD hφ' 3 j
    linarith
  · have h1 := (Rat.cast_le (K := ℝ)).mpr f2
    rw [Rat.cast_mul, Rat.cast_add, Rat.cast_one, Rat.cast_mul, Rat.cast_sub, Rat.cast_one, Rat.cast_mul,
      cast_ePQ p hu, hu, hfl] at h1
    exact h1
  · have h1 := (Rat.cast_le (K := ℝ)).mpr f3
    rw [Rat.cast_mul, Rat.cast_add, Rat.cast_one, Rat.cast_mul, Rat.cast_sub, Rat.cast_one, Rat.cast_mul,
      Rat.cast_mul, Rat.cast_sub, Rat.cast_one, Rat.cast_sub, Rat.cast_one, cast_ePQ p hu, cast_eFQ p hu,
      cast_ddLogHbQ p hu, hu, hfl, heta2] at h1
    have h2 := ddLogHb_mono p h4 hC0 hC hD hφ' 3
    refine h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ h1eF) hLow)
      h1eP)
    linarith
  · have h1 := (Rat.cast_le (K := ℝ)).mpr f1
    rw [Rat.cast_mul, Rat.cast_add, Rat.cast_one, Rat.cast_mul, Rat.cast_sub, Rat.cast_one, Rat.cast_mul,
      cast_ePQ p hu, hu, hfl] at h1
    exact h1

omit [Prec_gt_0 p] in
/-- the reduction's `δ` for a zero low part is at most its mirror's value -/
theorem ddl_red_le (hp : p = 53) (rb : ℚ) :
    ddRedDelta p ((ch8 : ℚ) : ℝ) dd2Cl 0 rb ≤ ((ddlDelta rb : ℚ) : ℝ) := by
  have hu := red8U_cast p hp
  obtain ⟨lA, lB⟩ := log_two_600
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
  have hEq : ddRedEq p dd2Cl 0 = ((ddlEq : ℚ) : ℝ) := by
    unfold ddRedEq ddlEq
    rw [hC, hE1, Rat.cast_mul, hcF]
    push_cast
    ring
  unfold ddRedDelta ddRedE2 ddlDelta
  rw [hE1, hEq]
  push_cast
  rw [hcF]
  nlinarith [eF_nonneg p]

/-- the reduction of `(-y_0, 0)` for `|y_0| ≤ ȳ`: `r` is a double word; for `k = 0`, `r = (-y_0, 0)` and
`|y_0|c_r < 1/2`; for `k ≠ 0`, `|y_0|c_r(1 + u) ≥ 1/2`, `|r|` is at most the bound of `DDLog2/Data.lean`, and `r` is
within `δ` at `r̄ = b + δ*` of `r_e` for every rational `b ≥ |r|` -/
theorem ddl_run (hp : p = 53) {O : DWOps} (hO : DWSpec p O) (y0 : ℝ) (hy0 : F p y0)
    (hyb : |y0| ≤ ((ddlYB : ℚ) : ℝ)) :
    DW p (dd2R p O (-y0, 0)) ∧
      (expK p (-y0) = 0 → dd2R p O (-y0, 0) = (-y0, 0) ∧ |y0| * ((cr8 : ℚ) : ℝ) < 1 / 2) ∧
      (expK p (-y0) ≠ 0 → 1 / 2 ≤ |y0| * ((cr8 : ℚ) : ℝ) * (1 + u p) ∧
        |dwVal (dd2R p O (-y0, 0))| ≤ ((dyQ ddlTop1S : ℚ) : ℝ) ∧
        ∀ b : ℚ, |dwVal (dd2R p O (-y0, 0))| ≤ b →
          |dwVal (dd2R p O (-y0, 0)) - (-y0 - expK p (-y0) * Real.log 2)| ≤
            ((ddlDelta (b + dyQ ddlDStarS) : ℚ) : ℝ)) := by
  have hu := red8U_cast p hp
  have hup := u_pos p
  have hp14 : 14 ≤ p := by omega
  obtain ⟨cA0, cY, cD, cT1, -, -, -, -, -, -, -, -, -, cD0, kE⟩ := ddl_consts
  obtain ⟨-, -, -, -, -, -, ccr, -, -⟩ := dd2_consts
  obtain ⟨lA, lB⟩ := log_two_600
  obtain ⟨kA, -, -, -⟩ := red8_check
  have hApos : (0 : ℝ) < ((ln2A : ℚ) : ℝ) := by exact_mod_cast kA
  have hL0 : 0 < Real.log 2 := lt_of_lt_of_le hApos lA
  have hcr : (0 : ℝ) < ((cr8 : ℚ) : ℝ) := by exact_mod_cast ccr
  have hinv1 : 1 / ((ln2B : ℚ) : ℝ) ≤ 1 / Real.log 2 := one_div_le_one_div_of_le hL0 lB
  have hinv2 : 1 / Real.log 2 ≤ 1 / ((ln2A : ℚ) : ℝ) := one_div_le_one_div_of_le hApos lA
  have hDl : |cR p - 1 / Real.log 2| ≤ ((red8Dl : ℚ) : ℝ) := by
    rw [cR_eq p hp]
    have h := abs_sub_le_max (c := ((cr8 : ℚ) : ℝ)) hinv1 hinv2
    simpa [red8Dl] using h
  have hY0 : (0 : ℝ) ≤ ((ddlYB : ℚ) : ℝ) := (abs_nonneg _).trans hyb
  have hEps : epsK p ((ddlYB : ℚ) : ℝ) ≤ ((ddlYB : ℚ) : ℝ) * (((red8Dl : ℚ) : ℝ) + u p * ((cr8 : ℚ) : ℝ)) := by
    unfold epsK
    rw [cR_eq p hp]
    rw [cR_eq p hp] at hDl
    exact mul_le_mul_of_nonneg_left (by linarith) hY0
  have hRM : rMax p ((ddlYB : ℚ) : ℝ) 0 ≤ ((ddlRMax : ℚ) : ℝ) := by
    unfold rMax
    rw [show ((ddlRMax : ℚ) : ℝ) = (1 / 2 + (ddlYB : ℝ) * ((red8Dl : ℝ) + u p * (cr8 : ℝ))) * (ln2B : ℝ) by
      rw [← hu]; simp [ddlRMax]]
    have hDl0 : (0 : ℝ) ≤ ((red8Dl : ℚ) : ℝ) := (abs_nonneg _).trans hDl
    have hE0 : (0 : ℝ) ≤ 1 / 2 + ((ddlYB : ℚ) : ℝ) * (((red8Dl : ℚ) : ℝ) + u p * ((cr8 : ℚ) : ℝ)) := by positivity
    have hK0 : 0 ≤ epsK p ((ddlYB : ℚ) : ℝ) := by
      unfold epsK
      rw [cR_eq p hp]
      positivity
    linarith [mul_le_mul (add_le_add (le_refl (1 / 2 : ℝ)) hEps) lB hL0.le hE0]
  have hDe : |Real.log 2 - ((ch8 : ℚ) : ℝ)| ≤ ((max |ch8 - ln2A| |ch8 - ln2B| : ℚ) : ℝ) := by
    rw [abs_sub_comm]
    have h := abs_sub_le_max (c := ((ch8 : ℚ) : ℝ)) lA lB
    simpa using h
  have hA0 : expA0 p ((ddlYB : ℚ) : ℝ) 0 ((ch8 : ℚ) : ℝ) ≤ ((ddlA0 : ℚ) : ℝ) := by
    unfold expA0
    rw [show ((ddlA0 : ℚ) : ℝ) = (ddlRMax : ℝ) + 1075 * ((max |ch8 - ln2A| |ch8 - ln2B| : ℚ) : ℝ) by
      simp [ddlA0]]
    linarith
  have hX0 : |((-y0, (0 : ℝ)) : ℝ × ℝ).1| ≤ ((ddlYB : ℚ) : ℝ) := by
    show |-y0| ≤ _
    rw [abs_neg]
    exact hyb
  have hX1 : ((ddlYB : ℚ) : ℝ) ≤ 745.3 := by
    have := (Rat.cast_le (K := ℝ)).mpr cY
    push_cast at this
    linarith
  have hxt : |((-y0, (0 : ℝ)) : ℝ × ℝ).2| ≤ (0 : ℝ) := by simp
  have hA0lt : expA0 p ((ddlYB : ℚ) : ℝ) 0 ((ch8 : ℚ) : ℝ) < 1 / 2 :=
    hA0.trans_lt (lt_of_lt_of_eq (Rat.cast_lt.mpr cA0) (by norm_num))
  have hzdw : DW p ((-y0, (0 : ℝ)) : ℝ × ℝ) := DW.of_F p (F_neg p hy0)
  obtain ⟨-, a2, -, -⟩ := dd_expred_a p hp14 (-y0, 0) hzdw.1 _ _ _ hX0 hX1 hxt (ch8_mult p hp) hA0lt
  have hval : dwVal ((-y0, (0 : ℝ)) : ℝ × ℝ) = -y0 := by simp [dwVal]
  rw [hval] at a2
  have hD0 : (0 : ℝ) ≤ ((dyQ ddlDStarS : ℚ) : ℝ) := Rat.cast_nonneg.mpr cD0
  by_cases hk0 : expK p (-y0) = 0
  · have hrx : dd2R p O (-y0, 0) = (-y0, 0) := by
      unfold dd2R ddExpR
      simp only [hk0, ↓reduceIte]
    refine ⟨by rw [hrx]; exact hzdw, fun _ => ⟨hrx, ?_⟩, fun h => absurd hk0 h⟩
    have h1 := abs_lt_half_of_RN p (roundAway_eq_zero hk0)
    rw [cR_eq p hp, abs_mul, abs_neg, abs_of_pos hcr] at h1
    exact h1
  · obtain ⟨b1, b2⟩ := dd_expred_b p hp14 hO (-y0, 0) hzdw _ _ _ dd2Cl (dd2Cl_dw p hp) hX0 hX1 hxt
      (ch8_mult p hp) hA0lt hk0 ((ddlRMax : ℚ) : ℝ) (by rw [hval]; exact a2.trans hRM)
    rw [hval] at b1
    obtain ⟨R, hR⟩ : ∃ R, R = dwVal (dd2R p O (-y0, 0)) := ⟨_, rfl⟩
    obtain ⟨re, hre⟩ : ∃ re, re = -y0 - expK p (-y0) * Real.log 2 := ⟨_, rfl⟩
    have a2' : |re| ≤ ((ddlRMax : ℚ) : ℝ) := by rw [hre]; exact a2.trans hRM
    have hδs : |R - re| ≤ ((dyQ ddlDStarS : ℚ) : ℝ) := by
      rw [hR, hre]
      exact b1.trans ((ddl_red_le p hp ddlRMax).trans (Rat.cast_le.mpr cD))
    rw [← hR, ← hre]
    refine ⟨b2, fun h => absurd h hk0, fun _ => ⟨?_, ?_, fun b hb => ?_⟩⟩
    · have h1 : 1 / 2 ≤ |RN p (-y0 * cR p)| := roundAway_ne_zero hk0
      have h3 : |-y0 * cR p| = |y0| * ((cr8 : ℚ) : ℝ) := by rw [abs_mul, abs_neg, cR_eq p hp, abs_of_pos hcr]
      have h2 := abs_RN_le p (-y0 * cR p)
      rw [h3] at h2
      calc (1 : ℝ) / 2 ≤ |RN p (-y0 * cR p)| := h1
        _ ≤ (1 + u p) * (|y0| * ((cr8 : ℚ) : ℝ)) := h2
        _ = |y0| * ((cr8 : ℚ) : ℝ) * (1 + u p) := by ring
    · have hT := (Rat.cast_le (K := ℝ)).mpr cT1
      rw [Rat.cast_add] at hT
      have h1 := abs_sub_abs_le_abs_sub R re
      linarith only [h1, hT, a2', hδs]
    · have h1 := abs_sub_abs_le_abs_sub re R
      rw [abs_sub_comm re R] at h1
      have hreb : |re| ≤ ((b + dyQ ddlDStarS : ℚ) : ℝ) := by
        rw [Rat.cast_add]
        linarith only [h1, hδs, hb]
      obtain ⟨b3, -⟩ := dd_expred_b p hp14 hO (-y0, 0) hzdw _ _ _ dd2Cl (dd2Cl_dw p hp) hX0 hX1 hxt
        (ch8_mult p hp) hA0lt hk0 ((b + dyQ ddlDStarS : ℚ) : ℝ) (by rw [hval, ← hre]; exact hreb)
      rw [hval] at b3
      rw [hR, hre]
      exact b3.trans (ddl_red_le p hp _)

omit [Prec_gt_0 p] in
/-- `2^{-131}(1 - 2^{-46}) ≤ 2^e(1 - 2^{-46})` for `e ≥ -131` -/
theorem ddlLow_le {e : ℤ} (he : -131 ≤ e) : ((ddlLow : ℚ) : ℝ) ≤ (2 : ℝ) ^ e * (1 - 1 / 2 ^ 46) := by
  have h1 : ((ddlLow : ℚ) : ℝ) = (2 : ℝ) ^ (-131 : ℤ) * (1 - 1 / 2 ^ 46) := by
    unfold ddlLow
    rw [show (-131 : ℤ) = -((131 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast, ← one_div]
    push_cast
    ring
  rw [h1]
  exact mul_le_mul_of_nonneg_right (zpow_le_zpow_right₀ (by norm_num) he) (by norm_num)

/-- `DD::ln` for a run whose case is known, with both conclusions: with the start within `E` of `ln x`, the
reduction's `r` within `δ` of `r_e`, `a ≤ |r| ≤ b` and its sign, and the facts `DDLAt` of the case at `ℓ = |ln x|`
with a target `T`, the result is a double word within `T` of `ln x`. The exponents `e_φ`, `e_t` and `e_c` are those
of step (2)'s `U` for `φ`, `t` and `c` -/
theorem ddl_core_both (hp : p = 53) {O : DWOps} (hO : DWSpec p O) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℝ × ℝ) (hx : DW p x) (hX0 : 0 < dwVal x) (y0 : ℝ) (hy0 : F p y0) {E : ℝ}
    (hE : |y0 - Real.log (dwVal x)| ≤ E) (k₁ k₂ : ℤ) (hk : k₁ + k₂ = expK p (-y0)) (hk2 : k₂ ≤ 0) {δ b : ℝ}
    {a : ℚ} (hr : DW p (dd2R p O (-y0, 0)))
    (hδ : |dwVal (dd2R p O (-y0, 0)) - (-y0 - expK p (-y0) * Real.log 2)| ≤ δ) (ha0 : 0 ≤ a)
    (ha : (a : ℝ) ≤ |dwVal (dd2R p O (-y0, 0))|) (hb : |dwVal (dd2R p O (-y0, 0))| ≤ b) (pos : Bool)
    (hsgn : if pos then 0 ≤ dwVal (dd2R p O (-y0, 0)) else dwVal (dd2R p O (-y0, 0)) ≤ 0) (e eφ et ec : ℤ)
    (hd : 1 ≤ ddDeg e)
    (hselφ : ((2 : ℝ) ^ eφ ≤ dd2U p (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) ∧
        dd2U p (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) < (2 : ℝ) ^ (eφ + 1)) ∨
      (dd2U p (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) < (2 : ℝ) ^ (-1022 : ℤ) ∧ eφ = -1023))
    (hselt : ((2 : ℝ) ^ et ≤ dd2U p (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e)) ∧
        dd2U p (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e)) < (2 : ℝ) ^ (et + 1)) ∨
      (dd2U p (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e)) < (2 : ℝ) ^ (-1022 : ℤ) ∧
        et = -1023))
    (hselc : ((2 : ℝ) ^ ec ≤ dd2U p (ddLogC O (ddS2 S et) 118 eφ et (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x)
          (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e))) ∧
        dd2U p (ddLogC O (ddS2 S et) 118 eφ et (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x)
          (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e))) < (2 : ℝ) ^ (ec + 1)) ∨
      (dd2U p (ddLogC O (ddS2 S et) 118 eφ et (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x)
          (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e))) < (2 : ℝ) ^ (-1022 : ℤ) ∧
        ec = -1023))
    (hφex : dwVal (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) = dwVal (ddS2 S k₂ (dwScale (k₁ + k₂) x)) - 1) {T : ℝ}
    (hat : DDLAt p pos (ddDeg e) a |Real.log (dwVal x)| E b δ T) :
    DW p (ddLogOp O (ddS2 S k₂) (ddS2 S et) (fun v => (S v.1, S v.2)) y0 x (k₁ + k₂)
        (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e)) 118 eφ et ec ddlF 3) ∧
      |dwVal (ddLogOp O (ddS2 S k₂) (ddS2 S et) (fun v => (S v.1, S v.2)) y0 x (k₁ + k₂)
          (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e)) 118 eφ et ec ddlF 3) -
        Real.log (dwVal x)| ≤ T := by
  have hu := red8U_cast p hp
  have h4 := four_u_lt p hp
  have hup := u_pos p
  have hu53 := u_53 p hp
  obtain ⟨hfl, heta, heta2⟩ := ddl_casts
  obtain ⟨hB, hC0, hCg, hfloor, hb12, hEm, hsum⟩ := hat
  rw [heta, heta2] at hB hC0 hCg
  rw [heta] at hEm
  rw [hfl] at hfloor
  obtain ⟨r, hrd⟩ : ∃ r, r = dd2R p O (-y0, 0) := ⟨_, rfl⟩
  rw [← hrd] at hr hδ ha hb hsgn hselt hselc ⊢
  obtain ⟨d', hd'⟩ : ∃ d', d' = ddDeg e := ⟨_, rfl⟩
  rw [← hd'] at hd hselt hselc hB hC0 hCg hfloor hEm ⊢
  have hE0 : 0 ≤ E := (abs_nonneg _).trans hE
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hδ
  have hb0 : 0 ≤ b := (abs_nonneg _).trans hb
  have ha0r : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha0
  have hbd : b < (d' : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (d' : ℝ) := Nat.cast_nonneg d'
    linarith
  have hφF : ∀ k, |dwVal (dd2F k) - invF k| ≤ ((dd2Phi k : ℚ) : ℝ) := fun k => by
    unfold dd2Phi dd2F dwVal invF
    push_cast
    exact le_rfl
  have hSg := SclDW.of_grid p hp S hS
  -- EXP's core: `t` is a double word below `1` in magnitude
  obtain ⟨c1, c2, c3⟩ := dd_core p hO h4 hSg r hr a b ha0r ha hb e d' hd hbd dd2F (dd2F_dw p hp)
    (fun k => ((dd2Phi k : ℚ) : ℝ)) hφF pos hsgn hfloor
  obtain ⟨t, htd⟩ : ∃ t, t = ddExpT O (fun v => (S v.1, S v.2)) e r dd2F d' := ⟨_, rfl⟩
  rw [← htd] at c1 c2 hselt hselc ⊢
  have hexp : Real.exp (1 / 2) ≤ 17 / 10 := by
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  have hT1 : |dwVal t| ≤ 19 / 20 := by
    have h1 := abs_exp_sub_one_le (dwVal r)
    have h2 := Real.exp_le_exp.mpr (hb.trans hb12)
    have h3 := abs_sub_abs_le_abs_sub (dwVal t) (Real.exp (dwVal r) - 1)
    linarith only [h1, h2, h3, c1, hEm, hexp]
  have het : et ≤ 0 := by
    by_contra hcon
    rcases hselt with ⟨h1, -⟩ | ⟨-, he⟩
    · have hl := dd2U_low p hp c2 h1
      have h6 : (2 : ℝ) ^ (1 : ℤ) ≤ (2 : ℝ) ^ et := zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h8 := mul_le_mul_of_nonneg_right h6 (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2 ^ 46)
      norm_num at h8
      linarith only [hl, h8, hT1]
    · omega
  -- `2^k x_h ≥ 1/4`, the floor of `x'`
  obtain ⟨X, hXd⟩ : ∃ X, X = dwVal x := ⟨_, rfl⟩
  have hX0' : 0 < X := hXd ▸ hX0
  have hE' : |y0 - Real.log X| ≤ E := hXd ▸ hE
  have hlox : (2 : ℝ) ^ (-967 : ℤ) ≤ |(2 : ℝ) ^ (k₁ + k₂) * x.1| := by
    have hre : |(-y0 - ((k₁ + k₂ : ℤ) : ℝ) * Real.log 2)| ≤ b + δ := by
      rw [hk]
      have := abs_sub_abs_le_abs_sub (-y0 - ((expK p (-y0) : ℤ) : ℝ) * Real.log 2) (dwVal r)
      rw [abs_sub_comm (-y0 - ((expK p (-y0) : ℤ) : ℝ) * Real.log 2) (dwVal r)] at this
      linarith only [this, hδ, hb]
    have hX' : (2 : ℝ) ^ (k₁ + k₂) * X =
        Real.exp (-(y0 - Real.log X) - (-y0 - ((k₁ + k₂ : ℤ) : ℝ) * Real.log 2)) := by
      rw [show -(y0 - Real.log X) - (-y0 - ((k₁ + k₂ : ℤ) : ℝ) * Real.log 2) =
        Real.log X + ((k₁ + k₂ : ℤ) : ℝ) * Real.log 2 by ring, Real.exp_add, Real.exp_log hX0', exp_int_mul_log_two,
        mul_comm]
    have hge : Real.exp (-1) ≤ (2 : ℝ) ^ (k₁ + k₂) * X := by
      rw [hX']
      exact Real.exp_le_exp.mpr (by linarith only [(abs_le.mp hE').2, (abs_le.mp hre).2, hsum])
    have he1 : (1 : ℝ) / 3 ≤ Real.exp (-1) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (Real.exp_pos 1) (by linarith only [Real.exp_one_lt_d9])
    have hxl := (DW.parts p hx).1
    have hXx : X ≤ (1 + u p) * |x.1| := by
      rw [hXd]
      have h9 : dwVal x ≤ |x.1| + |x.2| := (le_abs_self (x.1 + x.2)).trans (abs_add_le x.1 x.2)
      linarith only [h9, hxl]
    have h2k : (0 : ℝ) < (2 : ℝ) ^ (k₁ + k₂) := by positivity
    have h5 : (2 : ℝ) ^ (k₁ + k₂) * X ≤ (1 + u p) * ((2 : ℝ) ^ (k₁ + k₂) * |x.1|) := by
      have := mul_le_mul_of_nonneg_left hXx h2k.le
      linarith only [this]
    have h6 : (2 : ℝ) ^ (-967 : ℤ) ≤ 1 / 4 :=
      (zpow_le_zpow_right₀ (by norm_num) (by norm_num : (-967 : ℤ) ≤ -2)).trans_eq (by norm_num)
    rw [abs_mul, abs_of_pos h2k]
    rw [hu53] at h5
    refine h6.trans ?_
    linarith only [hge, he1, h5]
  -- the exponents bound the pairs
  have hUφ := dd2U_lt p hp _ hselφ
  have hUt := dd2U_lt p hp _ hselt
  have hUc := dd2U_lt p hp _ hselc
  obtain ⟨g1, g2, g3, g4⟩ := ddl_floor5 p hp hC0 hCg
  have hLow0 : (0 : ℝ) ≤ ((ddlLow : ℚ) : ℝ) := by exact_mod_cast ddl_floors.2.2.2.2.2
  have hCg1 : ((ddlCg : ℚ) : ℝ) < 1 := by exact_mod_cast ddl_floors.2.2.2.2.1
  have hthm := dd_thm42_case_sub_both p hp hO S hS x hx hX0 y0 hy0
    |Real.log (dwVal x)| E le_rfl hE r hr k₁ k₂ hk2 δ (by rw [hk]; exact hδ) a b ha0r ha hb pos hsgn e d' hd
    hbd dd2F (dd2F_dw p hp) (fun k => ((dd2Phi k : ℚ) : ℝ)) hφF hfloor hlox hφex 118 eφ et ec het hUφ
    (by rw [htd] at hUt; exact hUt) (by rw [htd] at hUc; exact hUc) ddlF (ddlF_dw p hp)
    (fun k => ((ddlPhi k : ℚ) : ℝ)) ddlF_err 3 (by norm_num) (coreT_le_ddTbC pos b)
    (logPhiB_le_ddPhiC _ pos E a b δ) le_rfl hLow0 hLow0
    (fun hmin hφdw htdw => by
      have h1 : -131 ≤ eφ ∧ -131 ≤ et := by
        constructor <;> omega
      refine ⟨?_, ?_, g4⟩
      · rcases hselφ with ⟨hs, -⟩ | ⟨-, he⟩
        · exact (ddlLow_le h1.1).trans (dd2U_low p hp hφdw hs)
        · omega
      · rcases hselt with ⟨hs, -⟩ | ⟨-, he⟩
        · exact (ddlLow_le h1.2).trans (dd2U_low p hp htdw (by rw [← htd]; exact hs))
        · omega)
    (fun hec hcdw => by
      refine ⟨?_, g1, g2, g3⟩
      rcases hselc with ⟨hs, -⟩ | ⟨-, he⟩
      · exact (ddlLow_le (e := ec) (by omega)).trans (dd2U_low p hp hcdw (by rw [← htd]; exact hs))
      · omega)
    (lt_of_le_of_lt hCg hCg1)
  rw [← htd] at hthm
  exact ⟨hthm.1, hthm.2.trans hB⟩

/-- `DD::ln` for a run whose case is known: with the start within `E` of `ln x`, the reduction's `r` within `δ` of
`r_e`, `a ≤ |r| ≤ b` and its sign, and the facts `DDLAt` of the case at `ℓ = |ln x|` with a target `T`, the result
is within `T` of `ln x`. The exponents `e_φ`, `e_t` and `e_c` are those of step (2)'s `U` for `φ`, `t` and `c` -/
theorem ddl_core (hp : p = 53) {O : DWOps} (hO : DWSpec p O) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℝ × ℝ) (hx : DW p x) (hX0 : 0 < dwVal x) (y0 : ℝ) (hy0 : F p y0) {E : ℝ}
    (hE : |y0 - Real.log (dwVal x)| ≤ E) (k₁ k₂ : ℤ) (hk : k₁ + k₂ = expK p (-y0)) (hk2 : k₂ ≤ 0) {δ b : ℝ}
    {a : ℚ} (hr : DW p (dd2R p O (-y0, 0)))
    (hδ : |dwVal (dd2R p O (-y0, 0)) - (-y0 - expK p (-y0) * Real.log 2)| ≤ δ) (ha0 : 0 ≤ a)
    (ha : (a : ℝ) ≤ |dwVal (dd2R p O (-y0, 0))|) (hb : |dwVal (dd2R p O (-y0, 0))| ≤ b) (pos : Bool)
    (hsgn : if pos then 0 ≤ dwVal (dd2R p O (-y0, 0)) else dwVal (dd2R p O (-y0, 0)) ≤ 0) (e eφ et ec : ℤ)
    (hd : 1 ≤ ddDeg e)
    (hselφ : ((2 : ℝ) ^ eφ ≤ dd2U p (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) ∧
        dd2U p (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) < (2 : ℝ) ^ (eφ + 1)) ∨
      (dd2U p (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) < (2 : ℝ) ^ (-1022 : ℤ) ∧ eφ = -1023))
    (hselt : ((2 : ℝ) ^ et ≤ dd2U p (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e)) ∧
        dd2U p (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e)) < (2 : ℝ) ^ (et + 1)) ∨
      (dd2U p (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e)) < (2 : ℝ) ^ (-1022 : ℤ) ∧
        et = -1023))
    (hselc : ((2 : ℝ) ^ ec ≤ dd2U p (ddLogC O (ddS2 S et) 118 eφ et (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x)
          (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e))) ∧
        dd2U p (ddLogC O (ddS2 S et) 118 eφ et (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x)
          (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e))) < (2 : ℝ) ^ (ec + 1)) ∨
      (dd2U p (ddLogC O (ddS2 S et) 118 eφ et (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x)
          (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e))) < (2 : ℝ) ^ (-1022 : ℤ) ∧
        ec = -1023))
    (hφex : dwVal (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) = dwVal (ddS2 S k₂ (dwScale (k₁ + k₂) x)) - 1) {T : ℝ}
    (hat : DDLAt p pos (ddDeg e) a |Real.log (dwVal x)| E b δ T) :
    |dwVal (ddLogOp O (ddS2 S k₂) (ddS2 S et) (fun v => (S v.1, S v.2)) y0 x (k₁ + k₂)
        (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e)) 118 eφ et ec ddlF 3) -
      Real.log (dwVal x)| ≤ T :=
  (ddl_core_both p hp hO S hS x hx hX0 y0 hy0 hE k₁ k₂ hk hk2 hr hδ ha0 ha hb pos hsgn e eφ et ec hd hselφ hselt
    hselc hφex hat).2

end ExpansionBounds
