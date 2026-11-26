import ExpansionBounds.DDTrig
import ExpansionBounds.TrigTan

/-!
# Theorem 35 (`thm:trig`) for the double-double functions: the reduction, the quadrant and the quotient

multidouble's `DD::sin`, `cos` and `tan`: RED at two parts, a FastTwoSum of `r_0` and `r_1`, which makes `r` a double
word (the greedy `r` can end in a tie), SINR and COSR on double words (`DDTrig.lean`), the quadrant, and DWDivDW2 for
the tangent's quotient, within `15u² + 56u³` (Theorem 7.1 of Joldes, Muller and Popescu, `DWDiv.lean`). The buckets
and the early returns go by the leading part: of `x` before the reduction, of the double word `r` after it.

`dd_sincos_core` and `dd_tan_core` are Theorem 35's steps after Lemma 34, the move from `r` to `r_e` and the
quadrant, from bounds `δ_S` and `δ_C` of the computed sine and cosine of `r`: the proofs of `thm35_sincos` and
`thm35_tan` with `n = 2`, the double-word operations' results in place of the `n`-part ones, and no ladder for the
quotient, as DWDivDW2 asks only double words.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ)

/-- the reduced argument of the double-double functions: RED at two parts, then a FastTwoSum -/
noncomputable def ddRed (x : ℕ → ℝ) : ℝ × ℝ := fastTwoSum p (redR p 2 x 0) (redR p 2 x 1)

/-- SINR of the reduced argument, `r` itself below `|r_h| < u`; the series length and the scaling go by `|r_h|` -/
noncomputable def ddYs (es : ℝ → ℤ) (Ks : ℝ → ℕ) (Fs : ℕ → ℝ × ℝ) (x : ℕ → ℝ) : ℝ × ℝ :=
  if |(ddRed p x).1| < u p then ddRed p x
  else ddSinR p (es |(ddRed p x).1|) (ddRed p x) Fs (Ks |(ddRed p x).1|)

/-- COSR of the reduced argument, `1` below `|r_h| < u` -/
noncomputable def ddYc (Kc : ℝ → ℕ) (Fc : ℕ → ℝ × ℝ) (x : ℕ → ℝ) : ℝ × ℝ :=
  if |(ddRed p x).1| < u p then (1, 0) else ddCosR p (ddRed p x) Fc (Kc |(ddRed p x).1|)

/-- the quadrant's choice on pairs: `a`, `b`, `-a`, `-b` for `q = 0, 1, 2, 3` -/
noncomputable def ddQuad (q : ℤ) (a b : ℝ × ℝ) : ℝ × ℝ :=
  if q % 4 = 0 then a else if q % 4 = 1 then b else if q % 4 = 2 then (-a.1, -a.2) else (-b.1, -b.2)

/-- `DD::sin`: `x` below `|x_0| < u`, else `Y_s`, `Y_c`, `-Y_s`, `-Y_c` by the quadrant -/
noncomputable def ddSin (es : ℝ → ℤ) (Ks Kc : ℝ → ℕ) (Fs Fc : ℕ → ℝ × ℝ) (x : ℕ → ℝ) : ℝ × ℝ :=
  if |x 0| < u p then (x 0, x 1) else ddQuad (redK p 2 x) (ddYs p es Ks Fs x) (ddYc p Kc Fc x)

/-- `DD::cos`: `1` below `|x_0| < u`, else `Y_c`, `-Y_s`, `-Y_c`, `Y_s` by the quadrant -/
noncomputable def ddCos (es : ℝ → ℤ) (Ks Kc : ℝ → ℕ) (Fs Fc : ℕ → ℝ × ℝ) (x : ℕ → ℝ) : ℝ × ℝ :=
  if |x 0| < u p then (1, 0) else ddQuad (redK p 2 x + 1) (ddYs p es Ks Fs x) (ddYc p Kc Fc x)

/-- the tangent's quotient: `2^{-e}DWDivDW2(2^e Y_s, Y_c)` for even `q` and `-DWDivDW2(Y_c, Y_s)` for odd `q` -/
noncomputable def ddTanQ (q e : ℤ) (Ys Yc : ℝ × ℝ) : ℝ × ℝ :=
  if q % 2 = 0 then
    ((2 : ℝ) ^ (-e) * (dwDivDW2 p ((2 : ℝ) ^ e * Ys.1) ((2 : ℝ) ^ e * Ys.2) Yc.1 Yc.2).1,
      (2 : ℝ) ^ (-e) * (dwDivDW2 p ((2 : ℝ) ^ e * Ys.1) ((2 : ℝ) ^ e * Ys.2) Yc.1 Yc.2).2)
  else (-(dwDivDW2 p Yc.1 Yc.2 Ys.1 Ys.2).1, -(dwDivDW2 p Yc.1 Yc.2 Ys.1 Ys.2).2)

/-- `DD::tan`: `x` below `|x_0| < u`, else the quotient of `Y_s` and `Y_c`, its scaling chosen from `|r_h|` -/
noncomputable def ddTan (es et : ℝ → ℤ) (Ks Kc : ℝ → ℕ) (Fs Fc : ℕ → ℝ × ℝ) (x : ℕ → ℝ) : ℝ × ℝ :=
  if |x 0| < u p then (x 0, x 1)
  else ddTanQ p (redK p 2 x) (et |(ddRed p x).1|) (ddYs p es Ks Fs x) (ddYc p Kc Fc x)

/-- the value of the quadrant's choice -/
theorem dwVal_ddQuad (q : ℤ) (a b : ℝ × ℝ) : dwVal (ddQuad q a b) =
    if q % 4 = 0 then dwVal a else if q % 4 = 1 then dwVal b else if q % 4 = 2 then -dwVal a else -dwVal b := by
  unfold ddQuad
  split_ifs <;> simp only [dwVal] <;> ring

/-- the value of the tangent's quotient -/
theorem dwVal_ddTanQ (q e : ℤ) (Ys Yc : ℝ × ℝ) : dwVal (ddTanQ p q e Ys Yc) =
    if q % 2 = 0 then
      (2 : ℝ) ^ (-e) * ((dwDivDW2 p ((2 : ℝ) ^ e * Ys.1) ((2 : ℝ) ^ e * Ys.2) Yc.1 Yc.2).1 +
        (dwDivDW2 p ((2 : ℝ) ^ e * Ys.1) ((2 : ℝ) ^ e * Ys.2) Yc.1 Yc.2).2)
    else -((dwDivDW2 p Yc.1 Yc.2 Ys.1 Ys.2).1 + (dwDivDW2 p Yc.1 Yc.2 Ys.1 Ys.2).2) := by
  unfold ddTanQ
  split_ifs <;> simp only [dwVal] <;> ring

variable [Prec_gt_0 p]

/-- a double word with a nonzero value has a nonzero high part -/
theorem DW.hi_ne_zero {y : ℝ × ℝ} (hy : DW p y) (h : dwVal y ≠ 0) : y.1 ≠ 0 := by
  intro h1
  have h2 : y.2 = 0 := RN_eq_zero p (by have := hy.2.2; rw [h1, zero_add] at this; exact this)
  exact h (by unfold dwVal; rw [h1, h2, add_zero])

/-- a double word `x` is on `H(2)`, its parts are in `F`, and the reduced argument is a double word with the value of
RED's `r` -/
theorem dd_red (hp : p = 53) (x : ℕ → ℝ) (hx : DW p (x 0, x 1)) (hx0 : |x 0| ≤ 2 ^ 52) :
    Htheta p 2 2 x ∧ (∀ i < 2, F p (x i)) ∧ DW p (ddRed p x) ∧
      dwVal (ddRed p x) = ∑ i ∈ range 2, redR p 2 x i := by
  have hp1 : 1 < p := by omega
  have hu := u_pos p
  have hu53 : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num
  have hH : Htheta p 2 2 x := by
    intro i h1 h2
    obtain rfl : i = 1 := by omega
    have := (DW.parts p hx).1
    rw [pow_one]
    exact this.trans (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))
  have hxF : ∀ i < 2, F p (x i) := by
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · obtain rfl : i = 0 := by omega
      exact hx.1
    · rw [h]
      exact hx.2.1
  obtain ⟨hrF, hrH, -, -, -⟩ := lemma32_r p 2 hp (by norm_num) x hxF hH hx0
  have h10 : |redR p 2 x 1| ≤ |redR p 2 x 0| := by
    have := hrH 1 le_rfl (by norm_num)
    rw [pow_one, hu53] at this
    nlinarith [abs_nonneg (redR p 2 x 0)]
  have hadd := fastTwoSum_add p hp1 (hrF 0 (by norm_num)) (hrF 1 (by norm_num)) h10
  refine ⟨hH, hxF, fastTwoSum_dw p hadd, ?_⟩
  unfold dwVal ddRed
  rw [hadd]
  simp [sum_range_succ]

/-- the buckets of the double word `r`: with `|r_h| < t = 2^m` and `u ≤ t`, `|r|` and `|r_e|` are at most
`t(1 + 2^{-50})`. Lemma 32's bound read on `r_h = RN(r)`, which is below `t` only if `r` is -/
theorem dd_bucket (hp : p = 53) (x : ℕ → ℝ) (hx : DW p (x 0, x 1)) (hx0 : |x 0| ≤ 2 ^ 52) (m : ℤ)
    (ht : u p ≤ (2 : ℝ) ^ m) (hr0 : |(ddRed p x).1| < (2 : ℝ) ^ m) :
    |dwVal (ddRed p x)| ≤ (2 : ℝ) ^ m * (1 + 1 / 2 ^ 50) ∧
      |∑ i ∈ range 2, x i - redK p 2 x * (Real.pi / 2)| ≤ (2 : ℝ) ^ m * (1 + 1 / 2 ^ 50) := by
  have hu : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num
  obtain ⟨hH, hxF, hdw, hval⟩ := dd_red p hp x hx hx0
  obtain ⟨hk, ha, -⟩ := lemma32_k p 2 hp (by norm_num) x hH hx0
  obtain ⟨-, -, -, hre, -⟩ := lemma32_r p 2 hp (by norm_num) x hxF hH hx0
  rw [← hval] at hre
  set t : ℝ := (2 : ℝ) ^ m with htd
  have ht0 : 0 < t := by positivity
  -- `|r| < t`, as `r_h = RN(r)` and `t` is a float
  have hR : |dwVal (ddRed p x)| < t := by
    by_contra h
    have := abs_RN_ge_of_F p (F_two_zpow p m) (not_lt.mp h)
    rw [show RN p (dwVal (ddRed p x)) = (ddRed p x).1 from hdw.2.2] at this
    linarith
  refine ⟨by nlinarith, ?_⟩
  set k := redK p 2 x with hkd
  set re := ∑ i ∈ range 2, x i - k * (Real.pi / 2) with hred
  -- `2E_π ≤ 2^{-157}t`, as `t ≥ u ≥ 2^{-1007}`
  have hu19 : (2 : ℝ) ^ (-1007 : ℤ) ≤ t := by
    refine le_trans ?_ ht
    rw [hu]
    have : (2 : ℝ) ^ (-1007 : ℤ) ≤ (2 : ℝ) ^ (-53 : ℤ) := zpow_le_zpow_right₀ one_le_two (by norm_num)
    exact this.trans (by norm_num)
  have hEπ : 2 * (|(k : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) ≤ 1 / 2 ^ 157 * t := by
    have hk52 : |(k : ℝ)| ≤ (2 : ℝ) ^ (52 : ℤ) := by
      have : (64 / 100 : ℝ) * 2 ^ 52 ≤ (2 : ℝ) ^ (52 : ℤ) := by norm_num
      linarith
    calc 2 * (|(k : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) ≤ 2 * ((2 : ℝ) ^ (52 : ℤ) * (2 : ℝ) ^ (-1217 : ℤ)) := by gcongr
      _ = 1 / 2 ^ 157 * (2 : ℝ) ^ (-1007 : ℤ) := by
          have e1 : (2 : ℝ) * ((2 : ℝ) ^ (52 : ℤ) * (2 : ℝ) ^ (-1217 : ℤ)) = (2 : ℝ) ^ (-1164 : ℤ) := by
            rw [← zpow_add₀ two_ne_zero, ← zpow_one_add₀ two_ne_zero]; norm_num
          have e2 : (1 : ℝ) / 2 ^ 157 * (2 : ℝ) ^ (-1007 : ℤ) = (2 : ℝ) ^ (-1164 : ℤ) := by
            rw [show (1 : ℝ) / 2 ^ 157 = (2 : ℝ) ^ (-157 : ℤ) by norm_num, ← zpow_add₀ two_ne_zero]; norm_num
          rw [e1, e2]
      _ ≤ 1 / 2 ^ 157 * t := by gcongr
  by_cases hk0 : redK1 p x = 0
  · obtain ⟨hk', hr, -⟩ := ha hk0
    have hre0 : re = ∑ i ∈ range 2, x i := by rw [hred, hk', Int.cast_zero, zero_mul, sub_zero]
    rw [hre0, ← hr, ← hval]
    nlinarith
  · have husn : us p ^ 2 ≤ u p := by
      calc us p ^ 2 ≤ us p ^ 1 := pow_le_pow_of_le_one (us_nonneg p) (by
            have := us_le_u p; rw [hu] at this; linarith) (by norm_num)
        _ = us p := pow_one _
        _ ≤ u p := us_le_u p
    have h1 : |re| ≤ |dwVal (ddRed p x)| + |dwVal (ddRed p x) - re| := by
      have := abs_sub_abs_le_abs_sub re (dwVal (ddRed p x))
      rw [abs_sub_comm re] at this
      linarith
    have h2 : us p ^ 2 * |re| ≤ u p * |re| := mul_le_mul_of_nonneg_right husn (abs_nonneg _)
    rw [hu] at h2
    linarith

/-- Theorem 35 for the double-double sine and cosine after Lemma 34: with `A` and `B` within `δ_S|sin r|` and
`δ_C cos r` of the sine and the cosine of the reduced argument `r`, `δ_S, δ_C ∈ [0, 1/2]` and `|r_e| ≤ r̄ ≤ 0.8`, the
quadrant's choices are within `C|sin x| + 5E_π` and `C|cos x| + 5E_π`, `C = ε max(δ_S + εu², δ_C + εu² r̄ tan₊ r̄)` -/
theorem dd_sincos_core (hp : p = 53) (x : ℕ → ℝ) (hx : DW p (x 0, x 1)) (hx0 : |x 0| ≤ 2 ^ 52)
    {A B rb dS dC : ℝ} (hrb : rb ≤ 8 / 10) (hre : |∑ i ∈ range 2, x i - redK p 2 x * (Real.pi / 2)| ≤ rb)
    (hdS0 : 0 ≤ dS) (hdS : dS ≤ 1 / 2) (hdC0 : 0 ≤ dC) (hdC : dC ≤ 1 / 2)
    (hA : |A - Real.sin (dwVal (ddRed p x))| ≤ dS * |Real.sin (dwVal (ddRed p x))|)
    (hB : |B - Real.cos (dwVal (ddRed p x))| ≤ dC * Real.cos (dwVal (ddRed p x))) :
    |(if redK p 2 x % 4 = 0 then A else if redK p 2 x % 4 = 1 then B
          else if redK p 2 x % 4 = 2 then -A else -B) - Real.sin (∑ i ∈ range 2, x i)| ≤
        trigC p 2 dS dC rb * |Real.sin (∑ i ∈ range 2, x i)| +
          5 * (|(redK p 2 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) ∧
      |(if (redK p 2 x + 1) % 4 = 0 then A else if (redK p 2 x + 1) % 4 = 1 then B
          else if (redK p 2 x + 1) % 4 = 2 then -A else -B) - Real.cos (∑ i ∈ range 2, x i)| ≤
        trigC p 2 dS dC rb * |Real.cos (∑ i ∈ range 2, x i)| +
          5 * (|(redK p 2 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) := by
  have hu := u_pos p
  have hu53 : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num
  obtain ⟨hH, hxF, -, hval⟩ := dd_red p hp x hx hx0
  obtain ⟨hk, -, -⟩ := lemma32_k p 2 hp (by norm_num) x hH hx0
  obtain ⟨-, -, -, hη, -⟩ := lemma32_r p 2 hp (by norm_num) x hxF hH hx0
  rw [← hval] at hη
  set k := redK p 2 x with hkd
  set R := dwVal (ddRed p x) with hRd
  set X := ∑ i ∈ range 2, x i with hXd
  set re := X - k * (Real.pi / 2) with hred
  set E := |(k : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ) with hEd
  -- `|R - r_e| ≤ u²|r_e| + 2E_π`
  have husn : us p ^ 2 ≤ u p ^ 2 := pow_le_pow_left₀ (us_nonneg p) (us_le_u p) 2
  have hη' : |R - re| ≤ u p ^ 2 * |re| + 2 * E := by
    have := mul_le_mul_of_nonneg_right husn (abs_nonneg re)
    linarith
  have hw1 : u p ^ 2 ≤ 1 / 8 := by rw [hu53]; norm_num
  have hE1 : E ≤ 1 / 8 := by
    have h2 : (2 : ℝ) ^ (-1217 : ℤ) ≤ 1 / 2 ^ 60 := by
      rw [zpow_neg, ← one_div, one_div_le_one_div (by positivity) (by positivity)]
      exact_mod_cast pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : 60 ≤ 1217)
    calc E ≤ 64 / 100 * 2 ^ 52 * (1 / 2 ^ 60) := mul_le_mul hk.le h2 (by positivity) (by positivity)
      _ ≤ 1 / 8 := by norm_num
  have hE0 : 0 ≤ E := by positivity
  -- the moves to `r_e`
  have hsin := sin_move (pow_nonneg hu.le 2) hw1 hE0 hE1 hdS0 hdS (hre.trans hrb) hA hη'
  have hcos := cos_move (pow_nonneg hu.le 2) hw1 hE0 hE1 hdC0 hdC hre hrb hB hη'
  set Cc := trigC p 2 dS dC rb with hCc
  have hpi : 8 / 10 ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hcpos : 0 ≤ Real.cos re := Real.cos_nonneg_of_mem_Icc ⟨by linarith [(abs_le.mp (hre.trans (hrb.trans hpi))).1],
    (abs_le.mp (hre.trans (hrb.trans hpi))).2⟩
  have hA' : |A - Real.sin re| ≤ Cc * |Real.sin re| + 5 * E := by
    refine hsin.trans (add_le_add (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)) le_rfl)
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
  have hB' : |B - Real.cos re| ≤ Cc * |Real.cos re| + 5 * E := by
    rw [abs_of_nonneg hcpos]
    refine hcos.trans (add_le_add (mul_le_mul_of_nonneg_right ?_ hcpos) le_rfl)
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
  have hXre : X = re + k * (Real.pi / 2) := by rw [hred]; ring
  have hXre1 : Real.cos X = Real.sin (re + ((k + 1 : ℤ) : ℝ) * (Real.pi / 2)) := by
    rw [hXre]; exact cos_add_quarter re k
  constructor
  · have h := quad_bound k hA' hB'
    rw [← hXre] at h
    exact h
  · have h := quad_bound (k + 1) hA' hB'
    rw [← hXre1] at h
    exact h

/-- Theorem 35 for the double-double tangent after Lemma 34: with the double words `Y_s` and `Y_c` within
`δ_S|sin r|` and `δ_C cos r` of the sine and the cosine of the reduced argument, `δ_S, δ_C ∈ [0, 1/10]`,
`|r|, |r_e| ≤ r̄ ≤ 0.8` and `|x - kπ/2| ≥ 2^{2p-1074}` for `k ≠ 0`, the quotient by DWDivDW2 is within
`(C^T + 5E_π/|sin x cos x|)|tan x|` of `tan x`, `C^T` with `δ_D = 15u² + 56u³` -/
theorem dd_tan_core (hp : p = 53) (x : ℕ → ℝ) (hx : DW p (x 0, x 1)) (hx0 : |x 0| ≤ 2 ^ 52)
    (hbig : ¬|x 0| < u p) {Ys Yc : ℝ × ℝ} (hYs : DW p Ys) (hYc : DW p Yc) {rb dS dC : ℝ} (hrb : rb ≤ 8 / 10)
    (hr : |dwVal (ddRed p x)| ≤ rb) (hre : |∑ i ∈ range 2, x i - redK p 2 x * (Real.pi / 2)| ≤ rb)
    (hdS0 : 0 ≤ dS) (hdS : dS ≤ 1 / 10) (hdC0 : 0 ≤ dC) (hdC : dC ≤ 1 / 10)
    (hA : |dwVal Ys - Real.sin (dwVal (ddRed p x))| ≤ dS * |Real.sin (dwVal (ddRed p x))|)
    (hB : |dwVal Yc - Real.cos (dwVal (ddRed p x))| ≤ dC * Real.cos (dwVal (ddRed p x)))
    (hfar : redK p 2 x ≠ 0 →
      (2 : ℝ) ^ (p * (2 : ℕ) - 1074) ≤ |∑ i ∈ range 2, x i - redK p 2 x * (Real.pi / 2)|) (e : ℤ) :
    |dwVal (ddTanQ p (redK p 2 x) e Ys Yc) - Real.tan (∑ i ∈ range 2, x i)| ≤
      (tanCT p 2 dS dC (15 * u p ^ 2 + 56 * u p ^ 3) rb + 5 * (|(redK p 2 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) /
        |Real.sin (∑ i ∈ range 2, x i) * Real.cos (∑ i ∈ range 2, x i)|) * |Real.tan (∑ i ∈ range 2, x i)| := by
  have hp7 : 7 ≤ p := by omega
  have hu := u_pos p
  have hu53 : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num
  obtain ⟨hH, hxF, -, hval⟩ := dd_red p hp x hx hx0
  obtain ⟨hk, -, -⟩ := lemma32_k p 2 hp (by norm_num) x hH hx0
  obtain ⟨-, -, -, hη, -⟩ := lemma32_r p 2 hp (by norm_num) x hxF hH hx0
  rw [← hval] at hη
  have hre0 : 0 < |∑ i ∈ range 2, x i - redK p 2 x * (Real.pi / 2)| :=
    tan_re_pos p 2 hp (by norm_num) x hxF hH hx0 (by norm_num; exact not_lt.mp hbig)
  rw [dwVal_ddTanQ]
  set k := redK p 2 x with hkd
  set R := dwVal (ddRed p x) with hRd
  set X := ∑ i ∈ range 2, x i with hXd
  set re := X - k * (Real.pi / 2) with hred
  set E := |(k : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ) with hEd
  set dD := 15 * u p ^ 2 + 56 * u p ^ 3 with hdDd
  set w := u p ^ 2 with hwd
  set K := 2 * rb / sinLo (2 * rb) with hKd
  obtain ⟨A, hAd⟩ : ∃ A, A = dwVal Ys := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B, B = dwVal Yc := ⟨_, rfl⟩
  rw [← hAd] at hA
  rw [← hBd] at hB
  have hrb0 : 0 ≤ rb := (abs_nonneg _).trans hr
  have hrb1 : rb ≤ 1 := by linarith
  have hdD0 : 0 ≤ dD := by positivity
  have hdD : dD ≤ 1 / 10 := by rw [hdDd, hwd, hu53]; norm_num
  -- `cos R ≥ cos₋ r̄ ≥ 0.69` and `|sin R| ≥ |R|(1 - r̄²/6)`
  have hcR : cosLo rb ≤ Real.cos R := cos_ge_cosLo R rb hr hrb1
  have hcl : 69 / 100 ≤ cosLo rb := cosLo_ge hrb0 hrb
  have hsR : |R| * (1 - rb ^ 2 / 6) ≤ |Real.sin R| := by
    have h := abs_sin_ge R (hr.trans hrb1)
    have : R ^ 2 ≤ rb ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hr 2
    nlinarith [abs_nonneg R]
  have hcRp : 0 < Real.cos R := by linarith
  have hcR' : |B - Real.cos R| ≤ dC * |Real.cos R| := by rw [abs_of_pos hcRp]; exact hB
  -- `Y_c ≠ 0`
  have hB0 : B ≠ 0 := by
    intro h
    rw [h, zero_sub, abs_neg, abs_of_pos hcRp] at hB
    have := mul_le_mul_of_nonneg_right hdC hcRp.le
    linarith
  have hYc1 : Yc.1 ≠ 0 := DW.hi_ne_zero p hYc (hBd ▸ hB0)
  -- the move's constants
  have hw0 : 0 ≤ w := pow_nonneg hu.le 2
  have hw1 : w ≤ 1 / 100 := by rw [hwd, hu53]; norm_num
  have hE0 : 0 ≤ E := by positivity
  have hE1 : E ≤ 1 / 1000 := by
    have h2 : (2 : ℝ) ^ (-1217 : ℤ) ≤ 1 / 2 ^ 70 := by
      rw [zpow_neg, ← one_div, one_div_le_one_div (by positivity) (by positivity)]
      exact_mod_cast pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : 70 ≤ 1217)
    calc E ≤ 64 / 100 * 2 ^ 52 * (1 / 2 ^ 70) := mul_le_mul hk.le h2 (by positivity) (by positivity)
      _ ≤ 1 / 1000 := by norm_num
  have husn : us p ^ 2 ≤ w := pow_le_pow_left₀ (us_nonneg p) (us_le_u p) 2
  have hη' : |R - re| ≤ w * |re| + 2 * E := by
    have := mul_le_mul_of_nonneg_right husn (abs_nonneg re)
    linarith
  obtain ⟨hK0, hK⟩ := K_bound hrb0 hrb hw1
  have hcre : 0 < Real.cos re := by
    have := cos_ge_cosLo re rb hre hrb1
    linarith
  have hsc : 0 < |Real.sin re| * Real.cos re := by
    have hpi := Real.pi_gt_three
    have : 0 < |Real.sin re| := by
      rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith)]
      exact Real.sin_pos_of_pos_of_lt_pi hre0 (by linarith)
    positivity
  obtain ⟨htq, hsc'⟩ := tan_quarter re k
  have hXre : X = re + k * (Real.pi / 2) := by rw [hred]; ring
  rw [hXre, Real.tan_eq_sin_div_cos, htq, hsc', abs_of_pos hcre]
  set Me := (1 + dS) * (1 + dD) / (1 - dC) with hMe
  set Mo := (1 + dC) * (1 + dD) / (1 - dS) with hMo
  have hfin : ∀ M τ D : ℝ, M ≤ max Me Mo →
      |D - τ| ≤ ((1 + 2 * w) * (M - 1 + (1 + 2 * w) * w * K) + 5 * E / (|Real.sin re| * Real.cos re)) * |τ| →
      |D - τ| ≤ (tanCT p 2 dS dC dD rb + 5 * E / (|Real.sin re| * Real.cos re)) * |τ| := by
    intro M τ D hM h
    refine h.trans (mul_le_mul_of_nonneg_right (add_le_add ?_ le_rfl) (abs_nonneg _))
    unfold tanCT
    rw [← hwd, ← hKd]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  by_cases hev : k % 2 = 0
  · -- even `q`: `2^{-e}DWDivDW2(2^e Y_s, Y_c)` and `tan r_e`
    simp only [hev, ↓reduceIte]
    have hσ : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
    have hσ' : (0 : ℝ) < (2 : ℝ) ^ (-e) := by positivity
    have hee : (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e = 1 := by rw [← zpow_add₀ two_ne_zero]; simp
    have hsdw : RN p ((2 : ℝ) ^ e * Ys.1 + (2 : ℝ) ^ e * Ys.2) = (2 : ℝ) ^ e * Ys.1 := (DW.scale p hYs e).2.2
    obtain ⟨h, -⟩ := dwDivDW2_err p hp7 hsdw hYc.2.2 hYc1
    obtain ⟨Q, hQd⟩ : ∃ Q, Q = (dwDivDW2 p ((2 : ℝ) ^ e * Ys.1) ((2 : ℝ) ^ e * Ys.2) Yc.1 Yc.2).1 +
        (dwDivDW2 p ((2 : ℝ) ^ e * Ys.1) ((2 : ℝ) ^ e * Ys.2) Yc.1 Yc.2).2 := ⟨_, rfl⟩
    rw [← hQd] at h ⊢
    rw [show (2 : ℝ) ^ e * Ys.1 + (2 : ℝ) ^ e * Ys.2 = (2 : ℝ) ^ e * A by rw [hAd]; unfold dwVal; ring,
      show Yc.1 + Yc.2 = B by rw [hBd]; rfl, ← hdDd] at h
    have hD : |A / B - (2 : ℝ) ^ (-e) * Q| ≤ dD * |A / B| := by
      have e1 : A / B - (2 : ℝ) ^ (-e) * Q = (2 : ℝ) ^ (-e) * ((2 : ℝ) ^ e * A / B - Q) := by
        rw [mul_sub, mul_div_assoc, ← mul_assoc, hee, one_mul]
      have e2 : |(2 : ℝ) ^ e * A / B| = (2 : ℝ) ^ e * |A / B| := by
        rw [mul_div_assoc, abs_mul, abs_of_pos hσ]
      rw [e2, abs_sub_comm] at h
      rw [e1, abs_mul, abs_of_pos hσ']
      calc (2 : ℝ) ^ (-e) * |(2 : ℝ) ^ e * A / B - Q| ≤ (2 : ℝ) ^ (-e) * (dD * ((2 : ℝ) ^ e * |A / B|)) :=
            mul_le_mul_of_nonneg_left h hσ'.le
        _ = ((2 : ℝ) ^ (-e) * (2 : ℝ) ^ e) * (dD * |A / B|) := by ring
        _ = dD * |A / B| := by rw [hee, one_mul]
    exact hfin Me _ _ (le_max_left _ _) (tan_ratio hcRp.ne' hdS0 hdC0 hdD0 hdS hdC hdD hw0 hK0 hK hE0 hsc hA hcR' hD
      (tan_move hw0 hw1 hE0 hE1 hre0 hre hrb hη'))
  · -- odd `q`: `-DWDivDW2(Y_c, Y_s)` and `-cot r_e`
    simp only [hev, ↓reduceIte]
    rw [neg_sub_neg, abs_sub_comm, abs_neg]
    have hEre : 2 * E ≤ w * |re| / 2 ^ 90 := tan_far p 2 hk.le (hfar (by omega))
    -- `R ≠ 0`, so `sin R ≠ 0` and `Y_s ≠ 0`
    have hRpos : 0 < |R| := by
      have h3 : 2 * E ≤ w * |re| / 2 := hEre.trans (div_le_div_of_nonneg_left (by positivity) (by norm_num)
        (by norm_num))
      have := abs_sub_abs_le_abs_sub re R
      rw [abs_sub_comm re] at this
      have := mul_le_mul_of_nonneg_right hw1 (abs_nonneg re)
      linarith
    have hrb2 : rb ^ 2 ≤ (8 / 10) ^ 2 := pow_le_pow_left₀ hrb0 hrb 2
    have hsRp : 0 < |Real.sin R| := lt_of_lt_of_le (mul_pos hRpos (by linarith)) hsR
    have hA0 : A ≠ 0 := by
      intro h
      rw [h, zero_sub, abs_neg] at hA
      have := mul_le_mul_of_nonneg_right hdS (abs_nonneg (Real.sin R))
      linarith
    have hYs1 : Ys.1 ≠ 0 := DW.hi_ne_zero p hYs (hAd ▸ hA0)
    obtain ⟨h, -⟩ := dwDivDW2_err p hp7 hYc.2.2 hYs.2.2 hYs1
    rw [show Yc.1 + Yc.2 = B by rw [hBd]; rfl, show Ys.1 + Ys.2 = A by rw [hAd]; rfl, ← hdDd, abs_sub_comm] at h
    exact hfin Mo _ _ (le_max_right _ _) (tan_ratio (abs_pos.mp hsRp) hdC0 hdS0 hdD0 hdC hdS hdD hw0 hK0 hK hE0 hsc
      hcR' hA h (cot_move hw0 hw1 hE0 hre0 hre hrb hη' hEre))

end ExpansionBounds
