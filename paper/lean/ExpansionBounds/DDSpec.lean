import ExpansionBounds.DWTimesFP3
import ExpansionBounds.DWTimesDW2
import ExpansionBounds.DDExp2
import ExpansionBounds.DDLn

/-!
# Proposition 44 on the four double-word algorithms

`ddOps` is the `DWOps` of AccurateDWPlusDW, DWPlusFP, DWTimesFP3 and DWTimesDW2, and `ddOps_spec` is `DWSpec` for
it, for `p ≥ 5`: Theorems 3.1, 2.2 and 4.3 of Joldes, Muller and Popescu (2017) and Theorem 2.7 of Muller and
Rideau (2022), each with its result a double word. `prop44_exp_dd` and `prop44_ln_dd` are `prop44_exp` and
`prop44_ln` on these operations, with no hypothesis on them; `prop44_ln_dd_dw` adds that `DD::ln`'s result is a
double word (`prop44_ln_dd_F`, `prop44_ln_dd_rn`: its parts are floats and the high part is their rounded sum).

For the logarithm, Lemma 41 on double words (`φ = x' - 1` exactly, the `hφex` of `DDLnSel`) is proved for
DWPlusFP: `x' = 2^k x`, rounded, is a double word with `x'_h ∈ [1/2, 2]` (`ddl_xprime`), where
`dwPlusFP_sub_one` applies. The range is from `|y_0 - ln x| ≤ 1/10` and `|-y_0 - k ln 2| ≤ 51/100`
(`ddl_re_le`), so `|ln(2^k x)| ≤ 61/100` and `2^k x ∈ [100/191, 191/100]`.
-/

namespace ExpansionBounds

variable (p : ℤ)

/-- the four double-word operations of `DD::exp` and `DD::ln`: AccurateDWPlusDW, DWPlusFP, DWTimesFP3 and
DWTimesDW2 -/
noncomputable def ddOps : DWOps where
  add := accDWPlusDW p
  addF := dwPlusFP p
  mulF := dwTimesFP3 p
  mul := dwTimesDW2 p

variable [Prec_gt_0 p]

/-- the published bounds of the four operations, for `p ≥ 5`: each returns a double word within `e_A`, `e_F`,
`e_M`, `e_P` of its exact result, relatively -/
theorem ddOps_spec (hp : 5 ≤ p) : DWSpec p (ddOps p) where
  add_dw := fun _ _ hx hy => accDWPlusDW_dw p (by omega) hx hy
  add_err := fun _ _ hx hy => accDWPlusDW_err p (by omega) hx hy
  addF_dw := fun _ _ hx hy => dwPlusFP_dw p (by omega) hx hy
  addF_err := fun _ _ hx hy => dwPlusFP_err p (by omega) hx hy
  mulF_dw := fun _ _ hx hy => dwTimesFP3_dw p (by omega) hx hy
  mulF_err := fun _ _ hx hy => dwTimesFP3_err p (by omega) hx hy
  mul_dw := fun _ _ hx hy => dwTimesDW2_dw p hp hx hy
  mul_err := fun _ _ hx hy => dwTimesDW2_err p hp hx hy

/-- Proposition 44 (`prop:ddexplog`) for `DD::exp` on the four algorithms, at `p = 53`: `prop44_exp` with no
hypothesis on the operations. What remains assumed: the rounding rule of a scaling (`hS`), `|x_h| ≤ 745.2`, the
exponents that the run selects, the scaling by `2^k` in two steps with `k₂ ≤ 0`, and no overflow. multidouble takes
`k₁ = k/2`, rounded toward zero, so `k₂ > 0` where `k > 0`; both steps then scale up, which binary64 does exactly,
and the value is that of the split `(k, 0)`.
For binary64 the run must also meet the paper's (A2′): every product, fused multiply-add and quotient returns what it
would with an unbounded exponent range, as in the model, but those that only select `k` or an exponent, which the paper
exempts -/
theorem prop44_exp_dd (hp : p = 53) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℝ × ℝ) (hx : DW p x) (hx0 : |x.1| ≤ 7452 / 10) (k₁ k₂ : ℤ) (hk : k₁ + k₂ = expK p x.1) (hk2 : k₂ ≤ 0)
    (e : ℤ)
    (hsel : ((2 : ℝ) ^ e ≤ dd2U p (dd2R p (ddOps p) x) ∧ dd2U p (dd2R p (ddOps p) x) < (2 : ℝ) ^ (e + 1)) ∨
      (dd2U p (dd2R p (ddOps p) x) < (2 : ℝ) ^ (-1022 : ℤ) ∧ e = -1023)) :
    |S ((2 : ℝ) ^ k₂ * S ((2 : ℝ) ^ k₁ *
          ((ddOps p).addF (ddExpT (ddOps p) (fun v => (S v.1, S v.2)) e (dd2R p (ddOps p) x) dd2F (ddDeg e)) 1).1)) +
        S ((2 : ℝ) ^ k₂ * S ((2 : ℝ) ^ k₁ *
          ((ddOps p).addF (ddExpT (ddOps p) (fun v => (S v.1, S v.2)) e (dd2R p (ddOps p) x) dd2F (ddDeg e)) 1).2)) -
        Real.exp (dwVal x)| ≤
      5465 / 1000 * u p ^ 2 * Real.exp (dwVal x) + (2 : ℝ) ^ (-1073 : ℤ) :=
  prop44_exp p hp (ddOps_spec p (by omega)) S hS x hx hx0 k₁ k₂ hk hk2 e hsel

/-! ### Lemma 41 for DWPlusFP, and the logarithm -/

/-- the reduction's `δ` at the top of `|r|` for `k ≠ 0` is at most `2^{-106}` -/
theorem ddl_delta_top : ddlDelta (dyQ ddlTop1S + dyQ ddlDStarS) ≤ 1 / 2 ^ 106 := by decide +kernel

/-- `|-y_0 - k ln 2| ≤ 51/100` for the `k` of EXP's reduction of `-y_0`, `|y_0| ≤ ȳ`: for `k = 0` it is
`|y_0| < 1/(2c_r) < 1/2`, and otherwise `|r| < 1/2` with `r` within `2^{-106}` of `-y_0 - k ln 2` -/
theorem ddl_re_le (hp : p = 53) {O : DWOps} (hO : DWSpec p O) (y0 : ℝ) (hy0 : F p y0)
    (hyb : |y0| ≤ ((ddlYB : ℚ) : ℝ)) : |-y0 - ((expK p (-y0) : ℤ) : ℝ) * Real.log 2| ≤ 51 / 100 := by
  obtain ⟨-, -, -, -, cT0, cT0', cT1', -⟩ := ddl_consts
  obtain ⟨-, -, -, -, -, -, ccr, -, -⟩ := dd2_consts
  have hcr : (0 : ℝ) < ((cr8 : ℚ) : ℝ) := by exact_mod_cast ccr
  obtain ⟨-, h0, h3⟩ := ddl_run p hp hO y0 hy0 hyb
  by_cases hk0 : expK p (-y0) = 0
  · obtain ⟨-, h02⟩ := h0 hk0
    rw [hk0, Int.cast_zero, zero_mul, sub_zero, abs_neg]
    have q0 : (1 : ℚ) / (2 * cr8) ≤ 1 / 2 := cT0.trans (cT0'.le.trans (by norm_num))
    have r0 : (1 : ℝ) / (2 * ((cr8 : ℚ) : ℝ)) ≤ 1 / 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr q0
      rw [Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_div, Rat.cast_one,
        Rat.cast_ofNat] at this
      exact this
    have h1 : |y0| ≤ 1 / (2 * ((cr8 : ℚ) : ℝ)) := by
      rw [le_div_iff₀ (by positivity)]
      linarith only [h02]
    linarith only [h1, r0]
  · obtain ⟨-, h32, h33⟩ := h3 hk0
    have hδ := h33 (dyQ ddlTop1S) h32
    have q1 : dyQ ddlTop1S ≤ 1 / 2 := cT1'.le.trans (by norm_num)
    have r1 : ((dyQ ddlTop1S : ℚ) : ℝ) ≤ 1 / 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr q1
      rw [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at this
      exact this
    have r2 : ((ddlDelta (dyQ ddlTop1S + dyQ ddlDStarS) : ℚ) : ℝ) ≤ 1 / 100 := by
      have := (Rat.cast_le (K := ℝ)).mpr ddl_delta_top
      rw [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] at this
      exact this.trans (by norm_num)
    have h1 := abs_sub_abs_le_abs_sub (-y0 - ((expK p (-y0) : ℤ) : ℝ) * Real.log 2) (dwVal (dd2R p O (-y0, 0)))
    rw [abs_sub_comm (-y0 - ((expK p (-y0) : ℤ) : ℝ) * Real.log 2) (dwVal (dd2R p O (-y0, 0)))] at h1
    linarith only [h1, hδ, h32, r1, r2]

/-- `e^{0.61} ≤ 1.91` -/
theorem exp_61_le : Real.exp (61 / 100) ≤ 191 / 100 := by
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h3 : Real.exp (1 / 2) ≤ 17 / 10 := by nlinarith [Real.exp_pos (1 / 2)]
  have h4 := Real.abs_exp_sub_one_sub_id_le (x := 11 / 100) (by rw [abs_of_pos] <;> norm_num)
  have h5 : Real.exp (11 / 100) ≤ 11221 / 10000 := by
    have := (abs_le.mp h4).2
    linarith only [this, show ((11 : ℝ) / 100) ^ 2 = 121 / 10000 by norm_num]
  have h6 : Real.exp (61 / 100) = Real.exp (1 / 2) * Real.exp (11 / 100) := by rw [← Real.exp_add]; norm_num
  rw [h6]
  calc Real.exp (1 / 2) * Real.exp (11 / 100) ≤ 17 / 10 * (11221 / 10000) :=
        mul_le_mul h3 h5 (Real.exp_pos _).le (by norm_num)
    _ ≤ 191 / 100 := by norm_num

/-- `2^k x ∈ [100/191, 191/100]` for the `k` of `DD::ln`: `|y_0 - ln x| ≤ 1/10` from `ȳ ≤ 745.3`, and
`|-y_0 - k ln 2| ≤ 51/100` -/
theorem ddl_scaled_range (hp : p = 53) {O : DWOps} (hO : DWSpec p O) {X : ℝ} (hX0 : 0 < X)
    (hX : |Real.log X| ≤ 7452 / 10) (y0 : ℝ) (hy0 : F p y0)
    (hE : |y0 - Real.log X| ≤ ((ddlE0 : ℚ) : ℝ) + ((ddlE1 : ℚ) : ℝ) * |Real.log X|) (k : ℤ)
    (hk : k = expK p (-y0)) : 100 / 191 ≤ (2 : ℝ) ^ k * X ∧ (2 : ℝ) ^ k * X ≤ 191 / 100 := by
  obtain ⟨-, cY, -, -, -, -, -, -, -, -, cE1, -⟩ := ddl_consts
  have hre := ddl_re_le p hp hO y0 hy0 (ddl_y0_le hE hX)
  rw [← hk] at hre
  have hE10 : ((ddlE0 : ℚ) : ℝ) + ((ddlE1 : ℚ) : ℝ) * |Real.log X| ≤ 1 / 10 := by
    have hY : ((ddlYB : ℚ) : ℝ) = 7452 / 10 + (((ddlE1 : ℚ) : ℝ) * (7452 / 10) + ((ddlE0 : ℚ) : ℝ)) := by
      unfold ddlYB ddlE red8X
      push_cast
      ring
    have h1 := (Rat.cast_le (K := ℝ)).mpr cY
    rw [hY, Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofNat] at h1
    have hE1 : (0 : ℝ) ≤ ((ddlE1 : ℚ) : ℝ) := by exact_mod_cast cE1
    have h2 := mul_le_mul_of_nonneg_left hX hE1
    linarith only [h1, h2]
  have hX' : (2 : ℝ) ^ k * X = Real.exp (-(y0 - Real.log X) - (-y0 - (k : ℝ) * Real.log 2)) := by
    rw [show -(y0 - Real.log X) - (-y0 - (k : ℝ) * Real.log 2) = Real.log X + (k : ℝ) * Real.log 2 by ring,
      Real.exp_add, Real.exp_log hX0, exp_int_mul_log_two, mul_comm]
  have habs : |-(y0 - Real.log X) - (-y0 - (k : ℝ) * Real.log 2)| ≤ 61 / 100 := by
    have := abs_sub (-(y0 - Real.log X)) (-y0 - (k : ℝ) * Real.log 2)
    rw [abs_neg] at this
    linarith only [this, hE, hE10, hre]
  rw [hX']
  constructor
  · have h1 := Real.exp_le_exp.mpr (abs_le.mp habs).1
    have h2 : (100 : ℝ) / 191 ≤ Real.exp (-(61 / 100)) := by
      rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (by norm_num) (Real.exp_pos _)]
      linarith only [exp_61_le]
    exact h2.trans h1
  · exact (Real.exp_le_exp.mpr (abs_le.mp habs).2).trans exp_61_le

/-- the scaled operand of `DD::ln`: `x' = 2^k x`, each part rounded by `S` in two steps, is a double word with
`x'_h ∈ [1/2, 2]` -/
theorem ddl_xprime (hp : p = 53) {O : DWOps} (hO : DWSpec p O) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℝ × ℝ) (hx : DW p x) (hX0 : 0 < dwVal x) (hX : |Real.log (dwVal x)| ≤ 7452 / 10) (y0 : ℝ) (hy0 : F p y0)
    (hE : |y0 - Real.log (dwVal x)| ≤ ((ddlE0 : ℚ) : ℝ) + ((ddlE1 : ℚ) : ℝ) * |Real.log (dwVal x)|)
    (k₁ k₂ : ℤ) (hk : k₁ + k₂ = expK p (-y0)) (hk2 : k₂ ≤ 0) :
    DW p (ddS2 S k₂ (dwScale (k₁ + k₂) x)) ∧ 1 / 2 ≤ (ddS2 S k₂ (dwScale (k₁ + k₂) x)).1 ∧
      (ddS2 S k₂ (dwScale (k₁ + k₂) x)).1 ≤ 2 := by
  have hu53 := u_53 p hp
  obtain ⟨hlo, hup⟩ := ddl_scaled_range p hp hO hX0 hX y0 hy0 hE (k₁ + k₂) hk
  -- `x_h > 0`
  have hx1pos : 0 < x.1 := by
    have h2 : RN p (dwVal x) = x.1 := hx.2.2
    have h0 : 0 ≤ x.1 := by
      have := RN_mono p hX0.le
      rwa [RN_zero, h2] at this
    have hne : x.1 ≠ 0 := fun h => by
      rw [h] at h2
      exact hX0.ne' (RN_eq_zero p h2)
    exact lt_of_le_of_ne h0 (Ne.symm hne)
  -- `2^k x_h` is within `u` of `2^k x`, relatively
  have hxl := (DW.parts p hx).1
  rw [abs_of_pos hx1pos] at hxl
  obtain ⟨hl1, hl2⟩ := abs_le.mp hxl
  have hXval : dwVal x = x.1 + x.2 := rfl
  have h2k : (0 : ℝ) < (2 : ℝ) ^ (k₁ + k₂) := by positivity
  obtain ⟨a, had⟩ : ∃ a, a = (2 : ℝ) ^ (k₁ + k₂) * x.1 := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [had]; positivity
  have hA1 : a * (1 - u p) ≤ (2 : ℝ) ^ (k₁ + k₂) * dwVal x := by
    rw [had, hXval]
    nlinarith only [h2k, hl1]
  have hA2 : (2 : ℝ) ^ (k₁ + k₂) * dwVal x ≤ a * (1 + u p) := by
    rw [had, hXval]
    nlinarith only [h2k, hl2]
  rw [hu53] at hA1 hA2
  have ha_up : a ≤ 192 / 100 := by linarith only [hA1, hup, ha0]
  have ha_lo : 52 / 100 ≤ a := by linarith only [hA2, hlo, ha0]
  -- the rounded scaling keeps a double word and moves `2^k x_h` by at most `2^{-1074}`
  have hT := SclDW.two_step p hp S hS hk2
  have hv1 : (dwScale (k₁ + k₂) x).1 = a := by rw [had]; rfl
  have hη : (2 : ℝ) * (2 : ℝ) ^ (-1075 : ℤ) ≤ 1 / 100 := by
    have h1 : (2 : ℝ) ^ (-1075 : ℤ) ≤ 1 / 256 :=
      (zpow_le_zpow_right₀ (by norm_num) (by norm_num : (-1075 : ℤ) ≤ -8)).trans_eq (by norm_num)
    exact (mul_le_mul_of_nonneg_left h1 (by norm_num)).trans (by norm_num)
  have hlo967 : (2 : ℝ) ^ (-967 : ℤ) ≤ |(dwScale (k₁ + k₂) x).1| := by
    rw [hv1, abs_of_pos ha0]
    have h1 : (2 : ℝ) ^ (-967 : ℤ) ≤ 1 / 4 :=
      (zpow_le_zpow_right₀ (by norm_num) (by norm_num : (-967 : ℤ) ≤ -2)).trans_eq (by norm_num)
    linarith only [h1, ha_lo]
  have hdw := hT.dw _ (DW.dwScale p hx (k₁ + k₂)) hlo967
  have herr := (hT.err₁ (dwScale (k₁ + k₂) x)).trans hη
  rw [hv1] at herr
  obtain ⟨e1, e2⟩ := abs_le.mp herr
  exact ⟨hdw, by linarith only [e1, ha_lo], by linarith only [e2, ha_up]⟩

/-- what a run of `DD::ln` after its start is asked, apart from Lemma 41: `k = k₁ + k₂` with `k₂ ≤ 0`, and `e`,
`e_φ`, `e_t` and `e_c` are the exponents of step (2)'s `U` for `r`, `φ`, `t` and `c` (`-1023` where
`U < 2^{-1022}`). These are the fields of `DDLnSel` but its `hφex` -/
structure DDLnRun (O : DWOps) (S : ℝ → ℝ) (x : ℝ × ℝ) (y0 : ℝ) (k₁ k₂ e eφ et ec : ℤ) : Prop where
  hk : k₁ + k₂ = expK p (-y0)
  hk2 : k₂ ≤ 0
  hsel : ((2 : ℝ) ^ e ≤ dd2U p (dd2R p O (-y0, 0)) ∧ dd2U p (dd2R p O (-y0, 0)) < (2 : ℝ) ^ (e + 1)) ∨
    (dd2U p (dd2R p O (-y0, 0)) < (2 : ℝ) ^ (-1022 : ℤ) ∧ e = -1023)
  hselφ : ((2 : ℝ) ^ eφ ≤ dd2U p (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) ∧
      dd2U p (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) < (2 : ℝ) ^ (eφ + 1)) ∨
    (dd2U p (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) < (2 : ℝ) ^ (-1022 : ℤ) ∧ eφ = -1023)
  hselt : ((2 : ℝ) ^ et ≤ dd2U p (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e)) ∧
      dd2U p (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e)) < (2 : ℝ) ^ (et + 1)) ∨
    (dd2U p (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e)) < (2 : ℝ) ^ (-1022 : ℤ) ∧
      et = -1023)
  hselc : ((2 : ℝ) ^ ec ≤ dd2U p (ddLogC O (ddS2 S et) 118 eφ et (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x)
        (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e))) ∧
      dd2U p (ddLogC O (ddS2 S et) 118 eφ et (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x)
        (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e))) < (2 : ℝ) ^ (ec + 1)) ∨
    (dd2U p (ddLogC O (ddS2 S et) 118 eφ et (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x)
        (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e))) < (2 : ℝ) ^ (-1022 : ℤ) ∧
      ec = -1023)

/-- the selection `DDLnSel` of a run on the four algorithms, from `DDLnRun`: Lemma 41 holds for DWPlusFP at
`x'`, a double word with `x'_h ∈ [1/2, 2]` (`ddl_xprime`, `dwPlusFP_sub_one`) -/
theorem ddLnRun_sel (hp : p = 53) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℝ × ℝ) (hx : DW p x) (hX0 : 0 < dwVal x) (hX : |Real.log (dwVal x)| ≤ 7452 / 10) (w : ℝ)
    (hw0 : |w - x.2 / x.1| ≤ u p * |x.2 / x.1| + (2 : ℝ) ^ (-1075 : ℤ)) (hw1 : x.1 = 1 → w = x.2)
    (k₁ k₂ e eφ et ec : ℤ) (hrun : DDLnRun p (ddOps p) S x (ddLnY0 p x w) k₁ k₂ e eφ et ec) :
    DDLnSel p (ddOps p) S x (ddLnY0 p x w) k₁ k₂ e eφ et ec := by
  have hO := ddOps_spec p (by omega)
  obtain ⟨hy0, hE, -⟩ := ddl_start p hp x hx hX0 w hw0 hw1
  obtain ⟨hdw, h1, h2⟩ := ddl_xprime p hp hO S hS x hx hX0 hX _ hy0 hE k₁ k₂ hrun.hk hrun.hk2
  have hφ : dwVal (ddLogPhi (ddOps p) (ddS2 S k₂) (k₁ + k₂) x) =
      dwVal (ddS2 S k₂ (dwScale (k₁ + k₂) x)) - 1 := (dwPlusFP_sub_one p (by omega) hdw h1 h2).1
  exact ⟨hrun.hk, hrun.hk2, hrun.hsel, hrun.hselφ, hrun.hselt, hrun.hselc, hφ⟩

/-- Proposition 44 (`prop:ddexplog`) for `DD::ln` on the four algorithms, at `p = 53`: `prop44_ln` with no
hypothesis on the operations and without Lemma 41, which `dwPlusFP_sub_one` gives at `x'` (`ddl_xprime`):
`|y - ln x| ≤ 15.351u²|ln x| + 2^{-1071}`.

What remains assumed: the rounding rule of a scaling (`hS`: a value is kept, or it is below `2^{-1022}` and is
rounded to a multiple of `2^{-1074}` within `2^{-1075}`); the two properties of the computed quotient `w`, that it
is within `u|x_l/x_h| + 2^{-1075}` of `x_l/x_h` (`hw0`) and that `w = x_l` where `x_h = 1` (`hw1`); the range
`|ln x| ≤ 745.2` (`hX`), which every positive finite binary64 number meets; the selection of the scalings
(`DDLnRun`: `k = k₁ + k₂` with `k₂ ≤ 0`, and `e`, `e_φ`, `e_t`, `e_c` the exponents of step (2)'s `U`); and no
overflow, the model having no largest finite value. multidouble takes `k₁ = k/2`, rounded toward zero, so `k₂ > 0`
where `k > 0`; both steps then scale `x` up, which binary64 does exactly, and the value is that of the split
`(k, 0)`.
For binary64 the run must also meet the paper's (A2′): every product, fused multiply-add and quotient returns what it
would with an unbounded exponent range, as in the model, but the quotient `x_l/x_h` of the start, whose error a
hypothesis bounds, and those that only select `k`, an exponent or a branch, which the paper exempts -/
theorem prop44_ln_dd (hp : p = 53) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℝ × ℝ) (hx : DW p x) (hX0 : 0 < dwVal x) (hX : |Real.log (dwVal x)| ≤ 7452 / 10) (w : ℝ)
    (hw0 : |w - x.2 / x.1| ≤ u p * |x.2 / x.1| + (2 : ℝ) ^ (-1075 : ℤ)) (hw1 : x.1 = 1 → w = x.2)
    (k₁ k₂ e eφ et ec : ℤ) (hrun : DDLnRun p (ddOps p) S x (ddLnY0 p x w) k₁ k₂ e eφ et ec) :
    |dwVal (ddLn p (ddOps p) S x (ddLnY0 p x w) k₁ k₂ e eφ et ec) - Real.log (dwVal x)| ≤
      15351 / 1000 * u p ^ 2 * |Real.log (dwVal x)| + (2 : ℝ) ^ (-1071 : ℤ) :=
  prop44_ln p hp (ddOps_spec p (by omega)) S hS x hx hX0 hX w hw0 hw1 k₁ k₂ e eφ et ec
    (ddLnRun_sel p hp S hS x hx hX0 hX w hw0 hw1 k₁ k₂ e eφ et ec hrun)

/-- `DD::ln`'s result on the four algorithms is a double word, under exactly the hypotheses of `prop44_ln_dd`:
`y = DWPlusFP(y_c, y_0)` with `y_c` a double word (step (5)) and `y_0` a float. The octo-double logarithm asks it
of its start -/
theorem prop44_ln_dd_dw (hp : p = 53) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℝ × ℝ) (hx : DW p x) (hX0 : 0 < dwVal x) (hX : |Real.log (dwVal x)| ≤ 7452 / 10) (w : ℝ)
    (hw0 : |w - x.2 / x.1| ≤ u p * |x.2 / x.1| + (2 : ℝ) ^ (-1075 : ℤ)) (hw1 : x.1 = 1 → w = x.2)
    (k₁ k₂ e eφ et ec : ℤ) (hrun : DDLnRun p (ddOps p) S x (ddLnY0 p x w) k₁ k₂ e eφ et ec) :
    DW p (ddLn p (ddOps p) S x (ddLnY0 p x w) k₁ k₂ e eφ et ec) :=
  prop44_ln_dw p hp (ddOps_spec p (by omega)) S hS x hx hX0 hX w hw0 hw1 k₁ k₂ e eφ et ec
    (ddLnRun_sel p hp S hS x hx hX0 hX w hw0 hw1 k₁ k₂ e eφ et ec hrun)

/-- both parts of `DD::ln`'s result on the four algorithms are floats, under the hypotheses of `prop44_ln_dd` -/
theorem prop44_ln_dd_F (hp : p = 53) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℝ × ℝ) (hx : DW p x) (hX0 : 0 < dwVal x) (hX : |Real.log (dwVal x)| ≤ 7452 / 10) (w : ℝ)
    (hw0 : |w - x.2 / x.1| ≤ u p * |x.2 / x.1| + (2 : ℝ) ^ (-1075 : ℤ)) (hw1 : x.1 = 1 → w = x.2)
    (k₁ k₂ e eφ et ec : ℤ) (hrun : DDLnRun p (ddOps p) S x (ddLnY0 p x w) k₁ k₂ e eφ et ec) :
    F p (ddLn p (ddOps p) S x (ddLnY0 p x w) k₁ k₂ e eφ et ec).1 ∧
      F p (ddLn p (ddOps p) S x (ddLnY0 p x w) k₁ k₂ e eφ et ec).2 :=
  ⟨(prop44_ln_dd_dw p hp S hS x hx hX0 hX w hw0 hw1 k₁ k₂ e eφ et ec hrun).1,
    (prop44_ln_dd_dw p hp S hS x hx hX0 hX w hw0 hw1 k₁ k₂ e eφ et ec hrun).2.1⟩

/-- the high part of `DD::ln`'s result on the four algorithms is the rounded sum of its parts, under the
hypotheses of `prop44_ln_dd` -/
theorem prop44_ln_dd_rn (hp : p = 53) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℝ × ℝ) (hx : DW p x) (hX0 : 0 < dwVal x) (hX : |Real.log (dwVal x)| ≤ 7452 / 10) (w : ℝ)
    (hw0 : |w - x.2 / x.1| ≤ u p * |x.2 / x.1| + (2 : ℝ) ^ (-1075 : ℤ)) (hw1 : x.1 = 1 → w = x.2)
    (k₁ k₂ e eφ et ec : ℤ) (hrun : DDLnRun p (ddOps p) S x (ddLnY0 p x w) k₁ k₂ e eφ et ec) :
    RN p ((ddLn p (ddOps p) S x (ddLnY0 p x w) k₁ k₂ e eφ et ec).1 +
        (ddLn p (ddOps p) S x (ddLnY0 p x w) k₁ k₂ e eφ et ec).2) =
      (ddLn p (ddOps p) S x (ddLnY0 p x w) k₁ k₂ e eφ et ec).1 :=
  (prop44_ln_dd_dw p hp S hS x hx hX0 hX w hw0 hw1 k₁ k₂ e eφ et ec hrun).2.2

end ExpansionBounds
