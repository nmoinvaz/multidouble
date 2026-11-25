import ExpansionBounds.SqrtDD8Delta
import ExpansionBounds.DWSqrt

/-!
# Theorem 22: the double-word start

`thm22` takes the bounds on the double-word start of SQRT^DD as hypotheses. Here the start is computed:
`(a_0', a_1') = FastTwoSum(a_0, a_1)`, `v = SQRTDWtoDW(a_0', a_1')` (`sqrtDW`) and `r = DWDivDW2((1, 0), v)`
(`dwDivDW2`). `FastTwoSum` is exact and returns a double word, `sqrtDW_err` gives `v` within `η_1 = 25u²/8` of
`√(a_0 + a_1)`, and `dwDivDW2_err` gives `rv` within `η_2 = 15u² + 56u³` of one and `r` a double word. So Theorem 22
holds with no hypothesis on the start (`thm22_start`), and at `n = 8`, `p = 53` with its constant (`sqrtdd8_start`).
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) [Prec_gt_0 p]

/-- the start of SQRT^DD: `(a_0', a_1') = FastTwoSum(a_0, a_1)`, `v = SQRTDWtoDW(a_0', a_1')` and
`r = DWDivDW2((1, 0), v)` -/
noncomputable def sqrtDDStart (a0 a1 : ℝ) : ℝ × ℝ :=
  let a := fastTwoSum p a0 a1
  let v := sqrtDW p a.1 a.2
  dwDivDW2 p 1 0 v.1 v.2

/-- the hypotheses of `thm22` on the start hold for `sqrtDDStart` -/
theorem sqrtDDStart_spec (hp : 7 ≤ p) {a0 a1 : ℝ} (ha0 : F p a0) (ha1 : F p a1) (h01 : |a1| ≤ |a0|)
    (hpos : 0 < a0 + a1) :
    F p (sqrtDDStart p a0 a1).1 ∧ F p (sqrtDDStart p a0 a1).2 ∧
      |(sqrtDDStart p a0 a1).2| ≤ u p * |(sqrtDDStart p a0 a1).1| ∧
      ∃ v, |v - Real.sqrt (a0 + a1)| ≤ ddEta1 p * Real.sqrt (a0 + a1) ∧
        |((sqrtDDStart p a0 a1).1 + (sqrtDDStart p a0 a1).2) * v - 1| ≤ ddEta2 p := by
  have hu0 := u_pos p
  have hu := u_le_128th p hp
  -- `FastTwoSum` is exact, and its result a double word
  obtain ⟨a, had⟩ : ∃ a, a = fastTwoSum p a0 a1 := ⟨_, rfl⟩
  have hsum : a.1 + a.2 = a0 + a1 := by rw [had]; exact fastTwoSum_add p (by omega) ha0 ha1 h01
  have ha1' : a.1 = RN p (a0 + a1) := by rw [had]; rfl
  have hdwa : RN p (a.1 + a.2) = a.1 := by rw [hsum, ha1']
  have hapos : 0 < a.1 := by
    have h := RN_mono p hpos.le
    rw [RN_zero, ← ha1'] at h
    rcases h.lt_or_eq with h | h
    · exact h
    · rw [ha1'] at h
      exact absurd (RN_eq_zero p h.symm) hpos.ne'
  -- the square root
  obtain ⟨v, hvd⟩ : ∃ v, v = sqrtDW p a.1 a.2 := ⟨_, rfl⟩
  obtain ⟨hv, hdwv⟩ := sqrtDW_err p (by omega) hdwa hapos
  rw [← hvd, hsum] at hv
  rw [← hvd] at hdwv
  have hS : 0 < Real.sqrt (a0 + a1) := Real.sqrt_pos.mpr hpos
  have hV : 0 < v.1 + v.2 := by
    have h := (abs_le.mp hv).1
    have hu2 : u p ^ 2 ≤ 1 / 16384 := by
      calc u p ^ 2 ≤ (1 / 128 : ℝ) ^ 2 := pow_le_pow_left₀ hu0.le hu 2
        _ = 1 / 16384 := by norm_num
    have h2 := mul_lt_mul_of_pos_right (by linarith : 25 / 8 * u p ^ 2 < 1) hS
    linarith
  have hv1 : v.1 ≠ 0 := fun h => hV.ne' (RN_eq_zero p (hdwv.trans h))
  -- the reciprocal
  have hdef : sqrtDDStart p a0 a1 = dwDivDW2 p 1 0 v.1 v.2 := by
    simp only [sqrtDDStart]
    rw [← had, ← hvd]
  obtain ⟨hr, hdwr⟩ := dwDivDW2_err p hp (xh := 1) (xl := 0) (by rw [add_zero, RN_of_F p (F_one p)]) hdwv hv1
  rw [← hdef, add_zero] at hr
  rw [← hdef] at hdwr
  refine ⟨by rw [← hdwr]; exact F_RN p _, by rw [hdef]; exact F_RN p _, dw_lo_le_u p hdwr, v.1 + v.2, hv, ?_⟩
  -- `(r - 1/v)v = rv - 1`
  have hVne := hV.ne'
  have h := mul_le_mul_of_nonneg_right hr (abs_nonneg (v.1 + v.2))
  rw [← abs_mul, show ((sqrtDDStart p a0 a1).1 + (sqrtDDStart p a0 a1).2 - 1 / (v.1 + v.2)) * (v.1 + v.2) =
    ((sqrtDDStart p a0 a1).1 + (sqrtDDStart p a0 a1).2) * (v.1 + v.2) - 1 by field_simp,
    mul_assoc, ← abs_mul, one_div_mul_cancel hVne, abs_one, mul_one] at h
  exact h

variable (n : ℕ)

/-- Theorem 22, the whole algorithm: SQRT^DD_n of `x` on `H(θ)`, from the start `sqrtDDStart` of the scaled operand,
is within `δ^DD√x` of `√x` -/
theorem thm22_start (hp : 7 ≤ p) (hn : 2 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {θ : ℝ} (hθ : 0 ≤ θ)
    (hρ : 2 * (θ * u p) < 1) (x : ℕ → ℝ) (hx : ∀ i < n, F p (x i)) (hH : Htheta p n θ x) (hx0 : 0 < x 0) :
    |Real.sqrt (∑ i ∈ range n, x i) -
        (sqrtDDOp p n x (sqrtDDStart p (sqrtA p x 0) (sqrtA p x 1)).1
          (sqrtDDStart p (sqrtA p x 0) (sqrtA p x 1)).2).sum| ≤
      ddDelta p n (θ * u p) * Real.sqrt (∑ i ∈ range n, x i) := by
  obtain ⟨haF, ha0, haH, -, -, -, -, -, -⟩ := sqrt_setup p n (by omega) hθ hρ x hx hH hx0
  -- `|a_1| ≤ θu a_0 < a_0/2`
  have h1 := haH 1 (by omega)
  rw [pow_one] at h1
  have h2 : θ * u p * sqrtA p x 0 ≤ 1 / 2 * sqrtA p x 0 := mul_le_mul_of_nonneg_right (by linarith) ha0.le
  have h01 : |sqrtA p x 1| ≤ |sqrtA p x 0| := by
    rw [abs_of_pos ha0]
    linarith
  have hpos : 0 < sqrtA p x 0 + sqrtA p x 1 := by
    have := (abs_le.mp h1).1
    linarith
  obtain ⟨hF0, hF1, h10, v, hv, hrv⟩ := sqrtDDStart_spec p hp (haF 0 (by omega)) (haF 1 (by omega)) h01 hpos
  exact thm22 p n hp hn hA3 hθ hρ x hx hH hx0 v _ _ hF0 hF1 hv hrv h10

/-- Theorem 22 at `n = 8`, `p = 53`, the whole algorithm: SQRT^DD of `x` on `H(2)` is within `3.0000319u^8√x` of
`√x` -/
theorem sqrtdd8_start (hp : p = 53) (x : ℕ → ℝ) (hx : ∀ i < 8, F p (x i)) (hH : Htheta p 8 2 x) (hx0 : 0 < x 0) :
    |Real.sqrt (∑ i ∈ range 8, x i) -
        (sqrtDDOp p 8 x (sqrtDDStart p (sqrtA p x 0) (sqrtA p x 1)).1
          (sqrtDDStart p (sqrtA p x 0) (sqrtA p x 1)).2).sum| ≤
      3.0000319 * u p ^ 8 * Real.sqrt (∑ i ∈ range 8, x i) := by
  have hu := u_53 p hp
  exact (thm22_start p 8 (by rw [hp]; norm_num) (by norm_num) (by rw [hu]; norm_num) (θ := 2) (by norm_num)
    (by rw [hu]; norm_num) x hx hH hx0).trans
    (mul_le_mul_of_nonneg_right (ddDelta8_two p hp) (Real.sqrt_nonneg _))

end ExpansionBounds
