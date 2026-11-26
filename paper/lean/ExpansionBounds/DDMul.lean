import ExpansionBounds.DWDiv
import ExpansionBounds.DWPlusFP

/-!
# multidouble's double-double product

`impl Mul for DD`: `(c_h, c_ℓ) = TwoProd(x_h, y_h)`, `t_1 = RN(x_h y_ℓ + c_ℓ)` and `t_2 = RN(x_ℓ y_h + t_1)` by fused
multiply-adds, and `(z_h, z_ℓ) = FastTwoSum(c_h, t_2)` (`ddMul`). The error is
`x_ℓ y_ℓ - (t_1 - (x_h y_ℓ + c_ℓ)) - (t_2 - (x_ℓ y_h + t_1))`, at most `(6 + 2u)u² |x_h y_h|` from
`|x_ℓ| ≤ u|x_h|`, `|y_ℓ| ≤ u|y_h|` and `|c_ℓ| ≤ u|x_h y_h|`; so the result is a double word within
`(6 + 2u)u²/(1 - u)²` of `xy`, relatively (`ddMul_good`), for `p ≥ 3`.
-/

namespace ExpansionBounds

variable (p : ℤ) [Prec_gt_0 p]

/-- multidouble's double-double product -/
noncomputable def ddMul (x y : ℝ × ℝ) : ℝ × ℝ :=
  fastTwoSum p (twoProd p x.1 y.1).1 (RN p (x.2 * y.1 + RN p (x.1 * y.2 + (twoProd p x.1 y.1).2)))

/-- the product of two double words is a double word within `(6 + 2u)u²/(1 - u)²` of their product, relatively -/
theorem ddMul_good (hp : 3 ≤ p) {x y : ℝ × ℝ} (hx : DW p x) (hy : DW p y) :
    DW p (ddMul p x y) ∧
      |dwVal (ddMul p x y) - dwVal x * dwVal y| ≤ (6 + 2 * u p) * u p ^ 2 / (1 - u p) ^ 2 * |dwVal x * dwVal y| := by
  obtain ⟨hxh, hxl, hdx⟩ := hx
  obtain ⟨hyh, hyl, hdy⟩ := hy
  obtain ⟨xh, xl⟩ := x
  obtain ⟨yh, yl⟩ := y
  simp only at hxh hxl hdx hyh hyl hdy
  have hu := u_pos p
  have hu8 : u p ≤ 1 / 8 := by
    unfold u
    calc (2 : ℝ) ^ (-p) ≤ (2 : ℝ) ^ (-3 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = 1 / 8 := by norm_num
  set P := xh * yh with hP
  obtain ⟨hsum, hcl, -⟩ := facts_c p hxh hyh
  set ch := (twoProd p xh yh).1 with hch
  set cl := (twoProd p xh yh).2 with hcl_def
  have hcl' : |cl| ≤ u p * |P| := hcl.trans (mul_le_mul_of_nonneg_right (us_le_u p) (abs_nonneg _))
  have hxl' : |xl| ≤ u p * |xh| := dw_lo_le_u p hdx
  have hyl' : |yl| ≤ u p * |yh| := dw_lo_le_u p hdy
  have hP0 : 0 ≤ |P| := abs_nonneg _
  -- the two fused multiply-adds
  set A := xh * yl + cl with hA
  set t1 := RN p A with ht1
  set B := xl * yh + t1 with hB
  set t2 := RN p B with ht2
  have hxyl : |xh * yl| ≤ u p * |P| := by
    rw [abs_mul, hP, abs_mul]
    calc |xh| * |yl| ≤ |xh| * (u p * |yh|) := mul_le_mul_of_nonneg_left hyl' (abs_nonneg _)
      _ = u p * (|xh| * |yh|) := by ring
  have hxly : |xl * yh| ≤ u p * |P| := by
    rw [abs_mul, hP, abs_mul]
    calc |xl| * |yh| ≤ u p * |xh| * |yh| := mul_le_mul_of_nonneg_right hxl' (abs_nonneg _)
      _ = u p * (|xh| * |yh|) := by ring
  have hxlyl : |xl * yl| ≤ u p ^ 2 * |P| := by
    rw [abs_mul, hP, abs_mul]
    calc |xl| * |yl| ≤ (u p * |xh|) * (u p * |yh|) :=
          mul_le_mul hxl' hyl' (abs_nonneg _) (by positivity)
      _ = u p ^ 2 * (|xh| * |yh|) := by ring
  have hA' : |A| ≤ 2 * u p * |P| := by
    calc |A| ≤ |xh * yl| + |cl| := abs_add_le _ _
      _ ≤ 2 * u p * |P| := by linarith
  have he1 : |t1 - A| ≤ u p * |A| :=
    (abs_RN_sub_le_us p A).trans (mul_le_mul_of_nonneg_right (us_le_u p) (abs_nonneg _))
  have ht1' : |t1| ≤ (1 + u p) * |A| := abs_RN_le p A
  have hB' : |B| ≤ (3 + 2 * u p) * u p * |P| := by
    calc |B| ≤ |xl * yh| + |t1| := abs_add_le _ _
      _ ≤ u p * |P| + (1 + u p) * (2 * u p * |P|) := by
          gcongr
          exact ht1'.trans (mul_le_mul_of_nonneg_left hA' (by linarith))
      _ = (3 + 2 * u p) * u p * |P| := by ring
  have he2 : |t2 - B| ≤ u p * |B| :=
    (abs_RN_sub_le_us p B).trans (mul_le_mul_of_nonneg_right (us_le_u p) (abs_nonneg _))
  have ht2' : |t2| ≤ (1 + u p) * |B| := abs_RN_le p B
  -- FastTwoSum is exact: `|t_2| ≤ |c_h|`
  have hch' : |P| / (1 + u p) ≤ |ch| := abs_RN_ge p P
  have hsmall : |t2| ≤ |ch| := by
    have h1 : |t2| ≤ (1 + u p) * ((3 + 2 * u p) * u p * |P|) :=
      ht2'.trans (mul_le_mul_of_nonneg_left hB' (by linarith))
    have h2 : (1 + u p) * ((3 + 2 * u p) * u p * |P|) ≤ |P| / (1 + u p) := by
      rw [le_div_iff₀ (by linarith)]
      have : (1 + u p) * ((3 + 2 * u p) * u p) * (1 + u p) ≤ 1 := by
        calc (1 + u p) * ((3 + 2 * u p) * u p) * (1 + u p) ≤ (9 / 8) * ((13 / 4) * (1 / 8)) * (9 / 8) := by
              gcongr <;> linarith
          _ ≤ 1 := by norm_num
      nlinarith
    linarith
  have hexact : (fastTwoSum p ch t2).1 + (fastTwoSum p ch t2).2 = ch + t2 :=
    fastTwoSum_add p (by omega) (F_RN p _) (F_RN p _) hsmall
  have hres : ddMul p (xh, xl) (yh, yl) = fastTwoSum p ch t2 := rfl
  refine ⟨by rw [hres]; exact fastTwoSum_dw p hexact, ?_⟩
  -- the error and its bound
  have hval : dwVal (ddMul p (xh, xl) (yh, yl)) - dwVal (xh, xl) * dwVal (yh, yl) =
      (t2 - B) + (t1 - A) - xl * yl := by
    rw [hres]
    unfold dwVal
    rw [hexact]
    simp only []
    have : ch = P - cl := by linarith
    rw [this, hB, hA, hP]
    ring
  rw [hval]
  have herr : |(t2 - B) + (t1 - A) - xl * yl| ≤ (6 + 2 * u p) * u p ^ 2 * |P| := by
    calc |(t2 - B) + (t1 - A) - xl * yl| ≤ |t2 - B| + |t1 - A| + |xl * yl| := by
          have := abs_sub (t2 - B + (t1 - A)) (xl * yl)
          have := abs_add_le (t2 - B) (t1 - A)
          linarith
      _ ≤ u p * ((3 + 2 * u p) * u p * |P|) + u p * (2 * u p * |P|) + u p ^ 2 * |P| := by
          gcongr
          · exact he2.trans (mul_le_mul_of_nonneg_left hB' hu.le)
          · exact he1.trans (mul_le_mul_of_nonneg_left hA' hu.le)
      _ = (6 + 2 * u p) * u p ^ 2 * |P| := by ring
  -- `|xy| ≥ (1 - u)² |x_h y_h|`
  have hxy : (1 - u p) ^ 2 * |P| ≤ |dwVal (xh, xl) * dwVal (yh, yl)| := by
    unfold dwVal
    simp only []
    rw [abs_mul, abs_mul]
    have h1 : (1 - u p) * |xh| ≤ |xh + xl| := by
      have := abs_sub_abs_le_abs_sub xh (-xl)
      rw [sub_neg_eq_add, abs_neg] at this
      linarith
    have h2 : (1 - u p) * |yh| ≤ |yh + yl| := by
      have := abs_sub_abs_le_abs_sub yh (-yl)
      rw [sub_neg_eq_add, abs_neg] at this
      linarith
    calc (1 - u p) ^ 2 * (|xh| * |yh|) = ((1 - u p) * |xh|) * ((1 - u p) * |yh|) := by ring
      _ ≤ |xh + xl| * |yh + yl| := mul_le_mul h1 h2 (mul_nonneg (by linarith) (abs_nonneg _)) (abs_nonneg _)
  have hpos : 0 < (1 - u p) ^ 2 := by
    have : 0 < 1 - u p := by linarith
    positivity
  calc |(t2 - B) + (t1 - A) - xl * yl| ≤ (6 + 2 * u p) * u p ^ 2 * |P| := herr
    _ = (6 + 2 * u p) * u p ^ 2 / (1 - u p) ^ 2 * ((1 - u p) ^ 2 * |P|) := by
        have h1u : 1 - u p ≠ 0 := (by linarith : (0 : ℝ) < 1 - u p).ne'
        field_simp
    _ ≤ (6 + 2 * u p) * u p ^ 2 / (1 - u p) ^ 2 * |dwVal (xh, xl) * dwVal (yh, yl)| :=
        mul_le_mul_of_nonneg_left hxy (by positivity)

end ExpansionBounds
