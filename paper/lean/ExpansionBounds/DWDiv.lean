import ExpansionBounds.DWord
import FloatSpec.src.Prop.Sterbenz

/-!
# Double-word arithmetic: DWDivDW2

The quotient of two double-word numbers, Algorithm 17 of Joldes, Muller and Popescu (2017), within `15u² + 56u³` of
the exact quotient for `p ≥ 7` (their Theorem 7.1). The proof follows theirs: `t_h = RN(x_h/y_h)`, the product
`(r_h, r_l) = DWTimesFP1(y, t_h)` within `3u²/2 + 4u³` (`dwTimesFP1_err`), `x_h - r_h` exact by Sterbenz, and three more
roundings, each within `u` relatively. The bounds are kept relative to `|x_h|` and then to `|x/y|`, so no sign is fixed.
-/

namespace ExpansionBounds

/-- the first half of Theorem 7.1's analysis, on real numbers: `r_h` is within `(3u + 6u²)|x_h|` of `x_h` -/
theorem dwDiv_core1 {u xh yh yl th R r1 : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 128) (hy0 : yh ≠ 0)
    (hyl : |yl| ≤ u * |yh|) (hth : |th - xh / yh| ≤ u * |xh / yh|)
    (hR : |R - (yh + yl) * th| ≤ (3 / 2 * u ^ 2 + 4 * u ^ 3) * |(yh + yl) * th|) (hr1 : |r1 - R| ≤ u * |R|) :
    |(yh + yl) * th - xh| ≤ (2 * u + u ^ 2) * |xh| ∧
      |R - (yh + yl) * th| ≤ (3 / 2 * u ^ 2 + 4 * u ^ 3) * (1 + u) ^ 2 * |xh| ∧
      |r1 - xh| ≤ (3 * u + 6 * u ^ 2) * |xh| := by
  have hη0 : (0 : ℝ) ≤ 3 / 2 * u ^ 2 + 4 * u ^ 3 := by positivity
  have hB : 0 < |yh| := abs_pos.mpr hy0
  have hAB : |xh / yh| * |yh| = |xh| := by rw [← abs_mul, div_mul_cancel₀ _ hy0]
  have hA0 : 0 ≤ |xh / yh| := abs_nonneg _
  -- `|t_h| ≤ (1 + u)|q|`
  have hth' : |th| ≤ (1 + u) * |xh / yh| := by
    have := abs_sub_abs_le_abs_sub th (xh / yh)
    linarith
  -- `y t_h - x_h = (t_h - q) y_h + t_h y_l`
  have e1 : (yh + yl) * th - xh = (th - xh / yh) * yh + th * yl := by
    field_simp
    ring
  have b1 : |(th - xh / yh) * yh| ≤ u * |xh| := by
    rw [abs_mul, ← hAB, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hth hB.le
  have b2 : |th * yl| ≤ (1 + u) * u * |xh| := by
    rw [abs_mul]
    calc |th| * |yl| ≤ ((1 + u) * |xh / yh|) * (u * |yh|) :=
          mul_le_mul hth' hyl (abs_nonneg _) (by positivity)
      _ = (1 + u) * u * |xh| := by rw [← hAB]; ring
  have g1 : |(yh + yl) * th - xh| ≤ (2 * u + u ^ 2) * |xh| := by
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    calc _ ≤ u * |xh| + (1 + u) * u * |xh| := add_le_add b1 b2
      _ = (2 * u + u ^ 2) * |xh| := by ring
  have g2 : |(yh + yl) * th| ≤ (1 + u) ^ 2 * |xh| := by
    have := abs_sub_abs_le_abs_sub ((yh + yl) * th) xh
    calc |(yh + yl) * th| ≤ |xh| + (2 * u + u ^ 2) * |xh| := by linarith
      _ = (1 + u) ^ 2 * |xh| := by ring
  have g3 : |R - (yh + yl) * th| ≤ (3 / 2 * u ^ 2 + 4 * u ^ 3) * (1 + u) ^ 2 * |xh| := by
    rw [mul_assoc]
    exact hR.trans (mul_le_mul_of_nonneg_left g2 hη0)
  have gR : |R| ≤ (1 + (3 / 2 * u ^ 2 + 4 * u ^ 3)) * (1 + u) ^ 2 * |xh| := by
    have := abs_sub_abs_le_abs_sub R ((yh + yl) * th)
    calc |R| ≤ (1 + u) ^ 2 * |xh| + (3 / 2 * u ^ 2 + 4 * u ^ 3) * (1 + u) ^ 2 * |xh| := by linarith
      _ = _ := by ring
  refine ⟨g1, g3, ?_⟩
  have e2 : r1 - xh = (r1 - R) + (R - (yh + yl) * th) + ((yh + yl) * th - xh) := by ring
  rw [e2]
  refine (abs_add_three _ _ _).trans ?_
  have b3 : |r1 - R| ≤ u * ((1 + (3 / 2 * u ^ 2 + 4 * u ^ 3)) * (1 + u) ^ 2 * |xh|) :=
    hr1.trans (mul_le_mul_of_nonneg_left gR hu0.le)
  -- `(3u + 6u²) - ((1 + u)³(1 + η) - 1) = u²(3/2 - 19u/2 - 33u²/2 - 27u³/2 - 4u⁴)`
  have hpoly : (0 : ℝ) ≤ u ^ 2 * (3 / 2 - 19 / 2 * u - 33 / 2 * u ^ 2 - 27 / 2 * u ^ 3 - 4 * u ^ 4) := by
    have h2 : u ^ 2 ≤ 1 := by nlinarith
    have h3 : u ^ 3 ≤ 1 := by nlinarith [pow_nonneg hu0.le 2]
    have h4 : u ^ 4 ≤ 1 := by nlinarith [pow_nonneg hu0.le 3]
    refine mul_nonneg (by positivity) ?_
    nlinarith [pow_nonneg hu0.le 2, pow_nonneg hu0.le 3, pow_nonneg hu0.le 4]
  have hx := abs_nonneg xh
  nlinarith [mul_nonneg hpoly hx]

/-- the middle of Theorem 7.1's analysis, on real numbers: `x - y t_h` and the error of `δ` against `x - (r_h + r_l)`,
relative to `|x_h|` -/
theorem dwDiv_core2 {u xh xl yh yl th R r1 r2 δl δ : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 128)
    (hxl : |xl| ≤ u * |xh|) (g1 : |(yh + yl) * th - xh| ≤ (2 * u + u ^ 2) * |xh|)
    (g4 : |r1 - xh| ≤ (3 * u + 6 * u ^ 2) * |xh|) (hR : R = r1 + r2) (hr2 : |r2| ≤ u * |r1|)
    (hδl : |δl - (xl - r2)| ≤ u * |xl - r2|) (hδ : |δ - ((xh - r1) + δl)| ≤ u * |(xh - r1) + δl|) :
    |(xh + xl) - (yh + yl) * th| ≤ (3 * u + u ^ 2) * |xh| ∧
      |δ - ((xh + xl) - R)| ≤ (7 * u ^ 2 + 15 * u ^ 3) * |xh| := by
  have ha := abs_nonneg xh
  constructor
  · rw [show (xh + xl) - (yh + yl) * th = -((yh + yl) * th - xh) + xl by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    calc _ ≤ (2 * u + u ^ 2) * |xh| + u * |xh| := add_le_add g1 hxl
      _ = (3 * u + u ^ 2) * |xh| := by ring
  -- `|r_h| ≤ (1 + 3u + 6u²)|x_h|` and `|x_l - r_l| ≤ (2u + 3u² + 6u³)|x_h|`
  have s1 : |r1| ≤ (1 + 3 * u + 6 * u ^ 2) * |xh| := by
    have := abs_sub_abs_le_abs_sub r1 xh
    calc |r1| ≤ |xh| + (3 * u + 6 * u ^ 2) * |xh| := by linarith
      _ = _ := by ring
  have s2 : |xl - r2| ≤ (2 * u + 3 * u ^ 2 + 6 * u ^ 3) * |xh| := by
    refine (abs_sub _ _).trans ?_
    calc |xl| + |r2| ≤ u * |xh| + u * ((1 + 3 * u + 6 * u ^ 2) * |xh|) :=
          add_le_add hxl (hr2.trans (mul_le_mul_of_nonneg_left s1 hu0.le))
      _ = _ := by ring
  have s3 : |δl - (xl - r2)| ≤ u * ((2 * u + 3 * u ^ 2 + 6 * u ^ 3) * |xh|) :=
    hδl.trans (mul_le_mul_of_nonneg_left s2 hu0.le)
  have s3' : |δl| ≤ (1 + u) * ((2 * u + 3 * u ^ 2 + 6 * u ^ 3) * |xh|) := by
    have := abs_sub_abs_le_abs_sub δl (xl - r2)
    calc |δl| ≤ |xl - r2| + |δl - (xl - r2)| := by linarith
      _ ≤ _ := by linarith
  have s4 : |(xh - r1) + δl| ≤ (3 * u + 6 * u ^ 2) * |xh| + (1 + u) * ((2 * u + 3 * u ^ 2 + 6 * u ^ 3) * |xh|) := by
    refine (abs_add_le _ _).trans (add_le_add ?_ s3')
    rwa [abs_sub_comm]
  have s5 : |δ - ((xh - r1) + δl)| ≤
      u * ((3 * u + 6 * u ^ 2) * |xh| + (1 + u) * ((2 * u + 3 * u ^ 2 + 6 * u ^ 3) * |xh|)) :=
    hδ.trans (mul_le_mul_of_nonneg_left s4 hu0.le)
  rw [show δ - ((xh + xl) - R) = (δ - ((xh - r1) + δl)) + (δl - (xl - r2)) by rw [hR]; ring]
  refine (abs_add_le _ _).trans ?_
  -- `(7u² + 15u³) - α = u³(1 - 15u - 6u²)`
  have hpoly : (0 : ℝ) ≤ u ^ 3 * (1 - 15 * u - 6 * u ^ 2) := by
    refine mul_nonneg (by positivity) ?_
    nlinarith [pow_nonneg hu0.le 2]
  nlinarith [mul_nonneg hpoly ha]

/-- `δ/y_h` against `(x - y t_h)/y`, relative to `|x_h|/|y|`: the `β` of Theorem 7.1's proof -/
theorem dwDiv_core3 {u xh X yh yl Y th R δ : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 128) (hy0 : yh ≠ 0)
    (hY : Y = yh + yl) (hyl : |yl| ≤ u * |yh|) (g2 : |X - Y * th| ≤ (3 * u + u ^ 2) * |xh|)
    (g3 : |R - Y * th| ≤ (3 / 2 * u ^ 2 + 4 * u ^ 3) * (1 + u) ^ 2 * |xh|)
    (g5 : |δ - (X - R)| ≤ (7 * u ^ 2 + 15 * u ^ 3) * |xh|) :
    Y ≠ 0 ∧ |(X - Y * th) / Y| ≤ (3 * u + u ^ 2) * (|xh| / |Y|) ∧
      |δ / yh - (X - Y * th) / Y| ≤
        (23 / 2 * u ^ 2 + 63 / 2 * u ^ 3 + 63 / 2 * u ^ 4 + 27 / 2 * u ^ 5 + 4 * u ^ 6) * (|xh| / |Y|) := by
  have hyh : 0 < |yh| := abs_pos.mpr hy0
  have hyl' : yl = Y - yh := by rw [hY]; ring
  have hY1 : (1 - u) * |yh| ≤ |Y| := by
    have h := abs_sub Y yl
    rw [show Y - yl = yh by rw [hY]; ring] at h
    linarith only [h, hyl]
  have hY2 : |Y| ≤ (1 + u) * |yh| := by
    rw [hY]
    exact (abs_add_le yh yl).trans (by linarith only [hyl])
  have hYpos : 0 < |Y| := lt_of_lt_of_le (mul_pos (by linarith only [hu]) hyh) hY1
  have hYne : Y ≠ 0 := abs_pos.mp hYpos
  -- `A = |x_h|/|y|` and `B = |x_h|/|y_h|`
  obtain ⟨A, hA⟩ : ∃ A, A = |xh| / |Y| := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = |xh| / |yh| := ⟨_, rfl⟩
  rw [← hA]
  have hBA : B ≤ (1 + u) * A := by
    rw [hB, hA, div_le_iff₀ hyh, show (1 + u) * (|xh| / |Y|) * |yh| = |xh| * ((1 + u) * |yh|) / |Y| by ring,
      le_div_iff₀ hYpos]
    exact mul_le_mul_of_nonneg_left hY2 (abs_nonneg _)
  -- the terms of `δ/y_h`
  have he1 : |(X - Y * th) / Y| ≤ (3 * u + u ^ 2) * A := by
    rw [abs_div, hA, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right g2 hYpos.le
  have ht1 : |(X - Y * th) * (yl / (yh * Y))| ≤ u * (3 * u + u ^ 2) * A := by
    rw [abs_mul, abs_div, abs_mul]
    have h1 : |yl| / (|yh| * |Y|) ≤ u / |Y| := by
      rw [div_le_div_iff₀ (mul_pos hyh hYpos) hYpos]
      calc |yl| * |Y| ≤ u * |yh| * |Y| := mul_le_mul_of_nonneg_right hyl hYpos.le
        _ = u * (|yh| * |Y|) := by ring
    calc |X - Y * th| * (|yl| / (|yh| * |Y|)) ≤ ((3 * u + u ^ 2) * |xh|) * (u / |Y|) :=
          mul_le_mul g2 h1 (by positivity) (by positivity)
      _ = u * (3 * u + u ^ 2) * A := by rw [hA]; ring
  have ht2 : |(R - Y * th) / yh| ≤ (3 / 2 * u ^ 2 + 4 * u ^ 3) * (1 + u) ^ 2 * B := by
    rw [abs_div, hB, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right g3 hyh.le
  have ht3 : |(δ - (X - R)) / yh| ≤ (7 * u ^ 2 + 15 * u ^ 3) * B := by
    rw [abs_div, hB, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right g5 hyh.le
  have hsplit : δ / yh - (X - Y * th) / Y =
      (X - Y * th) * (yl / (yh * Y)) - (R - Y * th) / yh + (δ - (X - R)) / yh := by
    rw [hyl']
    field_simp
    ring
  -- `B ≤ (1 + u)A` in each term
  have k2 := mul_le_mul_of_nonneg_left hBA (by positivity : (0 : ℝ) ≤ (3 / 2 * u ^ 2 + 4 * u ^ 3) * (1 + u) ^ 2)
  have k3 := mul_le_mul_of_nonneg_left hBA (by positivity : (0 : ℝ) ≤ 7 * u ^ 2 + 15 * u ^ 3)
  obtain ⟨b1, b2⟩ := abs_le.mp ht1
  obtain ⟨c1, c2⟩ := abs_le.mp ht2
  obtain ⟨d1, d2⟩ := abs_le.mp ht3
  refine ⟨hYne, he1, ?_⟩
  rw [hsplit, abs_le]
  constructor
  · linarith only [b1, c2, d1, k2, k3]
  · linarith only [b2, c1, d2, k2, k3]

/-- the end of Theorem 7.1's analysis, on real numbers: `t_h + t_l` against `x/y` -/
theorem dwDiv_core4 {u xh X yh Y th δ tl : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 128) (hY0 : Y ≠ 0)
    (hxX : |xh| ≤ (1 + u) * |X|) (he1 : |(X - Y * th) / Y| ≤ (3 * u + u ^ 2) * (|xh| / |Y|))
    (hβ : |δ / yh - (X - Y * th) / Y| ≤
      (23 / 2 * u ^ 2 + 63 / 2 * u ^ 3 + 63 / 2 * u ^ 4 + 27 / 2 * u ^ 5 + 4 * u ^ 6) * (|xh| / |Y|))
    (htl : |tl - δ / yh| ≤ u * |δ / yh|) :
    |th + tl - X / Y| ≤ (15 * u ^ 2 + 56 * u ^ 3) * |X / Y| := by
  have hYpos : 0 < |Y| := abs_pos.mpr hY0
  obtain ⟨A, hA⟩ : ∃ A, A = |xh| / |Y| := ⟨_, rfl⟩
  rw [← hA] at he1 hβ
  have hAW : A ≤ (1 + u) * |X / Y| := by
    rw [abs_div, hA, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hxX hYpos.le
  have he : th + tl - X / Y = tl - (X - Y * th) / Y := by
    field_simp
    ring
  obtain ⟨a1, a2⟩ := abs_le.mp he1
  obtain ⟨b1, b2⟩ := abs_le.mp hβ
  have hq : |δ / yh| ≤ (3 * u + u ^ 2) * A +
      (23 / 2 * u ^ 2 + 63 / 2 * u ^ 3 + 63 / 2 * u ^ 4 + 27 / 2 * u ^ 5 + 4 * u ^ 6) * A := by
    rw [abs_le]
    constructor
    · linarith only [a1, b1]
    · linarith only [a2, b2]
  obtain ⟨f1, f2⟩ := abs_le.mp (htl.trans (mul_le_mul_of_nonneg_left hq hu0.le))
  have hc : |tl - (X - Y * th) / Y| ≤
      (29 / 2 * u ^ 2 + 44 * u ^ 3 + 63 * u ^ 4 + 45 * u ^ 5 + 35 / 2 * u ^ 6 + 4 * u ^ 7) * A := by
    rw [abs_le]
    constructor
    · linarith only [f1, b1]
    · linarith only [f2, b2]
  have hu1 : u ≤ 1 := by linarith only [hu]
  have p3 := pow_le_pow_of_le_one hu0.le hu1 (by norm_num : 2 ≤ 3)
  have p4 := pow_le_pow_of_le_one hu0.le hu1 (by norm_num : 2 ≤ 4)
  have p5 := pow_le_pow_of_le_one hu0.le hu1 (by norm_num : 2 ≤ 5)
  have p6 := pow_le_pow_of_le_one hu0.le hu1 (by norm_num : 2 ≤ 6)
  have p2 : u ^ 2 ≤ 1 / 16384 := by
    calc u ^ 2 ≤ (1 / 128 : ℝ) ^ 2 := pow_le_pow_left₀ hu0.le hu 2
      _ = 1 / 16384 := by norm_num
  -- `15u² + 56u³` less the bound is `u²(1/2 - 5u/2 - 107u² - ⋯)`
  have hg : (0 : ℝ) ≤ 1 / 2 - 5 / 2 * u - 107 * u ^ 2 - 108 * u ^ 3 - 125 / 2 * u ^ 4 - 43 / 2 * u ^ 5 - 4 * u ^ 6 := by
    linarith only [hu, p2, p3, p4, p5, p6]
  have hpoly : (29 / 2 * u ^ 2 + 44 * u ^ 3 + 63 * u ^ 4 + 45 * u ^ 5 + 35 / 2 * u ^ 6 + 4 * u ^ 7) * (1 + u) ≤
      15 * u ^ 2 + 56 * u ^ 3 := by
    linarith only [mul_nonneg (pow_nonneg hu0.le 2) hg]
  have hc0 : (0 : ℝ) ≤ 29 / 2 * u ^ 2 + 44 * u ^ 3 + 63 * u ^ 4 + 45 * u ^ 5 + 35 / 2 * u ^ 6 + 4 * u ^ 7 := by
    positivity
  rw [he]
  calc |tl - (X - Y * th) / Y| ≤ _ := hc
    _ ≤ (29 / 2 * u ^ 2 + 44 * u ^ 3 + 63 * u ^ 4 + 45 * u ^ 5 + 35 / 2 * u ^ 6 + 4 * u ^ 7) * ((1 + u) * |X / Y|) :=
        mul_le_mul_of_nonneg_left hAW hc0
    _ = (29 / 2 * u ^ 2 + 44 * u ^ 3 + 63 * u ^ 4 + 45 * u ^ 5 + 35 / 2 * u ^ 6 + 4 * u ^ 7) * (1 + u) * |X / Y| := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpoly (abs_nonneg _)

/-- `|t_l| ≤ |t_h|`, so the last Fast2Sum of DWDivDW2 is exact -/
theorem dwDiv_core5 {u xh X yh Y th R δ tl : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 128) (hy0 : yh ≠ 0)
    (hth : |th - xh / yh| ≤ u * |xh / yh|) (g2 : |X - Y * th| ≤ (3 * u + u ^ 2) * |xh|)
    (g3 : |R - Y * th| ≤ (3 / 2 * u ^ 2 + 4 * u ^ 3) * (1 + u) ^ 2 * |xh|)
    (g5 : |δ - (X - R)| ≤ (7 * u ^ 2 + 15 * u ^ 3) * |xh|) (htl : |tl - δ / yh| ≤ u * |δ / yh|) :
    |tl| ≤ |th| := by
  have hyh : 0 < |yh| := abs_pos.mpr hy0
  obtain ⟨B, hB⟩ : ∃ B, B = |xh| / |yh| := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  -- `|δ| ≤ (3u + ⋯)|x_h|`, so `|t_l| ≤ (1 + u)(3u + ⋯)B ≤ (1 - u)B ≤ |t_h|`
  have hδ : |δ| ≤ ((7 * u ^ 2 + 15 * u ^ 3) + (3 * u + u ^ 2) + (3 / 2 * u ^ 2 + 4 * u ^ 3) * (1 + u) ^ 2) * |xh| := by
    obtain ⟨m1, m2⟩ := abs_le.mp g2
    obtain ⟨n1, n2⟩ := abs_le.mp g3
    obtain ⟨o1, o2⟩ := abs_le.mp g5
    rw [abs_le]
    constructor
    · linarith only [m1, n2, o1]
    · linarith only [m2, n1, o2]
  have hq2 : |δ / yh| ≤
      ((7 * u ^ 2 + 15 * u ^ 3) + (3 * u + u ^ 2) + (3 / 2 * u ^ 2 + 4 * u ^ 3) * (1 + u) ^ 2) * B := by
    rw [abs_div, hB, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hδ hyh.le
  have hu1 : u ≤ 1 := by linarith only [hu]
  have q2 : u ^ 2 ≤ u := pow_le_of_le_one hu0.le hu1 (by norm_num)
  have q3 : u ^ 3 ≤ u := pow_le_of_le_one hu0.le hu1 (by norm_num)
  have q4 : u ^ 4 ≤ u := pow_le_of_le_one hu0.le hu1 (by norm_num)
  have q5 : u ^ 5 ≤ u := pow_le_of_le_one hu0.le hu1 (by norm_num)
  have q6 : u ^ 6 ≤ u := pow_le_of_le_one hu0.le hu1 (by norm_num)
  have hd : (1 + u) * ((7 * u ^ 2 + 15 * u ^ 3) + (3 * u + u ^ 2) + (3 / 2 * u ^ 2 + 4 * u ^ 3) * (1 + u) ^ 2) ≤
      1 - u := by
    linarith only [hu, q2, q3, q4, q5, q6]
  have hthB : (1 - u) * B ≤ |th| := by
    have h := abs_sub_abs_le_abs_sub (xh / yh) th
    rw [abs_sub_comm] at h
    rw [abs_div, ← hB] at hth h
    linarith only [h, hth]
  have htlq : |tl| ≤ (1 + u) * |δ / yh| := by
    have h := abs_sub_abs_le_abs_sub tl (δ / yh)
    linarith only [h, htl]
  calc |tl| ≤ (1 + u) * |δ / yh| := htlq
    _ ≤ (1 + u) * (((7 * u ^ 2 + 15 * u ^ 3) + (3 * u + u ^ 2) + (3 / 2 * u ^ 2 + 4 * u ^ 3) * (1 + u) ^ 2) * B) :=
        mul_le_mul_of_nonneg_left hq2 (by linarith only [hu0])
    _ = (1 + u) * ((7 * u ^ 2 + 15 * u ^ 3) + (3 * u + u ^ 2) + (3 / 2 * u ^ 2 + 4 * u ^ 3) * (1 + u) ^ 2) * B := by
        ring
    _ ≤ (1 - u) * B := mul_le_mul_of_nonneg_right hd hB0
    _ ≤ |th| := hthB

variable (p : ℤ) [Prec_gt_0 p]

/-- Sterbenz's lemma without a sign: `x - y` is in `F` when `y` is within `|x|/2` of `x` -/
theorem F_sub_of_near {x y : ℝ} (hx : F p x) (hy : F p y) (h : |y - x| ≤ |x| / 2) : F p (x - y) := by
  rcases le_total 0 x with h0 | h0
  · rw [abs_of_nonneg h0] at h
    obtain ⟨h1, h2⟩ := abs_le.mp h
    exact sterbenz 2 (FloatSpec.Core.FLX.FLX_exp p) x y hx hy (by norm_num) ⟨by linarith, by linarith⟩
  · rw [abs_of_nonpos h0] at h
    obtain ⟨h1, h2⟩ := abs_le.mp h
    have h3 := F_neg p (sterbenz 2 (FloatSpec.Core.FLX.FLX_exp p) (-x) (-y) (F_neg p hx) (F_neg p hy) (by norm_num)
      ⟨by linarith, by linarith⟩)
    rwa [show -(-x - -y) = x - y by ring] at h3

omit [Prec_gt_0 p] in
theorem u_le_128th (hp : 7 ≤ p) : u p ≤ 1 / 128 := by
  unfold u
  calc (2 : ℝ) ^ (-p) ≤ (2 : ℝ) ^ (-7 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ = 1 / 128 := by norm_num

/-- DWDivDW2, Algorithm 17 of Joldes, Muller and Popescu: `(x_h, x_l) / (y_h, y_l)` -/
noncomputable def dwDivDW2 (xh xl yh yl : ℝ) : ℝ × ℝ :=
  let th := RN p (xh / yh)
  let r := dwTimesFP1 p yh yl th
  let πh := RN p (xh - r.1)
  let δl := RN p (xl - r.2)
  let δ := RN p (πh + δl)
  let tl := RN p (δ / yh)
  fastTwoSum p th tl

/-- a double word's low part is at most `u` times its high part -/
theorem dw_lo_le_u {xh xl : ℝ} (hdw : RN p (xh + xl) = xh) : |xl| ≤ u p * |xh| := by
  have h := abs_RN_sub_le_u_RN p (xh + xl)
  rwa [hdw, show xh - (xh + xl) = -xl by ring, abs_neg] at h

/-- Theorem 7.1 of JMP17: for `p ≥ 7`, DWDivDW2 of the double words `x = (x_h, x_l)` and `y = (y_h, y_l)`, `y_h ≠ 0`,
is within `15u² + 56u³` of `x/y`, relatively; its result is a double word -/
theorem dwDivDW2_err (hp : 7 ≤ p) {xh xl yh yl : ℝ} (hx : RN p (xh + xl) = xh) (hy : RN p (yh + yl) = yh)
    (hy0 : yh ≠ 0) :
    |(dwDivDW2 p xh xl yh yl).1 + (dwDivDW2 p xh xl yh yl).2 - (xh + xl) / (yh + yl)| ≤
        (15 * u p ^ 2 + 56 * u p ^ 3) * |(xh + xl) / (yh + yl)| ∧
      RN p ((dwDivDW2 p xh xl yh yl).1 + (dwDivDW2 p xh xl yh yl).2) = (dwDivDW2 p xh xl yh yl).1 := by
  have hu0 := u_pos p
  have hu := u_le_128th p hp
  have hxF : F p xh := hx ▸ F_RN p _
  have hyF : F p yh := hy ▸ F_RN p _
  have hxl := dw_lo_le_u p hx
  have hyl := dw_lo_le_u p hy
  have hxX : |xh| ≤ (1 + u p) * |xh + xl| := by
    have h := abs_RN_le p (xh + xl)
    rwa [hx] at h
  -- `t_h` and the product `(r_h, r_l)`
  obtain ⟨th, hthd⟩ : ∃ th, th = RN p (xh / yh) := ⟨_, rfl⟩
  have hthF : F p th := hthd ▸ F_RN p _
  have hth : |th - xh / yh| ≤ u p * |xh / yh| := by
    rw [hthd]
    exact (abs_RN_sub_le_us p _).trans (mul_le_mul_of_nonneg_right (us_le_u p) (abs_nonneg _))
  obtain ⟨r, hrd⟩ : ∃ r, r = dwTimesFP1 p yh yl th := ⟨_, rfl⟩
  have hR : |r.1 + r.2 - (yh + yl) * th| ≤ (3 / 2 * u p ^ 2 + 4 * u p ^ 3) * |(yh + yl) * th| := by
    rw [hrd]
    exact dwTimesFP1_err p (by omega) hyF hthF hy
  have hrdw : RN p (r.1 + r.2) = r.1 := by
    rw [hrd]
    exact dwTimesFP1_dw p (by omega) hyF hthF hy
  have hr1F : F p r.1 := hrdw ▸ F_RN p _
  have hr1 : |r.1 - (r.1 + r.2)| ≤ u p * |r.1 + r.2| := by
    have h := (abs_RN_sub_le_us p (r.1 + r.2)).trans (mul_le_mul_of_nonneg_right (us_le_u p) (abs_nonneg _))
    rwa [hrdw] at h
  have hr2 := dw_lo_le_u p hrdw
  obtain ⟨g1, g3, g4⟩ := dwDiv_core1 hu0 hu hy0 hyl hth hR hr1
  -- `x_h - r_h` is exact
  have hπ : RN p (xh - r.1) = xh - r.1 := by
    refine RN_of_F p (F_sub_of_near p hxF hr1F (g4.trans ?_))
    have : 3 * u p + 6 * u p ^ 2 ≤ 1 / 2 := by nlinarith
    calc (3 * u p + 6 * u p ^ 2) * |xh| ≤ 1 / 2 * |xh| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
      _ = |xh| / 2 := by ring
  obtain ⟨δl, hδld⟩ : ∃ δl, δl = RN p (xl - r.2) := ⟨_, rfl⟩
  have hδl : |δl - (xl - r.2)| ≤ u p * |xl - r.2| := by
    rw [hδld]
    exact (abs_RN_sub_le_us p _).trans (mul_le_mul_of_nonneg_right (us_le_u p) (abs_nonneg _))
  obtain ⟨δ, hδd⟩ : ∃ δ, δ = RN p ((xh - r.1) + δl) := ⟨_, rfl⟩
  have hδ : |δ - ((xh - r.1) + δl)| ≤ u p * |(xh - r.1) + δl| := by
    rw [hδd]
    exact (abs_RN_sub_le_us p _).trans (mul_le_mul_of_nonneg_right (us_le_u p) (abs_nonneg _))
  obtain ⟨g2, g5⟩ := dwDiv_core2 (yh := yh) (yl := yl) (th := th) hu0 hu hxl g1 g4 rfl hr2 hδl hδ
  obtain ⟨tl, htld⟩ : ∃ tl, tl = RN p (δ / yh) := ⟨_, rfl⟩
  have htl : |tl - δ / yh| ≤ u p * |δ / yh| := by
    rw [htld]
    exact (abs_RN_sub_le_us p _).trans (mul_le_mul_of_nonneg_right (us_le_u p) (abs_nonneg _))
  obtain ⟨hY0, he1, hβ⟩ := dwDiv_core3 hu0 hu hy0 rfl hyl g2 g3 g5
  have herr := dwDiv_core4 hu0 hu hY0 hxX he1 hβ htl
  have hle := dwDiv_core5 hu0 hu hy0 hth g2 g3 g5 htl
  -- the last Fast2Sum is exact
  have hdef : dwDivDW2 p xh xl yh yl = fastTwoSum p th tl := by
    simp only [dwDivDW2]
    rw [← hthd, ← hrd, hπ, ← hδld, ← hδd, ← htld]
  have hsum := fastTwoSum_add p (by omega) hthF (htld ▸ F_RN p _) hle
  rw [hdef]
  refine ⟨by rw [hsum]; exact herr, ?_⟩
  rw [hsum]
  rfl

end ExpansionBounds
