import ExpansionBounds.AccDWPlusDW
import ExpansionBounds.DWSqrt

/-!
# DWTimesDW2, the product of two double words

Algorithm 11 of Joldes, Muller and Popescu (2017), the MUL of `DD::exp` and `DD::ln`, with a fused multiply-add:

  `(c_h, c_ℓ1) = TwoProd(x_h, y_h)`, `t_ℓ = RN(x_h y_ℓ)`, `c_ℓ2 = RN(t_ℓ + x_ℓ y_h)`, `c_ℓ3 = RN(c_ℓ1 + c_ℓ2)`,
  `(z_h, z_ℓ) = FastTwoSum(c_h, c_ℓ3)`.

Theorem 2.7 of Muller and Rideau (2022), with its result a double word (`dwTimesDW2_good`): for `p ≥ 5` and double
words `x` and `y`, the result is a double word within `5u²/(1 + u)²` of `xy`, relatively. On `x_h, y_h ∈ [1, 2)`
the error is `-x_ℓ y_ℓ + ε₁ + ε₃ + ε₄`, the `ε` being the rounding errors of `t_ℓ`, `c_ℓ2` and `c_ℓ3`, at most
`8u²` in all. The cases are those of the paper's section 2.7: `x_h y_h ≥ 2`, where `xy ≥ 2(1 - u)²`; and
`x_h y_h < 2`, where `|c_ℓ1 + c_ℓ2| ≤ 4u` and the error is at most `5u²` with `xy ≥ (1 + u)²`, or `x_h` or `y_h` is
`1`, `c_ℓ1 = 0`, and the error is at most `4u²` with `xy ≥ (1 - u/2)²`.

The paper bounds `x_h + y_h` by its Lemma 2.10 (`≤ 3 - 2u` where `x_h y_h ≤ 2`); `x_h + y_h ≤ x_h y_h + 1 < 3`
suffices here. Where `x_h` or `y_h` is `1` the paper states `|η| ≤ 3u²`; the proof here uses `4u²`, which holds for
either and is enough for `p ≥ 5`.

`dwMul_extend` carries a bound proved on high parts in `[1, 2)` to every pair of double words, for a product that
commutes with the scalings by powers of two and with the negations; DWTimesDW3 uses it too.
-/

namespace ExpansionBounds

variable (p : ℤ)

/-- DWTimesDW2: `(c_h, c_ℓ1) = TwoProd(x_h, y_h)`, `t_ℓ = RN(x_h y_ℓ)`, `c_ℓ2 = RN(t_ℓ + x_ℓ y_h)`,
`c_ℓ3 = RN(c_ℓ1 + c_ℓ2)` and `(z_h, z_ℓ) = FastTwoSum(c_h, c_ℓ3)` -/
noncomputable def dwTimesDW2 (x y : ℝ × ℝ) : ℝ × ℝ :=
  fastTwoSum p (twoProd p x.1 y.1).1 (RN p ((twoProd p x.1 y.1).2 + RN p (RN p (x.1 * y.2) + x.2 * y.1)))

/-- DWTimesDW2 commutes with scalings by powers of two -/
theorem dwTimesDW2_scale (a b : ℤ) (x y : ℝ × ℝ) :
    dwTimesDW2 p ((2 : ℝ) ^ a * x.1, (2 : ℝ) ^ a * x.2) ((2 : ℝ) ^ b * y.1, (2 : ℝ) ^ b * y.2) =
      ((2 : ℝ) ^ (a + b) * (dwTimesDW2 p x y).1, (2 : ℝ) ^ (a + b) * (dwTimesDW2 p x y).2) := by
  have e : ∀ s t : ℝ, (2 : ℝ) ^ a * s * ((2 : ℝ) ^ b * t) = (2 : ℝ) ^ (a + b) * (s * t) := fun s t => by
    rw [zpow_add₀ two_ne_zero]; ring
  unfold dwTimesDW2
  simp only [twoProd_scale, e, RN_zpow_mul, ← mul_add, fastTwoSum_scale]

/-- DWTimesDW2 of a zero `x` is zero -/
theorem dwTimesDW2_zero_left (y : ℝ × ℝ) : dwTimesDW2 p (0, 0) y = (0, 0) := by
  simp [dwTimesDW2, twoProd, fastTwoSum, RN_zero]

/-- DWTimesDW2 by a zero `y` is zero -/
theorem dwTimesDW2_zero_right (x : ℝ × ℝ) : dwTimesDW2 p x (0, 0) = (0, 0) := by
  simp [dwTimesDW2, twoProd, fastTwoSum, RN_zero]

/-- an error of at most `G u²` at a product with `G (1 + u)² ≤ 5|xy|` is within the theorem's relative bound -/
theorem mul_rel (hu : 0 < u p) {η X G : ℝ} (hη : |η| ≤ G * u p ^ 2) (hX : G * (1 + u p) ^ 2 ≤ 5 * |X|) :
    |η| ≤ 5 * u p ^ 2 / (1 + u p) ^ 2 * |X| := by
  have h1 : (0 : ℝ) < (1 + u p) ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ h1]
  calc |η| * (1 + u p) ^ 2 ≤ G * u p ^ 2 * (1 + u p) ^ 2 := mul_le_mul_of_nonneg_right hη h1.le
    _ = u p ^ 2 * (G * (1 + u p) ^ 2) := by ring
    _ ≤ u p ^ 2 * (5 * |X|) := mul_le_mul_of_nonneg_left hX (by positivity)
    _ = 5 * u p ^ 2 * |X| := by ring

/-- the conclusion of a product's theorem at `(x_h, x_ℓ)` and `(y_h, y_ℓ)`: the result of `f` is a double word within
`c` of `xy`, relatively -/
def DWMulWithin (f : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ) (c xh xl yh yl : ℝ) : Prop :=
  DW p (f (xh, xl) (yh, yl)) ∧ |dwVal (f (xh, xl) (yh, yl)) - (xh + xl) * (yh + yl)| ≤ c * |(xh + xl) * (yh + yl)|

variable [Prec_gt_0 p]

/-- DWTimesDW2 commutes with the negation of `x` -/
theorem dwTimesDW2_neg_left (x y : ℝ × ℝ) :
    dwTimesDW2 p (-x.1, -x.2) y = (-(dwTimesDW2 p x y).1, -(dwTimesDW2 p x y).2) := by
  unfold dwTimesDW2
  simp only [twoProd_neg_left, neg_mul, RN_neg, ← neg_add, fastTwoSum_neg]

/-- DWTimesDW2 commutes with the negation of `y` -/
theorem dwTimesDW2_neg_right (x y : ℝ × ℝ) :
    dwTimesDW2 p x (-y.1, -y.2) = (-(dwTimesDW2 p x y).1, -(dwTimesDW2 p x y).2) := by
  unfold dwTimesDW2
  simp only [twoProd_neg_right, mul_neg, RN_neg, ← neg_add, fastTwoSum_neg]

/-- a product `f` of pairs that commutes with the scalings by powers of two and with the negations, and is zero at a
zero operand: a relative bound `c` with a double-word result, proved on high parts in `[1, 2)`, holds for every pair
of double words -/
theorem dwMul_extend {f : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ} {c : ℝ}
    (hs : ∀ (a b : ℤ) (x y : ℝ × ℝ), f ((2 : ℝ) ^ a * x.1, (2 : ℝ) ^ a * x.2) ((2 : ℝ) ^ b * y.1, (2 : ℝ) ^ b * y.2) =
      ((2 : ℝ) ^ (a + b) * (f x y).1, (2 : ℝ) ^ (a + b) * (f x y).2))
    (hnl : ∀ x y : ℝ × ℝ, f (-x.1, -x.2) y = (-(f x y).1, -(f x y).2))
    (hnr : ∀ x y : ℝ × ℝ, f x (-y.1, -y.2) = (-(f x y).1, -(f x y).2))
    (hzl : ∀ y, f (0, 0) y = (0, 0)) (hzr : ∀ x, f x (0, 0) = (0, 0))
    (hnorm : ∀ {xh xl yh yl : ℝ}, F p xh → F p yh → RN p (xh + xl) = xh → RN p (yh + yl) = yh → 1 ≤ xh → xh < 2 →
      1 ≤ yh → yh < 2 → DWMulWithin p f c xh xl yh yl)
    {x y : ℝ × ℝ} (hx : DW p x) (hy : DW p y) :
    DW p (f x y) ∧ |dwVal (f x y) - dwVal x * dwVal y| ≤ c * |dwVal x * dwVal y| := by
  -- from operands scaled by powers of two
  have ofScale : ∀ {xh xl yh yl : ℝ} (a b : ℤ),
      DWMulWithin p f c ((2 : ℝ) ^ a * xh) ((2 : ℝ) ^ a * xl) ((2 : ℝ) ^ b * yh) ((2 : ℝ) ^ b * yl) →
        DWMulWithin p f c xh xl yh yl := by
    intro xh xl yh yl a b h
    have hK : (0 : ℝ) < (2 : ℝ) ^ (a + b) := by positivity
    have hs' : f ((2 : ℝ) ^ a * xh, (2 : ℝ) ^ a * xl) ((2 : ℝ) ^ b * yh, (2 : ℝ) ^ b * yl) =
        ((2 : ℝ) ^ (a + b) * (f (xh, xl) (yh, yl)).1, (2 : ℝ) ^ (a + b) * (f (xh, xl) (yh, yl)).2) :=
      hs a b (xh, xl) (yh, yl)
    unfold DWMulWithin at h ⊢
    rw [hs'] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨DW.of_scale p (a + b) h1, ?_⟩
    have e1 : dwVal ((2 : ℝ) ^ (a + b) * (f (xh, xl) (yh, yl)).1, (2 : ℝ) ^ (a + b) * (f (xh, xl) (yh, yl)).2) -
        ((2 : ℝ) ^ a * xh + (2 : ℝ) ^ a * xl) * ((2 : ℝ) ^ b * yh + (2 : ℝ) ^ b * yl) =
          (2 : ℝ) ^ (a + b) * (dwVal (f (xh, xl) (yh, yl)) - (xh + xl) * (yh + yl)) := by
      unfold dwVal
      rw [zpow_add₀ two_ne_zero]; ring
    have e2 : ((2 : ℝ) ^ a * xh + (2 : ℝ) ^ a * xl) * ((2 : ℝ) ^ b * yh + (2 : ℝ) ^ b * yl) =
        (2 : ℝ) ^ (a + b) * ((xh + xl) * (yh + yl)) := by
      rw [zpow_add₀ two_ne_zero]; ring
    rw [e1, e2, abs_mul, abs_mul, abs_of_pos hK] at h2
    exact le_of_mul_le_mul_left (by linarith) hK
  -- from the negated `x`, and from the negated `y`
  have ofNegL : ∀ {xh xl yh yl : ℝ}, DWMulWithin p f c (-xh) (-xl) yh yl → DWMulWithin p f c xh xl yh yl := by
    intro xh xl yh yl h
    have hs' : f (-xh, -xl) (yh, yl) = (-(f (xh, xl) (yh, yl)).1, -(f (xh, xl) (yh, yl)).2) :=
      hnl (xh, xl) (yh, yl)
    unfold DWMulWithin at h ⊢
    rw [hs'] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨DW.of_neg p h1, ?_⟩
    have e1 : dwVal (-(f (xh, xl) (yh, yl)).1, -(f (xh, xl) (yh, yl)).2) - (-xh + -xl) * (yh + yl) =
        -(dwVal (f (xh, xl) (yh, yl)) - (xh + xl) * (yh + yl)) := by
      unfold dwVal
      ring
    rw [e1, abs_neg, show (-xh + -xl) * (yh + yl) = -((xh + xl) * (yh + yl)) by ring, abs_neg] at h2
    exact h2
  have ofNegR : ∀ {xh xl yh yl : ℝ}, DWMulWithin p f c xh xl (-yh) (-yl) → DWMulWithin p f c xh xl yh yl := by
    intro xh xl yh yl h
    have hs' : f (xh, xl) (-yh, -yl) = (-(f (xh, xl) (yh, yl)).1, -(f (xh, xl) (yh, yl)).2) :=
      hnr (xh, xl) (yh, yl)
    unfold DWMulWithin at h ⊢
    rw [hs'] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨DW.of_neg p h1, ?_⟩
    have e1 : dwVal (-(f (xh, xl) (yh, yl)).1, -(f (xh, xl) (yh, yl)).2) - (xh + xl) * (-yh + -yl) =
        -(dwVal (f (xh, xl) (yh, yl)) - (xh + xl) * (yh + yl)) := by
      unfold dwVal
      ring
    rw [e1, abs_neg, show (xh + xl) * (-yh + -yl) = -((xh + xl) * (yh + yl)) by ring, abs_neg] at h2
    exact h2
  -- positive high parts: both scaled into `[1, 2)`
  have pos : ∀ {xh xl yh yl : ℝ}, F p xh → F p yh → RN p (xh + xl) = xh → RN p (yh + yl) = yh → 0 < xh → 0 < yh →
      DWMulWithin p f c xh xl yh yl := by
    intro xh xl yh yl hxh hyh hdx hdy hx0 hy0
    obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hx0 (by norm_num : (1 : ℝ) < 2)
    obtain ⟨m, hm1, hm2⟩ := exists_mem_Ico_zpow hy0 (by norm_num : (1 : ℝ) < 2)
    have ha : (0 : ℝ) < (2 : ℝ) ^ (-n) := by positivity
    have hb : (0 : ℝ) < (2 : ℝ) ^ (-m) := by positivity
    have s1 : ∀ k : ℤ, (2 : ℝ) ^ (-k) * (2 : ℝ) ^ k = 1 := fun k => by
      rw [← zpow_add₀ two_ne_zero, neg_add_cancel, zpow_zero]
    have s2 : ∀ k : ℤ, (2 : ℝ) ^ (-k) * (2 : ℝ) ^ (k + 1) = 2 := fun k => by
      rw [← zpow_add₀ two_ne_zero, show -k + (k + 1) = 1 by ring, zpow_one]
    exact ofScale (-n) (-m) (hnorm (F_zpow_mul p (-n) hxh) (F_zpow_mul p (-m) hyh)
      (by rw [← mul_add, RN_zpow_mul, hdx]) (by rw [← mul_add, RN_zpow_mul, hdy])
      (by have := mul_le_mul_of_nonneg_left hn1 ha.le; rwa [s1] at this)
      (by have := mul_lt_mul_of_pos_left hn2 ha; rwa [s2] at this)
      (by have := mul_le_mul_of_nonneg_left hm1 hb.le; rwa [s1] at this)
      (by have := mul_lt_mul_of_pos_left hm2 hb; rwa [s2] at this))
  obtain ⟨xh, xl⟩ := x
  obtain ⟨yh, yl⟩ := y
  obtain ⟨hxh, -, hdx⟩ := hx
  obtain ⟨hyh, -, hdy⟩ := hy
  have hxh' : F p xh := hxh
  have hyh' : F p yh := hyh
  have hdx' : RN p (xh + xl) = xh := hdx
  have hdy' : RN p (yh + yl) = yh := hdy
  show DWMulWithin p f c xh xl yh yl
  -- a zero result
  have zero : ∀ {xh xl yh yl : ℝ}, f (xh, xl) (yh, yl) = (0, 0) → (xh + xl) * (yh + yl) = 0 →
      DWMulWithin p f c xh xl yh yl := by
    intro xh xl yh yl h0 h1
    unfold DWMulWithin
    rw [h0, h1]
    exact ⟨DW.of_F p (F_zero p), by simp [dwVal]⟩
  -- a positive `y_h`, and any `x_h`
  have key : ∀ {yh yl : ℝ}, F p yh → RN p (yh + yl) = yh → 0 < yh → DWMulWithin p f c xh xl yh yl := by
    intro yh yl hyh hdy hy0
    rcases lt_trichotomy xh 0 with hx | hx | hx
    · exact ofNegL (pos (F_neg p hxh') hyh (by rw [← neg_add, RN_neg, hdx']) hdy (by linarith) hy0)
    · have hl0 : xl = 0 := RN_eq_zero p (by rw [hx, zero_add] at hdx'; exact hdx')
      exact zero (by rw [hx, hl0]; exact hzl _) (by rw [hx, hl0]; ring)
    · exact pos hxh' hyh hdx' hdy hx hy0
  rcases lt_trichotomy yh 0 with hy0 | hy0 | hy0
  · exact ofNegR (key (F_neg p hyh') (by rw [← neg_add, RN_neg, hdy']) (by linarith))
  · have hl0 : yl = 0 := RN_eq_zero p (by rw [hy0, zero_add] at hdy'; exact hdy')
    exact zero (by rw [hy0, hl0]; exact hzr _) (by rw [hy0, hl0]; ring)
  · exact key hyh' hdy' hy0

/-- a double word with high part in `[1, 2)` is at least `1 - u/2`, and at least `1 + u` if the high part is
not `1` -/
theorem dw_ge_of_one_le (hp : 1 < p) {xh xl : ℝ} (hxh : F p xh) (hdw : RN p (xh + xl) = xh) (hx1 : 1 ≤ xh)
    (hx2 : xh < 2) : 1 - u p / 2 ≤ xh + xl ∧ (xh ≠ 1 → 1 + u p ≤ xh + xl) := by
  have hu := u_pos p
  have hl := (abs_le.mp (dw_lo_le p hp hxh hdw hx1 hx2)).1
  have hgt : xh ≠ 1 → 1 + u p ≤ xh + xl := by
    intro hne
    have hm1 : Mult (1 - p) (1 : ℝ) := by
      have := Mult.zpow (E := 1 - p) (e := 0) (by omega)
      rwa [zpow_zero] at this
    have := Mult.le_sub hm1 (mult_of_one_le p hxh hx1) (lt_of_le_of_ne hx1 (Ne.symm hne))
    rw [two_zpow_sub_p p 1, zpow_one] at this
    linarith
  refine ⟨?_, hgt⟩
  by_cases h : xh = 1
  · rw [h] at hdw ⊢
    have := dw_lo_ge_of_one p hp hdw
    linarith
  · have := hgt h
    linarith

/-- the steps of DWTimesDW2 on operands with high parts in `[1, 2)`: the last FastTwoSum is exact, the error is
`-x_ℓ y_ℓ + ε₁ + ε₃ + ε₄` with the rounding errors of `t_ℓ`, `c_ℓ2` and `c_ℓ3`, at most `u²`, `2u²` and `4u²`, and
`|t_ℓ + x_ℓ y_h| ≤ u (x_h + y_h)` -/
theorem dwTimesDW2_steps (hp : 5 ≤ p) {xh xl yh yl : ℝ} (hxh : F p xh) (hyh : F p yh)
    (hdx : RN p (xh + xl) = xh) (hdy : RN p (yh + yl) = yh) (hx1 : 1 ≤ xh) (hx2 : xh < 2) (hy1 : 1 ≤ yh)
    (hy2 : yh < 2) {c1 tl c2 c3 : ℝ} (hc1d : c1 = (twoProd p xh yh).2) (htld : tl = RN p (xh * yl))
    (hc2d : c2 = RN p (tl + xl * yh)) (hc3d : c3 = RN p (c1 + c2)) :
    DW p (dwTimesDW2 p (xh, xl) (yh, yl)) ∧
      dwVal (dwTimesDW2 p (xh, xl) (yh, yl)) - (xh + xl) * (yh + yl) =
        -(xl * yl) + (tl - xh * yl) + (c2 - (tl + xl * yh)) + (c3 - (c1 + c2)) ∧
      |xl * yl| ≤ u p ^ 2 ∧ |tl - xh * yl| ≤ u p ^ 2 ∧ |c2 - (tl + xl * yh)| ≤ 2 * u p ^ 2 ∧
      |c3 - (c1 + c2)| ≤ 4 * u p ^ 2 ∧ |tl + xl * yh| ≤ u p * (xh + yh) := by
  have hu := u_pos p
  have hu32 := u_le_32nd p hp
  have hp1 : 1 < p := by omega
  have hxl1 := dw_lo_le p hp1 hxh hdx hx1 hx2
  have hyl1 := dw_lo_le p hp1 hyh hdy hy1 hy2
  obtain ⟨hsum, -, -⟩ := facts_c p hxh hyh
  have hch1 : (twoProd p xh yh).1 = RN p (xh * yh) := rfl
  have e4 : (2 : ℝ) ^ (2 : ℤ) = 4 := by norm_num
  have e8 : (2 : ℝ) ^ (3 : ℤ) = 8 := by norm_num
  have hxy1 : 1 ≤ xh * yh := one_le_mul_of_one_le_of_one_le hx1 hy1
  have hxy4 : xh * yh ≤ 4 := by
    have := mul_le_mul hx2.le hy2.le (by linarith) (by linarith : (0 : ℝ) ≤ 2)
    linarith
  have hch : 1 ≤ (twoProd p xh yh).1 := by
    have := RN_mono p hxy1
    rwa [RN_of_F p (F_one p)] at this
  have hFu : ∀ k : ℤ, F p ((2 : ℝ) ^ k * u p) := fun k => F_zpow_mul p k (F_two_zpow p (-p))
  have hF4u : F p (4 * u p) := by have := hFu 2; rwa [e4] at this
  have hF8u : F p (8 * u p) := by have := hFu 3; rwa [e8] at this
  have hres : dwTimesDW2 p (xh, xl) (yh, yl) = fastTwoSum p (twoProd p xh yh).1 c3 := by
    rw [hc3d, hc2d, htld, hc1d]
    rfl
  rw [← hc1d] at hsum
  have hFc3 : F p c3 := by rw [hc3d]; exact F_RN p _
  -- `t_ℓ`: at most `u x_h`, within `u²` of `x_h y_ℓ`
  have hxyl : |xh * yl| ≤ u p * xh := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < xh), mul_comm]
    exact mul_le_mul_of_nonneg_right hyl1 (by linarith)
  have hux : u p * xh ≤ 2 * u p := by nlinarith only [hu, hx2]
  have huy : u p * yh ≤ 2 * u p := by nlinarith only [hu, hy2]
  have htl : |tl| ≤ u p * xh := by
    rw [htld]
    exact abs_RN_le_of_F p (F_zpow_mul p (-p) hxh) hxyl
  have hε1 : |tl - xh * yl| ≤ u p ^ 2 := by
    have := RN_grid p (1 - p) (z := xh * yl) (by
      rw [two_zpow_sub_p p 1, zpow_one]
      linarith)
    rw [two_zpow_sub_p p 1, zpow_one, ← htld] at this
    linarith only [this, show 2 * u p * u p / 2 = u p ^ 2 by ring]
  -- `c_ℓ2`: at most `4u`, within `2u²` of `t_ℓ + x_ℓ y_h`
  have hxly : |xl * yh| ≤ u p * yh := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < yh)]
    exact mul_le_mul_of_nonneg_right hxl1 (by linarith)
  have hs2 : |tl + xl * yh| ≤ u p * (xh + yh) := (abs_add_le _ _).trans (by linarith)
  have hs2' : |tl + xl * yh| ≤ 4 * u p := hs2.trans (by linarith)
  have hc2 : |c2| ≤ 4 * u p := by
    rw [hc2d]
    exact abs_RN_le_of_F p hF4u hs2'
  have hε3 : |c2 - (tl + xl * yh)| ≤ 2 * u p ^ 2 := by
    have := RN_grid p (2 - p) (z := tl + xl * yh) (by rw [two_zpow_sub_p p 2, e4]; exact hs2')
    rw [two_zpow_sub_p p 2, e4, ← hc2d] at this
    linarith only [this, show 4 * u p * u p / 2 = 2 * u p ^ 2 by ring]
  -- `c_ℓ1`: at most `2u`
  have hc1 : |c1| ≤ 2 * u p := by
    have := RN_grid p 2 (z := xh * yh) (by rw [e4, abs_of_pos (by linarith)]; exact hxy4)
    rw [e4, ← hch1, show (twoProd p xh yh).1 - xh * yh = -c1 by linarith, abs_neg] at this
    linarith
  -- `c_ℓ3`: at most `8u`, within `4u²` of `c_ℓ1 + c_ℓ2`
  have hs3 : |c1 + c2| ≤ 8 * u p := (abs_add_le _ _).trans (by linarith)
  have hc3 : |c3| ≤ 8 * u p := by
    rw [hc3d]
    exact abs_RN_le_of_F p hF8u hs3
  have hε4 : |c3 - (c1 + c2)| ≤ 4 * u p ^ 2 := by
    have := RN_grid p (3 - p) (z := c1 + c2) (by rw [two_zpow_sub_p p 3, e8]; exact hs3)
    rw [two_zpow_sub_p p 3, e8, ← hc3d] at this
    linarith only [this, show 8 * u p * u p / 2 = 4 * u p ^ 2 by ring]
  -- the FastTwoSum is exact
  have hadd := fastTwoSum_add p hp1 (F_RN p (xh * yh)) hFc3 (b := c3) (a := (twoProd p xh yh).1) (by
    rw [abs_of_pos (by linarith : (0 : ℝ) < (twoProd p xh yh).1)]
    linarith)
  have hval : dwVal (fastTwoSum p (twoProd p xh yh).1 c3) - (xh + xl) * (yh + yl) =
      -(xl * yl) + (tl - xh * yl) + (c2 - (tl + xl * yh)) + (c3 - (c1 + c2)) := by
    unfold dwVal
    rw [hadd]
    linear_combination hsum
  have hll : |xl * yl| ≤ u p ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul hxl1 hyl1 (abs_nonneg _) hu.le
  rw [hres]
  exact ⟨fastTwoSum_dw p hadd, hval, hll, hε1, hε3, hε4, hs2⟩

/-- the last two roundings of DWTimesDW2 and DWTimesDW3 on high parts in `[1, 2)` with `x_h y_h < 2`, for any `t_ℓ`
with `|t_ℓ + x_ℓ y_h| ≤ 3u`: the errors of `c_ℓ2` and `c_ℓ3` are at most `3u²` together, and `c_ℓ3` is exact where
`x_h` or `y_h` is `1`. `|c_ℓ1| ≤ u` and `|c_ℓ2| ≤ 3u`, so `|c_ℓ1 + c_ℓ2| ≤ 4u`; for `|c_ℓ2| ≥ 2u` this sum, a multiple
of `4u²`, is a float, and otherwise `c_ℓ2` is within `u²` -/
theorem dwTimesDW2_small (hp : 5 ≤ p) {xh xl yh : ℝ} (hxh : F p xh) (hyh : F p yh) (hx1 : 1 ≤ xh)
    (hy1 : 1 ≤ yh) (hB : xh * yh < 2) {c1 tl c2 c3 : ℝ} (hc1d : c1 = (twoProd p xh yh).2)
    (hc2d : c2 = RN p (tl + xl * yh)) (hc3d : c3 = RN p (c1 + c2))
    (hs2 : |tl + xl * yh| ≤ 3 * u p) (hε3 : |c2 - (tl + xl * yh)| ≤ 2 * u p ^ 2) :
    |c2 - (tl + xl * yh)| + |c3 - (c1 + c2)| ≤ 3 * u p ^ 2 ∧ ((xh = 1 ∨ yh = 1) → c3 - (c1 + c2) = 0) := by
  have hu := u_pos p
  have hu32 := u_le_32nd p hp
  have hp1 : 1 < p := by omega
  obtain ⟨hsum, -, -⟩ := facts_c p hxh hyh
  have hch1 : (twoProd p xh yh).1 = RN p (xh * yh) := rfl
  have e4 : (2 : ℝ) ^ (2 : ℤ) = 4 := by norm_num
  have hxy1 : 1 ≤ xh * yh := one_le_mul_of_one_le_of_one_le hx1 hy1
  have hch : 1 ≤ (twoProd p xh yh).1 := by
    have := RN_mono p hxy1
    rwa [RN_of_F p (F_one p)] at this
  rw [← hc1d] at hsum
  have hFc2 : F p c2 := by rw [hc2d]; exact F_RN p _
  have hF2u : F p (2 * u p) := by
    have := F_zpow_mul p 1 (F_two_zpow p (-p))
    rwa [zpow_one] at this
  have hc1' : |c1| ≤ u p := by
    have := RN_grid p 1 (z := xh * yh) (by rw [zpow_one, abs_of_pos (by linarith)]; exact hB.le)
    rw [zpow_one, ← hch1, show (twoProd p xh yh).1 - xh * yh = -c1 by linarith, abs_neg] at this
    linarith
  have hF3u : F p (3 * u p) := by
    have hF3 : F p (3 : ℝ) := F_of_mult_le p (E := 0) ⟨3, by norm_num⟩ (by
      rw [zero_add, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      calc (3 : ℝ) ≤ (2 : ℝ) ^ (2 : ℤ) := by norm_num
        _ ≤ (2 : ℝ) ^ p := zpow_le_zpow_right₀ (by norm_num) (by omega))
    have := F_zpow_mul p (-p) hF3
    rwa [show (2 : ℝ) ^ (-p) * 3 = 3 * u p by unfold u; ring] at this
  have hc2' : |c2| ≤ 3 * u p := by
    rw [hc2d]
    exact abs_RN_le_of_F p hF3u hs2
  have hs3' : |c1 + c2| ≤ 4 * u p := (abs_add_le _ _).trans (by linarith)
  have hε4' : |c3 - (c1 + c2)| ≤ 2 * u p ^ 2 := by
    have := RN_grid p (2 - p) (z := c1 + c2) (by rw [two_zpow_sub_p p 2, e4]; exact hs3')
    rw [two_zpow_sub_p p 2, e4, ← hc3d] at this
    linarith only [this, show 4 * u p * u p / 2 = 2 * u p ^ 2 by ring]
  constructor
  · rcases le_or_gt (2 * u p) |c2| with hbig | hsmall
    · -- `|c_ℓ2| ≥ 2u`: `c_ℓ1 + c_ℓ2`, a multiple of `4u²` at most `4u`, is a float
      have hmx : Mult (1 - p) xh := mult_of_one_le p hxh hx1
      have hmy : Mult (1 - p) yh := mult_of_one_le p hyh hy1
      have hmch : Mult (1 - p + (1 - p)) (twoProd p xh yh).1 :=
        (mult_of_one_le p (F_RN p (xh * yh)) hch).mono (by omega)
      have hmc1 : Mult (1 - p + (1 - p)) c1 := by
        rw [show c1 = xh * yh - (twoProd p xh yh).1 by linarith]
        exact (hmx.mul hmy).sub hmch
      have hmc2 : Mult (1 - p + (1 - p)) c2 := mult_of_F p hFc2 (by
        rw [show 1 - p + (1 - p) + p - 1 = 1 - p by ring, two_zpow_sub_p p 1, zpow_one]
        exact hbig)
      have hF : F p (c1 + c2) := F_of_mult_le p (hmc1.add hmc2) (by
        rw [show 1 - p + (1 - p) + p = 2 - p by ring, two_zpow_sub_p p 2, e4]
        exact hs3')
      have hε40 : c3 - (c1 + c2) = 0 := by rw [hc3d, RN_of_F p hF]; ring
      rw [hε40, abs_zero]
      nlinarith only [hε3, sq_nonneg (u p)]
    · -- `|c_ℓ2| < 2u`: `|t_ℓ + x_ℓ y_h| ≤ 2u`, and `c_ℓ2` is within `u²` of it
      have hs2'' : |tl + xl * yh| ≤ 2 * u p := by
        by_contra h
        have := abs_RN_ge_of_F p hF2u (not_le.mp h).le
        rw [← hc2d] at this
        linarith
      have hε3' : |c2 - (tl + xl * yh)| ≤ u p ^ 2 := by
        have := RN_grid p (1 - p) (z := tl + xl * yh) (by rw [two_zpow_sub_p p 1, zpow_one]; exact hs2'')
        rw [two_zpow_sub_p p 1, zpow_one, ← hc2d] at this
        linarith only [this, show 2 * u p * u p / 2 = u p ^ 2 by ring]
      linarith
  · -- `x_h` or `y_h` is `1`: `c_ℓ1 = 0` and `c_ℓ3 = c_ℓ2`
    intro h11
    have hFxy : F p (xh * yh) := by
      rcases h11 with h | h
      · rw [h, one_mul]; exact hyh
      · rw [h, mul_one]; exact hxh
    have hc10 : c1 = 0 := by
      rw [hch1, RN_of_F p hFxy] at hsum
      linarith
    rw [hc3d, hc10, zero_add, RN_of_F p hFc2]
    ring

/-- Theorem 2.7 of Muller and Rideau on operands with high parts in `[1, 2)` -/
theorem dwTimesDW2_norm (hp : 5 ≤ p) {xh xl yh yl : ℝ} (hxh : F p xh) (hyh : F p yh)
    (hdx : RN p (xh + xl) = xh) (hdy : RN p (yh + yl) = yh) (hx1 : 1 ≤ xh) (hx2 : xh < 2) (hy1 : 1 ≤ yh)
    (hy2 : yh < 2) : DWMulWithin p (dwTimesDW2 p) (5 * u p ^ 2 / (1 + u p) ^ 2) xh xl yh yl := by
  have hu := u_pos p
  have hu32 := u_le_32nd p hp
  have hp1 : 1 < p := by omega
  obtain ⟨c1, hc1d⟩ : ∃ c1, c1 = (twoProd p xh yh).2 := ⟨_, rfl⟩
  obtain ⟨tl, htld⟩ : ∃ tl, tl = RN p (xh * yl) := ⟨_, rfl⟩
  obtain ⟨c2, hc2d⟩ : ∃ c2, c2 = RN p (tl + xl * yh) := ⟨_, rfl⟩
  obtain ⟨c3, hc3d⟩ : ∃ c3, c3 = RN p (c1 + c2) := ⟨_, rfl⟩
  obtain ⟨hdw, hval, hll, hε1, hε3, hε4, hs2⟩ :=
    dwTimesDW2_steps p hp hxh hyh hdx hdy hx1 hx2 hy1 hy2 hc1d htld hc2d hc3d
  refine ⟨hdw, ?_⟩
  rw [hval]
  -- the error is `-x_ℓ y_ℓ + ε₁ + ε₃ + ε₄`
  have htri : |-(xl * yl) + (tl - xh * yl) + (c2 - (tl + xl * yh)) + (c3 - (c1 + c2))| ≤
      |xl * yl| + |tl - xh * yl| + |c2 - (tl + xl * yh)| + |c3 - (c1 + c2)| := by
    have a1 := abs_add_le (-(xl * yl) + (tl - xh * yl) + (c2 - (tl + xl * yh))) (c3 - (c1 + c2))
    have a2 := abs_add_le (-(xl * yl) + (tl - xh * yl)) (c2 - (tl + xl * yh))
    have a3 := abs_add_le (-(xl * yl)) (tl - xh * yl)
    rw [abs_neg] at a3
    linarith
  obtain ⟨gx1, gx2⟩ := dw_ge_of_one_le p hp1 hxh hdx hx1 hx2
  obtain ⟨gy1, gy2⟩ := dw_ge_of_one_le p hp1 hyh hdy hy1 hy2
  obtain ⟨X, hXd⟩ : ∃ X, X = (xh + xl) * (yh + yl) := ⟨_, rfl⟩
  rw [← hXd]
  rcases le_or_gt 2 (xh * yh) with hA | hB
  · -- `x_h y_h ≥ 2`: `|η| ≤ 8u²` and `xy ≥ 2(1 - u)²`
    have hxl2 := (abs_le.mp (dw_lo_le p hp1 hxh hdx hx1 hx2)).1
    have hyl2 := (abs_le.mp (dw_lo_le p hp1 hyh hdy hy1 hy2)).1
    have hX1 : xh * (1 - u p) ≤ xh + xl := by nlinarith only [hxl2, hx1, hu]
    have hY1 : yh * (1 - u p) ≤ yh + yl := by nlinarith only [hyl2, hy1, hu]
    have hX : 2 * (1 - u p) ^ 2 ≤ X := by
      rw [hXd]
      calc 2 * (1 - u p) ^ 2 ≤ xh * yh * (1 - u p) ^ 2 := mul_le_mul_of_nonneg_right hA (sq_nonneg _)
        _ = xh * (1 - u p) * (yh * (1 - u p)) := by ring
        _ ≤ (xh + xl) * (yh + yl) :=
          mul_le_mul hX1 hY1 (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have h1u : (0 : ℝ) < 1 - u p := by linarith
    refine mul_rel p hu (G := 8) (by linarith) ?_
    rw [abs_of_pos (lt_of_lt_of_le (by positivity) hX)]
    nlinarith only [hX, hu, hu32]
  · have hxy3 : xh + yh ≤ 3 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1), hB]
    obtain ⟨h3, h0⟩ := dwTimesDW2_small p hp hxh hyh hx1 hy1 hB hc1d hc2d hc3d
      (hs2.trans (by nlinarith only [hu, hxy3])) hε3
    by_cases h11 : xh = 1 ∨ yh = 1
    · -- `x_h` or `y_h` is `1`: `|η| ≤ 4u²` and `xy ≥ (1 - u/2)²`
      rw [h0 h11, abs_zero] at htri
      rw [h0 h11]
      have hX : (1 - u p / 2) ^ 2 ≤ X := by
        rw [hXd, sq]
        exact mul_le_mul gx1 gy1 (by linarith) (by linarith)
      refine mul_rel p hu (G := 4) (by linarith) ?_
      rw [abs_of_pos (lt_of_lt_of_le (by nlinarith only [hu, hu32]) hX)]
      nlinarith only [hX, hu, hu32]
    · -- `x_h, y_h ≥ 1 + 2u`: `|η| ≤ 5u²` and `xy ≥ (1 + u)²`
      have hne : xh ≠ 1 ∧ yh ≠ 1 := ⟨fun h => h11 (Or.inl h), fun h => h11 (Or.inr h)⟩
      have hX : (1 + u p) ^ 2 ≤ X := by
        rw [hXd, sq]
        exact mul_le_mul (gx2 hne.1) (gy2 hne.2) (by linarith) (by linarith [gx2 hne.1])
      refine mul_rel p hu (G := 5) (by linarith) ?_
      rw [abs_of_pos (lt_of_lt_of_le (by positivity) hX)]
      linarith

/-- Theorem 2.7 of Muller and Rideau (2022), with its result a double word: for `p ≥ 5` and double words `x` and
`y`, `DWTimesDW2(x, y)` is a double word within `5u²/(1 + u)²` of `xy`, relatively -/
theorem dwTimesDW2_good (hp : 5 ≤ p) {x y : ℝ × ℝ} (hx : DW p x) (hy : DW p y) :
    DW p (dwTimesDW2 p x y) ∧
      |dwVal (dwTimesDW2 p x y) - dwVal x * dwVal y| ≤ 5 * u p ^ 2 / (1 + u p) ^ 2 * |dwVal x * dwVal y| :=
  dwMul_extend p (dwTimesDW2_scale p) (dwTimesDW2_neg_left p) (dwTimesDW2_neg_right p) (dwTimesDW2_zero_left p)
    (dwTimesDW2_zero_right p)
    (fun h1 h2 h3 h4 h5 h6 h7 h8 => dwTimesDW2_norm p hp h1 h2 h3 h4 h5 h6 h7 h8) hx hy

/-- Theorem 2.7 of Muller and Rideau (2022): for `p ≥ 5`, DWTimesDW2 of two double words is within
`5u²/(1 + u)²` of their product, relatively -/
theorem dwTimesDW2_err (hp : 5 ≤ p) {x y : ℝ × ℝ} (hx : DW p x) (hy : DW p y) :
    |dwVal (dwTimesDW2 p x y) - dwVal x * dwVal y| ≤ 5 * u p ^ 2 / (1 + u p) ^ 2 * |dwVal x * dwVal y| :=
  (dwTimesDW2_good p hp hx hy).2

/-- the result of DWTimesDW2 is a double word: its last FastTwoSum is exact -/
theorem dwTimesDW2_dw (hp : 5 ≤ p) {x y : ℝ × ℝ} (hx : DW p x) (hy : DW p y) : DW p (dwTimesDW2 p x y) :=
  (dwTimesDW2_good p hp hx hy).1

end ExpansionBounds
