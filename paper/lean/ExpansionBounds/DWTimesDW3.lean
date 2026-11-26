import ExpansionBounds.DWTimesDW2

/-!
# DWTimesDW3, the product of two double words with three fused multiply-adds

Algorithm 12 of Joldes, Muller and Popescu (2017), the MUL of multidouble's double-double sine, cosine and tangent:

  `(c_h, c_ℓ1) = TwoProd(x_h, y_h)`, `t_ℓ0 = RN(x_ℓ y_ℓ)`, `t_ℓ1 = RN(x_h y_ℓ + t_ℓ0)`, `c_ℓ2 = RN(t_ℓ1 + x_ℓ y_h)`,
  `c_ℓ3 = RN(c_ℓ1 + c_ℓ2)`, `(z_h, z_ℓ) = FastTwoSum(c_h, c_ℓ3)`.

Theorem 2.8 of Muller and Rideau (2022), with its result a double word (`dwTimesDW3_good`): for `p ≥ 5` and double
words `x` and `y`, the result is a double word within `(4u² + u³/2)/(1 + u)²` of `xy`, relatively. On
`x_h, y_h ∈ [1, 2)` the error is `ε₀ + ε₁ + ε₂ + ε₃`, the rounding errors of `t_ℓ0`, `t_ℓ1`, `c_ℓ2` and `c_ℓ3`, at
most `u³/2`, `u²`, `2u²` and `4u²`. The cases are those of the paper's section 2.5: `x_h y_h ≥ 2`, where
`xy ≥ 2(1 - u)²`; and `x_h y_h < 2`, where `x_h + y_h ≤ 3 - 2u` (the paper's Lemma 2.10), so `|t_ℓ1 + x_ℓ y_h| ≤ 3u`
and the last two errors are at most `3u²` together, with `xy ≥ (1 + u)²`, or `x_h` or `y_h` is `1`, `c_ℓ1 = 0`, the
last rounding is exact, and `xy ≥ (1 - u/2)²`.

`dwMul_extend` carries a bound proved on high parts in `[1, 2)` to every pair of double words, for a product that
commutes with the scalings by powers of two and with the negations.
-/

namespace ExpansionBounds

variable (p : ℤ)

/-- DWTimesDW3: `(c_h, c_ℓ1) = TwoProd(x_h, y_h)`, `t_ℓ0 = RN(x_ℓ y_ℓ)`, `t_ℓ1 = RN(x_h y_ℓ + t_ℓ0)`,
`c_ℓ2 = RN(t_ℓ1 + x_ℓ y_h)`, `c_ℓ3 = RN(c_ℓ1 + c_ℓ2)` and `(z_h, z_ℓ) = FastTwoSum(c_h, c_ℓ3)` -/
noncomputable def dwTimesDW3 (x y : ℝ × ℝ) : ℝ × ℝ :=
  fastTwoSum p (twoProd p x.1 y.1).1
    (RN p ((twoProd p x.1 y.1).2 + RN p (RN p (x.1 * y.2 + RN p (x.2 * y.2)) + x.2 * y.1)))

/-- DWTimesDW3 commutes with scalings by powers of two -/
theorem dwTimesDW3_scale (a b : ℤ) (x y : ℝ × ℝ) :
    dwTimesDW3 p ((2 : ℝ) ^ a * x.1, (2 : ℝ) ^ a * x.2) ((2 : ℝ) ^ b * y.1, (2 : ℝ) ^ b * y.2) =
      ((2 : ℝ) ^ (a + b) * (dwTimesDW3 p x y).1, (2 : ℝ) ^ (a + b) * (dwTimesDW3 p x y).2) := by
  have e : ∀ s t : ℝ, (2 : ℝ) ^ a * s * ((2 : ℝ) ^ b * t) = (2 : ℝ) ^ (a + b) * (s * t) := fun s t => by
    rw [zpow_add₀ two_ne_zero]; ring
  unfold dwTimesDW3
  simp only [twoProd_scale, e, RN_zpow_mul, ← mul_add, fastTwoSum_scale]

/-- DWTimesDW3 of a zero `x` is zero -/
theorem dwTimesDW3_zero_left (y : ℝ × ℝ) : dwTimesDW3 p (0, 0) y = (0, 0) := by
  simp [dwTimesDW3, twoProd, fastTwoSum, RN_zero]

/-- DWTimesDW3 by a zero `y` is zero -/
theorem dwTimesDW3_zero_right (x : ℝ × ℝ) : dwTimesDW3 p x (0, 0) = (0, 0) := by
  simp [dwTimesDW3, twoProd, fastTwoSum, RN_zero]

/-- an error of at most `G` at a product with `G (1 + u)² ≤ (4u² + u³/2)|xy|` is within the theorem's relative
bound -/
theorem mul_rel3 (hu : 0 < u p) {η X G : ℝ} (hη : |η| ≤ G)
    (hX : G * (1 + u p) ^ 2 ≤ (4 * u p ^ 2 + u p ^ 3 / 2) * |X|) :
    |η| ≤ (4 * u p ^ 2 + u p ^ 3 / 2) / (1 + u p) ^ 2 * |X| := by
  have h1 : (0 : ℝ) < (1 + u p) ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ h1]
  exact (mul_le_mul_of_nonneg_right hη h1.le).trans hX

/-- the conclusion of a product's theorem at `(x_h, x_ℓ)` and `(y_h, y_ℓ)`: the result of `f` is a double word within
`c` of `xy`, relatively -/
def DWMulWithin (f : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ) (c xh xl yh yl : ℝ) : Prop :=
  DW p (f (xh, xl) (yh, yl)) ∧ |dwVal (f (xh, xl) (yh, yl)) - (xh + xl) * (yh + yl)| ≤ c * |(xh + xl) * (yh + yl)|

variable [Prec_gt_0 p]

/-- DWTimesDW3 commutes with the negation of `x` -/
theorem dwTimesDW3_neg_left (x y : ℝ × ℝ) :
    dwTimesDW3 p (-x.1, -x.2) y = (-(dwTimesDW3 p x y).1, -(dwTimesDW3 p x y).2) := by
  unfold dwTimesDW3
  simp only [twoProd_neg_left, neg_mul, RN_neg, ← neg_add, fastTwoSum_neg]

/-- DWTimesDW3 commutes with the negation of `y` -/
theorem dwTimesDW3_neg_right (x y : ℝ × ℝ) :
    dwTimesDW3 p x (-y.1, -y.2) = (-(dwTimesDW3 p x y).1, -(dwTimesDW3 p x y).2) := by
  unfold dwTimesDW3
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

/-- the steps of DWTimesDW3 on operands with high parts in `[1, 2)`: the last FastTwoSum is exact, the error is
`ε₀ + ε₁ + ε₂ + ε₃` with the rounding errors of `t_ℓ0`, `t_ℓ1`, `c_ℓ2` and `c_ℓ3`, at most `u³/2`, `u²`, `2u²` and
`4u²`, and `|t_ℓ1 + x_ℓ y_h| ≤ u (x_h + y_h) + 2u²` -/
theorem dwTimesDW3_steps (hp : 5 ≤ p) {xh xl yh yl : ℝ} (hxh : F p xh) (hyh : F p yh)
    (hdx : RN p (xh + xl) = xh) (hdy : RN p (yh + yl) = yh) (hx1 : 1 ≤ xh) (hx2 : xh < 2) (hy1 : 1 ≤ yh)
    (hy2 : yh < 2) {c1 t0 t1 c2 c3 : ℝ} (hc1d : c1 = (twoProd p xh yh).2) (ht0d : t0 = RN p (xl * yl))
    (ht1d : t1 = RN p (xh * yl + t0)) (hc2d : c2 = RN p (t1 + xl * yh)) (hc3d : c3 = RN p (c1 + c2)) :
    DW p (dwTimesDW3 p (xh, xl) (yh, yl)) ∧
      dwVal (dwTimesDW3 p (xh, xl) (yh, yl)) - (xh + xl) * (yh + yl) =
        (t0 - xl * yl) + (t1 - (xh * yl + t0)) + (c2 - (t1 + xl * yh)) + (c3 - (c1 + c2)) ∧
      |t0 - xl * yl| ≤ u p ^ 3 / 2 ∧ |t1 - (xh * yl + t0)| ≤ u p ^ 2 ∧ |c2 - (t1 + xl * yh)| ≤ 2 * u p ^ 2 ∧
      |c3 - (c1 + c2)| ≤ 4 * u p ^ 2 ∧ |t1 + xl * yh| ≤ u p * (xh + yh) + 2 * u p ^ 2 := by
  have hu := u_pos p
  have hu32 := u_le_32nd p hp
  have hp1 : 1 < p := by omega
  have hxl1 := dw_lo_le p hp1 hxh hdx hx1 hx2
  have hyl1 := dw_lo_le p hp1 hyh hdy hy1 hy2
  have hx2' := le_two_sub_of_lt_two p hxh hx1 hx2
  have hy2' := le_two_sub_of_lt_two p hyh hy1 hy2
  obtain ⟨hsum, -, -⟩ := facts_c p hxh hyh
  have hch1 : (twoProd p xh yh).1 = RN p (xh * yh) := rfl
  have e4 : (2 : ℝ) ^ (2 : ℤ) = 4 := by norm_num
  have e8 : (2 : ℝ) ^ (3 : ℤ) = 8 := by norm_num
  have euu : (2 : ℝ) ^ (-p - p) = u p ^ 2 := by
    rw [two_zpow_sub_p p (-p)]
    unfold u
    ring
  have hxy1 : 1 ≤ xh * yh := one_le_mul_of_one_le_of_one_le hx1 hy1
  have hxy4 : xh * yh ≤ 4 := by
    have := mul_le_mul hx2.le hy2.le (by linarith) (by linarith : (0 : ℝ) ≤ 2)
    linarith
  have hch : 1 ≤ (twoProd p xh yh).1 := by
    have := RN_mono p hxy1
    rwa [RN_of_F p (F_one p)] at this
  have hFu : ∀ k : ℤ, F p ((2 : ℝ) ^ k * u p) := fun k => F_zpow_mul p k (F_two_zpow p (-p))
  have hF2u : F p (2 * u p) := by have := hFu 1; rwa [zpow_one] at this
  have hF4u : F p (4 * u p) := by have := hFu 2; rwa [e4] at this
  have hF8u : F p (8 * u p) := by have := hFu 3; rwa [e8] at this
  have hres : dwTimesDW3 p (xh, xl) (yh, yl) = fastTwoSum p (twoProd p xh yh).1 c3 := by
    rw [hc3d, hc2d, ht1d, ht0d, hc1d]
    rfl
  rw [← hc1d] at hsum
  have hFc3 : F p c3 := by rw [hc3d]; exact F_RN p _
  -- `t_ℓ0`: at most `u²`, within `u³/2` of `x_ℓ y_ℓ`
  have hll : |xl * yl| ≤ u p ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul hxl1 hyl1 (abs_nonneg _) hu.le
  have ht0 : |t0| ≤ u p ^ 2 := by
    rw [ht0d]
    exact abs_RN_le_of_F p (F_u_pow p 2) hll
  have hε0 : |t0 - xl * yl| ≤ u p ^ 3 / 2 := by
    have := RN_grid p (-p - p) (z := xl * yl) (by rw [euu]; exact hll)
    rw [euu, ← ht0d] at this
    linarith only [this, show u p ^ 2 * u p / 2 = u p ^ 3 / 2 by ring]
  -- `t_ℓ1`: at most `2u`, within `u²` of `x_h y_ℓ + t_ℓ0`
  have hxyl : |xh * yl| ≤ u p * xh := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < xh), mul_comm]
    exact mul_le_mul_of_nonneg_right hyl1 (by linarith)
  have hz1 : |xh * yl + t0| ≤ u p * xh + u p ^ 2 := (abs_add_le _ _).trans (add_le_add hxyl ht0)
  have hz1' : |xh * yl + t0| ≤ 2 * u p := hz1.trans (by nlinarith only [hu, hx2'])
  have hε1 : |t1 - (xh * yl + t0)| ≤ u p ^ 2 := by
    have := RN_grid p (1 - p) (z := xh * yl + t0) (by rw [two_zpow_sub_p p 1, zpow_one]; exact hz1')
    rw [two_zpow_sub_p p 1, zpow_one, ← ht1d] at this
    linarith only [this, show 2 * u p * u p / 2 = u p ^ 2 by ring]
  have ht1 : |t1| ≤ u p * xh + 2 * u p ^ 2 := by
    have := abs_sub_abs_le_abs_sub t1 (xh * yl + t0)
    linarith
  -- `c_ℓ2`: at most `4u`, within `2u²` of `t_ℓ1 + x_ℓ y_h`
  have hxly : |xl * yh| ≤ u p * yh := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < yh)]
    exact mul_le_mul_of_nonneg_right hxl1 (by linarith)
  have hs2 : |t1 + xl * yh| ≤ u p * (xh + yh) + 2 * u p ^ 2 := (abs_add_le _ _).trans (by linarith)
  have hs2' : |t1 + xl * yh| ≤ 4 * u p := hs2.trans (by nlinarith only [hu, hx2', hy2'])
  have hc2 : |c2| ≤ 4 * u p := by
    rw [hc2d]
    exact abs_RN_le_of_F p hF4u hs2'
  have hε2 : |c2 - (t1 + xl * yh)| ≤ 2 * u p ^ 2 := by
    have := RN_grid p (2 - p) (z := t1 + xl * yh) (by rw [two_zpow_sub_p p 2, e4]; exact hs2')
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
  have hε3 : |c3 - (c1 + c2)| ≤ 4 * u p ^ 2 := by
    have := RN_grid p (3 - p) (z := c1 + c2) (by rw [two_zpow_sub_p p 3, e8]; exact hs3)
    rw [two_zpow_sub_p p 3, e8, ← hc3d] at this
    linarith only [this, show 8 * u p * u p / 2 = 4 * u p ^ 2 by ring]
  -- the FastTwoSum is exact
  have hadd := fastTwoSum_add p hp1 (F_RN p (xh * yh)) hFc3 (b := c3) (a := (twoProd p xh yh).1) (by
    rw [abs_of_pos (by linarith : (0 : ℝ) < (twoProd p xh yh).1)]
    linarith)
  have hval : dwVal (fastTwoSum p (twoProd p xh yh).1 c3) - (xh + xl) * (yh + yl) =
      (t0 - xl * yl) + (t1 - (xh * yl + t0)) + (c2 - (t1 + xl * yh)) + (c3 - (c1 + c2)) := by
    unfold dwVal
    rw [hadd]
    linear_combination hsum
  rw [hres]
  exact ⟨fastTwoSum_dw p hadd, hval, hε0, hε1, hε2, hε3, hs2⟩

/-- Theorem 2.8 of Muller and Rideau on operands with high parts in `[1, 2)` -/
theorem dwTimesDW3_norm (hp : 5 ≤ p) {xh xl yh yl : ℝ} (hxh : F p xh) (hyh : F p yh)
    (hdx : RN p (xh + xl) = xh) (hdy : RN p (yh + yl) = yh) (hx1 : 1 ≤ xh) (hx2 : xh < 2) (hy1 : 1 ≤ yh)
    (hy2 : yh < 2) :
    DWMulWithin p (dwTimesDW3 p) ((4 * u p ^ 2 + u p ^ 3 / 2) / (1 + u p) ^ 2) xh xl yh yl := by
  have hu := u_pos p
  have hu32 := u_le_32nd p hp
  have hp1 : 1 < p := by omega
  have hu2 : u p ^ 2 ≤ u p / 32 := by nlinarith only [hu, hu32]
  have hu3 : u p ^ 3 ≤ u p ^ 2 / 32 := by nlinarith only [hu, hu32, sq_nonneg (u p)]
  have hu30 : 0 ≤ u p ^ 3 := by positivity
  obtain ⟨c1, hc1d⟩ : ∃ c1, c1 = (twoProd p xh yh).2 := ⟨_, rfl⟩
  obtain ⟨t0, ht0d⟩ : ∃ t0, t0 = RN p (xl * yl) := ⟨_, rfl⟩
  obtain ⟨t1, ht1d⟩ : ∃ t1, t1 = RN p (xh * yl + t0) := ⟨_, rfl⟩
  obtain ⟨c2, hc2d⟩ : ∃ c2, c2 = RN p (t1 + xl * yh) := ⟨_, rfl⟩
  obtain ⟨c3, hc3d⟩ : ∃ c3, c3 = RN p (c1 + c2) := ⟨_, rfl⟩
  obtain ⟨hdw, hval, hε0, hε1, hε2, hε3, hs2⟩ :=
    dwTimesDW3_steps p hp hxh hyh hdx hdy hx1 hx2 hy1 hy2 hc1d ht0d ht1d hc2d hc3d
  refine ⟨hdw, ?_⟩
  rw [hval]
  -- the error is `ε₀ + ε₁ + ε₂ + ε₃`
  have htri : |(t0 - xl * yl) + (t1 - (xh * yl + t0)) + (c2 - (t1 + xl * yh)) + (c3 - (c1 + c2))| ≤
      |t0 - xl * yl| + |t1 - (xh * yl + t0)| + |c2 - (t1 + xl * yh)| + |c3 - (c1 + c2)| := by
    have a1 := abs_add_le ((t0 - xl * yl) + (t1 - (xh * yl + t0)) + (c2 - (t1 + xl * yh))) (c3 - (c1 + c2))
    have a2 := abs_add_le ((t0 - xl * yl) + (t1 - (xh * yl + t0))) (c2 - (t1 + xl * yh))
    have a3 := abs_add_le (t0 - xl * yl) (t1 - (xh * yl + t0))
    linarith
  obtain ⟨gx1, gx2⟩ := dw_ge_of_one_le p hp1 hxh hdx hx1 hx2
  obtain ⟨gy1, gy2⟩ := dw_ge_of_one_le p hp1 hyh hdy hy1 hy2
  obtain ⟨X, hXd⟩ : ∃ X, X = (xh + xl) * (yh + yl) := ⟨_, rfl⟩
  rw [← hXd]
  have hc0 : 0 ≤ 4 * u p ^ 2 + u p ^ 3 / 2 := by positivity
  rcases le_or_gt 2 (xh * yh) with hA | hB
  · -- `x_h y_h ≥ 2`: `|η| ≤ 7u² + u³/2` and `xy ≥ 2(1 - u)²`
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
    refine mul_rel3 p hu (G := 7 * u p ^ 2 + u p ^ 3 / 2) (by linarith) ?_
    rw [abs_of_pos (lt_of_lt_of_le (by positivity) hX)]
    have hq : 0 ≤ 1 - 59 / 2 * u p - 2 * u p ^ 2 + u p ^ 3 / 2 := by linarith
    have h5 := mul_le_mul_of_nonneg_left hX hc0
    linarith [mul_nonneg (sq_nonneg (u p)) hq]
  · have hxy3 : xh + yh < 3 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1), hB]
    -- Lemma 2.10 of the paper: `x_h + y_h`, a multiple of `2u` below `3`, is at most `3 - 2u`
    have hm3 : Mult (1 - p) (3 : ℝ) := by
      have h1 := Mult.zpow (E := 1 - p) (e := 0) (by omega)
      have h2 := Mult.zpow (E := 1 - p) (e := 1) (by omega)
      rw [zpow_zero] at h1
      rw [zpow_one] at h2
      have := h1.add h2
      rwa [show (1 : ℝ) + 2 = 3 by norm_num] at this
    have hxy3' : xh + yh ≤ 3 - 2 * u p := by
      have := Mult.le_sub ((mult_of_one_le p hxh hx1).add (mult_of_one_le p hyh hy1)) hm3 hxy3
      rwa [two_zpow_sub_p p 1, zpow_one] at this
    obtain ⟨h3, h0⟩ := dwTimesDW2_small p hp hxh hyh hx1 hy1 hB hc1d hc2d hc3d
      (hs2.trans (by nlinarith only [hu, hxy3'])) hε2
    by_cases h11 : xh = 1 ∨ yh = 1
    · -- `x_h` or `y_h` is `1`: `|η| ≤ 3u² + u³/2` and `xy ≥ (1 - u/2)²`
      rw [h0 h11, abs_zero] at htri
      rw [h0 h11]
      have hX : (1 - u p / 2) ^ 2 ≤ X := by
        rw [hXd, sq]
        exact mul_le_mul gx1 gy1 (by linarith) (by linarith)
      refine mul_rel3 p hu (G := 3 * u p ^ 2 + u p ^ 3 / 2) (by linarith) ?_
      rw [abs_of_pos (lt_of_lt_of_le (by nlinarith only [hu, hu32]) hX)]
      have hq : 0 ≤ 1 - 10 * u p - 7 / 2 * u p ^ 2 - 3 / 8 * u p ^ 3 := by linarith
      have h5 := mul_le_mul_of_nonneg_left hX hc0
      linarith [mul_nonneg (sq_nonneg (u p)) hq]
    · -- `x_h, y_h ≥ 1 + 2u`: `|η| ≤ 4u² + u³/2` and `xy ≥ (1 + u)²`
      have hne : xh ≠ 1 ∧ yh ≠ 1 := ⟨fun h => h11 (Or.inl h), fun h => h11 (Or.inr h)⟩
      have hX : (1 + u p) ^ 2 ≤ X := by
        rw [hXd, sq]
        exact mul_le_mul (gx2 hne.1) (gy2 hne.2) (by linarith) (by linarith [gx2 hne.1])
      refine mul_rel3 p hu (G := 4 * u p ^ 2 + u p ^ 3 / 2) (by linarith) ?_
      rw [abs_of_pos (lt_of_lt_of_le (by positivity) hX)]
      exact mul_le_mul_of_nonneg_left hX hc0

/-- Theorem 2.8 of Muller and Rideau (2022), with its result a double word: for `p ≥ 5` and double words `x` and
`y`, `DWTimesDW3(x, y)` is a double word within `(4u² + u³/2)/(1 + u)²` of `xy`, relatively -/
theorem dwTimesDW3_good (hp : 5 ≤ p) {x y : ℝ × ℝ} (hx : DW p x) (hy : DW p y) :
    DW p (dwTimesDW3 p x y) ∧
      |dwVal (dwTimesDW3 p x y) - dwVal x * dwVal y| ≤
        (4 * u p ^ 2 + u p ^ 3 / 2) / (1 + u p) ^ 2 * |dwVal x * dwVal y| :=
  dwMul_extend p (dwTimesDW3_scale p) (dwTimesDW3_neg_left p) (dwTimesDW3_neg_right p) (dwTimesDW3_zero_left p)
    (dwTimesDW3_zero_right p)
    (fun h1 h2 h3 h4 h5 h6 h7 h8 => dwTimesDW3_norm p hp h1 h2 h3 h4 h5 h6 h7 h8) hx hy

end ExpansionBounds
