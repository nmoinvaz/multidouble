import ExpansionBounds.DWPlusFP

/-!
# AccurateDWPlusDW, the sum of two double words

Algorithm 6 of Joldes, Muller and Popescu (2017), the ADD of `DD::exp` and `DD::ln`:

  `(s_h, s_ℓ) = TwoSum(x_h, y_h)`, `(t_h, t_ℓ) = TwoSum(x_ℓ, y_ℓ)`, `c = RN(s_ℓ + t_h)`,
  `(v_h, v_ℓ) = FastTwoSum(s_h, c)`, `w = RN(t_ℓ + v_ℓ)`, `(z_h, z_ℓ) = FastTwoSum(v_h, w)`.

Theorem 3.1 of that paper, with its result a double word (`accDWPlusDW_good`): for `p ≥ 3` and double words `x` and
`y`, the result is a double word within `3u²/(1 - 4u)` of `x + y`, relatively.
-/

namespace ExpansionBounds

variable (p : ℤ)

/-- `c = RN(s_ℓ + t_h)` of AccurateDWPlusDW -/
noncomputable def dwAddC (xh xl yh yl : ℝ) : ℝ := RN p ((twoSum p xh yh).2 + (twoSum p xl yl).1)

/-- `(v_h, v_ℓ) = FastTwoSum(s_h, c)` of AccurateDWPlusDW -/
noncomputable def dwAddV (xh xl yh yl : ℝ) : ℝ × ℝ := fastTwoSum p (twoSum p xh yh).1 (dwAddC p xh xl yh yl)

/-- `w = RN(t_ℓ + v_ℓ)` of AccurateDWPlusDW -/
noncomputable def dwAddW (xh xl yh yl : ℝ) : ℝ := RN p ((twoSum p xl yl).2 + (dwAddV p xh xl yh yl).2)

/-- AccurateDWPlusDW: `(z_h, z_ℓ) = FastTwoSum(v_h, w)` -/
noncomputable def accDWPlusDW (x y : ℝ × ℝ) : ℝ × ℝ :=
  fastTwoSum p (dwAddV p x.1 x.2 y.1 y.2).1 (dwAddW p x.1 x.2 y.1 y.2)

/-- AccurateDWPlusDW commutes with a scaling by a power of two -/
theorem accDWPlusDW_scale (k : ℤ) (x y : ℝ × ℝ) :
    accDWPlusDW p ((2 : ℝ) ^ k * x.1, (2 : ℝ) ^ k * x.2) ((2 : ℝ) ^ k * y.1, (2 : ℝ) ^ k * y.2) =
      ((2 : ℝ) ^ k * (accDWPlusDW p x y).1, (2 : ℝ) ^ k * (accDWPlusDW p x y).2) := by
  unfold accDWPlusDW dwAddW dwAddV dwAddC
  simp only [twoSum_scale, ← mul_add, RN_zpow_mul, fastTwoSum_scale]

variable [Prec_gt_0 p]

/-- AccurateDWPlusDW commutes with negation -/
theorem accDWPlusDW_neg (x y : ℝ × ℝ) :
    accDWPlusDW p (-x.1, -x.2) (-y.1, -y.2) = (-(accDWPlusDW p x y).1, -(accDWPlusDW p x y).2) := by
  unfold accDWPlusDW dwAddW dwAddV dwAddC
  simp only [twoSum_neg, ← neg_add, RN_neg, fastTwoSum_neg]

/-- AccurateDWPlusDW does not see the order of its operands -/
theorem accDWPlusDW_swap (hp : 1 < p) {x y : ℝ × ℝ} (hx1 : F p x.1) (hx2 : F p x.2) (hy1 : F p y.1)
    (hy2 : F p y.2) : accDWPlusDW p x y = accDWPlusDW p y x := by
  unfold accDWPlusDW dwAddW dwAddV dwAddC
  simp only [twoSum_comm p hp hx1 hy1, twoSum_comm p hp hx2 hy2]

/-! ### Rounding and FastTwoSum on a grid -/

/-- a rounding is at least a float bound of its argument -/
theorem abs_RN_ge_of_F {z B : ℝ} (hB : F p B) (h : B ≤ |z|) : B ≤ |RN p z| := by
  rcases le_abs'.mp h with h1 | h1
  · have := RN_mono p h1
    rw [RN_neg, RN_of_F p hB] at this
    exact le_trans (by linarith) (neg_le_abs _)
  · have := RN_mono p h1
    rw [RN_of_F p hB] at this
    exact this.trans (le_abs_self _)

omit [Prec_gt_0 p] in
/-- the exponent of a nonzero float: `b` is a multiple of `2^e` with `2^(e + p - 1) ≤ |b| < 2^(e + p)` -/
theorem exists_exp {b : ℝ} (hb : F p b) (h0 : b ≠ 0) :
    ∃ e : ℤ, Mult e b ∧ (2 : ℝ) ^ (e + p - 1) ≤ |b| ∧ |b| < (2 : ℝ) ^ (e + p) := by
  obtain ⟨m, hm1, hm2⟩ := exists_mem_Ico_zpow (abs_pos.mpr h0) (by norm_num : (1 : ℝ) < 2)
  refine ⟨m + 1 - p, mult_of_F p hb ?_, ?_, ?_⟩
  · rw [show m + 1 - p + p - 1 = m by ring]
    exact hm1
  · rw [show m + 1 - p + p - 1 = m by ring]
    exact hm1
  · rw [show m + 1 - p + p = m + 1 by ring]
    exact hm2

/-- FastTwoSum is exact where `RN(a + b) - a` is a float: the error of the sum always is -/
theorem fastTwoSum_add_of_F (hp : 1 < p) {a b : ℝ} (ha : F p a) (hb : F p b) (h : F p (RN p (a + b) - a)) :
    (fastTwoSum p a b).1 + (fastTwoSum p a b).2 = a + b := by
  have hts := twoSum_add p hp ha hb
  have h1 : (twoSum p a b).1 = RN p (a + b) := rfl
  have hF : F p (b - (RN p (a + b) - a)) := by
    have := F_twoSum_snd p a b
    rwa [show (twoSum p a b).2 = b - (RN p (a + b) - a) by rw [h1] at hts; linarith] at this
  show RN p (a + b) + RN p (b - RN p (RN p (a + b) - a)) = a + b
  rw [RN_of_F p h, RN_of_F p hF]
  ring

/-- for floats `a` and `b` on the grid `2^e` with `|b| < 2^(e + p)`, `RN(a + b) - a` is a float -/
theorem F_RN_add_sub {a b : ℝ} {e : ℤ} (ha : F p a) (hb : F p b) (hma : Mult e a) (hmb : Mult e b)
    (hhi : |b| < (2 : ℝ) ^ (e + p)) : F p (RN p (a + b) - a) := by
  have hp0 := ‹Prec_gt_0 p›.pos
  have hmab : Mult e (a + b) := hma.add hmb
  rcases le_or_gt |a + b| ((2 : ℝ) ^ (e + p)) with hA | hB
  · -- `a + b` is a float
    have hF : F p (a + b) := F_of_mult_le p hmab hA
    rw [RN_of_F p hF, add_sub_cancel_left]
    exact hb
  · -- `2^m < |a + b| ≤ 2^(m + 1)` with `m ≥ e + p`: `s` and `a` are multiples of `2^(m - p)`
    have hpos : (0 : ℝ) < |a + b| := lt_trans (by positivity) hB
    obtain ⟨m, hm1, hm2⟩ := exists_mem_Ioc_zpow hpos (by norm_num : (1 : ℝ) < 2)
    have hem : e + p ≤ m := by
      have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp (lt_of_lt_of_le hB hm2)
      omega
    have hs : (2 : ℝ) ^ m ≤ |RN p (a + b)| := abs_RN_ge_of_F p (F_two_zpow p m) hm1.le
    have hms : Mult (m - p) (RN p (a + b)) :=
      (mult_of_F p (F_RN p (a + b)) (E := m + 1 - p) (by
        rw [show m + 1 - p + p - 1 = m by ring]
        exact hs)).mono (by omega)
    have hδ := RN_err_grid_le p (E := m + 1 - p) (z := a + b) (by
      rw [show m + 1 - p + p = m + 1 by ring]
      exact hm2)
    have e1 : (2 : ℝ) ^ (m + 1 - p) = 2 * (2 : ℝ) ^ (m - p) := by
      rw [← zpow_one_add₀ two_ne_zero]
      congr 1
      ring
    rw [e1] at hδ
    have h3 : (2 : ℝ) ^ (e + p) ≤ (2 : ℝ) ^ m := zpow_le_zpow_right₀ (by norm_num) hem
    have hma' : Mult (m - p) a := by
      rcases eq_or_lt_of_le hem with h | h
      · exact hma.mono (by omega)
      · refine mult_of_F p ha ?_
        rw [show m - p + p - 1 = m - 1 by ring]
        have h1 : (2 : ℝ) ^ (e + p) ≤ (2 : ℝ) ^ (m - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
        have h2 : (2 : ℝ) * (2 : ℝ) ^ (m - 1) = (2 : ℝ) ^ m := by
          rw [← zpow_one_add₀ two_ne_zero]
          congr 1
          ring
        have h4 := abs_add_le a b
        linarith
    have hmd : Mult (m - p) (RN p (a + b) - a) := hms.sub hma'
    have hlt : |RN p (a + b) - a| < (2 : ℝ) ^ m + (2 : ℝ) ^ (m - p) := by
      rw [show RN p (a + b) - a = (RN p (a + b) - (a + b)) + b by ring]
      have h2 := abs_add_le (RN p (a + b) - (a + b)) b
      linarith
    have hmB : Mult (m - p) ((2 : ℝ) ^ m + (2 : ℝ) ^ (m - p)) := (Mult.zpow (by omega)).add (Mult.zpow le_rfl)
    obtain ⟨h4, h5⟩ := abs_lt.mp hlt
    have h6 := Mult.le_sub hmd hmB h5
    have hm0 : Mult (m - p) (0 : ℝ) := ⟨0, by simp⟩
    have h7 := Mult.le_sub (hm0.sub hmB) hmd (by linarith)
    refine F_of_mult_le p hmd ?_
    rw [show m - p + p = m by ring, abs_le]
    constructor <;> linarith

/-- FastTwoSum is exact where `a` is a multiple of `2^E` and `|b| < 2^(E + p)`: the exponent of `b` is at most
that of `a`, with no condition on their magnitudes -/
theorem fastTwoSum_add_grid (hp : 1 < p) {a b : ℝ} (ha : F p a) (hb : F p b) {E : ℤ} (hma : Mult E a)
    (hbE : |b| < (2 : ℝ) ^ (E + p)) : (fastTwoSum p a b).1 + (fastTwoSum p a b).2 = a + b := by
  refine fastTwoSum_add_of_F p hp ha hb ?_
  by_cases hb0 : b = 0
  · rw [hb0, add_zero, RN_of_F p ha, sub_self]
    exact F_zero p
  · obtain ⟨e, hmb, hlo, hhi⟩ := exists_exp p hb hb0
    have heE : e ≤ E := by
      have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp (lt_of_le_of_lt hlo hbE)
      omega
    exact F_RN_add_sub p ha hb (hma.mono heE) hmb hhi

/-! ### The algorithm where its two FastTwoSums are exact -/

/-- AccurateDWPlusDW where `v_h + v_ℓ = s_h + c`, and `v_h = 0` or `|w| ≤ |v_h|`: the result is a double word, off
`x + y` by the rounding errors of `c` and of `w` -/
theorem accDWPlusDW_of_exact (hp : 1 < p) {xh xl yh yl : ℝ} (hxh : F p xh) (hxl : F p xl) (hyh : F p yh)
    (hyl : F p yl)
    (h4 : (dwAddV p xh xl yh yl).1 + (dwAddV p xh xl yh yl).2 = (twoSum p xh yh).1 + dwAddC p xh xl yh yl)
    (h6 : (dwAddV p xh xl yh yl).1 = 0 ∨ |dwAddW p xh xl yh yl| ≤ |(dwAddV p xh xl yh yl).1|) :
    DW p (accDWPlusDW p (xh, xl) (yh, yl)) ∧
      dwVal (accDWPlusDW p (xh, xl) (yh, yl)) - (xh + xl + (yh + yl)) =
        (dwAddC p xh xl yh yl - ((twoSum p xh yh).2 + (twoSum p xl yl).1)) +
          (dwAddW p xh xl yh yl - ((twoSum p xl yl).2 + (dwAddV p xh xl yh yl).2)) := by
  have hs := twoSum_add p hp hxh hyh
  have ht := twoSum_add p hp hxl hyl
  have hFv : F p (dwAddV p xh xl yh yl).1 := F_RN p _
  have hFw : F p (dwAddW p xh xl yh yl) := F_RN p _
  have hadd : (fastTwoSum p (dwAddV p xh xl yh yl).1 (dwAddW p xh xl yh yl)).1 +
      (fastTwoSum p (dwAddV p xh xl yh yl).1 (dwAddW p xh xl yh yl)).2 =
        (dwAddV p xh xl yh yl).1 + dwAddW p xh xl yh yl := by
    rcases h6 with h | h
    · rw [h, fastTwoSum_zero_left p hFw]
      ring
    · exact fastTwoSum_add p hp hFv hFw h
  refine ⟨fastTwoSum_dw p hadd, ?_⟩
  show (fastTwoSum p (dwAddV p xh xl yh yl).1 (dwAddW p xh xl yh yl)).1 +
    (fastTwoSum p (dwAddV p xh xl yh yl).1 (dwAddW p xh xl yh yl)).2 - (xh + xl + (yh + yl)) = _
  rw [hadd]
  linarith

/-- the conclusion of Theorem 3.1 of JMP17 at `(x_h, x_ℓ)` and `(y_h, y_ℓ)`: the result is a double word within
`3u²/(1 - 4u)` of `x + y`, relatively -/
def AccGood (xh xl yh yl : ℝ) : Prop :=
  DW p (accDWPlusDW p (xh, xl) (yh, yl)) ∧
    |dwVal (accDWPlusDW p (xh, xl) (yh, yl)) - (xh + xl + (yh + yl))| ≤
      3 * u p ^ 2 / (1 - 4 * u p) * |xh + xl + (yh + yl)|

omit [Prec_gt_0 p] in
/-- an error of at most `G u²` at a sum with `G (1 - 4u) ≤ 3|x + y|` is within the theorem's relative bound -/
theorem acc_rel (hu : 4 * u p < 1) {η X G : ℝ} (hη : |η| ≤ G * u p ^ 2) (hX : G * (1 - 4 * u p) ≤ 3 * |X|) :
    |η| ≤ 3 * u p ^ 2 / (1 - 4 * u p) * |X| := by
  have h14 : 0 < 1 - 4 * u p := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ h14]
  calc |η| * (1 - 4 * u p) ≤ G * u p ^ 2 * (1 - 4 * u p) := mul_le_mul_of_nonneg_right hη h14.le
    _ = u p ^ 2 * (G * (1 - 4 * u p)) := by ring
    _ ≤ u p ^ 2 * (3 * |X|) := mul_le_mul_of_nonneg_left hX (by positivity)
    _ = 3 * u p ^ 2 * |X| := by ring

/-- the regular cases of AccurateDWPlusDW, on bounds of its steps: `|s_ℓ + t_h| ≤ A ≤ 2^k₁ u` for a float `A`,
`|s_h| + A ≤ 2^k₂` and `A + 2^k₂ u/2 + 2^k₂ u ≤ |s_h|`. Then `|c| ≤ A ≤ |s_h|`, `|v_ℓ| ≤ 2^k₂ u/2`,
`|w| ≤ 2^k₂ u ≤ |v_h|`, both FastTwoSums are exact, and the errors of `c` and `w` are at most `2^k₁ u²/2` and
`2^k₂ u²/2` -/
theorem acc_chain (hp : 3 ≤ p) {xh xl yh yl : ℝ} (hxh : F p xh) (hxl : F p xl) (hyh : F p yh) (hyl : F p yl)
    (k1 k2 : ℤ) (hk2 : 0 ≤ k2) {A : ℝ} (hFA : F p A)
    (hA : |(twoSum p xh yh).2 + (twoSum p xl yl).1| ≤ A) (hAk : A ≤ (2 : ℝ) ^ k1 * u p)
    (hup : |(twoSum p xh yh).1| + A ≤ (2 : ℝ) ^ k2)
    (hlow : A + (2 : ℝ) ^ k2 * u p / 2 + (2 : ℝ) ^ k2 * u p ≤ |(twoSum p xh yh).1|)
    (hL : |xl + yl| ≤ 2 * u p)
    (hX : ((2 : ℝ) ^ k1 + (2 : ℝ) ^ k2) / 2 * (1 - 4 * u p) ≤ 3 * |xh + xl + (yh + yl)|) :
    AccGood p xh xl yh yl := by
  have hu := u_pos p
  have hu8 := u_le_eighth p hp
  have hp1 : 1 < p := by omega
  have hK1 : (0 : ℝ) < (2 : ℝ) ^ k1 := by positivity
  have hK2 : (1 : ℝ) ≤ (2 : ℝ) ^ k2 := one_le_zpow₀ (by norm_num) hk2
  have hA0 : 0 ≤ A := (abs_nonneg _).trans hA
  -- `c`: at most `A`, within `2^k₁ u²/2` of `s_ℓ + t_h`
  have hc : dwAddC p xh xl yh yl = RN p ((twoSum p xh yh).2 + (twoSum p xl yl).1) := rfl
  have hcA : |dwAddC p xh xl yh yl| ≤ A := abs_RN_le_of_F p hFA hA
  have hε1 := RN_grid p (k1 - p) (z := (twoSum p xh yh).2 + (twoSum p xl yl).1) (by
    rw [two_zpow_sub_p]
    exact hA.trans hAk)
  rw [two_zpow_sub_p, ← hc] at hε1
  -- the first FastTwoSum is exact
  have hFc : F p (dwAddC p xh xl yh yl) := F_RN p _
  have h4 : (dwAddV p xh xl yh yl).1 + (dwAddV p xh xl yh yl).2 = (twoSum p xh yh).1 + dwAddC p xh xl yh yl :=
    fastTwoSum_add p hp1 (F_twoSum_fst p xh yh) hFc (by nlinarith)
  -- `v_ℓ`: at most `2^k₂ u/2`
  have hv1 : (dwAddV p xh xl yh yl).1 = RN p ((twoSum p xh yh).1 + dwAddC p xh xl yh yl) := rfl
  have hsc : |(twoSum p xh yh).1 + dwAddC p xh xl yh yl| ≤ (2 : ℝ) ^ k2 :=
    (abs_add_le _ _).trans (by linarith)
  have hvl := RN_grid p k2 hsc
  rw [← hv1, show (dwAddV p xh xl yh yl).1 - ((twoSum p xh yh).1 + dwAddC p xh xl yh yl) = -(dwAddV p xh xl yh yl).2 by
    linarith, abs_neg] at hvl
  -- `t_ℓ`: at most `u²`
  have ht := twoSum_add p hp1 hxl hyl
  have ht1 : (twoSum p xl yl).1 = RN p (xl + yl) := rfl
  have htl := RN_grid p (1 - p) (z := xl + yl) (by rw [two_zpow_sub_p, zpow_one]; exact hL)
  rw [two_zpow_sub_p, zpow_one, ← ht1, show (twoSum p xl yl).1 - (xl + yl) = -(twoSum p xl yl).2 by linarith,
    abs_neg] at htl
  -- `w`: at most `2^k₂ u`, within `2^k₂ u²/2` of `t_ℓ + v_ℓ`
  have hw : dwAddW p xh xl yh yl = RN p ((twoSum p xl yl).2 + (dwAddV p xh xl yh yl).2) := rfl
  have htv : |(twoSum p xl yl).2 + (dwAddV p xh xl yh yl).2| ≤ (2 : ℝ) ^ k2 * u p := by
    have := abs_add_le (twoSum p xl yl).2 (dwAddV p xh xl yh yl).2
    nlinarith
  have hFu : F p ((2 : ℝ) ^ k2 * u p) := F_zpow_mul p k2 (F_two_zpow p (-p))
  have hwB : |dwAddW p xh xl yh yl| ≤ (2 : ℝ) ^ k2 * u p := abs_RN_le_of_F p hFu htv
  have hε2 := RN_grid p (k2 - p) (z := (twoSum p xl yl).2 + (dwAddV p xh xl yh yl).2) (by
    rw [two_zpow_sub_p]
    exact htv)
  rw [two_zpow_sub_p, ← hw] at hε2
  -- `|v_h| ≥ |s_h| - |c| - |v_ℓ| ≥ |w|`
  have hvh : |dwAddW p xh xl yh yl| ≤ |(dwAddV p xh xl yh yl).1| := by
    have e : (twoSum p xh yh).1 = (dwAddV p xh xl yh yl).1 + ((dwAddV p xh xl yh yl).2 - dwAddC p xh xl yh yl) := by
      linarith
    have h1 := abs_add_le (dwAddV p xh xl yh yl).1 ((dwAddV p xh xl yh yl).2 - dwAddC p xh xl yh yl)
    rw [← e] at h1
    have h2 := abs_sub (dwAddV p xh xl yh yl).2 (dwAddC p xh xl yh yl)
    linarith
  obtain ⟨hdw, hval⟩ := accDWPlusDW_of_exact p hp1 hxh hxl hyh hyl h4 (Or.inr hvh)
  refine ⟨hdw, ?_⟩
  rw [hval]
  refine acc_rel p (by linarith) (G := ((2 : ℝ) ^ k1 + (2 : ℝ) ^ k2) / 2) ?_ hX
  have := abs_add_le (dwAddC p xh xl yh yl - ((twoSum p xh yh).2 + (twoSum p xl yl).1))
    (dwAddW p xh xl yh yl - ((twoSum p xl yl).2 + (dwAddV p xh xl yh yl).2))
  linarith

omit [Prec_gt_0 p] in
/-- an error of at most `3u²|x + y|` is within the theorem's relative bound -/
theorem acc_rel' (hu0 : 0 < u p) (hu : 4 * u p < 1) {η X : ℝ} (hη : |η| ≤ 3 * u p ^ 2 * |X|) :
    |η| ≤ 3 * u p ^ 2 / (1 - 4 * u p) * |X| := by
  have h14 : 0 < 1 - 4 * u p := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ h14]
  nlinarith [abs_nonneg η, mul_nonneg (abs_nonneg η) hu0.le]

/-- AccurateDWPlusDW at `y_h = -x_h`: the result is `TwoSum(x_ℓ, y_ℓ)`, the exact sum -/
theorem acc_cancel (hp : 3 ≤ p) {xh xl yl : ℝ} (hxh : F p xh) (hxl : F p xl) (hyl : F p yl) :
    AccGood p xh xl (-xh) yl := by
  have hu := u_pos p
  have hu8 := u_le_eighth p hp
  have hp1 : 1 < p := by omega
  have hsh : (twoSum p xh (-xh)).1 = 0 := by
    show RN p (xh + -xh) = 0
    rw [add_neg_cancel, RN_zero]
  have hsl : (twoSum p xh (-xh)).2 = 0 := by
    have := twoSum_add p hp1 hxh (F_neg p hxh)
    rw [hsh] at this
    linarith
  have ht := twoSum_add p hp1 hxl hyl
  have hFt : F p (twoSum p xl yl).1 := F_twoSum_fst p xl yl
  have hc : dwAddC p xh xl (-xh) yl = (twoSum p xl yl).1 := by
    show RN p ((twoSum p xh (-xh)).2 + (twoSum p xl yl).1) = _
    rw [hsl, zero_add, RN_of_F p hFt]
  have hv : dwAddV p xh xl (-xh) yl = ((twoSum p xl yl).1, 0) := by
    show fastTwoSum p (twoSum p xh (-xh)).1 (dwAddC p xh xl (-xh) yl) = _
    rw [hsh, hc]
    exact fastTwoSum_zero_left p hFt
  have hw : dwAddW p xh xl (-xh) yl = (twoSum p xl yl).2 := by
    show RN p ((twoSum p xl yl).2 + (dwAddV p xh xl (-xh) yl).2) = _
    rw [hv, add_zero, RN_of_F p (F_twoSum_snd p xl yl)]
  have h6 : |dwAddW p xh xl (-xh) yl| ≤ |(dwAddV p xh xl (-xh) yl).1| := by
    rw [hw, hv]
    have h1 := abs_RN_sub_le_u_RN p (xl + yl)
    have ht1 : (twoSum p xl yl).1 = RN p (xl + yl) := rfl
    rw [← ht1, show (twoSum p xl yl).1 - (xl + yl) = -(twoSum p xl yl).2 by linarith, abs_neg] at h1
    nlinarith [abs_nonneg (twoSum p xl yl).1]
  obtain ⟨hdw, hval⟩ := accDWPlusDW_of_exact p hp1 hxh hxl (F_neg p hxh) hyl (by rw [hv, hsh, hc]; ring) (Or.inr h6)
  refine ⟨hdw, ?_⟩
  rw [hval, hc, hw, hv, hsl]
  simp only [zero_add, add_zero, sub_self, abs_zero]
  have h14 : 0 < 1 - 4 * u p := by linarith
  positivity

/-- the Sterbenz case of AccurateDWPlusDW: `s_h = x_h + y_h > 0` is exact and a multiple of `u`, `|x_ℓ + y_ℓ| ≤ 2u`
and `|t_h| ≤ 3s_h/2`. The first FastTwoSum is exact on the grid of `s_h`, the second since `v_h`, a nonzero
multiple of the spacing at `t_h`, is at least `2|t_ℓ|`; and `w` is exact where `-3s_h/2 ≤ t_h ≤ -s_h/2`, or else
`|x_ℓ + y_ℓ| ≤ x + y` and the error of `w` is at most `(2 + u)u²(x + y)` -/
theorem acc_sterbenz (hp : 3 ≤ p) {xh xl yh yl : ℝ} (hxh : F p xh) (hxl : F p xl) (hyh : F p yh) (hyl : F p yl)
    (hs : F p (xh + yh)) (hs0 : 0 < xh + yh) (hm : Mult (-p) (xh + yh)) (hL : |xl + yl| ≤ 2 * u p)
    (ht32 : |(twoSum p xl yl).1| ≤ 3 / 2 * (xh + yh)) : AccGood p xh xl yh yl := by
  have hu := u_pos p
  have hu8 := u_le_eighth p hp
  have hp1 : 1 < p := by omega
  have h14 : 0 < 1 - 4 * u p := by linarith
  have hsh : (twoSum p xh yh).1 = xh + yh := RN_of_F p hs
  have hsl : (twoSum p xh yh).2 = 0 := by
    have := twoSum_add p hp1 hxh hyh
    rw [hsh] at this
    linarith
  have ht := twoSum_add p hp1 hxl hyl
  have ht1 : (twoSum p xl yl).1 = RN p (xl + yl) := rfl
  have hFt : F p (twoSum p xl yl).1 := F_twoSum_fst p xl yl
  have hF2u : F p (2 * u p) := by
    have := F_zpow_mul p 1 (F_two_zpow p (-p))
    rwa [zpow_one] at this
  have hth : |(twoSum p xl yl).1| ≤ 2 * u p := abs_RN_le_of_F p hF2u hL
  have hc : dwAddC p xh xl yh yl = (twoSum p xl yl).1 := by
    show RN p ((twoSum p xh yh).2 + (twoSum p xl yl).1) = _
    rw [hsl, zero_add, RN_of_F p hFt]
  -- the first FastTwoSum is exact
  have h4 : (dwAddV p xh xl yh yl).1 + (dwAddV p xh xl yh yl).2 = (twoSum p xh yh).1 + dwAddC p xh xl yh yl :=
    fastTwoSum_add_grid p hp1 (F_twoSum_fst p xh yh) (F_RN p _) (E := -p) (by rw [hsh]; exact hm) (by
      rw [hc, neg_add_cancel, zpow_zero]
      linarith)
  have hv1 : (dwAddV p xh xl yh yl).1 = RN p (xh + yh + (twoSum p xl yl).1) := by
    show RN p ((twoSum p xh yh).1 + dwAddC p xh xl yh yl) = _
    rw [hsh, hc]
  rw [hsh, hc] at h4
  have hw : dwAddW p xh xl yh yl = RN p ((twoSum p xl yl).2 + (dwAddV p xh xl yh yl).2) := rfl
  have hh4 : (dwAddV p xh xl yh yl).1 + (dwAddV p xh xl yh yl).2 = (twoSum p xh yh).1 + dwAddC p xh xl yh yl := by
    rw [hsh, hc]
    exact h4
  by_cases h0 : xh + yh + (twoSum p xl yl).1 = 0
  · -- `s_h + t_h = 0`: `v = 0` and `w = t_ℓ`
    have hv0 : (dwAddV p xh xl yh yl).1 = 0 := by rw [hv1, h0, RN_zero]
    have hvl0 : (dwAddV p xh xl yh yl).2 = 0 := by linarith
    obtain ⟨hdw, hval⟩ := accDWPlusDW_of_exact p hp1 hxh hxl hyh hyl hh4 (Or.inl hv0)
    refine ⟨hdw, ?_⟩
    rw [hval, hc, hw, hvl0, hsl, add_zero, RN_of_F p (F_twoSum_snd p xl yl)]
    simp only [zero_add, sub_self, add_zero, abs_zero]
    positivity
  · -- `|t_ℓ| ≤ |v_h|/2`
    have htl : |(twoSum p xl yl).2| ≤ |(dwAddV p xh xl yh yl).1| / 2 := by
      by_cases hth0 : (twoSum p xl yl).1 = 0
      · have hL0 : xl + yl = 0 := RN_eq_zero p (by rw [← ht1]; exact hth0)
        have : (twoSum p xl yl).2 = 0 := by linarith
        rw [this, abs_zero]
        positivity
      · obtain ⟨e, hme, hlo, hhi⟩ := exists_exp p hFt hth0
        have he : e ≤ -p := by
          have h1 : (2 : ℝ) ^ (e + p - 1) ≤ (2 : ℝ) ^ (1 - p) := by
            rw [two_zpow_sub_p p 1, zpow_one]
            linarith
          have := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h1
          omega
        have hms : Mult e (xh + yh + (twoSum p xl yl).1) := (hm.mono he).add hme
        have hm0 : Mult e (0 : ℝ) := ⟨0, by simp⟩
        have hge : (2 : ℝ) ^ e ≤ |xh + yh + (twoSum p xl yl).1| := by
          rcases lt_or_gt_of_ne h0 with h | h
          · have := Mult.le_sub hms hm0 h
            rw [abs_of_neg h]
            linarith
          · have := Mult.le_sub hm0 hms h
            rw [abs_of_pos h]
            linarith
        have hvge : (2 : ℝ) ^ e ≤ |(dwAddV p xh xl yh yl).1| := by
          rw [hv1]
          exact abs_RN_ge_of_F p (F_two_zpow p e) hge
        have hLle : |xl + yl| ≤ (2 : ℝ) ^ (e + p) := by
          by_contra h
          have := abs_RN_ge_of_F p (F_two_zpow p (e + p)) (not_le.mp h).le
          rw [← ht1] at this
          linarith
        have := RN_err_grid_le p hLle
        rw [← ht1, show (twoSum p xl yl).1 - (xl + yl) = -(twoSum p xl yl).2 by linarith, abs_neg] at this
        linarith
    -- `|v_ℓ| ≤ u|v_h|`, so `|w| ≤ (1 + u)(1/2 + u)|v_h| ≤ |v_h|`
    have hvl : |(dwAddV p xh xl yh yl).2| ≤ u p * |(dwAddV p xh xl yh yl).1| := by
      have := abs_RN_sub_le_u_RN p (xh + yh + (twoSum p xl yl).1)
      rw [← hv1, show (dwAddV p xh xl yh yl).1 - (xh + yh + (twoSum p xl yl).1) = -(dwAddV p xh xl yh yl).2 by
        linarith, abs_neg] at this
      exact this
    have h6 : |dwAddW p xh xl yh yl| ≤ |(dwAddV p xh xl yh yl).1| := by
      have h1 := abs_RN_le p ((twoSum p xl yl).2 + (dwAddV p xh xl yh yl).2)
      rw [← hw] at h1
      have h2 := abs_add_le (twoSum p xl yl).2 (dwAddV p xh xl yh yl).2
      have h3 : (1 + u p) * |(twoSum p xl yl).2 + (dwAddV p xh xl yh yl).2| ≤
          (1 + u p) * ((1 / 2 + u p) * |(dwAddV p xh xl yh yl).1|) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have h5 : (1 + u p) * (1 / 2 + u p) ≤ 1 := by nlinarith
      have h7 := mul_le_mul_of_nonneg_right h5 (abs_nonneg (dwAddV p xh xl yh yl).1)
      linarith
    obtain ⟨hdw, hval⟩ := accDWPlusDW_of_exact p hp1 hxh hxl hyh hyl hh4 (Or.inr h6)
    refine ⟨hdw, ?_⟩
    rw [hval, hc, hsl, zero_add, sub_self, zero_add]
    obtain ⟨ht3, ht4⟩ := abs_le.mp ht32
    rcases le_or_gt (twoSum p xl yl).1 (-(1 / 2) * (xh + yh)) with hS | hS
    · -- Sterbenz on `s_h + t_h`: `v_ℓ = 0` and `w = t_ℓ`
      have hF : F p (xh + yh + (twoSum p xl yl).1) := by
        have := F_sub_of_near p hs (F_neg p hFt) (by
          rw [abs_of_pos hs0, abs_le]
          constructor <;> linarith)
        rwa [sub_neg_eq_add] at this
      have hvl0 : (dwAddV p xh xl yh yl).2 = 0 := by
        rw [hv1, RN_of_F p hF] at h4
        linarith
      rw [hw, hvl0, add_zero, RN_of_F p (F_twoSum_snd p xl yl), sub_self, abs_zero]
      positivity
    · -- `x_ℓ + y_ℓ > -s_h/2`, so `|x_ℓ + y_ℓ| ≤ x + y`
      have hFh : F p (1 / 2 * (xh + yh)) := by
        have := F_zpow_mul p (-1) hs
        rwa [show ((2 : ℝ) ^ (-1 : ℤ)) = 1 / 2 by norm_num] at this
      have hLgt : -(1 / 2) * (xh + yh) < xl + yl := by
        by_contra h
        have := RN_mono p (not_lt.mp h)
        rw [← ht1, show -(1 / 2) * (xh + yh) = -(1 / 2 * (xh + yh)) by ring, RN_neg, RN_of_F p hFh] at this
        linarith
      have hXpos : 0 < xh + xl + (yh + yl) := by linarith
      have hLX : |xl + yl| ≤ xh + xl + (yh + yl) := by
        rw [abs_le]
        constructor <;> linarith
      have h1 : |(twoSum p xl yl).2| ≤ u p * |xl + yl| := by
        have := (abs_RN_sub_le_us p (xl + yl)).trans (mul_le_mul_of_nonneg_right (us_le_u p) (abs_nonneg _))
        rwa [← ht1, show (twoSum p xl yl).1 - (xl + yl) = -(twoSum p xl yl).2 by linarith, abs_neg] at this
      have h2 : |(dwAddV p xh xl yh yl).2| ≤ u p * |xh + yh + (twoSum p xl yl).1| := by
        have := (abs_RN_sub_le_us p (xh + yh + (twoSum p xl yl).1)).trans
          (mul_le_mul_of_nonneg_right (us_le_u p) (abs_nonneg _))
        rwa [← hv1, show (dwAddV p xh xl yh yl).1 - (xh + yh + (twoSum p xl yl).1) = -(dwAddV p xh xl yh yl).2 by
          linarith, abs_neg] at this
      have h3 : |xh + yh + (twoSum p xl yl).1| ≤ xh + xl + (yh + yl) + |(twoSum p xl yl).2| := by
        have := abs_add_le (xh + xl + (yh + yl)) (-(twoSum p xl yl).2)
        rw [abs_neg, abs_of_pos hXpos, show xh + xl + (yh + yl) + -(twoSum p xl yl).2 =
          xh + yh + (twoSum p xl yl).1 by linarith] at this
        exact this
      have h5 : |dwAddW p xh xl yh yl - ((twoSum p xl yl).2 + (dwAddV p xh xl yh yl).2)| ≤
          u p * |(twoSum p xl yl).2 + (dwAddV p xh xl yh yl).2| := by
        rw [hw]
        exact (abs_RN_sub_le_us p _).trans (mul_le_mul_of_nonneg_right (us_le_u p) (abs_nonneg _))
      have h7 := abs_add_le (twoSum p xl yl).2 (dwAddV p xh xl yh yl).2
      refine acc_rel' p hu (by linarith) ?_
      rw [abs_of_pos hXpos]
      obtain ⟨X, hXd⟩ : ∃ X, X = xh + xl + (yh + yl) := ⟨_, rfl⟩
      obtain ⟨T, hTd⟩ : ∃ T, T = |(twoSum p xl yl).2| := ⟨_, rfl⟩
      obtain ⟨V, hVd⟩ : ∃ V, V = |(dwAddV p xh xl yh yl).2| := ⟨_, rfl⟩
      obtain ⟨Lb, hLd⟩ : ∃ Lb, Lb = |xl + yl| := ⟨_, rfl⟩
      obtain ⟨S, hSd⟩ : ∃ S, S = |xh + yh + (twoSum p xl yl).1| := ⟨_, rfl⟩
      rw [← hXd] at hLX h3 hXpos ⊢
      rw [← hTd] at h1 h3 h7
      rw [← hVd] at h2 h7
      rw [← hLd] at h1 hLX
      rw [← hSd] at h2 h3
      have hT0 : 0 ≤ T := by rw [hTd]; exact abs_nonneg _
      have hV0 : 0 ≤ V := by rw [hVd]; exact abs_nonneg _
      have hLb0 : 0 ≤ Lb := by rw [hLd]; exact abs_nonneg _
      have a1 : T ≤ u p * X := h1.trans (mul_le_mul_of_nonneg_left hLX hu.le)
      have a2 : V ≤ u p * (X + u p * X) := h2.trans (mul_le_mul_of_nonneg_left (by linarith) hu.le)
      have a3 : u p * |(twoSum p xl yl).2 + (dwAddV p xh xl yh yl).2| ≤ u p * (u p * X + u p * (X + u p * X)) :=
        mul_le_mul_of_nonneg_left (by linarith) hu.le
      have a4 : u p * (u p * X + u p * (X + u p * X)) ≤ 3 * u p ^ 2 * X := by
        have : u p * (u p * X + u p * (X + u p * X)) = (2 + u p) * (u p ^ 2 * X) := by ring
        rw [this, show 3 * u p ^ 2 * X = 3 * (u p ^ 2 * X) by ring]
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith

/-- the low part of a double word whose high part is below `1` in magnitude is at most `u/2` -/
theorem dw_lo_le_half {a ℓ : ℝ} (hdw : RN p (a + ℓ) = a) (ha : |a| < 1) : |ℓ| ≤ u p / 2 := by
  have h := dw_lo_le_of_lt_two p (a := 2 * a) (ℓ := 2 * ℓ) (by
    have := RN_zpow_mul p 1 (a + ℓ)
    rw [zpow_one, hdw, mul_add] at this
    exact this) (by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  linarith

/-- Theorem 3.1 of JMP17 on normalized operands: `x_h ∈ [1, 2)` and `|y_h| ≤ x_h`. The cases are those of the
paper: `y_h = -x_h`; `-x_h < y_h ≤ -x_h/2` (Sterbenz); and `-x_h/2 < y_h` with `x_h + y_h` at most `1 - 2u`, at
most `2 - 4u`, or above -/
theorem accDWPlusDW_norm (hp : 3 ≤ p) {xh xl yh yl : ℝ} (hxh : F p xh) (hxl : F p xl) (hyh : F p yh)
    (hyl : F p yl) (hdx : RN p (xh + xl) = xh) (hdy : RN p (yh + yl) = yh) (h1 : 1 ≤ xh) (h2 : xh < 2)
    (hyx : |yh| ≤ xh) : AccGood p xh xl yh yl := by
  have hu := u_pos p
  have hu8 := u_le_eighth p hp
  have hp1 : 1 < p := by omega
  have hxl1 := dw_lo_le p hp1 hxh hdx h1 h2
  have hyl1 := dw_lo_le_of_lt_two p hdy (lt_of_le_of_lt hyx h2)
  obtain ⟨hy1, hy2⟩ := abs_le.mp hyx
  obtain ⟨hxl2, hxl3⟩ := abs_le.mp hxl1
  obtain ⟨hyl2, hyl3⟩ := abs_le.mp hyl1
  have hL : |xl + yl| ≤ 2 * u p := (abs_add_le _ _).trans (by linarith)
  have hF2u : F p (2 * u p) := by
    have := F_zpow_mul p 1 (F_two_zpow p (-p))
    rwa [zpow_one] at this
  have hF3 : F p (3 : ℝ) := F_of_mult_le p (E := 0) ⟨3, by norm_num⟩ (by
    rw [zero_add, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    calc (3 : ℝ) ≤ (2 : ℝ) ^ (2 : ℤ) := by norm_num
      _ ≤ (2 : ℝ) ^ p := zpow_le_zpow_right₀ (by norm_num) (by omega))
  have hF32 : F p (3 / 2 * u p) := by
    have := F_zpow_mul p (-1 - p) hF3
    have e : (2 : ℝ) ^ (-1 - p) * 3 = 3 / 2 * u p := by
      rw [two_zpow_sub_p p (-1), show ((2 : ℝ) ^ (-1 : ℤ)) = 1 / 2 by norm_num]
      ring
    rwa [e] at this
  have hmx : Mult (1 - p) xh := mult_of_one_le p hxh h1
  have hm0 : ∀ E : ℤ, Mult E (0 : ℝ) := fun E => ⟨0, by simp⟩
  have hth : |(twoSum p xl yl).1| ≤ 2 * u p := abs_RN_le_of_F p hF2u hL
  have hx2 := le_two_sub_of_lt_two p hxh h1 h2
  rcases le_or_gt yh (-(xh / 2)) with hS | hS
  · rcases eq_or_lt_of_le hy1 with h0 | h0
    · -- `y_h = -x_h`
      rw [← h0]
      exact acc_cancel p hp hxh hxl hyl
    · -- `-x_h < y_h ≤ -x_h/2`
      have hs : F p (xh + yh) := by
        have := F_sub_of_near p hxh (F_neg p hyh) (by
          rw [abs_of_pos (by linarith : (0 : ℝ) < xh), abs_le]
          constructor <;> linarith)
        rwa [sub_neg_eq_add] at this
      have hmy : Mult (-p) yh := mult_of_F p hyh (by
        rw [show (-p + p - 1 : ℤ) = -1 by ring, abs_of_neg (by linarith)]
        norm_num
        linarith)
      have hm : Mult (-p) (xh + yh) := (hmx.mono (by omega)).add hmy
      refine acc_sterbenz p hp hxh hxl hyh hyl hs (by linarith) hm hL ?_
      rcases le_or_gt yh (-1) with hσ | hσ
      · -- `y_h ≤ -1`: `s_h ≥ 2u ≥ |t_h|`
        have hmy2 : Mult (1 - p) yh := mult_of_F p hyh (by
          rw [show (1 - p + p - 1 : ℤ) = 0 by ring, zpow_zero, abs_of_neg (by linarith)]
          linarith)
        have := Mult.le_sub (hm0 (1 - p)) (hmx.add hmy2) (by linarith : (0 : ℝ) < xh + yh)
        rw [two_zpow_sub_p p 1, zpow_one] at this
        linarith
      · -- `-1 < y_h`: `|y_ℓ| ≤ u/2`, and `s_h ≥ u` with `|t_h| ≤ 3u/2`
        have hyl4 := dw_lo_le_half p hdy (by
          rw [abs_of_neg (by linarith)]
          linarith)
        have := Mult.le_sub (hm0 (-p)) hm (by linarith : (0 : ℝ) < xh + yh)
        have e : (2 : ℝ) ^ (-p) = u p := rfl
        rw [e] at this
        have hL2 : |xl + yl| ≤ 3 / 2 * u p := (abs_add_le _ _).trans (by linarith)
        have hth2 : |(twoSum p xl yl).1| ≤ 3 / 2 * u p := abs_RN_le_of_F p hF32 hL2
        linarith
  · -- `-x_h/2 < y_h`: `s_h ≥ 1/2`
    have hts := twoSum_add p hp1 hxh hyh
    have hs1 : (twoSum p xh yh).1 = RN p (xh + yh) := rfl
    have hsl : (twoSum p xh yh).2 = -(RN p (xh + yh) - (xh + yh)) := by rw [← hs1]; linarith
    have hFhalf : F p (1 / 2 : ℝ) := by
      have h := F_two_zpow p (-1)
      rwa [zpow_neg, zpow_one, ← one_div] at h
    have hs_half : 1 / 2 ≤ RN p (xh + yh) := by
      have := RN_mono p (by linarith : (1 / 2 : ℝ) ≤ xh + yh)
      rwa [RN_of_F p hFhalf] at this
    have hsabs : |(twoSum p xh yh).1| = RN p (xh + yh) := by rw [hs1, abs_of_pos (by linarith)]
    have e4 : (2 : ℝ) ^ (2 : ℤ) = 4 := by norm_num
    have hF12 : F p (1 - 2 * u p) := by
      have hm1 : Mult (-p) (1 : ℝ) := by
        have := Mult.zpow (E := -p) (e := 0) (by omega)
        rwa [zpow_zero] at this
      have hm2u : Mult (-p) (2 * u p) := by
        have := Mult.zpow (E := -p) (e := 1 - p) (by omega)
        rwa [two_zpow_sub_p p 1, zpow_one] at this
      exact F_of_mult_le p (hm1.sub hm2u) (by
        rw [show (-p + p : ℤ) = 0 by ring, zpow_zero, abs_of_pos (by linarith)]
        linarith)
    have hF24 : F p (2 - 4 * u p) := by
      have := F_zpow_mul p 1 hF12
      rwa [zpow_one, show 2 * (1 - 2 * u p) = 2 - 4 * u p by ring] at this
    rcases le_or_gt (xh + yh) (1 - 2 * u p) with hc1 | hc1
    · -- `1/2 < x_h + y_h ≤ 1 - 2u`
      have hs_up : RN p (xh + yh) ≤ 1 - 2 * u p := by
        have := RN_mono p hc1
        rwa [RN_of_F p hF12] at this
      have hyl4 := dw_lo_le_half p hdy (by
        rw [abs_lt]
        constructor <;> linarith)
      have hL2 : |xl + yl| ≤ 3 / 2 * u p := (abs_add_le _ _).trans (by linarith)
      have hth2 : |(twoSum p xl yl).1| ≤ 3 / 2 * u p := abs_RN_le_of_F p hF32 hL2
      have hg := RN_grid p 0 (z := xh + yh) (by
        rw [zpow_zero, abs_of_pos (by linarith)]
        linarith)
      rw [zpow_zero, one_mul] at hg
      have hsl' : |(twoSum p xh yh).2| ≤ u p / 2 := by
        rw [hsl, abs_neg]
        exact hg
      refine acc_chain p hp hxh hxl hyh hyl 1 0 le_rfl hF2u ?_ ?_ ?_ ?_ hL ?_
      · exact (abs_add_le _ _).trans (by linarith)
      · rw [zpow_one]
      · rw [hsabs, zpow_zero]
        linarith
      · rw [hsabs, zpow_zero]
        linarith
      · rw [zpow_one, zpow_zero]
        have hX : 1 / 2 - 3 / 2 * u p ≤ xh + xl + (yh + yl) := by linarith [(abs_le.mp hyl4).1]
        rw [abs_of_pos (by linarith)]
        linarith
    · rcases le_or_gt (xh + yh) (2 - 4 * u p) with hc2 | hc2
      · -- `1 - 2u < x_h + y_h ≤ 2 - 4u`
        have hs_lo : 1 - 2 * u p ≤ RN p (xh + yh) := by
          have := RN_mono p hc1.le
          rwa [RN_of_F p hF12] at this
        have hs_up : RN p (xh + yh) ≤ 2 - 4 * u p := by
          have := RN_mono p hc2
          rwa [RN_of_F p hF24] at this
        have hg := RN_grid p 1 (z := xh + yh) (by
          rw [zpow_one, abs_of_pos (by linarith)]
          linarith)
        rw [zpow_one] at hg
        have hsl' : |(twoSum p xh yh).2| ≤ u p := by
          rw [hsl, abs_neg]
          linarith
        have hF3u : F p (3 * u p) := by
          have := F_zpow_mul p (-p) hF3
          rwa [show (2 : ℝ) ^ (-p) * 3 = 3 * u p by unfold u; ring] at this
        refine acc_chain p hp hxh hxl hyh hyl 2 1 (by norm_num) hF3u ?_ ?_ ?_ ?_ hL ?_
        · exact (abs_add_le _ _).trans (by linarith)
        · rw [e4]
          linarith
        · rw [hsabs, zpow_one]
          linarith
        · rw [hsabs, zpow_one]
          linarith
        · rw [e4, zpow_one]
          have hX : 1 - 4 * u p ≤ xh + xl + (yh + yl) := by linarith
          rw [abs_of_pos (by linarith)]
          linarith
      · -- `2 - 4u < x_h + y_h ≤ 2x_h`
        have hF2x : F p (2 * xh) := by
          have := F_zpow_mul p 1 hxh
          rwa [zpow_one] at this
        have hs_up : RN p (xh + yh) ≤ 4 - 4 * u p := by
          have := RN_mono p (by linarith : xh + yh ≤ 2 * xh)
          rw [RN_of_F p hF2x] at this
          linarith
        have hs_lo : 2 - 4 * u p ≤ RN p (xh + yh) := by
          have := RN_mono p hc2.le
          rwa [RN_of_F p hF24] at this
        have hg := RN_grid p 2 (z := xh + yh) (by
          rw [e4, abs_of_pos (by linarith)]
          linarith)
        rw [e4] at hg
        have hsl' : |(twoSum p xh yh).2| ≤ 2 * u p := by
          rw [hsl, abs_neg]
          linarith
        have hF4u : F p (4 * u p) := by
          have := F_zpow_mul p 2 (F_two_zpow p (-p))
          rwa [e4] at this
        refine acc_chain p hp hxh hxl hyh hyl 2 2 (by norm_num) hF4u ?_ ?_ ?_ ?_ hL ?_
        · exact (abs_add_le _ _).trans (by linarith)
        · rw [e4]
        · rw [hsabs, e4]
          linarith
        · rw [hsabs, e4]
          linarith
        · rw [e4]
          have hX : 2 - 6 * u p ≤ xh + xl + (yh + yl) := by linarith
          rw [abs_of_pos (by linarith)]
          linarith

/-- `AccGood` passes from operands scaled by a power of two -/
theorem AccGood.of_scale {xh xl yh yl : ℝ} (k : ℤ)
    (h : AccGood p ((2 : ℝ) ^ k * xh) ((2 : ℝ) ^ k * xl) ((2 : ℝ) ^ k * yh) ((2 : ℝ) ^ k * yl)) :
    AccGood p xh xl yh yl := by
  have hK : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hs : accDWPlusDW p ((2 : ℝ) ^ k * xh, (2 : ℝ) ^ k * xl) ((2 : ℝ) ^ k * yh, (2 : ℝ) ^ k * yl) =
      ((2 : ℝ) ^ k * (accDWPlusDW p (xh, xl) (yh, yl)).1, (2 : ℝ) ^ k * (accDWPlusDW p (xh, xl) (yh, yl)).2) :=
    accDWPlusDW_scale p k (xh, xl) (yh, yl)
  unfold AccGood at h ⊢
  rw [hs] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨DW.of_scale p k h1, ?_⟩
  have e1 : dwVal ((2 : ℝ) ^ k * (accDWPlusDW p (xh, xl) (yh, yl)).1,
      (2 : ℝ) ^ k * (accDWPlusDW p (xh, xl) (yh, yl)).2) -
        ((2 : ℝ) ^ k * xh + (2 : ℝ) ^ k * xl + ((2 : ℝ) ^ k * yh + (2 : ℝ) ^ k * yl)) =
          (2 : ℝ) ^ k * (dwVal (accDWPlusDW p (xh, xl) (yh, yl)) - (xh + xl + (yh + yl))) := by
    unfold dwVal
    ring
  have e2 : (2 : ℝ) ^ k * xh + (2 : ℝ) ^ k * xl + ((2 : ℝ) ^ k * yh + (2 : ℝ) ^ k * yl) =
      (2 : ℝ) ^ k * (xh + xl + (yh + yl)) := by ring
  rw [e1, e2, abs_mul, abs_mul, abs_of_pos hK] at h2
  exact le_of_mul_le_mul_left (by linarith) hK

/-- `AccGood` passes from the negated operands -/
theorem AccGood.of_neg {xh xl yh yl : ℝ} (h : AccGood p (-xh) (-xl) (-yh) (-yl)) : AccGood p xh xl yh yl := by
  have hs : accDWPlusDW p (-xh, -xl) (-yh, -yl) =
      (-(accDWPlusDW p (xh, xl) (yh, yl)).1, -(accDWPlusDW p (xh, xl) (yh, yl)).2) :=
    accDWPlusDW_neg p (xh, xl) (yh, yl)
  unfold AccGood at h ⊢
  rw [hs] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨DW.of_neg p h1, ?_⟩
  have e1 : dwVal (-(accDWPlusDW p (xh, xl) (yh, yl)).1, -(accDWPlusDW p (xh, xl) (yh, yl)).2) -
      (-xh + -xl + (-yh + -yl)) = -(dwVal (accDWPlusDW p (xh, xl) (yh, yl)) - (xh + xl + (yh + yl))) := by
    unfold dwVal
    ring
  rw [e1, abs_neg, show -xh + -xl + (-yh + -yl) = -(xh + xl + (yh + yl)) by ring, abs_neg] at h2
  exact h2

/-- `AccGood` passes from the exchanged operands -/
theorem AccGood.of_swap (hp : 1 < p) {xh xl yh yl : ℝ} (hxh : F p xh) (hxl : F p xl) (hyh : F p yh)
    (hyl : F p yl) (h : AccGood p yh yl xh xl) : AccGood p xh xl yh yl := by
  unfold AccGood at h ⊢
  rw [accDWPlusDW_swap p hp (x := (xh, xl)) (y := (yh, yl)) hxh hxl hyh hyl, add_comm (xh + xl)]
  exact h

/-- Theorem 3.1 of JMP17 for a positive `x_h ≥ |y_h|`: `x_h` scaled into `[1, 2)` -/
theorem accDWPlusDW_pos (hp : 3 ≤ p) {xh xl yh yl : ℝ} (hxh : F p xh) (hxl : F p xl) (hyh : F p yh)
    (hyl : F p yl) (hdx : RN p (xh + xl) = xh) (hdy : RN p (yh + yl) = yh) (hx0 : 0 < xh) (hyx : |yh| ≤ xh) :
    AccGood p xh xl yh yl := by
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hx0 (by norm_num : (1 : ℝ) < 2)
  have ha : (0 : ℝ) < (2 : ℝ) ^ (-n) := by positivity
  have s1 : (2 : ℝ) ^ (-n) * (2 : ℝ) ^ n = 1 := by rw [← zpow_add₀ two_ne_zero, neg_add_cancel, zpow_zero]
  have s2 : (2 : ℝ) ^ (-n) * (2 : ℝ) ^ (n + 1) = 2 := by
    rw [← zpow_add₀ two_ne_zero, show -n + (n + 1) = 1 by ring, zpow_one]
  refine AccGood.of_scale p (-n) (accDWPlusDW_norm p hp (F_zpow_mul p (-n) hxh) (F_zpow_mul p (-n) hxl)
    (F_zpow_mul p (-n) hyh) (F_zpow_mul p (-n) hyl) (by rw [← mul_add, RN_zpow_mul, hdx])
    (by rw [← mul_add, RN_zpow_mul, hdy]) ?_ ?_ ?_)
  · have := mul_le_mul_of_nonneg_left hn1 ha.le
    rwa [s1] at this
  · have := mul_lt_mul_of_pos_left hn2 ha
    rwa [s2] at this
  · rw [abs_mul, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left hyx ha.le

/-- Theorem 3.1 of JMP17 for double words with `|y_h| ≤ |x_h|` -/
theorem accDWPlusDW_gen (hp : 3 ≤ p) {xh xl yh yl : ℝ} (hxh : F p xh) (hxl : F p xl) (hyh : F p yh)
    (hyl : F p yl) (hdx : RN p (xh + xl) = xh) (hdy : RN p (yh + yl) = yh) (hyx : |yh| ≤ |xh|) :
    AccGood p xh xl yh yl := by
  rcases lt_trichotomy xh 0 with h | h | h
  · refine AccGood.of_neg p (accDWPlusDW_pos p hp (F_neg p hxh) (F_neg p hxl) (F_neg p hyh) (F_neg p hyl)
      (by rw [← neg_add, RN_neg, hdx]) (by rw [← neg_add, RN_neg, hdy]) (by linarith) ?_)
    rw [abs_neg]
    rwa [abs_of_neg h] at hyx
  · -- `x_h = 0`, so `y_h = 0 = -x_h`
    have hy0 : yh = -xh := by
      rw [h, abs_zero] at hyx
      rw [h, neg_zero]
      exact abs_eq_zero.mp (le_antisymm hyx (abs_nonneg yh))
    rw [hy0]
    exact acc_cancel p hp hxh hxl hyl
  · exact accDWPlusDW_pos p hp hxh hxl hyh hyl hdx hdy h (by rwa [abs_of_pos h] at hyx)

/-- Theorem 3.1 of JMP17, with its result a double word: for `p ≥ 3` and double words `x` and `y`,
`AccurateDWPlusDW(x, y)` is a double word within `3u²/(1 - 4u)` of `x + y`, relatively -/
theorem accDWPlusDW_good (hp : 3 ≤ p) {x y : ℝ × ℝ} (hx : DW p x) (hy : DW p y) :
    DW p (accDWPlusDW p x y) ∧
      |dwVal (accDWPlusDW p x y) - (dwVal x + dwVal y)| ≤ 3 * u p ^ 2 / (1 - 4 * u p) * |dwVal x + dwVal y| := by
  obtain ⟨xh, xl⟩ := x
  obtain ⟨yh, yl⟩ := y
  obtain ⟨hxh, hxl, hdx⟩ := hx
  obtain ⟨hyh, hyl, hdy⟩ := hy
  have hxh' : F p xh := hxh
  have hxl' : F p xl := hxl
  have hyh' : F p yh := hyh
  have hyl' : F p yl := hyl
  have hdx' : RN p (xh + xl) = xh := hdx
  have hdy' : RN p (yh + yl) = yh := hdy
  show AccGood p xh xl yh yl
  rcases le_total |yh| |xh| with h | h
  · exact accDWPlusDW_gen p hp hxh' hxl' hyh' hyl' hdx' hdy' h
  · exact AccGood.of_swap p (by omega) hxh' hxl' hyh' hyl'
      (accDWPlusDW_gen p hp hyh' hyl' hxh' hxl' hdy' hdx' h)

/-- Theorem 3.1 of JMP17: for `p ≥ 3`, AccurateDWPlusDW of two double words is within `3u²/(1 - 4u)` of their
sum, relatively -/
theorem accDWPlusDW_err (hp : 3 ≤ p) {x y : ℝ × ℝ} (hx : DW p x) (hy : DW p y) :
    |dwVal (accDWPlusDW p x y) - (dwVal x + dwVal y)| ≤ 3 * u p ^ 2 / (1 - 4 * u p) * |dwVal x + dwVal y| :=
  (accDWPlusDW_good p hp hx hy).2

/-- the result of AccurateDWPlusDW is a double word: its last FastTwoSum is exact -/
theorem accDWPlusDW_dw (hp : 3 ≤ p) {x y : ℝ × ℝ} (hx : DW p x) (hy : DW p y) : DW p (accDWPlusDW p x y) :=
  (accDWPlusDW_good p hp hx hy).1

end ExpansionBounds
