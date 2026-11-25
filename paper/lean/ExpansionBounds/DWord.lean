import ExpansionBounds.RoundEval
import ExpansionBounds.LnB
import ExpansionBounds.Red

/-!
# Double-word arithmetic: DWTimesFP1

The product of a double-word number by a floating-point number, Algorithm 7 of Joldes, Muller and Popescu (2017),
within `3u²/2 + 4u³` of the exact product for `p ≥ 4` (their Theorem 4.1). The proof is theirs: after a scaling by
powers of two, `x_h` and `y` lie in `[1, 2)`, the two roundings that are not error-free are bounded on their grids,
and the cases `x_h y ≥ 2`, `t_h = 2` and `t_h < 2` give the three bounds.
-/

namespace ExpansionBounds

variable (p : ℤ)

/-- rounding commutes with a scaling by a power of two: the exponent range is unbounded -/
theorem RN_zpow_mul (k : ℤ) (x : ℝ) : RN p ((2 : ℝ) ^ k * x) = (2 : ℝ) ^ k * RN p x := by
  by_cases hx : x = 0
  · rw [hx, mul_zero, RN_zero, mul_zero]
  have hk : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  obtain ⟨e, he1, he2⟩ := exists_mem_Ico_zpow (abs_pos.mpr hx) (by norm_num : (1 : ℝ) < 2)
  have h1 : (2 : ℝ) ^ (e + 1 - 1) ≤ |x| := by rwa [add_sub_cancel_right]
  have a1 : (2 : ℝ) ^ (e + 1 + k - 1) ≤ |(2 : ℝ) ^ k * x| := by
    rw [abs_mul, abs_of_pos hk, show e + 1 + k - 1 = k + e by ring, zpow_add₀ two_ne_zero]
    exact mul_le_mul_of_nonneg_left he1 hk.le
  have a2 : |(2 : ℝ) ^ k * x| < (2 : ℝ) ^ (e + 1 + k) := by
    rw [abs_mul, abs_of_pos hk, show e + 1 + k = k + (e + 1) by ring, zpow_add₀ two_ne_zero]
    exact mul_lt_mul_of_pos_left he2 hk
  rw [RN_of_mag p a1 a2, RN_of_mag p h1 he2]
  have e1 : (2 : ℝ) ^ k * x * (2 : ℝ) ^ (-(e + 1 + k - p)) = x * (2 : ℝ) ^ (-(e + 1 - p)) := by
    rw [show -(e + 1 + k - p) = -k + -(e + 1 - p) by ring, zpow_add₀ two_ne_zero, zpow_neg]
    field_simp
  rw [e1, show e + 1 + k - p = k + (e + 1 - p) by ring, zpow_add₀ two_ne_zero]
  ring

variable [Prec_gt_0 p]

/-- the error of `RN` on a grid, up to the grid's last point: `|RN(z) - z| ≤ 2^E/2` for `|z| ≤ 2^{E+p}` -/
theorem RN_err_grid_le {E : ℤ} {z : ℝ} (hz : |z| ≤ (2 : ℝ) ^ (E + p)) : |RN p z - z| ≤ (2 : ℝ) ^ E / 2 := by
  by_cases h : |z| + (2 : ℝ) ^ E / 2 < (2 : ℝ) ^ (E + p)
  · exact RN_err_grid p h
  -- `z` is within half a step of `±2^{E+p}`, which is in `F`
  have hE : (0 : ℝ) < (2 : ℝ) ^ E := by positivity
  have hF : F p ((2 : ℝ) ^ (E + p)) := F_two_zpow p _
  have hnear := (RN_nearest p z).2
  rcases le_total 0 z with h0 | h0
  · rw [abs_of_nonneg h0] at hz h
    refine (hnear _ hF).trans ?_
    rw [abs_of_nonneg (by linarith)]
    linarith
  · rw [abs_of_nonpos h0] at hz h
    refine (hnear _ (F_neg p hF)).trans ?_
    rw [abs_of_nonpos (by linarith)]
    linarith

omit [Prec_gt_0 p] in
/-- a power of two is a multiple of every smaller one -/
theorem Mult.zpow {E e : ℤ} (h : E ≤ e) : Mult E ((2 : ℝ) ^ e) := by
  obtain ⟨n, hn⟩ := Mult.pow_split h
  exact ⟨2 ^ n, by rw [hn]; push_cast; ring⟩

omit [Prec_gt_0 p] in
/-- the product of two multiples -/
theorem Mult.mul {E E' : ℤ} {x y : ℝ} (hx : Mult E x) (hy : Mult E' y) : Mult (E + E') (x * y) := by
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨m, rfl⟩ := hy
  exact ⟨k * m, by rw [zpow_add₀ two_ne_zero]; push_cast; ring⟩

omit [Prec_gt_0 p] in
/-- two multiples of `2^E`, one below the other, are a step apart -/
theorem Mult.le_sub {E : ℤ} {z b : ℝ} (hz : Mult E z) (hb : Mult E b) (h : z < b) : z ≤ b - (2 : ℝ) ^ E := by
  obtain ⟨k, rfl⟩ := hz
  obtain ⟨m, rfl⟩ := hb
  have hE : (0 : ℝ) < (2 : ℝ) ^ E := by positivity
  have hkm : k < m := by
    by_contra hc
    have : (m : ℝ) ≤ k := by exact_mod_cast not_lt.mp hc
    nlinarith
  have : (k : ℝ) ≤ m - 1 := by exact_mod_cast Int.le_sub_one_of_lt hkm
  nlinarith

/-- a multiple of `2^E` of size at most `2^{E+p}` is in `F` -/
theorem F_of_mult_le {E : ℤ} {z : ℝ} (hz : Mult E z) (hb : |z| ≤ (2 : ℝ) ^ (E + p)) : F p z := by
  rcases hb.lt_or_eq with h | h
  · exact F_of_mult p hz h
  · rcases abs_eq (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (E + p)) |>.mp h with h1 | h1
    · rw [h1]; exact F_two_zpow p _
    · rw [h1]; exact F_neg p (F_two_zpow p _)

/-- DWTimesFP1 (Algorithm 7 of JMP17): `(c_h, c_l1) = 2Prod(x_h, y)`, `c_l2 = RN(x_l y)`,
`(t_h, t_l1) = Fast2Sum(c_h, c_l2)`, `t_l2 = RN(t_l1 + c_l1)` and `(z_h, z_l) = Fast2Sum(t_h, t_l2)` -/
noncomputable def dwTimesFP1 (xh xl y : ℝ) : ℝ × ℝ :=
  let c := twoProd p xh y
  let cl2 := RN p (xl * y)
  let t := fastTwoSum p c.1 cl2
  let tl2 := RN p (t.2 + c.2)
  fastTwoSum p t.1 tl2

/-- the low part of a double word whose high part is in `[1, 2)` is at most `u` -/
theorem dw_lo_le (hp : 1 < p) {xh xl : ℝ} (hxh : F p xh) (hdw : RN p (xh + xl) = xh) (hx1 : 1 ≤ xh) (hx2 : xh < 2) :
    |xl| ≤ u p := by
  have hu := u_pos p
  have e1 : (2 : ℝ) ^ (1 - p) = 2 * u p := by
    unfold u; rw [show (1 : ℤ) - p = 1 + -p by ring, zpow_add₀ two_ne_zero, zpow_one]
  have hmx : Mult (1 - p) xh := mult_of_F p hxh (by
    rw [show (1 - p + p - 1 : ℤ) = 0 by ring, zpow_zero, abs_of_pos (by linarith)]; exact hx1)
  have hm2u : Mult (1 - p) (2 * u p) := by rw [← e1]; exact Mult.zpow le_rfl
  have hm2 : Mult (1 - p) 2 := by
    have := Mult.zpow (E := 1 - p) (e := 1) (by omega)
    rwa [zpow_one] at this
  have hm1 : Mult (1 - p) 1 := by
    have := Mult.zpow (E := 1 - p) (e := 0) (by omega)
    rwa [zpow_zero] at this
  have htop : (2 : ℝ) ^ (1 - p + p) = 2 := by rw [show (1 - p + p : ℤ) = 1 by ring, zpow_one]
  have hxle : xh ≤ 2 - 2 * u p := by
    have := Mult.le_sub hmx hm2 hx2
    rwa [e1] at this
  have hn := (RN_nearest p (xh + xl)).2
  rw [hdw] at hn
  rcases le_or_gt 0 xl with h0 | h0
  · -- the float above `x_h`
    have hF : F p (xh + 2 * u p) :=
      F_of_mult_le p (hmx.add hm2u) (by rw [htop, abs_of_pos (by linarith)]; linarith)
    have h := hn _ hF
    rw [show xh - (xh + xl) = -xl by ring, abs_neg, abs_of_nonneg h0,
      show xh + 2 * u p - (xh + xl) = 2 * u p - xl by ring] at h
    rw [abs_of_nonneg h0]
    rcases abs_cases (2 * u p - xl) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  · rw [abs_of_neg h0]
    by_cases hx : xh = 1
    · -- the float below `1` is `1 - u`
      have hmu : Mult (-p) (u p) := by unfold u; exact Mult.zpow le_rfl
      have hm1' : Mult (-p) 1 := by
        have := Mult.zpow (E := -p) (e := 0) (by omega)
        rwa [zpow_zero] at this
      have hF : F p (1 - u p) := F_of_mult_le p (hm1'.sub hmu) (by
        rw [show (-p + p : ℤ) = 0 by ring, zpow_zero, abs_of_pos (by unfold u at *; nlinarith [hu])]
        linarith)
      have h := hn _ hF
      rw [hx, show (1 : ℝ) - (1 + xl) = -xl by ring, abs_neg, abs_of_neg h0,
        show 1 - u p - (1 + xl) = -(u p + xl) by ring, abs_neg] at h
      rcases abs_cases (u p + xl) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
    · -- the float below `x_h > 1` is `x_h - 2u`
      have hx' : 1 < xh := lt_of_le_of_ne hx1 (Ne.symm hx)
      have h1x := Mult.le_sub hm1 hmx hx'
      rw [e1] at h1x
      have hF : F p (xh - 2 * u p) :=
        F_of_mult_le p (hmx.sub hm2u) (by rw [htop, abs_of_pos (by linarith)]; linarith)
      have h := hn _ hF
      rw [show xh - (xh + xl) = -xl by ring, abs_neg, abs_of_neg h0,
        show xh - 2 * u p - (xh + xl) = -(2 * u p + xl) by ring, abs_neg] at h
      rcases abs_cases (2 * u p + xl) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith

omit [Prec_gt_0 p] in
/-- `u ≤ 1/16` from `p ≥ 4` -/
theorem u_le_sixteenth (hp : 4 ≤ p) : u p ≤ 1 / 16 := by
  unfold u
  calc (2 : ℝ) ^ (-p) ≤ (2 : ℝ) ^ (-4 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ = 1 / 16 := by norm_num

omit [Prec_gt_0 p] in
theorem two_zpow_sub_p (k : ℤ) : (2 : ℝ) ^ (k - p) = (2 : ℝ) ^ k * u p := by
  rw [sub_eq_add_neg, zpow_add₀ two_ne_zero]
  rfl

/-- the grid's error: `|RN z - z| ≤ 2^k u/2` for `|z| ≤ 2^k` -/
theorem RN_grid (k : ℤ) {z : ℝ} (hz : |z| ≤ (2 : ℝ) ^ k) : |RN p z - z| ≤ (2 : ℝ) ^ k * u p / 2 := by
  have h := RN_err_grid_le p (E := k - p) (z := z) (by rwa [sub_add_cancel])
  rwa [two_zpow_sub_p] at h

omit [Prec_gt_0 p] in
/-- a float at least `1` is a multiple of `2u` -/
theorem mult_of_one_le {v : ℝ} (hv : F p v) (h1 : 1 ≤ v) : Mult (1 - p) v :=
  mult_of_F p hv (by rw [show (1 - p + p - 1 : ℤ) = 0 by ring, zpow_zero, abs_of_pos (by linarith)]; exact h1)

/-- a float in `[1, 2)` is at most `2 - 2u` -/
theorem le_two_sub_of_lt_two {v : ℝ} (hv : F p v) (h1 : 1 ≤ v) (h2 : v < 2) : v ≤ 2 - 2 * u p := by
  have hm2 : Mult (1 - p) 2 := by
    have := Mult.zpow (E := 1 - p) (e := 1) (by have := ‹Prec_gt_0 p›.pos; omega)
    rwa [zpow_one] at this
  have := Mult.le_sub (mult_of_one_le p hv h1) hm2 h2
  rwa [two_zpow_sub_p, zpow_one] at this

/-- the steps of DWTimesFP1 on operands in `[1, 2)`: its result is `t_h + t_l2`, with the bounds of each value -/
theorem dwTimesFP1_steps (hp : 4 ≤ p) {xh xl y : ℝ} (hxh : F p xh) (hy : F p y)
    (hdw : RN p (xh + xl) = xh) (hx1 : 1 ≤ xh) (hx2 : xh < 2) (hy1 : 1 ≤ y) (hy2 : y < 2) :
    ∃ ch cl2 th tl2 : ℝ, ch = RN p (xh * y) ∧ cl2 = RN p (xl * y) ∧ th = RN p (ch + cl2) ∧
      tl2 = RN p ((ch + cl2 - th) + (xh * y - ch)) ∧
      (dwTimesFP1 p xh xl y).1 + (dwTimesFP1 p xh xl y).2 = th + tl2 ∧
      (dwTimesFP1 p xh xl y).1 = RN p (th + tl2) ∧
      1 ≤ ch ∧ |xh * y - ch| ≤ 2 * u p ∧ |cl2| ≤ 2 * u p ∧ |cl2 - xl * y| ≤ u p ^ 2 ∧
      1 - 2 * u p ≤ th ∧ |ch + cl2 - th| ≤ 2 * u p ∧ |tl2| ≤ 4 * u p ∧
      |tl2 - ((ch + cl2 - th) + (xh * y - ch))| ≤ 2 * u p ^ 2 ∧ |xl| ≤ u p := by
  have hp1 : 1 < p := by omega
  have hu := u_pos p
  have hu16 := u_le_sixteenth p hp
  have e1 : (2 : ℝ) ^ (1 - p) = 2 * u p := by rw [two_zpow_sub_p, zpow_one]
  have e2 : (2 : ℝ) ^ (2 - p) = 4 * u p := by rw [two_zpow_sub_p]; norm_num
  have F1 : F p 1 := by simpa using F_two_zpow p 0
  have hxle := le_two_sub_of_lt_two p hxh hx1 hx2
  have hyle := le_two_sub_of_lt_two p hy hy1 hy2
  have hxl := dw_lo_le p hp1 hxh hdw hx1 hx2
  obtain ⟨hxl1, hxl2⟩ := abs_le.mp hxl
  obtain ⟨hcsum, -, -⟩ := facts_c p hxh hy
  have hP1 : 1 ≤ xh * y := by nlinarith
  have hP4 : xh * y ≤ 4 - 4 * u p := by nlinarith
  -- `c_h` and `c_l1`
  have hch1 : 1 ≤ RN p (xh * y) := by
    have := RN_mono p hP1
    rwa [RN_of_F p F1] at this
  have hF44 : F p (4 - 4 * u p) := by
    have h4 : Mult (2 - p) 4 := by
      have := Mult.zpow (E := 2 - p) (e := 2) (by omega)
      norm_num at this
      exact this
    have h4u : Mult (2 - p) (4 * u p) := by rw [← e2]; exact Mult.zpow le_rfl
    refine F_of_mult_le p (h4.sub h4u) ?_
    rw [show (2 - p + p : ℤ) = 2 by ring, abs_of_pos (by linarith)]
    norm_num
    linarith
  have hch4 : RN p (xh * y) ≤ 4 - 4 * u p := by
    have := RN_mono p hP4
    rwa [RN_of_F p hF44] at this
  have hcl1 : |xh * y - RN p (xh * y)| ≤ 2 * u p := by
    rw [abs_sub_comm]
    calc |RN p (xh * y) - xh * y| ≤ (2 : ℝ) ^ (2 : ℤ) * u p / 2 :=
          RN_grid p 2 (by rw [abs_of_pos (by linarith)]; norm_num; linarith)
      _ = 2 * u p := by norm_num; ring
  -- `c_l2` and `ε_1`
  have hxly : |xl * y| ≤ 2 * u p := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < y)]
    nlinarith [abs_nonneg xl]
  have hcl2b : |RN p (xl * y)| ≤ 2 * u p := by
    refine abs_RN_le_of_F p ?_ hxly
    rw [← e1]; exact F_two_zpow p _
  have he1 : |RN p (xl * y) - xl * y| ≤ u p ^ 2 := by
    calc |RN p (xl * y) - xl * y| ≤ (2 : ℝ) ^ (1 - p) * u p / 2 := RN_grid p (1 - p) (by rw [e1]; exact hxly)
      _ = u p ^ 2 := by rw [e1]; ring
  obtain ⟨hcl2a, hcl2c⟩ := abs_le.mp hcl2b
  -- the first Fast2Sum is exact
  have ht_sum := fastTwoSum_add p hp1 (F_RN p (xh * y)) (F_RN p (xl * y))
    (by rw [abs_of_pos (by linarith : (0 : ℝ) < RN p (xh * y))]; linarith)
  have htl1 : |RN p (xh * y) + RN p (xl * y) - RN p (RN p (xh * y) + RN p (xl * y))| ≤ 2 * u p := by
    rw [abs_sub_comm]
    calc _ ≤ (2 : ℝ) ^ (2 : ℤ) * u p / 2 :=
          RN_grid p 2 (by rw [abs_of_pos (by linarith)]; norm_num; linarith)
      _ = 2 * u p := by norm_num; ring
  -- `t_l2` and `ε_2`
  have hsum4 : |RN p (xh * y) + RN p (xl * y) - RN p (RN p (xh * y) + RN p (xl * y)) + (xh * y - RN p (xh * y))| ≤
      4 * u p := (abs_add_le _ _).trans (by linarith)
  have htl2b := abs_RN_le_of_F p (by rw [← e2]; exact F_two_zpow p _) hsum4
  have he2 : |RN p (RN p (xh * y) + RN p (xl * y) - RN p (RN p (xh * y) + RN p (xl * y)) + (xh * y - RN p (xh * y))) -
      (RN p (xh * y) + RN p (xl * y) - RN p (RN p (xh * y) + RN p (xl * y)) + (xh * y - RN p (xh * y)))| ≤
        2 * u p ^ 2 := by
    calc _ ≤ (2 : ℝ) ^ (2 - p) * u p / 2 := RN_grid p (2 - p) (by rw [e2]; exact hsum4)
      _ = 2 * u p ^ 2 := by rw [e2]; ring
  -- the second Fast2Sum is exact
  have hF12 : F p (1 - 2 * u p) := by
    have hmu : Mult (-p) (2 * u p) := by rw [← e1]; exact Mult.zpow (by omega)
    have hm1' : Mult (-p) 1 := by
      have := Mult.zpow (E := -p) (e := 0) (by omega)
      rwa [zpow_zero] at this
    refine F_of_mult_le p (hm1'.sub hmu) ?_
    rw [show (-p + p : ℤ) = 0 by ring, zpow_zero, abs_of_pos (by linarith)]
    linarith
  have hth1 : 1 - 2 * u p ≤ RN p (RN p (xh * y) + RN p (xl * y)) := by
    have := RN_mono p (show 1 - 2 * u p ≤ RN p (xh * y) + RN p (xl * y) by linarith)
    rwa [RN_of_F p hF12] at this
  -- the values, as the algorithm forms them
  have hc2 : (twoProd p xh y).2 = xh * y - RN p (xh * y) := by
    have : (twoProd p xh y).1 = RN p (xh * y) := rfl
    linarith
  have ht2 : (fastTwoSum p (RN p (xh * y)) (RN p (xl * y))).2 =
      RN p (xh * y) + RN p (xl * y) - RN p (RN p (xh * y) + RN p (xl * y)) := by
    have : (fastTwoSum p (RN p (xh * y)) (RN p (xl * y))).1 = RN p (RN p (xh * y) + RN p (xl * y)) := rfl
    linarith
  have hz : dwTimesFP1 p xh xl y = fastTwoSum p (RN p (RN p (xh * y) + RN p (xl * y)))
      (RN p ((fastTwoSum p (RN p (xh * y)) (RN p (xl * y))).2 + (twoProd p xh y).2)) := rfl
  rw [ht2, hc2] at hz
  refine ⟨RN p (xh * y), RN p (xl * y), RN p (RN p (xh * y) + RN p (xl * y)), _, rfl, rfl, rfl, rfl, ?_, ?_, hch1,
    hcl1, hcl2b, he1, hth1, htl1, htl2b, he2, hxl⟩
  · rw [hz]
    exact fastTwoSum_add p hp1 (F_RN p _) (F_RN p _) (by
      rw [abs_of_pos (by linarith : (0 : ℝ) < RN p (RN p (xh * y) + RN p (xl * y)))]
      linarith [(abs_le.mp htl2b).2])
  · rw [hz]
    rfl

/-- DWTimesFP1 on operands in `[1, 2)` with `x_h y < 2` and `c_h + c_l2 ≤ 2`: the two rounding errors together are
at most `3u²/2`. Either `|c_l2| < u` and `ε_1 ≤ u²/2`, or `t_l1 + c_l1` is a float and `ε_2 = 0` -/
theorem dwTimesFP1_fine (hp : 4 ≤ p) {xh xl y ch cl2 th tl2 : ℝ} (hxh : F p xh) (hy : F p y) (hx1 : 1 ≤ xh)
    (hy1 : 1 ≤ y) (hch : ch = RN p (xh * y)) (hcl2 : cl2 = RN p (xl * y)) (hth : th = RN p (ch + cl2))
    (htl2 : tl2 = RN p ((ch + cl2 - th) + (xh * y - ch))) (hch1 : 1 ≤ ch) (hcl2b : |cl2| ≤ 2 * u p)
    (he1 : |cl2 - xl * y| ≤ u p ^ 2) (hth1 : 1 - 2 * u p ≤ th) (hP2 : xh * y < 2) (hcc : ch + cl2 ≤ 2) :
    |tl2 - ((ch + cl2 - th) + (xh * y - ch)) - (xl * y - cl2)| ≤ 3 / 2 * u p ^ 2 := by
  have hu := u_pos p
  have hu16 := u_le_sixteenth p hp
  have e1 : (2 : ℝ) ^ (1 - p) = 2 * u p := by rw [two_zpow_sub_p, zpow_one]
  have Fu : F p (u p) := F_two_zpow p (-p)
  have hPpos : 0 < xh * y := mul_pos (by linarith) (by linarith)
  have hccpos : 0 < ch + cl2 := by linarith [(abs_le.mp hcl2b).1]
  have hcl1' : |xh * y - ch| ≤ u p := by
    rw [hch, abs_sub_comm]
    calc _ ≤ (2 : ℝ) ^ (1 : ℤ) * u p / 2 := RN_grid p 1 (by rw [abs_of_pos hPpos, zpow_one]; exact hP2.le)
      _ = u p := by rw [zpow_one]; ring
  have htl1' : |ch + cl2 - th| ≤ u p := by
    rw [hth, abs_sub_comm]
    calc _ ≤ (2 : ℝ) ^ (1 : ℤ) * u p / 2 := RN_grid p 1 (by rw [abs_of_pos hccpos, zpow_one]; exact hcc)
      _ = u p := by rw [zpow_one]; ring
  have hs2 : |(ch + cl2 - th) + (xh * y - ch)| ≤ 2 * u p := (abs_add_le _ _).trans (by linarith)
  by_cases hsmall : |cl2| < u p
  · -- `|c_l2| < u`: `|x_l y| ≤ u`, so `ε_1` is at most `u²/2`
    have hxly : |xl * y| ≤ u p := by
      by_contra hc
      have hc' := not_le.mp hc
      rcases le_or_gt 0 (xl * y) with h0 | h0
      · rw [abs_of_nonneg h0] at hc'
        have := RN_mono p hc'.le
        rw [RN_of_F p Fu, ← hcl2] at this
        linarith [le_abs_self cl2]
      · rw [abs_of_neg h0] at hc'
        have := RN_mono p (show xl * y ≤ -u p by linarith)
        rw [RN_neg, RN_of_F p Fu, ← hcl2] at this
        linarith [neg_abs_le cl2]
    have he1' : |cl2 - xl * y| ≤ u p ^ 2 / 2 := by
      rw [hcl2]
      calc _ ≤ (2 : ℝ) ^ (-p) * u p / 2 := RN_grid p (-p) hxly
        _ = u p ^ 2 / 2 := by rw [show (2 : ℝ) ^ (-p) = u p from rfl]; ring
    have he2' : |tl2 - ((ch + cl2 - th) + (xh * y - ch))| ≤ u p ^ 2 := by
      rw [htl2]
      calc _ ≤ (2 : ℝ) ^ (1 - p) * u p / 2 := RN_grid p (1 - p) (by rw [e1]; exact hs2)
        _ = u p ^ 2 := by rw [e1]; ring
    have := abs_sub (tl2 - ((ch + cl2 - th) + (xh * y - ch))) (xl * y - cl2)
    rw [abs_sub_comm (xl * y) cl2] at this
    linarith
  · -- `|c_l2| ≥ u`: `t_l1 + c_l1` is a multiple of `2u²` of size at most `2u`, a float, so `ε_2 = 0`
    have hsmall' := not_lt.mp hsmall
    have hFch : F p ch := hch ▸ F_RN p _
    have hFcl2 : F p cl2 := hcl2 ▸ F_RN p _
    have hFth : F p th := hth ▸ F_RN p _
    have hmc : Mult (1 - 2 * p) cl2 := mult_of_F p hFcl2 (by
      rw [show (1 - 2 * p + p - 1 : ℤ) = -p by ring]; exact hsmall')
    have hmch : Mult (1 - 2 * p) ch := (mult_of_one_le p hFch hch1).mono (by omega)
    have hmth : Mult (1 - 2 * p) th := by
      refine (mult_of_F p (E := -p) hFth ?_).mono (by omega)
      rw [show (-p + p - 1 : ℤ) = -1 by ring, abs_of_pos (by linarith)]
      norm_num
      linarith
    have hmP : Mult (1 - 2 * p) (xh * y) :=
      ((mult_of_one_le p hxh hx1).mul (mult_of_one_le p hy hy1)).mono (by omega)
    have hms : Mult (1 - 2 * p) ((ch + cl2 - th) + (xh * y - ch)) := ((hmch.add hmc).sub hmth).add (hmP.sub hmch)
    have hFs : F p ((ch + cl2 - th) + (xh * y - ch)) := F_of_mult_le p hms (by
      rw [show (1 - 2 * p + p : ℤ) = 1 - p by ring, e1]; exact hs2)
    have h0 : tl2 - ((ch + cl2 - th) + (xh * y - ch)) = 0 := by rw [htl2, RN_of_F p hFs, sub_self]
    rw [h0, zero_sub, abs_neg, abs_sub_comm]
    linarith [pow_pos hu 2]

/-- Theorem 4.1 of JMP17 for operands scaled to `[1, 2)`: DWTimesFP1 is within `3u²/2 + 4u³` of `xy`, relatively -/
theorem dwTimesFP1_norm (hp : 4 ≤ p) {xh xl y : ℝ} (hxh : F p xh) (hy : F p y)
    (hdw : RN p (xh + xl) = xh) (hx1 : 1 ≤ xh) (hx2 : xh < 2) (hy1 : 1 ≤ y) (hy2 : y < 2) :
    |(dwTimesFP1 p xh xl y).1 + (dwTimesFP1 p xh xl y).2 - (xh + xl) * y| ≤
      (3 / 2 * u p ^ 2 + 4 * u p ^ 3) * ((xh + xl) * y) := by
  obtain ⟨ch, cl2, th, tl2, hch, hcl2, hth, htl2, hsum, -, hch1, hcl1, hcl2b, he1, hth1, htl1, htl2b, he2, hxl⟩ :=
    dwTimesFP1_steps p hp hxh hy hdw hx1 hx2 hy1 hy2
  have hp1 : 1 < p := by omega
  have hu := u_pos p
  have hu16 := u_le_sixteenth p hp
  have hu2 : u p ^ 2 ≤ 1 / 256 := by
    have := pow_le_pow_left₀ hu.le hu16 2
    norm_num at this
    exact this
  have e1 : (2 : ℝ) ^ (1 - p) = 2 * u p := by rw [two_zpow_sub_p, zpow_one]
  have F2 : F p 2 := by simpa using F_two_zpow p 1
  obtain ⟨hxl1, hxl2⟩ := abs_le.mp hxl
  have hres : (dwTimesFP1 p xh xl y).1 + (dwTimesFP1 p xh xl y).2 - (xh + xl) * y =
      (tl2 - ((ch + cl2 - th) + (xh * y - ch))) - (xl * y - cl2) := by rw [hsum]; ring
  rw [hres]
  have hy0 : (0 : ℝ) < y := by linarith
  have hxy1 : 1 - u p ≤ (xh + xl) * y := by
    calc 1 - u p = (1 - u p) * 1 := (mul_one _).symm
      _ ≤ (xh + xl) * y := mul_le_mul (by linarith) hy1 zero_le_one (by linarith)
  have hc0 : (0 : ℝ) ≤ 3 / 2 * u p ^ 2 + 4 * u p ^ 3 := by positivity
  have habs3 : |tl2 - ((ch + cl2 - th) + (xh * y - ch)) - (xl * y - cl2)| ≤ 3 * u p ^ 2 := by
    have := abs_sub (tl2 - ((ch + cl2 - th) + (xh * y - ch))) (xl * y - cl2)
    rw [abs_sub_comm (xl * y) cl2] at this
    linarith
  by_cases hP2 : 2 ≤ xh * y
  · -- `x_h y ≥ 2`: the absolute error `3u²` over `xy ≥ 2 - 2u`
    have hxy2 : 2 - 2 * u p ≤ (xh + xl) * y := by
      have h1 : -u p * y ≤ xl * y := mul_le_mul_of_nonneg_right hxl1 hy0.le
      have h2 : u p * y ≤ u p * 2 := mul_le_mul_of_nonneg_left hy2.le hu.le
      have h3 : (xh + xl) * y = xh * y + xl * y := by ring
      linarith
    have h3 : 3 * u p ^ 2 ≤ (3 / 2 * u p ^ 2 + 4 * u p ^ 3) * (2 - 2 * u p) := by
      have := mul_nonneg (pow_nonneg hu.le 3) (show (0 : ℝ) ≤ 5 - 8 * u p by linarith)
      have e : (3 / 2 * u p ^ 2 + 4 * u p ^ 3) * (2 - 2 * u p) - 3 * u p ^ 2 = u p ^ 3 * (5 - 8 * u p) := by ring
      linarith
    exact habs3.trans (h3.trans (mul_le_mul_of_nonneg_left hxy2 hc0))
  have hP2' := not_le.mp hP2
  -- `x_h y < 2`: `c_h ≤ 2` and `t_h ≤ 2`
  have hth2 : th ≤ 2 := by
    have hch2 : ch ≤ 2 := by
      have := RN_mono p hP2'.le
      rwa [RN_of_F p F2, ← hch] at this
    have h : ch + cl2 ≤ 2 + 2 * u p := by linarith [(abs_le.mp hcl2b).2]
    have h' := RN_mono p h
    have ht := RN_tie p hp1 1
    rw [zpow_one, e1] at ht
    rwa [ht, ← hth] at h'
  by_cases hth_eq : th = 2
  · -- `t_h = 2`: `xy ≥ 2 - 4u - 3u²`
    have hxy : 2 - 4 * u p - 3 * u p ^ 2 ≤ (xh + xl) * y := by
      have hkey : th + tl2 - (xh + xl) * y = (tl2 - ((ch + cl2 - th) + (xh * y - ch))) - (xl * y - cl2) := by ring
      have := (abs_le.mp habs3).2
      have := (abs_le.mp htl2b).1
      linarith
    have h3 : 3 * u p ^ 2 ≤ (3 / 2 * u p ^ 2 + 4 * u p ^ 3) * (2 - 4 * u p - 3 * u p ^ 2) := by
      have := mul_nonneg (pow_nonneg hu.le 3) (show (0 : ℝ) ≤ 2 - 41 / 2 * u p - 12 * u p ^ 2 by linarith)
      have e : (3 / 2 * u p ^ 2 + 4 * u p ^ 3) * (2 - 4 * u p - 3 * u p ^ 2) - 3 * u p ^ 2 =
          u p ^ 3 * (2 - 41 / 2 * u p - 12 * u p ^ 2) := by ring
      linarith
    exact habs3.trans (h3.trans (mul_le_mul_of_nonneg_left hxy hc0))
  -- `t_h < 2`: both errors on a finer grid
  have hcc : ch + cl2 ≤ 2 := by
    by_contra hc
    have := RN_mono p (not_le.mp hc).le
    rw [RN_of_F p F2, ← hth] at this
    exact hth_eq (le_antisymm hth2 this)
  have hE := dwTimesFP1_fine p hp hxh hy hx1 hy1 hch hcl2 hth htl2 hch1 hcl2b he1 hth1 hP2' hcc
  have h3 : 3 / 2 * u p ^ 2 ≤ (3 / 2 * u p ^ 2 + 4 * u p ^ 3) * (1 - u p) := by
    have := mul_nonneg (pow_nonneg hu.le 3) (show (0 : ℝ) ≤ 5 / 2 - 4 * u p by linarith)
    have e : (3 / 2 * u p ^ 2 + 4 * u p ^ 3) * (1 - u p) - 3 / 2 * u p ^ 2 = u p ^ 3 * (5 / 2 - 4 * u p) := by ring
    linarith
  exact hE.trans (h3.trans (mul_le_mul_of_nonneg_left hxy1 hc0))

/-! ### Scaling and signs -/

omit [Prec_gt_0 p] in
theorem twoProd_scale (a b : ℤ) (x y : ℝ) : twoProd p ((2 : ℝ) ^ a * x) ((2 : ℝ) ^ b * y) =
    ((2 : ℝ) ^ (a + b) * (twoProd p x y).1, (2 : ℝ) ^ (a + b) * (twoProd p x y).2) := by
  have e : (2 : ℝ) ^ a * x * ((2 : ℝ) ^ b * y) = (2 : ℝ) ^ (a + b) * (x * y) := by
    rw [zpow_add₀ two_ne_zero]; ring
  unfold twoProd
  simp only [e, RN_zpow_mul, ← mul_sub]

omit [Prec_gt_0 p] in
theorem fastTwoSum_scale (k : ℤ) (a b : ℝ) : fastTwoSum p ((2 : ℝ) ^ k * a) ((2 : ℝ) ^ k * b) =
    ((2 : ℝ) ^ k * (fastTwoSum p a b).1, (2 : ℝ) ^ k * (fastTwoSum p a b).2) := by
  unfold fastTwoSum
  simp only [← mul_add, RN_zpow_mul, ← mul_sub]

theorem twoProd_neg_left (x y : ℝ) : twoProd p (-x) y = (-(twoProd p x y).1, -(twoProd p x y).2) := by
  unfold twoProd
  simp only [neg_mul, RN_neg, sub_neg_eq_add]
  rw [show -(x * y) + RN p (x * y) = -(x * y - RN p (x * y)) by ring, RN_neg]

theorem twoProd_neg_right (x y : ℝ) : twoProd p x (-y) = (-(twoProd p x y).1, -(twoProd p x y).2) := by
  unfold twoProd
  simp only [mul_neg, RN_neg, sub_neg_eq_add]
  rw [show -(x * y) + RN p (x * y) = -(x * y - RN p (x * y)) by ring, RN_neg]

theorem fastTwoSum_neg (a b : ℝ) : fastTwoSum p (-a) (-b) = (-(fastTwoSum p a b).1, -(fastTwoSum p a b).2) := by
  unfold fastTwoSum
  have e1 : -a + -b = -(a + b) := by ring
  simp only [e1, RN_neg]
  rw [show -RN p (a + b) - -a = -(RN p (a + b) - a) by ring, RN_neg,
    show -b - -RN p (RN p (a + b) - a) = -(b - RN p (RN p (a + b) - a)) by ring, RN_neg]

omit [Prec_gt_0 p] in
/-- DWTimesFP1 commutes with scalings by powers of two -/
theorem dwTimesFP1_scale (a b : ℤ) (xh xl y : ℝ) :
    dwTimesFP1 p ((2 : ℝ) ^ a * xh) ((2 : ℝ) ^ a * xl) ((2 : ℝ) ^ b * y) =
      ((2 : ℝ) ^ (a + b) * (dwTimesFP1 p xh xl y).1, (2 : ℝ) ^ (a + b) * (dwTimesFP1 p xh xl y).2) := by
  have e : (2 : ℝ) ^ a * xl * ((2 : ℝ) ^ b * y) = (2 : ℝ) ^ (a + b) * (xl * y) := by
    rw [zpow_add₀ two_ne_zero]; ring
  unfold dwTimesFP1
  simp only [twoProd_scale, e, RN_zpow_mul, fastTwoSum_scale, ← mul_add]

theorem dwTimesFP1_neg_left (xh xl y : ℝ) :
    dwTimesFP1 p (-xh) (-xl) y = (-(dwTimesFP1 p xh xl y).1, -(dwTimesFP1 p xh xl y).2) := by
  unfold dwTimesFP1
  simp only [twoProd_neg_left, neg_mul, RN_neg, fastTwoSum_neg, ← neg_add]

theorem dwTimesFP1_neg_right (xh xl y : ℝ) :
    dwTimesFP1 p xh xl (-y) = (-(dwTimesFP1 p xh xl y).1, -(dwTimesFP1 p xh xl y).2) := by
  unfold dwTimesFP1
  simp only [twoProd_neg_right, mul_neg, RN_neg, fastTwoSum_neg, ← neg_add]

/-! ### Theorem 4.1 of JMP17 -/

/-- `RN x = 0` only at `x = 0` -/
theorem RN_eq_zero {x : ℝ} (h : RN p x = 0) : x = 0 := by
  have h1 := abs_RN_ge p x
  rw [h, abs_zero] at h1
  have hu := u_pos p
  by_contra hx
  have : 0 < |x| / (1 + u p) := div_pos (abs_pos.mpr hx) (by linarith)
  linarith

/-- DWTimesFP1 for positive `x_h` and `y`: the operands scaled into `[1, 2)` -/
theorem dwTimesFP1_pos (hp : 4 ≤ p) {xh xl y : ℝ} (hxh : F p xh) (hy : F p y) (hdw : RN p (xh + xl) = xh)
    (hx0 : 0 < xh) (hy0 : 0 < y) :
    |(dwTimesFP1 p xh xl y).1 + (dwTimesFP1 p xh xl y).2 - (xh + xl) * y| ≤
      (3 / 2 * u p ^ 2 + 4 * u p ^ 3) * ((xh + xl) * y) := by
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hx0 (by norm_num : (1 : ℝ) < 2)
  obtain ⟨m, hm1, hm2⟩ := exists_mem_Ico_zpow hy0 (by norm_num : (1 : ℝ) < 2)
  have ha : (0 : ℝ) < (2 : ℝ) ^ (-n) := by positivity
  have hb : (0 : ℝ) < (2 : ℝ) ^ (-m) := by positivity
  have hab : (0 : ℝ) < (2 : ℝ) ^ (-n + -m) := by positivity
  have s1 : ∀ k : ℤ, (2 : ℝ) ^ (-k) * (2 : ℝ) ^ k = 1 := fun k => by
    rw [← zpow_add₀ two_ne_zero, neg_add_cancel, zpow_zero]
  have s2 : ∀ k : ℤ, (2 : ℝ) ^ (-k) * (2 : ℝ) ^ (k + 1) = 2 := fun k => by
    rw [← zpow_add₀ two_ne_zero, show -k + (k + 1) = 1 by ring, zpow_one]
  have h := dwTimesFP1_norm p hp (F_zpow_mul p (-n) hxh) (F_zpow_mul p (-m) hy)
    (xl := (2 : ℝ) ^ (-n) * xl) (by rw [← mul_add, RN_zpow_mul, hdw])
    (by have := mul_le_mul_of_nonneg_left hn1 ha.le; rwa [s1] at this)
    (by have := mul_lt_mul_of_pos_left hn2 ha; rwa [s2] at this)
    (by have := mul_le_mul_of_nonneg_left hm1 hb.le; rwa [s1] at this)
    (by have := mul_lt_mul_of_pos_left hm2 hb; rwa [s2] at this)
  rw [dwTimesFP1_scale] at h
  have e1 : (2 : ℝ) ^ (-n + -m) * (dwTimesFP1 p xh xl y).1 + (2 : ℝ) ^ (-n + -m) * (dwTimesFP1 p xh xl y).2 -
      ((2 : ℝ) ^ (-n) * xh + (2 : ℝ) ^ (-n) * xl) * ((2 : ℝ) ^ (-m) * y) =
        (2 : ℝ) ^ (-n + -m) * ((dwTimesFP1 p xh xl y).1 + (dwTimesFP1 p xh xl y).2 - (xh + xl) * y) := by
    rw [zpow_add₀ two_ne_zero]; ring
  have e2 : (3 / 2 * u p ^ 2 + 4 * u p ^ 3) * (((2 : ℝ) ^ (-n) * xh + (2 : ℝ) ^ (-n) * xl) * ((2 : ℝ) ^ (-m) * y)) =
      (2 : ℝ) ^ (-n + -m) * ((3 / 2 * u p ^ 2 + 4 * u p ^ 3) * ((xh + xl) * y)) := by
    rw [zpow_add₀ two_ne_zero]; ring
  simp only [] at h
  rw [e1, e2, abs_mul, abs_of_pos hab] at h
  exact le_of_mul_le_mul_left h hab

/-- Theorem 4.1 of JMP17: for `p ≥ 4`, DWTimesFP1 of a double word `(x_h, x_l)` and a float `y` is within
`3u²/2 + 4u³` of `xy`, relatively -/
theorem dwTimesFP1_err (hp : 4 ≤ p) {xh xl y : ℝ} (hxh : F p xh) (hy : F p y) (hdw : RN p (xh + xl) = xh) :
    |(dwTimesFP1 p xh xl y).1 + (dwTimesFP1 p xh xl y).2 - (xh + xl) * y| ≤
      (3 / 2 * u p ^ 2 + 4 * u p ^ 3) * |(xh + xl) * y| := by
  -- a positive `y`, and any `x_h`
  have key : ∀ {xh xl y : ℝ}, F p xh → F p y → RN p (xh + xl) = xh → 0 < y →
      |(dwTimesFP1 p xh xl y).1 + (dwTimesFP1 p xh xl y).2 - (xh + xl) * y| ≤
        (3 / 2 * u p ^ 2 + 4 * u p ^ 3) * |(xh + xl) * y| := by
    intro xh xl y hxh hy hdw hy0
    have hc0 : (0 : ℝ) ≤ 3 / 2 * u p ^ 2 + 4 * u p ^ 3 := by have := u_pos p; positivity
    rcases lt_trichotomy xh 0 with hx | hx | hx
    · -- a negative `x_h`: the result of `-x`, negated
      have h := dwTimesFP1_pos p hp (F_neg p hxh) hy (xl := -xl)
        (by rw [← neg_add, RN_neg, hdw]) (by linarith) hy0
      rw [dwTimesFP1_neg_left] at h
      simp only [] at h
      rw [show -(dwTimesFP1 p xh xl y).1 + -(dwTimesFP1 p xh xl y).2 - (-xh + -xl) * y =
        -((dwTimesFP1 p xh xl y).1 + (dwTimesFP1 p xh xl y).2 - (xh + xl) * y) by ring, abs_neg] at h
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hc0)
      rw [show (-xh + -xl) * y = -((xh + xl) * y) by ring]
      exact neg_le_abs _
    · -- `x_h = 0`: then `x_l = 0`, and every step returns zero
      have hxl : xl = 0 := RN_eq_zero p (by rw [hx, zero_add] at hdw; exact hdw)
      rw [hx, hxl]
      simp [dwTimesFP1, twoProd, fastTwoSum, RN_zero]
    · exact (dwTimesFP1_pos p hp hxh hy hdw hx hy0).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hc0)
  rcases lt_trichotomy y 0 with hy0 | hy0 | hy0
  · have h := key hxh (F_neg p hy) hdw (by linarith : 0 < -y)
    rw [dwTimesFP1_neg_right] at h
    simp only [] at h
    rw [show -(dwTimesFP1 p xh xl y).1 + -(dwTimesFP1 p xh xl y).2 - (xh + xl) * -y =
      -((dwTimesFP1 p xh xl y).1 + (dwTimesFP1 p xh xl y).2 - (xh + xl) * y) by ring, abs_neg,
      show (xh + xl) * -y = -((xh + xl) * y) by ring, abs_neg] at h
    exact h
  · rw [hy0]
    simp [dwTimesFP1, twoProd, fastTwoSum, RN_zero]
  · exact key hxh hy hdw hy0

/-- the result of DWTimesFP1 is a double word, `z_h = RN(z_h + z_l)`: its last Fast2Sum is exact -/
theorem dwTimesFP1_dw (hp : 4 ≤ p) {xh xl y : ℝ} (hxh : F p xh) (hy : F p y) (hdw : RN p (xh + xl) = xh) :
    RN p ((dwTimesFP1 p xh xl y).1 + (dwTimesFP1 p xh xl y).2) = (dwTimesFP1 p xh xl y).1 := by
  -- positive operands, scaled into `[1, 2)`
  have pos : ∀ {xh xl y : ℝ}, F p xh → F p y → RN p (xh + xl) = xh → 0 < xh → 0 < y →
      RN p ((dwTimesFP1 p xh xl y).1 + (dwTimesFP1 p xh xl y).2) = (dwTimesFP1 p xh xl y).1 := by
    intro xh xl y hxh hy hdw hx0 hy0
    obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hx0 (by norm_num : (1 : ℝ) < 2)
    obtain ⟨m, hm1, hm2⟩ := exists_mem_Ico_zpow hy0 (by norm_num : (1 : ℝ) < 2)
    have ha : (0 : ℝ) < (2 : ℝ) ^ (-n) := by positivity
    have hb : (0 : ℝ) < (2 : ℝ) ^ (-m) := by positivity
    have s1 : ∀ k : ℤ, (2 : ℝ) ^ (-k) * (2 : ℝ) ^ k = 1 := fun k => by
      rw [← zpow_add₀ two_ne_zero, neg_add_cancel, zpow_zero]
    have s2 : ∀ k : ℤ, (2 : ℝ) ^ (-k) * (2 : ℝ) ^ (k + 1) = 2 := fun k => by
      rw [← zpow_add₀ two_ne_zero, show -k + (k + 1) = 1 by ring, zpow_one]
    obtain ⟨ch, cl2, th, tl2, -, -, -, -, hsum, hz1, -⟩ := dwTimesFP1_steps p hp (F_zpow_mul p (-n) hxh)
      (F_zpow_mul p (-m) hy) (xl := (2 : ℝ) ^ (-n) * xl) (by rw [← mul_add, RN_zpow_mul, hdw])
      (by have := mul_le_mul_of_nonneg_left hn1 ha.le; rwa [s1] at this)
      (by have := mul_lt_mul_of_pos_left hn2 ha; rwa [s2] at this)
      (by have := mul_le_mul_of_nonneg_left hm1 hb.le; rwa [s1] at this)
      (by have := mul_lt_mul_of_pos_left hm2 hb; rwa [s2] at this)
    have h : RN p ((dwTimesFP1 p ((2 : ℝ) ^ (-n) * xh) ((2 : ℝ) ^ (-n) * xl) ((2 : ℝ) ^ (-m) * y)).1 +
        (dwTimesFP1 p ((2 : ℝ) ^ (-n) * xh) ((2 : ℝ) ^ (-n) * xl) ((2 : ℝ) ^ (-m) * y)).2) =
          (dwTimesFP1 p ((2 : ℝ) ^ (-n) * xh) ((2 : ℝ) ^ (-n) * xl) ((2 : ℝ) ^ (-m) * y)).1 := by
      rw [hsum, hz1]
    rw [dwTimesFP1_scale] at h
    simp only [] at h
    rw [← mul_add, RN_zpow_mul] at h
    exact mul_left_cancel₀ (by positivity) h
  -- a positive `y`, and any `x_h`
  have key : ∀ {xh xl y : ℝ}, F p xh → F p y → RN p (xh + xl) = xh → 0 < y →
      RN p ((dwTimesFP1 p xh xl y).1 + (dwTimesFP1 p xh xl y).2) = (dwTimesFP1 p xh xl y).1 := by
    intro xh xl y hxh hy hdw hy0
    rcases lt_trichotomy xh 0 with hx | hx | hx
    · have h := pos (F_neg p hxh) hy (xl := -xl) (by rw [← neg_add, RN_neg, hdw]) (by linarith) hy0
      rw [dwTimesFP1_neg_left] at h
      simp only [] at h
      rw [← neg_add, RN_neg] at h
      exact neg_injective h
    · have hxl : xl = 0 := RN_eq_zero p (by rw [hx, zero_add] at hdw; exact hdw)
      rw [hx, hxl]
      simp [dwTimesFP1, twoProd, fastTwoSum, RN_zero]
    · exact pos hxh hy hdw hx hy0
  rcases lt_trichotomy y 0 with hy0 | hy0 | hy0
  · have h := key hxh (F_neg p hy) hdw (by linarith : 0 < -y)
    rw [dwTimesFP1_neg_right] at h
    simp only [] at h
    rw [← neg_add, RN_neg] at h
    exact neg_injective h
  · rw [hy0]
    simp [dwTimesFP1, twoProd, fastTwoSum, RN_zero]
  · exact key hxh hy hdw hy0

end ExpansionBounds
