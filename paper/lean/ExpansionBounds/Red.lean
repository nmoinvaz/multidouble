import ExpansionBounds.ExpRed
import ExpansionBounds.Sharp
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Lemma 32: RED

RED takes `k = ⌊RN(x_0c)⌉` with `c = RN(2/π)`, forms `v = 2^{-F}(2^F∑x_i - kP)` with `P = ⌊2^Fπ/2⌉` and `F = 1216`,
corrects `k` once by `k_2 = ⌊RN(RN(v)c)⌉` if `|RN(v)| > r_max = RN(0.7854)`, and returns `q = k mod 4` and the greedy
rounding `r` of `v` to `n` parts, or `q = 0` and `r = x` if the first `k` is zero; the final `k` is then zero, and under
`H(2)` with `|x_0| ≤ 2^52` only then. With an unbounded exponent range the greedy rounding loses at most `ū^n|v|`
whatever the sizes, so the hypothesis `|r_e| ≥ 2^{pn-1074}` of the paper is not needed, and `v` is formed exactly as a
real number. The model has no `ulp`, so the greedy parts' `|r_{i+1}| ≤ ½ulp(r_i)` of the paper is replaced by its
consequence `|r_{i+1}| ≤ u|r_i|`, which gives `H(1)`.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) (n : ℕ)

/-- the remainders of the greedy rounding: `v_0 = v` and `v_{i+1} = v_i - RN(v_i)` -/
noncomputable def greedyRem (v : ℝ) : ℕ → ℝ
  | 0 => v
  | i + 1 => greedyRem v i - RN p (greedyRem v i)

/-- the greedy rounding of `v` to parts: `r_i = RN(v - ∑_{l<i} r_l)` -/
noncomputable def greedy (v : ℝ) (i : ℕ) : ℝ := RN p (greedyRem p v i)


/-- `P = ⌊2^Fπ/2⌉` with `F = 1216` -/
noncomputable def redP : ℤ := roundAway ((2 : ℝ) ^ (1216 : ℕ) * (Real.pi / 2))

/-- `c = RN(2/π)` -/
noncomputable def redC : ℝ := RN p (2 / Real.pi)

/-- `r_max = RN(0.7854)` -/
noncomputable def redRmax : ℝ := RN p (7854 / 10000)

/-- `v = 2^{-F}(2^F∑x_i - kP)` -/
noncomputable def redV (x : ℕ → ℝ) (k : ℤ) : ℝ := ∑ i ∈ range n, x i - k * ((redP : ℝ) * (2 : ℝ) ^ (-1216 : ℤ))

/-- the first `k = ⌊RN(x_0c)⌉` -/
noncomputable def redK1 (x : ℕ → ℝ) : ℤ := roundAway (RN p (x 0 * redC p))

/-- the correction `k_2 = ⌊RN(RN(v)c)⌉` when `|RN(v)| > r_max`, zero otherwise -/
noncomputable def redK2 (x : ℕ → ℝ) : ℤ :=
  if redRmax p < |RN p (redV n x (redK1 p x))| then roundAway (RN p (RN p (redV n x (redK1 p x)) * redC p)) else 0

/-- the final `k`, zero when the first one is -/
noncomputable def redK (x : ℕ → ℝ) : ℤ := if redK1 p x = 0 then 0 else redK1 p x + redK2 p n x

/-- RED's `r`: `x` when the first `k` is zero, the greedy rounding of `v` to `n` parts otherwise; under `H(2)` with
`|x_0| ≤ 2^52` the first `k` is zero exactly when the final one is (Lemma 32) -/
noncomputable def redR (x : ℕ → ℝ) : ℕ → ℝ :=
  if redK1 p x = 0 then x else fun i => if i < n then greedy p (redV n x (redK p n x)) i else 0

/-- RED's `q = k mod 4` -/
noncomputable def redQ (x : ℕ → ℝ) : ℤ := redK p n x % 4

theorem greedy_sum (v : ℝ) : ∀ N, ∑ i ∈ range N, greedy p v i = v - greedyRem p v N
  | 0 => by simp [greedyRem]
  | N + 1 => by rw [sum_range_succ, greedy_sum v N, greedyRem, greedy]; ring

variable [Prec_gt_0 p]

theorem greedyRem_le (v : ℝ) : ∀ N, |greedyRem p v N| ≤ us p ^ N * |v|
  | 0 => by simp [greedyRem]
  | N + 1 => by
    have h := abs_RN_sub_le_us p (greedyRem p v N)
    rw [abs_sub_comm] at h
    calc |greedyRem p v (N + 1)| ≤ us p * |greedyRem p v N| := h
      _ ≤ us p * (us p ^ N * |v|) := mul_le_mul_of_nonneg_left (greedyRem_le v N) (us_nonneg p)
      _ = us p ^ (N + 1) * |v| := by ring

/-- `|RN(y)| ≤ c` for `|y| ≤ c ∈ F` -/
theorem abs_RN_le_of_F {y c : ℝ} (hc : F p c) (hy : |y| ≤ c) : |RN p y| ≤ c := by
  have h1 := RN_mono p (abs_le.mp hy).1
  have h2 := RN_mono p (abs_le.mp hy).2
  rw [RN_neg, RN_of_F p hc] at h1
  rw [RN_of_F p hc] at h2
  exact abs_le.mpr ⟨h1, h2⟩

theorem F_abs {x : ℝ} (hx : F p x) : F p |x| := by
  rcases abs_choice x with h | h <;> rw [h]
  · exact hx
  · exact F_neg p hx

/-- the greedy parts fall by `u` at least: `|r_{i+1}| ≤ u|r_i|`, so they satisfy `H(1)` -/
theorem greedy_succ_le (v : ℝ) (i : ℕ) : |greedy p v (i + 1)| ≤ u p * |greedy p v i| := by
  have h1 : |greedyRem p v (i + 1)| ≤ u p * |greedy p v i| := by
    show |greedyRem p v i - RN p (greedyRem p v i)| ≤ _
    rw [abs_sub_comm]
    exact abs_RN_sub_le_u_RN p _
  have hF : F p (u p * |greedy p v i|) := by
    have := F_zpow_mul p (-p) (F_abs p (F_RN p (greedyRem p v i)))
    simpa [u, greedy] using this
  exact abs_RN_le_of_F p hF h1

/-- the error of `RN` on a grid: `|RN(z) - z| ≤ 2^E/2` when the multiple of `2^E` nearest `z` is in `F` -/
theorem RN_err_grid {E : ℤ} {z : ℝ} (hz : |z| + (2 : ℝ) ^ E / 2 < (2 : ℝ) ^ (E + p)) :
    |RN p z - z| ≤ (2 : ℝ) ^ E / 2 := by
  have hE : 0 < (2 : ℝ) ^ E := by positivity
  set f : ℝ := (roundAway (z / (2 : ℝ) ^ E) : ℝ) * (2 : ℝ) ^ E with hf
  have hfz : |f - z| ≤ (2 : ℝ) ^ E / 2 := by
    have h := roundAway_sub (z / (2 : ℝ) ^ E)
    rw [show f - z = ((roundAway (z / (2 : ℝ) ^ E) : ℝ) - z / (2 : ℝ) ^ E) * (2 : ℝ) ^ E by
      rw [hf]; field_simp, abs_mul, abs_of_pos hE]
    calc _ ≤ 1 / 2 * (2 : ℝ) ^ E := mul_le_mul_of_nonneg_right h hE.le
      _ = _ := by ring
  have hfF : F p f := by
    refine F_of_mult p ⟨roundAway (z / (2 : ℝ) ^ E), rfl⟩ ?_
    calc |f| ≤ |z| + |f - z| := by
          have := abs_add_le z (f - z)
          rwa [add_sub_cancel] at this
      _ ≤ |z| + (2 : ℝ) ^ E / 2 := by linarith
      _ < _ := hz
  exact ((RN_nearest p z).2 f hfF).trans hfz

theorem roundAway_eq_zero {y : ℝ} (h : roundAway y = 0) : |y| < 1 / 2 := by
  unfold roundAway at h
  split_ifs at h with hy
  · rw [abs_of_nonneg hy]
    have := Int.lt_floor_add_one (y + 1 / 2)
    rw [h] at this
    push_cast at this
    linarith
  · push Not at hy
    rw [abs_of_neg hy]
    have h' : ⌊-y + 1 / 2⌋ = 0 := by omega
    have := Int.lt_floor_add_one (-y + 1 / 2)
    rw [h'] at this
    push_cast at this
    linarith

omit [Prec_gt_0 p] in
/-- `P2^{-F}` is within `2^{-F-1}` of `π/2` -/
theorem redP_err : |(redP : ℝ) * (2 : ℝ) ^ (-1216 : ℤ) - Real.pi / 2| ≤ (2 : ℝ) ^ (-1217 : ℤ) := by
  have h := roundAway_sub ((2 : ℝ) ^ (1216 : ℕ) * (Real.pi / 2))
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-1216 : ℤ) := by positivity
  have he : (2 : ℝ) ^ (-1216 : ℤ) * (2 : ℝ) ^ (1216 : ℕ) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]; norm_num
  calc |(redP : ℝ) * (2 : ℝ) ^ (-1216 : ℤ) - Real.pi / 2| =
        (2 : ℝ) ^ (-1216 : ℤ) * |(redP : ℝ) - (2 : ℝ) ^ (1216 : ℕ) * (Real.pi / 2)| := by
        rw [← abs_of_pos hpos, ← abs_mul, abs_of_pos hpos]
        congr 1
        rw [mul_sub, ← mul_assoc, he, one_mul, mul_comm]
    _ ≤ (2 : ℝ) ^ (-1216 : ℤ) * (1 / 2) := mul_le_mul_of_nonneg_left h hpos.le
    _ = (2 : ℝ) ^ (-1217 : ℤ) := by
        rw [show (-1217 : ℤ) = -1216 + -1 by norm_num, zpow_add₀ (by norm_num)]; norm_num

/-- `c = RN(2/π)` is within `2^{-54}` of `2/π` at `p = 53` -/
theorem redC_err (hp : p = 53) : |redC p - 2 / Real.pi| ≤ (2 : ℝ) ^ (-54 : ℤ) := by
  have hpi := Real.pi_gt_d6
  have h := RN_err_grid p (E := -53) (z := 2 / Real.pi) (by
    have h2 : 2 / Real.pi < 64 / 100 := by rw [div_lt_iff₀ (by positivity)]; nlinarith
    rw [hp, abs_of_pos (by positivity)]
    norm_num
    linarith)
  rw [show (2 : ℝ) ^ (-54 : ℤ) = (2 : ℝ) ^ (-53 : ℤ) / 2 by
    rw [show (-54 : ℤ) = -53 + -1 by norm_num, zpow_add₀ (by norm_num)]; norm_num]
  exact h

/-- `r_max = RN(0.7854)` is within `2^{-54}` of `0.7854` at `p = 53` -/
theorem redRmax_err (hp : p = 53) : |redRmax p - 7854 / 10000| ≤ (2 : ℝ) ^ (-54 : ℤ) := by
  have h := RN_err_grid p (E := -53) (z := 7854 / 10000) (by rw [hp]; norm_num)
  rw [show (2 : ℝ) ^ (-54 : ℤ) = (2 : ℝ) ^ (-53 : ℤ) / 2 by
    rw [show (-54 : ℤ) = -53 + -1 by norm_num, zpow_add₀ (by norm_num)]; norm_num]
  exact h

/-- the estimate of `k`: `|RN(yc) - 2Y/π| ≤ u|y||c| + |y||c - 2/π| + (2/π)|y - Y|` -/
theorem red_est (y Y : ℝ) : |RN p (y * redC p) - 2 / Real.pi * Y| ≤
    u p * (|y| * |redC p|) + |y| * |redC p - 2 / Real.pi| + 2 / Real.pi * |y - Y| := by
  have h1 : |RN p (y * redC p) - y * redC p| ≤ u p * (|y| * |redC p|) := by
    rw [← abs_mul]; exact (abs_RN_sub_le_us p _).trans (mul_le_mul_of_nonneg_right (us_le_u p) (abs_nonneg _))
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsplit : RN p (y * redC p) - 2 / Real.pi * Y =
      (RN p (y * redC p) - y * redC p) + y * (redC p - 2 / Real.pi) + 2 / Real.pi * (y - Y) := by ring
  rw [hsplit]
  calc _ ≤ |RN p (y * redC p) - y * redC p| + |y * (redC p - 2 / Real.pi)| + |2 / Real.pi * (y - Y)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by
        rw [abs_mul y, abs_mul (2 / Real.pi), abs_of_pos (by positivity : 0 < 2 / Real.pi)]
        linarith

omit [Prec_gt_0 p] in
theorem redV_add (x : ℕ → ℝ) (k1 k2 : ℤ) :
    redV n x (k1 + k2) = redV n x k1 - k2 * ((redP : ℝ) * (2 : ℝ) ^ (-1216 : ℤ)) := by
  unfold redV; push_cast; ring

omit [Prec_gt_0 p] in
/-- `v - r_e = -k(P2^{-F} - π/2)`, within `E_π = |k|2^{-1217}` -/
theorem redV_err (x : ℕ → ℝ) (k : ℤ) :
    |redV n x k - (∑ i ∈ range n, x i - k * (Real.pi / 2))| ≤ |(k : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ) := by
  rw [show redV n x k - (∑ i ∈ range n, x i - k * (Real.pi / 2)) =
    -((k : ℝ) * ((redP : ℝ) * (2 : ℝ) ^ (-1216 : ℤ) - Real.pi / 2)) by unfold redV; ring, abs_neg, abs_mul]
  exact mul_le_mul_of_nonneg_left (redP_err) (abs_nonneg _)

/-- Lemma 32 for `k` and `v`, at `p = 53` and `|x_0| ≤ 2^52` on `H(2)`: `|k| < 0.64·2^52`; if the first `k` is zero
so is the last, `r = x` and `|x| ≤ 0.785399`; otherwise `k ≠ 0` and `|v| ≤ (1 + u)r_max` -/
theorem lemma32_k (hp : p = 53) (hn : 1 ≤ n) (x : ℕ → ℝ) (hH : Htheta p n 2 x) (hx0 : |x 0| ≤ 2 ^ 52) :
    |(redK p n x : ℝ)| < 64 / 100 * 2 ^ 52 ∧
      (redK1 p x = 0 → redK p n x = 0 ∧ redR p n x = x ∧ |∑ i ∈ range n, x i| ≤ 785399 / 1000000) ∧
      (redK1 p x ≠ 0 → redK p n x ≠ 0 ∧ |redV n x (redK p n x)| ≤ (1 + u p) * redRmax p) := by
  have hu : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num
  have hus := us_le_u p
  have hπ1 := Real.pi_gt_d20
  have hπ2 := Real.pi_lt_d20
  have hπ0 := Real.pi_pos
  have hc := redC_err p hp
  have hrm := redRmax_err p hp
  have h54 : (2 : ℝ) ^ (-54 : ℤ) = 1 / 18014398509481984 := by norm_num
  have h1217 : (2 : ℝ) ^ (-1217 : ℤ) ≤ 1 / 2 ^ 200 := by
    rw [zpow_neg, ← one_div, one_div_le_one_div (by positivity) (by positivity)]
    exact_mod_cast pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : 200 ≤ 1217)
  rw [h54] at hc hrm
  have h2pi_lo : 6366197723675813 / 10000000000000000 < 2 / Real.pi := by
    rw [lt_div_iff₀ hπ0]; nlinarith
  have h2pi_hi : 2 / Real.pi < 6366197723675814 / 10000000000000000 := by
    rw [div_lt_iff₀ hπ0]; nlinarith
  have hc_hi : |redC p| ≤ 63662 / 100000 := by
    have := abs_sub_abs_le_abs_sub (redC p) (2 / Real.pi)
    rw [abs_of_pos (by positivity : 0 < 2 / Real.pi)] at this
    linarith
  have hc_lo : 6366197723675812 / 10000000000000000 ≤ |redC p| := by
    have := abs_sub_abs_le_abs_sub (2 / Real.pi) (redC p)
    rw [abs_of_pos (by positivity : 0 < 2 / Real.pi), abs_sub_comm] at this
    linarith
  set X := ∑ i ∈ range n, x i with hXd
  set a := |x 0| with ha
  have ha0 : 0 ≤ a := abs_nonneg _
  have hXx : |X - x 0| ≤ 2 * u p / (1 - 2 * u p) * a :=
    Htheta_tail p n hn 2 (by norm_num) (by rw [hu]; norm_num) x hH
  rw [hu] at hXx
  norm_num at hXx
  -- the estimate of the first `k`
  set c := redC p with hcd
  have hE1 : |RN p (x 0 * c) - 2 / Real.pi * X| ≤ a * (121 / 100 / 2 ^ 52) := by
    have h := red_est p (x 0) X
    rw [← ha, abs_sub_comm (x 0)] at h
    have t1 : u p * (a * |c|) ≤ 1 / 9007199254740992 * (a * (63662 / 100000)) := by
      rw [hu]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc_hi ha0) (by norm_num)
    have t2 : a * |c - 2 / Real.pi| ≤ a * (1 / 18014398509481984) := mul_le_mul_of_nonneg_left hc ha0
    have t3 : 2 / Real.pi * |X - x 0| ≤ 6366197723675814 / 10000000000000000 * |X - x 0| :=
      mul_le_mul_of_nonneg_right h2pi_hi.le (abs_nonneg _)
    nlinarith
  -- the first `k` and `v`
  have hu1 : (0 : ℝ) ≤ 1 + u p := by rw [hu]; norm_num
  set k1 := redK1 p x with hk1d
  have hk1r : |(k1 : ℝ) - RN p (x 0 * c)| ≤ 1 / 2 := roundAway_sub _
  have hRNx : |RN p (x 0 * c)| ≤ (1 + 1 / 9007199254740992) * (a * (63662 / 100000)) := by
    rw [← hu]
    refine (abs_RN_le p _).trans (mul_le_mul_of_nonneg_left ?_ hu1)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hc_hi ha0
  have hk1b : |(k1 : ℝ)| ≤ (1 + 1 / 9007199254740992) * (a * (63662 / 100000)) + 1 / 2 := by
    have := abs_sub_abs_le_abs_sub (k1 : ℝ) (RN p (x 0 * c))
    linarith
  set PP := (redP : ℝ) * (2 : ℝ) ^ (-1216 : ℤ) with hPP
  have hPe : |PP - Real.pi / 2| ≤ (2 : ℝ) ^ (-1217 : ℤ) := redP_err
  set v1 := redV n x k1 with hv1
  have hv1e := redV_err n x k1
  rw [← hv1] at hv1e
  have hre1 : |X - k1 * (Real.pi / 2)| ≤ Real.pi / 2 * (a * (121 / 100 / 2 ^ 52) + 1 / 2) := by
    rw [show X - k1 * (Real.pi / 2) = Real.pi / 2 * ((2 / Real.pi * X - RN p (x 0 * c)) + (RN p (x 0 * c) - k1)) by
      field_simp; ring, abs_mul, abs_of_pos (by positivity)]
    refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add ?_ ?_)) (by positivity)
    · rw [abs_sub_comm]; exact hE1
    · rw [abs_sub_comm]; exact hk1r
  have hv1b : |v1| ≤ Real.pi / 2 * (a * (121 / 100 / 2 ^ 52) + 1 / 2) + |(k1 : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ) := by
    have := abs_sub_abs_le_abs_sub v1 (X - k1 * (Real.pi / 2))
    linarith
  have hrmF : F p (redRmax p) := F_RN p _
  have hrm_lo : 7854 / 10000 - 1 / 18014398509481984 ≤ redRmax p := by linarith [(abs_le.mp hrm).1]
  have hrm_hi : redRmax p ≤ 7854 / 10000 + 1 / 18014398509481984 := by linarith [(abs_le.mp hrm).2]
  have hk1e : |(k1 : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ) ≤ 2 ^ 52 * (1 / 2 ^ 200) := by
    have : |(k1 : ℝ)| ≤ 2 ^ 52 := by
      have := mul_le_mul_of_nonneg_right hx0 (by norm_num : (0 : ℝ) ≤ 63662 / 100000)
      linarith
    exact mul_le_mul this h1217 (by positivity) (by positivity)
  have hpa : Real.pi / 2 * (a * (121 / 100 / 2 ^ 52) + 1 / 2) ≤ Real.pi / 2 * (2 ^ 52 * (121 / 100 / 2 ^ 52) + 1 / 2) :=
    mul_le_mul_of_nonneg_left (by gcongr) (by positivity)
  have hv27 : |v1| ≤ 27 / 10 := by linarith
  have hk0' : redK1 p x = k1 := rfl
  by_cases hk0 : k1 = 0
  · -- `k = 0`: `r = x` and `|x| ≤ 0.785399`
    have hk : redK p n x = 0 := by simp only [redK, hk0', hk0, ite_true]
    have hr : redR p n x = x := by simp only [redR, hk0', hk0, ite_true]
    have hlt : |RN p (x 0 * c)| < 1 / 2 := roundAway_eq_zero (by rw [← hk0]; rfl)
    have hge := abs_RN_ge p (x 0 * c)
    rw [abs_mul, ← ha, div_le_iff₀ (by linarith), hu] at hge
    have hac : a * (6366197723675812 / 10000000000000000) ≤ a * |c| := mul_le_mul_of_nonneg_left hc_lo ha0
    have hX : |X| ≤ a + |X - x 0| := by
      have := abs_sub_abs_le_abs_sub X (x 0)
      linarith
    refine ⟨by rw [hk]; norm_num, fun _ => ⟨hk, hr, by linarith⟩, fun h => absurd hk0 h⟩
  · by_cases hB : redRmax p < |RN p v1|
    · -- the correction: `|x_0| > 2^{31}`, so `|k_1| ≥ 3`, and `|k_2| ≤ 2`
      have ha31 : 2 ^ 31 < a := by
        by_contra hc31
        push Not at hc31
        have hk1s : |(k1 : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ) ≤ 2 ^ 31 * (1 / 2 ^ 200) := by
          have : |(k1 : ℝ)| ≤ 2 ^ 31 := by
            have := mul_le_mul_of_nonneg_right hc31 (by norm_num : (0 : ℝ) ≤ 63662 / 100000)
            linarith
          exact mul_le_mul this h1217 (by positivity) (by positivity)
        have h1 : Real.pi / 2 * (a * (121 / 100 / 2 ^ 52) + 1 / 2) ≤
            Real.pi / 2 * (2 ^ 31 * (121 / 100 / 2 ^ 52) + 1 / 2) :=
          mul_le_mul_of_nonneg_left (by gcongr) (by positivity)
        have hv : |v1| ≤ redRmax p := by linarith
        have := abs_RN_le_of_F p hrmF hv
        linarith
      have hge := abs_RN_ge p (x 0 * c)
      rw [abs_mul, ← ha, div_le_iff₀ (by linarith), hu] at hge
      have hac : 2 ^ 31 * (6366197723675812 / 10000000000000000) ≤ a * |c| :=
        (mul_le_mul_of_nonneg_right ha31.le (by norm_num)).trans (mul_le_mul_of_nonneg_left hc_lo ha0)
      have hk1l : 3 ≤ |(k1 : ℝ)| := by
        have := abs_sub_abs_le_abs_sub (RN p (x 0 * c)) (k1 : ℝ)
        rw [abs_sub_comm (RN p (x 0 * c))] at this
        linarith
      -- the second estimate
      have hE2 := red_est p (RN p v1) v1
      have hRv : |RN p v1| ≤ (1 + u p) * (27 / 10) := (abs_RN_le p v1).trans (mul_le_mul_of_nonneg_left hv27 hu1)
      have hRv1 : |RN p v1 - v1| ≤ u p * (27 / 10) :=
        (abs_RN_sub_le_us p v1).trans (mul_le_mul hus hv27 (abs_nonneg _) (u_pos p).le)
      rw [abs_sub_comm (RN p v1)] at hE2
      have hE2' : |RN p (RN p v1 * c) - 2 / Real.pi * v1| ≤ 5 * u p := by
        have t1 : u p * (|RN p v1| * |c|) ≤ u p * ((1 + u p) * (27 / 10) * (63662 / 100000)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hRv hc_hi (abs_nonneg _) (by rw [hu]; norm_num)) (u_pos p).le
        have t2 : |RN p v1| * |c - 2 / Real.pi| ≤ (1 + u p) * (27 / 10) * (1 / 18014398509481984) :=
          mul_le_mul hRv hc (abs_nonneg _) (by rw [hu]; norm_num)
        have t3 : 2 / Real.pi * |v1 - RN p v1| ≤ 6366197723675814 / 10000000000000000 * (u p * (27 / 10)) := by
          rw [abs_sub_comm]
          exact mul_le_mul h2pi_hi.le hRv1 (abs_nonneg _) (by norm_num)
        rw [hu] at t1 t2 t3 hE2 ⊢
        linarith
      set k2 := roundAway (RN p (RN p v1 * c)) with hk2d
      have hk2r : |(k2 : ℝ) - RN p (RN p v1 * c)| ≤ 1 / 2 := roundAway_sub _
      have hk2d' : |2 / Real.pi * v1 - k2| ≤ 1 / 2 + 5 * u p := by
        have := abs_sub_le (2 / Real.pi * v1) (RN p (RN p v1 * c)) (k2 : ℝ)
        rw [abs_sub_comm _ (RN p (RN p v1 * c))] at this
        rw [abs_sub_comm] at hk2r
        linarith
      have hk2R : |(k2 : ℝ)| ≤ 2 := by
        have h1 : |(k2 : ℝ)| < 3 := by
          have h2 : |2 / Real.pi * v1| ≤ 6366197723675814 / 10000000000000000 * (27 / 10) := by
            rw [abs_mul, abs_of_pos (by positivity)]
            exact mul_le_mul h2pi_hi.le hv27 (abs_nonneg _) (by norm_num)
          have := abs_sub_abs_le_abs_sub (k2 : ℝ) (2 / Real.pi * v1)
          rw [abs_sub_comm (k2 : ℝ)] at this
          rw [hu] at hk2d'
          linarith
        have h3 : |k2| < 3 := by exact_mod_cast h1
        have h4 : |k2| ≤ 2 := by omega
        exact_mod_cast h4
      have hk2' : redK2 p n x = k2 := by
        simp only [redK2, hk0', ← hv1, hB, ite_true, ← hk2d, ← hcd]
      have hk : redK p n x = k1 + k2 := by simp only [redK, hk0', hk0, ite_false, hk2']
      rw [hk]
      have hkR : |((k1 + k2 : ℤ) : ℝ)| ≤ |(k1 : ℝ)| + 2 := by
        push_cast
        exact (abs_add_le _ _).trans (by linarith)
      refine ⟨by linarith, fun h => absurd h hk0, fun _ => ⟨?_, ?_⟩⟩
      · intro h
        have h1 : ((k1 + k2 : ℤ) : ℝ) = 0 := by exact_mod_cast h
        push_cast at h1
        have h2 : (k1 : ℝ) = -k2 := by linarith
        rw [h2, abs_neg] at hk1l
        linarith
      · rw [redV_add, ← hv1, ← hPP]
        have hsplit : v1 - k2 * PP = Real.pi / 2 * (2 / Real.pi * v1 - k2) - k2 * (PP - Real.pi / 2) := by
          field_simp; ring
        rw [hsplit]
        have h1 : |Real.pi / 2 * (2 / Real.pi * v1 - k2)| ≤ Real.pi / 2 * (1 / 2 + 5 * (1 / 9007199254740992)) := by
          rw [abs_mul, abs_of_pos (by positivity), ← hu]; exact mul_le_mul_of_nonneg_left hk2d' (by positivity)
        have h2 : |(k2 : ℝ) * (PP - Real.pi / 2)| ≤ 2 * (1 / 2 ^ 200) := by
          rw [abs_mul]; exact mul_le_mul hk2R (hPe.trans h1217) (abs_nonneg _) (by norm_num)
        have h3 := abs_sub (Real.pi / 2 * (2 / Real.pi * v1 - k2)) ((k2 : ℝ) * (PP - Real.pi / 2))
        have h4 : 0 ≤ u p * redRmax p := mul_nonneg (u_pos p).le (by linarith)
        rw [hu] at h4 ⊢
        linarith
    · -- no correction
      push Not at hB
      have hk2' : redK2 p n x = 0 := by simp only [redK2, hk0', ← hv1, not_lt.mpr hB, ite_false]
      have hk : redK p n x = k1 := by simp only [redK, hk0', hk0, ite_false, hk2', add_zero]
      rw [hk]
      refine ⟨by linarith, fun h => absurd h hk0, fun _ => ⟨hk0, ?_⟩⟩
      rw [← hv1]
      have := abs_RN_ge p v1
      rw [div_le_iff₀ (by linarith)] at this
      calc |v1| ≤ |RN p v1| * (1 + u p) := this
        _ ≤ redRmax p * (1 + u p) := mul_le_mul_of_nonneg_right hB hu1
        _ = (1 + u p) * redRmax p := by ring

/-- Lemma 32 for `r`: in `F` and on `H(2)`; with `k ≠ 0` it is the greedy rounding of `v`, with `|r| ≤ r̄_0 = 0.78541`,
`|r_{i+1}| ≤ u|r_i|` and `|r - r_e| ≤ ū^n|r_e| + 2E_π`, and with `k = 0` it is `x = r_e` -/
theorem lemma32_r (hp : p = 53) (hn : 1 ≤ n) (x : ℕ → ℝ) (hx : ∀ i < n, F p (x i)) (hH : Htheta p n 2 x)
    (hx0 : |x 0| ≤ 2 ^ 52) :
    (∀ i < n, F p (redR p n x i)) ∧ Htheta p n 2 (redR p n x) ∧
      |∑ i ∈ range n, redR p n x i| ≤ 78541 / 100000 ∧
      |∑ i ∈ range n, redR p n x i - (∑ i ∈ range n, x i - redK p n x * (Real.pi / 2))| ≤
        us p ^ n * |∑ i ∈ range n, x i - redK p n x * (Real.pi / 2)| +
          2 * (|(redK p n x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) ∧
      (redK1 p x ≠ 0 → ∀ i, i + 1 < n → |redR p n x (i + 1)| ≤ u p * |redR p n x i|) := by
  have hu : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num
  have hus := us_le_u p
  have hus0 := us_nonneg p
  obtain ⟨-, ha, hb⟩ := lemma32_k p n hp hn x hH hx0
  set k := redK p n x with hk
  set re := ∑ i ∈ range n, x i - k * (Real.pi / 2) with hre
  have hEπ : 0 ≤ |(k : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ) := by positivity
  have husn : us p ^ n ≤ u p := by
    calc us p ^ n ≤ us p ^ 1 := pow_le_pow_of_le_one hus0 (by rw [hu] at hus; linarith) hn
      _ = us p := pow_one _
      _ ≤ u p := hus
  have husn1 : us p ^ n ≤ 1 := husn.trans (by rw [hu]; norm_num)
  by_cases hk0 : redK1 p x = 0
  · obtain ⟨hk', hr, hX⟩ := ha hk0
    rw [hr]
    refine ⟨hx, hH, by linarith, ?_, fun h => absurd hk0 h⟩
    have hre0 : re = ∑ i ∈ range n, x i := by rw [hre, hk', Int.cast_zero, zero_mul, sub_zero]
    rw [hre0, sub_self, abs_zero]
    positivity
  · obtain ⟨-, hv⟩ := hb hk0
    set v := redV n x k with hvd
    have hr : redR p n x = fun i => if i < n then greedy p v i else 0 := by
      simp only [redR, hk0, ite_false]
      rfl
    rw [hr]
    have hsum : ∑ i ∈ range n, (if i < n then greedy p v i else 0) = v - greedyRem p v n := by
      rw [← greedy_sum p v n]
      exact sum_congr rfl fun i hi => by simp [mem_range.mp hi]
    have hrem := greedyRem_le p v n
    have hve := redV_err n x k
    rw [← hvd] at hve
    have hrm := redRmax_err p hp
    have h54 : (2 : ℝ) ^ (-54 : ℤ) = 1 / 18014398509481984 := by norm_num
    rw [h54] at hrm
    have hrm_hi : redRmax p ≤ 7854 / 10000 + 1 / 18014398509481984 := by linarith [(abs_le.mp hrm).2]
    have hsucc : ∀ i, i + 1 < n → |(if i + 1 < n then greedy p v (i + 1) else 0)| ≤
        u p * |(if i < n then greedy p v i else 0)| := fun i hi => by
      simp only [hi, show i < n by omega, ite_true]
      exact greedy_succ_le p v i
    refine ⟨fun i hi => by simp only [hi, ite_true]; exact F_RN p _, fun i hi1 hin => ?_, ?_, ?_, fun _ => hsucc⟩
    · -- `|r_i| ≤ u^i|r_0| ≤ (2u)^i|r_0|`
      have hpow : ∀ m, m < n →
          |(if m < n then greedy p v m else 0)| ≤ u p ^ m * |(if 0 < n then greedy p v 0 else 0)| := by
        intro m
        induction m with
        | zero => intro _; simp
        | succ m ih =>
          intro hm
          calc _ ≤ u p * |(if m < n then greedy p v m else 0)| := hsucc m hm
            _ ≤ u p * (u p ^ m * |(if 0 < n then greedy p v 0 else 0)|) :=
                mul_le_mul_of_nonneg_left (ih (by omega)) (u_pos p).le
            _ = _ := by ring
      refine (hpow i hin).trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
      exact pow_le_pow_left₀ (u_pos p).le (by linarith [u_pos p]) i
    · rw [hsum]
      have h1 : |v - greedyRem p v n| ≤ |v| + u p * |v| := by
        have := abs_sub v (greedyRem p v n)
        have h2 : us p ^ n * |v| ≤ u p * |v| := mul_le_mul_of_nonneg_right husn (abs_nonneg _)
        linarith
      have h3 : |v| + u p * |v| ≤ (1 + u p) * ((1 + u p) * redRmax p) := by
        rw [show |v| + u p * |v| = (1 + u p) * |v| by ring]
        exact mul_le_mul_of_nonneg_left hv (by linarith [u_pos p])
      rw [hu] at h3
      nlinarith
    · rw [hsum]
      have h1 : |v - greedyRem p v n - re| ≤ |greedyRem p v n| + |v - re| := by
        rw [show v - greedyRem p v n - re = -(greedyRem p v n) + (v - re) by ring]
        exact (abs_add_le _ _).trans (by rw [abs_neg])
      have h2 : |v| ≤ |re| + |(k : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ) := by
        have := abs_sub_abs_le_abs_sub v re
        linarith
      have h3 : us p ^ n * |v| ≤ us p ^ n * |re| + |(k : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ) := by
        calc us p ^ n * |v| ≤ us p ^ n * (|re| + |(k : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) :=
              mul_le_mul_of_nonneg_left h2 (pow_nonneg hus0 n)
          _ ≤ us p ^ n * |re| + 1 * (|(k : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) := by
              rw [mul_add]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_right husn1 hEπ)
          _ = _ := by ring
      linarith

omit [Prec_gt_0 p] in
/-- below a power of two, an element of `F` at `p = 53` is at most its predecessor: `|r| ≤ 2^m(1 - u)` -/
theorem F_lt_zpow (hp : p = 53) {r : ℝ} (hr : F p r) (m : ℤ) (h : |r| < (2 : ℝ) ^ m) :
    |r| ≤ (2 : ℝ) ^ m * (1 - u p) := by
  have hu : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num
  have hm : (2 : ℝ) ^ m = (2 : ℝ) ^ (m - 53) * 2 ^ (53 : ℤ) := by rw [← zpow_add₀ two_ne_zero]; ring_nf
  have hm1 : (2 : ℝ) ^ m = 2 * (2 : ℝ) ^ (m - 1) := by
    rw [show m = (m - 1) + 1 by ring, zpow_add₀ two_ne_zero, zpow_one]; ring_nf
  by_cases h1 : |r| < (2 : ℝ) ^ (m - 1)
  · rw [hu]
    have : (0 : ℝ) < (2 : ℝ) ^ (m - 1) := by positivity
    nlinarith
  · push Not at h1
    obtain ⟨j, hj⟩ := mult_of_F p hr (E := m - 53) (by rw [hp]; ring_nf; ring_nf at h1; exact h1)
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (m - 53) := by positivity
    rw [hj, abs_mul, abs_of_pos hpos] at h ⊢
    have hj1 : (|(j : ℝ)|) < 2 ^ 53 := by
      rw [hm] at h
      have : |(j : ℝ)| * (2 : ℝ) ^ (m - 53) < 2 ^ 53 * (2 : ℝ) ^ (m - 53) := by
        calc _ < (2 : ℝ) ^ (m - 53) * 2 ^ (53 : ℤ) := h
          _ = _ := by norm_num; ring
      exact lt_of_mul_lt_mul_right this hpos.le
    have hj2 : |j| < 2 ^ 53 := by exact_mod_cast hj1
    have hj3 : |j| ≤ 2 ^ 53 - 1 := by omega
    have hj4 : |(j : ℝ)| ≤ 2 ^ 53 - 1 := by exact_mod_cast hj3
    rw [hm, hu]
    calc |(j : ℝ)| * (2 : ℝ) ^ (m - 53) ≤ (2 ^ 53 - 1) * (2 : ℝ) ^ (m - 53) := mul_le_mul_of_nonneg_right hj4 hpos.le
      _ = _ := by norm_num; ring

/-- Lemma 32's bucket bound on `r`, for every `n`: `|r_0| < t = 2^m` gives `|r| ≤ t(1 + 2^{-50})`, as
`|r| ≤ |r_0|/(1 - 2u)` and `|r_0| ≤ t(1 - u)` -/
theorem lemma32_bucket_r (hp : p = 53) (hn : 1 ≤ n) (x : ℕ → ℝ) (hx : ∀ i < n, F p (x i)) (hH : Htheta p n 2 x)
    (hx0 : |x 0| ≤ 2 ^ 52) (m : ℤ) (hr0 : |redR p n x 0| < (2 : ℝ) ^ m) :
    |∑ i ∈ range n, redR p n x i| ≤ (2 : ℝ) ^ m * (1 + 1 / 2 ^ 50) := by
  have hu : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num
  obtain ⟨hF, hrH, -⟩ := lemma32_r p n hp hn x hx hH hx0
  have ht0 : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hr0' := F_lt_zpow p hp (hF 0 (by omega)) m hr0
  rw [hu] at hr0'
  have htail := Htheta_tail p n hn 2 (by norm_num) (by rw [hu]; norm_num) _ hrH
  rw [hu] at htail
  norm_num at htail
  have := abs_sub_abs_le_abs_sub (∑ i ∈ range n, redR p n x i) (redR p n x 0)
  nlinarith

/-- Lemma 32's buckets, for `n ≤ 38`: `r` with `|r_0| < t = 2^m` and `u^{n/2} ≤ t` has `|r|` and `|r_e|` at most
`t(1 + 2^{-50})`; `t = 2^{-j}` is bucket `j`'s `r̄_j`, and `t = u^{n/2}` the `r̄_min` of `|r_0| < u^{n/2}` -/
theorem lemma32_bucket (hp : p = 53) (hn : 1 ≤ n) (hn38 : n ≤ 38) (x : ℕ → ℝ) (hx : ∀ i < n, F p (x i))
    (hH : Htheta p n 2 x) (hx0 : |x 0| ≤ 2 ^ 52) (m : ℤ) (ht : u p ^ (n / 2) ≤ (2 : ℝ) ^ m)
    (hr0 : |redR p n x 0| < (2 : ℝ) ^ m) :
    |∑ i ∈ range n, redR p n x i| ≤ (2 : ℝ) ^ m * (1 + 1 / 2 ^ 50) ∧
      |∑ i ∈ range n, x i - redK p n x * (Real.pi / 2)| ≤ (2 : ℝ) ^ m * (1 + 1 / 2 ^ 50) := by
  have hu : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num
  obtain ⟨hk, ha, hb⟩ := lemma32_k p n hp hn x hH hx0
  obtain ⟨hF, hrH, -, hre, -⟩ := lemma32_r p n hp hn x hx hH hx0
  set t : ℝ := (2 : ℝ) ^ m with htd
  have ht0 : 0 < t := by positivity
  have hr0' := F_lt_zpow p hp (hF 0 (by omega)) m hr0
  rw [← htd, hu] at hr0'
  -- `|r| ≤ |r_0|/(1 - 2u)`
  have htail := Htheta_tail p n hn 2 (by norm_num) (by rw [hu]; norm_num) _ hrH
  rw [hu] at htail
  norm_num at htail
  have hrs : |∑ i ∈ range n, redR p n x i| ≤ t * (1 + 1 / 2 ^ 50) := lemma32_bucket_r p n hp hn x hx hH hx0 m hr0
  refine ⟨hrs, ?_⟩
  set k := redK p n x with hkd
  set re := ∑ i ∈ range n, x i - k * (Real.pi / 2) with hred
  -- `2E_π ≤ 2^{-157}t`, as `t ≥ u^{19} = 2^{-1007}`
  have hu19 : (2 : ℝ) ^ (-1007 : ℤ) ≤ t := by
    refine le_trans ?_ ht
    calc (2 : ℝ) ^ (-1007 : ℤ) = u p ^ 19 := by
          rw [hp]; unfold u; rw [← zpow_natCast, ← zpow_mul]; norm_num
      _ ≤ u p ^ (n / 2) := pow_le_pow_of_le_one (u_pos p).le (by rw [hu]; norm_num) (by omega)
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
    have hre0 : re = ∑ i ∈ range n, x i := by rw [hred, hk', Int.cast_zero, zero_mul, sub_zero]
    rw [hre0, ← hr]
    exact hrs
  · have husn : us p ^ n ≤ u p := by
      calc us p ^ n ≤ us p ^ 1 := pow_le_pow_of_le_one (us_nonneg p) (by
            have := us_le_u p; rw [hu] at this; linarith) hn
        _ = us p := pow_one _
        _ ≤ u p := us_le_u p
    have h1 : |re| ≤ |∑ i ∈ range n, redR p n x i| + |∑ i ∈ range n, redR p n x i - re| := by
      have := abs_sub_abs_le_abs_sub re (∑ i ∈ range n, redR p n x i)
      rw [abs_sub_comm re] at this
      linarith
    have h2 : us p ^ n * |re| ≤ u p * |re| := mul_le_mul_of_nonneg_right husn (abs_nonneg _)
    rw [hu] at h2
    have h3 : |∑ i ∈ range n, redR p n x i| ≤ |redR p n x 0| + |∑ i ∈ range n, redR p n x i - redR p n x 0| := by
      have := abs_sub_abs_le_abs_sub (∑ i ∈ range n, redR p n x i) (redR p n x 0)
      linarith
    linarith

/-- Lemma 32 for `r_e`, in every bucket: `|r_e| ≤ r̄_0 = 0.78541`, as `r_e = x` for `k = 0`, and otherwise `r_e` is
within `E_π` of `v` with `|v| ≤ (1 + u)r_max` -/
theorem lemma32_re (hp : p = 53) (hn : 1 ≤ n) (x : ℕ → ℝ) (hH : Htheta p n 2 x) (hx0 : |x 0| ≤ 2 ^ 52) :
    |∑ i ∈ range n, x i - redK p n x * (Real.pi / 2)| ≤ 78541 / 100000 := by
  have hu : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num
  obtain ⟨hk, ha, hb⟩ := lemma32_k p n hp hn x hH hx0
  by_cases hk0 : redK1 p x = 0
  · obtain ⟨hk', -, hx⟩ := ha hk0
    rw [hk', Int.cast_zero, zero_mul, sub_zero]
    linarith
  · obtain ⟨-, hv⟩ := hb hk0
    rw [hu] at hv
    have he := redV_err n x (redK p n x)
    rw [abs_sub_comm] at he
    have h1 := abs_sub_abs_le_abs_sub (∑ i ∈ range n, x i - redK p n x * (Real.pi / 2)) (redV n x (redK p n x))
    have hR : redRmax p ≤ 7854 / 10000 + 1 / 10 ^ 10 := by
      have := (abs_le.mp (redRmax_err p hp)).2
      have h54 : (2 : ℝ) ^ (-54 : ℤ) ≤ 1 / 10 ^ 10 := by norm_num
      linarith
    have hE : |(redK p n x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ) ≤ 1 / 10 ^ 10 := by
      have h2 : (2 : ℝ) ^ (-1217 : ℤ) ≤ (2 : ℝ) ^ (-100 : ℤ) := zpow_le_zpow_right₀ one_le_two (by norm_num)
      calc _ ≤ 64 / 100 * 2 ^ 52 * (2 : ℝ) ^ (-100 : ℤ) := mul_le_mul hk.le h2 (by positivity) (by positivity)
        _ ≤ 1 / 10 ^ 10 := by norm_num
    generalize |(redK p n x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ) = E at he hE
    linarith only [hv, he, h1, hR, hE]

/-- Lemma 32 (b)'s `H(1)`: with `k ≠ 0`, `|r_{i+1}| ≤ u|r_i|` gives `|r_i| ≤ u^i|r_0|`. The paper's
`|r_{i+1}| ≤ ½ulp(r_i)` is stronger, but the model has no `ulp`, and `H(1)` needs only its consequence `u|r_i|` -/
theorem lemma32_H1 (hp : p = 53) (hn : 1 ≤ n) (x : ℕ → ℝ) (hx : ∀ i < n, F p (x i)) (hH : Htheta p n 2 x)
    (hx0 : |x 0| ≤ 2 ^ 52) (hk : redK1 p x ≠ 0) : Htheta p n 1 (redR p n x) := by
  obtain ⟨-, -, -, -, hl⟩ := lemma32_r p n hp hn x hx hH hx0
  replace hl := hl hk
  intro i hi1 hin
  rw [one_mul]
  induction i with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simpa using hl 0 hin
    · calc |redR p n x (j + 1)| ≤ u p * |redR p n x j| := hl j hin
        _ ≤ u p * (u p ^ j * |redR p n x 0|) := mul_le_mul_of_nonneg_left (ih hj (by omega)) (u_pos p).le
        _ = u p ^ (j + 1) * |redR p n x 0| := by ring

/-- Lemma 32's part bounds (eq:abar) for `H(2)`: `|r_i| ≤ (2u)^i(1 - 2u)/(1 - 4u)|r|`, from `|r_i| ≤ (2u)^i|r_0|` and
`|r_0| ≤ (1 - 2u)/(1 - 4u)|r|` -/
theorem lemma32_parts (hp : p = 53) (hn : 1 ≤ n) (x : ℕ → ℝ) (hx : ∀ i < n, F p (x i)) (hH : Htheta p n 2 x)
    (hx0 : |x 0| ≤ 2 ^ 52) :
    ∀ i < n, |redR p n x i| ≤ (2 * u p) ^ i * ((1 - 2 * u p) / (1 - 4 * u p)) * |∑ j ∈ range n, redR p n x j| := by
  have hu : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num
  obtain ⟨-, hrH, -⟩ := lemma32_r p n hp hn x hx hH hx0
  have hlo := Htheta_lower p n hn 2 (by norm_num) (by rw [hu]; norm_num) _ hrH
  have h0 : |redR p n x 0| ≤ (1 - 2 * u p) / (1 - 4 * u p) * |∑ j ∈ range n, redR p n x j| := by
    rw [hu] at hlo ⊢
    norm_num at hlo ⊢
    linarith
  intro i hi
  calc |redR p n x i| ≤ (2 * u p) ^ i * |redR p n x 0| := Htheta_le p n hrH i hi
    _ ≤ (2 * u p) ^ i * ((1 - 2 * u p) / (1 - 4 * u p) * |∑ j ∈ range n, redR p n x j|) :=
        mul_le_mul_of_nonneg_left h0 (pow_nonneg (mul_nonneg zero_le_two (u_pos p).le) i)
    _ = _ := by ring

end ExpansionBounds
