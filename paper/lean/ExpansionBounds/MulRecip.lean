import ExpansionBounds.Recip
import ExpansionBounds.DDMul
import ExpansionBounds.Kappa8

/-!
# Products by the greedy constants: `mul_recip`

`DD::mul_recip(k)` multiplies a double word by the two-sum of the first two greedy parts of `1/k`, and
`OD::mul_recip(k)` multiplies an octo-double by its first eight. The constant errs by at most `u^n(1 + u)` relatively
(`greedy_err`), the product by multidouble's bound, `(6 + 2u)u²/(1 - u)²` for the double-double (`ddMul_good`) and
Theorem 15's `u^8 + κu^9((1 - 2u)/(1 - 4u))²` with `κ ≤ 2^{37.93}` for the octo-double on `H(2)` (`thm15_mul_rel`,
`kappa8_mul`); the two add up (`mul_greedy_err`) to `dd_mul_greedy` and `od_mul_greedy`, for any real `r` in place of
`1/k`.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) [Prec_gt_0 p]

omit [Prec_gt_0 p] in
/-- a product within `ε` of `X c`, with `c` within `δ` of `r`, is within `ε(1 + δ) + δ` of `X r`, relatively -/
theorem mul_greedy_err {X c r z ε δ : ℝ} (hε : 0 ≤ ε) (hz : |z - X * c| ≤ ε * |X * c|) (hc : |r - c| ≤ δ * |r|) :
    |z - X * r| ≤ (ε * (1 + δ) + δ) * |X * r| := by
  have hc' : |c| ≤ (1 + δ) * |r| := by
    have := abs_sub_abs_le_abs_sub c r
    rw [abs_sub_comm] at hc
    linarith
  have h1 : |X * c - X * r| ≤ δ * |X * r| := by
    rw [← mul_sub, abs_mul, abs_mul, abs_sub_comm]
    calc |X| * |r - c| ≤ |X| * (δ * |r|) := mul_le_mul_of_nonneg_left hc (abs_nonneg _)
      _ = δ * (|X| * |r|) := by ring
  have h2 : ε * |X * c| ≤ ε * ((1 + δ) * |X * r|) := by
    apply mul_le_mul_of_nonneg_left _ hε
    rw [abs_mul, abs_mul]
    calc |X| * |c| ≤ |X| * ((1 + δ) * |r|) := mul_le_mul_of_nonneg_left hc' (abs_nonneg _)
      _ = (1 + δ) * (|X| * |r|) := by ring
  calc |z - X * r| ≤ |z - X * c| + |X * c - X * r| := by
        have := abs_add_le (z - X * c) (X * c - X * r)
        rwa [show z - X * c + (X * c - X * r) = z - X * r by ring] at this
    _ ≤ ε * ((1 + δ) * |X * r|) + δ * |X * r| := by linarith
    _ = (ε * (1 + δ) + δ) * |X * r| := by ring

/-- `DD::mul_recip`: a double word times the double-double greedy constant of `r` is within
`ε_P(1 + u²(1 + u)) + u²(1 + u)` of `xr`, `ε_P = (6 + 2u)u²/(1 - u)²`, relatively -/
theorem dd_mul_greedy (hp : 3 ≤ p) {x : ℝ × ℝ} (hx : DW p x) (r : ℝ) :
    |dwVal (ddMul p x (twoSum p (gPart p r 0) (gPart p r 1))) - dwVal x * r| ≤
      ((6 + 2 * u p) * u p ^ 2 / (1 - u p) ^ 2 * (1 + u p ^ 2 * (1 + u p)) + u p ^ 2 * (1 + u p)) *
        |dwVal x * r| := by
  have hp1 : 1 < p := by omega
  obtain ⟨hdw, herr, -⟩ := greedy_dd p hp1 r
  obtain ⟨-, hmul⟩ := ddMul_good p hp hx hdw
  have hu := u_pos p
  have hu1 : u p < 1 := by
    unfold u
    calc (2 : ℝ) ^ (-p) < (2 : ℝ) ^ (0 : ℤ) := zpow_lt_zpow_right₀ (by norm_num) (by omega)
      _ = 1 := by norm_num
  have hε : 0 ≤ (6 + 2 * u p) * u p ^ 2 / (1 - u p) ^ 2 := by
    apply div_nonneg _ (sq_nonneg _)
    positivity
  exact mul_greedy_err hε hmul (by unfold dwVal; exact herr)

/-- `OD::mul_recip`: an octo-double on `H(2)` times the octo-double greedy constant of `r` is within
`ε_8(1 + u^8(1 + u)) + u^8(1 + u)` of `xr`, `ε_8 = u^8 + 2^{37.93}u^9((1 - 2u)/(1 - 4u))²`, relatively, at `p = 53` -/
theorem od_mul_greedy (hp : p = 53) (x : ℕ → ℝ) (hx : ∀ i < 8, F p (x i)) (hH : Htheta p 8 2 x) (r : ℝ) :
    |(mulOp p 8 x (gPart p r)).sum - (∑ i ∈ range 8, x i) * r| ≤
      ((u p ^ 8 + (2 : ℝ) ^ (37.93 : ℝ) * u p ^ 9 * ((1 - 2 * u p) / (1 - 2 * (2 * u p))) ^ 2) *
          (1 + u p ^ 8 * (1 + u p)) + u p ^ 8 * (1 + u p)) * |(∑ i ∈ range 8, x i) * r| := by
  have hp1 : 1 < p := by omega
  have hu := u_pos p
  have hu53 : u p = 1 / 9007199254740992 := by
    unfold u; rw [hp]; norm_num
  have hA3 : (((8 : ℕ) : ℝ) ^ 2 + (8 : ℕ)) * u p < 1 := by rw [hu53]; norm_num
  have hρ : 2 * (2 * u p) < 1 := by rw [hu53]; norm_num
  -- the constant: floats on `H(1)`, so on `H(2)`
  have hc : ∀ j < 8, F p (gPart p r j) := fun j _ => F_gPart p r j
  have hHc : Htheta p 8 2 (gPart p r) := by
    intro i hi1 hi
    calc |gPart p r i| ≤ u p ^ i * |gPart p r 0| := gPart_le_pow p r i
      _ ≤ (2 * u p) ^ i * |gPart p r 0| := by
        gcongr
        linarith
  have hmul := thm15_mul_rel p 8 hp1 (by norm_num) hA3 2 (by norm_num) hρ x (gPart p r) hx hc hH hHc
  have hκ := (kappa8_mul p hp).2
  have hcoef : thmKappa p 8 (mulL p 8 2) (((8 ^ 2 + 8 - 1 : ℕ) : ℝ) * mulL p 8 2 8 + thmDelta p 8 2) *
        u p ^ (8 + 1) * ((1 - 2 * u p) / (1 - 2 * (2 * u p))) ^ 2 ≤
      (2 : ℝ) ^ (37.93 : ℝ) * u p ^ 9 * ((1 - 2 * u p) / (1 - 2 * (2 * u p))) ^ 2 := by
    gcongr
  have hε : |(mulOp p 8 x (gPart p r)).sum - (∑ i ∈ range 8, x i) * (∑ j ∈ range 8, gPart p r j)| ≤
      (u p ^ 8 + (2 : ℝ) ^ (37.93 : ℝ) * u p ^ 9 * ((1 - 2 * u p) / (1 - 2 * (2 * u p))) ^ 2) *
        |(∑ i ∈ range 8, x i) * (∑ j ∈ range 8, gPart p r j)| := by
    rw [abs_sub_comm]
    refine hmul.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
    linarith
  have hε0 : 0 ≤ u p ^ 8 + (2 : ℝ) ^ (37.93 : ℝ) * u p ^ 9 * ((1 - 2 * u p) / (1 - 2 * (2 * u p))) ^ 2 := by
    have : 0 ≤ (1 - 2 * u p) / (1 - 2 * (2 * u p)) := div_nonneg (by linarith) (by linarith)
    positivity
  exact mul_greedy_err hε0 hε (greedy_err p r 8 (by norm_num))

end ExpansionBounds
