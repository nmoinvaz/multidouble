import ExpansionBounds.Model
import FloatSpec.src.Prop.Relative

/-!
# Rounding to nearest: the bounds (eq:rn)

Under (A2), for every real `z`: `|RN(z) - z| ≤ ū|z|`, `|RN(z) - z| ≤ u|RN(z)|` and
`|z| / (1 + u) ≤ |RN(z)| ≤ (1 + u)|z|`.
-/

namespace ExpansionBounds

open FloatSpec.Core.Defs

variable (p : ℤ)

/-- ties to even is symmetric, the condition under which rounding commutes with negation -/
theorem tieEven_symm (t : ℤ) : tieEven t = !tieEven (-(t + 1)) := by
  unfold tieEven
  rcases Int.emod_two_eq_zero_or_one t with h | h
  · have h' : (-(t + 1)) % 2 = 1 := by omega
    rw [h, h']
    decide
  · have h' : (-(t + 1)) % 2 = 0 := by omega
    rw [h, h']
    decide

theorem RN_of_F {x : ℝ} (hx : F p x) : RN p x = x :=
  FloatSpec.Core.Generic_fmt.roundR_generic 2 (FloatSpec.Core.FLX.FLX_exp p) _ x (by norm_num) hx

theorem u_pos : 0 < u p := by
  unfold u
  positivity

theorem u_ro_eq : u_ro 2 p = u p := by
  unfold u_ro u
  push_cast
  rw [zpow_add₀ two_ne_zero, zpow_one]
  ring

theorem us_le_u : us p ≤ u p := by
  have h := u_pos p
  unfold us
  rw [div_le_iff₀ (by linarith)]
  nlinarith

variable [Prec_gt_0 p]

/-- `RN p x` is in `F p`, and no element of `F p` is closer to `x` -/
theorem RN_nearest (x : ℝ) : Rnd_N_pt (F p) x (RN p x) :=
  FloatSpec.Core.Generic_fmt.round_N_pt 2 (FloatSpec.Core.FLX.FLX_exp p) tieEven x (by norm_num)

theorem F_RN (x : ℝ) : F p (RN p x) := (RN_nearest p x).1

theorem RN_neg (x : ℝ) : RN p (-x) = -RN p x := by
  have h := FloatSpec.Core.Generic_fmt.round_N_opp 2 (FloatSpec.Core.FLX.FLX_exp p) tieEven x
  have hc : (fun t => !tieEven (-(t + 1))) = tieEven := funext fun t => (tieEven_symm t).symm
  rw [hc] at h
  exact h

theorem F_neg {x : ℝ} (hx : F p x) : F p (-x) := by
  have h := F_RN p (-x)
  rwa [RN_neg, RN_of_F p hx] at h

/-- (eq:rn), first: `|RN(z) - z| ≤ ū|z|` -/
theorem abs_RN_sub_le_us (z : ℝ) : |RN p z - z| ≤ us p * |z| := by
  have h := relative_error_N_FLX' (beta := 2) (choice := tieEven) (prec := p) (by norm_num) z
  rw [u_ro_eq] at h
  exact h

/-- (eq:rn), second: `|RN(z) - z| ≤ u|RN(z)|` -/
theorem abs_RN_sub_le_u_RN (z : ℝ) : |RN p z - z| ≤ u p * |RN p z| := by
  have h := relative_error_N_FLX_round (beta := 2) (choice := tieEven) (prec := p) (by norm_num) z
  rw [u_ro_eq] at h
  exact h

/-- (eq:rn), third, upper half: `|RN(z)| ≤ (1 + u)|z|` -/
theorem abs_RN_le (z : ℝ) : |RN p z| ≤ (1 + u p) * |z| := by
  have h1 := abs_RN_sub_le_us p z
  have h2 := us_le_u p
  have h3 : |RN p z| ≤ |RN p z - z| + |z| := by
    calc |RN p z| = |(RN p z - z) + z| := by ring_nf
      _ ≤ |RN p z - z| + |z| := abs_add_le _ _
  nlinarith [abs_nonneg z]

/-- (eq:rn), third, lower half: `|z| / (1 + u) ≤ |RN(z)|` -/
theorem abs_RN_ge (z : ℝ) : |z| / (1 + u p) ≤ |RN p z| := by
  have h1 := abs_RN_sub_le_u_RN p z
  have h2 := u_pos p
  have h3 : |z| ≤ |RN p z - z| + |RN p z| := by
    calc |z| = |-(RN p z - z) + RN p z| := by ring_nf
      _ ≤ |-(RN p z - z)| + |RN p z| := abs_add_le _ _
      _ = |RN p z - z| + |RN p z| := by rw [abs_neg]
  rw [div_le_iff₀ (by linarith)]
  nlinarith

end ExpansionBounds
