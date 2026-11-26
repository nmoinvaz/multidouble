import ExpansionBounds.Log8.PsiAll
import ExpansionBounds.Log8.StartHalf

/-!
# Theorem 42 (`thm:log`) at `n = 8` and `p = 53`

The octo-double logarithm, `LOG_{8,6,43,4}` with multidouble's constants and binary64's subnormals, after its start:
`|y - ln x| ≤ 9.926u^8|ln x| + 2^{-509}`, the constants `ε_ln` and `Φ` of the paper's theorem. The proof is the
paper's, on the convex variant of the bound `𝓔(ℓ)` (paragraph "Convexity"): the cases of the reduction of `-y_0`
are the tables of `Log8/Table.lean`, each on an interval of `|ln x|`, and the kernel evaluates the variant at the
two ends of each interval (`Log8/Run0.lean` to `Log8/Run8.lean`, joined in `Log8/All.lean`); `Log8/Driver.lean`
takes a run to its case. The start `y_0` enters `thm42_8` by its bound `E(|ln x|)`, a hypothesis there;
`thm42_8_start` derives it, for the branch of step (1) without the halving, from the double-word logarithm's bound
on `ln x̃` (`Log8/Start.lean`); `thm42_8_half` for the branch with the halving, from that bound on the halved double
word and AccurateDWPlusDW's bound (`Log8/StartHalf.lean`); and `thm42_8_both` is the two by a case on step (1)'s
test. `ln8Phi_eq` and `ln8C_eq` write steps (3) and (4) of the run as the algorithm computes them, each scaling in
two rounded steps.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) [Prec_gt_0 p]

omit [Prec_gt_0 p] in
/-- Step (3) of the run as the algorithm computes it: `φ = ADDF(x', -1)` with `x'_i = S(2^{k₂} S(2^{k₁} x_i))`,
the scaling by `2^k = 2^{k₁}2^{k₂}` in two rounded steps. -/
theorem ln8Phi_eq (S : ℝ → ℝ) (k₁ k₂ : ℤ) (x : ℕ → ℝ) :
    ln8Phi p S k₁ k₂ x = pt (addfOp p 8 (fun i => S ((2 : ℝ) ^ k₂ * S ((2 : ℝ) ^ k₁ * x i))) (-1)) := by
  have h : (fun i => (fun w => S ((2 : ℝ) ^ k₂ * S ((2 : ℝ) ^ (-k₂) * w))) ((2 : ℝ) ^ (k₁ + k₂) * x i)) =
      fun i => S ((2 : ℝ) ^ k₂ * S ((2 : ℝ) ^ k₁ * x i)) := by
    funext i
    show S ((2 : ℝ) ^ k₂ * S ((2 : ℝ) ^ (-k₂) * ((2 : ℝ) ^ (k₁ + k₂) * x i))) = _
    rw [← mul_assoc, ← zpow_add₀ two_ne_zero, show -k₂ + (k₁ + k₂) = k₁ by ring]
  unfold ln8Phi logPhi
  rw [h]

omit [Prec_gt_0 p] in
/-- Step (4) of the run as the algorithm computes it: `c = ADD(φ, t)` where `min(e_φ, e_t) < -B - 13 = -449`;
otherwise `c = ADD(ADD(φ, t), p)` with `p_i = S(2^{e_t} S(2^{e_φ} MUL(2^{-e_φ}φ, 2^{-e_t}t)_i))`, the scaling back
in two rounded steps. -/
theorem ln8C_eq (S : ℝ → ℝ) (eφ et : ℤ) (φ t : ℕ → ℝ) :
    ln8C p S eφ et φ t = if min eφ et < -449 then pt (addOp p 8 φ t)
      else pt (addOp p 8 (pt (addOp p 8 φ t)) fun i => S ((2 : ℝ) ^ et * S ((2 : ℝ) ^ eφ *
        pt (mulOp p 8 (fun i => (2 : ℝ) ^ (-eφ) * φ i) fun i => (2 : ℝ) ^ (-et) * t i) i))) := by
  have hpt : ∀ i, pt (smulOp p 8 id eφ φ fun i => (2 : ℝ) ^ (-et) * t i) i =
      (2 : ℝ) ^ eφ * pt (mulOp p 8 (fun i => (2 : ℝ) ^ (-eφ) * φ i) fun i => (2 : ℝ) ^ (-et) * t i) i := fun i => by
    unfold pt smulOp
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases (mulOp p 8 (fun i => (2 : ℝ) ^ (-eφ) * φ i) fun i => (2 : ℝ) ^ (-et) * t i)[i]? <;> simp
  have h : (fun i => (fun w => S ((2 : ℝ) ^ et * S ((2 : ℝ) ^ (-et) * w)))
        ((2 : ℝ) ^ et * pt (smulOp p 8 id eφ φ fun i => (2 : ℝ) ^ (-et) * t i) i)) =
      fun i => S ((2 : ℝ) ^ et * S ((2 : ℝ) ^ eφ *
        pt (mulOp p 8 (fun i => (2 : ℝ) ^ (-eφ) * φ i) fun i => (2 : ℝ) ^ (-et) * t i) i)) := by
    funext i
    show S ((2 : ℝ) ^ et * S ((2 : ℝ) ^ (-et) *
      ((2 : ℝ) ^ et * pt (smulOp p 8 id eφ φ fun i => (2 : ℝ) ^ (-et) * t i) i))) = _
    rw [← mul_assoc ((2 : ℝ) ^ (-et)), ← zpow_add₀ two_ne_zero, neg_add_cancel, zpow_zero, one_mul, hpt i]
  unfold ln8C logC
  rw [h, show (-436 : ℤ) - 13 = -449 by norm_num]

/-- Theorem 42 (`thm:log`) at `n = 8`, `s = 6`, `d = 43`, `q = 4`, `θ = 2` and `p = 53`, for `LOG_{8,6,43,4}` after
its start, with multidouble's constants and binary64's subnormals, without overflow (the model has no largest
finite value, and the paper's theorem takes a finite result): `|y - ln x| ≤ 9.926u^8|ln x| + 2^{-509}`.

The hypotheses, by group.
* The scalings' rounding: `S` keeps a value or rounds one below `2^{-1022}` to a multiple of `2^{-1074}` within
  `2^{-1075}` (`hS`), and step (3)'s scaling in two steps, `2^k = 2^{k₁}2^{k₂}`, has `k₂ ≤ 0` (`hk`, `hk2`), as in
  `thm40_8`. Step (4)'s two steps, `2^{e_φ}` then `2^{e_t}`, need `e_t ≤ 0`, which is proved: `∑|t_i| ≤ 1`.
* The argument: `x` in `F` on `H(2)` (`hx`, `hH`) with `x > 0` (`hX0`) and `|ln x| ≤ X = 745.2` (`hX`).
* The start: `y_0` in `F` (`hy0`), of two parts (`hy2`) with `|y_{0,1}| ≤ u|y_{0,0}|` (`hy1`), within
  `E(|ln x|)` of `ln x` (`hE`), where `E(ℓ) = e₀ + e₁ℓ` is the paper's `E` with the quoted `ε_DW = 15.351u²` and
  `Φ_DW = 2^{-1071}` of Proposition 44 (`log8E`).
* The selections: `e` is the exponent of step (2)'s `U`, or `-1023` where `U < 2^{-1022}` (`hsel`); `e_t` is that
  of `U_t`, in the same way (`hselt`); and `e_φ`, `e_c` bound the sums of the magnitudes of the parts of `φ` and
  `c` (`hUφ`, `hUc`), which the exponents of `U_φ` and `U_c` do. -/
theorem thm42_8 (hp : p = 53) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℕ → ℝ) (hx : ∀ i < 8, F p (x i)) (hH : Htheta p 8 2 x) (hX0 : 0 < ∑ i ∈ range 8, x i)
    (hX : |Real.log (∑ i ∈ range 8, x i)| ≤ 7452 / 10) (y0 : ℕ → ℝ) (hy0 : ∀ i < 8, F p (y0 i))
    (hy1 : |y0 1| ≤ u p * |y0 0|) (hy2 : ∀ i, 2 ≤ i → y0 i = 0)
    (hE : |∑ i ∈ range 8, y0 i - Real.log (∑ i ∈ range 8, x i)| ≤ log8E |Real.log (∑ i ∈ range 8, x i)|)
    (k₁ k₂ : ℤ) (hk : k₁ + k₂ = expK p (-y0 0)) (hk2 : k₂ ≤ 0) (e : ℤ)
    (hsel : ((2 : ℝ) ^ e ≤ expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8R p y0) ∧
        expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8R p y0) < (2 : ℝ) ^ (e + 1)) ∨
      (expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8R p y0) < (2 : ℝ) ^ (-1022 : ℤ) ∧ e = -1023))
    (eφ et ec : ℤ) (hUφ : ∑ i ∈ range 8, |ln8Phi p S k₁ k₂ x i| < (2 : ℝ) ^ (eφ + 1))
    (hselt : ((2 : ℝ) ^ et ≤ expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8T p S y0 e) ∧
        expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8T p S y0 e) < (2 : ℝ) ^ (et + 1)) ∨
      (expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8T p S y0 e) < (2 : ℝ) ^ (-1022 : ℤ) ∧ et = -1023))
    (hUc : ∑ i ∈ range 8, |ln8C p S eφ et (ln8Phi p S k₁ k₂ x) (ln8T p S y0 e) i| < (2 : ℝ) ^ (ec + 1)) :
    |(ln8 p S y0 x k₁ k₂ e eφ et ec).sum - Real.log (∑ i ∈ range 8, x i)| ≤
      9926 / 1000 * u p ^ 8 * |Real.log (∑ i ∈ range 8, x i)| + 1 / 2 ^ 509 := by
  subst hp
  exact log8_main (fun g hg => ⟨log8_all0 g hg, log8_psi0 g hg⟩) ⟨log8_last0, log8_psi_last0⟩
    (fun g hg => ⟨log8_all1 g hg, log8_psi1 g hg⟩) ⟨log8_last1, log8_psi_last1⟩ log8_shared S hS x hx hH hX0 hX y0
    hy0 hy1 hy2 hE k₁ k₂ hk hk2 e hsel eφ et ec hUφ hselt hUc

/-- Theorem 42 (`thm:log`) at `n = 8` and `p = 53` with the start derived, for the branch of step (1) without the
halving (`x_0 < 2^{1023}` in binary64): `|y - ln x| ≤ 9.926u^8|ln x| + 2^{-509}`.

The hypotheses are those of `thm42_8`, but for the start: `y_0` is a double word (`hy0`, `hyd`, `hy2`) and the
double-word logarithm's bound holds on `ln x̃`, `|y_0 - ln x̃| ≤ ε_DW|ln x̃| + Φ_DW` with the quoted
`ε_DW = 15.351u²` and `Φ_DW = 2^{-1071}` of Proposition 44 (`hDW`), where
`x̃ = FastTwoSum(x_0, RN(x_1 + RN(x_2 + …)))` is step (1)'s double word (`ln8Xt`). -/
theorem thm42_8_start (hp : p = 53) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℕ → ℝ) (hx : ∀ i < 8, F p (x i)) (hH : Htheta p 8 2 x) (hX0 : 0 < ∑ i ∈ range 8, x i)
    (hX : |Real.log (∑ i ∈ range 8, x i)| ≤ 7452 / 10) (y0 : ℕ → ℝ) (hy0 : ∀ i < 8, F p (y0 i))
    (hyd : RN p (y0 0 + y0 1) = y0 0) (hy2 : ∀ i, 2 ≤ i → y0 i = 0)
    (hDW : |y0 0 + y0 1 - Real.log ((ln8Xt p x).1 + (ln8Xt p x).2)| ≤
      15351 / 1000 * u p ^ 2 * |Real.log ((ln8Xt p x).1 + (ln8Xt p x).2)| + 1 / 2 ^ 1071)
    (k₁ k₂ : ℤ) (hk : k₁ + k₂ = expK p (-y0 0)) (hk2 : k₂ ≤ 0) (e : ℤ)
    (hsel : ((2 : ℝ) ^ e ≤ expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8R p y0) ∧
        expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8R p y0) < (2 : ℝ) ^ (e + 1)) ∨
      (expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8R p y0) < (2 : ℝ) ^ (-1022 : ℤ) ∧ e = -1023))
    (eφ et ec : ℤ) (hUφ : ∑ i ∈ range 8, |ln8Phi p S k₁ k₂ x i| < (2 : ℝ) ^ (eφ + 1))
    (hselt : ((2 : ℝ) ^ et ≤ expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8T p S y0 e) ∧
        expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8T p S y0 e) < (2 : ℝ) ^ (et + 1)) ∨
      (expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8T p S y0 e) < (2 : ℝ) ^ (-1022 : ℤ) ∧ et = -1023))
    (hUc : ∑ i ∈ range 8, |ln8C p S eφ et (ln8Phi p S k₁ k₂ x) (ln8T p S y0 e) i| < (2 : ℝ) ^ (ec + 1)) :
    |(ln8 p S y0 x k₁ k₂ e eφ et ec).sum - Real.log (∑ i ∈ range 8, x i)| ≤
      9926 / 1000 * u p ^ 8 * |Real.log (∑ i ∈ range 8, x i)| + 1 / 2 ^ 509 := by
  have hy1 : |y0 1| ≤ u p * |y0 0| := by
    have h := abs_RN_sub_le_u_RN p (y0 0 + y0 1)
    rwa [hyd, show y0 0 - (y0 0 + y0 1) = -y0 1 by ring, abs_neg] at h
  have hsum : ∑ i ∈ range 8, y0 i = y0 0 + y0 1 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hy2 2 le_rfl, hy2 3 (by norm_num),
      hy2 4 (by norm_num), hy2 5 (by norm_num), hy2 6 (by norm_num), hy2 7 (by norm_num)]
    ring
  exact thm42_8 p hp S hS x hx hH hX0 hX y0 hy0 hy1 hy2
    (log8_start p hp x hx hH hX0 _ (by rw [hsum]; exact hDW)) k₁ k₂ hk hk2 e hsel eφ et ec hUφ hselt hUc

/-- Theorem 42 (`thm:log`) at `n = 8` and `p = 53` with the start derived, for the branch of step (1) with the
halving, `x_0 ≥ 2^{1023}`: `|y - ln x| ≤ 9.926u^8|ln x| + 2^{-509}`. The model has no largest finite value, so
the branch is stated by its test (`hbig`).

The hypotheses are those of `thm42_8`, but for the start: `y_0` is a double word (`hy0`, `hyd`, `hy2`); `w` is a
two-part logarithm of the halved double word `x̃_h` (`ln8Xh`, each part of `x/2` rounded by `S`) within
Proposition 44's bound, `|w - ln x̃_h| ≤ ε_DW|ln x̃_h| + Φ_DW` with the quoted `ε_DW = 15.351u²` and
`Φ_DW = 2^{-1071}` (`hW`); and `y_0` is within AccurateDWPlusDW's bound of `w + c_L`,
`|y_0 - (w + c_L)| ≤ 3u²/(1 - 4u)·|w + c_L|`, with `c_L` multidouble's double-double `ln 2` (`hA`). -/
theorem thm42_8_half (hp : p = 53) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℕ → ℝ) (hx : ∀ i < 8, F p (x i)) (hH : Htheta p 8 2 x) (hX0 : 0 < ∑ i ∈ range 8, x i)
    (hX : |Real.log (∑ i ∈ range 8, x i)| ≤ 7452 / 10) (hbig : (2 : ℝ) ^ (1023 : ℤ) ≤ x 0) (y0 : ℕ → ℝ)
    (hy0 : ∀ i < 8, F p (y0 i)) (hyd : RN p (y0 0 + y0 1) = y0 0) (hy2 : ∀ i, 2 ≤ i → y0 i = 0) (w0 w1 : ℝ)
    (hW : |w0 + w1 - Real.log ((ln8Xh p S x).1 + (ln8Xh p S x).2)| ≤
      15351 / 1000 * u p ^ 2 * |Real.log ((ln8Xh p S x).1 + (ln8Xh p S x).2)| + 1 / 2 ^ 1071)
    (hA : |y0 0 + y0 1 - (w0 + w1 + (((dyQ log8CL0 : ℚ) : ℝ) + ((dyQ log8CL1 : ℚ) : ℝ)))| ≤
      3 * u p ^ 2 / (1 - 4 * u p) * |w0 + w1 + (((dyQ log8CL0 : ℚ) : ℝ) + ((dyQ log8CL1 : ℚ) : ℝ))|)
    (k₁ k₂ : ℤ) (hk : k₁ + k₂ = expK p (-y0 0)) (hk2 : k₂ ≤ 0) (e : ℤ)
    (hsel : ((2 : ℝ) ^ e ≤ expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8R p y0) ∧
        expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8R p y0) < (2 : ℝ) ^ (e + 1)) ∨
      (expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8R p y0) < (2 : ℝ) ^ (-1022 : ℤ) ∧ e = -1023))
    (eφ et ec : ℤ) (hUφ : ∑ i ∈ range 8, |ln8Phi p S k₁ k₂ x i| < (2 : ℝ) ^ (eφ + 1))
    (hselt : ((2 : ℝ) ^ et ≤ expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8T p S y0 e) ∧
        expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8T p S y0 e) < (2 : ℝ) ^ (et + 1)) ∨
      (expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8T p S y0 e) < (2 : ℝ) ^ (-1022 : ℤ) ∧ et = -1023))
    (hUc : ∑ i ∈ range 8, |ln8C p S eφ et (ln8Phi p S k₁ k₂ x) (ln8T p S y0 e) i| < (2 : ℝ) ^ (ec + 1)) :
    |(ln8 p S y0 x k₁ k₂ e eφ et ec).sum - Real.log (∑ i ∈ range 8, x i)| ≤
      9926 / 1000 * u p ^ 8 * |Real.log (∑ i ∈ range 8, x i)| + 1 / 2 ^ 509 := by
  have hy1 : |y0 1| ≤ u p * |y0 0| := by
    have h := abs_RN_sub_le_u_RN p (y0 0 + y0 1)
    rwa [hyd, show y0 0 - (y0 0 + y0 1) = -y0 1 by ring, abs_neg] at h
  have hsum : ∑ i ∈ range 8, y0 i = y0 0 + y0 1 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hy2 2 le_rfl, hy2 3 (by norm_num),
      hy2 4 (by norm_num), hy2 5 (by norm_num), hy2 6 (by norm_num), hy2 7 (by norm_num)]
    ring
  exact thm42_8 p hp S hS x hx hH hX0 hX y0 hy0 hy1 hy2
    (log8_start_halved p hp S hS x hx hH hX0 hX hbig (w0 + w1) _ hW (by rw [hsum]; exact hA)) k₁ k₂ hk hk2 e hsel
    eφ et ec hUφ hselt hUc

/-- Theorem 42 (`thm:log`) at `n = 8` and `p = 53` with the start derived, for both branches of step (1), by a
case on its test: where `x_0 < 2^{1023}`, the double-word logarithm's bound on `ln x̃` (`thm42_8_start`); where
`x_0 ≥ 2^{1023}`, a two-part `w` with that bound on `ln x̃_h` and AccurateDWPlusDW's bound on `y_0` against
`w + c_L` (`thm42_8_half`). The other hypotheses are those of `thm42_8_start`. -/
theorem thm42_8_both (hp : p = 53) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℕ → ℝ) (hx : ∀ i < 8, F p (x i)) (hH : Htheta p 8 2 x) (hX0 : 0 < ∑ i ∈ range 8, x i)
    (hX : |Real.log (∑ i ∈ range 8, x i)| ≤ 7452 / 10) (y0 : ℕ → ℝ)
    (hy0 : ∀ i < 8, F p (y0 i)) (hyd : RN p (y0 0 + y0 1) = y0 0) (hy2 : ∀ i, 2 ≤ i → y0 i = 0)
    (hstart : (x 0 < (2 : ℝ) ^ (1023 : ℤ) ∧
        |y0 0 + y0 1 - Real.log ((ln8Xt p x).1 + (ln8Xt p x).2)| ≤
          15351 / 1000 * u p ^ 2 * |Real.log ((ln8Xt p x).1 + (ln8Xt p x).2)| + 1 / 2 ^ 1071) ∨
      ((2 : ℝ) ^ (1023 : ℤ) ≤ x 0 ∧ ∃ w0 w1 : ℝ,
        |w0 + w1 - Real.log ((ln8Xh p S x).1 + (ln8Xh p S x).2)| ≤
          15351 / 1000 * u p ^ 2 * |Real.log ((ln8Xh p S x).1 + (ln8Xh p S x).2)| + 1 / 2 ^ 1071 ∧
        |y0 0 + y0 1 - (w0 + w1 + (((dyQ log8CL0 : ℚ) : ℝ) + ((dyQ log8CL1 : ℚ) : ℝ)))| ≤
          3 * u p ^ 2 / (1 - 4 * u p) * |w0 + w1 + (((dyQ log8CL0 : ℚ) : ℝ) + ((dyQ log8CL1 : ℚ) : ℝ))|))
    (k₁ k₂ : ℤ) (hk : k₁ + k₂ = expK p (-y0 0)) (hk2 : k₂ ≤ 0) (e : ℤ)
    (hsel : ((2 : ℝ) ^ e ≤ expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8R p y0) ∧
        expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8R p y0) < (2 : ℝ) ^ (e + 1)) ∨
      (expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8R p y0) < (2 : ℝ) ^ (-1022 : ℤ) ∧ e = -1023))
    (eφ et ec : ℤ) (hUφ : ∑ i ∈ range 8, |ln8Phi p S k₁ k₂ x i| < (2 : ℝ) ^ (eφ + 1))
    (hselt : ((2 : ℝ) ^ et ≤ expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8T p S y0 e) ∧
        expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8T p S y0 e) < (2 : ℝ) ^ (et + 1)) ∨
      (expU p 8 ((2 : ℝ) ^ (-48 : ℤ)) (ln8T p S y0 e) < (2 : ℝ) ^ (-1022 : ℤ) ∧ et = -1023))
    (hUc : ∑ i ∈ range 8, |ln8C p S eφ et (ln8Phi p S k₁ k₂ x) (ln8T p S y0 e) i| < (2 : ℝ) ^ (ec + 1)) :
    |(ln8 p S y0 x k₁ k₂ e eφ et ec).sum - Real.log (∑ i ∈ range 8, x i)| ≤
      9926 / 1000 * u p ^ 8 * |Real.log (∑ i ∈ range 8, x i)| + 1 / 2 ^ 509 := by
  rcases hstart with ⟨-, hDW⟩ | ⟨hbig, w0, w1, hW, hA⟩
  · exact thm42_8_start p hp S hS x hx hH hX0 hX y0 hy0 hyd hy2 hDW k₁ k₂ hk hk2 e hsel eφ et ec hUφ hselt hUc
  · exact thm42_8_half p hp S hS x hx hH hX0 hX hbig y0 hy0 hyd hy2 w0 w1 hW hA k₁ k₂ hk hk2 e hsel eφ et ec hUφ
      hselt hUc

end ExpansionBounds
