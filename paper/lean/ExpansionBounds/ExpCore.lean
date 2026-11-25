import ExpansionBounds.ExpRed
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Lemma 39: EXP's core

Under (A3), `(n² + n)u < 1`: steps (2) to (4) of EXP, where `U` bounds `∑|r_i|`, `r' = 2^{-m} r`, Horner's rule on the
`F_j` of `1/j!` gives `q`, `w = MUL(r', q)`, `t = 2^{e'} ADD(r̂, MUL(r̂, w))` with `r̂ = 2^{-e'} r'`, and `m` passes of
`t ← ADD(2t, MUL(t, t))`. The scaling by `2^{-m}` and step (3)'s scaling back by `2^{e'}` can leave the normal range:
they are rounded by `S₁` and `S₂`, which move a value by at most `η₁` and `η₂` (`Scl`), the paper's `η_0[m > 0]` and
`η_0`, and zero with an unbounded exponent range. `U` is formed as with an unbounded range. The paper's `n ≤ 31` with
`U`'s factor `1 + 2^{-48}` is here `(1 + u)^n ≤ 1 + γ` with the factor `1 + γ`.
-/

namespace ExpansionBounds

open Finset

/-- the exponential's series after `N` terms: `|e^x - ∑_{i<N} x^i/i!| ≤ B^N / (N!(1 - B/(N + 1)))` for `|x| ≤ B < N + 1`
-/
theorem exp_trunc (x B : ℝ) (hx : |x| ≤ B) (N : ℕ) (hB : B < N + 1) :
    |Real.exp x - ∑ i ∈ range N, x ^ i / (i.factorial : ℝ)| ≤
      B ^ N / ((N.factorial : ℝ) * (1 - B / (N + 1))) := by
  have hB0 : 0 ≤ B := (abs_nonneg x).trans hx
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have hq0 : 0 ≤ B / (N + 1) := div_nonneg hB0 hN1.le
  have hq1 : B / (N + 1) < 1 := by rw [div_lt_one hN1]; exact hB
  have hs : HasSum (fun i => x ^ i / (i.factorial : ℝ)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp x
  -- the tail from `N` and its geometric majorant
  have ht : HasSum (fun k => x ^ (k + N) / ((k + N).factorial : ℝ))
      (Real.exp x - ∑ i ∈ range N, x ^ i / (i.factorial : ℝ)) :=
    (hasSum_nat_add_iff' N).mpr hs
  have hg : HasSum (fun k => B ^ N / N.factorial * (B / (N + 1)) ^ k)
      (B ^ N / N.factorial * (1 - B / (N + 1))⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left _
  have hle : ∀ k, |x ^ (k + N) / ((k + N).factorial : ℝ)| ≤ B ^ N / N.factorial * (B / (N + 1)) ^ k := by
    intro k
    have hfk : (0 : ℝ) < (k + N).factorial := by exact_mod_cast Nat.factorial_pos _
    have hfac : (N.factorial : ℝ) * (N + 1) ^ k ≤ (k + N).factorial := by
      rw [add_comm k N]
      exact_mod_cast Nat.factorial_mul_pow_le_factorial
    rw [abs_div, abs_of_pos hfk, abs_pow, div_pow, pow_add]
    have hxk : |x| ^ k * |x| ^ N ≤ B ^ k * B ^ N :=
      mul_le_mul (pow_le_pow_left₀ (abs_nonneg x) hx k) (pow_le_pow_left₀ (abs_nonneg x) hx N)
        (pow_nonneg (abs_nonneg x) _) (pow_nonneg hB0 _)
    calc |x| ^ k * |x| ^ N / ((k + N).factorial : ℝ) ≤ B ^ k * B ^ N / ((N.factorial : ℝ) * (N + 1) ^ k) :=
          div_le_div₀ (mul_nonneg (pow_nonneg hB0 _) (pow_nonneg hB0 _)) hxk (by positivity) hfac
      _ = B ^ N / N.factorial * (B ^ k / (N + 1) ^ k) := by field_simp
  have h := hasSum_le (fun k => (abs_le.mp (hle k)).2) ht hg
  have h' := hasSum_le (fun k => (abs_le.mp (hle k)).1) hg.neg ht
  have heq : B ^ N / N.factorial * (1 - B / (N + 1))⁻¹ = B ^ N / ((N.factorial : ℝ) * (1 - B / (N + 1))) := by
    rw [div_mul_eq_div_div, div_eq_mul_inv (B ^ N / _)]
  rw [abs_le]
  constructor <;> linarith

/-- `1/j!` -/
noncomputable def invF (j : ℕ) : ℝ := 1 / (j.factorial : ℝ)

/-- `x + x² ∑_{l=2}^{d} x^{l-2}/l! = ∑_{i=0}^{d} x^i/i! - 1` -/
theorem exp_horner (x : ℝ) (d : ℕ) (hd : 2 ≤ d) :
    x + x ^ 2 * hornerE invF x d 2 = ∑ i ∈ range (d + 1), x ^ i / (i.factorial : ℝ) - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have hL : x ^ 2 * ∑ l ∈ range (k + 1), invF (2 + l) * x ^ l =
      ∑ l ∈ range (k + 1), x ^ (l + 1 + 1) / ((l + 1 + 1).factorial : ℝ) := by
    rw [mul_sum]
    exact sum_congr rfl fun l _ => by rw [invF, show 2 + l = l + 1 + 1 by omega, pow_add]; ring
  have hR : ∑ i ∈ range (k + 2 + 1), x ^ i / (i.factorial : ℝ) =
      ∑ l ∈ range (k + 1), x ^ (l + 1 + 1) / ((l + 1 + 1).factorial : ℝ) + x + 1 := by
    rw [show k + 2 + 1 = k + 1 + 1 + 1 by omega, sum_range_succ', sum_range_succ']
    simp only [zero_add, pow_one, pow_zero, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one]
  unfold hornerE
  rw [show k + 2 + 1 - 2 = k + 1 by omega, hL, hR]
  ring

/-- `v_k = ∑_{l=k}^{d'} b'^{l-k}/l!`: `v_{d'} = 1/d'!` and `v_k = 1/k! + b' v_{k+1}` -/
noncomputable def coreV (b' : ℝ) (d' : ℕ) (k : ℕ) : ℝ := hornerE invF b' d' k

/-- `E^tr_{d'} = b'^{d'+1} / ((d' + 1)!(1 - b'/(d' + 2)))` -/
noncomputable def eTr (b' : ℝ) (d' : ℕ) : ℝ := b' ^ (d' + 1) / (((d' + 1).factorial : ℝ) * (1 - b' / (d' + 2)))

theorem eTr_bound (x b' : ℝ) (hx : |x| ≤ b') (d' : ℕ) (hb : b' < d' + 2) :
    |Real.exp x - ∑ i ∈ range (d' + 1), x ^ i / (i.factorial : ℝ)| ≤ eTr b' d' := by
  have h := exp_trunc x b' hx (d' + 1) (by push_cast; linarith)
  unfold eTr
  convert h using 4
  push_cast
  ring

variable (p : ℤ) [Prec_gt_0 p] (n : ℕ)

/-- `RN(∑|r_i|)`, the sum taken from `|r_0|` down -/
noncomputable def absSum (r : ℕ → ℝ) : ℕ → ℝ
  | 0 => |r 0|
  | i + 1 => RN p (absSum r i + |r (i + 1)|)

/-- step (2)'s `U = RN(RN(∑|r_i|)(1 + γ))`, with `γ = 2^{-48}` in binary64 -/
noncomputable def expU (γ : ℝ) (r : ℕ → ℝ) : ℝ := RN p (absSum p r (n - 1) * (1 + γ))

theorem RN_ge_of_nonneg {z : ℝ} (hz : 0 ≤ z) : z / (1 + u p) ≤ RN p z := by
  have h := abs_RN_sub_le_us p z
  rw [abs_of_nonneg hz] at h
  have hu := u_pos p
  have hus : us p * (1 + u p) = u p := us_mul p
  rw [div_le_iff₀ (by linarith)]
  have := (abs_le.mp h).1
  nlinarith

theorem absSum_ge (r : ℕ → ℝ) : ∀ i, (∑ l ∈ range (i + 1), |r l|) / (1 + u p) ^ i ≤ absSum p r i := by
  have hu := u_pos p
  intro i
  induction i with
  | zero => simp [absSum]
  | succ i ih =>
    have hq : 1 ≤ (1 + u p) ^ i := one_le_pow₀ (by linarith)
    have hq0 : 0 < (1 + u p) ^ i := by positivity
    have hs0 : 0 ≤ absSum p r i := le_trans (div_nonneg (sum_nonneg fun l _ => abs_nonneg _) hq0.le) ih
    have h := RN_ge_of_nonneg p (add_nonneg hs0 (abs_nonneg (r (i + 1))))
    simp only [absSum]
    refine le_trans ?_ h
    rw [sum_range_succ, pow_succ, ← div_div, add_div]
    gcongr
    exact div_le_self (abs_nonneg _) hq

/-- `U ≥ ∑|r_i|` when `(1 + u)^n ≤ 1 + γ` -/
theorem expU_ge (hn : 1 ≤ n) (γ : ℝ) (hγ : (1 + u p) ^ n ≤ 1 + γ) (r : ℕ → ℝ) :
    ∑ i ∈ range n, |r i| ≤ expU p n γ r := by
  have hu := u_pos p
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hq0 : 0 < (1 + u p) ^ k := by positivity
  have h1 := absSum_ge p r k
  have hS0 : 0 ≤ ∑ l ∈ range (k + 1), |r l| := sum_nonneg fun l _ => abs_nonneg _
  have hγ0 : 0 ≤ 1 + γ := le_trans (by positivity) hγ
  have hs0 : 0 ≤ absSum p r k := le_trans (div_nonneg hS0 hq0.le) h1
  have h2 := RN_ge_of_nonneg p (mul_nonneg hs0 hγ0)
  unfold expU
  rw [show k + 1 - 1 = k by omega]
  refine le_trans ?_ h2
  rw [pow_succ] at hγ
  rw [le_div_iff₀ (by linarith)]
  calc (∑ l ∈ range (k + 1), |r l|) * (1 + u p) = (∑ l ∈ range (k + 1), |r l|) / (1 + u p) ^ k *
        ((1 + u p) ^ k * (1 + u p)) := by field_simp
    _ ≤ absSum p r k * (1 + γ) := mul_le_mul h1 hγ (by positivity) hs0

/-- a scaling's rounding where the exponent range ends: `S` moves a value by at most `η` and keeps it in `F p`. With
an unbounded range `S` is the identity and `η = 0` (`Scl.id`); in binary64 a scaled part below `2^{-1022}` is rounded
to a multiple of `2^{-1074}` and `η = η_0 = 2^{-1075}` (`Scl.of_grid`) -/
structure Scl (η : ℝ) (S : ℝ → ℝ) : Prop where
  err : ∀ v, |S v - v| ≤ η
  mem : ∀ v, F p v → F p (S v)

omit [Prec_gt_0 p] in
/-- the exact scaling of an unbounded exponent range -/
theorem Scl.id : Scl p 0 id := ⟨fun v => by simp, fun _ h => h⟩

omit [Prec_gt_0 p] in
theorem Scl.nonneg {η : ℝ} {S : ℝ → ℝ} (h : Scl p η S) : 0 ≤ η := (abs_nonneg _).trans (h.err 0)

/-- binary64's scalings, whatever the rule at a tie: a value is kept, or it is below `2^{-1022}` and is rounded to a
multiple of `2^{-1074}` within `η_0 = 2^{-1075}` -/
theorem Scl.of_grid (hp : p = 53) (S : ℝ → ℝ)
    (h : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ))) :
    Scl p ((2 : ℝ) ^ (-1075 : ℤ)) S := by
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · rcases h v with h1 | ⟨-, -, h3⟩
    · rw [h1, sub_self, abs_zero]
      positivity
    · exact h3
  · rcases h v with h1 | ⟨h1, h2, h3⟩
    · rw [h1]
      exact hv
    · refine F_of_mult p h1 ?_
      have ht := abs_sub_abs_le_abs_sub (S v) v
      have h4 : (2 : ℝ) ^ (-1022 : ℤ) + (2 : ℝ) ^ (-1075 : ℤ) < (2 : ℝ) ^ (-1074 + p) := by
        rw [hp]
        have e1 : (2 : ℝ) ^ (-1022 : ℤ) = (2 : ℝ) ^ (-1075 : ℤ) * 2 ^ (53 : ℕ) := by
          rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]
          norm_num
        have e2 : (2 : ℝ) ^ (-1074 + 53 : ℤ) = (2 : ℝ) ^ (-1075 : ℤ) * 2 ^ (54 : ℕ) := by
          rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]
          norm_num
        have hpos : (0 : ℝ) < (2 : ℝ) ^ (-1075 : ℤ) := by positivity
        rw [e1, e2]
        nlinarith
      linarith

/-- a rounding that meets `Scl.of_grid`'s hypothesis: below `2^{-1022}`, to a nearest multiple of `2^{-1074}` -/
noncomputable def subRound (v : ℝ) : ℝ :=
  if |v| < (2 : ℝ) ^ (-1022 : ℤ) then (round (v * (2 : ℝ) ^ (1074 : ℤ)) : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) else v

theorem subRound_grid (v : ℝ) : subRound v = v ∨
    (Mult (-1074) (subRound v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |subRound v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)) := by
  unfold subRound
  split_ifs with h
  · refine Or.inr ⟨⟨_, rfl⟩, h, ?_⟩
    have h1 := abs_sub_round (v * (2 : ℝ) ^ (1074 : ℤ))
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-1074 : ℤ) := by positivity
    have hcC : (2 : ℝ) ^ (-1074 : ℤ) * (2 : ℝ) ^ (1074 : ℤ) = 1 := by
      rw [← zpow_add₀ two_ne_zero, show (-1074 : ℤ) + 1074 = 0 by norm_num, zpow_zero]
    have e : (round (v * (2 : ℝ) ^ (1074 : ℤ)) : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) - v =
        (2 : ℝ) ^ (-1074 : ℤ) * ((round (v * (2 : ℝ) ^ (1074 : ℤ)) : ℝ) - v * (2 : ℝ) ^ (1074 : ℤ)) := by
      linear_combination v * hcC
    rw [e, abs_mul, abs_of_pos hpos, abs_sub_comm]
    calc (2 : ℝ) ^ (-1074 : ℤ) * |v * (2 : ℝ) ^ (1074 : ℤ) - round (v * (2 : ℝ) ^ (1074 : ℤ))| ≤
          (2 : ℝ) ^ (-1074 : ℤ) * (1 / 2) := mul_le_mul_of_nonneg_left h1 hpos.le
      _ = (2 : ℝ) ^ (-1075 : ℤ) := by
          rw [show (-1074 : ℤ) = -1075 + 1 by norm_num, zpow_add₀ two_ne_zero, zpow_one]; ring
  · exact Or.inl rfl

/-- a scaling in two steps, the second by `2^j` with `j ≤ 0`, moves a value by at most `2η` -/
theorem Scl.two_step {η : ℝ} {S : ℝ → ℝ} (h : Scl p η S) {j : ℤ} (hj : j ≤ 0) :
    Scl p (2 * η) fun v => S ((2 : ℝ) ^ j * S ((2 : ℝ) ^ (-j) * v)) := by
  have hj1 : (2 : ℝ) ^ j ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) hj
  have hj0 : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  refine ⟨fun v => ?_, fun v hv => h.mem _ (F_zpow_mul p _ (h.mem _ (F_zpow_mul p _ hv)))⟩
  show |S ((2 : ℝ) ^ j * S ((2 : ℝ) ^ (-j) * v)) - v| ≤ 2 * η
  obtain ⟨w, hw⟩ : ∃ w, w = S ((2 : ℝ) ^ (-j) * v) := ⟨_, rfl⟩
  have h1 := h.err ((2 : ℝ) ^ j * w)
  have h2 := h.err ((2 : ℝ) ^ (-j) * v)
  rw [← hw] at h2 ⊢
  have h3 : (2 : ℝ) ^ j * w - v = (2 : ℝ) ^ j * (w - (2 : ℝ) ^ (-j) * v) := by
    rw [mul_sub, ← mul_assoc, ← zpow_add₀ two_ne_zero, add_neg_cancel, zpow_zero, one_mul]
  have h4 : |(2 : ℝ) ^ j * w - v| ≤ η := by
    rw [h3, abs_mul, abs_of_pos hj0]
    calc _ ≤ 1 * η := mul_le_mul hj1 h2 (abs_nonneg _) zero_le_one
      _ = η := one_mul η
  calc |S ((2 : ℝ) ^ j * w) - v| = |(S ((2 : ℝ) ^ j * w) - (2 : ℝ) ^ j * w) + ((2 : ℝ) ^ j * w - v)| := by ring_nf
    _ ≤ η + η := (abs_add_le _ _).trans (add_le_add h1 h4)
    _ = 2 * η := by ring

/-- two scalings in a row, by `2^i` and then by `2^j`, each rounded by `S`, are the rounding of `Scl.two_step` applied
to the exactly scaled `2^j(2^i v)`: the pair is one rounding of that value -/
theorem Scl.two_step_apply (S : ℝ → ℝ) (i j : ℤ) (v : ℝ) :
    (fun w => S ((2 : ℝ) ^ j * S ((2 : ℝ) ^ (-j) * w))) ((2 : ℝ) ^ j * ((2 : ℝ) ^ i * v)) =
      S ((2 : ℝ) ^ j * S ((2 : ℝ) ^ i * v)) := by
  show S ((2 : ℝ) ^ j * S ((2 : ℝ) ^ (-j) * ((2 : ℝ) ^ j * ((2 : ℝ) ^ i * v)))) = _
  rw [← mul_assoc ((2 : ℝ) ^ (-j)), ← zpow_add₀ two_ne_zero, neg_add_cancel, zpow_zero, one_mul]

/-- so two scalings in a row, the second by `2^j` with `j ≤ 0`, move the exactly scaled value by at most `2η` -/
theorem Scl.two_back {η : ℝ} {S : ℝ → ℝ} (h : Scl p η S) {j : ℤ} (hj : j ≤ 0) (i : ℤ) (v : ℝ) :
    |S ((2 : ℝ) ^ j * S ((2 : ℝ) ^ i * v)) - (2 : ℝ) ^ j * ((2 : ℝ) ^ i * v)| ≤ 2 * η := by
  rw [← Scl.two_step_apply S i j v]
  exact (h.two_step p hj).err _

/-- `|e^x - e^y| ≤ e^B |x - y|` for `x, y ≤ B` -/
theorem abs_exp_sub_exp_le {x y B : ℝ} (hx : x ≤ B) (hy : y ≤ B) :
    |Real.exp x - Real.exp y| ≤ Real.exp B * |x - y| := by
  have key : ∀ s t : ℝ, s ≤ t → t ≤ B → |Real.exp s - Real.exp t| ≤ Real.exp B * |s - t| := by
    intro s t hst ht
    have h1 : Real.exp s ≤ Real.exp t := Real.exp_le_exp.mpr hst
    have h2 := Real.add_one_le_exp (s - t)
    have h3 : Real.exp s = Real.exp t * Real.exp (s - t) := by rw [← Real.exp_add]; ring_nf
    have h4 : Real.exp t ≤ Real.exp B := Real.exp_le_exp.mpr ht
    have ht0 := Real.exp_pos t
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    calc -(Real.exp s - Real.exp t) = Real.exp t * (1 - Real.exp (s - t)) := by rw [h3]; ring
      _ ≤ Real.exp t * (t - s) := mul_le_mul_of_nonneg_left (by linarith) ht0.le
      _ ≤ Real.exp B * (t - s) := mul_le_mul_of_nonneg_right h4 (by linarith)
      _ = Real.exp B * -(s - t) := by ring
  rcases le_total x y with h | h
  · exact key x y h hy
  · rw [abs_sub_comm, abs_sub_comm x y]
    exact key y x h hx

/-- step (3): `t = r'` for `d' = 1`; otherwise `q = p_2` by Horner's rule on the `F_j`, `w = MUL(r', q)`,
`r̂ = 2^{-e'} r'` and `t = 2^{e'} ADD(r̂, MUL(r̂, w))`, the scaling back rounded by `S` -/
noncomputable def expT0 (S : ℝ → ℝ) (e' : ℤ) (r' : ℕ → ℝ) (Fk : ℕ → ℕ → ℝ) (d' : ℕ) : ℕ → ℝ :=
  if d' = 1 then r' else fun i => S ((2 : ℝ) ^ e' * pt (addOp p n (fun i => (2 : ℝ) ^ (-e') * r' i)
    (pt (mulOp p n (fun i => (2 : ℝ) ^ (-e') * r' i)
      (pt (mulOp p n r' (hornerP p n (mulOp p n) r' Fk d' (d' - 2))))))) i)

/-- one pass of step (4): `t ← ADD(2t, MUL(t, t))` -/
noncomputable def expSq (t : ℕ → ℝ) : ℕ → ℝ := pt (addOp p n (fun i => 2 * t i) (pt (mulOp p n t t)))

/-- steps (3) and (4) after step (2) chose `e`, `m` and `d'`: `r' = 2^{-m} r` rounded by `S₁`, `e' = e - m`, and
step (3)'s scaling back rounded by `S₂` -/
noncomputable def expCore (S₁ S₂ : ℝ → ℝ) (e : ℤ) (m : ℕ) (r : ℕ → ℝ) (Fk : ℕ → ℕ → ℝ) (d' : ℕ) : ℕ → ℝ :=
  (expSq p n)^[m] (expT0 p n S₂ (e - m) (fun i => S₁ ((2 : ℝ) ^ (-(m : ℤ)) * r i)) Fk d')

omit [Prec_gt_0 p] in
/-- `(E_0, ψ_0)` for `t̄_0 = T0`: `e_2, π^q_2` of Lemma 33, `(ε', ω') = G_MUL(π', π^q_2; b'(v_2 + e_2))`,
`(ε'', ω) = G_MUL(π', ω'; b'(b'(v_2 + e_2) + ε'))`, `E^- = ε'' + b'(ε' + b'e_2) + E^tr_{d'} + D`, with `D` the
paper's `2nη_0[m > 0]`, `(ε''', ψ^-) = G_ADD(π', ω; t̄_0 + E^-)`, `E_0 = E^- + ε''' + nη` and `ψ_{0,i} = ψ^-_i + η`;
for `d' = 1`, `(E^tr_1 + D, π')` -/
noncomputable def core0 (T0 D η : ℝ) (π' : ℕ → ℝ) (b' : ℝ) (Fk : ℕ → ℕ → ℝ) (φ : ℕ → ℝ) (d' : ℕ) :
    ℝ × (ℕ → ℝ) :=
  if d' = 1 then (eTr b' 1 + D, π') else
    let H := hornerB p n π' b' 0 0 Fk φ (coreV b' d') d' (d' - 2)
    let Zw := b' * (coreV b' d' 2 + H.1)
    let ε1 := GmulE p n π' H.2 Zw
    let Zy := b' * (Zw + ε1)
    let ω := GmulP p n π' (GmulP p n π' H.2 Zw) Zy
    let Em := GmulE p n π' (GmulP p n π' H.2 Zw) Zy + b' * (ε1 + b' * H.1) + eTr b' d' + D
    (Em + GaddE p n π' ω (T0 + Em) + n * η, fun i => GaddP p n π' ω (T0 + Em) i + η)

omit [Prec_gt_0 p] in
/-- one squaring's bounds: `(ε^m, ν) = G_MUL(ψ, ψ; (T + E)²)`, `(ε^s, ψ') = G_ADD(2ψ, ν; T' + 2E(1 + T) + E² + ε^m)`
and `E' = 2gE + E² + ε^m + ε^s` -/
noncomputable def sqB (T T' g E : ℝ) (ψ : ℕ → ℝ) : ℝ × (ℕ → ℝ) :=
  let εm := GmulE p n ψ ψ ((T + E) ^ 2)
  let Zs := T' + 2 * E * (1 + T) + E ^ 2 + εm
  (2 * g * E + E ^ 2 + εm + GaddE p n (fun i => 2 * ψ i) (GmulP p n ψ ψ ((T + E) ^ 2)) Zs,
    GaddP p n (fun i => 2 * ψ i) (GmulP p n ψ ψ ((T + E) ^ 2)) Zs)

omit [Prec_gt_0 p] in
/-- `(E_j, ψ_j)`, from `(E_0, ψ_0)` by `sqB` with `t̄_j` and `g_j` -/
noncomputable def coreE (T g : ℕ → ℝ) (E0 : ℝ) (ψ0 : ℕ → ℝ) : ℕ → ℝ × (ℕ → ℝ)
  | 0 => (E0, ψ0)
  | j + 1 => sqB p n (T j) (T (j + 1)) (g j) (coreE T g E0 ψ0 j).1 (coreE T g E0 ψ0 j).2

/-- `t̄_j = e^{2^j b'} - 1` for `r ≥ 0` and `1 - e^{-2^j b'}` for `r ≤ 0` -/
noncomputable def coreT (pos : Bool) (b' : ℝ) (j : ℕ) : ℝ :=
  if pos then Real.exp (2 ^ j * b') - 1 else 1 - Real.exp (-(2 ^ j * b'))

/-- `g_j = 1 + t̄_j` for `r ≥ 0` and `e^{-2^j a'}` for `r ≤ 0`, with `a' = 2^{-m} a` -/
noncomputable def coreG (pos : Bool) (a' b' : ℝ) (j : ℕ) : ℝ :=
  if pos then Real.exp (2 ^ j * b') else Real.exp (-(2 ^ j * a'))

/-- `t*_j = e^{2^j R'} - 1` is within `t̄_j`, and `|2 + 2t*_j| ≤ 2g_j` -/
theorem tstar_bound (pos : Bool) (R' a' b' : ℝ) (hb : |R'| ≤ b') (ha : a' ≤ |R'|)
    (hsgn : if pos then 0 ≤ R' else R' ≤ 0) (j : ℕ) :
    |Real.exp (2 ^ j * R') - 1| ≤ coreT pos b' j ∧ |2 + 2 * (Real.exp (2 ^ j * R') - 1)| ≤ 2 * coreG pos a' b' j := by
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have he := Real.exp_pos (2 ^ j * R')
  have h2e : |2 + 2 * (Real.exp (2 ^ j * R') - 1)| = 2 * Real.exp (2 ^ j * R') := by
    rw [show 2 + 2 * (Real.exp (2 ^ j * R') - 1) = 2 * Real.exp (2 ^ j * R') by ring, abs_of_pos (by positivity)]
  rw [h2e]
  cases pos with
  | true =>
    simp only [ite_true] at hsgn
    simp only [coreT, coreG, ite_true]
    rw [abs_of_nonneg hsgn] at hb
    have hle : Real.exp (2 ^ j * R') ≤ Real.exp (2 ^ j * b') := Real.exp_le_exp.mpr (by nlinarith)
    have hge : 1 ≤ Real.exp (2 ^ j * R') := Real.one_le_exp (by positivity)
    rw [abs_of_nonneg (by linarith)]
    constructor <;> linarith
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hsgn
    simp only [coreT, coreG, Bool.false_eq_true, ite_false]
    rw [abs_of_nonpos hsgn] at hb ha
    have hge : Real.exp (-(2 ^ j * b')) ≤ Real.exp (2 ^ j * R') := Real.exp_le_exp.mpr (by nlinarith)
    have hle : Real.exp (2 ^ j * R') ≤ Real.exp (-(2 ^ j * a')) := Real.exp_le_exp.mpr (by nlinarith)
    have h1 : Real.exp (2 ^ j * R') ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    rw [abs_of_nonpos (by linarith)]
    constructor <;> linarith

/-- one pass of step (4): from `t` within `E` of `t*`, `ADD(2t, MUL(t, t))` is within `sqB`'s bound of `2t* + t*²` -/
theorem core_sq (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (t : ℕ → ℝ)
    (ht : ∀ i < n, F p (t i)) (ψ : ℕ → ℝ) (hψ : ∀ i < n, |t i| ≤ ψ i) (ts E T T' g : ℝ)
    (hE : |∑ i ∈ range n, t i - ts| ≤ E) (hT : |ts| ≤ T) (hT' : |2 * ts + ts ^ 2| ≤ T')
    (hg : |2 + 2 * ts| ≤ 2 * g) :
    |∑ i ∈ range n, expSq p n t i - (2 * ts + ts ^ 2)| ≤ (sqB p n T T' g E ψ).1 ∧
      (∀ i < n, |expSq p n t i| ≤ (sqB p n T T' g E ψ).2 i) ∧ ∀ i < n, F p (expSq p n t i) := by
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ i ∈ range n, t i := ⟨_, rfl⟩
  rw [← hS] at hE
  obtain ⟨h, hh⟩ : ∃ h, h = S - ts := ⟨_, rfl⟩
  rw [← hh] at hE
  have hE0 : 0 ≤ E := (abs_nonneg _).trans hE
  have hT0 : 0 ≤ T := (abs_nonneg _).trans hT
  have hSb : |S| ≤ T + E := by
    rw [show S = ts + h by rw [hh]; ring]
    exact (abs_add_le _ _).trans (add_le_add hT hE)
  -- `MUL(t, t)`
  have hZm : |(∑ i ∈ range n, t i) * ∑ j ∈ range n, t j| ≤ (T + E) ^ 2 := by
    rw [← hS, abs_mul, ← sq]
    exact pow_le_pow_left₀ (abs_nonneg _) hSb 2
  obtain ⟨n1, n2, n3, n4⟩ := mul_G p n hp hn hA3 t t ψ ψ ht ht hψ hψ _ hZm
  rw [← hS] at n1
  obtain ⟨N, hN⟩ : ∃ N, N = pt (mulOp p n t t) := ⟨_, rfl⟩
  have hNs : ∑ i ∈ range n, N i = (mulOp p n t t).sum := by rw [hN]; exact (list_sum_getD _ n n4).symm
  obtain ⟨εm, hεm⟩ : ∃ εm, εm = GmulE p n ψ ψ ((T + E) ^ 2) := ⟨_, rfl⟩
  rw [← hεm, ← hNs] at n1
  -- `ADD(2t, N)`
  have h2F : ∀ i < n, F p (2 * t i) := fun i hi => by
    have := F_zpow_mul p 1 (ht i hi)
    simpa using this
  have h2ψ : ∀ i < n, |2 * t i| ≤ 2 * ψ i := fun i hi => by
    rw [abs_mul, abs_two]
    linarith [hψ i hi]
  have h2s : ∑ i ∈ range n, 2 * t i = 2 * S := by rw [hS, mul_sum]
  have hhg : |h * (2 + 2 * ts)| ≤ E * (2 + 2 * T) := by
    rw [abs_mul]
    have : |2 + 2 * ts| ≤ 2 + 2 * T := (abs_add_le _ _).trans (by rw [abs_two, abs_mul, abs_two]; linarith)
    exact mul_le_mul hE this (abs_nonneg _) hE0
  have hh2 : h ^ 2 ≤ E ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hE 2
  have hsq : 2 * S + S * S = (2 * ts + ts ^ 2) + h * (2 + 2 * ts) + h ^ 2 := by rw [hh]; ring
  have hZs : |∑ i ∈ range n, 2 * t i + ∑ i ∈ range n, N i| ≤ T' + 2 * E * (1 + T) + E ^ 2 + εm := by
    rw [h2s, show 2 * S + ∑ i ∈ range n, N i =
      (2 * ts + ts ^ 2) + h * (2 + 2 * ts) + h ^ 2 + (∑ i ∈ range n, N i - S * S) by rw [← hsq]; ring]
    have h4 : |∑ i ∈ range n, N i - S * S| ≤ εm := by rw [abs_sub_comm]; exact n1
    have hh2' : |h ^ 2| ≤ E ^ 2 := by rw [abs_of_nonneg (sq_nonneg h)]; exact hh2
    calc _ ≤ |2 * ts + ts ^ 2| + |h * (2 + 2 * ts)| + |h ^ 2| + |∑ i ∈ range n, N i - S * S| :=
          (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ T' + E * (2 + 2 * T) + E ^ 2 + εm := add_le_add (add_le_add (add_le_add hT' hhg) hh2') h4
      _ = T' + 2 * E * (1 + T) + E ^ 2 + εm := by ring
  obtain ⟨a1, a2, a3, a4⟩ := add_G p n hp hn hA3 (fun i => 2 * t i) N (fun i => 2 * ψ i)
    (GmulP p n ψ ψ ((T + E) ^ 2)) h2F (fun j _ => by rw [hN]; exact n3 j) h2ψ (fun j _ => by rw [hN]; exact n2 j)
    _ hZs
  have hres : ∑ i ∈ range n, expSq p n t i = (addOp p n (fun i => 2 * t i) N).sum := by
    rw [expSq, ← hN]; exact (list_sum_getD _ n a4).symm
  refine ⟨?_, fun i _ => by rw [expSq, ← hN]; simp only [sqB]; rw [← hεm]; exact a2 i,
    fun i _ => by rw [expSq, ← hN]; exact a3 i⟩
  rw [hres]
  simp only [sqB]
  rw [← hεm]
  have hgE : |h * (2 + 2 * ts)| ≤ 2 * g * E := by
    rw [abs_mul, mul_comm (2 * g)]
    exact mul_le_mul hE hg (abs_nonneg _) hE0
  have hsplit : (addOp p n (fun i => 2 * t i) N).sum - (2 * ts + ts ^ 2) =
      -((∑ i ∈ range n, 2 * t i + ∑ i ∈ range n, N i) - (addOp p n (fun i => 2 * t i) N).sum) +
        (∑ i ∈ range n, N i - S * S) + h * (2 + 2 * ts) + h ^ 2 := by
    rw [h2s]; linear_combination hsq
  rw [hsplit]
  have h4 : |∑ i ∈ range n, N i - S * S| ≤ εm := by rw [abs_sub_comm]; exact n1
  have hh2' : |h ^ 2| ≤ E ^ 2 := by rw [abs_of_nonneg (sq_nonneg h)]; exact hh2
  calc _ ≤ |(∑ i ∈ range n, 2 * t i + ∑ i ∈ range n, N i) - (addOp p n (fun i => 2 * t i) N).sum| +
        |∑ i ∈ range n, N i - S * S| + |h * (2 + 2 * ts)| + |h ^ 2| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ le_rfl)) le_rfl)
        exact (abs_add_le _ _).trans (by rw [abs_neg])
    _ ≤ _ := add_le_add (add_le_add (add_le_add a1 h4) hgE) hh2'
    _ = _ := by ring

/-- step (3): `t` within `E_0` of `e^{R*} - 1` with parts at most `ψ_0`, for `|R'| ≤ b' < d' + 2`, `e^{R'}` within `D`
of `e^{R*}` and `|e^{R*} - 1| ≤ t̄_0`, the scaling back by `2^{e'}` moving each part by at most `η` -/
theorem core_t0 (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {η : ℝ} {S : ℝ → ℝ}
    (hS : Scl p η S) (r' : ℕ → ℝ)
    (hr : ∀ i < n, F p (r' i)) (π' : ℕ → ℝ) (hπ : ∀ i < n, |r' i| ≤ π' i) (R' b' : ℝ)
    (hR : R' = ∑ i ∈ range n, r' i) (hb : |R'| ≤ b') (Fk : ℕ → ℕ → ℝ) (hF : ∀ k, ∀ i < n, F p (Fk k i))
    (φ : ℕ → ℝ) (hφ : ∀ k, |∑ i ∈ range n, Fk k i - invF k| ≤ φ k) (d' : ℕ) (hd : 1 ≤ d') (hbd : b' < d' + 2)
    (e' : ℤ) (Rs T0 D : ℝ) (hD : |Real.exp R' - Real.exp Rs| ≤ D) (hT0 : |Real.exp Rs - 1| ≤ T0) :
    |∑ i ∈ range n, expT0 p n S e' r' Fk d' i - (Real.exp Rs - 1)| ≤ (core0 p n T0 D η π' b' Fk φ d').1 ∧
      (∀ i < n, |expT0 p n S e' r' Fk d' i| ≤ (core0 p n T0 D η π' b' Fk φ d').2 i) ∧
      ∀ i < n, F p (expT0 p n S e' r' Fk d' i) := by
  have hb0 : 0 ≤ b' := (abs_nonneg _).trans hb
  rcases eq_or_lt_of_le hd with h1 | h2
  · -- `d' = 1`: `t = r'`
    subst h1
    simp only [expT0, core0, ite_true]
    refine ⟨?_, hπ, hr⟩
    rw [← hR]
    have h := eTr_bound R' b' hb 1 (by exact_mod_cast hbd)
    have hs : ∑ i ∈ range (1 + 1), R' ^ i / (i.factorial : ℝ) = 1 + R' := by
      rw [sum_range_succ, sum_range_one]
      simp
    rw [hs] at h
    rw [show R' - (Real.exp Rs - 1) = -(Real.exp R' - (1 + R')) + (Real.exp R' - Real.exp Rs) by ring]
    exact (abs_add_le _ _).trans (add_le_add (by rw [abs_neg]; exact h) hD)
  have hd1 : d' ≠ 1 := by omega
  have hd2 : 2 ≤ d' := h2
  -- `q = p_2` by Lemma 33, with `z = r'`, `ε_z = 0`, `z̄ = b'` and `π^z = π'`
  obtain ⟨q, hq⟩ : ∃ q, q = hornerP p n (mulOp p n) r' Fk d' (d' - 2) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H, H = hornerB p n π' b' 0 0 Fk φ (coreV b' d') d' (d' - 2) := ⟨_, rfl⟩
  have hv : ∀ k, 2 ≤ k → k ≤ d' → |hornerE invF R' d' k| ≤ coreV b' d' k := fun k _ _ => by
    unfold hornerE coreV
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l _ => ?_)
    have hi : 0 ≤ invF (k + l) := by unfold invF; positivity
    rw [abs_mul, abs_of_nonneg hi, abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hb l) hi
  obtain ⟨q1, q2, q3⟩ := horner_step p n hp hn hA3 (mulOp_within p n hp hn hA3) r' hr π' hπ R' b' 0 hb le_rfl
    (by rw [← hR, sub_self, abs_zero, zero_mul]) Fk hF invF φ (coreV b' d') hφ d' 2 hv (d' - 2) le_rfl
  rw [show d' - (d' - 2) = 2 by omega, ← hq, ← hH] at q1
  rw [← hq, ← hH] at q2
  rw [← hq] at q3
  obtain ⟨h2v, hh2⟩ : ∃ h2v, h2v = hornerE invF R' d' 2 := ⟨_, rfl⟩
  rw [← hh2] at q1
  have hv2 : |h2v| ≤ coreV b' d' 2 := by rw [hh2]; exact hv 2 le_rfl hd2
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = ∑ i ∈ range n, q i := ⟨_, rfl⟩
  rw [← hQ] at q1
  have hQb : |Q| ≤ coreV b' d' 2 + H.1 := by
    have := abs_sub_abs_le_abs_sub Q h2v
    linarith
  -- `w = MUL(r', q)`
  obtain ⟨Zw, hZw⟩ : ∃ Zw, Zw = b' * (coreV b' d' 2 + H.1) := ⟨_, rfl⟩
  have hZwb : |(∑ i ∈ range n, r' i) * ∑ j ∈ range n, q j| ≤ Zw := by
    rw [← hR, ← hQ, abs_mul, hZw]
    exact mul_le_mul hb hQb (abs_nonneg _) hb0
  obtain ⟨w1, w2, w3, w4⟩ := mul_G p n hp hn hA3 r' q π' H.2 hr q3 hπ q2 Zw hZwb
  obtain ⟨w, hw⟩ : ∃ w, w = pt (mulOp p n r' q) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = ∑ i ∈ range n, w i := ⟨_, rfl⟩
  have hWs : (mulOp p n r' q).sum = W := by rw [hW, hw]; exact list_sum_getD _ n w4
  obtain ⟨ε1, hε1⟩ : ∃ ε1, ε1 = GmulE p n π' H.2 Zw := ⟨_, rfl⟩
  obtain ⟨ω1, hω1⟩ : ∃ ω1, ω1 = GmulP p n π' H.2 Zw := ⟨_, rfl⟩
  rw [← hR, ← hQ, hWs, ← hε1] at w1
  rw [← hω1] at w2
  have hWb : |W| ≤ Zw + ε1 := by
    have h1 := abs_sub_abs_le_abs_sub W (R' * Q)
    have h2 := hZwb
    rw [abs_sub_comm] at h1
    rw [← hR, ← hQ] at h2
    linarith
  have hWq : |W - R' * h2v| ≤ ε1 + b' * H.1 := by
    have hm : |R' * (Q - h2v)| ≤ b' * H.1 := by rw [abs_mul]; exact mul_le_mul hb q1 (abs_nonneg _) hb0
    calc |W - R' * h2v| = |-(R' * Q - W) + R' * (Q - h2v)| := by ring_nf
      _ ≤ |R' * Q - W| + |R' * (Q - h2v)| := (abs_add_le _ _).trans (by rw [abs_neg])
      _ ≤ ε1 + b' * H.1 := add_le_add w1 hm
  -- `MUL(r̂, w)` at `r̂ = 2^{-e'} r'`
  obtain ⟨c, hc⟩ : ∃ c, c = (2 : ℝ) ^ (-e') := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  have hcc : (2 : ℝ) ^ e' * c = 1 := by rw [hc, ← zpow_add₀ two_ne_zero, add_neg_cancel, zpow_zero]
  obtain ⟨rh, hrh⟩ : ∃ rh : ℕ → ℝ, rh = fun i => c * r' i := ⟨_, rfl⟩
  have hrhF : ∀ i < n, F p (rh i) := fun i hi => by rw [hrh, hc]; exact F_zpow_mul p (-e') (hr i hi)
  have hrhπ : ∀ i < n, |rh i| ≤ c * π' i := fun i hi => by
    rw [hrh, abs_mul, abs_of_pos hc0]
    exact mul_le_mul_of_nonneg_left (hπ i hi) hc0.le
  have hrhs : ∑ i ∈ range n, rh i = c * R' := by rw [hrh, hR, mul_sum]
  obtain ⟨Zy, hZy⟩ : ∃ Zy, Zy = b' * (Zw + ε1) := ⟨_, rfl⟩
  have hZyb : |(∑ i ∈ range n, rh i) * ∑ j ∈ range n, w j| ≤ c * 1 * Zy := by
    rw [hrhs, ← hW, abs_mul, abs_mul, abs_of_pos hc0, hZy, mul_one, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hb hWb (abs_nonneg _) hb0) hc0.le
  obtain ⟨y1, y2, y3, y4⟩ := mul_G p n hp hn hA3 rh w (fun i => c * π' i) (fun j => 1 * ω1 j) hrhF
    (fun j _ => by rw [hw]; exact w3 j) hrhπ (fun j _ => by rw [one_mul, hw]; exact w2 j) _ hZyb
  obtain ⟨gm1, gm2⟩ := Gmul_smul p n π' ω1 Zy hc0.le zero_le_one
  rw [gm1] at y1
  simp only [gm2] at y2
  obtain ⟨ε2, hε2⟩ : ∃ ε2, ε2 = GmulE p n π' ω1 Zy := ⟨_, rfl⟩
  obtain ⟨ω, hω⟩ : ∃ ω, ω = GmulP p n π' ω1 Zy := ⟨_, rfl⟩
  rw [← hε2] at y1
  rw [← hω] at y2
  obtain ⟨Y, hY⟩ : ∃ Y, Y = pt (mulOp p n rh w) := ⟨_, rfl⟩
  have hYs : (mulOp p n rh w).sum = ∑ i ∈ range n, Y i := by rw [hY]; exact list_sum_getD _ n y4
  rw [hrhs, ← hW, hYs] at y1
  -- `ADD(r̂, Y)`
  obtain ⟨Em, hEm⟩ : ∃ Em, Em = ε2 + b' * (ε1 + b' * H.1) + eTr b' d' + D := ⟨_, rfl⟩
  have hT0' : |Real.exp R' - 1| ≤ T0 + D := by
    rw [show Real.exp R' - 1 = (Real.exp Rs - 1) + (Real.exp R' - Real.exp Rs) by ring]
    exact (abs_add_le _ _).trans (add_le_add hT0 hD)
  have htr : |R' + R' * W - (Real.exp R' - 1)| ≤ b' * (ε1 + b' * H.1) + eTr b' d' := by
    have he := eTr_bound R' b' hb d' hbd
    have hx := exp_horner R' d' hd2
    rw [← hh2] at hx
    have hm : |R' * (W - R' * h2v)| ≤ b' * (ε1 + b' * H.1) := by
      rw [abs_mul]; exact mul_le_mul hb hWq (abs_nonneg _) hb0
    calc |R' + R' * W - (Real.exp R' - 1)| =
          |-(Real.exp R' - ∑ i ∈ range (d' + 1), R' ^ i / (i.factorial : ℝ)) + R' * (W - R' * h2v)| := by
          congr 1; linear_combination hx
      _ ≤ eTr b' d' + b' * (ε1 + b' * H.1) := (abs_add_le _ _).trans (by rw [abs_neg]; exact add_le_add he hm)
      _ = _ := by ring
  have hZ0 : |∑ i ∈ range n, rh i + ∑ i ∈ range n, Y i| ≤ c * (T0 + Em) := by
    have h1 : |c * (R' + R' * W)| ≤ c * (T0 + D + b' * (ε1 + b' * H.1) + eTr b' d') := by
      rw [abs_mul, abs_of_pos hc0]
      refine mul_le_mul_of_nonneg_left ?_ hc0.le
      have := abs_sub_abs_le_abs_sub (R' + R' * W) (Real.exp R' - 1)
      linarith
    have h2 : |∑ i ∈ range n, Y i - c * R' * W| ≤ c * 1 * ε2 := by rw [abs_sub_comm]; exact y1
    rw [hrhs, show c * R' + ∑ i ∈ range n, Y i = c * (R' + R' * W) + (∑ i ∈ range n, Y i - c * R' * W) by ring]
    calc _ ≤ |c * (R' + R' * W)| + |∑ i ∈ range n, Y i - c * R' * W| := abs_add_le _ _
      _ ≤ c * (T0 + D + b' * (ε1 + b' * H.1) + eTr b' d') + c * 1 * ε2 := add_le_add h1 h2
      _ = c * (T0 + Em) := by rw [hEm]; ring
  obtain ⟨a1, a2, a3, a4⟩ := add_G p n hp hn hA3 rh Y (fun i => c * π' i) (fun j => c * ω j) hrhF
    (fun j _ => by rw [hY]; exact y3 j) hrhπ (fun j _ => by rw [hY]; exact (y2 j).trans_eq (by ring)) _ hZ0
  obtain ⟨ga1, ga2⟩ := Gadd_smul p n π' ω (T0 + Em) hc0.le
  rw [ga1] at a1
  simp only [ga2] at a2
  have hT : expT0 p n S e' r' Fk d' = fun i => S ((2 : ℝ) ^ e' * pt (addOp p n rh Y) i) := by
    simp only [expT0, hd1, ↓reduceIte]
    rw [hY, hw, hq, hrh, hc]
  -- the scaling back moves each part by at most `η`
  have hts : |∑ i ∈ range n, expT0 p n S e' r' Fk d' i - (2 : ℝ) ^ e' * (addOp p n rh Y).sum| ≤ n * η := by
    rw [hT, list_sum_getD _ n a4, mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun i _ => hS.err _).trans_eq ?_)
    rw [sum_const, card_range, nsmul_eq_mul]
  have hcore : core0 p n T0 D η π' b' Fk φ d' =
      (Em + GaddE p n π' ω (T0 + Em) + n * η, fun i => GaddP p n π' ω (T0 + Em) i + η) := by
    simp only [core0, hd1, ↓reduceIte]
    rw [hEm, hε2, hω, hZy, hε1, hω1, hZw, hH]
  rw [hcore]
  have h2e : (0 : ℝ) < 2 ^ e' := by positivity
  refine ⟨?_, fun i _ => ?_, fun i _ => ?_⟩
  · rw [show ∑ i ∈ range n, expT0 p n S e' r' Fk d' i - (Real.exp Rs - 1) =
      (∑ i ∈ range n, expT0 p n S e' r' Fk d' i - (2 : ℝ) ^ e' * (addOp p n rh Y).sum) +
        ((2 : ℝ) ^ e' * (addOp p n rh Y).sum - (Real.exp R' - 1)) + (Real.exp R' - Real.exp Rs) by ring]
    refine ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hts le_rfl)) hD)).trans ?_
    have hsplit : (2 : ℝ) ^ e' * (addOp p n rh Y).sum - (Real.exp R' - 1) =
        -((2 : ℝ) ^ e' * ((∑ i ∈ range n, rh i + ∑ i ∈ range n, Y i) - (addOp p n rh Y).sum)) +
          (2 : ℝ) ^ e' * (∑ i ∈ range n, Y i - c * R' * W) + (R' + R' * W - (Real.exp R' - 1)) := by
      rw [hrhs]
      linear_combination (R' + R' * W) * hcc
    have hb1 : |(2 : ℝ) ^ e' * ((∑ i ∈ range n, rh i + ∑ i ∈ range n, Y i) - (addOp p n rh Y).sum)| ≤
        GaddE p n π' ω (T0 + Em) := by
      rw [abs_mul, abs_of_pos h2e]
      calc _ ≤ (2 : ℝ) ^ e' * (c * GaddE p n π' ω (T0 + Em)) := mul_le_mul_of_nonneg_left a1 h2e.le
        _ = _ := by rw [← mul_assoc, hcc, one_mul]
    have hb2 : |(2 : ℝ) ^ e' * (∑ i ∈ range n, Y i - c * R' * W)| ≤ ε2 := by
      rw [abs_mul, abs_of_pos h2e, abs_sub_comm]
      calc _ ≤ (2 : ℝ) ^ e' * (c * 1 * ε2) := mul_le_mul_of_nonneg_left y1 h2e.le
        _ = _ := by rw [mul_one, ← mul_assoc, hcc, one_mul]
    have hmid : |(2 : ℝ) ^ e' * (addOp p n rh Y).sum - (Real.exp R' - 1)| ≤
        GaddE p n π' ω (T0 + Em) + ε2 + (b' * (ε1 + b' * H.1) + eTr b' d') := by
      rw [hsplit]
      exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
        (add_le_add (by rw [abs_neg]; exact hb1) hb2)) htr)
    show _ ≤ Em + GaddE p n π' ω (T0 + Em) + n * η
    linarith
  · rw [hT]
    show |S ((2 : ℝ) ^ e' * (addOp p n rh Y).getD i 0)| ≤ GaddP p n π' ω (T0 + Em) i + η
    have h1 := abs_sub_abs_le_abs_sub (S ((2 : ℝ) ^ e' * (addOp p n rh Y).getD i 0))
      ((2 : ℝ) ^ e' * (addOp p n rh Y).getD i 0)
    have h2 := hS.err ((2 : ℝ) ^ e' * (addOp p n rh Y).getD i 0)
    have h3 : |(2 : ℝ) ^ e' * (addOp p n rh Y).getD i 0| ≤ GaddP p n π' ω (T0 + Em) i := by
      rw [abs_mul, abs_of_pos h2e]
      calc _ ≤ (2 : ℝ) ^ e' * (c * GaddP p n π' ω (T0 + Em) i) := mul_le_mul_of_nonneg_left (a2 i) h2e.le
        _ = _ := by rw [← mul_assoc, hcc, one_mul]
    linarith
  · rw [hT]
    exact hS.mem _ (F_zpow_mul p e' (a3 i))

/-- `b' = 2^{-m} min(b, c̄) + nη`, with `c̄ = 2^{e+1}` and `η` the paper's `η_0[m > 0]` -/
noncomputable def coreBp (e : ℤ) (m : ℕ) (b η : ℝ) : ℝ := (2 : ℝ) ^ (-(m : ℤ)) * min b ((2 : ℝ) ^ (e + 1)) + n * η

/-- `π'_i = 2^{-m} min(π_i, c̄) + η` -/
noncomputable def corePi (e : ℤ) (m : ℕ) (π : ℕ → ℝ) (η : ℝ) : ℕ → ℝ :=
  fun i => (2 : ℝ) ^ (-(m : ℤ)) * min (π i) ((2 : ℝ) ^ (e + 1)) + η

omit [Prec_gt_0 p] in
/-- `(E_m, ψ_m)` of Lemma 39, the scaling by `2^{-m}` moving each part by at most `η₁` and step (3)'s scaling back by
at most `η₂` -/
noncomputable def coreBound (η₁ η₂ : ℝ) (pos : Bool) (e : ℤ) (m : ℕ) (a b : ℝ) (π : ℕ → ℝ) (Fk : ℕ → ℕ → ℝ)
    (φ : ℕ → ℝ) (d' : ℕ) : ℝ × (ℕ → ℝ) :=
  coreE p n (coreT pos (coreBp n e m b η₁)) (coreG pos ((2 : ℝ) ^ (-(m : ℤ)) * a) (coreBp n e m b η₁))
    (core0 p n (coreT pos (coreBp n e m b η₁) 0) (2 * n * η₁) η₂ (corePi e m π η₁) (coreBp n e m b η₁) Fk φ d').1
    (core0 p n (coreT pos (coreBp n e m b η₁) 0) (2 * n * η₁) η₂ (corePi e m π η₁) (coreBp n e m b η₁) Fk φ d').2 m

/-- Lemma 39 (`lem:core`): steps (2) to (4) of EXP on `r` with `a ≤ |r| ≤ b` and `|r_i| ≤ π_i`, with `m` squarings,
degree `d'` and `U < c̄ = 2^{e+1}`, give `|t - (e^r - 1)| ≤ E_m` and `|t_i| ≤ ψ_{m,i}`, and `|e^r - 1| ≤ t̄_m`. The
scaling by `2^{-m}` moves each part by at most `η₁`, the paper's `η_0[m > 0]`, and step (3)'s scaling back by at most
`η₂`; where the first can lose, `e^{b'} ≤ 2`, as `b'` is near `2^{-s}` -/
theorem lemma_core (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {η₁ η₂ : ℝ} {S₁ S₂ : ℝ → ℝ}
    (hS₁ : Scl p η₁ S₁) (hS₂ : Scl p η₂ S₂) (r : ℕ → ℝ)
    (hr : ∀ i < n, F p (r i)) (R : ℝ) (hR : R = ∑ i ∈ range n, r i) (a b : ℝ) (ha : a ≤ |R|) (hb : |R| ≤ b)
    (π : ℕ → ℝ) (hπ : ∀ i < n, |r i| ≤ π i) (γ : ℝ) (hγ : (1 + u p) ^ n ≤ 1 + γ) (e : ℤ)
    (hU : expU p n γ r < (2 : ℝ) ^ (e + 1)) (m d' : ℕ) (hd : 1 ≤ d') (hbd : coreBp n e m b η₁ < d' + 2)
    (hb2 : 0 < η₁ → Real.exp (coreBp n e m b η₁) ≤ 2)
    (Fk : ℕ → ℕ → ℝ) (hF : ∀ k, ∀ i < n, F p (Fk k i)) (φ : ℕ → ℝ)
    (hφ : ∀ k, |∑ i ∈ range n, Fk k i - invF k| ≤ φ k) (pos : Bool) (hsgn : if pos then 0 ≤ R else R ≤ 0) :
    |∑ i ∈ range n, expCore p n S₁ S₂ e m r Fk d' i - (Real.exp R - 1)| ≤
        (coreBound p n η₁ η₂ pos e m a b π Fk φ d').1 ∧
      (∀ i < n, |expCore p n S₁ S₂ e m r Fk d' i| ≤ (coreBound p n η₁ η₂ pos e m a b π Fk φ d').2 i) ∧
      |Real.exp R - 1| ≤ coreT pos (coreBp n e m b η₁) m := by
  have hη₁ := hS₁.nonneg
  have hnη : (0 : ℝ) ≤ n * η₁ := mul_nonneg (Nat.cast_nonneg n) hη₁
  -- `∑|r_i| ≤ U < c̄`
  have hS := (expU_ge p n hn γ hγ r).trans_lt hU
  have hRc : |R| < (2 : ℝ) ^ (e + 1) := by rw [hR]; exact (abs_sum_le_sum_abs _ _).trans_lt hS
  have hric : ∀ i < n, |r i| < (2 : ℝ) ^ (e + 1) := fun i hi =>
    (single_le_sum (f := fun i => |r i|) (fun _ _ => abs_nonneg _) (mem_range.mpr hi)).trans_lt hS
  -- `r' = 2^{-m} r` rounded, and the exact `r* = 2^{-m} r`
  obtain ⟨c, hc⟩ : ∃ c, c = (2 : ℝ) ^ (-(m : ℤ)) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  obtain ⟨r', hr'⟩ : ∃ r' : ℕ → ℝ, r' = fun i => S₁ (c * r i) := ⟨_, rfl⟩
  have hr'F : ∀ i < n, F p (r' i) := fun i hi => by
    rw [hr', hc]; exact hS₁.mem _ (F_zpow_mul p _ (hr i hi))
  obtain ⟨Rs, hRs⟩ : ∃ Rs, Rs = c * R := ⟨_, rfl⟩
  obtain ⟨R', hR's⟩ : ∃ R', R' = ∑ i ∈ range n, r' i := ⟨_, rfl⟩
  obtain ⟨bp, hbp⟩ : ∃ bp, bp = coreBp n e m b η₁ := ⟨_, rfl⟩
  rw [← hbp] at hbd hb2
  have hRR : |R' - Rs| ≤ n * η₁ := by
    rw [hR's, hRs, hR, hr', mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun i _ => hS₁.err _).trans_eq ?_)
    rw [sum_const, card_range, nsmul_eq_mul]
  have hRsb : |Rs| ≤ bp := by
    rw [hRs, hbp, coreBp, ← hc, abs_mul, abs_of_pos hc0]
    linarith [mul_le_mul_of_nonneg_left (le_min hb hRc.le) hc0.le]
  have hR'b : |R'| ≤ bp := by
    have h1 := abs_sub_abs_le_abs_sub R' Rs
    have h2 : |Rs| ≤ c * min b ((2 : ℝ) ^ (e + 1)) := by
      rw [hRs, abs_mul, abs_of_pos hc0]
      exact mul_le_mul_of_nonneg_left (le_min hb hRc.le) hc0.le
    rw [hbp, coreBp, ← hc]
    linarith
  have hr'π : ∀ i < n, |r' i| ≤ corePi e m π η₁ i := fun i hi => by
    have h1 := abs_sub_abs_le_abs_sub (S₁ (c * r i)) (c * r i)
    have h2 := hS₁.err (c * r i)
    have h3 : |c * r i| ≤ c * min (π i) ((2 : ℝ) ^ (e + 1)) := by
      rw [abs_mul, abs_of_pos hc0]
      exact mul_le_mul_of_nonneg_left (le_min (hπ i hi) (hric i hi).le) hc0.le
    rw [hr']
    show |S₁ (c * r i)| ≤ (2 : ℝ) ^ (-(m : ℤ)) * min (π i) ((2 : ℝ) ^ (e + 1)) + η₁
    rw [← hc]
    linarith
  -- `|e^{r'} - e^{r*}| ≤ 2nη₁`
  have hD : |Real.exp R' - Real.exp Rs| ≤ 2 * n * η₁ := by
    rcases hη₁.eq_or_lt with h0 | h0
    · rw [← h0, mul_zero] at hRR ⊢
      rw [sub_eq_zero.mp (abs_nonpos_iff.mp hRR), sub_self, abs_zero]
    · have h1 := abs_exp_sub_exp_le ((le_abs_self R').trans hR'b) ((le_abs_self Rs).trans hRsb)
      have h2 : Real.exp bp * |R' - Rs| ≤ 2 * (n * η₁) :=
        mul_le_mul (hb2 h0) hRR (abs_nonneg _) (by norm_num)
      linarith
  have hRsa : c * a ≤ |Rs| := by
    rw [hRs, abs_mul, abs_of_pos hc0]
    exact mul_le_mul_of_nonneg_left ha hc0.le
  have hsgn' : if pos then 0 ≤ Rs else Rs ≤ 0 := by
    cases pos <;> simp only [Bool.false_eq_true, ite_true, ite_false] at hsgn ⊢ <;> rw [hRs]
    · exact mul_nonpos_of_nonneg_of_nonpos hc0.le hsgn
    · exact mul_nonneg hc0.le hsgn
  have hts := tstar_bound pos Rs (c * a) bp hRsb hRsa hsgn'
  -- `t*_{j+1} = 2t*_j + t*_j²`
  have hrec : ∀ j : ℕ, Real.exp (2 ^ (j + 1) * Rs) - 1 =
      2 * (Real.exp (2 ^ j * Rs) - 1) + (Real.exp (2 ^ j * Rs) - 1) ^ 2 := fun j => by
    rw [pow_succ, show (2 : ℝ) ^ j * 2 * Rs = 2 ^ j * Rs + 2 ^ j * Rs by ring, Real.exp_add]
    ring
  obtain ⟨T, hT⟩ : ∃ T, T = coreT pos bp := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = coreG pos (c * a) bp := ⟨_, rfl⟩
  obtain ⟨B0, hB0⟩ : ∃ B0, B0 = core0 p n (T 0) (2 * n * η₁) η₂ (corePi e m π η₁) bp Fk φ d' := ⟨_, rfl⟩
  obtain ⟨t0, ht0d⟩ : ∃ t0, t0 = expT0 p n S₂ (e - m) r' Fk d' := ⟨_, rfl⟩
  have h0 := core_t0 p n hp hn hA3 hS₂ r' hr'F _ hr'π R' bp hR's hR'b Fk hF φ hφ d' hd hbd (e - m) Rs (T 0)
    (2 * n * η₁) hD (by rw [hT]; simpa using (hts 0).1)
  rw [← hB0, ← ht0d] at h0
  -- the squarings
  have hind : ∀ j, |∑ i ∈ range n, (expSq p n)^[j] t0 i - (Real.exp (2 ^ j * Rs) - 1)| ≤
      (coreE p n T g B0.1 B0.2 j).1 ∧ (∀ i < n, |(expSq p n)^[j] t0 i| ≤ (coreE p n T g B0.1 B0.2 j).2 i) ∧
      ∀ i < n, F p ((expSq p n)^[j] t0 i) := by
    intro j
    induction j with
    | zero =>
      simp only [Function.iterate_zero, id, pow_zero, one_mul, coreE]
      exact h0
    | succ j ih =>
      obtain ⟨i1, i2, i3⟩ := ih
      rw [Function.iterate_succ_apply', hrec j]
      have hsq := core_sq p n hp hn hA3 _ i3 _ i2 (Real.exp (2 ^ j * Rs) - 1) _ (T j) (T (j + 1)) (g j) i1
        (by rw [hT]; exact (hts j).1) (by rw [← hrec j, hT]; exact (hts (j + 1)).1) (by rw [hg]; exact (hts j).2)
      exact hsq
  obtain ⟨f1, f2, -⟩ := hind m
  have hm : (2 : ℝ) ^ m * Rs = R := by
    rw [hRs, hc, ← mul_assoc, ← zpow_natCast, ← zpow_add₀ two_ne_zero, add_neg_cancel, zpow_zero, one_mul]
  rw [hm] at f1
  have hexp := (hts m).1
  rw [hm, hbp] at hexp
  have hcb : coreBound p n η₁ η₂ pos e m a b π Fk φ d' = coreE p n T g B0.1 B0.2 m := by
    rw [coreBound, hB0, hT, hg, hc, hbp]
  rw [hcb]
  have hcore : expCore p n S₁ S₂ e m r Fk d' = (expSq p n)^[m] t0 := by rw [expCore, ht0d, hr', hc]
  rw [hcore]
  exact ⟨f1, f2, hexp⟩

end ExpansionBounds
