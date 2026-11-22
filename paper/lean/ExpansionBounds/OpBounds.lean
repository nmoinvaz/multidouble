import ExpansionBounds.Levels
import ExpansionBounds.Parts

/-!
# Lemma 13 (a) and (b): from the levels to the result

Each operation ends with `Ren_n` of its levels `c_0, …, c_n`. Given `|c_m| ≤ X_m` and `|Z - ∑ c_m| ≤ F`, Theorem 9
(b) and (d) and Lemma 12 bound the error and the parts of the result, through `σ_l = ∑_{m ≥ l} X_m`,
`V_j = min(X_{j-1}, ū(1 + u)^{n-j} σ_{j-1})` and `W_k = ∑_{j > k} V_j`. The bounds of Lemma 11 grow with the inputs'
totals `A_m`, so bounds on the `A_m` give bounds on the levels.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ)

/-- `σ_l = ∑_{m ≥ l} X_m` over `X_0, …, X_n` -/
def sigmaX (n : ℕ) (X : ℕ → ℝ) (l : ℕ) : ℝ := ∑ m ∈ Ico l (n + 1), X m

/-- `V_j = min(X_{j-1}, ū(1 + u)^{n-j} σ_{j-1})` -/
noncomputable def Vb (n : ℕ) (X : ℕ → ℝ) (j : ℕ) : ℝ :=
  min (X (j - 1)) (us p * (1 + u p) ^ (n - j) * sigmaX n X (j - 1))

theorem abs_sub_le_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)

/-- `D_m` grows with the `A_m` -/
theorem levD_mono {A A' : ℕ → ℝ} {T : ℕ → ℕ} {uu : ℝ} (hu : 0 ≤ uu) (hA : ∀ m, A m ≤ A' m) (n : ℕ)
    (hTu : ∀ m < n, (T m : ℝ) * uu < 1) : ∀ m ≤ n, levD A T uu m ≤ levD A' T uu m := by
  intro m
  induction m with
  | zero => intro _; exact hA 0
  | succ m ih =>
    intro hm
    have h1 : 0 < 1 - (T m : ℝ) * uu := by linarith [hTu m (by omega)]
    have hc : 0 ≤ (T m : ℝ) * uu / (1 - T m * uu) := div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) h1.le
    have := mul_le_mul_of_nonneg_left (ih (by omega)) hc
    simp only [levD]
    rw [mul_div_right_comm, mul_div_right_comm (T m * uu)]
    linarith [hA (m + 1)]

variable [Prec_gt_0 p]

theorem vecSum_le_V (hp : 1 < p) (n : ℕ) (c : ℕ → ℝ) (hc : ∀ i ≤ n, F p (c i)) (X : ℕ → ℝ)
    (hX : ∀ m ≤ n, |c m| ≤ X m) (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n) : |vecSum p n c j| ≤ Vb p n X j := by
  obtain ⟨-, hd⟩ := vecSum_bounds p hp n c hc
  obtain ⟨h1, h2⟩ := hd j hj1 hjn
  have hσ : sigma n c (j - 1) ≤ sigmaX n X (j - 1) :=
    sum_le_sum fun m hm => hX m (by simp at hm; omega)
  refine le_min (h1.trans (hX _ (by omega))) (h2.trans ?_)
  exact mul_le_mul_of_nonneg_left hσ (mul_nonneg (us_nonneg p) (pow_nonneg (by linarith [u_pos p]) _))

/-- Lemma 13 (a) and (b) from (c): if the levels `c` have `|c_m| ≤ X_m` and `|Z - ∑ c_m| ≤ F`, then
`|Z - ∑ x_k| ≤ uⁿ Z̄ + (1 + uⁿ) F + ∑_{j=1}^n (uⁿ + u^{n+1-j}) V_j`, `|x_0| ≤ (1 + u)(Z̄ + F + W_1)` and
`|x_i| ≤ (1 + u)(u|x_{i-1}| + W_i)` for `1 ≤ i < n`, where the paper's `F = R + Δ` -/
theorem ren_of_levels (hp : 1 < p) (n : ℕ) (hn : 1 ≤ n) (c : ℕ → ℝ) (hc : ∀ i ≤ n, F p (c i)) (X : ℕ → ℝ)
    (hX : ∀ m ≤ n, |c m| ≤ X m) (Z Zb Fb : ℝ) (hZ : |Z| ≤ Zb) (hF : |Z - ∑ m ∈ range (n + 1), c m| ≤ Fb) :
    |Z - (ren p n n c).sum| ≤
        u p ^ n * Zb + (1 + u p ^ n) * Fb + ∑ j ∈ Ioc 0 n, (u p ^ n + u p ^ (n + 1 - j)) * Vb p n X j ∧
      |(ren p n n c).getD 0 0| ≤ (1 + u p) * (Zb + Fb + ∑ j ∈ Ioc 1 n, Vb p n X j) ∧
      ∀ i, 1 ≤ i → i ≤ n - 1 → |(ren p n n c).getD i 0| ≤
        (1 + u p) * (u p * |(ren p n n c).getD (i - 1) 0| + ∑ j ∈ Ioc i n, Vb p n X j) := by
  have hu := u_pos p
  have hus := us_nonneg p
  have husu := us_le_u p
  set S := ∑ m ∈ range (n + 1), c m with hSdef
  have hV : ∀ j ∈ Ioc 0 n, |vecSum p n c j| ≤ Vb p n X j := fun j hj =>
    vecSum_le_V p hp n c hc X hX j (mem_Ioc.mp hj).1 (mem_Ioc.mp hj).2
  have hS : |S| ≤ Zb + Fb := by
    have := abs_sub_abs_le_abs_sub S Z
    rw [abs_sub_comm] at this
    linarith
  -- `|v_0| ≤ |S| + ∑_{j ≥ 1} |v_j|`, by `∑ v_j = S`
  have hv0 : |vecSum p n c 0| ≤ Zb + Fb + ∑ j ∈ Ioc 0 n, Vb p n X j := by
    have h1 : vecSum p n c 0 = S - ∑ j ∈ Ioc 0 n, vecSum p n c j := by
      rw [hSdef, ← vecSum_sum p hp n c hc, sum_range_succ', sum_Ioc_zero]
      ring
    have h2 : |∑ j ∈ Ioc 0 n, vecSum p n c j| ≤ ∑ j ∈ Ioc 0 n, Vb p n X j :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum hV)
    rw [h1]
    linarith [abs_sub_le_add S (∑ j ∈ Ioc 0 n, vecSum p n c j)]
  -- Theorem 9 (b) at `k = 0`, with `ū ≤ u`
  have hE : |S - (ren p n n c).sum| ≤
      u p ^ n * (Zb + Fb + ∑ j ∈ Ioc 0 n, Vb p n X j) + ∑ j ∈ Ioc 0 n, u p ^ (n + 1 - j) * Vb p n X j := by
    have h := renErr_le p hp n hn c hc 0 (by omega)
    rw [Nat.sub_zero] at h
    refine h.trans (add_le_add ?_ ?_)
    · exact mul_le_mul (pow_le_pow_left₀ hus husu n) hv0 (abs_nonneg _) (pow_nonneg hu.le _)
    · exact sum_le_sum fun j hj =>
        mul_le_mul (pow_le_pow_left₀ hus husu _) (hV j hj) (abs_nonneg _) (pow_nonneg hu.le _)
  have hW : ∀ k, ∑ j ∈ Ioc k n, |vecSum p n c j| ≤ ∑ j ∈ Ioc k n, Vb p n X j := fun k =>
    sum_le_sum fun j hj => vecSum_le_V p hp n c hc X hX j (by simp at hj; omega) (mem_Ioc.mp hj).2
  obtain ⟨-, hx0, hxi⟩ := ren_parts p hp n hn c hc
  refine ⟨?_, ?_, fun i hi1 hi2 => ?_⟩
  · have hsplit : ∑ j ∈ Ioc 0 n, (u p ^ n + u p ^ (n + 1 - j)) * Vb p n X j =
        u p ^ n * ∑ j ∈ Ioc 0 n, Vb p n X j + ∑ j ∈ Ioc 0 n, u p ^ (n + 1 - j) * Vb p n X j := by
      rw [mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun _ _ => by ring
    rw [hsplit]
    calc |Z - (ren p n n c).sum| = |(Z - S) + (S - (ren p n n c).sum)| := by ring_nf
      _ ≤ |Z - S| + |S - (ren p n n c).sum| := abs_add_le _ _
      _ ≤ _ := by nlinarith [hF, hE]
  · exact hx0.trans (mul_le_mul_of_nonneg_left (by linarith [hW 1]) (by linarith))
  · exact (hxi i hi1 hi2).trans (mul_le_mul_of_nonneg_left (by linarith [hW i]) (by linarith))

end ExpansionBounds
