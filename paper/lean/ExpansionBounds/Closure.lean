import ExpansionBounds.Closed

/-!
# Theorem 17: the parts of the result, and closure under `H(θ')`

With levels within `L_m u^m M`, Theorem 9 (d) bounds the tail `W_k = ∑_{j>k} |v_j|` of VecSum by
`u^{k+1}(1 + u)^{n-1} Λ M`, and Lemma 12 unrolled bounds each part of `Ren_n` by
`u^i((1 + u)^i |x_0| + i u (1 + u)^{n+i-1} Λ M)`. When `|Z| ≥ ζM` and `ξ > 0`, the first part is at least `ξM`, so the
parts of the result satisfy the inequalities of `H(θ')` (`Htheta`). The `θ'` here is any number at least the paper's
maximum of `i`-th roots; the paper's `H(θ')` also needs `θ'u ≤ 1/4`.
-/

namespace ExpansionBounds

open Finset

/-- `(t + 1) x^t ≤ 1` for `0 ≤ x ≤ 1/2` -/
theorem succ_mul_pow_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : ∀ t : ℕ, ((t : ℝ) + 1) * x ^ t ≤ 1
  | 0 => by simp
  | t + 1 => by
    have ih := succ_mul_pow_le x h0 h1 t
    have hxt := pow_nonneg h0 t
    have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    push_cast
    rw [pow_succ]
    nlinarith [mul_nonneg ht (mul_nonneg hxt h0)]

variable (p : ℤ) [Prec_gt_0 p]

/-- the tail of VecSum for levels within `L_m u^m M`: `W_k ≤ u^{k+1}(1 + u)^{n-1} Λ M` -/
theorem W_closed (hp : 1 < p) (n : ℕ) (c : ℕ → ℝ) (hc : ∀ i ≤ n, F p (c i)) (L : ℕ → ℝ) (hL0 : ∀ m, 0 ≤ L m)
    (M : ℝ) (hM : 0 ≤ M) (hL : ∀ m ≤ n, |c m| ≤ L m * u p ^ m * M) (k : ℕ) (hk : 1 ≤ k) :
    ∑ j ∈ Ioc k n, |vecSum p n c j| ≤ u p ^ (k + 1) * (1 + u p) ^ (n - 1) * (∑ m ∈ range (n + 1), L m) * M := by
  have hu := u_pos p
  have hu2 := u_le_half p hp
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, g = fun m => L m * u p ^ m * M := ⟨_, rfl⟩
  have hg0 : ∀ m, 0 ≤ g m := fun m => by rw [hg]; exact mul_nonneg (mul_nonneg (hL0 m) (by positivity)) hM
  -- `|v_j| ≤ V_j ≤ u(1 + u)^{n-1} ∑_{m ≥ j-1} g_m`
  have hV : ∀ j ∈ Ioc k n, |vecSum p n c j| ≤ u p * (1 + u p) ^ (n - 1) * ∑ m ∈ Ico (j - 1) (n + 1), g m := by
    intro j hj
    rw [mem_Ioc] at hj
    have h := vecSum_le_V p hp n c hc g (fun m hm => by rw [hg]; exact hL m hm) j (by omega) hj.2
    refine h.trans ((min_le_right _ _).trans ?_)
    have hσ : 0 ≤ sigmaX n g (j - 1) := sum_nonneg fun m _ => hg0 m
    have hp1 : (1 + u p) ^ (n - j) ≤ (1 + u p) ^ (n - 1) := pow_le_pow_right₀ (by linarith) (by omega)
    calc us p * (1 + u p) ^ (n - j) * sigmaX n g (j - 1) ≤ u p * (1 + u p) ^ (n - 1) * sigmaX n g (j - 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul (us_le_u p) hp1 (by positivity) hu.le) hσ
      _ = _ := rfl
  refine (sum_le_sum hV).trans ?_
  rw [← mul_sum]
  -- swap the sums: each `g_m` with `k ≤ m ≤ n` appears `min(n, m + 1) - k ≤ m - k + 1` times
  have hswap : ∑ j ∈ Ioc k n, ∑ m ∈ Ico (j - 1) (n + 1), g m =
      ∑ m ∈ Ico k (n + 1), ∑ _j ∈ Ioc k (min n (m + 1)), g m := by
    refine sum_comm' fun j m => ?_
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [hswap]
  have hterm : ∀ m ∈ Ico k (n + 1), ∑ _j ∈ Ioc k (min n (m + 1)), g m ≤ u p ^ k * (L m * M) := by
    intro m hm
    rw [mem_Ico] at hm
    rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, hg]
    have hcard : ((min n (m + 1) - k : ℕ) : ℝ) ≤ ((m - k : ℕ) : ℝ) + 1 := by
      have : min n (m + 1) - k ≤ m - k + 1 := by omega
      exact_mod_cast this
    have hpow : ((m - k : ℕ) + 1 : ℝ) * u p ^ (m - k) ≤ 1 := succ_mul_pow_le (u p) hu.le hu2 (m - k)
    have hum : u p ^ m = u p ^ k * u p ^ (m - k) := by rw [← pow_add]; congr 1; omega
    have hLM : 0 ≤ L m * M := mul_nonneg (hL0 m) hM
    calc ((min n (m + 1) - k : ℕ) : ℝ) * (L m * u p ^ m * M)
        ≤ (((m - k : ℕ) : ℝ) + 1) * (L m * u p ^ m * M) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg (mul_nonneg (hL0 m) (by positivity)) hM)
      _ = u p ^ k * (L m * M) * ((((m - k : ℕ) : ℝ) + 1) * u p ^ (m - k)) := by rw [hum]; ring
      _ ≤ u p ^ k * (L m * M) * 1 := mul_le_mul_of_nonneg_left hpow (mul_nonneg (by positivity) hLM)
      _ = _ := mul_one _
  have hsub : ∑ m ∈ Ico k (n + 1), L m ≤ ∑ m ∈ range (n + 1), L m := by
    rw [range_eq_Ico]
    exact sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_left (by omega)) fun m _ _ => hL0 m
  calc u p * (1 + u p) ^ (n - 1) * ∑ m ∈ Ico k (n + 1), ∑ _j ∈ Ioc k (min n (m + 1)), g m
      ≤ u p * (1 + u p) ^ (n - 1) * ∑ m ∈ Ico k (n + 1), u p ^ k * (L m * M) :=
        mul_le_mul_of_nonneg_left (sum_le_sum hterm) (by positivity)
    _ = u p ^ (k + 1) * (1 + u p) ^ (n - 1) * (∑ m ∈ Ico k (n + 1), L m) * M := by
        rw [← mul_sum, ← sum_mul, pow_succ]; ring
    _ ≤ _ := by gcongr

/-- Lemma 12 unrolled: `|x_i| ≤ u^i((1 + u)^i |x_0| + i u (1 + u)^{n+i-1} Λ M)` for `i ≤ n - 1` -/
theorem parts_closed (hp : 1 < p) (n : ℕ) (hn : 1 ≤ n) (c : ℕ → ℝ) (hc : ∀ i ≤ n, F p (c i)) (L : ℕ → ℝ)
    (hL0 : ∀ m, 0 ≤ L m) (M : ℝ) (hM : 0 ≤ M) (hL : ∀ m ≤ n, |c m| ≤ L m * u p ^ m * M) :
    ∀ i, i ≤ n - 1 → |(ren p n n c).getD i 0| ≤
      u p ^ i * ((1 + u p) ^ i * |(ren p n n c).getD 0 0| +
        i * u p * (1 + u p) ^ (n + i - 1) * (∑ m ∈ range (n + 1), L m) * M) := by
  have hu := u_pos p
  obtain ⟨-, -, h3⟩ := ren_parts p hp n hn c hc
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = ∑ m ∈ range (n + 1), L m := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; exact sum_nonneg fun m _ => hL0 m
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have hW := W_closed p hp n c hc L hL0 M hM hL (i + 1) (by omega)
    rw [← hΛ] at hW ih ⊢
    have hx := h3 (i + 1) (by omega) hi
    rw [Nat.add_sub_cancel] at hx
    have ih' := ih (by omega)
    obtain ⟨x0, hx0⟩ : ∃ x0, x0 = |(ren p n n c).getD 0 0| := ⟨_, rfl⟩
    rw [← hx0] at ih' ⊢
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [show k + 1 + i - 1 = k + i by omega] at ih'
    rw [show k + 1 + (i + 1) - 1 = k + i + 1 by omega]
    rw [show k + 1 - 1 = k by omega] at hW
    have hq : 1 ≤ 1 + u p := by linarith
    have hqi : (1 + u p) ^ k ≤ (1 + u p) ^ (k + i) := pow_le_pow_right₀ hq (by omega)
    have hA : 0 ≤ Λ * M := mul_nonneg hΛ0 hM
    calc |(ren p (k + 1) (k + 1) c).getD (i + 1) 0|
        ≤ (1 + u p) * (u p * |(ren p (k + 1) (k + 1) c).getD i 0| +
            ∑ j ∈ Ioc (i + 1) (k + 1), |vecSum p (k + 1) c j|) := hx
      _ ≤ (1 + u p) * (u p * (u p ^ i * ((1 + u p) ^ i * x0 + i * u p * (1 + u p) ^ (k + i) * Λ * M)) +
            u p ^ (i + 1 + 1) * (1 + u p) ^ k * Λ * M) := by gcongr
      _ = u p ^ (i + 1) * ((1 + u p) ^ (i + 1) * x0 + i * u p * (1 + u p) ^ (k + i + 1) * Λ * M) +
            u p ^ (i + 2) * ((1 + u p) ^ (k + 1) * (Λ * M)) := by ring
      _ ≤ u p ^ (i + 1) * ((1 + u p) ^ (i + 1) * x0 + i * u p * (1 + u p) ^ (k + i + 1) * Λ * M) +
            u p ^ (i + 2) * ((1 + u p) ^ (k + i + 1) * (Λ * M)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq (by omega)) hA) (by positivity))
      _ = _ := by push_cast; ring

/-- Theorem 17's core: for levels within `L_m u^m M` summing to within `RΔ u^{n+1} M` of `Z`, the parts of `Ren_n`
satisfy the upper bound, and if `|Z| ≥ ζM` with `ξ > 0`, `|x_0| ≥ ξM` and `x` satisfies `H(θ')` for each `θ'` with
`(1 + u)^i + i u (1 + u)^{n+i-1} Λ/ξ ≤ θ'^i` -/
theorem closure_core (hp : 1 < p) (n : ℕ) (hn : 1 ≤ n) (c : ℕ → ℝ) (hc : ∀ i ≤ n, F p (c i)) (L : ℕ → ℝ)
    (hL0 : ∀ m, 0 ≤ L m) (M : ℝ) (hM : 0 ≤ M) (hL : ∀ m ≤ n, |c m| ≤ L m * u p ^ m * M) (Z RΔ : ℝ)
    (hZ : |Z - ∑ m ∈ range (n + 1), c m| ≤ RΔ * u p ^ (n + 1) * M) (ζ : ℝ) (hζ : ζ * M ≤ |Z|)
    (hξ : 0 < (ζ - RΔ * u p ^ (n + 1) - u p ^ 2 * (1 + u p) ^ (n - 1) * ∑ m ∈ range (n + 1), L m) / (1 + u p)) :
    (ζ - RΔ * u p ^ (n + 1) - u p ^ 2 * (1 + u p) ^ (n - 1) * ∑ m ∈ range (n + 1), L m) / (1 + u p) * M ≤
        |(ren p n n c).getD 0 0| ∧
      ∀ θ' : ℝ, (∀ i, 1 ≤ i → i < n → (1 + u p) ^ i + i * u p * (1 + u p) ^ (n + i - 1) *
        (∑ m ∈ range (n + 1), L m) / ((ζ - RΔ * u p ^ (n + 1) - u p ^ 2 * (1 + u p) ^ (n - 1) *
          ∑ m ∈ range (n + 1), L m) / (1 + u p)) ≤ θ' ^ i) →
        Htheta p n θ' fun i => (ren p n n c).getD i 0 := by
  have hu := u_pos p
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = ∑ m ∈ range (n + 1), L m := ⟨_, rfl⟩
  rw [← hΛ] at hξ ⊢
  obtain ⟨ξ, hξd⟩ : ∃ ξ, ξ = (ζ - RΔ * u p ^ (n + 1) - u p ^ 2 * (1 + u p) ^ (n - 1) * Λ) / (1 + u p) := ⟨_, rfl⟩
  rw [← hξd] at hξ ⊢
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ m ∈ range (n + 1), c m := ⟨_, rfl⟩
  rw [← hS] at hZ
  obtain ⟨h1, -, -⟩ := ren_parts p hp n hn c hc
  rw [← hS] at h1
  have hW := W_closed p hp n c hc L hL0 M hM hL 1 le_rfl
  rw [← hΛ, show 1 + 1 = 2 by rfl] at hW
  -- `|x_0| ≥ ξM`
  have hx0 : ξ * M ≤ |(ren p n n c).getD 0 0| := by
    refine le_trans ?_ h1
    have hSZ : ζ * M - RΔ * u p ^ (n + 1) * M ≤ |S| := by
      have := abs_sub_abs_le_abs_sub Z S
      linarith
    rw [le_div_iff₀ (by linarith), hξd, div_mul_eq_mul_div, div_mul_cancel₀ _ (by linarith)]
    linarith
  refine ⟨hx0, fun θ' hθ' i hi1 hin => ?_⟩
  have hpart := parts_closed p hp n hn c hc L hL0 M hM hL i (by omega)
  rw [← hΛ] at hpart
  obtain ⟨x0, hx0d⟩ : ∃ x0, x0 = |(ren p n n c).getD 0 0| := ⟨_, rfl⟩
  rw [← hx0d] at hpart hx0 ⊢
  have hMx : M ≤ x0 / ξ := by rw [le_div_iff₀ hξ, mul_comm]; exact hx0
  have hx00 : 0 ≤ x0 := by rw [hx0d]; exact abs_nonneg _
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; exact sum_nonneg fun m _ => hL0 m
  have hc0 : 0 ≤ (i : ℝ) * u p * (1 + u p) ^ (n + i - 1) * Λ := by positivity
  calc |(ren p n n c).getD i 0| ≤ u p ^ i * ((1 + u p) ^ i * x0 + i * u p * (1 + u p) ^ (n + i - 1) * Λ * M) := hpart
    _ ≤ u p ^ i * ((1 + u p) ^ i * x0 + i * u p * (1 + u p) ^ (n + i - 1) * Λ * (x0 / ξ)) := by
        gcongr
    _ = u p ^ i * ((1 + u p) ^ i + i * u p * (1 + u p) ^ (n + i - 1) * Λ / ξ) * x0 := by
        field_simp
    _ ≤ u p ^ i * θ' ^ i * x0 := by gcongr; exact hθ' i hi1 hin
    _ = (θ' * u p) ^ i * x0 := by rw [mul_pow]; ring

variable (n : ℕ)

omit [Prec_gt_0 p] in
/-- the tail of an `H(θ)` expansion: `|a - a_0| ≤ ρ/(1 - ρ) |a_0|` for `ρ < 1` -/
theorem Htheta_tail (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 ≤ θ) (hρ : θ * u p < 1) (a : ℕ → ℝ) (hH : Htheta p n θ a) :
    |∑ i ∈ range n, a i - a 0| ≤ θ * u p / (1 - θ * u p) * |a 0| := by
  obtain ⟨ρ, hρd⟩ : ∃ ρ, ρ = θ * u p := ⟨_, rfl⟩
  rw [← hρd] at hρ ⊢
  have hρ0 : 0 ≤ ρ := by rw [hρd]; exact mul_nonneg hθ (u_pos p).le
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [sum_range_succ', add_sub_cancel_right]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i ∈ range k, |a (i + 1)| ≤ ∑ i ∈ range k, ρ ^ (i + 1) * |a 0| :=
        sum_le_sum fun i hi => by rw [hρd]; exact hH (i + 1) (by omega) (by rw [mem_range] at hi; omega)
    _ = ρ * |a 0| * ∑ i ∈ range k, ρ ^ i := by rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
    _ ≤ ρ * |a 0| * (1 / (1 - ρ)) := mul_le_mul_of_nonneg_left (geom_le ρ hρ0 hρ k) (by positivity)
    _ = ρ / (1 - ρ) * |a 0| := by ring

omit [Prec_gt_0 p] in
/-- `(eq:a0)` as a lower bound: `|a| ≥ (1 - 2ρ)/(1 - ρ) |a_0|` -/
theorem Htheta_lower (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 ≤ θ) (hρ : 2 * (θ * u p) < 1) (a : ℕ → ℝ) (hH : Htheta p n θ a) :
    (1 - 2 * (θ * u p)) / (1 - θ * u p) * |a 0| ≤ |∑ i ∈ range n, a i| := by
  have hρ0 : 0 ≤ θ * u p := mul_nonneg hθ (u_pos p).le
  have ht := Htheta_tail p n hn θ hθ (by linarith) a hH
  have h1 := abs_sub_abs_le_abs_sub (a 0) (∑ i ∈ range n, a i)
  rw [abs_sub_comm] at h1
  have he : (1 - 2 * (θ * u p)) / (1 - θ * u p) = 1 - θ * u p / (1 - θ * u p) := by
    field_simp [show 1 - θ * u p ≠ 0 by linarith]; ring
  rw [he]
  linarith

omit [Prec_gt_0 p] in
/-- `ζ = ((1 - 2ρ)/(1 - ρ))²` serves for MUL -/
theorem zeta_mul (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 ≤ θ) (hρ : 2 * (θ * u p) < 1) (a b : ℕ → ℝ) (hHa : Htheta p n θ a)
    (hHb : Htheta p n θ b) :
    ((1 - 2 * (θ * u p)) / (1 - θ * u p)) ^ 2 * |a 0 * b 0| ≤ |(∑ i ∈ range n, a i) * (∑ j ∈ range n, b j)| := by
  have hc : 0 ≤ (1 - 2 * (θ * u p)) / (1 - θ * u p) := div_nonneg (by linarith) (by nlinarith [u_pos p])
  rw [abs_mul, abs_mul, sq]
  calc (1 - 2 * (θ * u p)) / (1 - θ * u p) * ((1 - 2 * (θ * u p)) / (1 - θ * u p)) * (|a 0| * |b 0|) =
        ((1 - 2 * (θ * u p)) / (1 - θ * u p) * |a 0|) * ((1 - 2 * (θ * u p)) / (1 - θ * u p) * |b 0|) := by ring
    _ ≤ _ := mul_le_mul (Htheta_lower p n hn θ hθ hρ a hHa) (Htheta_lower p n hn θ hθ hρ b hHb)
        (mul_nonneg hc (abs_nonneg _)) (abs_nonneg _)

omit [Prec_gt_0 p] in
/-- `ζ = (1 - 2ρ)/(1 - ρ)` serves for MULF -/
theorem zeta_mulf (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 ≤ θ) (hρ : 2 * (θ * u p) < 1) (a : ℕ → ℝ) (b : ℝ)
    (hHa : Htheta p n θ a) :
    (1 - 2 * (θ * u p)) / (1 - θ * u p) * |a 0 * b| ≤ |(∑ i ∈ range n, a i) * b| := by
  rw [abs_mul, abs_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (Htheta_lower p n hn θ hθ hρ a hHa) (abs_nonneg _)

omit [Prec_gt_0 p] in
/-- `|x + y| = |x| + |y|` when `xy ≥ 0` -/
theorem abs_add_of_mul_nonneg {x y : ℝ} (h : 0 ≤ x * y) : |x + y| = |x| + |y| := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hx, abs_of_nonneg hy, abs_of_nonneg (add_nonneg hx hy)]
  · have : x * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx hy
    rcases mul_eq_zero.mp (le_antisymm this h) with h0 | h0 <;> simp [h0]
  · have : x * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hx hy
    rcases mul_eq_zero.mp (le_antisymm this h) with h0 | h0 <;> simp [h0]
  · rw [abs_of_nonpos hx, abs_of_nonpos hy, abs_of_nonpos (add_nonpos hx hy)]; ring

omit [Prec_gt_0 p] in
/-- `ζ = (1 - 2ρ)/(1 - ρ)` serves for ADD when `a_0` and `b_0` have one sign -/
theorem zeta_add (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 ≤ θ) (hρ : 2 * (θ * u p) < 1) (a b : ℕ → ℝ) (hHa : Htheta p n θ a)
    (hHb : Htheta p n θ b) (hs : 0 ≤ a 0 * b 0) :
    (1 - 2 * (θ * u p)) / (1 - θ * u p) * (|a 0| + |b 0|) ≤ |∑ i ∈ range n, a i + ∑ i ∈ range n, b i| := by
  have hρ0 : 0 ≤ θ * u p := mul_nonneg hθ (u_pos p).le
  have ha := Htheta_tail p n hn θ hθ (by linarith) a hHa
  have hb := Htheta_tail p n hn θ hθ (by linarith) b hHb
  have h0 := abs_add_of_mul_nonneg hs
  have hsplit : ∑ i ∈ range n, a i + ∑ i ∈ range n, b i =
      (a 0 + b 0) + ((∑ i ∈ range n, a i - a 0) + (∑ i ∈ range n, b i - b 0)) := by ring
  have h1 := abs_sub_abs_le_abs_sub (a 0 + b 0) (-((∑ i ∈ range n, a i - a 0) + (∑ i ∈ range n, b i - b 0)))
  rw [sub_neg_eq_add, ← hsplit, abs_neg] at h1
  have h2 := abs_add_le (∑ i ∈ range n, a i - a 0) (∑ i ∈ range n, b i - b 0)
  have he : (1 - 2 * (θ * u p)) / (1 - θ * u p) = 1 - θ * u p / (1 - θ * u p) := by
    field_simp [show 1 - θ * u p ≠ 0 by linarith]; ring
  rw [he]
  nlinarith

omit [Prec_gt_0 p] in
/-- `ζ = (1 - 2ρ)/(1 - ρ)` serves for ADDF when `a_0` and `b` have one sign -/
theorem zeta_addf (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 ≤ θ) (hρ : 2 * (θ * u p) < 1) (a : ℕ → ℝ) (b : ℝ) (hHa : Htheta p n θ a)
    (hs : 0 ≤ a 0 * b) :
    (1 - 2 * (θ * u p)) / (1 - θ * u p) * (|a 0| + |b|) ≤ |∑ i ∈ range n, a i + b| := by
  have hρ0 : 0 ≤ θ * u p := mul_nonneg hθ (u_pos p).le
  have ha := Htheta_tail p n hn θ hθ (by linarith) a hHa
  have h0 := abs_add_of_mul_nonneg hs
  have h1 := abs_sub_abs_le_abs_sub (a 0 + b) (-(∑ i ∈ range n, a i - a 0))
  rw [sub_neg_eq_add, show a 0 + b + (∑ i ∈ range n, a i - a 0) = ∑ i ∈ range n, a i + b by ring, abs_neg] at h1
  have hq : 0 ≤ θ * u p / (1 - θ * u p) := div_nonneg hρ0 (by linarith)
  have he : (1 - 2 * (θ * u p)) / (1 - θ * u p) = 1 - θ * u p / (1 - θ * u p) := by
    field_simp [show 1 - θ * u p ≠ 0 by linarith]; ring
  rw [he]
  nlinarith [abs_nonneg b, mul_nonneg hq (abs_nonneg b)]

/-- Theorem 17 (`thm:t5`) for MUL: the parts of `x = MUL(a, b)` within `u^i((1 + u)^i|x_0| + i u (1 + u)^{n+i-1} Λ M)`,
and for `|ab| ≥ ζM` with `ξ > 0`, `|x_0| ≥ ξM` and `x` on `H(θ')` -/
theorem thm17_mul (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (θ : ℝ) (hθ : 0 < θ)
    (a b : ℕ → ℝ) (ha : ∀ i < n, F p (a i)) (hb : ∀ j < n, F p (b j)) (hHa : Htheta p n θ a)
    (hHb : Htheta p n θ b) :
    (∀ i, i ≤ n - 1 → |(mulOp p n a b).getD i 0| ≤ u p ^ i * ((1 + u p) ^ i * |(mulOp p n a b).getD 0 0| +
        i * u p * (1 + u p) ^ (n + i - 1) * (∑ m ∈ range (n + 1), mulL p n θ m) * |a 0 * b 0|)) ∧
      ∀ ζ : ℝ, ζ * |a 0 * b 0| ≤ |(∑ i ∈ range n, a i) * (∑ j ∈ range n, b j)| →
        0 < (ζ - (((n ^ 2 + n - 1 : ℕ) : ℝ) * mulL p n θ n + thmDelta p n θ) * u p ^ (n + 1) -
          u p ^ 2 * (1 + u p) ^ (n - 1) * ∑ m ∈ range (n + 1), mulL p n θ m) / (1 + u p) →
        (ζ - (((n ^ 2 + n - 1 : ℕ) : ℝ) * mulL p n θ n + thmDelta p n θ) * u p ^ (n + 1) -
          u p ^ 2 * (1 + u p) ^ (n - 1) * ∑ m ∈ range (n + 1), mulL p n θ m) / (1 + u p) * |a 0 * b 0| ≤
            |(mulOp p n a b).getD 0 0| ∧
          ∀ θ' : ℝ, (∀ i, 1 ≤ i → i < n → (1 + u p) ^ i + i * u p * (1 + u p) ^ (n + i - 1) *
            (∑ m ∈ range (n + 1), mulL p n θ m) / ((ζ - (((n ^ 2 + n - 1 : ℕ) : ℝ) * mulL p n θ n +
              thmDelta p n θ) * u p ^ (n + 1) - u p ^ 2 * (1 + u p) ^ (n - 1) *
                ∑ m ∈ range (n + 1), mulL p n θ m) / (1 + u p)) ≤ θ' ^ i) →
            Htheta p n θ' fun i => (mulOp p n a b).getD i 0 := by
  obtain ⟨t1, t2, -, -⟩ := thm14_mul p n hp hn hA3 θ hθ a b ha hb hHa hHb
  obtain ⟨-, -, -, -, c5⟩ := mulOps_levels p n hp hn a b _ _ ha hb (Htheta_le p n hHa) (Htheta_le p n hHb) hA3
  have hne : mulOps p n a b ≠ [] := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp [mulOps, List.range_succ]
  have hlast := runOps_last_mem p n _ hne LState.init
  have hL := t1 _ (List.mem_cons_of_mem _ hlast)
  have hL0 := mulL_nonneg p n hn hA3 θ hθ
  exact ⟨parts_closed p hp n hn _ (fun i _ => c5 i) _ hL0 _ (abs_nonneg _) hL, fun ζ hζ hξ =>
    closure_core p hp n hn _ (fun i _ => c5 i) _ hL0 _ (abs_nonneg _) hL _ _ t2 ζ hζ hξ⟩

/-- Theorem 17 for ADD, with `M = |a_0| + |b_0|` -/
theorem thm17_add (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (θ : ℝ) (hθ : 0 < θ)
    (a b : ℕ → ℝ) (ha : ∀ i < n, F p (a i)) (hb : ∀ j < n, F p (b j)) (hHa : Htheta p n θ a)
    (hHb : Htheta p n θ b) :
    (∀ i, i ≤ n - 1 → |(addOp p n a b).getD i 0| ≤ u p ^ i * ((1 + u p) ^ i * |(addOp p n a b).getD 0 0| +
        i * u p * (1 + u p) ^ (n + i - 1) * (∑ m ∈ range (n + 1), pairL p n θ m) * (|a 0| + |b 0|))) ∧
      ∀ ζ : ℝ, ζ * (|a 0| + |b 0|) ≤ |∑ i ∈ range n, a i + ∑ i ∈ range n, b i| →
        0 < (ζ - ((n - 1 : ℕ) : ℝ) * pairL p n θ n * u p ^ (n + 1) -
          u p ^ 2 * (1 + u p) ^ (n - 1) * ∑ m ∈ range (n + 1), pairL p n θ m) / (1 + u p) →
        (ζ - ((n - 1 : ℕ) : ℝ) * pairL p n θ n * u p ^ (n + 1) -
          u p ^ 2 * (1 + u p) ^ (n - 1) * ∑ m ∈ range (n + 1), pairL p n θ m) / (1 + u p) * (|a 0| + |b 0|) ≤
            |(addOp p n a b).getD 0 0| ∧
          ∀ θ' : ℝ, (∀ i, 1 ≤ i → i < n → (1 + u p) ^ i + i * u p * (1 + u p) ^ (n + i - 1) *
            (∑ m ∈ range (n + 1), pairL p n θ m) / ((ζ - ((n - 1 : ℕ) : ℝ) * pairL p n θ n * u p ^ (n + 1) -
              u p ^ 2 * (1 + u p) ^ (n - 1) * ∑ m ∈ range (n + 1), pairL p n θ m) / (1 + u p)) ≤ θ' ^ i) →
            Htheta p n θ' fun i => (addOp p n a b).getD i 0 := by
  obtain ⟨t1, t2, -, -⟩ := thm14_add p n hp hn hA3 θ hθ a b ha hb hHa hHb
  have hne : addOps p n a b ≠ [] := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp [addOps, pairOps, List.range_succ]
  have hlast := runOps_last_mem p n _ hne LState.init
  have hL := t1 _ (List.mem_cons_of_mem _ hlast)
  have hL0 := pairL_nonneg p n hA3 θ hθ
  have hF := fun i (_ : i ≤ n) => addLevels_F p n hp hn hA3 a b ha hb i
  have hM : 0 ≤ |a 0| + |b 0| := by positivity
  exact ⟨parts_closed p hp n hn _ hF _ hL0 _ hM hL, fun ζ hζ hξ =>
    closure_core p hp n hn _ hF _ hL0 _ hM hL _ _ (t2.trans_eq (by ring)) ζ hζ hξ⟩

/-- Theorem 17 for MULF, with `M = |a_0 b|` -/
theorem thm17_mulf (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (θ : ℝ) (hθ : 0 < θ)
    (a : ℕ → ℝ) (b : ℝ) (ha : ∀ i < n, F p (a i)) (hb : F p b) (hHa : Htheta p n θ a) :
    (∀ i, i ≤ n - 1 → |(mulfOp p n a b).getD i 0| ≤ u p ^ i * ((1 + u p) ^ i * |(mulfOp p n a b).getD 0 0| +
        i * u p * (1 + u p) ^ (n + i - 1) * (∑ m ∈ range (n + 1), pairL p n θ m) * |a 0 * b|)) ∧
      ∀ ζ : ℝ, ζ * |a 0 * b| ≤ |(∑ i ∈ range n, a i) * b| →
        0 < (ζ - ((n - 1 : ℕ) : ℝ) * pairL p n θ n * u p ^ (n + 1) -
          u p ^ 2 * (1 + u p) ^ (n - 1) * ∑ m ∈ range (n + 1), pairL p n θ m) / (1 + u p) →
        (ζ - ((n - 1 : ℕ) : ℝ) * pairL p n θ n * u p ^ (n + 1) -
          u p ^ 2 * (1 + u p) ^ (n - 1) * ∑ m ∈ range (n + 1), pairL p n θ m) / (1 + u p) * |a 0 * b| ≤
            |(mulfOp p n a b).getD 0 0| ∧
          ∀ θ' : ℝ, (∀ i, 1 ≤ i → i < n → (1 + u p) ^ i + i * u p * (1 + u p) ^ (n + i - 1) *
            (∑ m ∈ range (n + 1), pairL p n θ m) / ((ζ - ((n - 1 : ℕ) : ℝ) * pairL p n θ n * u p ^ (n + 1) -
              u p ^ 2 * (1 + u p) ^ (n - 1) * ∑ m ∈ range (n + 1), pairL p n θ m) / (1 + u p)) ≤ θ' ^ i) →
            Htheta p n θ' fun i => (mulfOp p n a b).getD i 0 := by
  obtain ⟨t1, t2, -, -⟩ := thm14_mulf p n hp hn hA3 θ hθ a b ha hb hHa
  have hne : mulfOps p n a b ≠ [] := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp [mulfOps, pairOps, List.range_succ]
  have hlast := runOps_last_mem p n _ hne LState.init
  have hL := t1 _ (List.mem_cons_of_mem _ hlast)
  have hL0 := pairL_nonneg p n hA3 θ hθ
  have hF := fun i (_ : i ≤ n) => mulfLevels_F p n hp hn hA3 a b ha hb i
  exact ⟨parts_closed p hp n hn _ hF _ hL0 _ (abs_nonneg _) hL, fun ζ hζ hξ =>
    closure_core p hp n hn _ hF _ hL0 _ (abs_nonneg _) hL _ _ (t2.trans_eq (by ring)) ζ hζ hξ⟩

/-- Theorem 17 for ADDF, with `M = |a_0| + |b|` and `R_n = Δ_n = 0` -/
theorem thm17_addf (hp : 1 < p) (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 < θ) (a : ℕ → ℝ) (b : ℝ) (ha : ∀ i < n, F p (a i))
    (hb : F p b) (hHa : Htheta p n θ a) :
    (∀ i, i ≤ n - 1 → |(addfOp p n a b).getD i 0| ≤ u p ^ i * ((1 + u p) ^ i * |(addfOp p n a b).getD 0 0| +
        i * u p * (1 + u p) ^ (n + i - 1) * (∑ m ∈ range (n + 1), addfL p n θ m) * (|a 0| + |b|))) ∧
      ∀ ζ : ℝ, ζ * (|a 0| + |b|) ≤ |∑ i ∈ range n, a i + b| →
        0 < (ζ - 0 * u p ^ (n + 1) - u p ^ 2 * (1 + u p) ^ (n - 1) * ∑ m ∈ range (n + 1), addfL p n θ m) /
          (1 + u p) →
        (ζ - 0 * u p ^ (n + 1) - u p ^ 2 * (1 + u p) ^ (n - 1) * ∑ m ∈ range (n + 1), addfL p n θ m) /
            (1 + u p) * (|a 0| + |b|) ≤ |(addfOp p n a b).getD 0 0| ∧
          ∀ θ' : ℝ, (∀ i, 1 ≤ i → i < n → (1 + u p) ^ i + i * u p * (1 + u p) ^ (n + i - 1) *
            (∑ m ∈ range (n + 1), addfL p n θ m) / ((ζ - 0 * u p ^ (n + 1) - u p ^ 2 * (1 + u p) ^ (n - 1) *
              ∑ m ∈ range (n + 1), addfL p n θ m) / (1 + u p)) ≤ θ' ^ i) →
            Htheta p n θ' fun i => (addfOp p n a b).getD i 0 := by
  obtain ⟨t1, t2⟩ := thm14_addf p n hp hn θ hθ a b ha hb hHa
  have hF : ∀ i ≤ n, F p (addfLevels p n a b i) := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hch := addf_chain p (n' + 1) hp a b ha hb (fun i => |a i|) (fun _ _ => le_rfl) _ le_rfl
    intro i hi
    rcases Nat.lt_or_ge i (n' + 1) with hlt | hge
    · simp only [addfLevels, hlt, ite_true]
      exact F_twoSum_fst p _ _
    · obtain rfl : i = n' + 1 := by omega
      simp only [addfLevels, lt_irrefl, ite_false, ite_true]
      exact (hch n' (by omega)).2.2.1
  have hL0 := addfL_nonneg p n θ hθ.le
  have hM : 0 ≤ |a 0| + |b| := by positivity
  have hZ : |(∑ i ∈ range n, a i + b) - ∑ m ∈ range (n + 1), addfLevels p n a b m| ≤ 0 * u p ^ (n + 1) *
      (|a 0| + |b|) := by rw [t2, sub_self, abs_zero]; simp
  exact ⟨parts_closed p hp n hn _ hF _ hL0 _ hM t1, fun ζ hζ hξ =>
    closure_core p hp n hn _ hF _ hL0 _ hM t1 _ _ hZ ζ hζ hξ⟩

end ExpansionBounds
