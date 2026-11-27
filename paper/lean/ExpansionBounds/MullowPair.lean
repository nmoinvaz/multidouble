import Mathlib.Tactic

/-!
# `series::mullow`: a block pair's integer and the plan's digits
-/

/-!
## `series::mullow`: a block pair's integer at an output index

Each coefficient of a block is an integer `X_i = ∑_{r<t} d_{i,r} 2^{16r}` of balanced digits, `|d| ≤ 2^15`. The
pair's terms of output index `m` are `X_i Y_j`, `i + j = m`; their sum is `∑_q C_q 2^{16q}` with
`C_q = ∑ d_{i,r} d'_{j,r'}`, `r + r' = q` (`pair_sum`). The convolution forms the weights `q ≥ q_0` only; the others
are at most `t 2^{30} ∑_{q<q_0} 2^{16q}` for each term (`dropped_le`). With each `X_i` within `η` of the scaled
coefficient `α_i`, `|α_i| ≥ L_A` and `|β_j| ≥ L_B`, the pair's integer is within `ρ ∑|α_iβ_j|` of `∑ α_iβ_j`
(`pair_err`).
-/

namespace ExpansionBounds

open Finset

/-- the integer of `t` balanced digits of weight `2^{16r}` -/
def digVal (t : ℕ) (d : ℕ → ℤ) : ℤ := ∑ r ∈ range t, d r * 2 ^ (16 * r)

/-- the indicator of the pair's terms of output index `m` -/
def onIdx (m i j : ℕ) : ℤ := if i + j = m then 1 else 0

/-- `C_q` at output index `m`: the digit products of weight `q` -/
def convC (t la lb m : ℕ) (dx dy : ℕ → ℕ → ℤ) (q : ℕ) : ℤ :=
  ∑ i ∈ range la, ∑ j ∈ range lb, onIdx m i j *
    ∑ r ∈ range t, ∑ r' ∈ range t, if r + r' = q then dx i r * dy j r' else 0

/-- the digit products of weight `q` of two digit sequences -/
def digConv (t : ℕ) (a b : ℕ → ℤ) (q : ℕ) : ℤ :=
  ∑ r ∈ range t, ∑ r' ∈ range t, if r + r' = q then a r * b r' else 0

/-- the product of two digit sums, by weight: `∑_{q < 2t - 1} digConv_q 2^{16q}` -/
theorem digVal_mul (t : ℕ) (a b : ℕ → ℤ) :
    digVal t a * digVal t b = ∑ q ∈ range (2 * t - 1), digConv t a b q * 2 ^ (16 * q) := by
  unfold digVal digConv
  rw [sum_mul_sum]
  symm
  calc ∑ q ∈ range (2 * t - 1), (∑ r ∈ range t, ∑ r' ∈ range t, if r + r' = q then a r * b r' else 0) * 2 ^ (16 * q)
      = ∑ q ∈ range (2 * t - 1), ∑ r ∈ range t, ∑ r' ∈ range t,
          (if r + r' = q then a r * b r' * 2 ^ (16 * q) else 0) := by
        refine sum_congr rfl fun q _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun r _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun r' _ => ?_
        split_ifs <;> ring
    _ = ∑ r ∈ range t, ∑ r' ∈ range t, ∑ q ∈ range (2 * t - 1),
          (if r + r' = q then a r * b r' * 2 ^ (16 * q) else 0) := by
        rw [sum_comm]
        refine sum_congr rfl fun r _ => ?_
        rw [sum_comm]
    _ = ∑ r ∈ range t, ∑ r' ∈ range t, a r * 2 ^ (16 * r) * (b r' * 2 ^ (16 * r')) := by
        refine sum_congr rfl fun r hr => sum_congr rfl fun r' hr' => ?_
        rw [mem_range] at hr hr'
        rw [sum_ite_eq, ite_eq_left (mem_range.mpr (by omega)), mul_add, pow_add]
        ring

theorem convC_eq (t la lb m : ℕ) (dx dy : ℕ → ℕ → ℤ) (q : ℕ) :
    convC t la lb m dx dy q = ∑ i ∈ range la, ∑ j ∈ range lb, onIdx m i j * digConv t (dx i) (dy j) q := rfl

/-- the pair's terms at output index `m` are `∑_q C_q 2^{16q}`, `q < 2t - 1` -/
theorem pair_sum (t la lb m : ℕ) (dx dy : ℕ → ℕ → ℤ) :
    ∑ i ∈ range la, ∑ j ∈ range lb, onIdx m i j * (digVal t (dx i) * digVal t (dy j)) =
      ∑ q ∈ range (2 * t - 1), convC t la lb m dx dy q * 2 ^ (16 * q) := by
  symm
  calc ∑ q ∈ range (2 * t - 1), convC t la lb m dx dy q * 2 ^ (16 * q)
      = ∑ q ∈ range (2 * t - 1), ∑ i ∈ range la, ∑ j ∈ range lb,
          onIdx m i j * (digConv t (dx i) (dy j) q * 2 ^ (16 * q)) := by
        refine sum_congr rfl fun q _ => ?_
        rw [convC_eq, sum_mul]
        refine sum_congr rfl fun i _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ i ∈ range la, ∑ j ∈ range lb, ∑ q ∈ range (2 * t - 1),
          onIdx m i j * (digConv t (dx i) (dy j) q * 2 ^ (16 * q)) := by
        rw [sum_comm]
        refine sum_congr rfl fun i _ => ?_
        rw [sum_comm]
    _ = _ := by
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
        rw [← mul_sum, digVal_mul]

theorem sum_ite_add_eq (t r q : ℕ) (f : ℕ → ℤ) :
    ∑ r' ∈ range t, (if r + r' = q then f r' else 0) = if r ≤ q ∧ q - r < t then f (q - r) else 0 := by
  by_cases h : r ≤ q
  · have e : ∀ r', (r + r' = q ↔ q - r = r') := fun r' => by omega
    simp_rw [e]
    rw [sum_ite_eq]
    simp [mem_range, h]
  · rw [sum_eq_zero fun r' _ => ite_eq_right (by omega), ite_eq_right (by omega)]

/-- a weight of two digit sequences of digits at most `2^15` is at most `t 2^{30}` -/
theorem digConv_le (t : ℕ) {a b : ℕ → ℤ} (ha : ∀ r, |a r| ≤ 2 ^ 15) (hb : ∀ r, |b r| ≤ 2 ^ 15) (q : ℕ) :
    |digConv t a b q| ≤ t * 2 ^ 30 := by
  unfold digConv
  calc |∑ r ∈ range t, ∑ r' ∈ range t, (if r + r' = q then a r * b r' else 0)|
      ≤ ∑ r ∈ range t, |∑ r' ∈ range t, (if r + r' = q then a r * b r' else 0)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ range t, (2 ^ 30 : ℤ) := by
        refine sum_le_sum fun r _ => ?_
        rw [sum_ite_add_eq]
        split_ifs
        · rw [abs_mul]
          calc |a r| * |b (q - r)| ≤ 2 ^ 15 * 2 ^ 15 := mul_le_mul (ha r) (hb _) (abs_nonneg _) (by norm_num)
            _ = 2 ^ 30 := by norm_num
        · simp
    _ = t * 2 ^ 30 := by simp

theorem onIdx_nonneg (m i j : ℕ) : 0 ≤ onIdx m i j := by unfold onIdx; split_ifs <;> norm_num

/-- the weights below `q_0`, which the convolution does not form, are at most `K ∑_{q<q_0} 2^{16q} ∑|α_iβ_j|` when each
pair's weights are at most `K|α_iβ_j|` -/
theorem dropped_le (t la lb m q0 : ℕ) {dx dy : ℕ → ℕ → ℤ} {α β : ℕ → ℝ} {K : ℝ}
    (hk : ∀ i < la, ∀ j < lb, ∀ q, |(digConv t (dx i) (dy j) q : ℝ)| ≤ K * (|α i| * |β j|)) :
    |∑ q ∈ range q0, (convC t la lb m dx dy q : ℝ) * 2 ^ (16 * q)| ≤
      K * (∑ q ∈ range q0, (2 : ℝ) ^ (16 * q)) *
        ∑ i ∈ range la, ∑ j ∈ range lb, (onIdx m i j : ℝ) * (|α i| * |β j|) := by
  have hon : ∀ i j, (0 : ℝ) ≤ onIdx m i j := fun i j => by exact_mod_cast onIdx_nonneg m i j
  set A := ∑ i ∈ range la, ∑ j ∈ range lb, (onIdx m i j : ℝ) * (|α i| * |β j|)
  have hC : ∀ q, |(convC t la lb m dx dy q : ℝ)| ≤ K * A := fun q => by
    rw [convC_eq]
    push_cast
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
    rw [abs_mul, abs_of_nonneg (hon i j)]
    calc (onIdx m i j : ℝ) * |(digConv t (dx i) (dy j) q : ℝ)| ≤ (onIdx m i j : ℝ) * (K * (|α i| * |β j|)) :=
          mul_le_mul_of_nonneg_left (hk i (mem_range.mp hi) j (mem_range.mp hj) q) (hon i j)
      _ = K * ((onIdx m i j : ℝ) * (|α i| * |β j|)) := by ring
  calc |∑ q ∈ range q0, (convC t la lb m dx dy q : ℝ) * 2 ^ (16 * q)|
      ≤ ∑ q ∈ range q0, |(convC t la lb m dx dy q : ℝ) * 2 ^ (16 * q)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ range q0, K * A * 2 ^ (16 * q) := sum_le_sum fun q _ => by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (16 * q))]
        exact mul_le_mul_of_nonneg_right (hC q) (by positivity)
    _ = K * (∑ q ∈ range q0, (2 : ℝ) ^ (16 * q)) * A := by rw [← mul_sum]; ring

/-- the pair's integer at output index `m`: the weights `q_0 ≤ q < 2t - 1` -/
def pairV (t la lb m q0 : ℕ) (dx dy : ℕ → ℕ → ℤ) : ℤ :=
  ∑ q ∈ Ico q0 (2 * t - 1), convC t la lb m dx dy q * 2 ^ (16 * q)

/-- one term: `|XY - αβ| ≤ (η/L_A + η/L_B + η²/(L_A L_B))|α||β|` -/
theorem term_err {X Y a b η LA LB : ℝ} (hLA : 0 < LA) (hLB : 0 < LB) (hη : 0 ≤ η) (hX : |X - a| ≤ η)
    (ha : LA ≤ |a|) (hY : |Y - b| ≤ η) (hb : LB ≤ |b|) :
    |X * Y - a * b| ≤ (η / LA + η / LB + η ^ 2 / (LA * LB)) * (|a| * |b|) := by
  have e : X * Y - a * b = (X - a) * (Y - b) + (X - a) * b + a * (Y - b) := by ring
  have h1 : |X * Y - a * b| ≤ η * η + η * |b| + |a| * η := by
    rw [e]
    calc |(X - a) * (Y - b) + (X - a) * b + a * (Y - b)|
        ≤ |(X - a) * (Y - b)| + |(X - a) * b| + |a * (Y - b)| := abs_add_three _ _ _
      _ ≤ η * η + η * |b| + |a| * η := by
        rw [abs_mul, abs_mul, abs_mul]
        gcongr
  have hab : LA * LB ≤ |a| * |b| := mul_le_mul ha hb hLB.le (abs_nonneg _)
  have r1 : η * |b| ≤ η / LA * (|a| * |b|) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hLA]
    nlinarith [mul_le_mul_of_nonneg_left ha (mul_nonneg hη (abs_nonneg b))]
  have r2 : |a| * η ≤ η / LB * (|a| * |b|) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hLB]
    nlinarith [mul_le_mul_of_nonneg_left hb (mul_nonneg (abs_nonneg a) hη)]
  have r3 : η * η ≤ η ^ 2 / (LA * LB) * (|a| * |b|) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos hLA hLB)]
    nlinarith [sq_nonneg η]
  calc |X * Y - a * b| ≤ η * η + η * |b| + |a| * η := h1
    _ ≤ η ^ 2 / (LA * LB) * (|a| * |b|) + η / LA * (|a| * |b|) + η / LB * (|a| * |b|) := by linarith
    _ = (η / LA + η / LB + η ^ 2 / (LA * LB)) * (|a| * |b|) := by ring

/-- a block pair's integer at output index `m` is within `ρ ∑|α_iβ_j|` of `∑ α_iβ_j`, the sums over its terms,
`ρ = η/L_A + η/L_B + η²/(L_A L_B) + t 2^{30} ∑_{q<q_0} 2^{16q}/(L_A L_B)`; a coefficient is zero with zero digits, or
at least `L` with its integer within `η` -/
theorem pair_err (t la lb m q0 : ℕ) (hq0 : q0 ≤ 2 * t - 1) {dx dy : ℕ → ℕ → ℤ}
    (hx : ∀ i r, |dx i r| ≤ 2 ^ 15) (hy : ∀ j r, |dy j r| ≤ 2 ^ 15)
    {α β : ℕ → ℝ} {η LA LB : ℝ} (hLA : 0 < LA) (hLB : 0 < LB) (hη : 0 ≤ η)
    (hα : ∀ i < la, (α i = 0 ∧ ∀ r, dx i r = 0) ∨ (|(digVal t (dx i) : ℝ) - α i| ≤ η ∧ LA ≤ |α i|))
    (hβ : ∀ j < lb, (β j = 0 ∧ ∀ r, dy j r = 0) ∨ (|(digVal t (dy j) : ℝ) - β j| ≤ η ∧ LB ≤ |β j|)) :
    |(pairV t la lb m q0 dx dy : ℝ) - ∑ i ∈ range la, ∑ j ∈ range lb, (onIdx m i j : ℝ) * (α i * β j)| ≤
      (η / LA + η / LB + η ^ 2 / (LA * LB) + t * 2 ^ 30 * (∑ q ∈ range q0, (2 : ℝ) ^ (16 * q)) / (LA * LB)) *
        ∑ i ∈ range la, ∑ j ∈ range lb, (onIdx m i j : ℝ) * (|α i| * |β j|) := by
  set c := η / LA + η / LB + η ^ 2 / (LA * LB)
  set G := ∑ q ∈ range q0, (2 : ℝ) ^ (16 * q)
  set A := ∑ i ∈ range la, ∑ j ∈ range lb, (onIdx m i j : ℝ) * (|α i| * |β j|)
  have hon : ∀ i j, (0 : ℝ) ≤ onIdx m i j := fun i j => by exact_mod_cast onIdx_nonneg m i j
  have hc : 0 ≤ c := by positivity
  -- zero digits make a zero integer and zero weights
  have hz0 : ∀ {d : ℕ → ℤ}, (∀ r, d r = 0) → digVal t d = 0 := fun h => by simp [digVal, h]
  have hzc : ∀ {a b : ℕ → ℤ} q, ((∀ r, a r = 0) ∨ ∀ r, b r = 0) → digConv t a b q = 0 := fun q h => by
    rcases h with h | h <;> simp [digConv, h]
  -- the pair's integer is its terms less the dropped weights
  have hsplit : pairV t la lb m q0 dx dy =
      ∑ i ∈ range la, ∑ j ∈ range lb, onIdx m i j * (digVal t (dx i) * digVal t (dy j)) -
        ∑ q ∈ range q0, convC t la lb m dx dy q * 2 ^ (16 * q) := by
    rw [pair_sum, ← sum_range_add_sum_Ico _ hq0, pairV]
    ring
  -- each pair's weights are at most `t 2^{30} ≤ t 2^{30} |α_iβ_j|/(L_A L_B)`, or zero
  have hd := dropped_le t la lb m q0 (α := α) (β := β) (K := t * 2 ^ 30 / (LA * LB)) (dx := dx) (dy := dy)
    fun i hi j hj q => by
      rcases hα i hi with ⟨_, hzi⟩ | ⟨_, hai⟩
      · rw [hzc q (Or.inl hzi)]; simp only [Int.cast_zero, abs_zero]; positivity
      rcases hβ j hj with ⟨_, hzj⟩ | ⟨_, hbj⟩
      · rw [hzc q (Or.inr hzj)]; simp only [Int.cast_zero, abs_zero]; positivity
      have h1 : |(digConv t (dx i) (dy j) q : ℝ)| ≤ t * 2 ^ 30 := by exact_mod_cast digConv_le t (hx i) (hy j) q
      have h2 : 1 ≤ |α i| * |β j| / (LA * LB) := by
        rw [le_div_iff₀ (mul_pos hLA hLB), one_mul]
        exact mul_le_mul hai hbj hLB.le (abs_nonneg _)
      calc |(digConv t (dx i) (dy j) q : ℝ)| ≤ t * 2 ^ 30 * 1 := by linarith
        _ ≤ t * 2 ^ 30 * (|α i| * |β j| / (LA * LB)) := by gcongr
        _ = t * 2 ^ 30 / (LA * LB) * (|α i| * |β j|) := by ring
  have hterms : |(((∑ i ∈ range la, ∑ j ∈ range lb, onIdx m i j * (digVal t (dx i) * digVal t (dy j))) : ℤ) : ℝ) -
      ∑ i ∈ range la, ∑ j ∈ range lb, (onIdx m i j : ℝ) * (α i * β j)| ≤ c * A := by
    push_cast
    rw [← sum_sub_distrib, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
    rw [← sum_sub_distrib, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
    have hij : |(digVal t (dx i) : ℝ) * (digVal t (dy j) : ℝ) - α i * β j| ≤ c * (|α i| * |β j|) := by
      rcases hα i (mem_range.mp hi) with ⟨ha0, hzi⟩ | ⟨hxi, hai⟩
      · rw [hz0 hzi, ha0]; simp
      rcases hβ j (mem_range.mp hj) with ⟨hb0, hzj⟩ | ⟨hyj, hbj⟩
      · rw [hz0 hzj, hb0]; simp
      exact term_err hLA hLB hη hxi hai hyj hbj
    rw [← mul_sub, abs_mul, abs_of_nonneg (hon i j)]
    calc (onIdx m i j : ℝ) * |(digVal t (dx i) : ℝ) * (digVal t (dy j) : ℝ) - α i * β j|
        ≤ (onIdx m i j : ℝ) * (c * (|α i| * |β j|)) := mul_le_mul_of_nonneg_left hij (hon i j)
      _ = c * ((onIdx m i j : ℝ) * (|α i| * |β j|)) := by ring
  rw [hsplit]
  push_cast
  push_cast at hterms
  have e : (∑ i ∈ range la, ∑ j ∈ range lb, (onIdx m i j : ℝ) * ((digVal t (dx i) : ℝ) * (digVal t (dy j) : ℝ)) -
        ∑ q ∈ range q0, (convC t la lb m dx dy q : ℝ) * 2 ^ (16 * q)) -
        ∑ i ∈ range la, ∑ j ∈ range lb, (onIdx m i j : ℝ) * (α i * β j) =
      (∑ i ∈ range la, ∑ j ∈ range lb, (onIdx m i j : ℝ) * ((digVal t (dx i) : ℝ) * (digVal t (dy j) : ℝ)) -
        ∑ i ∈ range la, ∑ j ∈ range lb, (onIdx m i j : ℝ) * (α i * β j)) -
        ∑ q ∈ range q0, (convC t la lb m dx dy q : ℝ) * 2 ^ (16 * q) := by ring
  rw [e]
  calc _ ≤ _ := abs_sub _ _
    _ ≤ c * A + t * 2 ^ 30 / (LA * LB) * G * A := add_le_add hterms hd
    _ = (c + t * 2 ^ 30 * G / (LA * LB)) * A := by ring

end ExpansionBounds

/-!
## `series::plan`: the pair's error at the plan's digits and weights

`plan` takes `t` digits per coefficient, `W = 16t - 2 ≥ prec + h + 5` bits for the spread `h` of each block, and
forms the weights from `q_0`, `16 q_0 ≤ 2W - h_a - h_b - 2 - prec - 14 - lg` with `t ≤ 2^lg` (or `q_0 = 0`). With
coefficients at least `L = 2^{W - 1 - h}(1 - 2u)` and their integers within `η = 1/(1 - u)`, the pair's `ρ` of
`pair_err` is at most `1.13 · 2^{-prec}` (`plan_rho`).
-/

namespace ExpansionBounds

open Finset

/-- `∑_{q<q_0} 2^{16q} ≤ 2^{16 q_0}/(2^{16} - 1)` -/
theorem sum_pow16_le (q0 : ℕ) : ∑ q ∈ range q0, (2 : ℝ) ^ (16 * q) ≤ 2 ^ (16 * q0) / (2 ^ 16 - 1) := by
  rw [le_div_iff₀ (by norm_num)]
  have : (2 ^ 16 - 1 : ℝ) * ∑ q ∈ range q0, (2 : ℝ) ^ (16 * q) = 2 ^ (16 * q0) - 1 := by
    induction q0 with
    | zero => simp
    | succ q ih => rw [sum_range_succ, mul_add, ih, mul_add 16 q 1, pow_add]; ring
  linarith

/-- the pair's `ρ` at the plan's digits and weights, for `prec ≥ 1`: at most `1.13 · 2^{-prec}` -/
theorem plan_rho {prec ha hb t q0 lg : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 53) (hprec : 1 ≤ prec)
    (hW : prec + max ha hb + 5 ≤ 16 * t - 2) (ht2 : 1 ≤ t)
    (hq0 : q0 = 0 ∨ 16 * q0 + prec + 14 + lg + ha + hb + 2 ≤ 2 * (16 * t - 2)) (htl : t ≤ 2 ^ lg) :
    let η : ℝ := 1 / (1 - u)
    let LA : ℝ := 2 ^ (16 * t - 2 - 1 - ha) * (1 - 2 * u)
    let LB : ℝ := 2 ^ (16 * t - 2 - 1 - hb) * (1 - 2 * u)
    η / LA + η / LB + η ^ 2 / (LA * LB) + t * 2 ^ 30 * (∑ q ∈ range q0, (2 : ℝ) ^ (16 * q)) / (LA * LB) ≤
      113 / 100 / 2 ^ prec := by
  intro η LA LB
  set A := 16 * t - 2 - 1 - ha
  set B := 16 * t - 2 - 1 - hb
  set X : ℝ := 2 ^ prec with hX
  have hXp : 0 < X := by positivity
  have hu53 : u ≤ 1 / 10000 := hu.trans (by norm_num)
  set c := 1 - 2 * u with hc
  have hc1 : 9998 / 10000 ≤ c := by linarith
  have hcp : 0 < c := by linarith
  have hη : η ≤ 10001 / 10000 := by
    show 1 / (1 - u) ≤ 10001 / 10000
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hηp : 0 < η := by show 0 < 1 / (1 - u); exact div_pos one_pos (by linarith)
  -- each block's least coefficient is at least `16 · 2^{prec}` times `c`
  have hA : (2 : ℝ) ^ (prec + 4) ≤ 2 ^ A := pow_le_pow_right₀ (by norm_num) (by omega)
  have hB : (2 : ℝ) ^ (prec + 4) ≤ 2 ^ B := pow_le_pow_right₀ (by norm_num) (by omega)
  have h16 : (2 : ℝ) ^ (prec + 4) = 16 * X := by rw [pow_add]; norm_num; ring
  rw [h16] at hA hB
  have hLA : 16 * X * c ≤ LA := by show 16 * X * c ≤ 2 ^ A * c; gcongr
  have hLB : 16 * X * c ≤ LB := by show 16 * X * c ≤ 2 ^ B * c; gcongr
  have hp16 : 0 < 16 * X * c := by positivity
  have t1 : η / LA ≤ η / (16 * X * c) := div_le_div_of_nonneg_left hηp.le hp16 hLA
  have t2 : η / LB ≤ η / (16 * X * c) := div_le_div_of_nonneg_left hηp.le hp16 hLB
  have hLL : (16 * X * c) * (16 * X * c) ≤ LA * LB := mul_le_mul hLA hLB hp16.le (hp16.le.trans hLA)
  have t3 : η ^ 2 / (LA * LB) ≤ η ^ 2 / ((16 * X * c) * (16 * X * c)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hLL
  -- the dropped weights: at most `2^{16}/((2^{16} - 1) c²)` times `2^{-prec}`
  have t4 : t * 2 ^ 30 * (∑ q ∈ range q0, (2 : ℝ) ^ (16 * q)) / (LA * LB) ≤ 2 ^ 16 / ((2 ^ 16 - 1) * c ^ 2) / X := by
    rcases hq0 with h0 | hq
    · subst h0
      simp only [range_zero, sum_empty, mul_zero, zero_div]
      positivity
    · have hG := sum_pow16_le q0
      have hAB : (2 : ℝ) ^ (16 * q0) * X * 2 ^ 14 * 2 ^ lg ≤ 2 ^ A * 2 ^ B := by
        rw [hX, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have htR : (t : ℝ) ≤ 2 ^ lg := by exact_mod_cast htl
      have hnum : (t : ℝ) * 2 ^ 30 * ∑ q ∈ range q0, (2 : ℝ) ^ (16 * q) ≤
          2 ^ lg * 2 ^ 30 * (2 ^ (16 * q0) / (2 ^ 16 - 1)) := by gcongr
      have hden : (2 : ℝ) ^ (16 * q0) * X * 2 ^ 14 * 2 ^ lg * c ^ 2 ≤ LA * LB := by
        show _ ≤ 2 ^ A * c * (2 ^ B * c)
        nlinarith [hAB, sq_nonneg c]
      have hdp : 0 < (2 : ℝ) ^ (16 * q0) * X * 2 ^ 14 * 2 ^ lg * c ^ 2 := by positivity
      calc t * 2 ^ 30 * (∑ q ∈ range q0, (2 : ℝ) ^ (16 * q)) / (LA * LB)
          ≤ 2 ^ lg * 2 ^ 30 * (2 ^ (16 * q0) / (2 ^ 16 - 1)) / ((2 : ℝ) ^ (16 * q0) * X * 2 ^ 14 * 2 ^ lg * c ^ 2) :=
            div_le_div₀ (by positivity) hnum hdp hden
        _ = 2 ^ 16 / ((2 ^ 16 - 1) * c ^ 2) / X := by field_simp
  -- the four terms in units of `2^{-prec}`
  have e1 : η / (16 * X * c) = η / (16 * c) / X := by field_simp
  have e3 : η ^ 2 / ((16 * X * c) * (16 * X * c)) = η ^ 2 / (256 * c ^ 2 * X) / X := by field_simp; ring
  have hX2 : (2 : ℝ) ≤ X := by
    rw [hX]; calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ prec := pow_le_pow_right₀ (by norm_num) hprec
  have b1 : η / (16 * c) ≤ 6252 / 100000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have b3 : η ^ 2 / (256 * c ^ 2 * X) ≤ 2 / 1000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [sq_nonneg η, sq_nonneg c]
  have b4 : (2 : ℝ) ^ 16 / ((2 ^ 16 - 1) * c ^ 2) ≤ 10003 / 10000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [sq_nonneg c]
  have hsum : η / (16 * c) / X + η / (16 * c) / X + η ^ 2 / (256 * c ^ 2 * X) / X +
      2 ^ 16 / ((2 ^ 16 - 1) * c ^ 2) / X ≤ 113 / 100 / X := by
    rw [← add_div, ← add_div, ← add_div]
    apply div_le_div_of_nonneg_right _ hXp.le
    linarith
  rw [e1] at t1 t2
  rw [e3] at t3
  linarith

end ExpansionBounds
