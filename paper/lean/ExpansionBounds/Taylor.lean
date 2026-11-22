import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The sine and cosine series

For `|r| ≤ 1` the terms of the sine and cosine series alternate in sign and decrease, so a partial sum errs by at
most its first omitted term, `|sin r| ≥ |r|(1 - r²/6)`, and `cos r ≥ cos₋ r̄ = 1 - r̄²/2 + r̄⁴/24 - r̄⁶/720` for
`|r| ≤ r̄ ≤ 1`.
-/

namespace ExpansionBounds

open Finset

/-- `s_k = (-1)^k / (2k + 1)!` -/
noncomputable def sinC (k : ℕ) : ℝ := (-1) ^ k / ((2 * k + 1).factorial : ℝ)

/-- `c_k = (-1)^k / (2k)!` -/
noncomputable def cosC (k : ℕ) : ℝ := (-1) ^ k / ((2 * k).factorial : ℝ)

/-- `cos₋ x = 1 - x²/2 + x⁴/24 - x⁶/720` -/
noncomputable def cosLo (x : ℝ) : ℝ := 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720

/-- a finite alternating sum of decreasing nonnegative terms lies between `0` and its first term -/
theorem alt_sum_bounds (N : ℕ) : ∀ b : ℕ → ℝ, Antitone b → (∀ l, 0 ≤ b l) →
    0 ≤ ∑ l ∈ range N, (-1) ^ l * b l ∧ ∑ l ∈ range N, (-1) ^ l * b l ≤ b 0 := by
  induction N with
  | zero => intro b _ hb; simp [hb 0]
  | succ N ih =>
    intro b hba hb
    obtain ⟨h1, h2⟩ := ih (fun l => b (l + 1)) (fun i j hij => hba (by omega)) (fun l => hb _)
    have hs : ∑ l ∈ range (N + 1), (-1) ^ l * b l = b 0 - ∑ l ∈ range N, (-1) ^ l * b (l + 1) := by
      rw [sum_range_succ']
      simp only [pow_succ, pow_zero, one_mul, mul_neg, mul_one, neg_mul, sum_neg_distrib]
      ring
    rw [hs]
    have := hba (Nat.zero_le 1)
    constructor <;> linarith

theorem pow_div_fact_antitone (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) (c : ℕ) :
    Antitone fun i : ℕ => x ^ (2 * i + c) / ((2 * i + c).factorial : ℝ) := by
  refine antitone_nat_of_succ_le fun i => ?_
  have hf1 : (0 : ℝ) < ((2 * i + c).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hf2 : (0 : ℝ) < ((2 * (i + 1) + c).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hfl : ((2 * i + c).factorial : ℝ) ≤ ((2 * (i + 1) + c).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hp : x ^ (2 * (i + 1) + c) ≤ x ^ (2 * i + c) := pow_le_pow_of_le_one h0 h1 (by omega)
  rw [div_le_div_iff₀ hf2 hf1]
  exact mul_le_mul hp hfl hf1.le (pow_nonneg h0 _)

theorem pow_div_fact_summable (x : ℝ) (c : ℕ) :
    Summable fun i : ℕ => x ^ (2 * i + c) / ((2 * i + c).factorial : ℝ) := by
  have hi : Function.Injective fun i : ℕ => 2 * i + c := fun a b h => by simp only at h; omega
  have hs : Summable fun m : ℕ => x ^ m / (m.factorial : ℝ) := Real.summable_pow_div_factorial x
  exact hs.comp_injective hi

/-- the sine series after `K` terms: `|sin r - ∑_{k<K} s_k r^{2k+1}| ≤ |r|^{2K+1} / (2K + 1)!` -/
theorem sin_taylor (r : ℝ) (hr : |r| ≤ 1) (K : ℕ) :
    |Real.sin r - ∑ k ∈ range K, sinC k * r ^ (2 * k + 1)| ≤ |r| ^ (2 * K + 1) / ((2 * K + 1).factorial : ℝ) := by
  wlog h0 : 0 ≤ r generalizing r
  · have h := this (-r) (by rwa [abs_neg]) (by linarith)
    have hs : ∑ k ∈ range K, sinC k * (-r) ^ (2 * k + 1) = -∑ k ∈ range K, sinC k * r ^ (2 * k + 1) := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun k _ => by rw [Odd.neg_pow ⟨k, rfl⟩]; ring
    rw [Real.sin_neg, abs_neg, hs, show -Real.sin r - -∑ k ∈ range K, sinC k * r ^ (2 * k + 1) =
      -(Real.sin r - ∑ k ∈ range K, sinC k * r ^ (2 * k + 1)) by ring, abs_neg] at h
    exact h
  have h1 : r ≤ 1 := by rwa [abs_of_nonneg h0] at hr
  set f : ℕ → ℝ := fun i => r ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)
  have hsin : Real.sin r = ∑' i, (-1) ^ i * f i := by
    rw [Real.sin_eq_tsum]
    exact tsum_congr fun i => by simp only [f]; ring
  have h := alternating_series_error_bound f (pow_div_fact_antitone r h0 h1 1) (pow_div_fact_summable r 1) K
  have hsum : ∑ i ∈ range K, (-1) ^ i * f i = ∑ k ∈ range K, sinC k * r ^ (2 * k + 1) :=
    sum_congr rfl fun k _ => by simp only [f, sinC]; ring
  rw [← hsin, hsum] at h
  rwa [abs_of_nonneg h0]

/-- the cosine series after `K` terms: `|cos r - ∑_{k<K} c_k r^{2k}| ≤ r^{2K} / (2K)!` -/
theorem cos_taylor (r : ℝ) (hr : |r| ≤ 1) (K : ℕ) :
    |Real.cos r - ∑ k ∈ range K, cosC k * r ^ (2 * k)| ≤ |r| ^ (2 * K) / ((2 * K).factorial : ℝ) := by
  wlog h0 : 0 ≤ r generalizing r
  · have h := this (-r) (by rwa [abs_neg]) (by linarith)
    have hs : ∑ k ∈ range K, cosC k * (-r) ^ (2 * k) = ∑ k ∈ range K, cosC k * r ^ (2 * k) :=
      sum_congr rfl fun k _ => by rw [Even.neg_pow ⟨k, by ring⟩]
    rwa [Real.cos_neg, abs_neg, hs] at h
  have h1 : r ≤ 1 := by rwa [abs_of_nonneg h0] at hr
  set f : ℕ → ℝ := fun i => r ^ (2 * i + 0) / ((2 * i + 0).factorial : ℝ)
  have hcos : Real.cos r = ∑' i, (-1) ^ i * f i := by
    rw [Real.cos_eq_tsum]
    exact tsum_congr fun i => by simp only [f, add_zero]; ring
  have h := alternating_series_error_bound f (pow_div_fact_antitone r h0 h1 0) (pow_div_fact_summable r 0) K
  have hsum : ∑ i ∈ range K, (-1) ^ i * f i = ∑ k ∈ range K, cosC k * r ^ (2 * k) :=
    sum_congr rfl fun k _ => by simp only [f, cosC, add_zero]; try ring
  rw [← hcos, hsum] at h
  simpa [abs_of_nonneg h0, f] using h

/-- `|sin r| ≥ |r|(1 - r²/6)` -/
theorem abs_sin_ge (r : ℝ) (hr : |r| ≤ 1) : |r| * (1 - r ^ 2 / 6) ≤ |Real.sin r| := by
  have h := sin_taylor r hr 1
  simp only [sum_range_one, sinC, pow_zero, mul_zero, zero_add, pow_one, Nat.factorial, Nat.succ_eq_add_one,
    mul_one, Nat.cast_one, div_one, one_mul] at h
  have h3 : |r| ^ 3 = |r| * r ^ 2 := by rw [pow_succ, mul_comm, sq_abs]
  norm_num at h
  rw [h3] at h
  have := abs_sub_abs_le_abs_sub r (Real.sin r)
  rw [abs_sub_comm] at this
  nlinarith [abs_nonneg r]

/-- `cos r ≥ cos₋ r̄` for `|r| ≤ r̄ ≤ 1` -/
theorem cos_ge_cosLo (r rb : ℝ) (hr : |r| ≤ rb) (hrb : rb ≤ 1) : cosLo rb ≤ Real.cos r := by
  wlog h0 : 0 ≤ r generalizing r
  · have := this (-r) (by rwa [abs_neg]) (by linarith)
    rwa [Real.cos_neg] at this
  have h1 : r ≤ 1 := by rw [abs_of_nonneg h0] at hr; linarith
  set f : ℕ → ℝ := fun i => r ^ (2 * i + 0) / ((2 * i + 0).factorial : ℝ)
  have hcos : HasSum (fun i => (-1) ^ i * f i) (Real.cos r) := by
    have := Real.hasSum_cos r
    convert this using 1
    funext i
    simp only [f, add_zero]
    ring
  have hlo := (pow_div_fact_antitone r h0 h1 0).alternating_series_le_tendsto hcos.tendsto_sum_nat 2
  have hval : ∑ i ∈ range (2 * 2), (-1) ^ i * f i = cosLo r := by
    simp [f, sum_range_succ, cosLo, Nat.factorial]
    ring
  rw [hval] at hlo
  refine le_trans ?_ hlo
  -- `cos₋` decreases on `[0, 1]`
  have hr' : r ≤ rb := by rwa [abs_of_nonneg h0] at hr
  unfold cosLo
  have ht : r ^ 2 ≤ rb ^ 2 := pow_le_pow_left₀ h0 hr' 2
  have ht1 : rb ^ 2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg (r ^ 2), sq_nonneg (rb ^ 2), mul_nonneg (sq_nonneg r) (sq_nonneg rb), pow_nonneg h0 2]

end ExpansionBounds
