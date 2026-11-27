import Mathlib.Tactic

/-!
# `series::digits`: a coefficient's digits and their loss
-/

/-!
## `series::digits`: one part taken into 16-bit digits

`digits` takes each part `P` of a scaled coefficient, on one lane, into digits from level `r_hi` down to `r_lo`:
`q_r = rnd(rem/2^{16r})` and `rem ← rem - q_r 2^{16r}`, `rnd` the nearest integer (`extRem`). What is left is at
most half the last weight (`extRem_le`); none is left where `P` is a multiple of `2^{16 r_lo}` (`extRem_exact`); and a
part below 1 loses at most itself (`extRem_small`).
-/

namespace ExpansionBounds

open Finset

/-- what is left of the part `P` after `n` levels, from level `r_hi` down; `rnd` rounds to an integer -/
noncomputable def extRem (rnd : ℝ → ℤ) (P : ℝ) (rhi : ℕ) : ℕ → ℝ
  | 0 => P
  | n + 1 => extRem rnd P rhi n - rnd (extRem rnd P rhi n / 2 ^ (16 * (rhi - n))) * 2 ^ (16 * (rhi - n))

variable {rnd : ℝ → ℤ} (hrnd : ∀ x, |x - rnd x| ≤ 1 / 2)
include hrnd

/-- after the level `r`, at most half its weight `2^{16r}` is left -/
theorem extRem_le (P : ℝ) (rhi n : ℕ) :
    |extRem rnd P rhi (n + 1)| ≤ 2 ^ (16 * (rhi - n)) / 2 := by
  simp only [extRem]
  set S : ℝ := 2 ^ (16 * (rhi - n))
  have hS : 0 < S := by positivity
  set x := extRem rnd P rhi n
  have e : x - rnd (x / S) * S = S * (x / S - rnd (x / S)) := by field_simp
  rw [e, abs_mul, abs_of_pos hS]
  have := hrnd (x / S)
  nlinarith

/-- a rounding of an integer is that integer -/
theorem rnd_int (z : ℤ) : rnd z = z := by
  have h := hrnd z
  have h2 : |((z - rnd z : ℤ) : ℝ)| < 1 := by push_cast; linarith
  have h3 : |z - rnd z| < 1 := by exact_mod_cast h2
  have := Int.abs_lt_one_iff.mp h3
  omega

/-- the rounding of a value below `1/2` is 0 -/
theorem rnd_small {x : ℝ} (hx : |x| < 1 / 2) : rnd x = 0 := by
  have h := hrnd x
  rw [abs_sub_comm] at h
  have h1 : |(rnd x : ℝ)| < 1 := by
    have := abs_add_le ((rnd x : ℝ) - x) x
    rw [sub_add_cancel] at this
    linarith
  have : |rnd x| < 1 := by exact_mod_cast h1
  exact Int.abs_lt_one_iff.mp this

omit hrnd in
/-- while the levels stay at or above `r_lo`, what is left of a multiple of `2^{16 r_lo}` is one -/
theorem extRem_mult {P : ℝ} {rlo rhi : ℕ} {z : ℤ} (hP : P = z * 2 ^ (16 * rlo)) :
    ∀ n ≤ rhi - rlo + 1, rlo ≤ rhi → ∃ w : ℤ, extRem rnd P rhi n = w * 2 ^ (16 * rlo) := by
  intro n
  induction n with
  | zero => exact fun _ _ => ⟨z, hP⟩
  | succ n ih =>
    intro hn hr
    obtain ⟨w, hw⟩ := ih (by omega) hr
    refine ⟨w - rnd (extRem rnd P rhi n / 2 ^ (16 * (rhi - n))) * 2 ^ (16 * (rhi - n - rlo)), ?_⟩
    simp only [extRem]
    rw [hw]
    have e : (2 : ℝ) ^ (16 * (rhi - n)) = 2 ^ (16 * (rhi - n - rlo)) * 2 ^ (16 * rlo) := by
      rw [← pow_add]
      congr 1
      omega
    rw [e]
    push_cast
    ring

/-- a multiple of `2^{16 r_lo}`, taken from level `r_hi` down to `r_lo`, leaves nothing -/
theorem extRem_exact {P : ℝ} {rlo rhi : ℕ} {z : ℤ} (hP : P = z * 2 ^ (16 * rlo)) (hr : rlo ≤ rhi) :
    extRem rnd P rhi (rhi - rlo + 1) = 0 := by
  obtain ⟨w, hw⟩ := extRem_mult (rnd := rnd) hP (rhi - rlo + 1) le_rfl hr
  have hle := extRem_le hrnd P rhi (rhi - rlo)
  rw [show rhi - (rhi - rlo) = rlo by omega, hw] at hle
  have hS : (0 : ℝ) < 2 ^ (16 * rlo) := by positivity
  rw [abs_mul, abs_of_pos hS] at hle
  have : |(w : ℝ)| ≤ 1 / 2 := by nlinarith
  have hw0 : |w| < 1 := by
    have : (|w| : ℝ) < 1 := by linarith
    exact_mod_cast this
  rw [hw, Int.abs_lt_one_iff.mp hw0]
  simp

/-- a part below 1 loses at most itself, whatever the levels -/
theorem extRem_small {P : ℝ} (hP : |P| < 1) (rhi : ℕ) : ∀ n, |extRem rnd P rhi n| ≤ |P| := by
  intro n
  induction n with
  | zero => simp [extRem]
  | succ n ih =>
    simp only [extRem]
    set x := extRem rnd P rhi n
    have hx1 : |x| < 1 := lt_of_le_of_lt ih hP
    rcases Nat.eq_zero_or_pos (rhi - n) with h0 | hpos
    · -- level 0: the rounding to an integer, at most `|x|` off for `|x| < 1`
      rw [h0, mul_zero, pow_zero, div_one, mul_one]
      by_cases hh : |x| < 1 / 2
      · rw [rnd_small hrnd hh]
        simpa using ih
      · have := hrnd x
        push Not at hh
        linarith
    · -- a level `r ≥ 1`: the digit is 0
      have hS : (2 : ℝ) ^ 16 ≤ 2 ^ (16 * (rhi - n)) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hsmall : |x / 2 ^ (16 * (rhi - n))| < 1 / 2 := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (16 * (rhi - n))), div_lt_iff₀ (by positivity)]
        nlinarith
      rw [rnd_small hrnd hsmall]
      simpa using ih

/-- the carry into digit `r` of `digits`' last loop: `c_0 = 0`, `c_{r+1} = rnd((D_r + c_r)/2^{16})` -/
noncomputable def carryIn (rnd : ℝ → ℤ) (D : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | r + 1 => rnd (((D r + carryIn rnd D r : ℤ) : ℝ) / 2 ^ 16)

/-- the balanced digit `d_r = D_r + c_r - c_{r+1} 2^{16}` -/
noncomputable def balDig (rnd : ℝ → ℤ) (D : ℕ → ℤ) (r : ℕ) : ℤ :=
  D r + carryIn rnd D r - carryIn rnd D (r + 1) * 2 ^ 16

omit hrnd in
/-- the digits keep the sum, less the carry out of the top -/
theorem balDig_sum (D : ℕ → ℤ) (t : ℕ) :
    ∑ r ∈ range t, balDig rnd D r * 2 ^ (16 * r) =
      ∑ r ∈ range t, D r * 2 ^ (16 * r) - carryIn rnd D t * 2 ^ (16 * t) := by
  induction t with
  | zero => simp [carryIn]
  | succ t ih =>
    rw [sum_range_succ, sum_range_succ, ih, balDig, mul_add 16 t 1, pow_add]
    ring

/-- `x` less its rounding to a multiple of `S` is at most `S/2` -/
theorem rnd_rem (x : ℝ) {S : ℝ} (hS : 0 < S) : |x - rnd (x / S) * S| ≤ S / 2 := by
  have e : x - rnd (x / S) * S = S * (x / S - rnd (x / S)) := by field_simp
  rw [e, abs_mul, abs_of_pos hS]
  have := hrnd (x / S)
  nlinarith

/-- each balanced digit is at most `2^{15}` -/
theorem balDig_le (D : ℕ → ℤ) (r : ℕ) : |balDig rnd D r| ≤ 2 ^ 15 := by
  have h := rnd_rem hrnd (((D r + carryIn rnd D r : ℤ) : ℝ)) (by norm_num : (0 : ℝ) < 2 ^ 16)
  have e : ((balDig rnd D r : ℤ) : ℝ) = ((D r + carryIn rnd D r : ℤ) : ℝ) -
      rnd (((D r + carryIn rnd D r : ℤ) : ℝ) / 2 ^ 16) * 2 ^ 16 := by
    simp only [balDig, carryIn]
    push_cast
    ring
  have hR : |((balDig rnd D r : ℤ) : ℝ)| ≤ 2 ^ 15 := by
    rw [e]
    linarith
  exact_mod_cast hR

omit hrnd in
/-- `(2^{16} - 1) ∑_{r<t} 2^{16r} = 2^{16t} - 1` -/
theorem geo16 (t : ℕ) : (2 ^ 16 - 1 : ℝ) * ∑ r ∈ range t, (2 : ℝ) ^ (16 * r) = 2 ^ (16 * t) - 1 := by
  induction t with
  | zero => simp
  | succ t ih => rw [sum_range_succ, mul_add, ih, mul_add 16 t 1, pow_add]; ring

/-- no carry leaves the top digit where the sum is below `0.49 2^{16t}` -/
theorem carry_top (D : ℕ → ℤ) (t : ℕ)
    (hD : |((∑ r ∈ range t, D r * 2 ^ (16 * r) : ℤ) : ℝ)| ≤ 49 / 100 * 2 ^ (16 * t)) : carryIn rnd D t = 0 := by
  have hs := balDig_sum (rnd := rnd) D t
  have hdig : |((∑ r ∈ range t, balDig rnd D r * 2 ^ (16 * r) : ℤ) : ℝ)| ≤
      2 ^ 15 * ∑ r ∈ range t, (2 : ℝ) ^ (16 * r) := by
    push_cast
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r _ => ?_)
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (16 * r))]
    have := balDig_le hrnd D r
    have : |(balDig rnd D r : ℝ)| ≤ 2 ^ 15 := by exact_mod_cast this
    nlinarith [(by positivity : (0 : ℝ) < 2 ^ (16 * r))]
  have hgeo := geo16 t
  have hG : 2 ^ 15 * ∑ r ∈ range t, (2 : ℝ) ^ (16 * r) ≤ 51 / 100 * 2 ^ (16 * t) := by
    have hpos : (0 : ℝ) < 2 ^ (16 * t) := by positivity
    nlinarith
  have hc : |((carryIn rnd D t * 2 ^ (16 * t) : ℤ) : ℝ)| < 2 ^ (16 * t) := by
    have e : ((carryIn rnd D t * 2 ^ (16 * t) : ℤ) : ℝ) =
        ((∑ r ∈ range t, D r * 2 ^ (16 * r) : ℤ) : ℝ) - ((∑ r ∈ range t, balDig rnd D r * 2 ^ (16 * r) : ℤ) : ℝ) := by
      rw [hs]; push_cast; ring
    rw [e]
    have := abs_sub (((∑ r ∈ range t, D r * 2 ^ (16 * r) : ℤ) : ℝ))
      (((∑ r ∈ range t, balDig rnd D r * 2 ^ (16 * r) : ℤ) : ℝ))
    have hpos : (0 : ℝ) < 2 ^ (16 * t) := by positivity
    linarith
  have hc' : |(carryIn rnd D t : ℝ)| < 1 := by
    push_cast at hc
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (16 * t))] at hc
    have hpos : (0 : ℝ) < 2 ^ (16 * t) := by positivity
    nlinarith [abs_nonneg (carryIn rnd D t : ℝ)]
  exact Int.abs_lt_one_iff.mp (by exact_mod_cast hc')

end ExpansionBounds

/-!
## `series::digits`: a coefficient's integer

A part at least 1 is a multiple of `2^{16 r_lo}` unless `r_lo = 0` (the code's `r_lo` comes from the least part at
least 1 over the lanes); so each part loses at most itself below 1, nothing as an integer, and at most `1/2`
otherwise (`part_err`). Over parts each at most `u` times the one before, only the last part at least 1 can be no
integer, every earlier one being at least `2^{53}`; so the coefficient's integer is within `1/2 + 1/(1 - u)` of the
scaled coefficient (`coef_err`).
-/

namespace ExpansionBounds

open Finset

variable {rnd : ℝ → ℤ} (hrnd : ∀ x, |x - rnd x| ≤ 1 / 2)
include hrnd

/-- what a part's extraction may lose: at most itself below 1, nothing for an integer, at most `1/2` otherwise -/
def PartLoss (P e : ℝ) : Prop :=
  (|P| < 1 → |e| ≤ |P|) ∧ (1 ≤ |P| → (∃ z : ℤ, P = z) → e = 0) ∧ (1 ≤ |P| → |e| ≤ 1 / 2)

/-- one part's extraction loses what `PartLoss` allows, given the code's `r_lo` -/
theorem part_err {P : ℝ} {rlo rhi : ℕ} (hr : rlo ≤ rhi)
    (hcode : 1 ≤ |P| → rlo = 0 ∨ ∃ z : ℤ, P = z * 2 ^ (16 * rlo)) :
    PartLoss P (extRem rnd P rhi (rhi - rlo + 1)) := by
  refine ⟨fun h1 => extRem_small hrnd h1 rhi _, fun h1 ⟨z, hz⟩ => ?_, fun h1 => ?_⟩
  · rcases hcode h1 with h0 | ⟨w, hw⟩
    · subst h0
      exact extRem_exact hrnd (z := z) (by simp [hz]) hr
    · exact extRem_exact hrnd hw hr
  · rcases hcode h1 with h0 | ⟨w, hw⟩
    · subst h0
      simpa using extRem_le hrnd P rhi rhi
    · rw [extRem_exact hrnd hw hr]
      norm_num

omit hrnd in
/-- a coefficient's loss over its parts, each at most `u` times the one before and an integer from `2^{52}`: from
part `k` on, at most `|P_k|/(1 - u)` where `|P_k| < 1`, and at most `1/(1 - u)` in all -/
theorem coef_tail {u : ℝ} (hu0 : 0 ≤ u) (hu : u * 2 ^ 53 ≤ 1) {np : ℕ} {P e : ℕ → ℝ}
    (hord : ∀ p, |P (p + 1)| ≤ u * |P p|) (hint : ∀ p, 2 ^ 52 ≤ |P p| → ∃ z : ℤ, P p = z)
    (he : ∀ p, PartLoss (P p) (e p)) (d : ℕ) :
    (|P (np - d)| < 1 → ∑ p ∈ Ico (np - d) np, |e p| ≤ |P (np - d)| / (1 - u)) ∧
      ∑ p ∈ Ico (np - d) np, |e p| ≤ 1 / (1 - u) := by
  have hu1 : u < 1 := by nlinarith
  have h1u : 0 < 1 - u := by linarith
  induction d with
  | zero => simp only [Nat.sub_zero, Ico_self, sum_empty]; exact ⟨fun _ => by positivity, by positivity⟩
  | succ d ih =>
    rcases Nat.lt_or_ge d np with hd | hd
    · -- the parts from `k = np - d - 1` on: part `k`, then those from `k + 1 = np - d`
      set k := np - (d + 1) with hk
      have hk1 : np - d = k + 1 := by omega
      rw [hk1] at ih
      have hsplit : ∑ p ∈ Ico k np, |e p| = |e k| + ∑ p ∈ Ico (k + 1) np, |e p| := by
        rw [sum_eq_sum_Ico_succ_bot (by omega)]
      rw [hsplit]
      obtain ⟨ihs, ihb⟩ := ih
      obtain ⟨hs, hi, hh⟩ := he k
      have hnext := hord k
      refine ⟨fun hk1' => ?_, ?_⟩
      · have hn1 : |P (k + 1)| < 1 := by nlinarith [abs_nonneg (P k)]
        have := ihs hn1
        have h2 : |P (k + 1)| / (1 - u) ≤ u * |P k| / (1 - u) := div_le_div_of_nonneg_right hnext h1u.le
        have h3 : |P k| + u * |P k| / (1 - u) = |P k| / (1 - u) := by field_simp; ring
        linarith [hs hk1']
      · rcases lt_or_ge |P k| 1 with hlt | hge
        · have hn1 : |P (k + 1)| < 1 := by nlinarith [abs_nonneg (P k)]
          have := ihs hn1
          have h2 : |P (k + 1)| / (1 - u) ≤ u * |P k| / (1 - u) := div_le_div_of_nonneg_right hnext h1u.le
          have h3 : |P k| + u * |P k| / (1 - u) = |P k| / (1 - u) := by field_simp; ring
          have h4 : |P k| / (1 - u) ≤ 1 / (1 - u) := div_le_div_of_nonneg_right hlt.le h1u.le
          linarith [hs hlt]
        · by_cases hz : ∃ z : ℤ, P k = z
          · rw [hi hge hz, abs_zero, zero_add]
            exact ihb
          · -- no integer: below `2^{52}`, so the next part is at most `1/2`
            have hb : |P k| < 2 ^ 52 := by
              by_contra hc
              exact hz (hint k (not_lt.mp hc))
            have hn : |P (k + 1)| ≤ 1 / 2 := by
              calc |P (k + 1)| ≤ u * |P k| := hnext
                _ ≤ u * 2 ^ 52 := by gcongr
                _ ≤ 1 / 2 := by nlinarith
            have := ihs (by linarith)
            have h2 : |P (k + 1)| / (1 - u) ≤ (1 / 2) / (1 - u) := div_le_div_of_nonneg_right hn h1u.le
            have h3 : 1 / 2 + (1 / 2) / (1 - u) ≤ 1 / (1 - u) := by
              rw [div_add_div _ _ (by norm_num) h1u.ne', div_le_div_iff₀ (by positivity) h1u]
              nlinarith
            linarith [hh hge]
    · -- past the parts: nothing
      have : np - (d + 1) = np - d := by omega
      rw [this]
      exact ih

omit hrnd in
/-- a coefficient's integer is within `1/(1 - u)` of the scaled coefficient -/
theorem coef_err {u : ℝ} (hu0 : 0 ≤ u) (hu : u * 2 ^ 53 ≤ 1) {np : ℕ} {P e : ℕ → ℝ}
    (hord : ∀ p, |P (p + 1)| ≤ u * |P p|) (hint : ∀ p, 2 ^ 52 ≤ |P p| → ∃ z : ℤ, P p = z)
    (he : ∀ p, PartLoss (P p) (e p)) :
    |∑ p ∈ range np, e p| ≤ 1 / (1 - u) := by
  have h := (coef_tail (np := np) hu0 hu hord hint he np).2
  rw [Nat.sub_self, ← range_eq_Ico] at h
  exact (abs_sum_le_sum_abs _ _).trans h

end ExpansionBounds
