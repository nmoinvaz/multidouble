import ExpansionBounds.MullowCode
import ExpansionBounds.MullowPair

/-!
# `series::mullow`: a coefficient on one lane, and a block pair's integer read out
-/

/-!
## `series::digits`: a coefficient's digits on one lane

A coefficient's scaled parts `P_i` (floats, each at most `u` times the one before, `n_p ≤ 8` of them), split
from `r_hi` down to the code's `r_lo` (or skipped when below `1/2`), give balanced digits `|d_r| ≤ 2^{15}` whose
integer is within `η = 1/(1 - u)` of `α = ∑ P_i`, when `|α| + η ≤ 0.49 · 2^{16t}` (`lane_digits`); the code's
digits on the lane are these (`lane_code`).
-/

namespace ExpansionBounds

open Finset

variable {p : ℤ} [Prec_gt_0 p]

/-- the code's `r_lo` capped at `r_hi` keeps the part a multiple of its lowest digit's weight -/
theorem hcode_min {P : ℝ} {rlo rhi : ℕ} (h : rlo = 0 ∨ ∃ z : ℤ, P = z * 2 ^ (16 * rlo)) :
    min rlo rhi = 0 ∨ ∃ z : ℤ, P = z * 2 ^ (16 * min rlo rhi) := by
  rcases h with h | ⟨z, hz⟩
  · left; omega
  · right
    refine ⟨z * 2 ^ (16 * (rlo - min rlo rhi)), ?_⟩
    rw [hz]
    push_cast
    rw [mul_assoc, ← pow_add, show 16 * (rlo - min rlo rhi) + 16 * min rlo rhi = 16 * rlo by omega]

/-- a coefficient's digits on one lane: balanced, with their integer within `1/(1 - u)` of `∑ P_i` -/
theorem lane_digits (hp : p = 53) {u : ℝ} (hu : u = 2 ^ (-53 : ℤ)) {np t : ℕ} {P : ℕ → ℝ}
    (hF : ∀ i, F p (P i)) (hord : ∀ i, |P (i + 1)| ≤ u * |P i|)
    {rhi rlo : ℕ → ℕ} {sk : ℕ → Prop} [DecidablePred sk] (hsk : ∀ i, sk i → |P i| < 1 / 2)
    (hrhi : ∀ i, ¬ sk i → |P i| < 2 ^ (16 * rhi i + 16) ∧ rhi i < t)
    (hcode : ∀ i, ¬ sk i → 1 ≤ |P i| → rlo i = 0 ∨ ∃ z : ℤ, P i = z * 2 ^ (16 * rlo i))
    (htop : |∑ i ∈ range np, P i| + 1 / (1 - u) ≤ 49 / 100 * 2 ^ (16 * t)) :
    (∀ r, |balDig (rndC p) (fun r => mD p P rhi rlo sk np r) r| ≤ 2 ^ 15) ∧
      |(digVal t (balDig (rndC p) (fun r => mD p P rhi rlo sk np r)) : ℝ) - ∑ i ∈ range np, P i| ≤ 1 / (1 - u) := by
  have hrnd := rndC_err p hp
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hu53 : u * 2 ^ 53 ≤ 1 := by rw [hu, ← zpow_natCast, ← zpow_add₀ two_ne_zero]; norm_num
  refine ⟨fun r => balDig_le hrnd _ r, ?_⟩
  -- each part's loss: the part itself when skipped, else its last remainder
  set e : ℕ → ℝ := fun i => if sk i then P i else extRem (rndC p) (P i) (rhi i) (rhi i - min (rlo i) (rhi i) + 1)
  -- the digit sums' integer is the parts less their losses
  have hsplit : ∑ r ∈ range t, (mD p P rhi rlo sk np r : ℝ) * 2 ^ (16 * r) = ∑ i ∈ range np, (P i - e i) := by
    simp only [mD]
    push_cast
    simp_rw [sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    by_cases hs : sk i
    · simp [e, hs]
    · simp only [e, hs, ↓reduceIte]
      exact qd_sum (p := p) (P i) (min_le_right _ _) (hrhi i hs).2
  have hloss : ∀ i, PartLoss (P i) (e i) := fun i => by
    by_cases hs : sk i
    · simp only [e, hs, ↓reduceIte]
      have := hsk i hs
      exact ⟨fun _ => le_rfl, fun h1 => absurd h1 (by linarith), fun h1 => absurd h1 (by linarith)⟩
    · simp only [e, hs, ↓reduceIte]
      exact part_err hrnd (min_le_right _ _) fun h1 => hcode_min (hcode i hs h1)
  have hint : ∀ i, 2 ^ 52 ≤ |P i| → ∃ z : ℤ, P i = z := fun i h => F_int p (hF i) (by
    rw [hp]; have : (2 : ℝ) ^ 52 = 4503599627370496 := by norm_num
    norm_num; linarith)
  have hE := coef_err (np := np) hu0 hu53 hord hint hloss
  -- no carry out of the top digit
  have hD : |((∑ r ∈ range t, mD p P rhi rlo sk np r * 2 ^ (16 * r) : ℤ) : ℝ)| ≤ 49 / 100 * 2 ^ (16 * t) := by
    push_cast
    rw [hsplit, sum_sub_distrib]
    calc |∑ i ∈ range np, P i - ∑ i ∈ range np, e i| ≤ |∑ i ∈ range np, P i| + |∑ i ∈ range np, e i| := abs_sub _ _
      _ ≤ _ := by linarith
  have hc := carry_top hrnd (fun r => mD p P rhi rlo sk np r) t hD
  have hval : (digVal t (balDig (rndC p) (fun r => mD p P rhi rlo sk np r)) : ℝ) =
      ∑ i ∈ range np, P i - ∑ i ∈ range np, e i := by
    rw [digVal]
    have := balDig_sum (rnd := rndC p) (fun r => mD p P rhi rlo sk np r) t
    rw [hc, zero_mul, sub_zero] at this
    rw [this]
    push_cast
    rw [hsplit, sum_sub_distrib]
  rw [hval, show ∑ i ∈ range np, P i - ∑ i ∈ range np, e i - ∑ i ∈ range np, P i = -∑ i ∈ range np, e i by ring,
    abs_neg]
  exact hE

/-- the code's digits on the lane are the model's -/
theorem lane_code (hp : p = 53) {np : ℕ} (hnp : np ≤ 8) {P : ℕ → ℝ} (hF : ∀ i, F p (P i))
    {rhi rlo : ℕ → ℕ} {sk : ℕ → Prop} [DecidablePred sk] (hrhi : ∀ i, |P i| < 2 ^ (16 * rhi i + 16)) (r : ℕ) :
    cDig p (fun r => cD p P rhi rlo sk r np) r = balDig (rndC p) (fun r => mD p P rhi rlo sk np r) r := by
  refine cDig_eq hp (fun r => (cD_eq hp (rlo := rlo) (sk := sk) hF hrhi r np hnp).1) (fun r => ?_) r
  have h := (cD_eq hp (rlo := rlo) (sk := sk) hF hrhi r np hnp).2
  have : (np : ℤ) * 2 ^ 16 ≤ 2 ^ 50 := by push_cast; omega
  exact h.trans this

end ExpansionBounds

/-!
## `series::load`: a coefficient on one lane, ready for the pair

A coefficient's parts `a_i` (floats, each at most `u` times the one before) scaled by `2^k`, `W - h ≤ e + k ≤ W`,
give digits at most `2^{15}` that are zero for a zero coefficient, and otherwise an integer within `1/(1 - u)` of
`α = 2^k ∑ a_i`, `|α| ≥ 2^{W-h-1}(1 - 2u)`: the hypothesis of `pair_err` (`coef_ok`). `rhi_code` and `rlo_code` give
its hypotheses on `r_hi` and `r_lo` from the code's.
-/

namespace ExpansionBounds

open Finset

variable {p : ℤ} [Prec_gt_0 p]

/-- zero parts give zero digits -/
theorem zero_digits (hp : p = 53) {P : ℕ → ℝ} (hP : ∀ i, P i = 0) (rhi rlo : ℕ → ℕ) (sk : ℕ → Prop)
    [DecidablePred sk] (np r : ℕ) : balDig (rndC p) (fun r => mD p P rhi rlo sk np r) r = 0 := by
  have hrnd := rndC_err p hp
  have h0 : rndC p 0 = 0 := rnd_small hrnd (by norm_num)
  have hE : ∀ rhi n, extRem (rndC p) 0 rhi n = 0 := fun rhi n => by
    induction n with
    | zero => rfl
    | succ n ih => rw [extRem, ih, zero_div, h0]; simp
  have hD : ∀ r, mD p P rhi rlo sk np r = 0 := fun r => by
    refine sum_eq_zero fun i _ => ?_
    split_ifs
    · rfl
    · unfold qd; split_ifs
      · rw [hP, hE, zero_div, h0]
      · rfl
  have hC : ∀ r, carryIn (rndC p) (fun r => mD p P rhi rlo sk np r) r = 0 := fun r => by
    induction r with
    | zero => rfl
    | succ r ih => rw [carryIn, hD, ih]; simpa using h0
  rw [balDig, hD, hC, hC]; ring

/-- a coefficient on one lane gives the hypothesis of `pair_err` -/
theorem coef_ok (hp : p = 53) {u : ℝ} (hu : u = 2 ^ (-53 : ℤ)) {np t W h : ℕ} (hnp : 1 ≤ np) (hW : W = 16 * t - 2)
    (hWh : h + 1 ≤ W) {a : ℕ → ℝ} (hF : ∀ i, F p (a i)) (hord : ∀ i, |a (i + 1)| ≤ u * |a i|) {k : ℤ}
    (hk : a 0 ≠ 0 → ∃ e : ℤ, (2 : ℝ) ^ (e - 1) ≤ |a 0| ∧ |a 0| < 2 ^ e ∧ ((W - h : ℕ) : ℤ) ≤ e + k ∧ e + k ≤ W)
    {rhi rlo : ℕ → ℕ} {sk : ℕ → Prop} [DecidablePred sk] (hsk : ∀ i, sk i → |a i * 2 ^ k| < 1 / 2)
    (hrhi : ∀ i, ¬ sk i → |a i * 2 ^ k| < 2 ^ (16 * rhi i + 16) ∧ rhi i < t)
    (hcode : ∀ i, ¬ sk i → 1 ≤ |a i * 2 ^ k| → rlo i = 0 ∨ ∃ z : ℤ, a i * 2 ^ k = z * 2 ^ (16 * rlo i)) :
    (∀ r, |balDig (rndC p) (fun r => mD p (fun i => a i * 2 ^ k) rhi rlo sk np r) r| ≤ 2 ^ 15) ∧
      ((∑ i ∈ range np, a i * 2 ^ k = 0 ∧
          ∀ r, balDig (rndC p) (fun r => mD p (fun i => a i * 2 ^ k) rhi rlo sk np r) r = 0) ∨
        (|(digVal t (balDig (rndC p) (fun r => mD p (fun i => a i * 2 ^ k) rhi rlo sk np r)) : ℝ) -
            ∑ i ∈ range np, a i * 2 ^ k| ≤ 1 / (1 - u) ∧
          (2 : ℝ) ^ (W - h - 1) * (1 - 2 * u) ≤ |∑ i ∈ range np, a i * 2 ^ k|)) := by
  set P : ℕ → ℝ := fun i => a i * 2 ^ k with hPdef
  have hrnd := rndC_err p hp
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hu4 : u ≤ 1 / 4 := by rw [hu]; norm_num
  have hK : (0 : ℝ) < 2 ^ k := by positivity
  have hFP : ∀ i, F p (P i) := fun i => by simp only [P]; rw [mul_comm]; exact F_zpow_mul p _ (hF i)
  have hordP : ∀ i, |P (i + 1)| ≤ u * |P i| := fun i => by
    simp only [P, abs_mul, abs_of_pos hK]
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hord i) hK.le
  have hbal : ∀ r, |balDig (rndC p) (fun r => mD p P rhi rlo sk np r) r| ≤ 2 ^ 15 := fun r => balDig_le hrnd _ r
  refine ⟨hbal, ?_⟩
  by_cases ha0 : a 0 = 0
  · -- a zero coefficient: every part is zero
    have hz : ∀ i, a i = 0 := fun i => by
      induction i with
      | zero => exact ha0
      | succ i ih => have := hord i; rw [ih, abs_zero, mul_zero] at this; exact abs_nonpos_iff.mp this
    have hPz : ∀ i, P i = 0 := fun i => by simp [P, hz i]
    left
    exact ⟨sum_eq_zero fun i _ => hPz i, zero_digits hp hPz rhi rlo sk np⟩
  · right
    obtain ⟨e, he1, he2, hk1, hk2⟩ := hk ha0
    obtain ⟨hlo, hhi⟩ := alpha_bounds hu0 hu4 hord hnp he1 he2 hWh hk1 hk2
    have hsum : ∑ i ∈ range np, P i = 2 ^ k * ∑ i ∈ range np, a i := by
      rw [mul_sum]; exact sum_congr rfl fun i _ => by simp only [P]; ring
    rw [← hsum] at hlo hhi
    refine ⟨?_, hlo⟩
    refine (lane_digits hp hu hFP hordP hsk hrhi hcode ?_).2
    -- `|α| + η ≤ 2^W (1 + 2u) + 2 ≤ 0.49 · 2^{W + 2}`, `W ≥ 14`
    have hη : 1 / (1 - u) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    have hW2 : (2 : ℝ) ^ (16 * t) = 4 * 2 ^ W := by
      rw [hW, show 16 * t = 2 + (16 * t - 2) by omega, pow_add]; norm_num
    have hW1 : (2 : ℝ) ^ 14 ≤ 2 ^ W := pow_le_pow_right₀ (by norm_num) (by omega)
    have hu3 : u ≤ 1 / 1000 := by rw [hu]; norm_num
    rw [hW2]
    nlinarith

end ExpansionBounds

/-!
## `series::pair`: a block pair's integer at an output index, read out

The inverse transform's rounded values are the weights `C_{q_0 + q}` (the hypothesis `FftExact`, which the code
checks to within `1/4` of an integer but this file does not prove). The code carries them into balanced digits
exactly (`readout`); their integer `V` is the pair's integer over `2^{16 q_0}` (`pairV_shift`). With the scales of
the two blocks cancelling on the output index, `V 2^e` is within `ρ ∑|a_i b_j| 2^{e_2}` of `∑ a_i b_j 2^{e_2}`
(`pair_value`).
-/

namespace ExpansionBounds

open Finset

variable {p : ℤ} [Prec_gt_0 p]

/-- the pair's integer from `q_0` on, over `2^{16 q_0}` -/
theorem pairV_shift (t la lb m q0 : ℕ) (dx dy : ℕ → ℕ → ℤ) :
    pairV t la lb m q0 dx dy =
      2 ^ (16 * q0) * ∑ q ∈ range (2 * t - 1 - q0), convC t la lb m dx dy (q0 + q) * 2 ^ (16 * q) := by
  rw [pairV, mul_sum, sum_Ico_eq_sum_range]
  refine sum_congr rfl fun q _ => ?_
  rw [mul_add, pow_add]; ring

/-- a weight of the pair is at most `l_a t 2^{30}` -/
theorem convC_le_la (t la lb m : ℕ) {dx dy : ℕ → ℕ → ℤ} (hx : ∀ i r, |dx i r| ≤ 2 ^ 15)
    (hy : ∀ j r, |dy j r| ≤ 2 ^ 15) (q : ℕ) : |convC t la lb m dx dy q| ≤ la * (t * 2 ^ 30) := by
  rw [convC_eq]
  calc |∑ i ∈ range la, ∑ j ∈ range lb, onIdx m i j * digConv t (dx i) (dy j) q|
      ≤ ∑ i ∈ range la, |∑ j ∈ range lb, onIdx m i j * digConv t (dx i) (dy j) q| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range la, (t * 2 ^ 30 : ℤ) := sum_le_sum fun i _ => by
        -- one `j` at most has `i + j = m`
        have e : ∑ j ∈ range lb, onIdx m i j * digConv t (dx i) (dy j) q =
            if m - i < lb ∧ i ≤ m then digConv t (dx i) (dy (m - i)) q else 0 := by
          have : ∀ j, onIdx m i j * digConv t (dx i) (dy j) q =
              if m - i = j ∧ i ≤ m then digConv t (dx i) (dy j) q else 0 := fun j => by
            unfold onIdx
            by_cases h : i + j = m
            · rw [ite_eq_left h, ite_eq_left (by omega), one_mul]
            · rw [ite_eq_right h, ite_eq_right (by omega), zero_mul]
          simp_rw [this]
          by_cases hi : i ≤ m
          · simp only [hi, and_true]; rw [sum_ite_eq]; simp [mem_range]
          · simp [hi]
        rw [e]
        split_ifs
        · exact digConv_le t (hx i) (hy _) q
        · simp
    _ = la * (t * 2 ^ 30) := by simp

/-- the code's read-out: weights at most `2^{50}`, zero from `N` on, carried into `n_d ≥ N + 3` balanced digits
exactly, whose integer is the weights' -/
theorem readout (hp : p = 53) {Cs : ℕ → ℤ} {N nd : ℕ} (hC : ∀ q, |Cs q| ≤ 2 ^ 50) (hz : ∀ q, N ≤ q → Cs q = 0)
    (hnd : N + 3 ≤ nd) :
    (∀ r, cDig p (fun q => (Cs q : ℝ)) r = balDig (rndC p) Cs r) ∧ (∀ r, |balDig (rndC p) Cs r| ≤ 2 ^ 15) ∧
      digVal nd (balDig (rndC p) Cs) = ∑ q ∈ range N, Cs q * 2 ^ (16 * q) := by
  have hrnd := rndC_err p hp
  refine ⟨cDig_eq hp (fun r => rfl) hC, balDig_le hrnd Cs, ?_⟩
  have hsum : ∑ r ∈ range nd, Cs r * 2 ^ (16 * r) = ∑ q ∈ range N, Cs q * 2 ^ (16 * q) := by
    rw [← sum_range_add_sum_Ico _ (by omega : N ≤ nd), sum_eq_zero (s := Ico N nd) fun q hq => by
      rw [hz q (mem_Ico.mp hq).1, zero_mul], add_zero]
  -- no carry out: `|∑| ≤ 2^{50} 2^{16N}/(2^{16} - 1) ≤ 0.49 · 2^{16 n_d}`
  have hD : |((∑ r ∈ range nd, Cs r * 2 ^ (16 * r) : ℤ) : ℝ)| ≤ 49 / 100 * 2 ^ (16 * nd) := by
    rw [hsum]
    push_cast
    have h1 : |∑ q ∈ range N, (Cs q : ℝ) * 2 ^ (16 * q)| ≤ 2 ^ 50 * ∑ q ∈ range N, (2 : ℝ) ^ (16 * q) := by
      rw [mul_sum]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun q _ => ?_)
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (16 * q))]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hC q) (by positivity)
    have h2 := sum_pow16_le N
    have h3 : (2 : ℝ) ^ (16 * nd) = 2 ^ (16 * N) * 2 ^ 48 * 2 ^ (16 * (nd - N - 3)) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    have h4 : (1 : ℝ) ≤ 2 ^ (16 * (nd - N - 3)) := one_le_pow₀ (by norm_num)
    have h5 : (0 : ℝ) < 2 ^ (16 * N) := by positivity
    rw [h3]
    calc _ ≤ 2 ^ 50 * ∑ q ∈ range N, (2 : ℝ) ^ (16 * q) := h1
      _ ≤ 2 ^ 50 * (2 ^ (16 * N) / (2 ^ 16 - 1)) := by gcongr
      _ ≤ 49 / 100 * (2 ^ (16 * N) * 2 ^ 48 * 1) := by
          rw [mul_div_assoc', div_le_iff₀ (by norm_num)]; nlinarith
      _ ≤ _ := by gcongr
  have hc := carry_top hrnd Cs nd hD
  have := balDig_sum (rnd := rndC p) Cs nd
  rw [hc, zero_mul, sub_zero, hsum] at this
  exact this

/-- the FFT's hypothesis: its rounded values are the pair's weights from `q_0` on (zero past them) -/
def FftExact (t la lb m q0 : ℕ) (dx dy : ℕ → ℕ → ℤ) (z : ℕ → ℤ) : Prop :=
  ∀ q, z q = if q < 2 * t - 1 - q0 then convC t la lb m dx dy (q0 + q) else 0

/-- a block pair on one lane at output index `m`: the read-out integer `V` times `2^{e}` against the terms, given
each coefficient as `coef_ok` gives it, the plan's `ρ` bound, the FFT's hypothesis, and the scales cancelling -/
theorem pair_value (hp : p = 53) {t la lb m q0 nd : ℕ} (ht : 1 ≤ t) (hq0 : q0 ≤ 2 * t - 1) (hnd : 2 * t + 2 - q0 ≤ nd)
    (hlat : la * t ≤ 2 ^ 20) {dx dy : ℕ → ℕ → ℤ} (hx : ∀ i r, |dx i r| ≤ 2 ^ 15) (hy : ∀ j r, |dy j r| ≤ 2 ^ 15)
    {α β a b : ℕ → ℝ} {η LA LB ρ : ℝ} (hLA : 0 < LA) (hLB : 0 < LB) (hη : 0 ≤ η)
    (hα : ∀ i < la, (α i = 0 ∧ ∀ r, dx i r = 0) ∨ (|(digVal t (dx i) : ℝ) - α i| ≤ η ∧ LA ≤ |α i|))
    (hβ : ∀ j < lb, (β j = 0 ∧ ∀ r, dy j r = 0) ∨ (|(digVal t (dy j) : ℝ) - β j| ≤ η ∧ LB ≤ |β j|))
    (hρ : η / LA + η / LB + η ^ 2 / (LA * LB) + t * 2 ^ 30 * (∑ q ∈ range q0, (2 : ℝ) ^ (16 * q)) / (LA * LB) ≤ ρ)
    {z : ℕ → ℤ} (hfft : FftExact t la lb m q0 dx dy z) {e e2 : ℤ}
    (hab : ∀ i j, i + j = m → α i * β j * 2 ^ (e - 16 * q0) = a i * b j * 2 ^ e2)
    (habs : ∀ i j, i + j = m → |α i| * |β j| * 2 ^ (e - 16 * q0) = |a i| * |b j| * 2 ^ e2) :
    (∀ r, cDig p (fun q => (z q : ℝ)) r = balDig (rndC p) z r) ∧ (∀ r, |balDig (rndC p) z r| ≤ 2 ^ 15) ∧
      |(digVal nd (balDig (rndC p) z) : ℝ) * 2 ^ e -
          ∑ i ∈ range la, ∑ j ∈ range lb, (onIdx m i j : ℝ) * (a i * b j * 2 ^ e2)| ≤
        ρ * ∑ i ∈ range la, ∑ j ∈ range lb, (onIdx m i j : ℝ) * (|a i| * |b j| * 2 ^ e2) := by
  set N := 2 * t - 1 - q0 with hN
  have hC : ∀ q, |z q| ≤ 2 ^ 50 := fun q => by
    rw [hfft q]
    split_ifs
    · refine (convC_le_la t la lb m hx hy _).trans ?_
      have : (la : ℤ) * t ≤ 2 ^ 20 := by exact_mod_cast hlat
      nlinarith
    · simp
  have hz : ∀ q, N ≤ q → z q = 0 := fun q hq => by rw [hfft q, ite_eq_right (by omega)]
  obtain ⟨h1, h2, h3⟩ := readout hp hC hz (by omega : N + 3 ≤ nd)
  refine ⟨h1, h2, ?_⟩
  -- the read-out integer is the pair's integer over `2^{16 q_0}`
  have hV : (pairV t la lb m q0 dx dy : ℝ) = 2 ^ (16 * q0) * (digVal nd (balDig (rndC p) z) : ℝ) := by
    rw [pairV_shift t la lb m q0, h3]
    push_cast
    congr 1
    refine sum_congr rfl fun q hq => ?_
    rw [hfft q, ite_eq_left (mem_range.mp hq)]
  have hp' := pair_err t la lb m q0 hq0 hx hy hLA hLB hη hα hβ
  set E : ℤ := e - 16 * q0
  have hE : (0 : ℝ) < 2 ^ E := by positivity
  have hsc : (2 : ℝ) ^ (16 * q0) * 2 ^ E = 2 ^ e := by
    rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]; congr 1; push_cast; ring
  have hS : (∑ i ∈ range la, ∑ j ∈ range lb, (onIdx m i j : ℝ) * (α i * β j)) * 2 ^ E =
      ∑ i ∈ range la, ∑ j ∈ range lb, (onIdx m i j : ℝ) * (a i * b j * 2 ^ e2) := by
    rw [sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun j _ => ?_
    unfold onIdx
    by_cases h : i + j = m
    · rw [ite_eq_left h, ← hab i j h]; push_cast; ring
    · rw [ite_eq_right h]; push_cast; ring
  have hA : (∑ i ∈ range la, ∑ j ∈ range lb, (onIdx m i j : ℝ) * (|α i| * |β j|)) * 2 ^ E =
      ∑ i ∈ range la, ∑ j ∈ range lb, (onIdx m i j : ℝ) * (|a i| * |b j| * 2 ^ e2) := by
    rw [sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun j _ => ?_
    unfold onIdx
    by_cases h : i + j = m
    · rw [ite_eq_left h, ← habs i j h]; push_cast; ring
    · rw [ite_eq_right h]; push_cast; ring
  have hA0 : 0 ≤ ∑ i ∈ range la, ∑ j ∈ range lb, (onIdx m i j : ℝ) * (|α i| * |β j|) :=
    sum_nonneg fun i _ => sum_nonneg fun j _ => mul_nonneg (by exact_mod_cast onIdx_nonneg m i j) (by positivity)
  have e1 : (digVal nd (balDig (rndC p) z) : ℝ) * 2 ^ e -
      ∑ i ∈ range la, ∑ j ∈ range lb, (onIdx m i j : ℝ) * (a i * b j * 2 ^ e2) =
      ((pairV t la lb m q0 dx dy : ℝ) - ∑ i ∈ range la, ∑ j ∈ range lb, (onIdx m i j : ℝ) * (α i * β j)) * 2 ^ E := by
    rw [sub_mul, hS, hV, ← hsc]; ring
  rw [e1, abs_mul, abs_of_pos hE, ← hA]
  calc _ ≤ (η / LA + η / LB + η ^ 2 / (LA * LB) + t * 2 ^ 30 * (∑ q ∈ range q0, (2 : ℝ) ^ (16 * q)) / (LA * LB)) *
        (∑ i ∈ range la, ∑ j ∈ range lb, (onIdx m i j : ℝ) * (|α i| * |β j|)) * 2 ^ E :=
        mul_le_mul_of_nonneg_right hp' hE.le
    _ ≤ ρ * (∑ i ∈ range la, ∑ j ∈ range lb, (onIdx m i j : ℝ) * (|α i| * |β j|)) * 2 ^ E := by gcongr
    _ = _ := by ring

end ExpansionBounds
