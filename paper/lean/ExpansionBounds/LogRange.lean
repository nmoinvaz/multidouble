import ExpansionBounds.LogThm

/-!
# Lemma 41's range: `x'_0 ∈ [1/2, 2]`

Lemma 41 and Theorem 42 take `1/2 ≤ 2^k x_0 ≤ 2` as a hypothesis. It follows from what LOG's steps (1) and (2) give.
With the start `y_0` within `E` of `ln x`, the reduced `r` within `δ` of `-y_0 - k ln 2` and `|r| ≤ b`,
`|ln(2^k x)| ≤ b + E + δ`, so `2^k x ∈ [e^{-c}, e^c]` with `c = b + E + δ`. And for `x` on `H(θ)` with `x > 0`,
`(1 - ρ)x ≤ x_0 ≤ (1 - ρ)/(1 - 2ρ) x` by `(eq:a0)`. So `c ≤ 3/5` and `ρ ≤ 1/100` put `2^k x_0` in `[1/2, 2]`: LOG has
`b` near `(ln 2)/2` and `E`, `δ` and `ρ` near `u`.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) (n : ℕ)

/-- on `H(θ)` with `2ρ < 1`, a positive `x` has `x_0 > 0` and `(1 - ρ)x ≤ x_0 ≤ (1 - ρ)/(1 - 2ρ) x` -/
theorem Htheta_lead_pos (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 ≤ θ) (hρ : 2 * (θ * u p) < 1) (x : ℕ → ℝ)
    (hH : Htheta p n θ x) (hX0 : 0 < ∑ i ∈ range n, x i) :
    (1 - θ * u p) * ∑ i ∈ range n, x i ≤ x 0 ∧
      x 0 ≤ (1 - θ * u p) / (1 - 2 * (θ * u p)) * ∑ i ∈ range n, x i := by
  obtain ⟨ρ, hρd⟩ : ∃ ρ, ρ = θ * u p := ⟨_, rfl⟩
  obtain ⟨X, hXd⟩ : ∃ X, X = ∑ i ∈ range n, x i := ⟨_, rfl⟩
  have ht := Htheta_tail p n hn θ hθ (by linarith) x hH
  have ha := Htheta_a0 p n hn θ hθ hρ x hH
  rw [← hρd] at hρ ht ha ⊢
  rw [← hXd] at ht ha hX0 ⊢
  have hρ0 : 0 ≤ ρ := by rw [hρd]; exact mul_nonneg hθ (u_pos p).le
  have h1 : 0 < 1 - ρ := by linarith
  have h2 : 0 < 1 - 2 * ρ := by linarith
  have hq : ρ / (1 - ρ) < 1 := by rw [div_lt_one h1]; linarith
  obtain ⟨t1, t2⟩ := abs_le.mp ht
  -- `x_0 > 0`: otherwise `x ≤ x_0(1 - ρ/(1 - ρ)) ≤ 0`
  have hx0 : 0 < x 0 := by
    by_contra hneg
    have hle : x 0 ≤ 0 := not_lt.mp hneg
    rw [abs_of_nonpos hle] at t2
    nlinarith [mul_nonneg (sub_nonneg.mpr hq.le) (neg_nonneg.mpr hle)]
  rw [abs_of_pos hx0] at t1 t2 ha
  rw [abs_of_pos hX0] at ha
  refine ⟨?_, ha⟩
  -- `x ≤ x_0 + ρ/(1 - ρ) x_0 = x_0/(1 - ρ)`
  have h3 : X ≤ x 0 / (1 - ρ) := by
    have : x 0 + ρ / (1 - ρ) * x 0 = x 0 / (1 - ρ) := by field_simp; ring
    linarith
  rw [le_div_iff₀ h1] at h3
  linarith

/-- Lemma 41's range (`lem:fexact`), from LOG's start and reduction: for `x > 0` on `H(θ)`, `y_0` within `E` of
`ln x`, `r` within `δ` of `-y_0 - k ln 2` and `|r| ≤ b`, `2^k x_0` lies between `e^{-c}(1 - ρ)` and
`e^c(1 - ρ)/(1 - 2ρ)` with `c = b + E + δ` -/
theorem log_range (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 ≤ θ) (hρ : 2 * (θ * u p) < 1) (x : ℕ → ℝ) (hH : Htheta p n θ x)
    (hX0 : 0 < ∑ i ∈ range n, x i) (Y0 R : ℝ) (k : ℤ) (E δ b : ℝ)
    (hE : |Y0 - Real.log (∑ i ∈ range n, x i)| ≤ E) (hδ : |R - (-Y0 - k * Real.log 2)| ≤ δ) (hb : |R| ≤ b) :
    Real.exp (-(b + E + δ)) * (1 - θ * u p) ≤ (2 : ℝ) ^ k * x 0 ∧
      (2 : ℝ) ^ k * x 0 ≤ Real.exp (b + E + δ) * ((1 - θ * u p) / (1 - 2 * (θ * u p))) := by
  obtain ⟨l1, l2⟩ := Htheta_lead_pos p n hn θ hθ hρ x hH hX0
  obtain ⟨ρ, hρd⟩ : ∃ ρ, ρ = θ * u p := ⟨_, rfl⟩
  obtain ⟨X, hXd⟩ : ∃ X, X = ∑ i ∈ range n, x i := ⟨_, rfl⟩
  rw [← hρd] at hρ l1 l2 ⊢
  rw [← hXd] at hX0 hE l1 l2
  have hρ0 : 0 ≤ ρ := by rw [hρd]; exact mul_nonneg hθ (u_pos p).le
  have h1 : 0 < 1 - ρ := by linarith
  have h2 : 0 < 1 - 2 * ρ := by linarith
  -- `|k ln 2 + ln x| ≤ b + E + δ`
  obtain ⟨e1, e2⟩ := abs_le.mp hE
  obtain ⟨d1, d2⟩ := abs_le.mp hδ
  obtain ⟨b1, b2⟩ := abs_le.mp hb
  have hk : (2 : ℝ) ^ k * X = Real.exp (k * Real.log 2 + Real.log X) := by
    rw [Real.exp_add, Real.exp_log hX0, exp_int_mul_log_two]
  have hlo : Real.exp (-(b + E + δ)) ≤ (2 : ℝ) ^ k * X := by
    rw [hk]
    exact Real.exp_le_exp.mpr (by linarith)
  have hhi : (2 : ℝ) ^ k * X ≤ Real.exp (b + E + δ) := by
    rw [hk]
    exact Real.exp_le_exp.mpr (by linarith)
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  constructor
  · calc Real.exp (-(b + E + δ)) * (1 - ρ) ≤ (2 : ℝ) ^ k * X * (1 - ρ) := mul_le_mul_of_nonneg_right hlo h1.le
      _ = (2 : ℝ) ^ k * ((1 - ρ) * X) := by ring
      _ ≤ (2 : ℝ) ^ k * x 0 := mul_le_mul_of_nonneg_left l1 h2k.le
  · calc (2 : ℝ) ^ k * x 0 ≤ (2 : ℝ) ^ k * ((1 - ρ) / (1 - 2 * ρ) * X) := mul_le_mul_of_nonneg_left l2 h2k.le
      _ = (2 : ℝ) ^ k * X * ((1 - ρ) / (1 - 2 * ρ)) := by ring
      _ ≤ Real.exp (b + E + δ) * ((1 - ρ) / (1 - 2 * ρ)) :=
        mul_le_mul_of_nonneg_right hhi (div_nonneg h1.le h2.le)

/-- `e^{3/5} ≤ 183/100` -/
theorem exp_three_fifths_le : Real.exp (3 / 5) ≤ 183 / 100 := by
  have h := Real.exp_bound (x := 3 / 5) (by rw [abs_of_nonneg (by norm_num)]; norm_num) (n := 4) (by norm_num)
  have h' := (abs_le.mp h).2
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 5)] at h'
  norm_num [sum_range_succ, Nat.factorial] at h'
  linarith

/-- Lemma 41's range in LOG's regime: `b + E + δ ≤ 3/5` and `ρ ≤ 1/100` give `1/2 ≤ 2^k x_0 ≤ 2` -/
theorem log_range_half_two (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 ≤ θ) (hρ : θ * u p ≤ 1 / 100) (x : ℕ → ℝ)
    (hH : Htheta p n θ x) (hX0 : 0 < ∑ i ∈ range n, x i) (Y0 R : ℝ) (k : ℤ) (E δ b : ℝ)
    (hE : |Y0 - Real.log (∑ i ∈ range n, x i)| ≤ E) (hδ : |R - (-Y0 - k * Real.log 2)| ≤ δ) (hb : |R| ≤ b)
    (hc : b + E + δ ≤ 3 / 5) : 1 / 2 ≤ (2 : ℝ) ^ k * x 0 ∧ (2 : ℝ) ^ k * x 0 ≤ 2 := by
  obtain ⟨r1, r2⟩ := log_range p n hn θ hθ (by linarith) x hH hX0 Y0 R k E δ b hE hδ hb
  obtain ⟨ρ, hρd⟩ : ∃ ρ, ρ = θ * u p := ⟨_, rfl⟩
  rw [← hρd] at hρ r1 r2
  have hρ0 : 0 ≤ ρ := by rw [hρd]; exact mul_nonneg hθ (u_pos p).le
  have h35 := exp_three_fifths_le
  have hup : Real.exp (b + E + δ) ≤ 183 / 100 := (Real.exp_le_exp.mpr hc).trans h35
  have hpos : 0 < Real.exp (b + E + δ) := Real.exp_pos _
  -- `e^{-c} = 1/e^c ≥ 100/183`
  have hlow : 100 / 183 ≤ Real.exp (-(b + E + δ)) := by
    rw [Real.exp_neg, le_inv_comm₀ (by norm_num) hpos]
    exact hup.trans (by norm_num)
  have h2 : 0 < 1 - 2 * ρ := by linarith
  constructor
  · refine le_trans ?_ r1
    nlinarith
  · refine r2.trans ?_
    have hfrac : (1 - ρ) / (1 - 2 * ρ) ≤ 99 / 98 := by
      rw [div_le_iff₀ h2]
      linarith
    calc Real.exp (b + E + δ) * ((1 - ρ) / (1 - 2 * ρ)) ≤ 183 / 100 * (99 / 98) :=
          mul_le_mul hup hfrac (div_nonneg (by linarith) h2.le) (by norm_num)
      _ ≤ 2 := by norm_num

variable [Prec_gt_0 p]

/-- Theorem 42 (`thm:log`) for a case, with the range of `x'_0` proved: for `x` on `H(θ)` with `ρ ≤ 1/100` and
`b + E + δ ≤ 3/5`, `2^k x_0` lies in `[1/2, 2]`; the scaling keeps such a part, so the hypothesis
`1/2 ≤ x'_0 ≤ 2` of `thm42_case` holds -/
theorem thm42_case_ladder (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {η₁ η₂ ηx ηp ηc : ℝ}
    {S₁ S₂ Sx Sp Sc : ℝ → ℝ} (hS₁ : Scl p η₁ S₁) (hS₂ : Scl p η₂ S₂) (hSx : Scl p ηx Sx) (hSp : Scl p ηp Sp)
    (hSc : Scl p ηc Sc) (x : ℕ → ℝ)
    (hx : ∀ i < n, F p (x i)) (hX0 : 0 < ∑ i ∈ range n, x i) (θ : ℝ) (hθ : 0 ≤ θ) (hρ : θ * u p ≤ 1 / 100)
    (hH : Htheta p n θ x) (y0 : ℕ → ℝ) (hy0 : ∀ i < n, F p (y0 i))
    (πy : ℕ → ℝ) (hπy : ∀ i < n, |y0 i| ≤ πy i) (ℓ E : ℝ) (hℓ : |Real.log (∑ i ∈ range n, x i)| ≤ ℓ)
    (hE : |∑ i ∈ range n, y0 i - Real.log (∑ i ∈ range n, x i)| ≤ E)
    (r : ℕ → ℝ) (hr : ∀ i < n, F p (r i)) (k : ℤ) (δ : ℝ)
    (hδ : |∑ i ∈ range n, r i - (-∑ i ∈ range n, y0 i - k * Real.log 2)| ≤ δ) (a b : ℝ)
    (ha : a ≤ |∑ i ∈ range n, r i|) (hb : |∑ i ∈ range n, r i| ≤ b) (hc : b + E + δ ≤ 3 / 5)
    (π : ℕ → ℝ) (hπ : ∀ i < n, |r i| ≤ π i)
    (pos : Bool) (hsgn : if pos then 0 ≤ ∑ i ∈ range n, r i else ∑ i ∈ range n, r i ≤ 0)
    (e : ℤ) (hU : ∑ i ∈ range n, |r i| < (2 : ℝ) ^ (e + 1)) (m d' : ℕ)
    (hd : 1 ≤ d') (hbd : coreBp n e m b η₁ < d' + 2) (hb2 : 0 < η₁ → Real.exp (coreBp n e m b η₁) ≤ 2)
    (Fk : ℕ → ℕ → ℝ) (hF : ∀ k, ∀ i < n, F p (Fk k i))
    (φF : ℕ → ℝ) (hφF : ∀ k, |∑ i ∈ range n, Fk k i - invF k| ≤ φF k)
    (πx : ℕ → ℝ) (hπx0 : ∀ i, 0 ≤ πx i) (hπx : ∀ i < n, |Sx ((2 : ℝ) ^ k * x i)| ≤ πx i)
    (hSx0 : Sx ((2 : ℝ) ^ k * x 0) = (2 : ℝ) ^ k * x 0) (B eφ et ec : ℤ)
    (hUφ : ∑ i ∈ range n, |logPhi p n Sx k x i| < (2 : ℝ) ^ (eφ + 1))
    (hUt : ∑ i ∈ range n, |expCore p n S₁ S₂ e m r Fk d' i| < (2 : ℝ) ^ (et + 1))
    (hUc : ∑ i ∈ range n, |logC p n Sp B eφ et (logPhi p n Sx k x) (expCore p n S₁ S₂ e m r Fk d') i| <
      (2 : ℝ) ^ (ec + 1))
    (F' : ℕ → ℕ → ℝ) (hF' : ∀ k, ∀ i < n, F p (F' k i)) (φ' : ℕ → ℝ)
    (hφ' : ∀ k, |∑ i ∈ range n, F' k i - logFe k| ≤ φ' k) (q : ℕ) (hq : 2 ≤ q)
    (hC : Real.exp E - 1 + (logCase4 p n η₁ η₂ ηx ηp E pos e m a b δ π Fk φF d' πx B).1 < 1) :
    |(logOp p n Sx Sp Sc y0 x k (expCore p n S₁ S₂ e m r Fk d') B eφ et ec F' q).sum -
        Real.log (∑ i ∈ range n, x i)| ≤
      logBound p n η₁ η₂ ηx ηp ηc ℓ E πy pos e m a b δ π Fk φF d' πx F' φ' q B :=
  thm42_case p n hp hn hA3 hS₁ hS₂ hSx hSp hSc x hx hX0 y0 hy0 πy hπy ℓ E hℓ hE r hr k δ hδ a b ha hb π hπ pos hsgn
    e hU m d' hd hbd hb2 Fk hF φF hφF πx hπx0 hπx
    (by rw [hSx0]; exact log_range_half_two p n hn θ hθ hρ x hH hX0 _ _ k E δ b hE hδ hb hc) B eφ et ec hUφ hUt
    hUc F' hF' φ' hφ' q hq hC

end ExpansionBounds
