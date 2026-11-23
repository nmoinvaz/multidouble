import ExpansionBounds.SinCos
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Lemma 38: EXP's reduction

Step (1) of EXP takes `k = RN(x_0 c_r)` to the nearest integer, half away from zero, with `c_r = RN(1/ln 2)`, and for
`k ≠ 0` forms `r = ADD(x', MULF(c_ℓ, -k))` with `x' = (x_0 - k c_h, x_1, …)`. The paper takes `p = 53`, a 42-bit
`c_h` and binary64's exponent range. Here `p ≥ 14`, `c_h` is any multiple of `2^{-p-1}`, `c_ℓ` any expansion in `F`,
and the exponent range is unbounded, so `η_0 = 0` and (A2') holds. Part (b) assumes (A3), `(n² + n)u < 1`.
-/

namespace ExpansionBounds

open Finset

/-- rounding to the nearest integer, half away from zero -/
noncomputable def roundAway (y : ℝ) : ℤ := if 0 ≤ y then ⌊y + 1 / 2⌋ else -⌊-y + 1 / 2⌋

theorem roundAway_sub (y : ℝ) : |(roundAway y : ℝ) - y| ≤ 1 / 2 := by
  unfold roundAway
  split_ifs with h
  · have h1 := Int.floor_le (y + 1 / 2)
    have h2 := Int.lt_floor_add_one (y + 1 / 2)
    rw [abs_le]
    constructor <;> linarith
  · have h1 := Int.floor_le (-y + 1 / 2)
    have h2 := Int.lt_floor_add_one (-y + 1 / 2)
    push_cast
    rw [abs_le]
    constructor <;> linarith

theorem roundAway_ne_zero {y : ℝ} (hk : roundAway y ≠ 0) : 1 / 2 ≤ |y| := by
  unfold roundAway at hk
  split_ifs at hk with h
  · have h0 : 0 ≤ ⌊y + 1 / 2⌋ := Int.floor_nonneg.mpr (by linarith)
    have h1 : (1 : ℝ) ≤ ⌊y + 1 / 2⌋ := by exact_mod_cast (show (1 : ℤ) ≤ ⌊y + 1 / 2⌋ by omega)
    have h2 := Int.floor_le (y + 1 / 2)
    rw [abs_of_nonneg h]
    linarith
  · have h0 : 0 ≤ ⌊-y + 1 / 2⌋ := Int.floor_nonneg.mpr (by linarith)
    have h1 : (1 : ℝ) ≤ ⌊-y + 1 / 2⌋ := by exact_mod_cast (show (1 : ℤ) ≤ ⌊-y + 1 / 2⌋ by omega)
    have h2 := Int.floor_le (-y + 1 / 2)
    rw [abs_of_neg (not_le.mp h)]
    linarith

variable (p : ℤ) [Prec_gt_0 p] (n : ℕ)

/-- a multiple of `2^E` below `2^(E + p)` in magnitude is in `F p` -/
theorem F_of_mult {E : ℤ} {z : ℝ} (hz : Mult E z) (hb : |z| < (2 : ℝ) ^ (E + p)) : F p z := by
  by_cases hz0 : z = 0
  · rw [hz0]
    exact F_zero p
  have hmag : FloatSpec.Core.Raux.mag 2 z ≤ E + p := by
    have h := FloatSpec.Core.Raux.mag_le_bpow 2 z (E + p) (by norm_num) hz0 (by exact_mod_cast hb) trivial
    simpa [Std.Do.wp, Std.Do.PostCond.noThrow, pure] using h
  have h : RN p z = z :=
    roundR_eq_of_le (FloatSpec.Core.FLX.FLX_exp p) (FloatSpec.Core.Generic_fmt.Znearest tieEven) hz (by
      show FloatSpec.Core.FLX.FLX_exp p (FloatSpec.Core.Raux.mag 2 z) ≤ E
      unfold FloatSpec.Core.FLX.FLX_exp
      omega)
  have hF := F_RN p z
  rwa [h] at hF

omit [Prec_gt_0 p] in
/-- an element of `F p` at least `2^(E + p - 1)` in magnitude is a multiple of `2^E` -/
theorem mult_of_F {E : ℤ} {x : ℝ} (hx : F p x) (hb : (2 : ℝ) ^ (E + p - 1) ≤ |x|) : Mult E x := by
  have hmag : E + p ≤ FloatSpec.Core.Raux.mag 2 x :=
    FloatSpec.Core.Raux.mag_ge_bpow 2 x (E + p) (by norm_num) (by exact_mod_cast hb)
  refine (F_mult p hx).mono ?_
  show E ≤ FloatSpec.Core.FLX.FLX_exp p (FloatSpec.Core.Raux.mag 2 x)
  unfold FloatSpec.Core.FLX.FLX_exp
  omega

omit [Prec_gt_0 p] in
/-- `G_MULF(α, β_0; Z̄)`'s error bound, with `λ_m = α_m β_0` -/
noncomputable def GmulfE (α : ℕ → ℝ) (β0 Zb : ℝ) : ℝ :=
  gErr p n (pairX p n fun m => α m * β0) Zb (pairR p n fun m => α m * β0)

omit [Prec_gt_0 p] in
/-- `G_MULF(α, β_0; Z̄)`'s part bounds -/
noncomputable def GmulfP (α : ℕ → ℝ) (β0 Zb : ℝ) : ℕ → ℝ :=
  gParts p n (pairX p n fun m => α m * β0) Zb (pairR p n fun m => α m * β0)

/-- `G_MULF` bounds MULF: for `a` with part bounds `α`, `|b| ≤ β_0` and `|ab| ≤ Z̄` -/
theorem mulf_G (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (a : ℕ → ℝ) (b : ℝ) (α : ℕ → ℝ)
    (β0 : ℝ) (ha : ∀ i < n, F p (a i)) (hb : F p b) (hα : ∀ i < n, |a i| ≤ α i) (hβ : |b| ≤ β0) (Zb : ℝ)
    (hZ : |(∑ i ∈ range n, a i) * b| ≤ Zb) :
    |(∑ i ∈ range n, a i) * b - (mulfOp p n a b).sum| ≤ GmulfE p n α β0 Zb ∧
      (∀ i, |(mulfOp p n a b).getD i 0| ≤ GmulfP p n α β0 Zb i) ∧ (∀ i, F p ((mulfOp p n a b).getD i 0)) ∧
      (mulfOp p n a b).length ≤ n := by
  rw [sum_mul] at hZ ⊢
  obtain ⟨r1, r2, r3, -, -, -, -⟩ := lemma13_mulf p n hp hn a b ha hb α β0 hα hβ hA3 Zb hZ
  have hu := u_pos p
  have hfc : ∀ i < n, _ := fun i hi => facts_c p (ha i hi) hb
  have hab : ∀ i < n, |a i * b| ≤ α i * β0 := fun i hi => by
    rw [abs_mul]
    exact mul_le_mul (hα i hi) hβ (abs_nonneg _) ((abs_nonneg _).trans (hα i hi))
  have hF : ∀ m, F p (mulfLevels p n a b m) :=
    (pairOps_levels p n hp hn (fun i => twoProd p (a i) b) _ (fun i _ => ⟨F_RN p _, F_RN p _⟩)
      (fun i hi => (hfc i hi).2.2.trans (mul_le_mul_of_nonneg_left (hab i hi) (by linarith)))
      (fun i hi => (hfc i hi).2.1.trans ((mul_le_mul_of_nonneg_right (us_le_u p) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hab i hi) hu.le))) hA3).2.2.2.2
  obtain ⟨l1, l2, -⟩ := ren_spec p n hn _ (fun i _ => hF i)
  exact ⟨r1, gParts_le p n _ _ _ _ l1 r2 r3, l2, l1⟩

/-- `c_r = RN(1/ln 2)` -/
noncomputable def cR : ℝ := RN p (1 / Real.log 2)

/-- step (1)'s `k`: `RN(x_0 c_r)` to the nearest integer, half away from zero -/
noncomputable def expK (x0 : ℝ) : ℤ := roundAway (RN p (x0 * cR p))

/-- `ε_k = X(|c_r - 1/ln 2| + u c_r)` -/
noncomputable def epsK (X : ℝ) : ℝ := X * (|cR p - 1 / Real.log 2| + u p * cR p)

/-- `r̄_max = (1/2 + ε_k) ln 2 + x̄_t` -/
noncomputable def rMax (X xt : ℝ) : ℝ := (1 / 2 + epsK p X) * Real.log 2 + xt

/-- `α_0 = r̄_max + x̄_t + k̄|ln 2 - c_h|`, with `k̄ = 1075` -/
noncomputable def expA0 (X xt ch : ℝ) : ℝ := rMax p X xt + xt + 1075 * |Real.log 2 - ch|

/-- `x' = (x_0 - k c_h, x_1, …, x_{n-1})` -/
noncomputable def xRed (x : ℕ → ℝ) (ch : ℝ) : ℕ → ℝ := fun i => if i = 0 then x 0 - expK p (x 0) * ch else x i

/-- step (1)'s `r`: `x` for `k = 0`, otherwise `ADD(x', MULF(c_ℓ, -k))` -/
noncomputable def expR (x : ℕ → ℝ) (ch : ℝ) (cl : ℕ → ℝ) : ℕ → ℝ :=
  if expK p (x 0) = 0 then x else pt (addOp p n (xRed p x ch) (pt (mulfOp p n cl (-(expK p (x 0) : ℝ)))))

/-- Lemma 38 (a) (`lem:expred`): `|k| ≤ k̄ = 1075`, `|r_e| ≤ r̄_max` and `|x_0 - k c_h| ≤ α_0`, and for `k ≠ 0`,
`x_0 - k c_h ∈ F` -/
theorem lemma_expred_a (hp : 14 ≤ p) (x : ℕ → ℝ) (hx0 : F p (x 0)) (X xt ch : ℝ) (hX : |x 0| ≤ X)
    (hX1 : X ≤ 745.3) (hxt : |∑ i ∈ range n, x i - x 0| ≤ xt) (hch : Mult (-p - 1) ch)
    (hA0 : expA0 p X xt ch < 1 / 2) :
    |expK p (x 0)| ≤ 1075 ∧ |∑ i ∈ range n, x i - expK p (x 0) * Real.log 2| ≤ rMax p X xt ∧
      |x 0 - expK p (x 0) * ch| ≤ expA0 p X xt ch ∧ (expK p (x 0) ≠ 0 → F p (x 0 - expK p (x 0) * ch)) := by
  obtain ⟨k, hk⟩ : ∃ k, k = expK p (x 0) := ⟨_, rfl⟩
  rw [← hk]
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log 2 := ⟨_, rfl⟩
  obtain ⟨il, hil⟩ : ∃ il, il = 1 / Real.log 2 := ⟨_, rfl⟩
  rw [← hL] at hl1 hl2 hil ⊢
  have hL0 : 0 < L := by linarith
  have hLil : L * il = 1 := by rw [hil]; field_simp
  have hil1 : il ≤ 1.4427 := by rw [hil, div_le_iff₀ hL0]; linarith
  have hil0 : 0 < il := by rw [hil]; positivity
  have hu := u_pos p
  have hu14 : u p ≤ 1 / 16384 := by
    unfold u
    calc (2 : ℝ) ^ (-p) ≤ (2 : ℝ) ^ (-14 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = 1 / 16384 := by norm_num
  have hX0 : 0 ≤ X := (abs_nonneg _).trans hX
  have hxt0 : 0 ≤ xt := (abs_nonneg _).trans hxt
  -- `c_r` within `u/ln 2` of `1/ln 2`
  obtain ⟨c, hc⟩ : ∃ c, c = cR p := ⟨_, rfl⟩
  have hc1 : |c - il| ≤ u p * il := by
    have h := abs_RN_sub_le_us p (1 / Real.log 2)
    rw [← hL, ← hil, abs_of_pos hil0] at h
    rw [hc, cR, ← hL, ← hil]
    exact h.trans (mul_le_mul_of_nonneg_right (us_le_u p) hil0.le)
  have hc0 : 0 ≤ c := by
    rw [abs_le] at hc1
    nlinarith
  have hc2 : c ≤ (1 + u p) * il := by
    rw [abs_le] at hc1
    linarith
  have hc3 : (1 + u p) * c ≤ 2 := by nlinarith
  -- `ε_k ≤ 1/4`
  have hε : epsK p X ≤ 1 / 4 := by
    have e1 : |c - il| + u p * c ≤ u p * il * (2 + u p) :=
      calc |c - il| + u p * c ≤ u p * il + u p * ((1 + u p) * il) :=
            add_le_add hc1 (mul_le_mul_of_nonneg_left hc2 hu.le)
        _ = u p * il * (2 + u p) := by ring
    have e2 : u p * il * (2 + u p) ≤ 1 / 16384 * 1.4427 * (2 + 1 / 16384) :=
      mul_le_mul (mul_le_mul hu14 hil1 hil0.le (by norm_num)) (by linarith) (by linarith) (by norm_num)
    unfold epsK
    rw [← hc, ← hL, ← hil]
    calc X * (|c - il| + u p * c) ≤ X * (1 / 16384 * 1.4427 * (2 + 1 / 16384)) :=
          mul_le_mul_of_nonneg_left (e1.trans e2) hX0
      _ ≤ 745.3 * (1 / 16384 * 1.4427 * (2 + 1 / 16384)) := mul_le_mul_of_nonneg_right hX1 (by norm_num)
      _ ≤ 1 / 4 := by norm_num
  -- `|RN(x_0 c_r) - x_0/ln 2| ≤ ε_k`
  obtain ⟨y, hy⟩ : ∃ y, y = RN p (x 0 * c) := ⟨_, rfl⟩
  have hky : |(k : ℝ) - y| ≤ 1 / 2 := by rw [hk, hy, hc]; exact roundAway_sub _
  have hyx : |y - x 0 * il| ≤ epsK p X := by
    have h := abs_RN_sub_le_u_RN p (x 0 * c)
    have h' := (abs_RN_sub_le_us p (x 0 * c)).trans (mul_le_mul_of_nonneg_right (us_le_u p) (abs_nonneg _))
    rw [← hy] at h h'
    have hxc : |x 0 * c| ≤ X * c := by rw [abs_mul, abs_of_nonneg hc0]; exact mul_le_mul_of_nonneg_right hX hc0
    have hd : |x 0 * (c - il)| ≤ X * |c - il| := by rw [abs_mul]; exact mul_le_mul_of_nonneg_right hX (abs_nonneg _)
    have hs : y - x 0 * il = (y - x 0 * c) + x 0 * (c - il) := by ring
    unfold epsK
    rw [← hc, ← hL, ← hil, hs]
    calc |(y - x 0 * c) + x 0 * (c - il)| ≤ |y - x 0 * c| + |x 0 * (c - il)| := abs_add_le _ _
      _ ≤ u p * (X * c) + X * |c - il| := add_le_add (h'.trans (mul_le_mul_of_nonneg_left hxc hu.le)) hd
      _ = X * (|c - il| + u p * c) := by ring
  have hkx : |(k : ℝ) - x 0 * il| ≤ 1 / 2 + epsK p X := by
    calc |(k : ℝ) - x 0 * il| = |((k : ℝ) - y) + (y - x 0 * il)| := by ring_nf
      _ ≤ |(k : ℝ) - y| + |y - x 0 * il| := abs_add_le _ _
      _ ≤ 1 / 2 + epsK p X := add_le_add hky hyx
  -- `|k| ≤ 1075`
  have hkb : |k| ≤ 1075 := by
    have hx1 : |x 0 * il| ≤ X * 1.4427 := by
      rw [abs_mul, abs_of_pos hil0]
      exact mul_le_mul hX hil1 hil0.le hX0
    have hkr : |(k : ℝ)| < 1076 := by
      have := abs_sub_abs_le_abs_sub (k : ℝ) (x 0 * il)
      nlinarith
    have : ((|k| : ℤ) : ℝ) < 1076 := by rw [Int.cast_abs]; exact hkr
    have : |k| < 1076 := by exact_mod_cast this
    omega
  have hkb' : |(k : ℝ)| ≤ 1075 := by rw [← Int.cast_abs]; exact_mod_cast hkb
  -- `|x_0 - k ln 2| ≤ (1/2 + ε_k) ln 2`
  have hx0k : |x 0 - k * L| ≤ (1 / 2 + epsK p X) * L := by
    have : x 0 - k * L = -(L * ((k : ℝ) - x 0 * il)) := by linear_combination (-(x 0)) * hLil
    rw [this, abs_neg, abs_mul, abs_of_pos hL0, mul_comm]
    exact mul_le_mul_of_nonneg_right hkx hL0.le
  have hre : |∑ i ∈ range n, x i - k * L| ≤ rMax p X xt := by
    unfold rMax
    rw [← hL]
    calc |∑ i ∈ range n, x i - k * L| = |(∑ i ∈ range n, x i - x 0) + (x 0 - k * L)| := by ring_nf
      _ ≤ xt + (1 / 2 + epsK p X) * L := (abs_add_le _ _).trans (add_le_add hxt hx0k)
      _ = (1 / 2 + epsK p X) * L + xt := by ring
  have hA : |x 0 - k * ch| ≤ expA0 p X xt ch := by
    unfold expA0 rMax
    rw [← hL]
    have hkc : |(k : ℝ) * (L - ch)| ≤ 1075 * |L - ch| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hkb' (abs_nonneg _)
    calc |x 0 - k * ch| = |(x 0 - k * L) + k * (L - ch)| := by ring_nf
      _ ≤ (1 / 2 + epsK p X) * L + 1075 * |L - ch| := (abs_add_le _ _).trans (add_le_add hx0k hkc)
      _ ≤ (1 / 2 + epsK p X) * L + xt + xt + 1075 * |L - ch| := by linarith
  refine ⟨hkb, hre, hA, fun hk0 => ?_⟩
  -- for `k ≠ 0`, `|x_0| ≥ 1/4`, so `x_0` and `k c_h` are multiples of `2^{-p-1}`
  have hk1 : expK p (x 0) ≠ 0 := hk ▸ hk0
  have hy2 : 1 / 2 ≤ |y| := by rw [hy, hc]; exact roundAway_ne_zero hk1
  have hx4 : 1 / 4 ≤ |x 0| := by
    have h := abs_RN_le p (x 0 * c)
    rw [← hy, abs_mul, abs_of_nonneg hc0] at h
    nlinarith [abs_nonneg (x 0)]
  have hm0 : Mult (-p - 1) (x 0) := mult_of_F p hx0 (by
    rw [show -p - 1 + p - 1 = (-2 : ℤ) by ring]
    norm_num
    linarith)
  have hm1 : Mult (-p - 1) (k * ch) := by
    obtain ⟨m, hm⟩ := hch
    exact ⟨k * m, by rw [hm]; push_cast; ring⟩
  refine F_of_mult p (hm0.sub hm1) ?_
  rw [show -p - 1 + p = (-1 : ℤ) by ring]
  norm_num
  linarith

/-- `η_ℓ = |ln 2 - c_h - ∑ c_ℓ|` -/
noncomputable def etaL (ch : ℝ) (cl : ℕ → ℝ) : ℝ := |Real.log 2 - ch - ∑ i ∈ range n, cl i|

omit [Prec_gt_0 p] in
/-- `(ε_1, μ) = G_MULF(|c_ℓ|, k̄; k̄|c_ℓ|)`: the error bound -/
noncomputable def redE1 (cl : ℕ → ℝ) : ℝ := GmulfE p n (fun i => |cl i|) 1075 (1075 * |∑ i ∈ range n, cl i|)

omit [Prec_gt_0 p] in
/-- `(ε_1, μ) = G_MULF(|c_ℓ|, k̄; k̄|c_ℓ|)`: the part bounds -/
noncomputable def redMu (cl : ℕ → ℝ) : ℕ → ℝ := GmulfP p n (fun i => |cl i|) 1075 (1075 * |∑ i ∈ range n, cl i|)

/-- `Z̄ = r̄ + k̄η_ℓ + ε_1` of `G_ADD(α, μ; Z̄)` -/
noncomputable def redZ (ch : ℝ) (cl : ℕ → ℝ) (rb : ℝ) : ℝ := rb + 1075 * etaL n ch cl + redE1 p n cl

/-- Lemma 38 (b) (`lem:expred`): for `k ≠ 0` and `|r_e| ≤ r̄`, `|r - r_e| ≤ δ = ε_1 + ε_2 + k̄η_ℓ` and
`|r_i| ≤ π^r_i`, with `(ε_2, π^r) = G_ADD(α, μ; r̄ + k̄η_ℓ + ε_1)` -/
theorem lemma_expred_b (hp : 14 ≤ p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (x : ℕ → ℝ)
    (hx : ∀ i < n, F p (x i)) (X xt ch : ℝ) (cl α : ℕ → ℝ) (hX : |x 0| ≤ X) (hX1 : X ≤ 745.3)
    (hxt : |∑ i ∈ range n, x i - x 0| ≤ xt) (hch : Mult (-p - 1) ch) (hcl : ∀ i < n, F p (cl i))
    (hA0 : expA0 p X xt ch < 1 / 2) (hα0 : expA0 p X xt ch ≤ α 0) (hα : ∀ i, 1 ≤ i → i < n → |x i| ≤ α i)
    (hk : expK p (x 0) ≠ 0) (rb : ℝ) (hrb : |∑ i ∈ range n, x i - expK p (x 0) * Real.log 2| ≤ rb) :
    |∑ i ∈ range n, expR p n x ch cl i - (∑ i ∈ range n, x i - expK p (x 0) * Real.log 2)| ≤
        redE1 p n cl + GaddE p n α (redMu p n cl) (redZ p n ch cl rb) + 1075 * etaL n ch cl ∧
      ∀ i, |expR p n x ch cl i| ≤ GaddP p n α (redMu p n cl) (redZ p n ch cl rb) i := by
  have hp1 : 1 < p := by omega
  obtain ⟨hkb, -, hA, hF0⟩ := lemma_expred_a p n hp x (hx 0 hn) X xt ch hX hX1 hxt hch hA0
  obtain ⟨k, hkdef⟩ : ∃ k, k = expK p (x 0) := ⟨_, rfl⟩
  rw [← hkdef] at hk hkb hA hF0 hrb ⊢
  have hkb' : |(k : ℝ)| ≤ 1075 := by rw [← Int.cast_abs]; exact_mod_cast hkb
  -- `-k ∈ F`, as `|k| < 2^p`
  have hkF : F p (-(k : ℝ)) := by
    refine F_of_mult p (E := 0) ⟨-k, by push_cast; ring⟩ ?_
    rw [abs_neg, zero_add]
    calc |(k : ℝ)| ≤ 1075 := hkb'
      _ < (2 : ℝ) ^ (14 : ℤ) := by norm_num
      _ ≤ (2 : ℝ) ^ p := zpow_le_zpow_right₀ (by norm_num) hp
  obtain ⟨C, hC⟩ : ∃ C, C = ∑ i ∈ range n, cl i := ⟨_, rfl⟩
  have hZm : |(∑ i ∈ range n, cl i) * -(k : ℝ)| ≤ 1075 * |∑ i ∈ range n, cl i| := by
    rw [abs_mul, abs_neg, mul_comm]
    exact mul_le_mul_of_nonneg_right hkb' (abs_nonneg _)
  obtain ⟨m1, m2, m3, m4⟩ := mulf_G p n hp1 hn hA3 cl (-(k : ℝ)) (fun i => |cl i|) 1075 hcl hkF
    (fun _ _ => le_rfl) (by rw [abs_neg]; exact hkb') _ hZm
  obtain ⟨M, hM⟩ : ∃ M, M = pt (mulfOp p n cl (-(k : ℝ))) := ⟨_, rfl⟩
  have hMs : ∑ i ∈ range n, M i = (mulfOp p n cl (-(k : ℝ))).sum := by rw [hM]; exact (list_sum_getD _ n m4).symm
  -- `x'`: its parts in `F` and within `α`, and its sum `x - k c_h`
  obtain ⟨x', hx'⟩ : ∃ x', x' = xRed p x ch := ⟨_, rfl⟩
  have hx'i : ∀ i, x' i = x i - if i = 0 then (k : ℝ) * ch else 0 := fun i => by
    rw [hx', xRed, ← hkdef]
    split_ifs with h
    · rw [h]
    · ring
  have hx'F : ∀ i < n, F p (x' i) := fun i hi => by
    rw [hx'i]
    split_ifs with h
    · rw [h]; exact hF0 hk
    · rw [sub_zero]; exact hx i hi
  have hx'α : ∀ i < n, |x' i| ≤ α i := fun i hi => by
    rw [hx'i]
    split_ifs with h
    · rw [h]; exact hA.trans hα0
    · rw [sub_zero]; exact hα i (by omega) hi
  have hx's : ∑ i ∈ range n, x' i = ∑ i ∈ range n, x i - k * ch := by
    simp only [hx'i, sum_sub_distrib, sum_ite_eq', mem_range, show 0 < n by omega, ite_true]
  -- the exact sum that ADD rounds: `r_e + k(ln 2 - c_h - ∑ c_ℓ)` plus MULF's error
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log 2 := ⟨_, rfl⟩
  rw [← hL] at hrb ⊢
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ i ∈ range n, x i := ⟨_, rfl⟩
  rw [← hS] at hrb hx's ⊢
  rw [← hC] at m1 hZm
  obtain ⟨d, hd⟩ : ∃ d, d = (mulfOp p n cl (-(k : ℝ))).sum - C * -(k : ℝ) := ⟨_, rfl⟩
  have hd1 : |d| ≤ redE1 p n cl := by
    rw [hd, abs_sub_comm]
    unfold redE1
    rw [← hC]
    exact m1
  have heta : |(k : ℝ) * (L - ch - C)| ≤ 1075 * etaL n ch cl := by
    unfold etaL
    rw [← hL, ← hC, abs_mul]
    exact mul_le_mul_of_nonneg_right hkb' (abs_nonneg _)
  have hZe : ∑ i ∈ range n, x' i + ∑ i ∈ range n, M i - (S - k * L) = k * (L - ch - C) + d := by
    rw [hx's, hMs, hd]
    ring
  have hZ : |∑ i ∈ range n, x' i + ∑ i ∈ range n, M i| ≤ redZ p n ch cl rb := by
    have : ∑ i ∈ range n, x' i + ∑ i ∈ range n, M i = (S - k * L) + (k * (L - ch - C) + d) := by
      rw [← hZe]
      ring
    rw [this]
    unfold redZ
    calc |(S - k * L) + (k * (L - ch - C) + d)| ≤ |S - k * L| + (|(k : ℝ) * (L - ch - C)| + |d|) :=
          (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
      _ ≤ rb + (1075 * etaL n ch cl + redE1 p n cl) := add_le_add hrb (add_le_add heta hd1)
      _ = rb + 1075 * etaL n ch cl + redE1 p n cl := by ring
  obtain ⟨a1, a2, -, a4⟩ := add_G p n hp1 hn hA3 x' M α (redMu p n cl) hx'F (fun j _ => by rw [hM]; exact m3 j)
    hx'α (fun j _ => by rw [hM]; exact m2 j) _ hZ
  have hr : expR p n x ch cl = pt (addOp p n x' M) := by
    simp only [expR, ← hkdef, hk, ↓reduceIte, hx', hM]
  have hrs : ∑ i ∈ range n, expR p n x ch cl i = (addOp p n x' M).sum := by
    rw [hr]; exact (list_sum_getD _ n a4).symm
  refine ⟨?_, fun i => by rw [hr]; exact a2 i⟩
  rw [hrs]
  have hsplit : (addOp p n x' M).sum - (S - k * L) = -((∑ i ∈ range n, x' i + ∑ i ∈ range n, M i) -
      (addOp p n x' M).sum) + (k * (L - ch - C) + d) := by
    rw [← hZe]
    ring
  rw [hsplit]
  calc |-((∑ i ∈ range n, x' i + ∑ i ∈ range n, M i) - (addOp p n x' M).sum) + (k * (L - ch - C) + d)|
      ≤ |(∑ i ∈ range n, x' i + ∑ i ∈ range n, M i) - (addOp p n x' M).sum| + (|(k : ℝ) * (L - ch - C)| + |d|) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg]
        exact add_le_add le_rfl (abs_add_le _ _)
    _ ≤ GaddE p n α (redMu p n cl) (redZ p n ch cl rb) + (1075 * etaL n ch cl + redE1 p n cl) :=
        add_le_add a1 (add_le_add heta hd1)
    _ = redE1 p n cl + GaddE p n α (redMu p n cl) (redZ p n ch cl rb) + 1075 * etaL n ch cl := by ring

end ExpansionBounds
