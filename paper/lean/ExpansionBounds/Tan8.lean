import ExpansionBounds.Div8
import ExpansionBounds.Tan8.All
import ExpansionBounds.Trig8

/-!
# Theorem 35 at `n = 8` and `p = 53`: the tangent within `6.418350521u^8`

The octo-double TAN, the quotient of the computed sine and cosine, with multidouble's coefficients and series lengths,
on `x` in `F`, on `H(2)` and with `|x_0| ≤ 2^52`, and at least `2^{8p-1074}` away from the nonzero multiples of `π/2`:

`|TAN_8(x) - tan x| ≤ (6.418350521u^8 + 5E_π/|sin x cos x|)|tan x|`, `E_π = |k| 2^{-1217}`.

In each bucket the kernel checks, on the states of Horner's runs, that the computed sine and cosine are on `H(θ)`
(`θ = 1.4143` in the top bucket and `3` below, where Lemma 34's part bounds leave room) and that `C^T` with
`δ_D = u^8 + κ_DIV(θu)u^9` is at most `6.418350521u^8` (`Tan8/Run0.lean` to `Run3.lean`).
-/

namespace ExpansionBounds

open Finset

/-- below the last bucket: `r` itself over `1`, on `H(3)`, and the early return within `tan₊ r̄/r̄ - 1` -/
theorem tan8_tiny : tan8Chk trig8T (trig8T ^ 2 / (6 - trig8T ^ 2)) (trig8T ^ 2 / (2 * cosLoQ trig8T))
      (fun i => if i < 8 then trig8Ab i else 0) (fun i => if i = 0 then 1 else 0) 3 461400803 ∧
    tanHiQ trig8T / trig8T - 1 ≤ 6418350521 / 1000000000 * trig8U ^ 8 := by
  decide +kernel

variable (p : ℤ) [Prec_gt_0 p]

/-- Theorem 35 (`thm:trig`) for TAN at `n = 8` and `p = 53`, with multidouble's coefficients and series lengths:
for `x` in `F`, on `H(2)`, with `|x_0| ≤ 2^52` and at least `2^{8p-1074}` away from the nonzero multiples of `π/2`,
the tangent is within `6.418350521u^8 + 5E_π/|sin x cos x|` of `tan x`, relatively -/
theorem thm35_tan_8 (hp : p = 53) (x : ℕ → ℝ) (hx : ∀ i < 8, F p (x i)) (hH : Htheta p 8 2 x)
    (hx0 : |x 0| ≤ 2 ^ 52) (es et : ℝ → ℤ)
    (hfar : redK p 8 x ≠ 0 →
      (2 : ℝ) ^ (p * (8 : ℕ) - 1074) ≤ |∑ i ∈ range 8, x i - redK p 8 x * (Real.pi / 2)|) :
    |∑ i ∈ range 8, tanN p 8 es et trig8Ks trig8Kc trig8FsR trig8FcR x i - Real.tan (∑ i ∈ range 8, x i)| ≤
      (6418350521 / 1000000000 * u p ^ 8 + 5 * (|(redK p 8 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) /
        |Real.sin (∑ i ∈ range 8, x i) * Real.cos (∑ i ∈ range 8, x i)|) * |Real.tan (∑ i ∈ range 8, x i)| := by
  subst hp
  have htu : ((trig8U : ℚ) : ℝ) = u (53 : ℤ) := by
    unfold trig8U
    exact u_53_rat 53 rfl
  have hu : u (53 : ℤ) = 1 / 9007199254740992 := by
    rw [← htu]
    unfold trig8U
    norm_num
  have hA3 : (((8 : ℕ) : ℝ) ^ 2 + (8 : ℕ)) * u (53 : ℤ) < 1 := by
    rw [hu]
    norm_num
  have hE : 0 ≤ 5 * (|(redK 53 8 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) /
      |Real.sin (∑ i ∈ range 8, x i) * Real.cos (∑ i ∈ range 8, x i)| := by positivity
  obtain ⟨hl1, hl2, hr1, hr2, hK⟩ := trig8_tables
  obtain ⟨t1, t2, t3, -, -, -, -, -⟩ := trig8_tiny
  obtain ⟨tchk, tsmall⟩ := tan8_tiny
  obtain ⟨⟨kd0a, kd0b⟩, ⟨kd3a, kd3b⟩, kd10⟩ := tan8_kdiv
  have hFs : ∀ k, ∀ i < 8, F 53 (trig8FsR k i) := fun k i _ =>
    dyFn_getD_F 53 trig8Fs (dyF_of_all 53 trig8Fs hr1) k i
  have hFc : ∀ k, ∀ i < 8, F 53 (trig8FcR k i) := fun k i _ =>
    dyFn_getD_F 53 trig8Fc (dyF_of_all 53 trig8Fc hr2) k i
  have hT : ((trig8T : ℚ) : ℝ) = u (53 : ℤ) ^ (8 / 2) * (1 + 1 / 2 ^ 50) := by
    unfold trig8T
    push_cast
    rw [htu]
  by_cases hsmall : |x 0| < u (53 : ℤ) ^ (8 / 2)
  · -- the early return
    have hs := thm35_tan_small 53 8 rfl (by norm_num) x hH hsmall es et trig8Ks trig8Kc trig8FsR trig8FcR
    rw [← hT] at hs
    have c : tanHi ((trig8T : ℚ) : ℝ) / ((trig8T : ℚ) : ℝ) - 1 ≤ 6418350521 / 1000000000 * u (53 : ℤ) ^ 8 := by
      have := (Rat.cast_le (K := ℝ)).mpr tsmall
      push_cast at this
      rwa [htu, cast_tanHi] at this
    exact hs.trans (mul_le_mul_of_nonneg_right (le_add_of_le_of_nonneg c hE) (abs_nonneg _))
  obtain ⟨hmem, hlt⟩ := trig8G_spec |redR 53 8 x 0|
  obtain ⟨hKs, hKc⟩ := hK _ hmem
  -- `tan8Chk` on bounds of `δ_S`, `δ_C`, `ψ_s` and `ψ_c` gives the theorem
  have fin : ∀ (rb dSq dCq : ℚ) (ψsq ψcq : ℕ → ℚ) (θ Kd : ℚ), 0 ≤ rb →
      |∑ i ∈ range 8, redR 53 8 x i| ≤ ((rb : ℚ) : ℝ) →
      |∑ i ∈ range 8, x i - redK 53 8 x * (Real.pi / 2)| ≤ ((rb : ℚ) : ℝ) →
      0 ≤ trigDS 53 8 (redR 53 8 x 0) ((rb : ℚ) : ℝ) trig8FsR (trig8Ks |redR 53 8 x 0|) →
      trigDS 53 8 (redR 53 8 x 0) ((rb : ℚ) : ℝ) trig8FsR (trig8Ks |redR 53 8 x 0|) ≤ ((dSq : ℚ) : ℝ) →
      0 ≤ trigDC 53 8 (redR 53 8 x 0) ((rb : ℚ) : ℝ) trig8FcR (trig8Kc |redR 53 8 x 0|) →
      trigDC 53 8 (redR 53 8 x 0) ((rb : ℚ) : ℝ) trig8FcR (trig8Kc |redR 53 8 x 0|) ≤ ((dCq : ℚ) : ℝ) →
      (∀ i, tanPs 53 8 (redR 53 8 x 0) ((rb : ℚ) : ℝ) trig8FsR (trig8Ks |redR 53 8 x 0|) i ≤ ((ψsq i : ℚ) : ℝ)) →
      (∀ i, tanPc 53 8 (redR 53 8 x 0) ((rb : ℚ) : ℝ) trig8FcR (trig8Kc |redR 53 8 x 0|) i ≤ ((ψcq i : ℚ) : ℝ)) →
      0 ≤ θ → θ ≤ 3 → 0 ≤ kdivQ trig8U 8 (θ * trig8U) → kdivQ trig8U 8 (θ * trig8U) ≤ Kd → Kd ≤ 461400803 →
      tan8Chk rb dSq dCq ψsq ψcq θ Kd →
      |∑ i ∈ range 8, tanN 53 8 es et trig8Ks trig8Kc trig8FsR trig8FcR x i - Real.tan (∑ i ∈ range 8, x i)| ≤
        (6418350521 / 1000000000 * u (53 : ℤ) ^ 8 + 5 * (|(redK 53 8 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) /
          |Real.sin (∑ i ∈ range 8, x i) * Real.cos (∑ i ∈ range 8, x i)|) *
            |Real.tan (∑ i ∈ range 8, x i)| := by
    intro rb dSq dCq ψsq ψcq θ Kd hrb0 hr hre a1 a2 c1 c2 hps hpc hθ0 hθ3 hk0 hk1 hKd
      ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩
    have hrb0' : (0 : ℝ) ≤ ((rb : ℚ) : ℝ) := by exact_mod_cast hrb0
    have hrb' : ((rb : ℚ) : ℝ) ≤ 8 / 10 := ((Rat.cast_le (K := ℝ)).mpr k1).trans_eq (by norm_num)
    have hθ0' : (0 : ℝ) ≤ ((θ : ℚ) : ℝ) := by exact_mod_cast hθ0
    have hθ3' : ((θ : ℚ) : ℝ) ≤ 3 := by exact_mod_cast hθ3
    have hθu : 0 ≤ ((θ : ℚ) : ℝ) * u (53 : ℤ) := mul_nonneg hθ0' (u_pos 53).le
    have hc : (0 : ℝ) < cosLo ((rb : ℚ) : ℝ) := by
      rw [← cast_cosLo]
      exact_mod_cast k2
    have h6 : (0 : ℝ) ≤ 1 - ((rb : ℚ) : ℝ) ^ 2 / 6 := by nlinarith
    -- the quotient's `δ_D`
    have ek : kdiv 53 8 (((θ : ℚ) : ℝ) * u (53 : ℤ)) = ((kdivQ trig8U 8 (θ * trig8U) : ℚ) : ℝ) :=
      kdiv_53 53 rfl 8 θ
    have hD0 : 0 ≤ u (53 : ℤ) ^ 8 + kdiv 53 8 (((θ : ℚ) : ℝ) * u (53 : ℤ)) * u (53 : ℤ) ^ (8 + 1) := by
      rw [ek]
      exact add_nonneg (pow_nonneg (u_pos 53).le _)
        (mul_nonneg ((Rat.cast_nonneg (K := ℝ)).mpr hk0) (pow_nonneg (u_pos 53).le _))
    have hD : u (53 : ℤ) ^ 8 + kdiv 53 8 (((θ : ℚ) : ℝ) * u (53 : ℤ)) * u (53 : ℤ) ^ (8 + 1) ≤
        ((trig8U ^ 8 + Kd * trig8U ^ 9 : ℚ) : ℝ) := by
      rw [ek]
      push_cast
      rw [htu]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right ((Rat.cast_le (K := ℝ)).mpr hk1)
        (pow_nonneg (u_pos 53).le _))
    have hD10 : ((trig8U ^ 8 + Kd * trig8U ^ 9 : ℚ) : ℝ) ≤ 1 / 10 := by
      have h1 : trig8U ^ 8 + Kd * trig8U ^ 9 ≤ trig8U ^ 8 + 461400803 * trig8U ^ 9 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hKd (by unfold trig8U; positivity))
      exact ((Rat.cast_le (K := ℝ)).mpr (h1.trans kd10)).trans_eq (by norm_num)
    -- the ladders of the computed sine and cosine
    have o3 := (Rat.cast_le (K := ℝ)).mpr k3
    have o4 := (Rat.cast_le (K := ℝ)).mpr k4
    have o5 := (Rat.cast_lt (K := ℝ)).mpr k5
    have o7 := (Rat.cast_lt (K := ℝ)).mpr k7
    have o9 := (Rat.cast_le (K := ℝ)).mpr k9
    push_cast at o3 o4 o5 o7 o9
    rw [cast_cosLo] at o7
    rw [htu] at o9
    have sS : ∑ i ∈ Ico 1 8, tanPs 53 8 (redR 53 8 x 0) ((rb : ℚ) : ℝ) trig8FsR (trig8Ks |redR 53 8 x 0|) i ≤
        ∑ i ∈ Ico 1 8, ((ψsq i : ℚ) : ℝ) := sum_le_sum fun i _ => hps i
    have sC : ∑ i ∈ Ico 1 8, tanPc 53 8 (redR 53 8 x 0) ((rb : ℚ) : ℝ) trig8FcR (trig8Kc |redR 53 8 x 0|) i ≤
        ∑ i ∈ Ico 1 8, ((ψcq i : ℚ) : ℝ) := sum_le_sum fun i _ => hpc i
    have lS : (1 - ((rb : ℚ) : ℝ) ^ 2 / 6) * (1 - ((dSq : ℚ) : ℝ)) - ∑ i ∈ Ico 1 8, ((ψsq i : ℚ) : ℝ) ≤
        (1 - ((rb : ℚ) : ℝ) ^ 2 / 6) *
            (1 - trigDS 53 8 (redR 53 8 x 0) ((rb : ℚ) : ℝ) trig8FsR (trig8Ks |redR 53 8 x 0|)) -
          ∑ i ∈ Ico 1 8, tanPs 53 8 (redR 53 8 x 0) ((rb : ℚ) : ℝ) trig8FsR (trig8Ks |redR 53 8 x 0|) i := by
      have := mul_le_mul_of_nonneg_left (sub_le_sub_left a2 1) h6
      linarith
    have lC : cosLo ((rb : ℚ) : ℝ) * (1 - ((dCq : ℚ) : ℝ)) - ∑ i ∈ Ico 1 8, ((ψcq i : ℚ) : ℝ) ≤
        cosLo ((rb : ℚ) : ℝ) *
            (1 - trigDC 53 8 (redR 53 8 x 0) ((rb : ℚ) : ℝ) trig8FcR (trig8Kc |redR 53 8 x 0|)) -
          ∑ i ∈ Ico 1 8, tanPc 53 8 (redR 53 8 x 0) ((rb : ℚ) : ℝ) trig8FcR (trig8Kc |redR 53 8 x 0|) i := by
      have := mul_le_mul_of_nonneg_left (sub_le_sub_left c2 1) hc.le
      linarith
    have key := thm35_tan 53 8 rfl (by norm_num) hA3 x hx hH hx0 hsmall es et trig8Ks trig8Kc trig8FsR trig8FcR
      hFs hFc hKs hKc ((rb : ℚ) : ℝ) hrb' hr hre a1 (a2.trans o3) c1 (c2.trans o4) hθ0'
      (by rw [hu]; nlinarith) hD0 (hD.trans hD10) (lt_of_lt_of_le o5 lS)
      (fun i h1 h8 => by
        have q := (Rat.cast_le (K := ℝ)).mpr (k6 i (mem_Ico.mpr ⟨h1, h8⟩))
        push_cast at q
        rw [htu] at q
        exact (hps i).trans (q.trans (mul_le_mul_of_nonneg_left lS (pow_nonneg hθu _))))
      (lt_of_lt_of_le o7 lC)
      (fun i h1 h8 => by
        have q := (Rat.cast_le (K := ℝ)).mpr (k8 i (mem_Ico.mpr ⟨h1, h8⟩))
        push_cast at q
        rw [htu, cast_cosLo] at q
        exact (hpc i).trans (q.trans (mul_le_mul_of_nonneg_left lC (pow_nonneg hθu _))))
      hfar
    have hCT := (tanCT_le 53 8 htu rb a1 a2 (lt_of_le_of_lt k3 (by norm_num)) c1 c2
      (lt_of_le_of_lt k4 (by norm_num)) hD0 hD).trans o9
    exact key.trans (mul_le_mul_of_nonneg_right (add_le_add hCT le_rfl) (abs_nonneg _))
  by_cases htiny : |redR 53 8 x 0| < u (53 : ℤ) ^ (8 / 2)
  · -- `|r_0|` below the last bucket: SINR returns `r` and COSR `1`
    have hpow : u (53 : ℤ) ^ (8 / 2) = (2 : ℝ) ^ (-212 : ℤ) := by
      rw [hu]
      norm_num
    obtain ⟨hr, hre⟩ := lemma32_bucket 53 8 rfl (by norm_num) (by norm_num) x hx hH hx0 (-212) hpow.le
      (by rw [← hpow]; exact htiny)
    rw [← hpow, ← hT] at hr hre
    have hT0 : (0 : ℚ) ≤ trig8T := by
      unfold trig8T trig8U
      positivity
    have eS : trigDS 53 8 (redR 53 8 x 0) ((trig8T : ℚ) : ℝ) trig8FsR (trig8Ks |redR 53 8 x 0|) =
        ((trig8T ^ 2 / (6 - trig8T ^ 2) : ℚ) : ℝ) := by
      simp only [trigDS, htiny, ↓reduceIte]
      push_cast
      rfl
    have eC : trigDC 53 8 (redR 53 8 x 0) ((trig8T : ℚ) : ℝ) trig8FcR (trig8Kc |redR 53 8 x 0|) =
        ((trig8T ^ 2 / (2 * cosLoQ trig8T) : ℚ) : ℝ) := by
      simp only [trigDC, htiny, ↓reduceIte]
      push_cast
      rw [cast_cosLo]
    have h6 : (0 : ℚ) ≤ trig8T ^ 2 / (6 - trig8T ^ 2) := div_nonneg (sq_nonneg _) (by linarith)
    have h7 : (0 : ℚ) ≤ trig8T ^ 2 / (2 * cosLoQ trig8T) := div_nonneg (sq_nonneg _) (by linarith)
    have hab : ∀ i, abar (2 * u (53 : ℤ)) i = ((trig8Ab i : ℚ) : ℝ) := fun i => by
      unfold trig8Ab
      rw [cast_abar]
      push_cast
      rw [htu]
    refine fin trig8T _ _ _ _ 3 461400803 hT0 hr hre (by rw [eS]; exact_mod_cast h6) (by rw [eS])
      (by rw [eC]; exact_mod_cast h7) (by rw [eC]) (fun i => ?_) (fun i => ?_) (by norm_num) le_rfl kd3a kd3b
      le_rfl tchk
    · simp only [tanPs, htiny, ↓reduceIte]
      split_ifs
      · exact (hab i).le
      · simp
    · simp only [tanPc, htiny, ↓reduceIte]
      split_ifs <;> simp
  -- a bucket: Lemma 34's bounds and the ladders, evaluated by the kernel
  obtain ⟨sS, sC, hS, hC, tok⟩ := tan8_all _ hmem
  have eKs : trig8Ks |redR 53 8 x 0| = (trig8G |redR 53 8 x 0|).2.1 := rfl
  have eKc : trig8Kc |redR 53 8 x 0| = (trig8G |redR 53 8 x 0|).2.2 := rfl
  generalize trig8G |redR 53 8 x 0| = g at *
  have hrb0 := trig8Rb_nonneg g.1
  have hrb8 : trig8Rb g.1 ≤ 8 / 10 := tok.1
  have hcos : 0 < cosLoQ (trig8Rb g.1) := tok.2.1
  have hrb6 : trig8Rb g.1 ^ 2 < 6 := by nlinarith
  have hr : |∑ i ∈ range 8, redR 53 8 x i| ≤ ((trig8Rb g.1 : ℚ) : ℝ) ∧
      |∑ i ∈ range 8, x i - redK 53 8 x * (Real.pi / 2)| ≤ ((trig8Rb g.1 : ℚ) : ℝ) := by
    by_cases hj : g.1 = 0
    · have e : ((trig8Rb g.1 : ℚ) : ℝ) = 78541 / 100000 := by
        simp only [trig8Rb, hj, ↓reduceIte]
        norm_num
      obtain ⟨-, -, h3, -, -⟩ := lemma32_r 53 8 rfl (by norm_num) x hx hH hx0
      rw [e]
      exact ⟨h3, lemma32_re 53 8 rfl (by norm_num) x hH hx0⟩
    · have hlt' := hlt hj
      have e : ((trig8Rb g.1 : ℚ) : ℝ) = (2 : ℝ) ^ (-(g.1 : ℤ)) * (1 + 1 / 2 ^ 50) := by
        simp only [trig8Rb, hj, ↓reduceIte]
        push_cast
        rw [zpow_neg, zpow_natCast, one_div]
      rw [e]
      exact lemma32_bucket 53 8 rfl (by norm_num) (by norm_num) x hx hH hx0 (-(g.1 : ℤ))
        ((not_lt.mp htiny).trans hlt'.le) hlt'
  have hab : (fun i => ((trig8Ab i : ℚ) : ℝ)) = abar (2 * u (53 : ℤ)) := by
    funext i
    unfold trig8Ab
    rw [cast_abar]
    push_cast
    rw [htu]
  have hstS := scHU_ge 53 8 htu (le_upQ 200) (by norm_num) hA3 trig8Ab_nonneg (trig8Rb g.1) sinCQ sinC cast_sinC
    trig8FsQ (fun k i hi => dyFn_getD_zero trig8Fs hl1 k hi) g.2.1
  have hstC := scHU_ge 53 8 htu (le_upQ 200) (by norm_num) hA3 trig8Ab_nonneg (trig8Rb g.1) cosCQ cosC cast_cosC
    trig8FcQ (fun k i hi => dyFn_getD_zero trig8Fc hl2 k hi) g.2.2
  have eS : scHU trig8U 8 (upQ 200) trig8Ab (trig8Rb g.1) sinCQ trig8FsQ g.2.1 = sS := hS
  have eC : scHU trig8U 8 (upQ 200) trig8Ab (trig8Rb g.1) cosCQ trig8FcQ g.2.2 = sC := hC
  rw [eS] at hstS
  rw [eC] at hstC
  obtain ⟨dS0, dS1, pS⟩ := sinTail_le 53 8 htu (le_upQ 200) hA3 trig8Ab_nonneg hrb0 hrb6 trig8FsQ g.2.1 hstS
  obtain ⟨dC0, dC1, pC⟩ := cosTail_le 53 8 htu (le_upQ 200) hA3 trig8Ab_nonneg hrb0 hcos trig8FcQ g.2.2 hstC
  have eDS : trigDS 53 8 (redR 53 8 x 0) ((trig8Rb g.1 : ℚ) : ℝ) trig8FsR (trig8Ks |redR 53 8 x 0|) =
      sinDelta 53 8 (fun i => ((trig8Ab i : ℚ) : ℝ)) ((trig8Rb g.1 : ℚ) : ℝ)
        (fun k i => ((trig8FsQ k i : ℚ) : ℝ)) g.2.1 := by
    simp only [trigDS, htiny, ↓reduceIte]
    rw [hab, eKs]
    rfl
  have eDC : trigDC 53 8 (redR 53 8 x 0) ((trig8Rb g.1 : ℚ) : ℝ) trig8FcR (trig8Kc |redR 53 8 x 0|) =
      cosDelta 53 8 (fun i => ((trig8Ab i : ℚ) : ℝ)) ((trig8Rb g.1 : ℚ) : ℝ)
        (fun k i => ((trig8FcQ k i : ℚ) : ℝ)) g.2.2 := by
    simp only [trigDC, htiny, ↓reduceIte]
    rw [hab, eKc]
    rfl
  have ePS : ∀ i, tanPs 53 8 (redR 53 8 x 0) ((trig8Rb g.1 : ℚ) : ℝ) trig8FsR (trig8Ks |redR 53 8 x 0|) i =
      sinPsi 53 8 (fun i => ((trig8Ab i : ℚ) : ℝ)) ((trig8Rb g.1 : ℚ) : ℝ)
        (fun k i => ((trig8FsQ k i : ℚ) : ℝ)) g.2.1 i := fun i => by
    simp only [tanPs, htiny, ↓reduceIte]
    rw [hab, eKs]
    rfl
  have ePC : ∀ i, tanPc 53 8 (redR 53 8 x 0) ((trig8Rb g.1 : ℚ) : ℝ) trig8FcR (trig8Kc |redR 53 8 x 0|) i =
      cosPsi 53 8 (fun i => ((trig8Ab i : ℚ) : ℝ)) ((trig8Rb g.1 : ℚ) : ℝ)
        (fun k i => ((trig8FcQ k i : ℚ) : ℝ)) g.2.2 i := fun i => by
    simp only [tanPc, htiny, ↓reduceIte]
    rw [hab, eKc]
    rfl
  have hk : 0 ≤ tan8Th g.1 ∧ tan8Th g.1 ≤ 3 ∧ 0 ≤ kdivQ trig8U 8 (tan8Th g.1 * trig8U) ∧
      kdivQ trig8U 8 (tan8Th g.1 * trig8U) ≤ tan8Kd g.1 ∧ tan8Kd g.1 ≤ 461400803 := by
    by_cases hj : g.1 = 0
    · simp only [tan8Th, tan8Kd, hj, ↓reduceIte]
      exact ⟨by norm_num, by norm_num, kd0a, kd0b, by norm_num⟩
    · simp only [tan8Th, tan8Kd, hj, ↓reduceIte]
      exact ⟨by norm_num, le_rfl, kd3a, kd3b, le_rfl⟩
  obtain ⟨hk1, hk2, hk3, hk4, hk5⟩ := hk
  exact fin (trig8Rb g.1) _ _ _ _ (tan8Th g.1) (tan8Kd g.1) hrb0 hr.1 hr.2 (by rw [eDS]; exact dS0)
    (by rw [eDS]; exact dS1) (by rw [eDC]; exact dC0) (by rw [eDC]; exact dC1)
    (fun i => by rw [ePS]; exact pS i) (fun i => by rw [ePC]; exact pC i) hk1 hk2 hk3 hk4 hk5 tok

end ExpansionBounds
