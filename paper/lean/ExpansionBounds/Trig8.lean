import ExpansionBounds.Trig8.Low
import ExpansionBounds.Kappa8

/-!
# Theorem 35 at `n = 8` and `p = 53`: the sine and the cosine within `3.163167393u^8`

The octo-double SIN and COS, with multidouble's coefficients and series lengths (`Trig8/Data.lean`), on `x` in `F`, on
`H(2)` and with `|x_0| ≤ 2^52`:

`|SIN_8(x) - sin x| ≤ 3.163167393u^8|sin x| + 5E_π` and `|COS_8(x) - cos x| ≤ 3.163167393u^8|cos x| + 5E_π`,

`E_π = |k| 2^{-1217}`. Each bucket of `|r_0|` takes the `r̄` of the first bucket with its series lengths: `0.78541` in
the top bucket (Lemma 32) and `2^{-j}(1 + 2^{-50})` below. The kernel evaluates Lemma 34's bounds there, rounded up to
200 bits (`Trig8/Run0.lean` to `Run7.lean`), and `C = ε max(δ_S + εu^8, δ_C + εu^8 r̄ tan₊ r̄)` is at most
`3.163167393u^8` in every one of them, the largest in the top bucket. Below the top bucket it is smaller
(`Trig8/Low.lean`), which gives the remark after the theorem: `2.175822u^8` for `|r_0| < 1/2` and `2.000706u^8` for
`|r_0| < 2^{-5}` (`thm35_sincos_8_half`, `thm35_sincos_8_32`).
-/

namespace ExpansionBounds

open Finset

/-- the run of buckets of `t = |r_0|`: the last whose first bucket `j` has `t < 2^{-j}`, the top one if none -/
noncomputable def trig8G (t : ℝ) : ℕ × ℕ × ℕ :=
  ((trig8Groups.filter fun g => decide (t < (2 : ℝ) ^ (-(g.1 : ℤ)))).getLast?).getD (0, 41, 41)

/-- SINR's series length `K_s` by `|r_0|` -/
noncomputable def trig8Ks (t : ℝ) : ℕ := (trig8G t).2.1

/-- COSR's series length `K_c` by `|r_0|` -/
noncomputable def trig8Kc (t : ℝ) : ℕ := (trig8G t).2.2

/-- SINR's coefficients -/
noncomputable def trig8FsR (k i : ℕ) : ℝ := ((trig8FsQ k i : ℚ) : ℝ)

/-- COSR's coefficients -/
noncomputable def trig8FcR (k i : ℕ) : ℝ := ((trig8FcQ k i : ℚ) : ℝ)

theorem trig8G_spec (t : ℝ) :
    trig8G t ∈ trig8Groups ∧ ((trig8G t).1 ≠ 0 → t < (2 : ℝ) ^ (-((trig8G t).1 : ℤ))) := by
  unfold trig8G
  generalize hl : (trig8Groups.filter fun g => decide (t < (2 : ℝ) ^ (-(g.1 : ℤ)))).getLast? = o
  rcases o with _ | g
  · exact ⟨by decide, fun h => (h rfl).elim⟩
  · obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hl
    have hm : g ∈ trig8Groups.filter fun g => decide (t < (2 : ℝ) ^ (-(g.1 : ℤ))) := by
      rw [hys]
      simp
    obtain ⟨h1, h2⟩ := List.mem_filter.mp hm
    exact ⟨h1, fun _ => of_decide_eq_true h2⟩

theorem trig8Rb_nonneg (j : ℕ) : 0 ≤ trig8Rb j := by
  unfold trig8Rb
  split_ifs <;> positivity

theorem trig8Ab_nonneg (i : ℕ) : 0 ≤ trig8Ab i := by
  unfold trig8Ab abarQ trig8U
  exact mul_nonneg (pow_nonneg (by norm_num) i) (by norm_num)

/-- a table's rows have at most eight parts, so its coefficients vanish past them -/
theorem dyFn_getD_zero (T : List (List (ℤ × ℕ))) (hT : ∀ t ∈ T, t.length ≤ 8) (k : ℕ) {i : ℕ} (hi : 8 ≤ i) :
    dyFn (T.getD k []) i = 0 := by
  apply dyFn_of_le
  by_cases hk : k < T.length
  · have hm : T.getD k [] ∈ T := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      exact List.getElem_mem hk
    exact (hT _ hm).trans hi
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    exact Nat.zero_le i

/-- the tables: at most eight parts to a coefficient, every part in `F`, and series of at least two terms -/
theorem trig8_tables : (∀ t ∈ trig8Fs, t.length ≤ 8) ∧ (∀ t ∈ trig8Fc, t.length ≤ 8) ∧
    (∀ t ∈ trig8Fs, ∀ q ∈ t, rnQ 53 (dyQ q) = dyQ q) ∧ (∀ t ∈ trig8Fc, ∀ q ∈ t, rnQ 53 (dyQ q) = dyQ q) ∧
    ∀ g ∈ trig8Groups, 2 ≤ g.2.1 ∧ 2 ≤ g.2.2 := by
  decide +kernel

/-- `r̄` below the last bucket: `u^4(1 + 2^{-50})` -/
def trig8T : ℚ := trig8U ^ 4 * (1 + 1 / 2 ^ 50)

/-- below the last bucket SINR returns `r` and COSR `1`, within `r̄²/(6 - r̄²)` and `r̄²/(2cos₋ r̄)`, which with `C`
there are below the least of the bounds, `2.000706u^8` -/
theorem trig8_tiny : trig8T ≤ 8 / 10 ∧ trig8T ^ 2 < 6 ∧ 0 < cosLoQ trig8T ∧ trig8T ^ 2 / (6 - trig8T ^ 2) ≤ 1 / 2 ∧
    trig8T ^ 2 / (2 * cosLoQ trig8T) ≤ 1 / 2 ∧
    trigCQ trig8U 8 (trig8T ^ 2 / (6 - trig8T ^ 2)) (trig8T ^ 2 / (2 * cosLoQ trig8T)) trig8T ≤
      2000706 / 1000000 * trig8U ^ 8 ∧
    trig8T ^ 2 / (6 - trig8T ^ 2) ≤ 2000706 / 1000000 * trig8U ^ 8 ∧
    trig8T ^ 2 / (2 * cosLoQ trig8T) ≤ 2000706 / 1000000 * trig8U ^ 8 := by
  decide +kernel

variable (p : ℤ) [Prec_gt_0 p]

/-- the coefficients of a table whose parts are in `F` are in `F` -/
theorem dyFn_getD_F (T : List (List (ℤ × ℕ))) (hF : ∀ t ∈ T, ∀ l, F p (dyFn t l : ℝ)) (k i : ℕ) :
    F p ((dyFn (T.getD k []) i : ℚ) : ℝ) := by
  by_cases hk : k < T.length
  · have hm : T.getD k [] ∈ T := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      exact List.getElem_mem hk
    exact hF _ hm i
  · have e : T.getD k [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [e, dyFn_of_le [] (Nat.zero_le i), Rat.cast_zero]
    exact F_zero p

/-- the runs of buckets follow each other: their first buckets increase -/
theorem trig8_sorted : trig8Groups.Pairwise fun a b => a.1 < b.1 := by decide

/-- `t < 2^{-j}`, for `j` the first bucket of a run, falls in that run or in a later one -/
theorem trig8G_ge (t : ℝ) {g0 : ℕ × ℕ × ℕ} (h0 : g0 ∈ trig8Groups) (ht : t < (2 : ℝ) ^ (-(g0.1 : ℤ))) :
    g0.1 ≤ (trig8G t).1 := by
  unfold trig8G
  have hm0 : g0 ∈ trig8Groups.filter fun g => decide (t < (2 : ℝ) ^ (-(g.1 : ℤ))) :=
    List.mem_filter.mpr ⟨h0, decide_eq_true ht⟩
  generalize hl : (trig8Groups.filter fun g => decide (t < (2 : ℝ) ^ (-(g.1 : ℤ)))).getLast? = o
  rcases o with _ | g
  · rw [List.getLast?_eq_none_iff] at hl
    rw [hl] at hm0
    simp at hm0
  · obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hl
    have hp : (ys ++ [g]).Pairwise fun a b => a.1 < b.1 := by
      rw [← hys]
      exact trig8_sorted.filter _
    rw [hys] at hm0
    show g0.1 ≤ g.1
    rcases List.mem_append.mp hm0 with h | h
    · exact ((List.pairwise_append.mp hp).2.2 _ h g (by simp)).le
    · rw [List.mem_singleton.mp h]

/-- `C ≤ c u^8` on the last states of Horner's runs in the run of buckets `g` -/
def Trig8GroupLe (c : ℚ) (g : ℕ × ℕ × ℕ) : Prop :=
  ∀ sS sC, trig8Run sinCQ trig8FsQ g.1 (g.2.1 - 1) 0 (g.2.1 - 2) (trig8Init sinCQ trig8FsQ (g.2.1 - 1)) = sS →
    trig8Run cosCQ trig8FcQ g.1 (g.2.2 - 1) 0 (g.2.2 - 2) (trig8Init cosCQ trig8FcQ (g.2.2 - 1)) = sC →
    trig8CLe c g.1 g.2.1 g.2.2 sS sC

/-- Theorem 35 (`thm:trig`) for SIN and COS at `n = 8` and `p = 53` with the bound `c u^8`, for a `c ≥ 2.000706` that
bounds `C` in the run of buckets of `|r_0|` -/
theorem thm35_sincos_8_c (hp : p = 53) (x : ℕ → ℝ) (hx : ∀ i < 8, F p (x i)) (hH : Htheta p 8 2 x)
    (hx0 : |x 0| ≤ 2 ^ 52) (es : ℝ → ℤ) (c : ℚ) (hc : 2000706 / 1000000 ≤ c)
    (hcg : Trig8GroupLe c (trig8G |redR p 8 x 0|)) :
    |∑ i ∈ range 8, sinN p 8 es trig8Ks trig8Kc trig8FsR trig8FcR x i - Real.sin (∑ i ∈ range 8, x i)| ≤
        (c : ℝ) * u p ^ 8 * |Real.sin (∑ i ∈ range 8, x i)| +
          5 * (|(redK p 8 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) ∧
      |∑ i ∈ range 8, cosN p 8 es trig8Ks trig8Kc trig8FsR trig8FcR x i - Real.cos (∑ i ∈ range 8, x i)| ≤
        (c : ℝ) * u p ^ 8 * |Real.cos (∑ i ∈ range 8, x i)| +
          5 * (|(redK p 8 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) := by
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
  have hEπ : 0 ≤ 5 * (|(redK 53 8 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) := by positivity
  obtain ⟨hl1, hl2, hr1, hr2, hK⟩ := trig8_tables
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := trig8_tiny
  have hFs : ∀ k, ∀ i < 8, F 53 (trig8FsR k i) := fun k i _ =>
    dyFn_getD_F 53 trig8Fs (dyF_of_all 53 trig8Fs hr1) k i
  have hFc : ∀ k, ∀ i < 8, F 53 (trig8FcR k i) := fun k i _ =>
    dyFn_getD_F 53 trig8Fc (dyF_of_all 53 trig8Fc hr2) k i
  have hT : ((trig8T : ℚ) : ℝ) = u (53 : ℤ) ^ (8 / 2) * (1 + 1 / 2 ^ 50) := by
    unfold trig8T
    push_cast
    rw [htu]
  have hT0 : (0 : ℝ) ≤ ((trig8T : ℚ) : ℝ) := by
    rw [hT, hu]
    positivity
  have hcT : (0 : ℝ) < cosLo ((trig8T : ℚ) : ℝ) := by
    rw [← cast_cosLo]
    exact_mod_cast t3
  have hu8 : (0 : ℚ) ≤ trig8U ^ 8 := by unfold trig8U; positivity
  have c7 : ((trig8T : ℚ) : ℝ) ^ 2 / (6 - ((trig8T : ℚ) : ℝ) ^ 2) ≤ (c : ℝ) * u (53 : ℤ) ^ 8 := by
    have := (Rat.cast_le (K := ℝ)).mpr (t7.trans (mul_le_mul_of_nonneg_right hc hu8))
    push_cast at this
    rwa [htu] at this
  have c8 : ((trig8T : ℚ) : ℝ) ^ 2 / (2 * cosLo ((trig8T : ℚ) : ℝ)) ≤
      (c : ℝ) * u (53 : ℤ) ^ 8 := by
    have := (Rat.cast_le (K := ℝ)).mpr (t8.trans (mul_le_mul_of_nonneg_right hc hu8))
    push_cast at this
    rwa [htu, cast_cosLo] at this
  by_cases hsmall : |x 0| < u (53 : ℤ) ^ (8 / 2)
  · -- the early return
    obtain ⟨-, hs, hc⟩ := thm35_small 53 8 rfl (by norm_num) x hH hsmall es trig8Ks trig8Kc trig8FsR trig8FcR
    rw [← hT] at hs hc
    have hcoef : 0 ≤ ((trig8T : ℚ) : ℝ) ^ 2 / (2 * cosLo ((trig8T : ℚ) : ℝ)) :=
      div_nonneg (sq_nonneg _) (by linarith)
    exact ⟨hs.trans (le_add_of_le_of_nonneg (mul_le_mul_of_nonneg_right c7 (abs_nonneg _)) hEπ),
      hc.trans ((mul_le_mul_of_nonneg_left (le_abs_self _) hcoef).trans
        (le_add_of_le_of_nonneg (mul_le_mul_of_nonneg_right c8 (abs_nonneg _)) hEπ))⟩
  obtain ⟨hmem, hlt⟩ := trig8G_spec |redR 53 8 x 0|
  obtain ⟨hKs, hKc⟩ := hK _ hmem
  -- the bound on `C` gives the theorem
  have fin : ∀ rb : ℝ, rb ≤ 8 / 10 → |∑ i ∈ range 8, redR 53 8 x i| ≤ rb →
      |∑ i ∈ range 8, x i - redK 53 8 x * (Real.pi / 2)| ≤ rb →
      0 ≤ trigDS 53 8 (redR 53 8 x 0) rb trig8FsR (trig8Ks |redR 53 8 x 0|) →
      trigDS 53 8 (redR 53 8 x 0) rb trig8FsR (trig8Ks |redR 53 8 x 0|) ≤ 1 / 2 →
      0 ≤ trigDC 53 8 (redR 53 8 x 0) rb trig8FcR (trig8Kc |redR 53 8 x 0|) →
      trigDC 53 8 (redR 53 8 x 0) rb trig8FcR (trig8Kc |redR 53 8 x 0|) ≤ 1 / 2 →
      trigC 53 8 (trigDS 53 8 (redR 53 8 x 0) rb trig8FsR (trig8Ks |redR 53 8 x 0|))
        (trigDC 53 8 (redR 53 8 x 0) rb trig8FcR (trig8Kc |redR 53 8 x 0|)) rb ≤
          (c : ℝ) * u (53 : ℤ) ^ 8 →
      |∑ i ∈ range 8, sinN 53 8 es trig8Ks trig8Kc trig8FsR trig8FcR x i - Real.sin (∑ i ∈ range 8, x i)| ≤
          (c : ℝ) * u (53 : ℤ) ^ 8 * |Real.sin (∑ i ∈ range 8, x i)| +
            5 * (|(redK 53 8 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) ∧
        |∑ i ∈ range 8, cosN 53 8 es trig8Ks trig8Kc trig8FsR trig8FcR x i - Real.cos (∑ i ∈ range 8, x i)| ≤
          (c : ℝ) * u (53 : ℤ) ^ 8 * |Real.cos (∑ i ∈ range 8, x i)| +
            5 * (|(redK 53 8 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) := by
    intro rb hrb hr hre a1 a2 a3 a4 hC
    obtain ⟨ks, kc⟩ := thm35_sincos 53 8 rfl (by norm_num) hA3 x hx hH hx0 hsmall es trig8Ks trig8Kc trig8FsR
      trig8FcR hFs hFc hKs hKc rb hrb hr hre a1 a2 a3 a4
    exact ⟨ks.trans (add_le_add (mul_le_mul_of_nonneg_right hC (abs_nonneg _)) le_rfl),
      kc.trans (add_le_add (mul_le_mul_of_nonneg_right hC (abs_nonneg _)) le_rfl)⟩
  by_cases htiny : |redR 53 8 x 0| < u (53 : ℤ) ^ (8 / 2)
  · -- `|r_0|` below the last bucket: SINR returns `r` and COSR `1`
    have hpow : u (53 : ℤ) ^ (8 / 2) = (2 : ℝ) ^ (-212 : ℤ) := by
      rw [hu]
      norm_num
    obtain ⟨hr, hre⟩ := lemma32_bucket 53 8 rfl (by norm_num) (by norm_num) x hx hH hx0 (-212) hpow.le
      (by rw [← hpow]; exact htiny)
    rw [← hpow, ← hT] at hr hre
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
    refine fin _ (((Rat.cast_le (K := ℝ)).mpr t1).trans_eq (by norm_num)) hr hre ?_ ?_ ?_ ?_ ?_
    · rw [eS]; exact_mod_cast h6
    · rw [eS]; exact ((Rat.cast_le (K := ℝ)).mpr t4).trans_eq (by norm_num)
    · rw [eC]; exact_mod_cast h7
    · rw [eC]; exact ((Rat.cast_le (K := ℝ)).mpr t5).trans_eq (by norm_num)
    · rw [eS, eC]
      refine (trigC_le 53 8 htu trig8T le_rfl le_rfl).trans ?_
      have := (Rat.cast_le (K := ℝ)).mpr (t6.trans (mul_le_mul_of_nonneg_right hc hu8))
      push_cast at this
      rwa [htu] at this
  -- a bucket: Lemma 34's bounds, evaluated by the kernel
  obtain ⟨sS, sC, hS, hC, ok1, ok2, -, ok4, ok5⟩ := trig8_all _ hmem
  have ok3 : trigCQ trig8U 8
      (sinDeltaL trig8U 8 (upQ 200) trig8Ab (trig8Rb (trig8G |redR 53 8 x 0|).1) (trig8G |redR 53 8 x 0|).2.1 sS)
      (cosDeltaL trig8U 8 (upQ 200) trig8Ab (trig8Rb (trig8G |redR 53 8 x 0|).1) (trig8G |redR 53 8 x 0|).2.2 sC)
      (trig8Rb (trig8G |redR 53 8 x 0|).1) ≤ c * trig8U ^ 8 := hcg sS sC hS hC
  clear hcg
  have eKs : trig8Ks |redR 53 8 x 0| = (trig8G |redR 53 8 x 0|).2.1 := rfl
  have eKc : trig8Kc |redR 53 8 x 0| = (trig8G |redR 53 8 x 0|).2.2 := rfl
  generalize trig8G |redR 53 8 x 0| = g at *
  have hrb0 := trig8Rb_nonneg g.1
  have hrb6 : trig8Rb g.1 ^ 2 < 6 := by nlinarith
  have hrb0' : (0 : ℝ) ≤ ((trig8Rb g.1 : ℚ) : ℝ) := by exact_mod_cast hrb0
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
  obtain ⟨dS0, dS1, -⟩ := sinTail_le 53 8 htu (le_upQ 200) hA3 trig8Ab_nonneg hrb0 hrb6 trig8FsQ g.2.1 hstS
  obtain ⟨dC0, dC1, -⟩ := cosTail_le 53 8 htu (le_upQ 200) hA3 trig8Ab_nonneg hrb0 ok5 trig8FcQ g.2.2 hstC
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
  have o1 := (Rat.cast_le (K := ℝ)).mpr ok1
  have o2 := (Rat.cast_le (K := ℝ)).mpr ok2
  have o3 := (Rat.cast_le (K := ℝ)).mpr ok3
  push_cast at o1 o2 o3
  rw [htu] at o3
  refine fin _ (((Rat.cast_le (K := ℝ)).mpr ok4).trans_eq (by norm_num)) hr.1 hr.2 ?_ ?_ ?_ ?_ ?_
  · rw [eDS]; exact dS0
  · rw [eDS]; exact dS1.trans o1
  · rw [eDC]; exact dC0
  · rw [eDC]; exact dC1.trans o2
  · rw [eDS, eDC]
    exact (trigC_le 53 8 htu (trig8Rb g.1) dS1 dC1).trans o3


/-- Theorem 35 (`thm:trig`) for SIN and COS at `n = 8` and `p = 53`, with multidouble's coefficients and series
lengths: for `x` in `F`, on `H(2)` and with `|x_0| ≤ 2^52`, the sine and the cosine are within `3.163167393u^8` of
`sin x` and `cos x`, relatively, plus `5E_π` -/
theorem thm35_sincos_8 (hp : p = 53) (x : ℕ → ℝ) (hx : ∀ i < 8, F p (x i)) (hH : Htheta p 8 2 x)
    (hx0 : |x 0| ≤ 2 ^ 52) (es : ℝ → ℤ) :
    |∑ i ∈ range 8, sinN p 8 es trig8Ks trig8Kc trig8FsR trig8FcR x i - Real.sin (∑ i ∈ range 8, x i)| ≤
        3163167393 / 1000000000 * u p ^ 8 * |Real.sin (∑ i ∈ range 8, x i)| +
          5 * (|(redK p 8 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) ∧
      |∑ i ∈ range 8, cosN p 8 es trig8Ks trig8Kc trig8FsR trig8FcR x i - Real.cos (∑ i ∈ range 8, x i)| ≤
        3163167393 / 1000000000 * u p ^ 8 * |Real.cos (∑ i ∈ range 8, x i)| +
          5 * (|(redK p 8 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) := by
  have h := thm35_sincos_8_c p hp x hx hH hx0 es (3163167393 / 1000000000) (by norm_num) (by
    unfold Trig8GroupLe
    intro sS sC hS hC
    subst hS hC
    obtain ⟨sS', sC', hS', hC', -, -, ok3, -, -⟩ := trig8_all _ (trig8G_spec |redR p 8 x 0|).1
    rw [hS', hC']
    exact ok3)
  rw [show ((3163167393 / 1000000000 : ℚ) : ℝ) = 3163167393 / 1000000000 by norm_num] at h
  exact h

/-- the remark after Theorem 35: where `|r_0| < 2^{-J}`, for `J = 1` and `J = 5`, the sine and the cosine are within
`trig8Low J u^8`, `2.175822u^8` and `2.000706u^8` -/
theorem thm35_sincos_8_low (hp : p = 53) (x : ℕ → ℝ) (hx : ∀ i < 8, F p (x i)) (hH : Htheta p 8 2 x)
    (hx0 : |x 0| ≤ 2 ^ 52) (es : ℝ → ℤ) {J : ℕ} (hJ : J = 1 ∨ J = 5)
    (hr : |redR p 8 x 0| < (2 : ℝ) ^ (-(J : ℤ))) :
    |∑ i ∈ range 8, sinN p 8 es trig8Ks trig8Kc trig8FsR trig8FcR x i - Real.sin (∑ i ∈ range 8, x i)| ≤
        (trig8Low J : ℝ) * u p ^ 8 * |Real.sin (∑ i ∈ range 8, x i)| +
          5 * (|(redK p 8 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) ∧
      |∑ i ∈ range 8, cosN p 8 es trig8Ks trig8Kc trig8FsR trig8FcR x i - Real.cos (∑ i ∈ range 8, x i)| ≤
        (trig8Low J : ℝ) * u p ^ 8 * |Real.cos (∑ i ∈ range 8, x i)| +
          5 * (|(redK p 8 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) := by
  obtain ⟨g0, hg0, rfl⟩ : ∃ g0 ∈ trig8Groups, g0.1 = J := by rcases hJ with rfl | rfl <;> decide
  have hge := trig8G_ge |redR p 8 x 0| hg0 hr
  have h1 : 1 ≤ (trig8G |redR p 8 x 0|).1 := by rcases hJ with h | h <;> omega
  refine thm35_sincos_8_c p hp x hx hH hx0 es (trig8Low g0.1) (by unfold trig8Low; split_ifs <;> norm_num) ?_
  unfold Trig8GroupLe
  intro sS sC hS hC
  subst hS hC
  obtain ⟨sS', sC', hS', hC', ok⟩ := trig8_low _ (trig8G_spec |redR p 8 x 0|).1 h1
  rw [hS', hC']
  unfold trig8CLe at ok ⊢
  refine ok.trans (mul_le_mul_of_nonneg_right ?_ (by unfold trig8U; positivity))
  unfold trig8Low
  by_cases h5 : (trig8G |redR p 8 x 0|).1 < 5
  · have h5' : g0.1 < 5 := lt_of_le_of_lt hge h5
    simp only [h5, h5', ↓reduceIte, le_refl]
  · simp only [h5, ↓reduceIte]
    split_ifs <;> norm_num

/-- the remark after Theorem 35 for `|r_0| < 1/2`: the sine and the cosine are within `2.175822u^8` -/
theorem thm35_sincos_8_half (hp : p = 53) (x : ℕ → ℝ) (hx : ∀ i < 8, F p (x i)) (hH : Htheta p 8 2 x)
    (hx0 : |x 0| ≤ 2 ^ 52) (es : ℝ → ℤ) (hr : |redR p 8 x 0| < 1 / 2) :
    |∑ i ∈ range 8, sinN p 8 es trig8Ks trig8Kc trig8FsR trig8FcR x i - Real.sin (∑ i ∈ range 8, x i)| ≤
        2175822 / 1000000 * u p ^ 8 * |Real.sin (∑ i ∈ range 8, x i)| +
          5 * (|(redK p 8 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) ∧
      |∑ i ∈ range 8, cosN p 8 es trig8Ks trig8Kc trig8FsR trig8FcR x i - Real.cos (∑ i ∈ range 8, x i)| ≤
        2175822 / 1000000 * u p ^ 8 * |Real.cos (∑ i ∈ range 8, x i)| +
          5 * (|(redK p 8 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) := by
  have h := thm35_sincos_8_low p hp x hx hH hx0 es (J := 1) (Or.inl rfl) (by
    rw [show (2 : ℝ) ^ (-((1 : ℕ) : ℤ)) = 1 / 2 by norm_num]
    exact hr)
  rw [show ((trig8Low 1 : ℚ) : ℝ) = 2175822 / 1000000 by unfold trig8Low; norm_num] at h
  exact h

/-- the remark after Theorem 35 for `|r_0| < 2^{-5}`: the sine and the cosine are within `2.000706u^8` -/
theorem thm35_sincos_8_32 (hp : p = 53) (x : ℕ → ℝ) (hx : ∀ i < 8, F p (x i)) (hH : Htheta p 8 2 x)
    (hx0 : |x 0| ≤ 2 ^ 52) (es : ℝ → ℤ) (hr : |redR p 8 x 0| < 1 / 32) :
    |∑ i ∈ range 8, sinN p 8 es trig8Ks trig8Kc trig8FsR trig8FcR x i - Real.sin (∑ i ∈ range 8, x i)| ≤
        2000706 / 1000000 * u p ^ 8 * |Real.sin (∑ i ∈ range 8, x i)| +
          5 * (|(redK p 8 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) ∧
      |∑ i ∈ range 8, cosN p 8 es trig8Ks trig8Kc trig8FsR trig8FcR x i - Real.cos (∑ i ∈ range 8, x i)| ≤
        2000706 / 1000000 * u p ^ 8 * |Real.cos (∑ i ∈ range 8, x i)| +
          5 * (|(redK p 8 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) := by
  have h := thm35_sincos_8_low p hp x hx hH hx0 es (J := 5) (Or.inr rfl) (by
    rw [show (2 : ℝ) ^ (-((5 : ℕ) : ℤ)) = 1 / 32 by norm_num]
    exact hr)
  rw [show ((trig8Low 5 : ℚ) : ℝ) = 2000706 / 1000000 by unfold trig8Low; norm_num] at h
  exact h

end ExpansionBounds
