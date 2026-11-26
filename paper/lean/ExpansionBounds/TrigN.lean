import ExpansionBounds.TrigN.Defs
import ExpansionBounds.Tan8

/-!
# Theorem 35 at any `n` and `p = 53`: the sine, the cosine and the tangent from a table

`Trig8.lean` and `Tan8.lean` for a table `T` of any `n` from 2 to 38: with the series' coefficients and lengths of
`T`, on `x` in `F`, on `H(2)` and with `|x_0| ≤ 2^52`,

`|SIN_n(x) - sin x| ≤ c u^n|sin x| + 5E_π` and `|COS_n(x) - cos x| ≤ c u^n|cos x| + 5E_π`,

for a `c` that the kernel checked in every run of buckets (`T.Group c`), on the tables (`T.TabOk`) and below the last
bucket (`T.TinyOk c`); and `|TAN_n(x) - tan x| ≤ (c u^n + 5E_π/|sin x cos x|)|tan x|` for a `c` checked with the
quotient's ladders (`T.TanGroup`, `T.KdivOk`, `T.TanTinyOk`), where `|x - kπ/2| ≥ 2^{np-1074}` if RED's `k` is not
zero (`hfar`). From `n = 21` on that bound exceeds every `|x - kπ/2| ≤ 0.78541`, so the tangent's theorem applies
there only where `k` is zero.

The paper states Theorem 35 for even `n`. The theorems here also take odd `n`, for the algorithm whose early
return and last bucket test `|x_0| < u^{⌊n/2⌋}` and `|r_0| < u^{⌊n/2⌋}`, as `n/2` is the floor.

`T.groups` lists the runs of buckets by their first bucket, and the theorems ask that its head be the run of bucket 0
(`hhead`). `G` picks the run of `|r_0|` by bucket number, so the other runs may come in any order: where they start at
distinct buckets, as in the generated tables, every `|r_0|` gets the series lengths of its own run.

The remark after Theorem 35 gives the bounds at `n = 2`, `4` and `12`; `Trig2.lean`, `Trig4.lean` and `Trig12.lean`
prove them with these, the last outside the default build.
-/

namespace ExpansionBounds

open Finset

namespace TrigTab

variable (T : TrigTab)

/-- the run of buckets of `t = |r_0|`: of the runs whose first bucket `j` has `t < 2^{-j}`, the one with the largest
`j`, the first of them in `T.groups` if two start at the same bucket (`G_max`); the top one if none -/
noncomputable def G (t : ℝ) : ℕ × ℕ × ℕ :=
  ((T.groups.filter fun g => decide (t < (2 : ℝ) ^ (-(g.1 : ℤ)))).argmax fun g => g.1).getD (T.groups.headD (0, 2, 2))

/-- SINR's series length `K_s` by `|r_0|` -/
noncomputable def Ks (t : ℝ) : ℕ := (T.G t).2.1

/-- COSR's series length `K_c` by `|r_0|` -/
noncomputable def Kc (t : ℝ) : ℕ := (T.G t).2.2

/-- SINR's coefficients -/
noncomputable def FsR (k i : ℕ) : ℝ := ((T.FsQ k i : ℚ) : ℝ)

/-- COSR's coefficients -/
noncomputable def FcR (k i : ℕ) : ℝ := ((T.FcQ k i : ℚ) : ℝ)

theorem G_spec (hhead : ∃ a b, T.groups.head? = some (0, a, b)) (t : ℝ) :
    T.G t ∈ T.groups ∧ ((T.G t).1 ≠ 0 → t < (2 : ℝ) ^ (-((T.G t).1 : ℤ))) := by
  obtain ⟨a, b, hh⟩ := hhead
  have hd : T.groups.headD (0, 2, 2) = (0, a, b) := by
    rw [List.headD_eq_head?_getD, hh]
    rfl
  have hmem : (0, a, b) ∈ T.groups := List.mem_of_mem_head? hh
  unfold G
  generalize hl : (T.groups.filter fun g => decide (t < (2 : ℝ) ^ (-(g.1 : ℤ)))).argmax (fun g => g.1) = o
  rcases o with _ | g
  · rw [hd]
    exact ⟨hmem, fun h => (h rfl).elim⟩
  · obtain ⟨h1, h2⟩ := List.mem_filter.mp (List.argmax_mem hl)
    exact ⟨h1, fun _ => of_decide_eq_true h2⟩

/-- `G` takes the run that contains the bucket of `t`: no run whose first bucket `j` has `t < 2^{-j}` starts after
it, whatever the order of `T.groups` -/
theorem G_max (t : ℝ) {g : ℕ × ℕ × ℕ} (hg : g ∈ T.groups) (ht : t < (2 : ℝ) ^ (-(g.1 : ℤ))) :
    g.1 ≤ (T.G t).1 := by
  have hgf : g ∈ T.groups.filter fun g => decide (t < (2 : ℝ) ^ (-(g.1 : ℤ))) :=
    List.mem_filter.mpr ⟨hg, decide_eq_true ht⟩
  unfold G
  generalize hl : (T.groups.filter fun g => decide (t < (2 : ℝ) ^ (-(g.1 : ℤ)))).argmax (fun g => g.1) = o
  rcases o with _ | m
  · rw [List.argmax_eq_none] at hl
    rw [hl] at hgf
    simp at hgf
  · have h := List.le_of_mem_argmax hgf hl
    exact h

end TrigTab

/-- a table's rows have at most `n` parts, so its coefficients vanish past them -/
theorem dyFn_getD_zero_of (T : List (List (ℤ × ℕ))) {n : ℕ} (hT : ∀ t ∈ T, t.length ≤ n) (k : ℕ) {i : ℕ}
    (hi : n ≤ i) : dyFn (T.getD k []) i = 0 := by
  apply dyFn_of_le
  by_cases hk : k < T.length
  · have hm : T.getD k [] ∈ T := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      exact List.getElem_mem hk
    exact (hT _ hm).trans hi
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    exact Nat.zero_le i

variable (p : ℤ) [Prec_gt_0 p]

/-- Theorem 35 (`thm:trig`) for SIN and COS at `p = 53`, for a table of `n` parts and a bound `c u^n` that the kernel
checked on it: for `x` in `F`, on `H(2)` and with `|x_0| ≤ 2^52`, the sine and the cosine are within `c u^n` of
`sin x` and `cos x`, relatively, plus `5E_π` -/
theorem thm35_sincos_tab (T : TrigTab) (c : ℚ) (hn2 : 2 ≤ T.n) (hn38 : T.n ≤ 38)
    (hhead : ∃ a b, T.groups.head? = some (0, a, b)) (htab : T.TabOk) (htiny : T.TinyOk c)
    (hall : ∀ g ∈ T.groups, T.Group c g) (hp : p = 53) (x : ℕ → ℝ) (hx : ∀ i < T.n, F p (x i))
    (hH : Htheta p T.n 2 x) (hx0 : |x 0| ≤ 2 ^ 52) (es : ℝ → ℤ) :
    |∑ i ∈ range T.n, sinN p T.n es T.Ks T.Kc T.FsR T.FcR x i - Real.sin (∑ i ∈ range T.n, x i)| ≤
        (c : ℝ) * u p ^ T.n * |Real.sin (∑ i ∈ range T.n, x i)| +
          5 * (|(redK p T.n x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) ∧
      |∑ i ∈ range T.n, cosN p T.n es T.Ks T.Kc T.FsR T.FcR x i - Real.cos (∑ i ∈ range T.n, x i)| ≤
        (c : ℝ) * u p ^ T.n * |Real.cos (∑ i ∈ range T.n, x i)| +
          5 * (|(redK p T.n x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) := by
  subst hp
  obtain ⟨n, fs, fc, groups⟩ := T
  simp only at hn2 hn38 hhead hx hH ⊢
  set T : TrigTab := ⟨n, fs, fc, groups⟩ with hTd
  have hn1 : 1 ≤ n := by omega
  have htu : ((trig8U : ℚ) : ℝ) = u (53 : ℤ) := by
    unfold trig8U
    exact u_53_rat 53 rfl
  have hu : u (53 : ℤ) = 1 / 9007199254740992 := by
    rw [← htu]
    unfold trig8U
    norm_num
  have hA3 : ((n : ℝ) ^ 2 + n) * u (53 : ℤ) < 1 := by
    have h38 : (n : ℝ) ≤ 38 := by exact_mod_cast hn38
    have h0 : (0 : ℝ) ≤ n := by positivity
    rw [hu]
    nlinarith
  have hEπ : 0 ≤ 5 * (|(redK 53 n x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) := by positivity
  obtain ⟨hl1, hl2, hr1, hr2, hK⟩ := htab
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := htiny
  have hFs : ∀ k, ∀ i < n, F 53 (T.FsR k i) := fun k i _ => dyFn_getD_F 53 fs (dyF_of_all 53 fs hr1) k i
  have hFc : ∀ k, ∀ i < n, F 53 (T.FcR k i) := fun k i _ => dyFn_getD_F 53 fc (dyF_of_all 53 fc hr2) k i
  have hT : ((T.tiny : ℚ) : ℝ) = u (53 : ℤ) ^ (n / 2) * (1 + 1 / 2 ^ 50) := by
    unfold TrigTab.tiny
    push_cast
    rw [htu]
  have hT0 : (0 : ℝ) ≤ ((T.tiny : ℚ) : ℝ) := by
    rw [hT, hu]
    positivity
  have hcT : (0 : ℝ) < cosLo ((T.tiny : ℚ) : ℝ) := by
    rw [← cast_cosLo]
    exact_mod_cast t3
  have c7 : ((T.tiny : ℚ) : ℝ) ^ 2 / (6 - ((T.tiny : ℚ) : ℝ) ^ 2) ≤ (c : ℝ) * u (53 : ℤ) ^ n := by
    have := (Rat.cast_le (K := ℝ)).mpr t7
    push_cast at this
    rwa [htu] at this
  have c8 : ((T.tiny : ℚ) : ℝ) ^ 2 / (2 * cosLo ((T.tiny : ℚ) : ℝ)) ≤ (c : ℝ) * u (53 : ℤ) ^ n := by
    have := (Rat.cast_le (K := ℝ)).mpr t8
    push_cast at this
    rwa [htu, cast_cosLo] at this
  by_cases hsmall : |x 0| < u (53 : ℤ) ^ (n / 2)
  · -- the early return
    obtain ⟨-, hs, hc⟩ := thm35_small 53 n rfl hn2 x hH hsmall es T.Ks T.Kc T.FsR T.FcR
    rw [← hT] at hs hc
    have hcoef : 0 ≤ ((T.tiny : ℚ) : ℝ) ^ 2 / (2 * cosLo ((T.tiny : ℚ) : ℝ)) :=
      div_nonneg (sq_nonneg _) (by linarith)
    exact ⟨hs.trans (le_add_of_le_of_nonneg (mul_le_mul_of_nonneg_right c7 (abs_nonneg _)) hEπ),
      hc.trans ((mul_le_mul_of_nonneg_left (le_abs_self _) hcoef).trans
        (le_add_of_le_of_nonneg (mul_le_mul_of_nonneg_right c8 (abs_nonneg _)) hEπ))⟩
  obtain ⟨hmem, hlt⟩ := T.G_spec hhead |redR 53 n x 0|
  obtain ⟨hKs, hKc⟩ := hK _ hmem
  -- the bound on `C` gives the theorem
  have fin : ∀ rb : ℝ, rb ≤ 8 / 10 → |∑ i ∈ range n, redR 53 n x i| ≤ rb →
      |∑ i ∈ range n, x i - redK 53 n x * (Real.pi / 2)| ≤ rb →
      0 ≤ trigDS 53 n (redR 53 n x 0) rb T.FsR (T.Ks |redR 53 n x 0|) →
      trigDS 53 n (redR 53 n x 0) rb T.FsR (T.Ks |redR 53 n x 0|) ≤ 1 / 2 →
      0 ≤ trigDC 53 n (redR 53 n x 0) rb T.FcR (T.Kc |redR 53 n x 0|) →
      trigDC 53 n (redR 53 n x 0) rb T.FcR (T.Kc |redR 53 n x 0|) ≤ 1 / 2 →
      trigC 53 n (trigDS 53 n (redR 53 n x 0) rb T.FsR (T.Ks |redR 53 n x 0|))
        (trigDC 53 n (redR 53 n x 0) rb T.FcR (T.Kc |redR 53 n x 0|)) rb ≤ (c : ℝ) * u (53 : ℤ) ^ n →
      |∑ i ∈ range n, sinN 53 n es T.Ks T.Kc T.FsR T.FcR x i - Real.sin (∑ i ∈ range n, x i)| ≤
          (c : ℝ) * u (53 : ℤ) ^ n * |Real.sin (∑ i ∈ range n, x i)| +
            5 * (|(redK 53 n x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) ∧
        |∑ i ∈ range n, cosN 53 n es T.Ks T.Kc T.FsR T.FcR x i - Real.cos (∑ i ∈ range n, x i)| ≤
          (c : ℝ) * u (53 : ℤ) ^ n * |Real.cos (∑ i ∈ range n, x i)| +
            5 * (|(redK 53 n x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) := by
    intro rb hrb hr hre a1 a2 a3 a4 hC
    obtain ⟨ks, kc⟩ := thm35_sincos 53 n rfl hn1 hA3 x hx hH hx0 hsmall es T.Ks T.Kc T.FsR T.FcR hFs hFc hKs hKc rb
      hrb hr hre a1 a2 a3 a4
    exact ⟨ks.trans (add_le_add (mul_le_mul_of_nonneg_right hC (abs_nonneg _)) le_rfl),
      kc.trans (add_le_add (mul_le_mul_of_nonneg_right hC (abs_nonneg _)) le_rfl)⟩
  by_cases htiny : |redR 53 n x 0| < u (53 : ℤ) ^ (n / 2)
  · -- `|r_0|` below the last bucket: SINR returns `r` and COSR `1`
    have hpow : u (53 : ℤ) ^ (n / 2) = (2 : ℝ) ^ (-(53 * ((n / 2 : ℕ) : ℤ))) := by
      unfold u
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
    obtain ⟨hr, hre⟩ := lemma32_bucket 53 n rfl hn1 hn38 x hx hH hx0 (-(53 * ((n / 2 : ℕ) : ℤ))) hpow.le
      (by rw [← hpow]; exact htiny)
    rw [← hpow, ← hT] at hr hre
    have eS : trigDS 53 n (redR 53 n x 0) ((T.tiny : ℚ) : ℝ) T.FsR (T.Ks |redR 53 n x 0|) =
        ((T.tiny ^ 2 / (6 - T.tiny ^ 2) : ℚ) : ℝ) := by
      simp only [trigDS, htiny, ↓reduceIte]
      push_cast
      rfl
    have eC : trigDC 53 n (redR 53 n x 0) ((T.tiny : ℚ) : ℝ) T.FcR (T.Kc |redR 53 n x 0|) =
        ((T.tiny ^ 2 / (2 * cosLoQ T.tiny) : ℚ) : ℝ) := by
      simp only [trigDC, htiny, ↓reduceIte]
      push_cast
      rw [cast_cosLo]
    have h6 : (0 : ℚ) ≤ T.tiny ^ 2 / (6 - T.tiny ^ 2) := div_nonneg (sq_nonneg _) (by linarith)
    have h7 : (0 : ℚ) ≤ T.tiny ^ 2 / (2 * cosLoQ T.tiny) := div_nonneg (sq_nonneg _) (by linarith)
    refine fin _ (((Rat.cast_le (K := ℝ)).mpr t1).trans_eq (by norm_num)) hr hre ?_ ?_ ?_ ?_ ?_
    · rw [eS]; exact_mod_cast h6
    · rw [eS]; exact ((Rat.cast_le (K := ℝ)).mpr t4).trans_eq (by norm_num)
    · rw [eC]; exact_mod_cast h7
    · rw [eC]; exact ((Rat.cast_le (K := ℝ)).mpr t5).trans_eq (by norm_num)
    · rw [eS, eC]
      refine (trigC_le 53 n htu T.tiny le_rfl le_rfl).trans ?_
      have := (Rat.cast_le (K := ℝ)).mpr t6
      push_cast at this
      rwa [htu] at this
  -- a bucket: Lemma 34's bounds, evaluated by the kernel
  obtain ⟨sS, sC, hS, hC, ok1, ok2, ok3, ok4, ok5⟩ := hall _ hmem
  have eKs : T.Ks |redR 53 n x 0| = (T.G |redR 53 n x 0|).2.1 := rfl
  have eKc : T.Kc |redR 53 n x 0| = (T.G |redR 53 n x 0|).2.2 := rfl
  generalize T.G |redR 53 n x 0| = g at *
  have hrb0 := trig8Rb_nonneg g.1
  have hrb6 : trig8Rb g.1 ^ 2 < 6 := by nlinarith
  have hrb0' : (0 : ℝ) ≤ ((trig8Rb g.1 : ℚ) : ℝ) := by exact_mod_cast hrb0
  have hr : |∑ i ∈ range n, redR 53 n x i| ≤ ((trig8Rb g.1 : ℚ) : ℝ) ∧
      |∑ i ∈ range n, x i - redK 53 n x * (Real.pi / 2)| ≤ ((trig8Rb g.1 : ℚ) : ℝ) := by
    by_cases hj : g.1 = 0
    · have e : ((trig8Rb g.1 : ℚ) : ℝ) = 78541 / 100000 := by
        simp only [trig8Rb, hj, ↓reduceIte]
        norm_num
      obtain ⟨-, -, h3, -, -⟩ := lemma32_r 53 n rfl hn1 x hx hH hx0
      rw [e]
      exact ⟨h3, lemma32_re 53 n rfl hn1 x hH hx0⟩
    · have hlt' := hlt hj
      have e : ((trig8Rb g.1 : ℚ) : ℝ) = (2 : ℝ) ^ (-(g.1 : ℤ)) * (1 + 1 / 2 ^ 50) := by
        simp only [trig8Rb, hj, ↓reduceIte]
        push_cast
        rw [zpow_neg, zpow_natCast, one_div]
      rw [e]
      exact lemma32_bucket 53 n rfl hn1 hn38 x hx hH hx0 (-(g.1 : ℤ)) ((not_lt.mp htiny).trans hlt'.le) hlt'
  have hab : (fun i => ((trig8Ab i : ℚ) : ℝ)) = abar (2 * u (53 : ℤ)) := by
    funext i
    unfold trig8Ab
    rw [cast_abar]
    push_cast
    rw [htu]
  have hstS := scHU_ge 53 n htu (le_upQ 200) hn1 hA3 trig8Ab_nonneg (trig8Rb g.1) sinCQ sinC cast_sinC
    T.FsQ (fun k i hi => dyFn_getD_zero_of fs hl1 k hi) g.2.1
  have hstC := scHU_ge 53 n htu (le_upQ 200) hn1 hA3 trig8Ab_nonneg (trig8Rb g.1) cosCQ cosC cast_cosC
    T.FcQ (fun k i hi => dyFn_getD_zero_of fc hl2 k hi) g.2.2
  have eS : scHU trig8U n (upQ 200) trig8Ab (trig8Rb g.1) sinCQ T.FsQ g.2.1 = sS := hS
  have eC : scHU trig8U n (upQ 200) trig8Ab (trig8Rb g.1) cosCQ T.FcQ g.2.2 = sC := hC
  rw [eS] at hstS
  rw [eC] at hstC
  obtain ⟨dS0, dS1, -⟩ := sinTail_le 53 n htu (le_upQ 200) hA3 trig8Ab_nonneg hrb0 hrb6 T.FsQ g.2.1 hstS
  obtain ⟨dC0, dC1, -⟩ := cosTail_le 53 n htu (le_upQ 200) hA3 trig8Ab_nonneg hrb0 ok5 T.FcQ g.2.2 hstC
  have eDS : trigDS 53 n (redR 53 n x 0) ((trig8Rb g.1 : ℚ) : ℝ) T.FsR (T.Ks |redR 53 n x 0|) =
      sinDelta 53 n (fun i => ((trig8Ab i : ℚ) : ℝ)) ((trig8Rb g.1 : ℚ) : ℝ)
        (fun k i => ((T.FsQ k i : ℚ) : ℝ)) g.2.1 := by
    simp only [trigDS, htiny, ↓reduceIte]
    rw [hab, eKs]
    rfl
  have eDC : trigDC 53 n (redR 53 n x 0) ((trig8Rb g.1 : ℚ) : ℝ) T.FcR (T.Kc |redR 53 n x 0|) =
      cosDelta 53 n (fun i => ((trig8Ab i : ℚ) : ℝ)) ((trig8Rb g.1 : ℚ) : ℝ)
        (fun k i => ((T.FcQ k i : ℚ) : ℝ)) g.2.2 := by
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
    exact (trigC_le 53 n htu (trig8Rb g.1) dS1 dC1).trans o3

/-- Theorem 35 (`thm:trig`) for TAN at `p = 53`, for a table of `n` parts and a bound `c u^n` that the kernel checked
on it: for `x` in `F`, on `H(2)`, with `|x_0| ≤ 2^52` and, where RED's `k` is not zero, `|x - kπ/2| ≥ 2^{np-1074}`,
the tangent is within `c u^n + 5E_π/|sin x cos x|` of `tan x`, relatively -/
theorem thm35_tan_tab (T : TrigTab) (c kd0 kd3 : ℚ) (hn2 : 2 ≤ T.n) (hn38 : T.n ≤ 38)
    (hhead : ∃ a b, T.groups.head? = some (0, a, b)) (htab : T.TabOk) (hkd : T.KdivOk kd0 kd3)
    (htiny : T.TanTinyOk c kd3) (hall : ∀ g ∈ T.groups, T.TanGroup c kd0 kd3 g) (hp : p = 53) (x : ℕ → ℝ)
    (hx : ∀ i < T.n, F p (x i)) (hH : Htheta p T.n 2 x) (hx0 : |x 0| ≤ 2 ^ 52) (es et : ℝ → ℤ)
    (hfar : redK p T.n x ≠ 0 →
      (2 : ℝ) ^ (p * (T.n : ℕ) - 1074) ≤ |∑ i ∈ range T.n, x i - redK p T.n x * (Real.pi / 2)|) :
    |∑ i ∈ range T.n, tanN p T.n es et T.Ks T.Kc T.FsR T.FcR x i - Real.tan (∑ i ∈ range T.n, x i)| ≤
      ((c : ℝ) * u p ^ T.n + 5 * (|(redK p T.n x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) /
        |Real.sin (∑ i ∈ range T.n, x i) * Real.cos (∑ i ∈ range T.n, x i)|) *
          |Real.tan (∑ i ∈ range T.n, x i)| := by
  subst hp
  obtain ⟨n, fs, fc, groups⟩ := T
  simp only at hn2 hn38 hhead hx hH hfar ⊢
  set T : TrigTab := ⟨n, fs, fc, groups⟩ with hTd
  have hn1 : 1 ≤ n := by omega
  have htu : ((trig8U : ℚ) : ℝ) = u (53 : ℤ) := by
    unfold trig8U
    exact u_53_rat 53 rfl
  have hu : u (53 : ℤ) = 1 / 9007199254740992 := by
    rw [← htu]
    unfold trig8U
    norm_num
  have hA3 : ((n : ℝ) ^ 2 + n) * u (53 : ℤ) < 1 := by
    have h38 : (n : ℝ) ≤ 38 := by exact_mod_cast hn38
    have h0 : (0 : ℝ) ≤ n := by positivity
    rw [hu]
    nlinarith
  have hE : 0 ≤ 5 * (|(redK 53 n x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) /
      |Real.sin (∑ i ∈ range n, x i) * Real.cos (∑ i ∈ range n, x i)| := by positivity
  obtain ⟨hl1, hl2, hr1, hr2, hK⟩ := htab
  obtain ⟨t1, t2, t3, tchk, tsmall⟩ := htiny
  have hun : (0 : ℚ) ≤ trig8U ^ (n + 1) := by unfold trig8U; positivity
  obtain ⟨⟨kd0a, kd0b⟩, ⟨kd3a, kd3b⟩, kd10, kd03⟩ := hkd
  have hFs : ∀ k, ∀ i < n, F 53 (T.FsR k i) := fun k i _ => dyFn_getD_F 53 fs (dyF_of_all 53 fs hr1) k i
  have hFc : ∀ k, ∀ i < n, F 53 (T.FcR k i) := fun k i _ => dyFn_getD_F 53 fc (dyF_of_all 53 fc hr2) k i
  have hT : ((T.tiny : ℚ) : ℝ) = u (53 : ℤ) ^ (n / 2) * (1 + 1 / 2 ^ 50) := by
    unfold TrigTab.tiny
    push_cast
    rw [htu]
  by_cases hsmall : |x 0| < u (53 : ℤ) ^ (n / 2)
  · -- the early return
    have hs := thm35_tan_small 53 n rfl hn2 x hH hsmall es et T.Ks T.Kc T.FsR T.FcR
    rw [← hT] at hs
    have ce : tanHi ((T.tiny : ℚ) : ℝ) / ((T.tiny : ℚ) : ℝ) - 1 ≤ (c : ℝ) * u (53 : ℤ) ^ n := by
      have := (Rat.cast_le (K := ℝ)).mpr tsmall
      push_cast at this
      rwa [htu, cast_tanHi] at this
    exact hs.trans (mul_le_mul_of_nonneg_right (le_add_of_le_of_nonneg ce hE) (abs_nonneg _))
  obtain ⟨hmem, hlt⟩ := T.G_spec hhead |redR 53 n x 0|
  obtain ⟨hKs, hKc⟩ := hK _ hmem
  -- `TanChk` on bounds of `δ_S`, `δ_C`, `ψ_s` and `ψ_c` gives the theorem
  have fin : ∀ (rb dSq dCq : ℚ) (ψsq ψcq : ℕ → ℚ) (θ Kd : ℚ), 0 ≤ rb →
      |∑ i ∈ range n, redR 53 n x i| ≤ ((rb : ℚ) : ℝ) →
      |∑ i ∈ range n, x i - redK 53 n x * (Real.pi / 2)| ≤ ((rb : ℚ) : ℝ) →
      0 ≤ trigDS 53 n (redR 53 n x 0) ((rb : ℚ) : ℝ) T.FsR (T.Ks |redR 53 n x 0|) →
      trigDS 53 n (redR 53 n x 0) ((rb : ℚ) : ℝ) T.FsR (T.Ks |redR 53 n x 0|) ≤ ((dSq : ℚ) : ℝ) →
      0 ≤ trigDC 53 n (redR 53 n x 0) ((rb : ℚ) : ℝ) T.FcR (T.Kc |redR 53 n x 0|) →
      trigDC 53 n (redR 53 n x 0) ((rb : ℚ) : ℝ) T.FcR (T.Kc |redR 53 n x 0|) ≤ ((dCq : ℚ) : ℝ) →
      (∀ i, tanPs 53 n (redR 53 n x 0) ((rb : ℚ) : ℝ) T.FsR (T.Ks |redR 53 n x 0|) i ≤ ((ψsq i : ℚ) : ℝ)) →
      (∀ i, tanPc 53 n (redR 53 n x 0) ((rb : ℚ) : ℝ) T.FcR (T.Kc |redR 53 n x 0|) i ≤ ((ψcq i : ℚ) : ℝ)) →
      0 ≤ θ → θ ≤ 3 → 0 ≤ kdivQ trig8U n (θ * trig8U) → kdivQ trig8U n (θ * trig8U) ≤ Kd → Kd ≤ kd3 →
      T.TanChk c rb dSq dCq ψsq ψcq θ Kd →
      |∑ i ∈ range n, tanN 53 n es et T.Ks T.Kc T.FsR T.FcR x i - Real.tan (∑ i ∈ range n, x i)| ≤
        ((c : ℝ) * u (53 : ℤ) ^ n + 5 * (|(redK 53 n x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) /
          |Real.sin (∑ i ∈ range n, x i) * Real.cos (∑ i ∈ range n, x i)|) *
            |Real.tan (∑ i ∈ range n, x i)| := by
    intro rb dSq dCq ψsq ψcq θ Kd hrb0 hr hre a1 a2 c1 c2 hps hpc hθ0 hθ3 hk0 hk1 hKd
      ⟨k1, k2, k3, k4, k5, k6, k7, k8, kc⟩
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
    have ek : kdiv 53 n (((θ : ℚ) : ℝ) * u (53 : ℤ)) = ((kdivQ trig8U n (θ * trig8U) : ℚ) : ℝ) :=
      kdiv_53 53 rfl n θ
    have hD0 : 0 ≤ u (53 : ℤ) ^ n + kdiv 53 n (((θ : ℚ) : ℝ) * u (53 : ℤ)) * u (53 : ℤ) ^ (n + 1) := by
      rw [ek]
      exact add_nonneg (pow_nonneg (u_pos 53).le _)
        (mul_nonneg ((Rat.cast_nonneg (K := ℝ)).mpr hk0) (pow_nonneg (u_pos 53).le _))
    have hD : u (53 : ℤ) ^ n + kdiv 53 n (((θ : ℚ) : ℝ) * u (53 : ℤ)) * u (53 : ℤ) ^ (n + 1) ≤
        ((trig8U ^ n + Kd * trig8U ^ (n + 1) : ℚ) : ℝ) := by
      rw [ek]
      push_cast
      rw [htu]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right ((Rat.cast_le (K := ℝ)).mpr hk1)
        (pow_nonneg (u_pos 53).le _))
    have hD10 : ((trig8U ^ n + Kd * trig8U ^ (n + 1) : ℚ) : ℝ) ≤ 1 / 10 := by
      have h1 : trig8U ^ n + Kd * trig8U ^ (n + 1) ≤ trig8U ^ n + kd3 * trig8U ^ (n + 1) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hKd hun)
      exact ((Rat.cast_le (K := ℝ)).mpr (h1.trans kd10)).trans_eq (by norm_num)
    -- the ladders of the computed sine and cosine
    have o3 := (Rat.cast_le (K := ℝ)).mpr k3
    have o4 := (Rat.cast_le (K := ℝ)).mpr k4
    have o5 := (Rat.cast_lt (K := ℝ)).mpr k5
    have o7 := (Rat.cast_lt (K := ℝ)).mpr k7
    have o9 := (Rat.cast_le (K := ℝ)).mpr kc
    push_cast at o3 o4 o5 o7 o9
    rw [cast_cosLo] at o7
    rw [htu] at o9
    have sS : ∑ i ∈ Ico 1 n, tanPs 53 n (redR 53 n x 0) ((rb : ℚ) : ℝ) T.FsR (T.Ks |redR 53 n x 0|) i ≤
        ∑ i ∈ Ico 1 n, ((ψsq i : ℚ) : ℝ) := sum_le_sum fun i _ => hps i
    have sC : ∑ i ∈ Ico 1 n, tanPc 53 n (redR 53 n x 0) ((rb : ℚ) : ℝ) T.FcR (T.Kc |redR 53 n x 0|) i ≤
        ∑ i ∈ Ico 1 n, ((ψcq i : ℚ) : ℝ) := sum_le_sum fun i _ => hpc i
    have lS : (1 - ((rb : ℚ) : ℝ) ^ 2 / 6) * (1 - ((dSq : ℚ) : ℝ)) - ∑ i ∈ Ico 1 n, ((ψsq i : ℚ) : ℝ) ≤
        (1 - ((rb : ℚ) : ℝ) ^ 2 / 6) *
            (1 - trigDS 53 n (redR 53 n x 0) ((rb : ℚ) : ℝ) T.FsR (T.Ks |redR 53 n x 0|)) -
          ∑ i ∈ Ico 1 n, tanPs 53 n (redR 53 n x 0) ((rb : ℚ) : ℝ) T.FsR (T.Ks |redR 53 n x 0|) i := by
      have := mul_le_mul_of_nonneg_left (sub_le_sub_left a2 1) h6
      linarith
    have lC : cosLo ((rb : ℚ) : ℝ) * (1 - ((dCq : ℚ) : ℝ)) - ∑ i ∈ Ico 1 n, ((ψcq i : ℚ) : ℝ) ≤
        cosLo ((rb : ℚ) : ℝ) *
            (1 - trigDC 53 n (redR 53 n x 0) ((rb : ℚ) : ℝ) T.FcR (T.Kc |redR 53 n x 0|)) -
          ∑ i ∈ Ico 1 n, tanPc 53 n (redR 53 n x 0) ((rb : ℚ) : ℝ) T.FcR (T.Kc |redR 53 n x 0|) i := by
      have := mul_le_mul_of_nonneg_left (sub_le_sub_left c2 1) hc.le
      linarith
    have key := thm35_tan 53 n rfl hn1 hA3 x hx hH hx0 hsmall es et T.Ks T.Kc T.FsR T.FcR
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
    have hCT := (tanCT_le 53 n htu rb a1 a2 (lt_of_le_of_lt k3 (by norm_num)) c1 c2
      (lt_of_le_of_lt k4 (by norm_num)) hD0 hD).trans o9
    exact key.trans (mul_le_mul_of_nonneg_right (add_le_add hCT le_rfl) (abs_nonneg _))
  by_cases htiny : |redR 53 n x 0| < u (53 : ℤ) ^ (n / 2)
  · -- `|r_0|` below the last bucket: SINR returns `r` and COSR `1`
    have hpow : u (53 : ℤ) ^ (n / 2) = (2 : ℝ) ^ (-(53 * ((n / 2 : ℕ) : ℤ))) := by
      unfold u
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
    obtain ⟨hr, hre⟩ := lemma32_bucket 53 n rfl hn1 hn38 x hx hH hx0 (-(53 * ((n / 2 : ℕ) : ℤ))) hpow.le
      (by rw [← hpow]; exact htiny)
    rw [← hpow, ← hT] at hr hre
    have hT0 : (0 : ℚ) ≤ T.tiny := by
      unfold TrigTab.tiny trig8U
      positivity
    have eS : trigDS 53 n (redR 53 n x 0) ((T.tiny : ℚ) : ℝ) T.FsR (T.Ks |redR 53 n x 0|) =
        ((T.tiny ^ 2 / (6 - T.tiny ^ 2) : ℚ) : ℝ) := by
      simp only [trigDS, htiny, ↓reduceIte]
      push_cast
      rfl
    have eC : trigDC 53 n (redR 53 n x 0) ((T.tiny : ℚ) : ℝ) T.FcR (T.Kc |redR 53 n x 0|) =
        ((T.tiny ^ 2 / (2 * cosLoQ T.tiny) : ℚ) : ℝ) := by
      simp only [trigDC, htiny, ↓reduceIte]
      push_cast
      rw [cast_cosLo]
    have h6 : (0 : ℚ) ≤ T.tiny ^ 2 / (6 - T.tiny ^ 2) := div_nonneg (sq_nonneg _) (by linarith)
    have h7 : (0 : ℚ) ≤ T.tiny ^ 2 / (2 * cosLoQ T.tiny) := div_nonneg (sq_nonneg _) (by linarith)
    have hab : ∀ i, abar (2 * u (53 : ℤ)) i = ((trig8Ab i : ℚ) : ℝ) := fun i => by
      unfold trig8Ab
      rw [cast_abar]
      push_cast
      rw [htu]
    refine fin T.tiny _ _ _ _ 3 kd3 hT0 hr hre (by rw [eS]; exact_mod_cast h6) (by rw [eS])
      (by rw [eC]; exact_mod_cast h7) (by rw [eC]) (fun i => ?_) (fun i => ?_) (by norm_num) le_rfl kd3a kd3b
      le_rfl tchk
    · simp only [tanPs, htiny, ↓reduceIte]
      split_ifs
      · exact (hab i).le
      · simp
    · simp only [tanPc, htiny, ↓reduceIte]
      split_ifs <;> simp
  -- a bucket: Lemma 34's bounds and the ladders, evaluated by the kernel
  obtain ⟨sS, sC, hS, hC, tok⟩ := hall _ hmem
  have eKs : T.Ks |redR 53 n x 0| = (T.G |redR 53 n x 0|).2.1 := rfl
  have eKc : T.Kc |redR 53 n x 0| = (T.G |redR 53 n x 0|).2.2 := rfl
  generalize T.G |redR 53 n x 0| = g at *
  have hrb0 := trig8Rb_nonneg g.1
  have hrb8 : trig8Rb g.1 ≤ 8 / 10 := tok.1
  have hcos : 0 < cosLoQ (trig8Rb g.1) := tok.2.1
  have hrb6 : trig8Rb g.1 ^ 2 < 6 := by nlinarith
  have hr : |∑ i ∈ range n, redR 53 n x i| ≤ ((trig8Rb g.1 : ℚ) : ℝ) ∧
      |∑ i ∈ range n, x i - redK 53 n x * (Real.pi / 2)| ≤ ((trig8Rb g.1 : ℚ) : ℝ) := by
    by_cases hj : g.1 = 0
    · have e : ((trig8Rb g.1 : ℚ) : ℝ) = 78541 / 100000 := by
        simp only [trig8Rb, hj, ↓reduceIte]
        norm_num
      obtain ⟨-, -, h3, -, -⟩ := lemma32_r 53 n rfl hn1 x hx hH hx0
      rw [e]
      exact ⟨h3, lemma32_re 53 n rfl hn1 x hH hx0⟩
    · have hlt' := hlt hj
      have e : ((trig8Rb g.1 : ℚ) : ℝ) = (2 : ℝ) ^ (-(g.1 : ℤ)) * (1 + 1 / 2 ^ 50) := by
        simp only [trig8Rb, hj, ↓reduceIte]
        push_cast
        rw [zpow_neg, zpow_natCast, one_div]
      rw [e]
      exact lemma32_bucket 53 n rfl hn1 hn38 x hx hH hx0 (-(g.1 : ℤ)) ((not_lt.mp htiny).trans hlt'.le) hlt'
  have hab : (fun i => ((trig8Ab i : ℚ) : ℝ)) = abar (2 * u (53 : ℤ)) := by
    funext i
    unfold trig8Ab
    rw [cast_abar]
    push_cast
    rw [htu]
  have hstS := scHU_ge 53 n htu (le_upQ 200) hn1 hA3 trig8Ab_nonneg (trig8Rb g.1) sinCQ sinC cast_sinC
    T.FsQ (fun k i hi => dyFn_getD_zero_of fs hl1 k hi) g.2.1
  have hstC := scHU_ge 53 n htu (le_upQ 200) hn1 hA3 trig8Ab_nonneg (trig8Rb g.1) cosCQ cosC cast_cosC
    T.FcQ (fun k i hi => dyFn_getD_zero_of fc hl2 k hi) g.2.2
  have eS : scHU trig8U n (upQ 200) trig8Ab (trig8Rb g.1) sinCQ T.FsQ g.2.1 = sS := hS
  have eC : scHU trig8U n (upQ 200) trig8Ab (trig8Rb g.1) cosCQ T.FcQ g.2.2 = sC := hC
  rw [eS] at hstS
  rw [eC] at hstC
  obtain ⟨dS0, dS1, pS⟩ := sinTail_le 53 n htu (le_upQ 200) hA3 trig8Ab_nonneg hrb0 hrb6 T.FsQ g.2.1 hstS
  obtain ⟨dC0, dC1, pC⟩ := cosTail_le 53 n htu (le_upQ 200) hA3 trig8Ab_nonneg hrb0 hcos T.FcQ g.2.2 hstC
  have eDS : trigDS 53 n (redR 53 n x 0) ((trig8Rb g.1 : ℚ) : ℝ) T.FsR (T.Ks |redR 53 n x 0|) =
      sinDelta 53 n (fun i => ((trig8Ab i : ℚ) : ℝ)) ((trig8Rb g.1 : ℚ) : ℝ)
        (fun k i => ((T.FsQ k i : ℚ) : ℝ)) g.2.1 := by
    simp only [trigDS, htiny, ↓reduceIte]
    rw [hab, eKs]
    rfl
  have eDC : trigDC 53 n (redR 53 n x 0) ((trig8Rb g.1 : ℚ) : ℝ) T.FcR (T.Kc |redR 53 n x 0|) =
      cosDelta 53 n (fun i => ((trig8Ab i : ℚ) : ℝ)) ((trig8Rb g.1 : ℚ) : ℝ)
        (fun k i => ((T.FcQ k i : ℚ) : ℝ)) g.2.2 := by
    simp only [trigDC, htiny, ↓reduceIte]
    rw [hab, eKc]
    rfl
  have ePS : ∀ i, tanPs 53 n (redR 53 n x 0) ((trig8Rb g.1 : ℚ) : ℝ) T.FsR (T.Ks |redR 53 n x 0|) i =
      sinPsi 53 n (fun i => ((trig8Ab i : ℚ) : ℝ)) ((trig8Rb g.1 : ℚ) : ℝ)
        (fun k i => ((T.FsQ k i : ℚ) : ℝ)) g.2.1 i := fun i => by
    simp only [tanPs, htiny, ↓reduceIte]
    rw [hab, eKs]
    rfl
  have ePC : ∀ i, tanPc 53 n (redR 53 n x 0) ((trig8Rb g.1 : ℚ) : ℝ) T.FcR (T.Kc |redR 53 n x 0|) i =
      cosPsi 53 n (fun i => ((trig8Ab i : ℚ) : ℝ)) ((trig8Rb g.1 : ℚ) : ℝ)
        (fun k i => ((T.FcQ k i : ℚ) : ℝ)) g.2.2 i := fun i => by
    simp only [tanPc, htiny, ↓reduceIte]
    rw [hab, eKc]
    rfl
  have hk : 0 ≤ tan8Th g.1 ∧ tan8Th g.1 ≤ 3 ∧ 0 ≤ kdivQ trig8U n (tan8Th g.1 * trig8U) ∧
      kdivQ trig8U n (tan8Th g.1 * trig8U) ≤ TrigTab.tanKd kd0 kd3 g.1 ∧ TrigTab.tanKd kd0 kd3 g.1 ≤ kd3 := by
    by_cases hj : g.1 = 0
    · simp only [tan8Th, TrigTab.tanKd, hj, ↓reduceIte]
      exact ⟨by norm_num, by norm_num, kd0a, kd0b, kd03⟩
    · simp only [tan8Th, TrigTab.tanKd, hj, ↓reduceIte]
      exact ⟨by norm_num, le_rfl, kd3a, kd3b, le_rfl⟩
  obtain ⟨hk1, hk2, hk3, hk4, hk5⟩ := hk
  exact fin (trig8Rb g.1) _ _ _ _ (tan8Th g.1) (TrigTab.tanKd kd0 kd3 g.1) hrb0 hr.1 hr.2
    (by rw [eDS]; exact dS0) (by rw [eDS]; exact dS1) (by rw [eDC]; exact dC0) (by rw [eDC]; exact dC1)
    (fun i => by rw [ePS]; exact pS i) (fun i => by rw [ePC]; exact pC i) hk1 hk2 hk3 hk4 hk5 tok

end ExpansionBounds
