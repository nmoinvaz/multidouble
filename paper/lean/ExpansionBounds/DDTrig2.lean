import ExpansionBounds.DDTrigThm
import ExpansionBounds.Trig2

/-!
# Theorem 35 (`thm:trig`) for multidouble's double-double sine, cosine and tangent

Theorem 35's last claim: with the published double-word bounds of DWTimesDW3, AccurateDWPlusDW, DWPlusFP and DWDivDW2
in place of Lemma 13 and Theorem 19, `DD::sin`, `cos` and `tan` of a double word `x` with `|x_0| ≤ 2^52` are within

  `7.841412u²|sin x| + 5E_π`, `7.841412u²|cos x| + 5E_π` and `(28.414066u² + 5E_π/|sin x cos x|)|tan x|`

(`thm35_sincos_dd`, `thm35_tan_dd`), at `p = 53`, the tangent for `|x - kπ/2| ≥ 2^{2p-1074}` where `k ≠ 0`.

The coefficients are the two leading parts of the table of `Trig2/Data.lean`, each row a double word (`dd_rows_s`,
`dd_rows_c`), with the series lengths of the same table. The kernel evaluates `δ_S`, `δ_C`, `C` and `C^T` of
`DDTrig.lean` in exact rationals, in the first bucket of each run of buckets with the same series lengths and below
the last bucket (`dd_all`, `dd_tan_all`, `dd_tiny`, `dd_tan_tiny`): the bounds grow with `r̄`, so the first bucket of a
run bounds the others, as in `trig_consts.py`, whose values round these up.
-/

namespace ExpansionBounds

open Finset

/-- the bound of the double-double sine and cosine, in units of `u²` -/
def ddC : ℚ := 7841412 / 1000000

/-- the bound of the double-double tangent, in units of `u²` -/
def ddCt : ℚ := 28414066 / 1000000

/-- `φ_k = |ŝ_k - s_k|` for the two-part coefficient `ŝ_k` -/
def ddtPhiS (k : ℕ) : ℚ := |trig2Tab.FsQ k 0 + trig2Tab.FsQ k 1 - sinCQ k|

/-- `φ_k = |ĉ_k - c_k|` for the two-part coefficient `ĉ_k` -/
def ddtPhiC (k : ℕ) : ℚ := |trig2Tab.FcQ k 0 + trig2Tab.FcQ k 1 - cosCQ k|

/-- each row of a table is a double word: `RN(t_0 + t_1) = t_0` -/
def DDRows (T : List (List (ℤ × ℕ))) : Prop := ∀ t ∈ T, rnQ 53 (dyFn t 0 + dyFn t 1) = dyFn t 0

instance (T : List (List (ℤ × ℕ))) : Decidable (DDRows T) := by
  unfold DDRows
  infer_instance

/-- bucket `j` with series of `K_s` and `K_c` terms: `δ_S, δ_C ≤ 1/2`, `C ≤ c u²`, `r̄_j ≤ 0.8` and `cos₋ r̄_j > 0` -/
def DDOk (c : ℚ) (g : ℕ × ℕ × ℕ) : Prop :=
  ddtDS (trig8Rb g.1) ddtPhiS g.2.1 ≤ 1 / 2 ∧ ddtDC (trig8Rb g.1) ddtPhiC g.2.2 ≤ 1 / 2 ∧
    trigCQ trig8U 2 (ddtDS (trig8Rb g.1) ddtPhiS g.2.1) (ddtDC (trig8Rb g.1) ddtPhiC g.2.2) (trig8Rb g.1) ≤
      c * trig8U ^ 2 ∧ trig8Rb g.1 ≤ 8 / 10 ∧ 0 < cosLoQ (trig8Rb g.1)

instance (c : ℚ) (g : ℕ × ℕ × ℕ) : Decidable (DDOk c g) := by
  unfold DDOk
  infer_instance

/-- bucket `j` for the tangent: `δ_S, δ_C ≤ 1/10` and `C^T ≤ c u²` with `δ_D = 15u² + 56u³` -/
def DDTanOk (c : ℚ) (g : ℕ × ℕ × ℕ) : Prop :=
  ddtDS (trig8Rb g.1) ddtPhiS g.2.1 ≤ 1 / 10 ∧ ddtDC (trig8Rb g.1) ddtPhiC g.2.2 ≤ 1 / 10 ∧
    tanCTQ trig8U 2 (ddtDS (trig8Rb g.1) ddtPhiS g.2.1) (ddtDC (trig8Rb g.1) ddtPhiC g.2.2) ddtED (trig8Rb g.1) ≤
      c * trig8U ^ 2 ∧ trig8Rb g.1 ≤ 8 / 10 ∧ 0 < cosLoQ (trig8Rb g.1)

instance (c : ℚ) (g : ℕ × ℕ × ℕ) : Decidable (DDTanOk c g) := by
  unfold DDTanOk
  infer_instance

/-- `r̄_min = u(1 + 2^{-50})`, the bound of `|r|` and `|x|` below `|r_h| < u` and `|x_0| < u` -/
def ddTiny : ℚ := trig8U * (1 + 1 / 2 ^ 50)

/-- below the last bucket SINR returns `r` and COSR `1`, within `r̄²/(6 - r̄²)` and `r̄²/(2cos₋ r̄)`, which with `C`
there are at most `c u²` -/
def DDTinyOk (c : ℚ) : Prop :=
  ddTiny ≤ 8 / 10 ∧ ddTiny ^ 2 < 6 ∧ 0 < cosLoQ ddTiny ∧ ddTiny ^ 2 / (6 - ddTiny ^ 2) ≤ 1 / 2 ∧
    ddTiny ^ 2 / (2 * cosLoQ ddTiny) ≤ 1 / 2 ∧
    trigCQ trig8U 2 (ddTiny ^ 2 / (6 - ddTiny ^ 2)) (ddTiny ^ 2 / (2 * cosLoQ ddTiny)) ddTiny ≤ c * trig8U ^ 2 ∧
    ddTiny ^ 2 / (6 - ddTiny ^ 2) ≤ c * trig8U ^ 2 ∧ ddTiny ^ 2 / (2 * cosLoQ ddTiny) ≤ c * trig8U ^ 2

instance (c : ℚ) : Decidable (DDTinyOk c) := by
  unfold DDTinyOk
  infer_instance

/-- below the last bucket for the tangent: `δ_S, δ_C ≤ 1/10`, `C^T ≤ c u²`, and the early return within
`tan₊ r̄/r̄ - 1 ≤ c u²` -/
def DDTanTinyOk (c : ℚ) : Prop :=
  0 < ddTiny ∧ ddTiny ≤ 8 / 10 ∧ ddTiny ^ 2 < 6 ∧ 0 < cosLoQ ddTiny ∧ ddTiny ^ 2 / (6 - ddTiny ^ 2) ≤ 1 / 10 ∧
    ddTiny ^ 2 / (2 * cosLoQ ddTiny) ≤ 1 / 10 ∧
    tanCTQ trig8U 2 (ddTiny ^ 2 / (6 - ddTiny ^ 2)) (ddTiny ^ 2 / (2 * cosLoQ ddTiny)) ddtED ddTiny ≤
      c * trig8U ^ 2 ∧ tanHiQ ddTiny / ddTiny - 1 ≤ c * trig8U ^ 2

instance (c : ℚ) : Decidable (DDTanTinyOk c) := by
  unfold DDTanTinyOk
  infer_instance

/-- the rows of SINR's coefficients are double words -/
theorem dd_rows_s : DDRows trig2Fs := by decide +kernel

/-- the rows of COSR's coefficients are double words -/
theorem dd_rows_c : DDRows trig2Fc := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `C ≤ 7.841412u²` in every run of buckets -/
theorem dd_all : ∀ g ∈ trig2Tab.groups, DDOk ddC g := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- `C^T ≤ 28.414066u²` in every run of buckets -/
theorem dd_tan_all : ∀ g ∈ trig2Tab.groups, DDTanOk ddCt g := by decide +kernel

/-- the bounds below the last bucket, for the sine and the cosine -/
theorem dd_tiny : DDTinyOk ddC := by decide +kernel

/-- the bounds below the last bucket, for the tangent -/
theorem dd_tan_tiny : DDTanTinyOk ddCt := by decide +kernel

/-- the double-double coefficients of SINR: the two leading parts of each row of the table -/
noncomputable def ddFs (k : ℕ) : ℝ × ℝ := (trig2Tab.FsR k 0, trig2Tab.FsR k 1)

/-- the double-double coefficients of COSR -/
noncomputable def ddFc (k : ℕ) : ℝ × ℝ := (trig2Tab.FcR k 0, trig2Tab.FcR k 1)

theorem dd_phiS (k : ℕ) : |dwVal (ddFs k) - sinC k| ≤ ((ddtPhiS k : ℚ) : ℝ) := by
  unfold ddtPhiS ddFs dwVal TrigTab.FsR
  push_cast
  rw [cast_sinC]

theorem dd_phiC (k : ℕ) : |dwVal (ddFc k) - cosC k| ≤ ((ddtPhiC k : ℚ) : ℝ) := by
  unfold ddtPhiC ddFc dwVal TrigTab.FcR
  push_cast
  rw [cast_cosC]

variable (p : ℤ) [Prec_gt_0 p]

/-- a table whose parts are floats and whose rows round to their first parts gives double words -/
theorem dd_row_dw (T : List (List (ℤ × ℕ))) (hF : ∀ t ∈ T, ∀ q ∈ t, rnQ p (dyQ q) = dyQ q)
    (hD : ∀ t ∈ T, rnQ p (dyFn t 0 + dyFn t 1) = dyFn t 0) (k : ℕ) :
    DW p (((dyFn (T.getD k []) 0 : ℚ) : ℝ), ((dyFn (T.getD k []) 1 : ℚ) : ℝ)) := by
  refine ⟨dyFn_getD_F p T (dyF_of_all p T hF) k 0, dyFn_getD_F p T (dyF_of_all p T hF) k 1, ?_⟩
  show RN p (((dyFn (T.getD k []) 0 : ℚ) : ℝ) + ((dyFn (T.getD k []) 1 : ℚ) : ℝ)) =
    ((dyFn (T.getD k []) 0 : ℚ) : ℝ)
  by_cases hk : k < T.length
  · have hm : T.getD k [] ∈ T := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      exact List.getElem_mem hk
    rw [← Rat.cast_add, ← cast_rn, hD _ hm]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simp [dyFn_of_le, RN_zero]

theorem dd_Fs_dw (hp : p = 53) (k : ℕ) : DW p (ddFs k) := by
  subst hp
  exact dd_row_dw 53 trig2Fs trig2_tab.2.2.1 dd_rows_s k

theorem dd_Fc_dw (hp : p = 53) (k : ℕ) : DW p (ddFc k) := by
  subst hp
  exact dd_row_dw 53 trig2Fc trig2_tab.2.2.2.1 dd_rows_c k

omit [Prec_gt_0 p] in
/-- `ddTiny` is `u(1 + 2^{-50})` -/
theorem cast_ddTiny (hp : p = 53) : ((ddTiny : ℚ) : ℝ) = u p * (1 + 1 / 2 ^ 50) := by
  unfold ddTiny
  push_cast
  rw [cast_trig8U p hp]

/-- below the early return's test, `|x| ≤ r̄_min` -/
theorem dd_early (hp : p = 53) (x : ℕ → ℝ) (hx : DW p (x 0, x 1)) (hsmall : |x 0| < u p) :
    |∑ i ∈ range 2, x i| ≤ ((ddTiny : ℚ) : ℝ) := by
  have hu : u p = 1 / 9007199254740992 := by rw [hp]; unfold u; norm_num
  have h1 : |x 1| ≤ u p * |x 0| := (DW.parts p hx).1
  have h2 := abs_add_le (x 0) (x 1)
  rw [cast_ddTiny p hp, show ∑ i ∈ range 2, x i = x 0 + x 1 by simp [sum_range_succ]]
  rw [hu] at h1 hsmall ⊢
  linarith

/-- the computed sine and cosine of the reduced argument, in a run of the double-double functions: for rationals
`r̄`, `δ_S` and `δ_C`, those below the last bucket or those of the run of buckets of `|r_h|`, `|r|, |r_e| ≤ r̄`, and
`Y_s` and `Y_c` are double words within `δ_S|sin r|` and `δ_C cos r` -/
theorem dd_run (hp : p = 53) (x : ℕ → ℝ) (hx : DW p (x 0, x 1)) (hx0 : |x 0| ≤ 2 ^ 52) (es : ℝ → ℤ) :
    ∃ rb dS dC : ℚ,
      ((rb = ddTiny ∧ dS = ddTiny ^ 2 / (6 - ddTiny ^ 2) ∧ dC = ddTiny ^ 2 / (2 * cosLoQ ddTiny)) ∨
        ∃ g ∈ trig2Tab.groups, rb = trig8Rb g.1 ∧ dS = ddtDS (trig8Rb g.1) ddtPhiS g.2.1 ∧
          dC = ddtDC (trig8Rb g.1) ddtPhiC g.2.2) ∧
      |dwVal (ddRed p x)| ≤ ((rb : ℚ) : ℝ) ∧
      |∑ i ∈ range 2, x i - redK p 2 x * (Real.pi / 2)| ≤ ((rb : ℚ) : ℝ) ∧
      0 ≤ ((dS : ℚ) : ℝ) ∧ 0 ≤ ((dC : ℚ) : ℝ) ∧
      DW p (ddYs p es trig2Tab.Ks ddFs x) ∧ DW p (ddYc p trig2Tab.Kc ddFc x) ∧
      |dwVal (ddYs p es trig2Tab.Ks ddFs x) - Real.sin (dwVal (ddRed p x))| ≤
        ((dS : ℚ) : ℝ) * |Real.sin (dwVal (ddRed p x))| ∧
      |dwVal (ddYc p trig2Tab.Kc ddFc x) - Real.cos (dwVal (ddRed p x))| ≤
        ((dC : ℚ) : ℝ) * Real.cos (dwVal (ddRed p x)) := by
  subst hp
  obtain ⟨hH, hxF, hrdw, hval⟩ := dd_red 53 rfl x hx hx0
  by_cases htiny : |(ddRed 53 x).1| < u (53 : ℤ)
  · -- `|r_h|` below the last bucket: SINR returns `r` and COSR `1`
    obtain ⟨t1, t2, t3, -⟩ := dd_tiny
    have hT1 : ((ddTiny : ℚ) : ℝ) ≤ 1 := by
      have := (Rat.cast_le (K := ℝ)).mpr t1
      push_cast at this
      linarith
    have h6 : (0 : ℚ) ≤ ddTiny ^ 2 / (6 - ddTiny ^ 2) := div_nonneg (sq_nonneg _) (by linarith)
    have h7 : (0 : ℚ) ≤ ddTiny ^ 2 / (2 * cosLoQ ddTiny) := div_nonneg (sq_nonneg _) (by linarith)
    obtain ⟨hr, hre⟩ := dd_bucket 53 rfl x hx hx0 (-53) le_rfl htiny
    rw [show (2 : ℝ) ^ (-53 : ℤ) * (1 + 1 / 2 ^ 50) = ((ddTiny : ℚ) : ℝ) by rw [cast_ddTiny 53 rfl]; rfl] at hr hre
    refine ⟨ddTiny, _, _, Or.inl ⟨rfl, rfl, rfl⟩, hr, hre, by exact_mod_cast h6, by exact_mod_cast h7, ?_, ?_, ?_, ?_⟩
    · simp only [ddYs, htiny, ↓reduceIte]
      exact hrdw
    · simp only [ddYc, htiny, ↓reduceIte]
      exact DW.of_F 53 (F_one 53)
    · simp only [ddYs, htiny, ↓reduceIte]
      push_cast
      exact sinr_small _ _ hr hT1
    · simp only [ddYc, htiny, ↓reduceIte, dwVal, add_zero]
      push_cast
      rw [cast_cosLo]
      exact cosr_small _ _ hr hT1
  -- a bucket: the double-word series' bounds
  obtain ⟨hmem, hlt⟩ := trig2Tab.G_spec ⟨_, _, rfl⟩ |(ddRed 53 x).1|
  obtain ⟨hKs, hKc⟩ := trig2_tab.2.2.2.2 _ hmem
  obtain ⟨-, -, -, ok4, -⟩ := dd_all _ hmem
  have eKs : trig2Tab.Ks |(ddRed 53 x).1| = (trig2Tab.G |(ddRed 53 x).1|).2.1 := rfl
  have eKc : trig2Tab.Kc |(ddRed 53 x).1| = (trig2Tab.G |(ddRed 53 x).1|).2.2 := rfl
  generalize trig2Tab.G |(ddRed 53 x).1| = g at *
  have hr : |dwVal (ddRed 53 x)| ≤ ((trig8Rb g.1 : ℚ) : ℝ) ∧
      |∑ i ∈ range 2, x i - redK 53 2 x * (Real.pi / 2)| ≤ ((trig8Rb g.1 : ℚ) : ℝ) := by
    by_cases hj : g.1 = 0
    · have e : ((trig8Rb g.1 : ℚ) : ℝ) = 78541 / 100000 := by
        simp only [trig8Rb, hj, ↓reduceIte]
        norm_num
      obtain ⟨-, -, h3, -, -⟩ := lemma32_r 53 2 rfl (by norm_num) x hxF hH hx0
      rw [e, hval]
      exact ⟨h3, lemma32_re 53 2 rfl (by norm_num) x hH hx0⟩
    · have hlt' := hlt hj
      have e : ((trig8Rb g.1 : ℚ) : ℝ) = (2 : ℝ) ^ (-(g.1 : ℤ)) * (1 + 1 / 2 ^ 50) := by
        simp only [trig8Rb, hj, ↓reduceIte]
        push_cast
        rw [zpow_neg, zpow_natCast, one_div]
      rw [e]
      exact dd_bucket 53 rfl x hx hx0 (-(g.1 : ℤ)) ((not_lt.mp htiny).trans hlt'.le) hlt'
  have hrb1 : trig8Rb g.1 ≤ 1 := ok4.trans (by norm_num)
  obtain ⟨s1, s0, sdw⟩ := dd_sinr 53 rfl hrdw hr.1 hrb1 ddFs (dd_Fs_dw 53 rfl) dd_phiS g.2.1 hKs
    (es |(ddRed 53 x).1|)
  obtain ⟨c1, c0, cdw⟩ := dd_cosr 53 rfl hrdw hr.1 hrb1 ddFc (dd_Fc_dw 53 rfl) dd_phiC g.2.2 hKc
  refine ⟨trig8Rb g.1, _, _, Or.inr ⟨g, hmem, rfl, rfl, rfl⟩, hr.1, hr.2, s0, c0, ?_, ?_, ?_, ?_⟩
  · simp only [ddYs, htiny, ↓reduceIte, eKs]
    exact sdw
  · simp only [ddYc, htiny, ↓reduceIte, eKc]
    exact cdw
  · simp only [ddYs, htiny, ↓reduceIte, eKs]
    exact s1
  · simp only [ddYc, htiny, ↓reduceIte, eKc]
    exact c1

/-- Theorem 35 (`thm:trig`) for multidouble's double-double sine and cosine, at `p = 53`: for a double word `x` with
`|x_0| ≤ 2^52`, `DD::sin` and `DD::cos` are within `7.841412u²` of `sin x` and `cos x`, relatively, plus `5E_π` -/
theorem thm35_sincos_dd (hp : p = 53) (x : ℕ → ℝ) (hx : DW p (x 0, x 1)) (hx0 : |x 0| ≤ 2 ^ 52) (es : ℝ → ℤ) :
    |dwVal (ddSin p es trig2Tab.Ks trig2Tab.Kc ddFs ddFc x) - Real.sin (x 0 + x 1)| ≤
        7841412 / 1000000 * u p ^ 2 * |Real.sin (x 0 + x 1)| +
          5 * (|(redK p 2 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) ∧
      |dwVal (ddCos p es trig2Tab.Ks trig2Tab.Kc ddFs ddFc x) - Real.cos (x 0 + x 1)| ≤
        7841412 / 1000000 * u p ^ 2 * |Real.cos (x 0 + x 1)| +
          5 * (|(redK p 2 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) := by
  subst hp
  have hsum : ∑ i ∈ range 2, x i = x 0 + x 1 := by simp [sum_range_succ]
  rw [← hsum, ← show ((ddC : ℚ) : ℝ) = 7841412 / 1000000 by unfold ddC; norm_num]
  have htu := cast_trig8U 53 rfl
  have hEπ : 0 ≤ 5 * (|(redK 53 2 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) := by positivity
  by_cases hsmall : |x 0| < u (53 : ℤ)
  · -- the early return
    obtain ⟨t1, -, t3, -, -, -, t7, t8⟩ := dd_tiny
    have hT1 : ((ddTiny : ℚ) : ℝ) ≤ 1 := by
      have := (Rat.cast_le (K := ℝ)).mpr t1
      push_cast at this
      linarith
    have hcT : (0 : ℝ) < cosLo ((ddTiny : ℚ) : ℝ) := by
      rw [← cast_cosLo]
      exact_mod_cast t3
    have hX := dd_early 53 rfl x hx hsmall
    have hs := sinr_small _ _ hX hT1
    have hc := cosr_small _ _ hX hT1
    have c7 : ((ddTiny : ℚ) : ℝ) ^ 2 / (6 - ((ddTiny : ℚ) : ℝ) ^ 2) ≤ (ddC : ℝ) * u (53 : ℤ) ^ 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr t7
      push_cast at this
      rwa [htu] at this
    have c8 : ((ddTiny : ℚ) : ℝ) ^ 2 / (2 * cosLo ((ddTiny : ℚ) : ℝ)) ≤ (ddC : ℝ) * u (53 : ℤ) ^ 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr t8
      push_cast at this
      rwa [htu, cast_cosLo] at this
    have hcoef : 0 ≤ ((ddTiny : ℚ) : ℝ) ^ 2 / (2 * cosLo ((ddTiny : ℚ) : ℝ)) :=
      div_nonneg (sq_nonneg _) (by linarith)
    have eS : dwVal (ddSin 53 es trig2Tab.Ks trig2Tab.Kc ddFs ddFc x) = ∑ i ∈ range 2, x i := by
      simp only [ddSin, hsmall, ↓reduceIte, dwVal, hsum]
    have eC : dwVal (ddCos 53 es trig2Tab.Ks trig2Tab.Kc ddFs ddFc x) = 1 := by
      simp only [ddCos, hsmall, ↓reduceIte, dwVal, add_zero]
    rw [eS, eC]
    exact ⟨hs.trans (le_add_of_le_of_nonneg (mul_le_mul_of_nonneg_right c7 (abs_nonneg _)) hEπ),
      hc.trans ((mul_le_mul_of_nonneg_left (le_abs_self _) hcoef).trans
        (le_add_of_le_of_nonneg (mul_le_mul_of_nonneg_right c8 (abs_nonneg _)) hEπ))⟩
  have eS : dwVal (ddSin 53 es trig2Tab.Ks trig2Tab.Kc ddFs ddFc x) =
      dwVal (ddQuad (redK 53 2 x) (ddYs 53 es trig2Tab.Ks ddFs x) (ddYc 53 trig2Tab.Kc ddFc x)) := by
    simp only [ddSin, hsmall, ↓reduceIte]
  have eC : dwVal (ddCos 53 es trig2Tab.Ks trig2Tab.Kc ddFs ddFc x) =
      dwVal (ddQuad (redK 53 2 x + 1) (ddYs 53 es trig2Tab.Ks ddFs x) (ddYc 53 trig2Tab.Kc ddFc x)) := by
    simp only [ddCos, hsmall, ↓reduceIte]
  rw [eS, eC, dwVal_ddQuad, dwVal_ddQuad]
  -- the bounds of the run, and the kernel's check of `C` on them
  obtain ⟨rb, dS, dC, hcase, -, hre, a1, a3, -, -, hA, hB⟩ := dd_run 53 rfl x hx hx0 es
  have hC : trigCQ trig8U 2 dS dC rb ≤ ddC * trig8U ^ 2 ∧ rb ≤ 8 / 10 ∧ dS ≤ 1 / 2 ∧ dC ≤ 1 / 2 := by
    rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨g, hg, rfl, rfl, rfl⟩
    · obtain ⟨t1, -, -, t4, t5, t6, -, -⟩ := dd_tiny
      exact ⟨t6, t1, t4, t5⟩
    · obtain ⟨ok1, ok2, ok3, ok4, -⟩ := dd_all g hg
      exact ⟨ok3, ok4, ok1, ok2⟩
  obtain ⟨c1, c2, c3, c4⟩ := hC
  obtain ⟨ks, kc⟩ := dd_sincos_core 53 rfl x hx hx0 (((Rat.cast_le (K := ℝ)).mpr c2).trans_eq (by norm_num)) hre a1
    (((Rat.cast_le (K := ℝ)).mpr c3).trans_eq (by norm_num)) a3
    (((Rat.cast_le (K := ℝ)).mpr c4).trans_eq (by norm_num)) hA hB
  have o1 := (Rat.cast_le (K := ℝ)).mpr c1
  push_cast at o1
  rw [htu] at o1
  have o := (trigC_le 53 2 htu rb le_rfl le_rfl).trans o1
  exact ⟨ks.trans (add_le_add (mul_le_mul_of_nonneg_right o (abs_nonneg _)) le_rfl),
    kc.trans (add_le_add (mul_le_mul_of_nonneg_right o (abs_nonneg _)) le_rfl)⟩

/-- Theorem 35 (`thm:trig`) for multidouble's double-double tangent, at `p = 53`: for a double word `x` with
`|x_0| ≤ 2^52`, at least `2^{2p-1074}` away from the nonzero multiples of `π/2`, `DD::tan` is within
`28.414066u² + 5E_π/|sin x cos x|` of `tan x`, relatively -/
theorem thm35_tan_dd (hp : p = 53) (x : ℕ → ℝ) (hx : DW p (x 0, x 1)) (hx0 : |x 0| ≤ 2 ^ 52) (es et : ℝ → ℤ)
    (hfar : redK p 2 x ≠ 0 → (2 : ℝ) ^ (p * (2 : ℕ) - 1074) ≤ |x 0 + x 1 - redK p 2 x * (Real.pi / 2)|) :
    |dwVal (ddTan p es et trig2Tab.Ks trig2Tab.Kc ddFs ddFc x) - Real.tan (x 0 + x 1)| ≤
      (28414066 / 1000000 * u p ^ 2 + 5 * (|(redK p 2 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) /
        |Real.sin (x 0 + x 1) * Real.cos (x 0 + x 1)|) * |Real.tan (x 0 + x 1)| := by
  subst hp
  have hsum : ∑ i ∈ range 2, x i = x 0 + x 1 := by simp [sum_range_succ]
  rw [← hsum] at hfar ⊢
  rw [← show ((ddCt : ℚ) : ℝ) = 28414066 / 1000000 by unfold ddCt; norm_num]
  have htu := cast_trig8U 53 rfl
  have hE : 0 ≤ 5 * (|(redK 53 2 x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) /
      |Real.sin (∑ i ∈ range 2, x i) * Real.cos (∑ i ∈ range 2, x i)| := by positivity
  by_cases hsmall : |x 0| < u (53 : ℤ)
  · -- the early return
    obtain ⟨t0, t1, -, -, -, -, -, t7⟩ := dd_tan_tiny
    have hT1 : ((ddTiny : ℚ) : ℝ) ≤ 1 := by
      have := (Rat.cast_le (K := ℝ)).mpr t1
      push_cast at this
      linarith
    have hs := tan_small (dd_early 53 rfl x hx hsmall) (by exact_mod_cast t0) hT1
    have ce : tanHi ((ddTiny : ℚ) : ℝ) / ((ddTiny : ℚ) : ℝ) - 1 ≤ (ddCt : ℝ) * u (53 : ℤ) ^ 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr t7
      push_cast at this
      rwa [htu, cast_tanHi] at this
    have eT : dwVal (ddTan 53 es et trig2Tab.Ks trig2Tab.Kc ddFs ddFc x) = ∑ i ∈ range 2, x i := by
      simp only [ddTan, hsmall, ↓reduceIte, dwVal, hsum]
    rw [eT]
    exact hs.trans (mul_le_mul_of_nonneg_right (le_add_of_le_of_nonneg ce hE) (abs_nonneg _))
  have eT : ddTan 53 es et trig2Tab.Ks trig2Tab.Kc ddFs ddFc x =
      ddTanQ 53 (redK 53 2 x) (et |(ddRed 53 x).1|) (ddYs 53 es trig2Tab.Ks ddFs x)
        (ddYc 53 trig2Tab.Kc ddFc x) := by
    simp only [ddTan, hsmall, ↓reduceIte]
  rw [eT]
  -- the bounds of the run, and the kernel's check of `C^T` on them
  obtain ⟨rb, dS, dC, hcase, hr, hre, a1, a3, hYs, hYc, hA, hB⟩ := dd_run 53 rfl x hx hx0 es
  have hC : tanCTQ trig8U 2 dS dC ddtED rb ≤ ddCt * trig8U ^ 2 ∧ rb ≤ 8 / 10 ∧ dS ≤ 1 / 10 ∧ dC ≤ 1 / 10 := by
    rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨g, hg, rfl, rfl, rfl⟩
    · obtain ⟨-, t1, -, -, t4, t5, t6, -⟩ := dd_tan_tiny
      exact ⟨t6, t1, t4, t5⟩
    · obtain ⟨ok1, ok2, ok3, ok4, -⟩ := dd_tan_all g hg
      exact ⟨ok3, ok4, ok1, ok2⟩
  obtain ⟨c1, c2, c3, c4⟩ := hC
  have key := dd_tan_core 53 rfl x hx hx0 hsmall hYs hYc
    (((Rat.cast_le (K := ℝ)).mpr c2).trans_eq (by norm_num)) hr hre a1
    (((Rat.cast_le (K := ℝ)).mpr c3).trans_eq (by norm_num)) a3
    (((Rat.cast_le (K := ℝ)).mpr c4).trans_eq (by norm_num)) hA hB hfar (et |(ddRed 53 x).1|)
  have hD := cast_ddtED 53 rfl
  have o9 := (Rat.cast_le (K := ℝ)).mpr c1
  push_cast at o9
  rw [htu] at o9
  have hCT := (tanCT_le 53 2 htu rb a1 le_rfl (lt_of_le_of_lt c3 (by norm_num)) a3 le_rfl
    (lt_of_le_of_lt c4 (by norm_num)) (by rw [← hD]; exact_mod_cast (show (0 : ℚ) ≤ ddtED by
      unfold ddtED trig8U; positivity)) hD.ge).trans o9
  exact key.trans (mul_le_mul_of_nonneg_right (add_le_add hCT le_rfl) (abs_nonneg _))

end ExpansionBounds
