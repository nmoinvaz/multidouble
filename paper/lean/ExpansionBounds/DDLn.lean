import ExpansionBounds.DDLogAt
import ExpansionBounds.DDLog

/-!
# Proposition 44 (`prop:ddexplog`): `DD::ln` within `15.351u²|ln x| + 2^{-1071}`

`DD::ln` at `p = 53`: LOG with `s = 1`, `d = 27` and `q = 3` on double words, with multidouble's constants and
binary64's subnormals, from the start `y_0 = RN(ln_b(x_h) + w)`, `w` the computed quotient `x_l/x_h`
(`ddLnY0`, `ddLn`). The four double-word operations are those of `DDOps.lean`, with their published bounds as
hypotheses (`DWSpec`).

The start is within `E(ℓ) = e_0 + e_1ℓ` of `ln x` for `ℓ = |ln x|` (Lemma 43 and `prop44_start`), and within
`ℓ(u(1 + ℓ) + ℓ)` for `ℓ < u(1 - u)/2` (`prop44_start_small`). The reduction of `-y_0` gives `k` and `r`
(`ddl_run`). For `k ≠ 0`, `ℓ` is at least the least `ℓ` with `k ≠ 0`, and the exponent of `U` and `|r|` select an
interval of `|r|` (`ddl1_bin`, `ddl_k1`). For `k = 0`, `r = -y_0`, and the exponent of `U` selects a group, whose
`|y_0|` put `ℓ` in an interval: on the start's linear piece (`ddl_k0`), or, for the exponents below `-59`, below
`u(1 - u)/2`, on its second piece (`ddl_k0_small`). The kernel's checks of the case (`DDLog2/`) then give the bound
through `ddl_core`.
-/

namespace ExpansionBounds

open Finset

/-- the groups of `k ≠ 0` cover the exponents `-118 ≤ e ≤ -2` and those of `k = 0` on the linear piece
`-59 ≤ e ≤ -2`; the group of degree 2 of `k = 0` is `-118 ≤ e ≤ -60`; the last groups, of degree 1, end at `-119` -/
theorem ddl_grps : (∀ e : ℤ, -118 ≤ e → e ≤ -2 → ∃ g ∈ ddl1Grp, g.2.1 ≤ e ∧ e ≤ g.2.2.1) ∧ ddl1Last.1 = 1 ∧
    ddl1Last.2.2.1 = -119 ∧ (∀ e : ℤ, -59 ≤ e → e ≤ -2 → ∃ g ∈ ddl0Lin, g.2.1 ≤ e ∧ e ≤ g.2.2.1) ∧
    ddl0S.2.1 = -118 ∧ ddl0S.2.2.1 = -60 ∧ ddl0Last.1 = 1 ∧ ddl0Last.2.2.1 = -119 := by
  decide +kernel

variable (p : ℤ) [Prec_gt_0 p]

/-- the start of `DD::ln`: `y_0 = RN(ln_b(x_h) + w)`, `w` the computed quotient `x_l/x_h` -/
noncomputable def ddLnY0 (x : ℝ × ℝ) (w : ℝ) : ℝ := RN p (lnB p x.1 + w)

/-- `DD::ln` after its start `y_0`: `k = k₁ + k₂` and `r` from EXP's reduction of `-y_0`, `t` from its core with the
exponent `e` of `U`, and LOG's steps (3) to (5) with the exponents `e_φ`, `e_t` and `e_c`; every scaling rounds
each part by `S`, the scaling of `x` in two steps `2^{k₁}`, `2^{k₂}`, and that of step (4)'s product in two steps
`2^{e_φ}`, `2^{e_t}` -/
noncomputable def ddLn (O : DWOps) (S : ℝ → ℝ) (x : ℝ × ℝ) (y0 : ℝ) (k₁ k₂ e eφ et ec : ℤ) : ℝ × ℝ :=
  ddLogOp O (ddS2 S k₂) (ddS2 S et) (fun v => (S v.1, S v.2)) y0 x (k₁ + k₂)
    (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e)) 118 eφ et ec ddlF 3

/-- what a run of `DD::ln` after its start is asked: `k = k₁ + k₂` with `k₂ ≤ 0`; `e`, `e_φ`, `e_t` and `e_c` are
the exponents of step (2)'s `U` for `r`, `φ`, `t` and `c`, or `-1023` where `U < 2^{-1022}`, as multidouble selects
them, though below `2^{-1022}` the predicate also admits the exponent of `U` itself, which the proof does not need to
exclude; and Lemma 41 on double words, `φ = x' - 1` exactly. For `k > 0` the split `(k, 0)` meets `k₂ ≤ 0`;
multidouble's, `k₁ = k/2` rounded toward zero, scales up in both steps, which binary64 does exactly, so it gives the
same value -/
structure DDLnSel (O : DWOps) (S : ℝ → ℝ) (x : ℝ × ℝ) (y0 : ℝ) (k₁ k₂ e eφ et ec : ℤ) : Prop where
  hk : k₁ + k₂ = expK p (-y0)
  hk2 : k₂ ≤ 0
  hsel : ((2 : ℝ) ^ e ≤ dd2U p (dd2R p O (-y0, 0)) ∧ dd2U p (dd2R p O (-y0, 0)) < (2 : ℝ) ^ (e + 1)) ∨
    (dd2U p (dd2R p O (-y0, 0)) < (2 : ℝ) ^ (-1022 : ℤ) ∧ e = -1023)
  hselφ : ((2 : ℝ) ^ eφ ≤ dd2U p (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) ∧
      dd2U p (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) < (2 : ℝ) ^ (eφ + 1)) ∨
    (dd2U p (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) < (2 : ℝ) ^ (-1022 : ℤ) ∧ eφ = -1023)
  hselt : ((2 : ℝ) ^ et ≤ dd2U p (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e)) ∧
      dd2U p (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e)) < (2 : ℝ) ^ (et + 1)) ∨
    (dd2U p (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e)) < (2 : ℝ) ^ (-1022 : ℤ) ∧
      et = -1023)
  hselc : ((2 : ℝ) ^ ec ≤ dd2U p (ddLogC O (ddS2 S et) 118 eφ et (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x)
        (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e))) ∧
      dd2U p (ddLogC O (ddS2 S et) 118 eφ et (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x)
        (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e))) < (2 : ℝ) ^ (ec + 1)) ∨
    (dd2U p (ddLogC O (ddS2 S et) 118 eφ et (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x)
        (ddExpT O (fun v => (S v.1, S v.2)) e (dd2R p O (-y0, 0)) dd2F (ddDeg e))) < (2 : ℝ) ^ (-1022 : ℤ) ∧
      ec = -1023)
  hφex : dwVal (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) = dwVal (ddS2 S k₂ (dwScale (k₁ + k₂) x)) - 1

omit [Prec_gt_0 p] in
/-- the targets as real numbers: `15.351u²ℓ` and `15.351u²ℓ + 2^{-1071}` -/
theorem ddl_target (hp : p = 53) (l : ℝ) :
    ((ddlEps : ℚ) : ℝ) * l = 15351 / 1000 * u p ^ 2 * l ∧ ((ddlFl : ℚ) : ℝ) = (2 : ℝ) ^ (-1071 : ℤ) := by
  have hu := red8U_cast p hp
  constructor
  · unfold ddlEps
    push_cast
    rw [hu]
  · unfold ddlFl
    rw [show (-1071 : ℤ) = -((1071 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast, ← one_div]
    simp only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat]

/-- the start: for a double word `x > 0`, `x_h > 0`, `y_0` is a float within `e_0 + e_1ℓ` of `ln x`, `ℓ = |ln x|`,
and within `ℓ(u(1 + ℓ) + ℓ)` for `ℓ < u(1 - u)/2`, where `x_h = 1` and the quotient is `x_l` -/
theorem ddl_start (hp : p = 53) (x : ℝ × ℝ) (hx : DW p x) (hX0 : 0 < dwVal x) (w : ℝ)
    (hw0 : |w - x.2 / x.1| ≤ u p * |x.2 / x.1| + (2 : ℝ) ^ (-1075 : ℤ)) (hw1 : x.1 = 1 → w = x.2) :
    F p (ddLnY0 p x w) ∧
      |ddLnY0 p x w - Real.log (dwVal x)| ≤ ((ddlE0 : ℚ) : ℝ) + ((ddlE1 : ℚ) : ℝ) * |Real.log (dwVal x)| ∧
      (|Real.log (dwVal x)| < u p * (1 - u p) / 2 → |ddLnY0 p x w - Real.log (dwVal x)| ≤
        |Real.log (dwVal x)| * (u p * (1 + |Real.log (dwVal x)|) + |Real.log (dwVal x)|)) := by
  have hu := red8U_cast p hp
  have hup := u_pos p
  obtain ⟨-, heta, -⟩ := ddl_casts
  -- `x_h > 0`
  have h0 : 0 ≤ x.1 := by
    have := RN_mono p hX0.le
    rw [RN_zero] at this
    have h2 : RN p (dwVal x) = x.1 := hx.2.2
    rw [h2] at this
    exact this
  have hne : x.1 ≠ 0 := fun h => by
    have h2 : RN p (dwVal x) = x.1 := hx.2.2
    rw [h] at h2
    exact hX0.ne' (RN_eq_zero p h2)
  have hpos : 0 < x.1 := lt_of_le_of_ne h0 (Ne.symm hne)
  have hv : |x.2 / x.1| ≤ u p := by
    rw [abs_div, div_le_iff₀ (abs_pos.mpr hne)]
    exact (DW.parts p hx).1
  refine ⟨F_RN p _, ?_, fun hs => ?_⟩
  · have h1 := prop44_start p hp hx.1 hpos hv hw0 (le_refl |Real.log (x.1 + x.2)|)
    refine h1.trans (le_of_eq ?_)
    unfold ddlE0 ddlE1 ddlEtaB dwVal
    push_cast
    rw [hu, heta]
    ring
  · obtain ⟨hx1, h1⟩ := prop44_start_small p hp hx.1 hx.2.1 hx.2.2 hX0 (le_refl |Real.log (x.1 + x.2)|) hs
    have hy : ddLnY0 p x w = RN p (lnB p x.1 + RN p (x.2 / x.1)) := by
      unfold ddLnY0
      rw [hw1 hx1, hx1, div_one, RN_of_F p hx.2.1]
    rw [hy]
    exact h1

/-- the exponent of `U` is at most `-2` for a double word below `2^{-1}(1 - 2^{-46})` -/
theorem ddl_e_le (hp : p = 53) {v : ℝ × ℝ} (hv : DW p v) {top : ℝ} (htop : top < (2 : ℝ) ^ (-1 : ℤ) * (1 - 1 / 2 ^ 46))
    (hR : |dwVal v| ≤ top) {e : ℤ}
    (hsel : ((2 : ℝ) ^ e ≤ dd2U p v ∧ dd2U p v < (2 : ℝ) ^ (e + 1)) ∨
      (dd2U p v < (2 : ℝ) ^ (-1022 : ℤ) ∧ e = -1023)) : e ≤ -2 := by
  by_contra hcon
  rcases hsel with ⟨h1, -⟩ | ⟨-, he⟩
  · have hl := dd2U_low p hp hv h1
    have h6 : (2 : ℝ) ^ (-1 : ℤ) ≤ (2 : ℝ) ^ e := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h8 := mul_le_mul_of_nonneg_right h6 (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2 ^ 46)
    linarith only [hl, h8, htop, hR]
  · omega

/-- `k ≠ 0`: the exponent of `U` and `|r|` select an interval `[a, b]` of `|r|` with its checks -/
theorem ddl1_bin (hp : p = 53) {r : ℝ × ℝ} (hr : DW p r) (hR : |dwVal r| ≤ ((dyQ ddlTop1S : ℚ) : ℝ)) {e : ℤ}
    (hsel : ((2 : ℝ) ^ e ≤ dd2U p r ∧ dd2U p r < (2 : ℝ) ^ (e + 1)) ∨
      (dd2U p r < (2 : ℝ) ^ (-1022 : ℤ) ∧ e = -1023)) :
    ∃ a b : ℚ, 1 ≤ ddDeg e ∧ DDL1Bin (ddDeg e) a b ∧ ((a : ℚ) : ℝ) ≤ |dwVal r| ∧ |dwVal r| ≤ ((b : ℚ) : ℝ) := by
  obtain ⟨-, -, -, -, -, -, cTop, -⟩ := ddl_consts
  obtain ⟨gCov, gL1, gL2, -⟩ := ddl_grps
  have hTop := (Rat.cast_lt (K := ℝ)).mpr cTop
  push_cast at hTop
  have he2 := ddl_e_le p hp hr hTop hR hsel
  have hU := dd2U_lt p hp r hsel
  have hRS : |dwVal r| ≤ |r.1| + |r.2| := abs_add_le _ _
  have hR0 : 0 ≤ |dwVal r| := abs_nonneg _
  by_cases he118 : -118 ≤ e
  · obtain ⟨g, hg, hg1, hg2⟩ := gCov e he118 he2
    obtain ⟨o1, o2, o3, o4, o5⟩ := ddl1_all g hg
    have h1 : (2 : ℝ) ^ e ≤ dd2U p r := by
      rcases hsel with ⟨h1, -⟩ | ⟨-, he⟩
      · exact h1
      · omega
    have hlo : (((if false = true then 0 else (2 : ℚ) ^ g.2.1 * (1 - 1 / 2 ^ 46) : ℚ)) : ℝ) ≤ |dwVal r| := by
      simp only [Bool.false_eq_true, ↓reduceIte]
      push_cast
      have h6 : (2 : ℝ) ^ g.2.1 ≤ (2 : ℝ) ^ e := zpow_le_zpow_right₀ (by norm_num) hg1
      have h8 := mul_le_mul_of_nonneg_right h6 (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2 ^ 46)
      linarith only [dd2U_low p hp hr h1, h8]
    have hhi : |dwVal r| ≤ (((min (dyQ ddlTop1S) ((2 : ℚ) ^ (g.2.2.1 + 1)) : ℚ)) : ℝ) := by
      push_cast
      exact le_min hR ((hRS.trans hU.le).trans (zpow_le_zpow_right₀ (by norm_num) (by omega)))
    obtain ⟨ab, hab, hab1, hab2⟩ := exp8Chain_cover _ _ _ o4 (by simpa using o3) |dwVal r| hlo hhi
    obtain ⟨bn, hbn, rfl⟩ := List.mem_map.mp hab
    exact ⟨_, _, by rw [← o1 e hg1 hg2]; exact o2, by rw [← o1 e hg1 hg2]; exact o5 bn hbn, hab1, hab2⟩
  · have he119 : e ≤ -119 := by omega
    obtain ⟨-, o2, o3, o4, o5⟩ := ddl1_last
    have hdl : ddDeg e = ddl1Last.1 := by rw [gL1, ddDeg_small he119]
    have hlo : (((if true = true then 0 else (2 : ℚ) ^ ddl1Last.2.1 * (1 - 1 / 2 ^ 46) : ℚ)) : ℝ) ≤ |dwVal r| := by
      simp only [↓reduceIte, Rat.cast_zero]
      exact hR0
    have hhi : |dwVal r| ≤ (((min (dyQ ddlTop1S) ((2 : ℚ) ^ (ddl1Last.2.2.1 + 1)) : ℚ)) : ℝ) := by
      rw [gL2]
      push_cast
      exact le_min hR ((hRS.trans hU.le).trans (zpow_le_zpow_right₀ (by norm_num) (by omega)))
    obtain ⟨ab, hab, hab1, hab2⟩ := exp8Chain_cover _ _ _ o4 (by simpa using o3) |dwVal r| hlo hhi
    obtain ⟨bn, hbn, rfl⟩ := List.mem_map.mp hab
    exact ⟨_, _, by rw [hdl]; exact o2, by rw [hdl]; exact o5 bn hbn, hab1, hab2⟩

omit [Prec_gt_0 p] in
/-- `|y_0| ≤ ȳ` from the start within `e_0 + e_1ℓ` and `ℓ ≤ 745.2` -/
theorem ddl_y0_le {y0 L : ℝ} (hE : |y0 - L| ≤ ((ddlE0 : ℚ) : ℝ) + ((ddlE1 : ℚ) : ℝ) * |L|) (hX : |L| ≤ 7452 / 10) :
    |y0| ≤ ((ddlYB : ℚ) : ℝ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, cE1, -, -, -, -⟩ := ddl_consts
  have hE1 : (0 : ℝ) ≤ ((ddlE1 : ℚ) : ℝ) := by exact_mod_cast cE1
  have hY : ((ddlYB : ℚ) : ℝ) = 7452 / 10 + (((ddlE1 : ℚ) : ℝ) * (7452 / 10) + ((ddlE0 : ℚ) : ℝ)) := by
    unfold ddlYB ddlE red8X
    push_cast
    ring
  have h1 := abs_sub_abs_le_abs_sub y0 L
  have h2 := mul_le_mul_of_nonneg_left hX hE1
  rw [hY]
  linarith only [h1, h2, hE, hX]

/-- `ddl_k1` with both conclusions: for `k ≠ 0`, `DD::ln`'s result is a double word within `15.351u²|ln x|` -/
theorem ddl_k1_both (hp : p = 53) {O : DWOps} (hO : DWSpec p O) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℝ × ℝ) (hx : DW p x) (hX0 : 0 < dwVal x) (hX : |Real.log (dwVal x)| ≤ 7452 / 10) (y0 : ℝ)
    (hy0 : F p y0)
    (hE : |y0 - Real.log (dwVal x)| ≤ ((ddlE0 : ℚ) : ℝ) + ((ddlE1 : ℚ) : ℝ) * |Real.log (dwVal x)|)
    {k₁ k₂ e eφ et ec : ℤ} (hrun : DDLnSel p O S x y0 k₁ k₂ e eφ et ec) (hk0 : expK p (-y0) ≠ 0) :
    DW p (ddLn p O S x y0 k₁ k₂ e eφ et ec) ∧
      |dwVal (ddLn p O S x y0 k₁ k₂ e eφ et ec) - Real.log (dwVal x)| ≤
        ((ddlEps : ℚ) : ℝ) * |Real.log (dwVal x)| := by
  have hu := red8U_cast p hp
  have hup := u_pos p
  obtain ⟨-, -, -, -, -, -, -, cLk, -, -, cE1, -, -, -, -⟩ := ddl_consts
  obtain ⟨-, -, -, -, -, -, ccr, -, -⟩ := dd2_consts
  have hcr : (0 : ℝ) < ((cr8 : ℚ) : ℝ) := by exact_mod_cast ccr
  have hE1 : (0 : ℝ) ≤ ((ddlE1 : ℚ) : ℝ) := by exact_mod_cast cE1
  obtain ⟨hr, -, h3⟩ := ddl_run p hp hO y0 hy0 (ddl_y0_le hE hX)
  obtain ⟨h31, h32, h33⟩ := h3 hk0
  obtain ⟨a, b, hd, hbin, hab1, hab2⟩ := ddl1_bin p hp hr h32 hrun.hsel
  obtain ⟨pos, hpos⟩ : ∃ pos : Bool, if pos then 0 ≤ dwVal (dd2R p O (-y0, 0)) else dwVal (dd2R p O (-y0, 0)) ≤ 0 := by
    rcases le_total 0 (dwVal (dd2R p O (-y0, 0))) with h | h
    · exact ⟨true, by simpa using h⟩
    · exact ⟨false, by simpa using h⟩
  obtain ⟨L, hL⟩ : ∃ L, L = |Real.log (dwVal x)| := ⟨_, rfl⟩
  rw [← hL] at hE hX ⊢
  -- `ℓ` is at least the least `ℓ` with `k ≠ 0`
  have hl1 : ((dyQ ddlLkS : ℚ) : ℝ) ≤ L := by
    have h1 := (Rat.cast_le (K := ℝ)).mpr cLk
    rw [Rat.cast_add, Rat.cast_mul, Rat.cast_add, Rat.cast_one, Rat.cast_div, Rat.cast_one, Rat.cast_mul,
      Rat.cast_mul, Rat.cast_ofNat, Rat.cast_add, Rat.cast_one, hu] at h1
    have h2 : 1 / (2 * ((cr8 : ℚ) : ℝ) * (1 + u p)) ≤ |y0| := by
      rw [div_le_iff₀ (by positivity)]
      linarith only [h31]
    have h3 := abs_sub_abs_le_abs_sub y0 (Real.log (dwVal x))
    have h4 : |Real.log (dwVal x)| ≤ L := by rw [hL]
    have h5 : (1 + ((ddlE1 : ℚ) : ℝ)) * ((dyQ ddlLkS : ℚ) : ℝ) ≤ (1 + ((ddlE1 : ℚ) : ℝ)) * L := by
      have h6 : |y0| ≤ |Real.log (dwVal x)| + (((ddlE0 : ℚ) : ℝ) + ((ddlE1 : ℚ) : ℝ) * L) := by
        linarith only [h3, hE]
      rw [← hL] at h6
      linarith only [h1, h2, h6]
    exact le_of_mul_le_mul_left h5 (by linarith only [hE1])
  have hl2 : L ≤ ((red8X : ℚ) : ℝ) := by
    have : ((red8X : ℚ) : ℝ) = 7452 / 10 := by simp [red8X]
    rw [this]
    exact hX
  have hat := ddl_at1 p hp hbin pos hl1 hl2
  rw [hL] at hat hE ⊢
  have ha0 : 0 ≤ a := hbin.1.1.2.2.1
  exact ddl_core_both p hp hO S hS x hx hX0 y0 hy0 hE k₁ k₂ hrun.hk hrun.hk2 hr (h33 b hab2) ha0 hab1 hab2 pos hpos e eφ
    et ec hd hrun.hselφ hrun.hselt hrun.hselc hrun.hφex hat

/-- `DD::ln` for `k ≠ 0`: within `15.351u²|ln x|` -/
theorem ddl_k1 (hp : p = 53) {O : DWOps} (hO : DWSpec p O) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℝ × ℝ) (hx : DW p x) (hX0 : 0 < dwVal x) (hX : |Real.log (dwVal x)| ≤ 7452 / 10) (y0 : ℝ)
    (hy0 : F p y0)
    (hE : |y0 - Real.log (dwVal x)| ≤ ((ddlE0 : ℚ) : ℝ) + ((ddlE1 : ℚ) : ℝ) * |Real.log (dwVal x)|)
    {k₁ k₂ e eφ et ec : ℤ} (hrun : DDLnSel p O S x y0 k₁ k₂ e eφ et ec) (hk0 : expK p (-y0) ≠ 0) :
    |dwVal (ddLn p O S x y0 k₁ k₂ e eφ et ec) - Real.log (dwVal x)| ≤
      ((ddlEps : ℚ) : ℝ) * |Real.log (dwVal x)| :=
  (ddl_k1_both p hp hO S hS x hx hX0 hX y0 hy0 hE hrun hk0).2

/-- `ddl_k0_small` with both conclusions: for `k = 0` on the start's second piece, `DD::ln`'s result is a double
word within `15.351u²|ln x| + 2^{-1071}` -/
theorem ddl_k0_small_both (hp : p = 53) {O : DWOps} (hO : DWSpec p O) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℝ × ℝ) (hx : DW p x) (hX0 : 0 < dwVal x) (y0 : ℝ) (hy0 : F p y0)
    (hE : |y0 - Real.log (dwVal x)| ≤ ((ddlE0 : ℚ) : ℝ) + ((ddlE1 : ℚ) : ℝ) * |Real.log (dwVal x)|)
    (hEs : |Real.log (dwVal x)| < u p * (1 - u p) / 2 → |y0 - Real.log (dwVal x)| ≤
      |Real.log (dwVal x)| * (u p * (1 + |Real.log (dwVal x)|) + |Real.log (dwVal x)|))
    {k₁ k₂ e eφ et ec : ℤ} (hrun : DDLnSel p O S x y0 k₁ k₂ e eφ et ec) (hr : DW p (dd2R p O (-y0, 0)))
    (hRa : |dwVal (dd2R p O (-y0, 0))| = |y0|)
    (hδ : |dwVal (dd2R p O (-y0, 0)) - (-y0 - expK p (-y0) * Real.log 2)| ≤ 0)
    (hytop : |y0| ≤ ((dyQ ddlTop0S : ℚ) : ℝ)) (hyU : |y0| < (2 : ℝ) ^ (e + 1)) (last : Bool)
    (g : ℕ × ℤ × ℤ × (ℤ × ℕ)) (hg : DDL0Small last g) (hdeg : g.1 = ddDeg e) (hehi : e ≤ g.2.2.1)
    (ha : (((if last then 0 else (2 : ℚ) ^ g.2.1 * (1 - 1 / 2 ^ 46) : ℚ)) : ℝ) ≤ |y0|) :
    DW p (ddLn p O S x y0 k₁ k₂ e eφ et ec) ∧
      |dwVal (ddLn p O S x y0 k₁ k₂ e eφ et ec) - Real.log (dwVal x)| ≤
        ((ddlEps : ℚ) : ℝ) * |Real.log (dwVal x)| + ((ddlFl : ℚ) : ℝ) := by
  have hu := red8U_cast p hp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, cE1, cE1lt, cE0, -, -⟩ := ddl_consts
  have hE1 : (0 : ℝ) ≤ ((ddlE1 : ℚ) : ℝ) := by exact_mod_cast cE1
  have hE1lt : ((ddlE1 : ℚ) : ℝ) < 1 := by exact_mod_cast cE1lt
  obtain ⟨-, o2, o3, o4, o5, o6⟩ := hg
  obtain ⟨pos, hpos⟩ : ∃ pos : Bool, if pos then 0 ≤ dwVal (dd2R p O (-y0, 0)) else dwVal (dd2R p O (-y0, 0)) ≤ 0 := by
    rcases le_total 0 (dwVal (dd2R p O (-y0, 0))) with h | h
    · exact ⟨true, by simpa using h⟩
    · exact ⟨false, by simpa using h⟩
  have hk : DDLChord0 pos g.1 (if last then 0 else (2 : ℚ) ^ g.2.1 * (1 - 1 / 2 ^ 46)) (dyQ g.2.2.2)
      (ddlEs (dyQ g.2.2.2)) (dyQ g.2.2.2 + ddlEs (dyQ g.2.2.2)) := by
    cases pos
    · exact o6
    · exact o5
  obtain ⟨L, hL⟩ : ∃ L, L = |Real.log (dwVal x)| := ⟨_, rfl⟩
  have hLU : L ≤ |y0| + (((ddlE0 : ℚ) : ℝ) + ((ddlE1 : ℚ) : ℝ) * L) := by
    have h1 := abs_sub_abs_le_abs_sub (Real.log (dwVal x)) y0
    rw [abs_sub_comm (Real.log (dwVal x)) y0] at h1
    rw [hL]
    linarith only [h1, hE]
  have hhi : |y0| ≤ (((min (dyQ ddlTop0S) ((2 : ℚ) ^ (g.2.2.1 + 1)) : ℚ)) : ℝ) := by
    push_cast
    exact le_min hytop (hyU.le.trans (zpow_le_zpow_right₀ (by norm_num) (by omega)))
  have hl2 : L ≤ ((dyQ g.2.2.2 : ℚ) : ℝ) := by
    have h3 := (Rat.cast_le (K := ℝ)).mpr o3
    rw [Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_one] at h3
    have h5 : (1 - ((ddlE1 : ℚ) : ℝ)) * L ≤ (1 - ((ddlE1 : ℚ) : ℝ)) * ((dyQ g.2.2.2 : ℚ) : ℝ) := by
      linarith only [h3, hLU, hhi]
    exact le_of_mul_le_mul_left h5 (by linarith only [hE1lt])
  have hsm : L < u p * (1 - u p) / 2 := by
    have h4 := (Rat.cast_lt (K := ℝ)).mpr o4
    rw [Rat.cast_div, Rat.cast_mul, Rat.cast_sub, Rat.cast_one, Rat.cast_ofNat, hu] at h4
    exact lt_of_le_of_lt hl2 h4
  have hL0 : 0 ≤ L := by rw [hL]; exact abs_nonneg _
  have hat := ddl_at0s p hp hk hL0 hl2
  rw [hdeg] at hat o2
  rw [hL] at hat hsm
  have hEsv := hEs hsm
  have hb : |dwVal (dd2R p O (-y0, 0))| ≤ |Real.log (dwVal x)| +
      |Real.log (dwVal x)| * (u p * (1 + |Real.log (dwVal x)|) + |Real.log (dwVal x)|) := by
    rw [hRa]
    have h1 := abs_sub_abs_le_abs_sub y0 (Real.log (dwVal x))
    linarith only [h1, hEsv]
  have ha0 : (0 : ℚ) ≤ (if last then 0 else (2 : ℚ) ^ g.2.1 * (1 - 1 / 2 ^ 46)) := hk.1.2.2.1
  exact ddl_core_both p hp hO S hS x hx hX0 y0 hy0 hEsv k₁ k₂ hrun.hk hrun.hk2 hr hδ ha0 (hRa ▸ ha) hb pos hpos e eφ
    et ec o2 hrun.hselφ hrun.hselt hrun.hselc hrun.hφex hat

/-- `DD::ln` for `k = 0` on the start's second piece: for a group with `DDL0Small` that holds the exponent `e` of
`U`, whose `|y_0|` are at least its `a` and below `2^{e+1}`, the result is within `15.351u²|ln x| + 2^{-1071}` -/
theorem ddl_k0_small (hp : p = 53) {O : DWOps} (hO : DWSpec p O) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℝ × ℝ) (hx : DW p x) (hX0 : 0 < dwVal x) (y0 : ℝ) (hy0 : F p y0)
    (hE : |y0 - Real.log (dwVal x)| ≤ ((ddlE0 : ℚ) : ℝ) + ((ddlE1 : ℚ) : ℝ) * |Real.log (dwVal x)|)
    (hEs : |Real.log (dwVal x)| < u p * (1 - u p) / 2 → |y0 - Real.log (dwVal x)| ≤
      |Real.log (dwVal x)| * (u p * (1 + |Real.log (dwVal x)|) + |Real.log (dwVal x)|))
    {k₁ k₂ e eφ et ec : ℤ} (hrun : DDLnSel p O S x y0 k₁ k₂ e eφ et ec) (hr : DW p (dd2R p O (-y0, 0)))
    (hRa : |dwVal (dd2R p O (-y0, 0))| = |y0|)
    (hδ : |dwVal (dd2R p O (-y0, 0)) - (-y0 - expK p (-y0) * Real.log 2)| ≤ 0)
    (hytop : |y0| ≤ ((dyQ ddlTop0S : ℚ) : ℝ)) (hyU : |y0| < (2 : ℝ) ^ (e + 1)) (last : Bool)
    (g : ℕ × ℤ × ℤ × (ℤ × ℕ)) (hg : DDL0Small last g) (hdeg : g.1 = ddDeg e) (hehi : e ≤ g.2.2.1)
    (ha : (((if last then 0 else (2 : ℚ) ^ g.2.1 * (1 - 1 / 2 ^ 46) : ℚ)) : ℝ) ≤ |y0|) :
    |dwVal (ddLn p O S x y0 k₁ k₂ e eφ et ec) - Real.log (dwVal x)| ≤
      ((ddlEps : ℚ) : ℝ) * |Real.log (dwVal x)| + ((ddlFl : ℚ) : ℝ) :=
  (ddl_k0_small_both p hp hO S hS x hx hX0 y0 hy0 hE hEs hrun hr hRa hδ hytop hyU last g hg hdeg hehi
    ha).2

/-- `ddl_k0` with both conclusions: for `k = 0`, `DD::ln`'s result is a double word within
`15.351u²|ln x| + 2^{-1071}` -/
theorem ddl_k0_both (hp : p = 53) {O : DWOps} (hO : DWSpec p O) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℝ × ℝ) (hx : DW p x) (hX0 : 0 < dwVal x) (hX : |Real.log (dwVal x)| ≤ 7452 / 10) (y0 : ℝ)
    (hy0 : F p y0)
    (hE : |y0 - Real.log (dwVal x)| ≤ ((ddlE0 : ℚ) : ℝ) + ((ddlE1 : ℚ) : ℝ) * |Real.log (dwVal x)|)
    (hEs : |Real.log (dwVal x)| < u p * (1 - u p) / 2 → |y0 - Real.log (dwVal x)| ≤
      |Real.log (dwVal x)| * (u p * (1 + |Real.log (dwVal x)|) + |Real.log (dwVal x)|))
    {k₁ k₂ e eφ et ec : ℤ} (hrun : DDLnSel p O S x y0 k₁ k₂ e eφ et ec) (hk0 : expK p (-y0) = 0) :
    DW p (ddLn p O S x y0 k₁ k₂ e eφ et ec) ∧
      |dwVal (ddLn p O S x y0 k₁ k₂ e eφ et ec) - Real.log (dwVal x)| ≤
        ((ddlEps : ℚ) : ℝ) * |Real.log (dwVal x)| + ((ddlFl : ℚ) : ℝ) := by
  obtain ⟨-, -, -, -, cT0, cTop0, -, -, -, -, cE1, cE1lt, -, -, -⟩ := ddl_consts
  obtain ⟨-, -, -, -, -, -, ccr, -, -⟩ := dd2_consts
  obtain ⟨-, -, -, gCov0, gS1, gS2, gL1, gL2⟩ := ddl_grps
  have hcr : (0 : ℝ) < ((cr8 : ℚ) : ℝ) := by exact_mod_cast ccr
  have hE1 : (0 : ℝ) ≤ ((ddlE1 : ℚ) : ℝ) := by exact_mod_cast cE1
  have hE1lt : ((ddlE1 : ℚ) : ℝ) < 1 := by exact_mod_cast cE1lt
  have hFl0 : (0 : ℝ) ≤ ((ddlFl : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ ddlFl := by unfold ddlFl; positivity
    exact_mod_cast this
  obtain ⟨hr, h2, -⟩ := ddl_run p hp hO y0 hy0 (ddl_y0_le hE hX)
  obtain ⟨hrx, hycr⟩ := h2 hk0
  -- `r = (-y_0, 0)`
  have hRv : dwVal (dd2R p O (-y0, 0)) = -y0 := by
    rw [hrx]
    simp [dwVal]
  have hRa : |dwVal (dd2R p O (-y0, 0))| = |y0| := by rw [hRv, abs_neg]
  have hδ : |dwVal (dd2R p O (-y0, 0)) - (-y0 - expK p (-y0) * Real.log 2)| ≤ 0 := by
    rw [hRv, hk0]
    simp
  have hytop : |y0| ≤ ((dyQ ddlTop0S : ℚ) : ℝ) := by
    have h1 := (Rat.cast_le (K := ℝ)).mpr cT0
    rw [Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat] at h1
    refine le_trans ?_ h1
    rw [le_div_iff₀ (by positivity)]
    linarith only [hycr]
  have hTop := (Rat.cast_lt (K := ℝ)).mpr cTop0
  push_cast at hTop
  have he2 := ddl_e_le p hp hr hTop (hRa ▸ hytop) hrun.hsel
  have hyU : |y0| < (2 : ℝ) ^ (e + 1) := by
    have hU := dd2U_lt p hp _ hrun.hsel
    rw [hrx] at hU
    simpa using hU
  by_cases he59 : -59 ≤ e
  · -- the start's linear piece
    obtain ⟨g, hg, hg1, hg2⟩ := gCov0 e he59 he2
    obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := ddl0_all g hg
    have h2e : (2 : ℝ) ^ e ≤ dd2U p (dd2R p O (-y0, 0)) := by
      rcases hrun.hsel with ⟨h1, -⟩ | ⟨-, he⟩
      · exact h1
      · omega
    have hlow := dd2U_low p hp hr h2e
    have ha : ((((2 : ℚ) ^ g.2.1 * (1 - 1 / 2 ^ 46) : ℚ)) : ℝ) ≤ |dwVal (dd2R p O (-y0, 0))| := by
      push_cast
      have h6 : (2 : ℝ) ^ g.2.1 ≤ (2 : ℝ) ^ e := zpow_le_zpow_right₀ (by norm_num) hg1
      have h8 := mul_le_mul_of_nonneg_right h6 (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2 ^ 46)
      linarith only [hlow, h8]
    obtain ⟨pos, hpos⟩ : ∃ pos : Bool,
        if pos then 0 ≤ dwVal (dd2R p O (-y0, 0)) else dwVal (dd2R p O (-y0, 0)) ≤ 0 := by
      rcases le_total 0 (dwVal (dd2R p O (-y0, 0))) with h | h
      · exact ⟨true, by simpa using h⟩
      · exact ⟨false, by simpa using h⟩
    have hk : DDLChord pos g.1 ((2 : ℚ) ^ g.2.1 * (1 - 1 / 2 ^ 46)) (dyQ g.2.2.2.1) (ddlE (dyQ g.2.2.2.1))
        (dyQ g.2.2.2.1 + ddlE (dyQ g.2.2.2.1)) (dyQ g.2.2.2.2) (ddlE (dyQ g.2.2.2.2))
        (dyQ g.2.2.2.2 + ddlE (dyQ g.2.2.2.2)) 0 := by
      cases pos
      · exact o7
      · exact o6
    obtain ⟨L, hL⟩ : ∃ L, L = |Real.log (dwVal x)| := ⟨_, rfl⟩
    have h1 := abs_sub_abs_le_abs_sub (Real.log (dwVal x)) y0
    rw [abs_sub_comm (Real.log (dwVal x)) y0, ← hL] at h1
    have h1' := abs_sub_abs_le_abs_sub y0 (Real.log (dwVal x))
    rw [← hL] at h1' hE
    have hl1 : ((dyQ g.2.2.2.1 : ℚ) : ℝ) ≤ L := by
      have h4 := (Rat.cast_le (K := ℝ)).mpr o4
      rw [Rat.cast_add, Rat.cast_mul, Rat.cast_add, Rat.cast_one] at h4
      rw [hRa] at ha
      have h5 : (1 + ((ddlE1 : ℚ) : ℝ)) * ((dyQ g.2.2.2.1 : ℚ) : ℝ) ≤ (1 + ((ddlE1 : ℚ) : ℝ)) * L := by
        linarith only [h4, ha, h1', hE]
      exact le_of_mul_le_mul_left h5 (by linarith only [hE1])
    have hhi : |y0| ≤ (((min (dyQ ddlTop0S) ((2 : ℚ) ^ (g.2.2.1 + 1)) : ℚ)) : ℝ) := by
      push_cast
      exact le_min hytop (hyU.le.trans (zpow_le_zpow_right₀ (by norm_num) (by omega)))
    have hl2 : L ≤ ((dyQ g.2.2.2.2 : ℚ) : ℝ) := by
      have h5 := (Rat.cast_le (K := ℝ)).mpr o5
      rw [Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_one] at h5
      have h6 : (1 - ((ddlE1 : ℚ) : ℝ)) * L ≤ (1 - ((ddlE1 : ℚ) : ℝ)) * ((dyQ g.2.2.2.2 : ℚ) : ℝ) := by
        linarith only [h5, h1, hE, hhi]
      exact le_of_mul_le_mul_left h6 (by linarith only [hE1lt])
    have hat := ddl_at0 p hp hk hl1 hl2
    rw [o1 e hg1 hg2] at hat o2
    have hb : |dwVal (dd2R p O (-y0, 0))| ≤ ((ddlE0 : ℚ) : ℝ) + (1 + ((ddlE1 : ℚ) : ℝ)) * L := by
      rw [hRa]
      linarith only [h1', hE]
    rw [hL] at hat hb hE
    have ha0 : (0 : ℚ) ≤ (2 : ℚ) ^ g.2.1 * (1 - 1 / 2 ^ 46) := hk.1.2.2.1
    have hres := ddl_core_both p hp hO S hS x hx hX0 y0 hy0 hE k₁ k₂ hrun.hk hrun.hk2 hr hδ ha0 ha hb pos hpos e eφ et
      ec o2 hrun.hselφ hrun.hselt hrun.hselc hrun.hφex hat
    exact ⟨hres.1, hres.2.trans (le_add_of_nonneg_right hFl0)⟩
  · -- the start's second piece
    have he60 : e ≤ -60 := by omega
    by_cases he118 : -118 ≤ e
    · obtain ⟨o1, -⟩ := ddl0_s
      have h2e : (2 : ℝ) ^ e ≤ dd2U p (dd2R p O (-y0, 0)) := by
        rcases hrun.hsel with ⟨h1, -⟩ | ⟨-, he⟩
        · exact h1
        · omega
      have hlow := dd2U_low p hp hr h2e
      rw [hRa] at hlow
      refine ddl_k0_small_both p hp hO S hS x hx hX0 y0 hy0 hE hEs hrun hr hRa hδ hytop hyU false ddl0S ddl0_s
        (o1 e (by rw [gS1]; exact he118) (by rw [gS2]; exact he60)) (by rw [gS2]; exact he60) ?_
      simp only [Bool.false_eq_true, ↓reduceIte]
      push_cast
      have h6 : (2 : ℝ) ^ ddl0S.2.1 ≤ (2 : ℝ) ^ e := zpow_le_zpow_right₀ (by norm_num) (by rw [gS1]; exact he118)
      have h8 := mul_le_mul_of_nonneg_right h6 (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2 ^ 46)
      linarith only [hlow, h8]
    · have he119 : e ≤ -119 := by omega
      refine ddl_k0_small_both p hp hO S hS x hx hX0 y0 hy0 hE hEs hrun hr hRa hδ hytop hyU true ddl0Last ddl0_last
        (by rw [gL1, ddDeg_small he119]) (by rw [gL2]; exact he119) ?_
      simp only [↓reduceIte, Rat.cast_zero]
      exact abs_nonneg _

/-- `DD::ln` for `k = 0`: within `15.351u²|ln x| + 2^{-1071}`. `r = -y_0`, and the exponent `e` of `U` selects a
group: for `e ≥ -59` on the start's linear piece, otherwise on its second piece -/
theorem ddl_k0 (hp : p = 53) {O : DWOps} (hO : DWSpec p O) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℝ × ℝ) (hx : DW p x) (hX0 : 0 < dwVal x) (hX : |Real.log (dwVal x)| ≤ 7452 / 10) (y0 : ℝ)
    (hy0 : F p y0)
    (hE : |y0 - Real.log (dwVal x)| ≤ ((ddlE0 : ℚ) : ℝ) + ((ddlE1 : ℚ) : ℝ) * |Real.log (dwVal x)|)
    (hEs : |Real.log (dwVal x)| < u p * (1 - u p) / 2 → |y0 - Real.log (dwVal x)| ≤
      |Real.log (dwVal x)| * (u p * (1 + |Real.log (dwVal x)|) + |Real.log (dwVal x)|))
    {k₁ k₂ e eφ et ec : ℤ} (hrun : DDLnSel p O S x y0 k₁ k₂ e eφ et ec) (hk0 : expK p (-y0) = 0) :
    |dwVal (ddLn p O S x y0 k₁ k₂ e eφ et ec) - Real.log (dwVal x)| ≤
      ((ddlEps : ℚ) : ℝ) * |Real.log (dwVal x)| + ((ddlFl : ℚ) : ℝ) :=
  (ddl_k0_both p hp hO S hS x hx hX0 hX y0 hy0 hE hEs hrun hk0).2

/-- `prop44_ln` with both conclusions: under its hypotheses, `DD::ln`'s result is a double word and
`|y - ln x| ≤ 15.351u²|ln x| + 2^{-1071}` -/
theorem prop44_ln_both (hp : p = 53) {O : DWOps} (hO : DWSpec p O) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℝ × ℝ) (hx : DW p x) (hX0 : 0 < dwVal x) (hX : |Real.log (dwVal x)| ≤ 7452 / 10) (w : ℝ)
    (hw0 : |w - x.2 / x.1| ≤ u p * |x.2 / x.1| + (2 : ℝ) ^ (-1075 : ℤ)) (hw1 : x.1 = 1 → w = x.2)
    (k₁ k₂ e eφ et ec : ℤ) (hrun : DDLnSel p O S x (ddLnY0 p x w) k₁ k₂ e eφ et ec) :
    DW p (ddLn p O S x (ddLnY0 p x w) k₁ k₂ e eφ et ec) ∧
      |dwVal (ddLn p O S x (ddLnY0 p x w) k₁ k₂ e eφ et ec) - Real.log (dwVal x)| ≤
        15351 / 1000 * u p ^ 2 * |Real.log (dwVal x)| + (2 : ℝ) ^ (-1071 : ℤ) := by
  obtain ⟨hy0, hE, hEs⟩ := ddl_start p hp x hx hX0 w hw0 hw1
  obtain ⟨t1, t2⟩ := ddl_target p hp |Real.log (dwVal x)|
  rw [← t1, ← t2]
  have hFl0 : (0 : ℝ) ≤ ((ddlFl : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ ddlFl := by unfold ddlFl; positivity
    exact_mod_cast this
  by_cases hk0 : expK p (-ddLnY0 p x w) = 0
  · exact ddl_k0_both p hp hO S hS x hx hX0 hX _ hy0 hE hEs hrun hk0
  · have h := ddl_k1_both p hp hO S hS x hx hX0 hX _ hy0 hE hrun hk0
    exact ⟨h.1, h.2.trans (le_add_of_nonneg_right hFl0)⟩

/-- Proposition 44 (`prop:ddexplog`) for `DD::ln`, at `p = 53` with multidouble's constants and binary64's
subnormals: for a double word `x > 0` with `|ln x| ≤ 745.2`, the start `y_0 = RN(ln_b(x_h) + w)` with `w` the
computed quotient `x_l/x_h`, `k = k₁ + k₂` and `r` from EXP's reduction of `-y_0`, the exponents `e`, `e_φ`, `e_t`
and `e_c` of step (2)'s `U` for `r`, `φ`, `t` and `c` (`-1023` where `U < 2^{-1022}`), the scalings up of the core's `r`
by `2^{-e}` and of the factors of steps (4) and (5) exact, as in Lemma 33, and every other scaling rounded by `S`, that
of `x` in two steps `2^{k₁}` then `2^{k₂}` with `k₂ ≤ 0` and that of step (4)'s product in two steps:
`|y - ln x| ≤ 15.351u²|ln x| + 2^{-1071}`.

What remains assumed: the four published bounds of the double-word operations (`DWSpec`: AccurateDWPlusDW,
DWPlusFP, DWTimesFP3 and DWTimesDW2 return double words within `e_A`, `e_F`, `e_M` and `e_P` of their exact
results); Lemma 41 on double words (`hφex`: `DWPlusFP(x', -1) = x' - 1` exactly, which the relative bound of
DWPlusFP does not give); the rounding rule of a scaling (`hS`: a value is kept, or it is below `2^{-1022}` and is
rounded to a multiple of `2^{-1074}` within `2^{-1075}`); the two properties of the computed quotient `w`, that it
is within `u|x_l/x_h| + 2^{-1075}` of `x_l/x_h` (`hw0`, the paper's statement of its rounding with the loss to the
subnormals) and that `w = x_l` where `x_h = 1` (`hw1`: a quotient by `1` is exact in binary64, as `x_l` is a
float); the range `|ln x| ≤ 745.2` (`hX`), which every positive finite binary64 number meets; and no overflow, the
model having no largest finite value. The floors of the scalings back are not assumed: the kernel checks them for
each case. multidouble's split of `k > 0`, with `k₂ > 0`, gives the value of the split `(k, 0)` (`DDLnSel`).
For binary64 the run must also meet the paper's (A2′): every product, fused multiply-add and quotient returns what it
would with an unbounded exponent range, as in the model, but the quotient `x_l/x_h` of the start, whose error a
hypothesis bounds, and those that only select `k`, an exponent or a branch, which the paper exempts -/
theorem prop44_ln (hp : p = 53) {O : DWOps} (hO : DWSpec p O) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℝ × ℝ) (hx : DW p x) (hX0 : 0 < dwVal x) (hX : |Real.log (dwVal x)| ≤ 7452 / 10) (w : ℝ)
    (hw0 : |w - x.2 / x.1| ≤ u p * |x.2 / x.1| + (2 : ℝ) ^ (-1075 : ℤ)) (hw1 : x.1 = 1 → w = x.2)
    (k₁ k₂ e eφ et ec : ℤ) (hrun : DDLnSel p O S x (ddLnY0 p x w) k₁ k₂ e eφ et ec) :
    |dwVal (ddLn p O S x (ddLnY0 p x w) k₁ k₂ e eφ et ec) - Real.log (dwVal x)| ≤
      15351 / 1000 * u p ^ 2 * |Real.log (dwVal x)| + (2 : ℝ) ^ (-1071 : ℤ) :=
  (prop44_ln_both p hp hO S hS x hx hX0 hX w hw0 hw1 k₁ k₂ e eφ et ec hrun).2

/-- `DD::ln`'s result is a double word, under the hypotheses of `prop44_ln`: both parts are floats and the high
part is the rounded sum, as the octo-double logarithm asks of its start -/
theorem prop44_ln_dw (hp : p = 53) {O : DWOps} (hO : DWSpec p O) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℝ × ℝ) (hx : DW p x) (hX0 : 0 < dwVal x) (hX : |Real.log (dwVal x)| ≤ 7452 / 10) (w : ℝ)
    (hw0 : |w - x.2 / x.1| ≤ u p * |x.2 / x.1| + (2 : ℝ) ^ (-1075 : ℤ)) (hw1 : x.1 = 1 → w = x.2)
    (k₁ k₂ e eφ et ec : ℤ) (hrun : DDLnSel p O S x (ddLnY0 p x w) k₁ k₂ e eφ et ec) :
    DW p (ddLn p O S x (ddLnY0 p x w) k₁ k₂ e eφ et ec) :=
  (prop44_ln_both p hp hO S hS x hx hX0 hX w hw0 hw1 k₁ k₂ e eφ et ec hrun).1

end ExpansionBounds
