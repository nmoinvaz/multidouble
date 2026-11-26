import ExpansionBounds.DDLogSub

/-!
# `DD::ln` returns a double word

Theorem 42 read with `n = 2` bounds `|y - ln x|`; the theorems here add that `y` is a double word, which the
octo-double logarithm asks of its start. `y = DWPlusFP(y_c, y_0)` with `y_0` a float, and step (5) gives `y_c` as a
double word (`dd_log_step5`), so the published DWPlusFP returns one (`dd_thm42_case_g_dw`: the steps of
`dd_thm42_case_g` up to `y_c`, under its hypotheses but `ℓ`). `dd_thm42_case_sub_both` is `dd_thm42_case_sub` with
both conclusions.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) [Prec_gt_0 p]

/-- under the hypotheses of `dd_thm42_case_g` but `ℓ`, `DD::ln`'s result `y = DWPlusFP(y_c, y_0)` is a double
word: `y_c` is one by step (5), and `y_0` is a float -/
theorem dd_thm42_case_g_dw {O : DWOps} (hO : DWSpec p O) (hu : 4 * u p < 1) {η lo ηx lox ηp lop ηc loc : ℝ}
    {S Sx Sp Sc : ℝ × ℝ → ℝ × ℝ} (hS : SclDW p η lo S) (hSx : SclDW p ηx lox Sx) (hSp : SclDW p ηp lop Sp)
    (hSc : SclDW p ηc loc Sc) (x : ℝ × ℝ) (hx : DW p x) (hX0 : 0 < dwVal x) (y0 : ℝ) (hy0 : F p y0) (E : ℝ)
    (hE : |y0 - Real.log (dwVal x)| ≤ E) (r : ℝ × ℝ) (hr : DW p r) (k : ℤ)
    (δ : ℝ) (hδ : |dwVal r - (-y0 - k * Real.log 2)| ≤ δ) (a b : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ |dwVal r|)
    (hb : |dwVal r| ≤ b) (pos : Bool) (hsgn : if pos then 0 ≤ dwVal r else dwVal r ≤ 0) (e : ℤ) (d' : ℕ)
    (hd : 1 ≤ d') (hbd : b < d' + 2) (Fk : ℕ → ℝ × ℝ) (hF : ∀ k, DW p (Fk k)) (φF : ℕ → ℝ)
    (hφF : ∀ k, |dwVal (Fk k) - invF k| ≤ φF k)
    (hlo : d' ≠ 1 → lo * (1 + u p) ≤ a / (1 + a) - ddCoreE p (coreT pos b 0) 0 b φF d')
    (hlox : lox ≤ |(2 : ℝ) ^ k * x.1|) (hφex : dwVal (ddLogPhi O Sx k x) = dwVal (Sx (dwScale k x)) - 1)
    (B eφ et ec : ℤ) (hUφ : |(ddLogPhi O Sx k x).1| + |(ddLogPhi O Sx k x).2| < (2 : ℝ) ^ (eφ + 1))
    (hUt : |(ddExpT O S e r Fk d').1| + |(ddExpT O S e r Fk d').2| < (2 : ℝ) ^ (et + 1))
    (hUc : |(ddLogC O Sp B eφ et (ddLogPhi O Sx k x) (ddExpT O S e r Fk d')).1| +
      |(ddLogC O Sp B eφ et (ddLogPhi O Sx k x) (ddExpT O S e r Fk d')).2| < (2 : ℝ) ^ (ec + 1))
    (F' : ℕ → ℝ × ℝ) (hF' : ∀ k, DW p (F' k)) (φ' : ℕ → ℝ) (hφ' : ∀ k, |dwVal (F' k) - logFe k| ≤ φ' k) (q : ℕ)
    (hq : 2 ≤ q) {tb φb ξ : ℝ} (htbT : coreT pos b 0 ≤ tb) (hφbP : logPhiB (2 * ηx) pos E a b δ ≤ φb)
    (hξX : logXi (2 * ηx) pos E a b δ ≤ ξ) {lφ lt lc lv : ℝ} (hlφ0 : 0 ≤ lφ) (hlc0 : 0 ≤ lc)
    (hfl4 : ¬ min eφ et < -B - 13 → DW p (ddLogPhi O Sx k x) → DW p (ddExpT O S e r Fk d') →
      lφ ≤ |dwVal (ddLogPhi O Sx k x)| ∧ lt ≤ |dwVal (ddExpT O S e r Fk d')| ∧
      lop * (1 + u p) ≤ (1 - eP p) * (lφ * lt))
    (hfl5 : ¬ ec < -B - 13 → DW p (ddLogC O Sp B eφ et (ddLogPhi O Sx k x) (ddExpT O S e r Fk d')) →
      lc ≤ |dwVal (ddLogC O Sp B eφ et (ddLogPhi O Sx k x) (ddExpT O S e r Fk d'))| ∧
      (∀ j, 2 ≤ j → j ≤ q → lv ≤ 1 / (j : ℝ) -
        (Real.exp E - 1 + ddLogEc p (2 * ηx) (2 * ηp) φb tb (ddCoreE p tb η b φF d') E δ b ξ B) *
          logV (Real.exp E - 1 + ddLogEc p (2 * ηx) (2 * ηp) φb tb (ddCoreE p tb η b φF d') E δ b ξ B) q (j + 1) -
        ddHornerB p (Real.exp E - 1 + ddLogEc p (2 * ηx) (2 * ηp) φb tb (ddCoreE p tb η b φF d') E δ b ξ B)
          (2 * ηc) φ'
          (logV (Real.exp E - 1 + ddLogEc p (2 * ηx) (2 * ηp) φb tb (ddCoreE p tb η b φF d') E δ b ξ B) q) q
          (q - j)) ∧
      loc * (1 + u p) ≤ (1 - eP p) * (lc * lv) ∧
      loc * (1 + u p) ≤ (1 - eP p) * (lc * ((1 - eF p) * (1 - ddLogHb p (2 * ηc)
        (Real.exp E - 1 + ddLogEc p (2 * ηx) (2 * ηp) φb tb (ddCoreE p tb η b φF d') E δ b ξ B) φ' q))))
    (hC : Real.exp E - 1 + ddLogEc p (2 * ηx) (2 * ηp) φb tb (ddCoreE p tb η b φF d') E δ b ξ B < 1) :
    DW p (ddLogOp O Sx Sp Sc y0 x k (ddExpT O S e r Fk d') B eφ et ec F' q) := by
  have h1eP : 0 ≤ 1 - eP p := by linarith only [eP_le_one p hu]
  -- Lemma 39
  obtain ⟨c1', c2, c3'⟩ := dd_core p hO hu hS r hr a b ha0 ha hb e d' hd hbd Fk hF φF hφF pos hsgn hlo
  have c1 := c1'.trans (ddCoreE_mono p hu htbT η b φF d')
  have c3 := c3'.trans htbT
  obtain ⟨R, hR⟩ : ∃ R, R = dwVal r := ⟨_, rfl⟩
  rw [← hR] at hδ ha hb hsgn c1 c3
  obtain ⟨t, htd⟩ : ∃ t, t = ddExpT O S e r Fk d' := ⟨_, rfl⟩
  rw [← htd] at c1 c2 hUt hUc hfl4 hfl5 ⊢
  obtain ⟨Em, hEm⟩ : ∃ Em, Em = ddCoreE p tb η b φF d' := ⟨_, rfl⟩
  rw [← hEm] at c1 hfl5 hC
  -- `2^k x = e^{-e_0 - r_e}` with `e_0 = y_0 - ln x` and `r_e = -y_0 - k ln 2`
  obtain ⟨X, hXd⟩ : ∃ X, X = dwVal x := ⟨_, rfl⟩
  rw [← hXd] at hX0 hE
  obtain ⟨e0, he0d⟩ : ∃ e0, e0 = y0 - Real.log X := ⟨_, rfl⟩
  obtain ⟨re, hred⟩ : ∃ re, re = -y0 - k * Real.log 2 := ⟨_, rfl⟩
  rw [← he0d] at hE
  rw [← hred] at hδ
  have hX' : (2 : ℝ) ^ k * dwVal x = Real.exp (-e0 - re) := by
    rw [← hXd, he0d, hred, show -(y0 - Real.log X) - (-y0 - k * Real.log 2) = Real.log X + k * Real.log 2 by ring,
      Real.exp_add, Real.exp_log hX0, exp_int_mul_log_two, mul_comm]
  -- step (3)
  obtain ⟨s1, s2, s3', s4'⟩ := dd_log_step3 p hO hSx x hx k hlox hφex pos hX' hE hδ ha hb hsgn
  have s3 := s3'.trans hξX
  have s4 := s4'.trans hφbP
  obtain ⟨φ, hφd⟩ : ∃ φ, φ = ddLogPhi O Sx k x := ⟨_, rfl⟩
  rw [← hφd] at s1 s2 s3 s4 hUφ hUc hfl4 hfl5
  -- step (4)
  obtain ⟨x1, x2, x3⟩ := log_c_exact hδ hE hb s2 s3 c1 c3
  have htbT' : |dwVal t| ≤ tb + Em := by
    have := abs_sub_abs_le_abs_sub (dwVal t) (Real.exp R - 1)
    linarith only [this, c1, c3]
  obtain ⟨d1, d2⟩ := dd_log_step4 p hO hu hSp φ t s1 c2 s4 htbT' x3 x2 x1 B eφ et hUφ hUt (fun h => by
    obtain ⟨f1, f2, f3⟩ := hfl4 h s1 c2
    exact f3.trans (mul_le_mul_of_nonneg_left (mul_le_abs_mul hlφ0 f1 f2) h1eP))
  obtain ⟨c, hcd⟩ : ∃ c, c = ddLogC O Sp B eφ et φ t := ⟨_, rfl⟩
  rw [← hcd] at d1 d2 hUc hfl5
  obtain ⟨Ec, hEcd⟩ : ∃ Ec, Ec = ddLogEc p (2 * ηx) (2 * ηp) φb tb Em E δ b ξ B := ⟨_, rfl⟩
  rw [← hEcd] at hfl5 hC
  have hEc : |dwVal c - (Real.exp (-e0) - 1)| ≤ Ec := by
    refine d2.trans (le_of_eq ?_)
    rw [hEcd]
    unfold ddLogEc
    ring
  -- step (5), and the last DWPlusFP
  obtain ⟨g1, -⟩ := dd_log_step5 p hO hu hSc c d1 x1 hEc hC F' hF' φ' hφ' q hq B ec hUc hlc0
    (fun h => hfl5 h d1)
  have hres : ddLogOp O Sx Sp Sc y0 x k t B eφ et ec F' q = O.addF (ddLogYc O Sc B ec c F' q) y0 := by
    rw [hcd, hφd]
    rfl
  rw [hres]
  exact hO.addF_dw _ y0 g1 hy0

/-- `dd_thm42_case_sub` with both conclusions: under its hypotheses, `DD::ln`'s result is a double word and
`|y - ln x| ≤ 𝓔(ℓ)` -/
theorem dd_thm42_case_sub_both (hp : p = 53) {O : DWOps} (hO : DWSpec p O) (S : ℝ → ℝ)
    (hS : ∀ v, S v = v ∨ (Mult (-1074) (S v) ∧ |v| < (2 : ℝ) ^ (-1022 : ℤ) ∧ |S v - v| ≤ (2 : ℝ) ^ (-1075 : ℤ)))
    (x : ℝ × ℝ) (hx : DW p x) (hX0 : 0 < dwVal x) (y0 : ℝ) (hy0 : F p y0) (ℓ E : ℝ) (hℓ : |Real.log (dwVal x)| ≤ ℓ)
    (hE : |y0 - Real.log (dwVal x)| ≤ E) (r : ℝ × ℝ) (hr : DW p r) (k₁ k₂ : ℤ) (hk2 : k₂ ≤ 0) (δ : ℝ) (hδ : |dwVal r -
    (-y0 - (k₁ + k₂ : ℤ) * Real.log 2)| ≤ δ) (a b : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ |dwVal r|) (hb : |dwVal r| ≤ b) (pos :
    Bool) (hsgn : if pos then 0 ≤ dwVal r else dwVal r ≤ 0) (e : ℤ) (d' : ℕ) (hd : 1 ≤ d') (hbd : b < d' + 2) (Fk : ℕ
    → ℝ × ℝ) (hF : ∀ k, DW p (Fk k)) (φF : ℕ → ℝ) (hφF : ∀ k, |dwVal (Fk k) - invF k| ≤ φF k) (hlo : d' ≠ 1 → (2 : ℝ)
    ^ (-967 : ℤ) * (1 + u p) ≤ a / (1 + a) - ddCoreE p (coreT pos b 0) 0 b φF d') (hlox : (2 : ℝ) ^ (-967 : ℤ) ≤ |(2 :
    ℝ) ^ (k₁ + k₂) * x.1|) (hφex : dwVal (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) = dwVal (ddS2 S k₂ (dwScale (k₁ + k₂)
    x)) - 1) (B eφ et ec : ℤ) (het : et ≤ 0) (hUφ : |(ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x).1| + |(ddLogPhi O (ddS2 S
    k₂) (k₁ + k₂) x).2| < (2 : ℝ) ^ (eφ + 1)) (hUt : |(ddExpT O (fun v => (S v.1, S v.2)) e r Fk d').1| + |(ddExpT O
    (fun v => (S v.1, S v.2)) e r Fk d').2| < (2 : ℝ) ^ (et + 1)) (hUc : |(ddLogC O (ddS2 S et) B eφ et (ddLogPhi O
    (ddS2 S k₂) (k₁ + k₂) x) (ddExpT O (fun v => (S v.1, S v.2)) e r Fk d')).1| + |(ddLogC O (ddS2 S et) B eφ et
    (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) (ddExpT O (fun v => (S v.1, S v.2)) e r Fk d')).2| < (2 : ℝ) ^ (ec + 1)) (F'
    : ℕ → ℝ × ℝ) (hF' : ∀ k, DW p (F' k)) (φ' : ℕ → ℝ) (hφ' : ∀ k, |dwVal (F' k) - logFe k| ≤ φ' k) (q : ℕ) (hq : 2 ≤
    q) {tb φb ξ : ℝ} (htbT : coreT pos b 0 ≤ tb) (hφbP : logPhiB (2 * (2 * (2 : ℝ) ^ (-1075 : ℤ))) pos E a b δ ≤ φb)
    (hξX : logXi (2 * (2 * (2 : ℝ) ^ (-1075 : ℤ))) pos E a b δ ≤ ξ) {lφ lt lc lv : ℝ} (hlφ0 : 0 ≤ lφ) (hlc0 : 0 ≤ lc)
    (hfl4 : ¬ min eφ et < -B - 13 → DW p (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) → DW p (ddExpT O (fun v => (S v.1, S
    v.2)) e r Fk d') → lφ ≤ |dwVal (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x)| ∧ lt ≤ |dwVal (ddExpT O (fun v => (S v.1, S
    v.2)) e r Fk d')| ∧ (2 : ℝ) ^ (-967 : ℤ) * (1 + u p) ≤ (1 - eP p) * (lφ * lt)) (hfl5 : ¬ ec < -B - 13 → DW p
    (ddLogC O (ddS2 S et) B eφ et (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) (ddExpT O (fun v => (S v.1, S v.2)) e r Fk d'))
    → lc ≤ |dwVal (ddLogC O (ddS2 S et) B eφ et (ddLogPhi O (ddS2 S k₂) (k₁ + k₂) x) (ddExpT O (fun v => (S v.1, S
    v.2)) e r Fk d'))| ∧ (∀ j, 2 ≤ j → j ≤ q → lv ≤ 1 / (j : ℝ) - (Real.exp E - 1 + ddLogEc p (2 * (2 * (2 : ℝ) ^
    (-1075 : ℤ))) (2 * (2 * (2 : ℝ) ^ (-1075 : ℤ))) φb tb (ddCoreE p tb ((2 : ℝ) ^ (-1075 : ℤ)) b φF d') E δ b ξ B) *
    logV (Real.exp E - 1 + ddLogEc p (2 * (2 * (2 : ℝ) ^ (-1075 : ℤ))) (2 * (2 * (2 : ℝ) ^ (-1075 : ℤ))) φb tb
    (ddCoreE p tb ((2 : ℝ) ^ (-1075 : ℤ)) b φF d') E δ b ξ B) q (j + 1) - ddHornerB p (Real.exp E - 1 + ddLogEc p (2 *
    (2 * (2 : ℝ) ^ (-1075 : ℤ))) (2 * (2 * (2 : ℝ) ^ (-1075 : ℤ))) φb tb (ddCoreE p tb ((2 : ℝ) ^ (-1075 : ℤ)) b φF
    d') E δ b ξ B) (2 * (2 : ℝ) ^ (-1075 : ℤ)) φ' (logV (Real.exp E - 1 + ddLogEc p (2 * (2 * (2 : ℝ) ^ (-1075 : ℤ)))
    (2 * (2 * (2 : ℝ) ^ (-1075 : ℤ))) φb tb (ddCoreE p tb ((2 : ℝ) ^ (-1075 : ℤ)) b φF d') E δ b ξ B) q) q (q - j)) ∧
    (2 : ℝ) ^ (-967 : ℤ) * (1 + u p) ≤ (1 - eP p) * (lc * lv) ∧ (2 : ℝ) ^ (-967 : ℤ) * (1 + u p) ≤ (1 - eP p) * (lc *
    ((1 - eF p) * (1 - ddLogHb p (2 * (2 : ℝ) ^ (-1075 : ℤ)) (Real.exp E - 1 + ddLogEc p (2 * (2 * (2 : ℝ) ^ (-1075 :
    ℤ))) (2 * (2 * (2 : ℝ) ^ (-1075 : ℤ))) φb tb (ddCoreE p tb ((2 : ℝ) ^ (-1075 : ℤ)) b φF d') E δ b ξ B) φ' q))))
    (hC : Real.exp E - 1 + ddLogEc p (2 * (2 * (2 : ℝ) ^ (-1075 : ℤ))) (2 * (2 * (2 : ℝ) ^ (-1075 : ℤ))) φb tb
    (ddCoreE p tb ((2 : ℝ) ^ (-1075 : ℤ)) b φF d') E δ b ξ B < 1) :
    DW p (ddLogOp O (ddS2 S k₂) (ddS2 S et) (fun v => (S v.1, S v.2)) y0 x (k₁ + k₂) (ddExpT O (fun v => (S v.1, S
    v.2)) e r Fk d') B eφ et ec F' q) ∧ |dwVal (ddLogOp O (ddS2 S k₂) (ddS2 S et) (fun v => (S v.1, S v.2)) y0 x
    (k₁ + k₂) (ddExpT O (fun v => (S v.1, S v.2)) e r Fk d') B eφ et ec F' q) - Real.log (dwVal x)| ≤ ddLogBoundG p
    ((2 : ℝ) ^ (-1075 : ℤ)) (2 * (2 : ℝ) ^ (-1075 : ℤ)) (2 * (2 : ℝ) ^ (-1075 : ℤ)) ((2 : ℝ) ^ (-1075 : ℤ)) ℓ E tb
    φb ξ b δ φF d' φ' q B := by
  have hu : 4 * u p < 1 := by
    unfold u
    rw [hp]
    norm_num
  exact ⟨dd_thm42_case_g_dw p hO hu (SclDW.of_grid p hp S hS) (SclDW.two_step p hp S hS hk2)
      (SclDW.two_step p hp S hS het) (SclDW.of_grid p hp S hS) x hx hX0 y0 hy0 E hE r hr (k₁ + k₂) δ hδ a b ha0
      ha hb pos hsgn e d' hd hbd Fk hF φF hφF hlo hlox hφex B eφ et ec hUφ hUt hUc F' hF' φ' hφ' q hq htbT hφbP
      hξX hlφ0 hlc0 hfl4 hfl5 hC,
    dd_thm42_case_sub p hp hO S hS x hx hX0 y0 hy0 ℓ E hℓ hE r hr k₁ k₂ hk2 δ hδ a b ha0 ha hb pos hsgn e d' hd
      hbd Fk hF φF hφF hlo hlox hφex B eφ et ec het hUφ hUt hUc F' hF' φ' hφ' q hq htbT hφbP hξX hlφ0 hlc0 hfl4
      hfl5 hC⟩

end ExpansionBounds
