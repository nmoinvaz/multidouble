import ExpansionBounds.DDHorner
import ExpansionBounds.ExpThm

/-!
# Proposition 44 (`prop:ddexplog`): the core of `DD::exp`

Lemma 39 (`lem:core`) read with `n = 2`, with no part bounds and each `G_OP`'s error replaced by `e_OP Z̄`, and with
`m = 0`: `DD::exp` runs EXP with `s = 1`, and `|r| < 1/2` leaves no squaring. For a double word `r` with
`a ≤ |r| ≤ b` and degree `d'`, step (3) is `t = r` for `d' = 1`, and otherwise `q = p_2` by Horner's rule on the
double words `F_j` of `1/j!`, `w = MUL(r, q)`, `r̂ = 2^{-e} r` and `t = 2^e ADD(r̂, MUL(r̂, w))`. With `e_2` of Horner's
rule and `v_2 = ∑_{i ≥ 2} b^{i-2}/i!`,

  `ε' = e_P b(v_2 + e_2)`, `ε'' = e_P b(b(v_2 + e_2) + ε')`, `E^- = ε'' + b(ε' + b e_2) + E^tr_{d'}`,
  `E_0 = E^- + e_A(t̄_0 + E^-) + 2η_0`,

the `E` of `Exp.core` in `explog_consts.py` for double words at `m = 0`, before its roundings up; for `d' = 1`,
`E_0 = E^tr_1`. The bound has `b` where the lemma has `min(b, 2^{e+1})`, which is not larger.

The scaling back by `2^e` is rounded by a function that moves each part by at most `η` (`SclDW`). The next operation's
bound needs a double word, and a low part rounded on the subnormal grid leaves one only if the high part is far enough
above that grid: `SclDW` keeps a double word whose high part is at least `lo`, and the core asks
`lo(1 + u) ≤ a/(1 + a) - (E^- + e_A(t̄_0 + E^-))`, a bound below on `|t_h|` from `|e^r - 1| ≥ a/(1 + a)`.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ)

/-- a rounded scaling of double words: each part within `η`, and a double word whose high part is at least `lo` in
magnitude stays one -/
structure SclDW (η lo : ℝ) (S : ℝ × ℝ → ℝ × ℝ) : Prop where
  err₁ : ∀ v, |(S v).1 - v.1| ≤ η
  err₂ : ∀ v, |(S v).2 - v.2| ≤ η
  dw : ∀ v, DW p v → lo ≤ |v.1| → DW p (S v)

/-- `2^k x`, part by part -/
noncomputable def dwScale (k : ℤ) (x : ℝ × ℝ) : ℝ × ℝ := ((2 : ℝ) ^ k * x.1, (2 : ℝ) ^ k * x.2)

/-- the value of `2^k x` -/
theorem dwVal_dwScale (k : ℤ) (x : ℝ × ℝ) : dwVal (dwScale k x) = (2 : ℝ) ^ k * dwVal x := by
  simp only [dwVal, dwScale]
  ring

/-- step (3) on double words: `t = r` for `d' = 1`; otherwise `q = p_2` by Horner's rule on the `F_j`,
`w = MUL(r, q)`, `r̂ = 2^{-e} r` and `t = 2^e ADD(r̂, MUL(r̂, w))`, the scaling back rounded by `S` -/
noncomputable def ddExpT (O : DWOps) (S : ℝ × ℝ → ℝ × ℝ) (e : ℤ) (r : ℝ × ℝ) (Fk : ℕ → ℝ × ℝ) (d' : ℕ) : ℝ × ℝ :=
  if d' = 1 then r else
    S (dwScale e (O.add (dwScale (-e) r)
      (O.mul (dwScale (-e) r) (O.mul r (ddHornerP O (O.mul r) Fk d' (d' - 2))))))

/-- `E_0` read with `n = 2` and `m = 0`, for `t̄_0 = T0` and the scaling back within `η` a part: `E^tr_1` for
`d' = 1`; otherwise `ε' = e_P b(v_2 + e_2)`, `E^- = e_P b(b(v_2 + e_2) + ε') + b(ε' + b e_2) + E^tr_{d'}` and
`E_0 = E^- + e_A(T0 + E^-) + 2η` -/
noncomputable def ddCoreE (T0 η b : ℝ) (φ : ℕ → ℝ) (d' : ℕ) : ℝ :=
  if d' = 1 then eTr b 1 else
    let e2 := ddHornerB p b 0 φ (coreV b d') d' (d' - 2)
    let Zw := b * (coreV b d' 2 + e2)
    let ε1 := eP p * Zw
    let Em := eP p * (b * (Zw + ε1)) + b * (ε1 + b * e2) + eTr b d'
    Em + eA p * (T0 + Em) + 2 * η

/-- `η ≥ 0` -/
theorem SclDW.nonneg {η lo : ℝ} {S : ℝ × ℝ → ℝ × ℝ} (h : SclDW p η lo S) : 0 ≤ η :=
  (abs_nonneg _).trans (h.err₁ 0)

/-- a rounded scaling moves the value by at most `2η` -/
theorem SclDW.val {η lo : ℝ} {S : ℝ × ℝ → ℝ × ℝ} (h : SclDW p η lo S) (v : ℝ × ℝ) :
    |dwVal (S v) - dwVal v| ≤ 2 * η := by
  have h1 := h.err₁ v
  have h2 := h.err₂ v
  calc |dwVal (S v) - dwVal v| = |((S v).1 - v.1) + ((S v).2 - v.2)| := by simp only [dwVal]; ring_nf
    _ ≤ |(S v).1 - v.1| + |(S v).2 - v.2| := abs_add_le _ _
    _ ≤ 2 * η := by linarith

/-- `|e^R - 1| ≥ a/(1 + a)` for `|R| ≥ a ≥ 0` -/
theorem abs_exp_sub_one_ge {R a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ |R|) : a / (1 + a) ≤ |Real.exp R - 1| := by
  have hR0 := abs_nonneg R
  have h1 : a / (1 + a) ≤ |R| / (1 + |R|) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  refine h1.trans ?_
  rcases le_total 0 R with h | h
  · rw [abs_of_nonneg h]
    have h2 := Real.add_one_le_exp R
    rw [abs_of_nonneg (by linarith), div_le_iff₀ (by linarith)]
    nlinarith
  · rw [abs_of_nonpos h]
    have h2 := Real.add_one_le_exp (-R)
    have h3 : Real.exp R ≤ 1 := Real.exp_le_one_iff.mpr h
    have h4 : Real.exp R * Real.exp (-R) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h5 := Real.exp_pos R
    rw [abs_of_nonpos (by linarith), div_le_iff₀ (by linarith)]
    nlinarith

/-- `|s x| ≤ B|s y|` from `|x| ≤ B|y|`, for `s ≥ 0` -/
theorem abs_scale_le {s x y B : ℝ} (hs : 0 ≤ s) (h : |x| ≤ B * |y|) : |s * x| ≤ B * |s * y| := by
  rw [abs_mul, abs_mul, abs_of_nonneg hs]
  calc s * |x| ≤ s * (B * |y|) := mul_le_mul_of_nonneg_left h hs
    _ = B * (s * |y|) := by ring

/-- step (3)'s errors on real numbers: with `|R| ≤ b`, `q` within `e_2` of `q*`, `|q*| ≤ v_2`, `w` and `Y` products
within `c_P`, relatively, of `Rq` and `Rw`, `Th` a sum within `c_A` of `R + Y`, and `R + R²q*` within `tr` of `X`,
`|X| ≤ T0`: `|Th - X| ≤ E^- + c_A(T0 + E^-)` -/
theorem dd_core_real {cP cA R q qs w Y Th b v2 e2 tr T0 X : ℝ} (hcP : 0 ≤ cP) (hcA : 0 ≤ cA) (hR : |R| ≤ b)
    (hqs : |qs| ≤ v2) (hq : |q - qs| ≤ e2) (hw : |w - R * q| ≤ cP * |R * q|) (hY : |Y - R * w| ≤ cP * |R * w|)
    (hTh : |Th - (R + Y)| ≤ cA * |R + Y|) (htr : |R + R ^ 2 * qs - X| ≤ tr) (hT0 : |X| ≤ T0) {Zw ε1 Em : ℝ}
    (hZw : Zw = b * (v2 + e2)) (hε1 : ε1 = cP * Zw)
    (hEm : Em = cP * (b * (Zw + ε1)) + b * (ε1 + b * e2) + tr) :
    |Th - X| ≤ Em + cA * (T0 + Em) := by
  have hb0 : 0 ≤ b := (abs_nonneg _).trans hR
  have hqb : |q| ≤ v2 + e2 := by
    calc |q| = |qs + (q - qs)| := by ring_nf
      _ ≤ |qs| + |q - qs| := abs_add_le _ _
      _ ≤ v2 + e2 := add_le_add hqs hq
  have hRq : |R * q| ≤ Zw := by
    rw [hZw, abs_mul]
    exact mul_le_mul hR hqb (abs_nonneg _) hb0
  have hw1 : |w - R * q| ≤ ε1 := by
    rw [hε1]
    exact hw.trans (mul_le_mul_of_nonneg_left hRq hcP)
  have hwb : |w| ≤ Zw + ε1 := by
    calc |w| = |R * q + (w - R * q)| := by ring_nf
      _ ≤ |R * q| + |w - R * q| := abs_add_le _ _
      _ ≤ Zw + ε1 := add_le_add hRq hw1
  have hRw : |R * w| ≤ b * (Zw + ε1) := by
    rw [abs_mul]
    exact mul_le_mul hR hwb (abs_nonneg _) hb0
  have hY1 : |Y - R * w| ≤ cP * (b * (Zw + ε1)) := hY.trans (mul_le_mul_of_nonneg_left hRw hcP)
  have h3 : |R * (w - R * q)| ≤ b * ε1 := by
    rw [abs_mul]
    exact mul_le_mul hR hw1 (abs_nonneg _) hb0
  have h4 : |R * (R * (q - qs))| ≤ b * (b * e2) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul hR (mul_le_mul hR hq (abs_nonneg _) hb0) (by positivity) hb0
  have hS : |R + Y - X| ≤ Em := by
    rw [hEm, show R + Y - X = (Y - R * w) + R * (w - R * q) + R * (R * (q - qs)) + (R + R ^ 2 * qs - X) by ring]
    calc _ ≤ |Y - R * w| + |R * (w - R * q)| + |R * (R * (q - qs))| + |R + R ^ 2 * qs - X| :=
          (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ cP * (b * (Zw + ε1)) + b * ε1 + b * (b * e2) + tr := add_le_add (add_le_add (add_le_add hY1 h3) h4) htr
      _ = _ := by ring
  have hSb : |R + Y| ≤ T0 + Em := by
    calc |R + Y| = |X + (R + Y - X)| := by ring_nf
      _ ≤ |X| + |R + Y - X| := abs_add_le _ _
      _ ≤ T0 + Em := add_le_add hT0 hS
  calc |Th - X| = |(R + Y - X) + (Th - (R + Y))| := by ring_nf
    _ ≤ |R + Y - X| + |Th - (R + Y)| := abs_add_le _ _
    _ ≤ Em + cA * (T0 + Em) := add_le_add hS (hTh.trans (mul_le_mul_of_nonneg_left hSb hcA))

variable [Prec_gt_0 p]

/-- a scaling by a power of two keeps a double word -/
theorem DW.dwScale {x : ℝ × ℝ} (hx : DW p x) (k : ℤ) : DW p (dwScale k x) := DW.scale p hx k

/-- Lemma 39 (`lem:core`) read with `n = 2` and `m = 0`: for a double word `r` with `a ≤ |r| ≤ b` and the case's
sign, step (3) with degree `d'` gives a double word `t` with `|t - (e^r - 1)| ≤ E_0`, and `|e^r - 1| ≤ t̄_0`. The
scaling back by `2^e` moves each part by at most `η` and keeps a double word whose high part is at least `lo` -/
theorem dd_core {O : DWOps} (hO : DWSpec p O) (hu : 4 * u p < 1) {η lo : ℝ} {S : ℝ × ℝ → ℝ × ℝ}
    (hS : SclDW p η lo S) (r : ℝ × ℝ) (hr : DW p r) (a b : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ |dwVal r|)
    (hb : |dwVal r| ≤ b) (e : ℤ) (d' : ℕ) (hd : 1 ≤ d') (hbd : b < d' + 2) (Fk : ℕ → ℝ × ℝ)
    (hF : ∀ k, DW p (Fk k)) (φ : ℕ → ℝ) (hφ : ∀ k, |dwVal (Fk k) - invF k| ≤ φ k) (pos : Bool)
    (hsgn : if pos then 0 ≤ dwVal r else dwVal r ≤ 0)
    (hlo : d' ≠ 1 → lo * (1 + u p) ≤ a / (1 + a) - ddCoreE p (coreT pos b 0) 0 b φ d') :
    |dwVal (ddExpT O S e r Fk d') - (Real.exp (dwVal r) - 1)| ≤ ddCoreE p (coreT pos b 0) η b φ d' ∧
      DW p (ddExpT O S e r Fk d') ∧ |Real.exp (dwVal r) - 1| ≤ coreT pos b 0 := by
  have hu0 := u_pos p
  obtain ⟨R, hR⟩ : ∃ R, R = dwVal r := ⟨_, rfl⟩
  rw [← hR] at ha hb hsgn ⊢
  have hT := (tstar_bound pos R a b hb ha hsgn 0).1
  rw [pow_zero, one_mul] at hT
  rcases eq_or_lt_of_le hd with h1 | h2
  · -- `d' = 1`: `t = r`
    subst h1
    simp only [ddExpT, ddCoreE, ↓reduceIte]
    refine ⟨?_, hr, hT⟩
    rw [← hR]
    have h := eTr_bound R b hb 1 (by exact_mod_cast hbd)
    have hs : ∑ i ∈ range (1 + 1), R ^ i / (i.factorial : ℝ) = 1 + R := by
      rw [sum_range_succ, sum_range_one]
      simp
    rw [hs] at h
    rw [show R - (Real.exp R - 1) = -(Real.exp R - (1 + R)) by ring, abs_neg]
    exact h
  have hd1 : d' ≠ 1 := by omega
  have hd2 : 2 ≤ d' := h2
  have heA := eA_nonneg p hu
  have heP := eP_nonneg p
  -- `q = p_2` by Horner's rule, with `z = r` and `z̄ = b`
  have hv : ∀ k, 2 ≤ k → k ≤ d' → |hornerE invF R d' k| ≤ coreV b d' k := fun k _ _ => by
    unfold hornerE coreV
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l _ => ?_)
    have hi : 0 ≤ invF (k + l) := by unfold invF; positivity
    rw [abs_mul, abs_of_nonneg hi, abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hb l) hi
  have hM : ∀ q, DW p q → True →
      DW p (O.mul r q) ∧ |dwVal (O.mul r q) - R * dwVal q| ≤ eP p * |R * dwVal q| + 0 := fun q hq _ =>
    ⟨hO.mul_dw r q hr hq, by rw [add_zero, hR]; exact hO.mul_err r q hr hq⟩
  obtain ⟨q1, q2⟩ := dd_horner_step p hO hu hb hM Fk hF invF φ (coreV b d') hφ d' 2 hv (d' - 2) le_rfl
    (fun _ _ => trivial)
  rw [show d' - (d' - 2) = 2 by omega] at q1
  obtain ⟨q, hq⟩ : ∃ q, q = ddHornerP O (O.mul r) Fk d' (d' - 2) := ⟨_, rfl⟩
  obtain ⟨e2, he2⟩ : ∃ e2, e2 = ddHornerB p b 0 φ (coreV b d') d' (d' - 2) := ⟨_, rfl⟩
  rw [← hq, ← he2] at q1
  rw [← hq] at q2
  -- `w = MUL(r, q)`, `r̂ = 2^{-e} r`, `y = MUL(r̂, w)` and `t̂ = ADD(r̂, y)`
  obtain ⟨w, hw⟩ : ∃ w, w = O.mul r q := ⟨_, rfl⟩
  have hwdw : DW p w := hw ▸ hO.mul_dw r q hr q2
  have hw1 : |dwVal w - R * dwVal q| ≤ eP p * |R * dwVal q| := by
    rw [hw, hR]
    exact hO.mul_err r q hr q2
  obtain ⟨rh, hrh⟩ : ∃ rh, rh = dwScale (-e) r := ⟨_, rfl⟩
  have hrhdw : DW p rh := hrh ▸ DW.dwScale p hr (-e)
  have hrhv : dwVal rh = (2 : ℝ) ^ (-e) * R := by rw [hrh, dwVal_dwScale, hR]
  obtain ⟨y, hy⟩ : ∃ y, y = O.mul rh w := ⟨_, rfl⟩
  have hydw : DW p y := hy ▸ hO.mul_dw rh w hrhdw hwdw
  obtain ⟨th, hth⟩ : ∃ th, th = O.add rh y := ⟨_, rfl⟩
  have hthdw : DW p th := hth ▸ hO.add_dw rh y hrhdw hydw
  have hs0 : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  have hsc : (2 : ℝ) ^ e * (2 : ℝ) ^ (-e) = 1 := by rw [← zpow_add₀ two_ne_zero, add_neg_cancel, zpow_zero]
  have hy1 : |(2 : ℝ) ^ e * dwVal y - R * dwVal w| ≤ eP p * |R * dwVal w| := by
    have h := abs_scale_le hs0.le (hO.mul_err rh w hrhdw hwdw)
    rw [← hy, hrhv] at h
    rwa [show (2 : ℝ) ^ e * (dwVal y - (2 : ℝ) ^ (-e) * R * dwVal w) = (2 : ℝ) ^ e * dwVal y - R * dwVal w by
        linear_combination (-(R * dwVal w)) * hsc,
      show (2 : ℝ) ^ e * ((2 : ℝ) ^ (-e) * R * dwVal w) = R * dwVal w by
        linear_combination (R * dwVal w) * hsc] at h
  have hth1 : |(2 : ℝ) ^ e * dwVal th - (R + (2 : ℝ) ^ e * dwVal y)| ≤ eA p * |R + (2 : ℝ) ^ e * dwVal y| := by
    have h := abs_scale_le hs0.le (hO.add_err rh y hrhdw hydw)
    rw [← hth, hrhv] at h
    rwa [show (2 : ℝ) ^ e * (dwVal th - ((2 : ℝ) ^ (-e) * R + dwVal y)) =
          (2 : ℝ) ^ e * dwVal th - (R + (2 : ℝ) ^ e * dwVal y) by linear_combination (-R) * hsc,
      show (2 : ℝ) ^ e * ((2 : ℝ) ^ (-e) * R + dwVal y) = R + (2 : ℝ) ^ e * dwVal y by
        linear_combination R * hsc] at h
  -- the series: `r + r²q*_2` within `E^tr` of `e^r - 1`
  have htr : |R + R ^ 2 * hornerE invF R d' 2 - (Real.exp R - 1)| ≤ eTr b d' := by
    have h := eTr_bound R b hb d' hbd
    rw [exp_horner R d' hd2, show ∑ i ∈ range (d' + 1), R ^ i / (i.factorial : ℝ) - 1 - (Real.exp R - 1) =
      -(Real.exp R - ∑ i ∈ range (d' + 1), R ^ i / (i.factorial : ℝ)) by ring, abs_neg]
    exact h
  obtain ⟨V, hV⟩ : ∃ V, V = dwScale e th := ⟨_, rfl⟩
  have hVdw : DW p V := hV ▸ DW.dwScale p hthdw e
  have hVv : dwVal V = (2 : ℝ) ^ e * dwVal th := by rw [hV, dwVal_dwScale]
  have key := dd_core_real heP heA hb (hv 2 le_rfl hd2) q1 hw1 hy1 hth1 htr hT rfl rfl rfl
  rw [← hVv] at key
  have ht : ddExpT O S e r Fk d' = S V := by
    simp only [ddExpT, hd1, ↓reduceIte, hV, hth, hy, hw, hrh, hq]
  have hlo' := hlo hd1
  simp only [ddCoreE, hd1, ↓reduceIte, ← he2] at hlo' ⊢
  rw [ht]
  have hSv := hS.val p V
  refine ⟨?_, hS.dw V hVdw ?_, hT⟩
  · calc |dwVal (S V) - (Real.exp R - 1)| = |(dwVal V - (Real.exp R - 1)) + (dwVal (S V) - dwVal V)| := by ring_nf
      _ ≤ |dwVal V - (Real.exp R - 1)| + |dwVal (S V) - dwVal V| := abs_add_le _ _
      _ ≤ _ := by linarith
  · -- `|V_h|(1 + u) ≥ |V| ≥ |e^r - 1| - E_0 ≥ lo(1 + u)`
    have h1 := abs_exp_sub_one_ge ha0 ha
    have h2 := abs_sub_abs_le_abs_sub (Real.exp R - 1) (dwVal V)
    rw [abs_sub_comm (Real.exp R - 1) (dwVal V)] at h2
    have h3 : |dwVal V| ≤ (1 + u p) * |V.1| := by
      have h4 := (DW.parts p hVdw).1
      calc |dwVal V| ≤ |V.1| + |V.2| := abs_add_le _ _
        _ ≤ (1 + u p) * |V.1| := by linarith
    refine le_of_mul_le_mul_right ?_ (by linarith : (0 : ℝ) < 1 + u p)
    linarith

end ExpansionBounds
