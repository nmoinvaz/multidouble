import ExpansionBounds.DDLogThm
import ExpansionBounds.Convex

/-!
# Proposition 44 (`prop:ddexplog`): `DD::ln`'s bound is convex in `ℓ`

The paragraph "Convexity" of Theorem 42's proof, read with `n = 2`. For a fixed case the bound is evaluated with
`t̄ = b` for `r ≤ 0`, larger than `1 - e^{-b}`, and `φ̄ = max(ξ - 1, E + b + δ + 2nη_0)`, larger than the theorem's
(`ddTbC`, `ddPhiC`, `ddLogBoundC`): this is the convex mode of `Log.bin` in `explog_consts.py`, which `dd_log` runs.
With the start's error `E`, the reduction's `δ` and the bound `b` of `|r|` nonnegative, nondecreasing and convex in
`ℓ` on a set `s` of nonnegative numbers, and `C < 1` and `b < d' + 2` on `s`, the bound is nonnegative, nondecreasing
and convex in `ℓ` on `s` (`cvx_ddLogBoundC`): each quantity is built by the operations of `Convex.lean`, Horner's
bounds by induction (`cvx_ddHornerB`).
-/

namespace ExpansionBounds

open Set

variable (p : ℤ)

/-- `t̄` in convex mode: `e^b - 1` for `r ≥ 0` and `b` for `r ≤ 0` -/
noncomputable def ddTbC (pos : Bool) (b : ℝ) : ℝ := if pos then Real.exp b - 1 else b

/-- `φ̄` in convex mode: `max(ξ - 1, E + b + δ + D)`, with `D` the paper's `2nη_0` -/
noncomputable def ddPhiC (D : ℝ) (pos : Bool) (E a b δ : ℝ) : ℝ := max (logXi D pos E a b δ - 1) (E + b + δ + D)

/-- `𝓔(ℓ)` in convex mode -/
noncomputable def ddLogBoundC (η ηx ηp ηc ℓ E : ℝ) (pos : Bool) (a b δ : ℝ) (φF : ℕ → ℝ) (d' : ℕ) (φ' : ℕ → ℝ)
    (q : ℕ) (B : ℤ) : ℝ :=
  ddLogBoundG p η ηx ηp ηc ℓ E (ddTbC pos b) (ddPhiC (2 * ηx) pos E a b δ) (logXi (2 * ηx) pos E a b δ) b δ φF d'
    φ' q B

/-- `C = e^E - 1 + E_c` in convex mode -/
noncomputable def ddLogCC (η ηx ηp E : ℝ) (pos : Bool) (a b δ : ℝ) (φF : ℕ → ℝ) (d' : ℕ) (B : ℤ) : ℝ :=
  Real.exp E - 1 + ddLogEc p (2 * ηx) (2 * ηp) (ddPhiC (2 * ηx) pos E a b δ) (ddTbC pos b)
    (ddCoreE p (ddTbC pos b) η b φF d') E δ b (logXi (2 * ηx) pos E a b δ) B

/-- the convex mode's `t̄` is at least the theorem's -/
theorem coreT_le_ddTbC (pos : Bool) (b : ℝ) : coreT pos b 0 ≤ ddTbC pos b := by
  unfold coreT ddTbC
  cases pos with
  | true => simp
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, pow_zero, one_mul]
    linarith [Real.add_one_le_exp (-b)]

/-- the convex mode's `φ̄` is at least the theorem's -/
theorem logPhiB_le_ddPhiC (D : ℝ) (pos : Bool) (E a b δ : ℝ) : logPhiB D pos E a b δ ≤ ddPhiC D pos E a b δ := by
  unfold logPhiB ddPhiC
  exact max_le_max le_rfl (by linarith [Real.add_one_le_exp (-(E + b + δ))])

variable {s : Set ℝ}

/-- `v_k = ∑ b^l/(k + l)!` is in the class with `b` -/
theorem cvx_coreV {b : ℝ → ℝ} (hb : Cvx s b) (d k : ℕ) : Cvx s fun x => coreV (b x) d k := by
  have h := Cvx.sum hb.convex.1 (Finset.range (d + 1 - k)) (F := fun l x => invF (k + l) * b x ^ l)
    (fun l _ => (hb.pow l).const_mul (by unfold invF; positivity))
  exact h.congr fun x _ => rfl

/-- `v_k = ∑ C^l/(k + l)` is in the class with `C` -/
theorem cvx_logV {C : ℝ → ℝ} (hC : Cvx s C) (q k : ℕ) : Cvx s fun x => logV (C x) q k := by
  have h := Cvx.sum hC.convex.1 (Finset.range (q + 1 - k)) (F := fun l x => C x ^ l / ((k + l : ℕ) : ℝ))
    (fun l _ => (hC.pow l).div_const (Nat.cast_nonneg _))
  exact h.congr fun x _ => rfl

/-- Horner's `e_k` on double words is in the class with `z̄` and the `v_k` -/
theorem cvx_ddHornerB (hu : 4 * u p < 1) {zb : ℝ → ℝ} {v : ℕ → ℝ → ℝ} (hzb : Cvx s zb) (hv : ∀ k, Cvx s (v k))
    {D : ℝ} (hD : 0 ≤ D) {φ : ℕ → ℝ} (hφ : ∀ k, 0 ≤ φ k) (d : ℕ) :
    ∀ j, Cvx s fun x => ddHornerB p (zb x) D φ (fun k => v k x) d j
  | 0 => (Cvx.const hzb.convex.1 (hφ d)).congr fun _ _ => rfl
  | j + 1 => by
    have ih := cvx_ddHornerB hu hzb hv hD hφ d j
    have heA := eA_nonneg p hu
    have heP := eP_nonneg p
    have hs := hzb.convex.1
    have hDk := ((hzb.mul ih).add (Cvx.const hs (hφ (d - (j + 1))))).add
      (((hzb.mul ((hv (d - (j + 1) + 1)).add ih)).const_mul heP).add (Cvx.const hs hD))
    exact (hDk.add (((hv (d - (j + 1))).add hDk).const_mul heA)).congr fun x _ => rfl

/-- `E^tr_d` is in the class with `b`, where `b < d + 2` -/
theorem cvx_eTr {b : ℝ → ℝ} (hb : Cvx s b) (d : ℕ) (hbd : ∀ x ∈ s, b x < d + 2) : Cvx s fun x => eTr (b x) d := by
  have hf : Cvx s fun x => b x / ((d : ℝ) + 2) := hb.div_const (by positivity)
  have h1 : ∀ x ∈ s, b x / ((d : ℝ) + 2) < 1 := fun x hx => by
    rw [div_lt_one (by positivity)]
    exact hbd x hx
  have hg : Cvx s fun x => b x ^ (d + 1) / ((d + 1).factorial : ℝ) :=
    (hb.pow (d + 1)).div_const (Nat.cast_nonneg _)
  exact (hg.div_one_sub hf h1).congr fun x _ => by
    unfold eTr
    rw [div_div]

/-- `E_0` is in the class with `t̄_0` and `b`, where `b < d' + 2` -/
theorem cvx_ddCoreE (hu : 4 * u p < 1) {T0 b : ℝ → ℝ} (hT : Cvx s T0) (hb : Cvx s b) {η : ℝ} (hη : 0 ≤ η)
    {φ : ℕ → ℝ} (hφ : ∀ k, 0 ≤ φ k) (d' : ℕ) (hbd : ∀ x ∈ s, b x < d' + 2) :
    Cvx s fun x => ddCoreE p (T0 x) η (b x) φ d' := by
  have hs := hb.convex.1
  have heA := eA_nonneg p hu
  have heP := eP_nonneg p
  by_cases hd : d' = 1
  · subst hd
    exact (cvx_eTr hb 1 hbd).congr fun x _ => by simp [ddCoreE]
  · have hv := fun k => cvx_coreV hb d' k
    have he2 := cvx_ddHornerB p hu (v := fun k x => coreV (b x) d' k) hb hv le_rfl hφ d' (d' - 2)
    have hZw := hb.mul ((hv 2).add he2)
    have hε1 := hZw.const_mul heP
    have hEm := (((hb.mul (hZw.add hε1)).const_mul heP).add (hb.mul (hε1.add (hb.mul he2)))).add
      (cvx_eTr hb d' hbd)
    have hres := (hEm.add ((hT.add hEm).const_mul heA)).add (Cvx.const hs (by linarith : (0 : ℝ) ≤ 2 * η))
    exact hres.congr fun x _ => by simp only [ddCoreE, hd, ↓reduceIte]

/-- step (4)'s `E_c` is in the class with its arguments -/
theorem cvx_ddLogEc (hu : 4 * u p < 1) {φb tb Em E δ b ξ : ℝ → ℝ} (hφb : Cvx s φb) (htb : Cvx s tb)
    (hEm : Cvx s Em) (hE : Cvx s E) (hδ : Cvx s δ) (hb : Cvx s b) (hξ : Cvx s ξ) {D Dp : ℝ} (hD : 0 ≤ D)
    (hDp : 0 ≤ Dp) (B : ℤ) :
    Cvx s fun x => ddLogEc p D Dp (φb x) (tb x) (Em x) (E x) (δ x) (b x) (ξ x) B := by
  have hs := hE.convex.1
  have heA := eA_nonneg p hu
  have heP := eP_nonneg p
  have htE := htb.add hEm
  have hεφt := (((hφb.mul htE).const_mul heP).add (Cvx.const hs hDp)).add
    ((hφb.max htE).const_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (-B - 12)))
  have hbδ := hb.add hδ
  have hEδ' := hE.add hδ
  have hεs := ((((hbδ.exp_sub_one_sub.const_mul (by norm_num : (0 : ℝ) ≤ 2)).add
    (hbδ.exp.mul hEδ'.exp_sub_one)).add hEm).add (Cvx.const hs hD)).const_mul heA
  have hEδ := (hE.exp.mul hδ.exp_sub_one).add ((((Cvx.const hs zero_le_one).add htb).add hEm).const_mul hD)
  have hεc := ((((hE.exp_sub_one.add (hξ.mul hEm)).add hEδ).add hεφt).add hεs).const_mul heA
  exact (((((hξ.mul hEm).add hEδ).add hεφt).add hεs).add hεc).congr fun x _ => rfl

/-- step (5)'s `P` is in the class with `C` and `E_c`, where `C < 1` -/
theorem cvx_ddLogP (hu : 4 * u p < 1) {C Ec : ℝ → ℝ} (hC : Cvx s C) (hEc : Cvx s Ec) (hC1 : ∀ x ∈ s, C x < 1)
    {Dc : ℝ} (hDc : 0 ≤ Dc) {φ' : ℕ → ℝ} (hφ' : ∀ k, 0 ≤ φ' k) (q : ℕ) (B : ℤ) :
    Cvx s fun x => ddLogP p Dc (C x) (Ec x) φ' q B := by
  have hs := hC.convex.1
  have heP := eP_nonneg p
  have heF := eF_nonneg p
  have hv := fun k => cvx_logV hC q k
  have he2 := cvx_ddHornerB p hu (v := fun k x => logV (C x) q k) hC hv hDc hφ' q (q - 2)
  have hZh := hC.mul ((hv 2).add he2)
  have hεh := (hZh.const_mul heP).add (Cvx.const hs hDc)
  have hhb := hZh.add hεh
  have hεg := ((Cvx.const hs zero_le_one).add hhb).const_mul heF
  have hεr := ((hC.mul (((Cvx.const hs zero_le_one).add hhb).add hεg)).const_mul heP).add (Cvx.const hs hDc)
  have hmid := hC.mul ((hεg.add hεh).add (hC.mul he2))
  have hM := ((hC.pow (q + 1)).div_const (by positivity : (0 : ℝ) ≤ (q : ℝ) + 1)).max
    (hC.const_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (-B - 13)))
  exact (((hεr.add hmid).add (hM.div_one_sub hC hC1)).add (hEc.div_one_sub hC hC1)).congr fun x _ => rfl

/-- the bound with `t̄`, `φ̄` and `ξ` given is in the class with all of its arguments, where `b < d' + 2` and
`C < 1` -/
theorem cvx_ddLogBoundG (hu : 4 * u p < 1) {L E tb φb ξ b δ : ℝ → ℝ} (hL : Cvx s L) (hE : Cvx s E)
    (htb : Cvx s tb) (hφb : Cvx s φb) (hξ : Cvx s ξ) (hb : Cvx s b) (hδ : Cvx s δ) {η ηx ηp ηc : ℝ} (hη : 0 ≤ η)
    (hηx : 0 ≤ ηx) (hηp : 0 ≤ ηp) (hηc : 0 ≤ ηc) {φF : ℕ → ℝ} (hφF : ∀ k, 0 ≤ φF k) (d' : ℕ)
    (hbd : ∀ x ∈ s, b x < d' + 2) {φ' : ℕ → ℝ} (hφ' : ∀ k, 0 ≤ φ' k) (q : ℕ) (B : ℤ)
    (hC : ∀ x ∈ s, Real.exp (E x) - 1 + ddLogEc p (2 * ηx) (2 * ηp) (φb x) (tb x)
      (ddCoreE p (tb x) η (b x) φF d') (E x) (δ x) (b x) (ξ x) B < 1) :
    Cvx s fun x => ddLogBoundG p η ηx ηp ηc (L x) (E x) (tb x) (φb x) (ξ x) (b x) (δ x) φF d' φ' q B := by
  have heF := eF_nonneg p
  have hEm := cvx_ddCoreE p hu htb hb hη hφF d' hbd
  have hEc := cvx_ddLogEc p hu hφb htb hEm hE hδ hb hξ (by linarith : (0 : ℝ) ≤ 2 * ηx)
    (by linarith : (0 : ℝ) ≤ 2 * ηp) B
  have hCv := hE.exp_sub_one.add hEc
  have hP := cvx_ddLogP p hu hCv hEc hC (by linarith : (0 : ℝ) ≤ 2 * ηc) hφ' q B
  exact (((hL.add hP).const_mul heF).add hP).congr fun x _ => rfl

/-- `ξ = e^{E+δ-a} + D` or `e^{E+b+δ} + D` is in the class with `E`, `δ` and `b` -/
theorem cvx_logXi {E δ b : ℝ → ℝ} (hE : Cvx s E) (hδ : Cvx s δ) (hb : Cvx s b) {D : ℝ} (hD : 0 ≤ D) (pos : Bool)
    (a : ℝ) : Cvx s fun x => logXi D pos (E x) a (b x) (δ x) := by
  have hs := hE.convex.1
  cases pos with
  | true =>
    have hm : MonotoneOn (fun x => E x + δ x - a) s := fun x hx y hy hxy => by
      have h1 := hE.mono hx hy hxy
      have h2 := hδ.mono hx hy hxy
      simp only
      linarith
    have hc : ConvexOn ℝ s (fun x => E x + δ x - a) := (hE.convex.add hδ.convex).sub (concaveOn_const a hs)
    exact ((Cvx.exp_of hm hc).add (Cvx.const hs hD)).congr fun x _ => by simp [logXi]
  | false =>
    exact ((((hE.add hb).add hδ).exp).add (Cvx.const hs hD)).congr fun x _ => by simp [logXi]

/-- the convex mode's `t̄` is in the class with `b` -/
theorem cvx_ddTbC {b : ℝ → ℝ} (hb : Cvx s b) (pos : Bool) : Cvx s fun x => ddTbC pos (b x) := by
  cases pos with
  | true => exact hb.exp_sub_one.congr fun x _ => by simp [ddTbC]
  | false => exact hb.congr fun x _ => by simp [ddTbC]

/-- the convex mode's `φ̄ = max(ξ - 1, E + b + δ + D)` is in the class with `E`, `δ` and `b` -/
theorem cvx_ddPhiC {E δ b : ℝ → ℝ} (hE : Cvx s E) (hδ : Cvx s δ) (hb : Cvx s b) {D : ℝ} (hD : 0 ≤ D) (pos : Bool)
    (a : ℝ) : Cvx s fun x => ddPhiC D pos (E x) a (b x) (δ x) := by
  have hs := hE.convex.1
  have hξ := cvx_logXi hE hδ hb hD pos a
  have hm : MonotoneOn (fun x => logXi D pos (E x) a (b x) (δ x) - 1) s := fun x hx y hy hxy => by
    have h1 := hξ.mono hx hy hxy
    simp only at h1 ⊢
    linarith
  have hc : ConvexOn ℝ s (fun x => logXi D pos (E x) a (b x) (δ x) - 1) := hξ.convex.sub (concaveOn_const 1 hs)
  exact (Cvx.max_left hm hc (((hE.add hb).add hδ).add (Cvx.const hs hD))).congr fun x _ => rfl

/-- Theorem 42's proof, "Convexity", read with `n = 2`: for a fixed case, with `E`, `δ` and `b` nonnegative,
nondecreasing and convex in `ℓ` on a set `s` of nonnegative numbers, `b < d' + 2` and `C < 1` on `s`, the bound of
the convex mode is nonnegative, nondecreasing and convex in `ℓ` on `s` -/
theorem cvx_ddLogBoundC (hu : 4 * u p < 1) (hs0 : ∀ x ∈ s, 0 ≤ x) {E δ b : ℝ → ℝ} (hE : Cvx s E) (hδ : Cvx s δ)
    (hb : Cvx s b) {η ηx ηp ηc : ℝ} (hη : 0 ≤ η) (hηx : 0 ≤ ηx) (hηp : 0 ≤ ηp) (hηc : 0 ≤ ηc) (pos : Bool) (a : ℝ)
    {φF : ℕ → ℝ} (hφF : ∀ k, 0 ≤ φF k) (d' : ℕ) (hbd : ∀ x ∈ s, b x < d' + 2) {φ' : ℕ → ℝ} (hφ' : ∀ k, 0 ≤ φ' k)
    (q : ℕ) (B : ℤ)
    (hC : ∀ x ∈ s, ddLogCC p η ηx ηp (E x) pos a (b x) (δ x) φF d' B < 1) :
    Cvx s fun x => ddLogBoundC p η ηx ηp ηc x (E x) pos a (b x) (δ x) φF d' φ' q B := by
  have hs := hE.convex.1
  exact (cvx_ddLogBoundG p hu (Cvx.id hs hs0) hE (cvx_ddTbC hb pos)
    (cvx_ddPhiC hE hδ hb (by linarith : (0 : ℝ) ≤ 2 * ηx) pos a)
    (cvx_logXi hE hδ hb (by linarith : (0 : ℝ) ≤ 2 * ηx) pos a) hb hδ hη hηx hηp hηc hφF d' hbd hφ' q B hC).congr
    fun x _ => rfl

/-- `C` of the convex mode is in the class with `E`, `δ` and `b`, where `b < d' + 2`: it is below `1` on an
interval if it is at its upper end -/
theorem cvx_ddLogCC (hu : 4 * u p < 1) {E δ b : ℝ → ℝ} (hE : Cvx s E) (hδ : Cvx s δ) (hb : Cvx s b)
    {η ηx ηp : ℝ} (hη : 0 ≤ η) (hηx : 0 ≤ ηx) (hηp : 0 ≤ ηp) (pos : Bool) (a : ℝ) {φF : ℕ → ℝ}
    (hφF : ∀ k, 0 ≤ φF k) (d' : ℕ) (hbd : ∀ x ∈ s, b x < d' + 2) (B : ℤ) :
    Cvx s fun x => ddLogCC p η ηx ηp (E x) pos a (b x) (δ x) φF d' B := by
  have hD : (0 : ℝ) ≤ 2 * ηx := by linarith
  have htb := cvx_ddTbC hb pos
  exact (hE.exp_sub_one.add (cvx_ddLogEc p hu (cvx_ddPhiC hE hδ hb hD pos a) htb
    (cvx_ddCoreE p hu htb hb hη hφF d' hbd) hE hδ hb (cvx_logXi hE hδ hb hD pos a) hD
    (by linarith : (0 : ℝ) ≤ 2 * ηp) B)).congr fun x _ => rfl

/-- Theorem 42's first chord read with `n = 2`: for a fixed case with `E`, `δ` and `b` in the class on `[ℓ₁, ℓ₂]`,
`ℓ₁ ≥ 0`, and `b < d' + 2` and `C < 1` at `ℓ₂`, the bound of the convex mode within `εℓ` at both ends is within
`εℓ` on the interval -/
theorem dd_log_chord (hu : 4 * u p < 1) {l₁ l₂ : ℝ} (h0 : 0 ≤ l₁) {E δ b : ℝ → ℝ} (hE : Cvx (Icc l₁ l₂) E)
    (hδ : Cvx (Icc l₁ l₂) δ) (hb : Cvx (Icc l₁ l₂) b) {η ηx ηp ηc : ℝ} (hη : 0 ≤ η) (hηx : 0 ≤ ηx) (hηp : 0 ≤ ηp)
    (hηc : 0 ≤ ηc) (pos : Bool) (a : ℝ) {φF : ℕ → ℝ} (hφF : ∀ k, 0 ≤ φF k) (d' : ℕ) (hbd : b l₂ < d' + 2)
    {φ' : ℕ → ℝ} (hφ' : ∀ k, 0 ≤ φ' k) (q : ℕ) (B : ℤ)
    (hC : ddLogCC p η ηx ηp (E l₂) pos a (b l₂) (δ l₂) φF d' B < 1) {ε : ℝ}
    (h₁ : ddLogBoundC p η ηx ηp ηc l₁ (E l₁) pos a (b l₁) (δ l₁) φF d' φ' q B ≤ ε * l₁)
    (h₂ : ddLogBoundC p η ηx ηp ηc l₂ (E l₂) pos a (b l₂) (δ l₂) φF d' φ' q B ≤ ε * l₂) {l : ℝ}
    (hl : l ∈ Icc l₁ l₂) :
    ddLogBoundC p η ηx ηp ηc l (E l) pos a (b l) (δ l) φF d' φ' q B ≤ ε * l := by
  have h2 : l₂ ∈ Icc l₁ l₂ := right_mem_Icc.mpr (hl.1.trans hl.2)
  have hbd' : ∀ x ∈ Icc l₁ l₂, b x < d' + 2 := fun x hx => lt_of_le_of_lt (hb.mono hx h2 hx.2) hbd
  have hC' : ∀ x ∈ Icc l₁ l₂, ddLogCC p η ηx ηp (E x) pos a (b x) (δ x) φF d' B < 1 := fun x hx =>
    lt_of_le_of_lt ((cvx_ddLogCC p hu hE hδ hb hη hηx hηp pos a hφF d' hbd' B).mono hx h2 hx.2) hC
  have hF := cvx_ddLogBoundC p hu (fun x hx => h0.trans hx.1) hE hδ hb hη hηx hηp hηc pos a hφF d' hbd' hφ' q B hC'
  exact chord_le_mul hF.convex h₁ h₂ hl

/-- Theorem 42's second chord read with `n = 2`: on `[0, ℓ₂]`, the bound of the convex mode within `Φ` at `0` and
within `εℓ₂ + Φ` at `ℓ₂` is within `εℓ + Φ` on the interval -/
theorem dd_log_chord_zero (hu : 4 * u p < 1) {l₂ : ℝ} {E δ b : ℝ → ℝ} (hE : Cvx (Icc 0 l₂) E)
    (hδ : Cvx (Icc 0 l₂) δ) (hb : Cvx (Icc 0 l₂) b) {η ηx ηp ηc : ℝ} (hη : 0 ≤ η) (hηx : 0 ≤ ηx) (hηp : 0 ≤ ηp)
    (hηc : 0 ≤ ηc) (pos : Bool) (a : ℝ) {φF : ℕ → ℝ} (hφF : ∀ k, 0 ≤ φF k) (d' : ℕ) (hbd : b l₂ < d' + 2)
    {φ' : ℕ → ℝ} (hφ' : ∀ k, 0 ≤ φ' k) (q : ℕ) (B : ℤ)
    (hC : ddLogCC p η ηx ηp (E l₂) pos a (b l₂) (δ l₂) φF d' B < 1) {ε Φ : ℝ}
    (h₁ : ddLogBoundC p η ηx ηp ηc 0 (E 0) pos a (b 0) (δ 0) φF d' φ' q B ≤ Φ)
    (h₂ : ddLogBoundC p η ηx ηp ηc l₂ (E l₂) pos a (b l₂) (δ l₂) φF d' φ' q B ≤ ε * l₂ + Φ) {l : ℝ}
    (hl : l ∈ Icc 0 l₂) :
    ddLogBoundC p η ηx ηp ηc l (E l) pos a (b l) (δ l) φF d' φ' q B ≤ ε * l + Φ := by
  have h2 : l₂ ∈ Icc 0 l₂ := right_mem_Icc.mpr (hl.1.trans hl.2)
  have hbd' : ∀ x ∈ Icc 0 l₂, b x < d' + 2 := fun x hx => lt_of_le_of_lt (hb.mono hx h2 hx.2) hbd
  have hC' : ∀ x ∈ Icc 0 l₂, ddLogCC p η ηx ηp (E x) pos a (b x) (δ x) φF d' B < 1 := fun x hx =>
    lt_of_le_of_lt ((cvx_ddLogCC p hu hE hδ hb hη hηx hηp pos a hφF d' hbd' B).mono hx h2 hx.2) hC
  have hF := cvx_ddLogBoundC p hu (fun x hx => hx.1) hE hδ hb hη hηx hηp hηc pos a hφF d' hbd' hφ' q B hC'
  exact chord_le_mul_add hF.convex h₁ h₂ hl

/-- the bound of the convex mode is at least the theorem's, for nonnegative arguments with `b < d' + 2` and the
convex mode's `C < 1`: the bound grows along the segment from the theorem's `t̄` and `φ̄` to the convex mode's -/
theorem ddLogBound_le_ddLogBoundC (hu : 4 * u p < 1) {η ηx ηp ηc ℓ E a b δ : ℝ} (hη : 0 ≤ η) (hηx : 0 ≤ ηx)
    (hηp : 0 ≤ ηp) (hηc : 0 ≤ ηc) (hℓ : 0 ≤ ℓ) (hE : 0 ≤ E) (hb : 0 ≤ b) (hδ : 0 ≤ δ) (pos : Bool) {φF : ℕ → ℝ}
    (hφF : ∀ k, 0 ≤ φF k) (d' : ℕ) (hbd : b < d' + 2) {φ' : ℕ → ℝ} (hφ' : ∀ k, 0 ≤ φ' k) (q : ℕ) (B : ℤ)
    (hC : ddLogCC p η ηx ηp E pos a b δ φF d' B < 1) :
    ddLogBound p η ηx ηp ηc ℓ E pos a b δ φF d' φ' q B ≤ ddLogBoundC p η ηx ηp ηc ℓ E pos a b δ φF d' φ' q B := by
  have hs : Convex ℝ (Icc (0 : ℝ) 1) := convex_Icc 0 1
  have hD : (0 : ℝ) ≤ 2 * ηx := by linarith
  have ht0 : 0 ≤ coreT pos b 0 := by
    unfold coreT
    cases pos with
    | true =>
      simp only [↓reduceIte, pow_zero, one_mul]
      linarith [Real.one_le_exp hb]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, pow_zero, one_mul]
      linarith [Real.exp_le_one_iff.mpr (by linarith : -b ≤ 0)]
  have hp0 : 0 ≤ logPhiB (2 * ηx) pos E a b δ := by
    unfold logPhiB
    refine le_max_of_le_right ?_
    linarith [Real.exp_le_one_iff.mpr (by linarith : -(E + b + δ) ≤ 0)]
  have hξ0 : 0 ≤ logXi (2 * ηx) pos E a b δ := by
    unfold logXi
    split_ifs <;> linarith [Real.exp_pos (E + δ - a), Real.exp_pos (E + b + δ)]
  have htb := cvx_segment ht0 (coreT_le_ddTbC pos b)
  have hφb := cvx_segment hp0 (logPhiB_le_ddPhiC (2 * ηx) pos E a b δ)
  have hEc := Cvx.const hs hE
  have hbc := Cvx.const hs hb
  have hδc := Cvx.const hs hδ
  have hξc := Cvx.const hs hξ0
  -- `C < 1` along the segment, as `C` grows to its value in convex mode
  have hCm := (hEc.exp_sub_one.add (cvx_ddLogEc p hu hφb htb
    (cvx_ddCoreE p hu htb hbc hη hφF d' (fun _ _ => hbd)) hEc hδc hbc hξc hD (by linarith : (0 : ℝ) ≤ 2 * ηp) B)).mono
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.mpr zero_le_one
  have hCt : ∀ t ∈ Icc (0 : ℝ) 1, Real.exp E - 1 + ddLogEc p (2 * ηx) (2 * ηp)
      (logPhiB (2 * ηx) pos E a b δ + (ddPhiC (2 * ηx) pos E a b δ - logPhiB (2 * ηx) pos E a b δ) * t)
      (coreT pos b 0 + (ddTbC pos b - coreT pos b 0) * t)
      (ddCoreE p (coreT pos b 0 + (ddTbC pos b - coreT pos b 0) * t) η b φF d') E δ b
      (logXi (2 * ηx) pos E a b δ) B < 1 := fun t ht => by
    have h := hCm ht h1 ht.2
    simp only [mul_one, add_sub_cancel] at h
    exact lt_of_le_of_lt h hC
  have hF := cvx_ddLogBoundG p hu (Cvx.const hs hℓ) hEc htb hφb hξc hbc hδc hη hηx hηp hηc hφF d'
    (fun _ _ => hbd) hφ' q B hCt
  have h := hF.zero_le_one.2
  simp only [mul_zero, add_zero, mul_one, add_sub_cancel] at h
  exact h

end ExpansionBounds
