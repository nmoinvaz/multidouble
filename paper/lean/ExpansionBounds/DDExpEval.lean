import ExpansionBounds.DDExp
import ExpansionBounds.ExpEval

/-!
# Proposition 44 (`prop:ddexplog`): the bound of a case of `DD::exp` in rational arithmetic

The mirrors over `ℚ` of the double-word bounds: `e_A`, `e_F` and `e_P`, `v_k`, Horner's `e_k` (`ddHornerBQ`) and
`E_0` (`ddCoreEQ`) have the same recursions as the real ones, and a `cast_` theorem shows that each mirror's value,
cast to `ℝ`, is the bound at the cast arguments. The bound `ε` of a case (`ddExpEps`) has `e^z` at four arguments,
which the mirror `ddExpEpsQ` takes from the enclosure of `e^z` by 16 terms of its series, each on the side that
raises `ε`: `ddExpEps_le` shows that `ddExpEpsQ`, cast to `ℝ`, is at least `ε`, and `ddFloor_le` carries the
floor of the scaling back, `2^{-967}(1 + u) ≤ a/(1 + a) - E_0`, from the rationals.
-/

namespace ExpansionBounds

open Finset

/-- `e_A = 3u²/(1 - 4u)` over `ℚ` -/
def eAQ (uq : ℚ) : ℚ := 3 * uq ^ 2 / (1 - 4 * uq)

/-- `e_F = e_M = 2u²` over `ℚ` -/
def eFQ (uq : ℚ) : ℚ := 2 * uq ^ 2

/-- `e_P = 5u²/(1 + u)²` over `ℚ` -/
def ePQ (uq : ℚ) : ℚ := 5 * uq ^ 2 / (1 + uq) ^ 2

/-- `v_k = ∑_{l ≤ d - k} b^l/(k + l)!` over `ℚ` -/
def coreVXQ (b : ℚ) (d k : ℕ) : ℚ := ∑ l ∈ range (d + 1 - k), 1 / ((k + l).factorial : ℚ) * b ^ l

/-- Horner's `e_{d-j}` on double words over `ℚ` -/
def ddHornerBQ (uq zb D : ℚ) (φ v : ℕ → ℚ) (d : ℕ) : ℕ → ℚ
  | 0 => φ d
  | j + 1 =>
    let k := d - (j + 1)
    let e1 := ddHornerBQ uq zb D φ v d j
    let Dk := zb * e1 + φ k + (ePQ uq * (zb * (v (k + 1) + e1)) + D)
    Dk + eAQ uq * (v k + Dk)

/-- `E_0` read with `n = 2` and `m = 0` over `ℚ` -/
def ddCoreEQ (uq T0 η b : ℚ) (φ : ℕ → ℚ) (d' : ℕ) : ℚ :=
  if d' = 1 then eTrQ b 1 else
    let e2 := ddHornerBQ uq b 0 φ (coreVXQ b d') d' (d' - 2)
    let Zw := b * (coreVXQ b d' 2 + e2)
    let ε1 := ePQ uq * Zw
    let Em := ePQ uq * (b * (Zw + ε1)) + b * (ε1 + b * e2) + eTrQ b d'
    Em + eAQ uq * (T0 + Em) + 2 * η

/-- `t̄_0`'s bound: `e^b - 1` for `r ≥ 0` and `1 - e^{-b}` for `r ≤ 0`, on the enclosure of `e^z` -/
def ddT0Q (pos : Bool) (b : ℚ) : ℚ := if pos then expUpQ b - 1 else 1 - expLoQ (-b)

/-- the bound `ε` of a case over `ℚ`, each `e^z` from its enclosure on the side that raises `ε` -/
def ddExpEpsQ (uq η : ℚ) (pos : Bool) (a b δ : ℚ) (φ : ℕ → ℚ) (d' : ℕ) : ℚ :=
  let E := ddCoreEQ uq (ddT0Q pos b) η b φ d'
  (E + eFQ uq * ((if pos then expUpQ b else expUpQ (-a)) + E)) /
    (if pos then expLoQ (a - δ) else expLoQ (-b - δ)) + expUpQ δ - 1

/-- `coreVXQ`, cast to `ℝ`, is `v_k` -/
theorem cast_coreVXQ (b : ℚ) (d k : ℕ) : ((coreVXQ b d k : ℚ) : ℝ) = coreV (b : ℝ) d k := by
  simp [coreVXQ, coreV, hornerE, invF]

/-- `eTrQ`, cast to `ℝ`, is `E^tr_d` -/
theorem cast_eTrQ (b : ℚ) (d : ℕ) : ((eTrQ b d : ℚ) : ℝ) = eTr (b : ℝ) d := by
  simp [eTrQ, eTr]

/-- the quotient of a case's bound grows with its numerator and falls with its divisor -/
theorem ddEps_real_le {E Eq Z0 Z0q V Vq D Dq cF : ℝ} (hcF : 0 ≤ cF) (hE : E ≤ Eq) (hZ : Z0 ≤ Z0q) (hV : Vq ≤ V)
    (hVq : 0 < Vq) (hD : D ≤ Dq) (hN : 0 ≤ Eq + cF * (Z0q + Eq)) :
    (E + cF * (Z0 + E)) / V + D - 1 ≤ (Eq + cF * (Z0q + Eq)) / Vq + Dq - 1 := by
  have h1 : E + cF * (Z0 + E) ≤ Eq + cF * (Z0q + Eq) :=
    add_le_add hE (mul_le_mul_of_nonneg_left (add_le_add hZ hE) hcF)
  have := div_le_div₀ hN h1 hVq hV
  linarith

variable (p : ℤ) {uq : ℚ} (h : (uq : ℝ) = u p)

include h in
/-- `eAQ`, cast to `ℝ`, is `e_A` -/
theorem cast_eAQ : ((eAQ uq : ℚ) : ℝ) = eA p := by
  unfold eAQ eA
  push_cast
  rw [h]

include h in
/-- `eFQ`, cast to `ℝ`, is `e_F` -/
theorem cast_eFQ : ((eFQ uq : ℚ) : ℝ) = eF p := by
  unfold eFQ eF
  push_cast
  rw [h]

include h in
/-- `ePQ`, cast to `ℝ`, is `e_P` -/
theorem cast_ePQ : ((ePQ uq : ℚ) : ℝ) = eP p := by
  unfold ePQ eP
  push_cast
  rw [h]

include h in
/-- `ddHornerBQ`, cast to `ℝ`, is Horner's `e_{d-j}` at the cast arguments -/
theorem cast_ddHornerBQ (zb D : ℚ) (φ v : ℕ → ℚ) (d : ℕ) : ∀ j,
    ((ddHornerBQ uq zb D φ v d j : ℚ) : ℝ) = ddHornerB p zb D (fun k => φ k) (fun k => v k) d j
  | 0 => rfl
  | j + 1 => by
    simp only [ddHornerBQ, ddHornerB]
    push_cast
    rw [cast_ddHornerBQ zb D φ v d j, cast_ePQ p h, cast_eAQ p h]

include h in
/-- `ddCoreEQ`, cast to `ℝ`, is `E_0` at the cast arguments -/
theorem cast_ddCoreEQ (T0 η b : ℚ) (φ : ℕ → ℚ) (d' : ℕ) :
    ((ddCoreEQ uq T0 η b φ d' : ℚ) : ℝ) = ddCoreE p T0 η b (fun k => φ k) d' := by
  have hv : (fun k => ((coreVXQ b d' k : ℚ) : ℝ)) = coreV (b : ℝ) d' := funext fun k => cast_coreVXQ b d' k
  unfold ddCoreEQ ddCoreE
  split_ifs with hd
  · exact cast_eTrQ b 1
  · simp only
    push_cast
    rw [cast_ddHornerBQ p h, hv, cast_ePQ p h, cast_eAQ p h, cast_eTrQ, cast_coreVXQ]
    simp only [Rat.cast_zero]

/-- `E_0` grows with `t̄_0` -/
theorem ddCoreE_mono (hu : 4 * u p < 1) {T0 T0' : ℝ} (hT : T0 ≤ T0') (η b : ℝ) (φ : ℕ → ℝ) (d' : ℕ) :
    ddCoreE p T0 η b φ d' ≤ ddCoreE p T0' η b φ d' := by
  unfold ddCoreE
  split_ifs
  · exact le_rfl
  · simp only
    linarith [mul_le_mul_of_nonneg_left hT (eA_nonneg p hu)]

/-- `t̄_0` is at most its mirror, for `0 ≤ b ≤ 1` -/
theorem ddT0_le (pos : Bool) {b : ℚ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    coreT pos (b : ℝ) 0 ≤ ((ddT0Q pos b : ℚ) : ℝ) := by
  cases pos with
  | true =>
    simp only [coreT, ddT0Q, ↓reduceIte, pow_zero, one_mul]
    obtain ⟨-, e2⟩ := exp_enclosure b (by rw [abs_of_nonneg hb0]; exact hb1)
    push_cast
    linarith
  | false =>
    simp only [coreT, ddT0Q, Bool.false_eq_true, ↓reduceIte, pow_zero, one_mul]
    obtain ⟨e1, -⟩ := exp_enclosure (-b) (by rw [abs_neg, abs_of_nonneg hb0]; exact hb1)
    push_cast at e1 ⊢
    linarith

include h in
/-- `E_0` is at most its mirror's value, for `0 ≤ b ≤ 1` -/
theorem ddCoreE_le (hu : 4 * u p < 1) (pos : Bool) {b : ℚ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (η : ℚ) (φ : ℕ → ℚ)
    (d' : ℕ) :
    ddCoreE p (coreT pos (b : ℝ) 0) η b (fun k => φ k) d' ≤ ((ddCoreEQ uq (ddT0Q pos b) η b φ d' : ℚ) : ℝ) := by
  rw [cast_ddCoreEQ p h]
  exact ddCoreE_mono p hu (ddT0_le pos hb0 hb1) _ _ _ _

include h in
/-- the floor of the scaling back, from the rationals: `lo(1 + u) ≤ a/(1 + a) - E_0` at `η = 0` -/
theorem ddFloor_le (hu : 4 * u p < 1) (pos : Bool) {lo a b : ℚ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (φ : ℕ → ℚ) (d' : ℕ)
    (hchk : lo * (1 + uq) ≤ a / (1 + a) - ddCoreEQ uq (ddT0Q pos b) 0 b φ d') :
    (lo : ℝ) * (1 + u p) ≤ (a : ℝ) / (1 + a) - ddCoreE p (coreT pos (b : ℝ) 0) 0 b (fun k => φ k) d' := by
  have h1 := (Rat.cast_le (K := ℝ)).mpr hchk
  rw [Rat.cast_mul, Rat.cast_add, Rat.cast_one, Rat.cast_sub, Rat.cast_div, Rat.cast_add, Rat.cast_one, h] at h1
  have h2 := ddCoreE_le p h hu pos hb0 hb1 0 φ d'
  rw [Rat.cast_zero] at h2
  linarith

include h in
/-- the bound `ε` of a case is at most its mirror's value: for `0 ≤ a ≤ b`, `0 ≤ δ` and `b + δ ≤ 1`, with the
mirror's divisor positive and its numerator nonnegative -/
theorem ddExpEps_le (hu : 4 * u p < 1) (pos : Bool) {η a b δ : ℚ} (ha : 0 ≤ a) (hab : a ≤ b) (hδ : 0 ≤ δ)
    (hb : b + δ ≤ 1) (φ : ℕ → ℚ) (d' : ℕ) (hV : 0 < (if pos then expLoQ (a - δ) else expLoQ (-b - δ)))
    (hN : 0 ≤ ddCoreEQ uq (ddT0Q pos b) η b φ d' +
      eFQ uq * ((if pos then expUpQ b else expUpQ (-a)) + ddCoreEQ uq (ddT0Q pos b) η b φ d')) :
    ddExpEps p η pos a b δ (fun k => φ k) d' ≤ ((ddExpEpsQ uq η pos a b δ φ d' : ℚ) : ℝ) := by
  have hb0 : 0 ≤ b := ha.trans hab
  have hb1 : b ≤ 1 := by linarith
  have hE := ddCoreE_le p h hu pos hb0 hb1 η φ d'
  have hD := (exp_enclosure δ (by rw [abs_of_nonneg hδ]; linarith)).2
  have hcF := eF_nonneg p
  have hVr := (Rat.cast_lt (K := ℝ)).mpr hV
  have hNr := (Rat.cast_le (K := ℝ)).mpr hN
  unfold ddExpEps ddExpEpsQ expZ expV
  cases pos with
  | true =>
    simp only [↓reduceIte] at hVr hNr ⊢
    push_cast at hVr hNr ⊢
    rw [cast_eFQ p h] at hNr ⊢
    have hZ := (exp_enclosure b (by rw [abs_of_nonneg hb0]; exact hb1)).2
    have hv := (exp_enclosure (a - δ) (by rw [abs_le]; constructor <;> linarith)).1
    push_cast at hv
    exact ddEps_real_le hcF hE hZ hv hVr hD hNr
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hVr hNr ⊢
    push_cast at hVr hNr ⊢
    rw [cast_eFQ p h] at hNr ⊢
    have hZ := (exp_enclosure (-a) (by rw [abs_neg, abs_of_nonneg ha]; linarith)).2
    have hv := (exp_enclosure (-b - δ) (by rw [abs_le]; constructor <;> linarith)).1
    push_cast at hZ hv
    exact ddEps_real_le hcF hE hZ hv hVr hD hNr

end ExpansionBounds
