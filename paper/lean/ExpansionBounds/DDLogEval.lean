import ExpansionBounds.DDLogCvx
import ExpansionBounds.DDExpEval

/-!
# Proposition 44 (`prop:ddexplog`): the bound of a case of `DD::ln` in rational arithmetic

The bound of the convex mode has `e^z` at six arguments. `ddLogEcX` and `ddLogBoundX` are `E_c` and the bound with
those exponentials as arguments, `X_1 = e^{b̂} - 1 - b̂`, `X_2 = e^{b̂}`, `X_3 = e^{E+δ} - 1`, `X_4 = e^E`,
`X_5 = e^δ - 1` and `X_6 = e^E - 1` for `b̂ = b + δ`, beside `t̄`, `φ̄` and `ξ`: the bound is in the class of
`Convex.lean` with all of them (`cvx_ddLogBoundX`), so it grows with each (`ddLogBoundX_le`, along the segment from
one set of arguments to a larger one). The mirrors over `ℚ` (`ddLogEcXQ`, `ddLogPQ`, `ddLogBoundXQ`) have the same
recursions, and `ddLogBoundCQ` takes each exponential from the upper end of the 16-term enclosure of `e^z`: cast to
`ℝ` it is at least the bound of the convex mode (`ddLogBoundC_le`), and `ddLogCCQ` at least its `C`.
-/

namespace ExpansionBounds

open Set

variable (p : ℤ)

/-- step (4)'s `E_c` with its exponentials given: `X_1 = e^{b̂} - 1 - b̂`, `X_2 = e^{b̂}`, `X_3 = e^{E+δ} - 1`,
`X_4 = e^E`, `X_5 = e^δ - 1` and `X_6 = e^E - 1` -/
noncomputable def ddLogEcX (D Dp φb tb Em ξ X1 X2 X3 X4 X5 X6 : ℝ) (B : ℤ) : ℝ :=
  let εφt := eP p * (φb * (tb + Em)) + Dp + (2 : ℝ) ^ (-B - 12) * max φb (tb + Em)
  let εs := eA p * (2 * X1 + X2 * X3 + Em + D)
  let Eδ := X4 * X5 + D * (1 + tb + Em)
  let εc := eA p * (X6 + ξ * Em + Eδ + εφt + εs)
  ξ * Em + Eδ + εφt + εs + εc

/-- the bound with `t̄`, `φ̄`, `ξ` and the exponentials given -/
noncomputable def ddLogBoundX (η ηx ηp ηc ℓ tb φb ξ b X1 X2 X3 X4 X5 X6 : ℝ) (φF : ℕ → ℝ) (d' : ℕ) (φ' : ℕ → ℝ)
    (q : ℕ) (B : ℤ) : ℝ :=
  let Em := ddCoreE p tb η b φF d'
  let Ec := ddLogEcX p (2 * ηx) (2 * ηp) φb tb Em ξ X1 X2 X3 X4 X5 X6 B
  let P := ddLogP p (2 * ηc) (X6 + Ec) Ec φ' q B
  eF p * (ℓ + P) + P

/-- `E_c` is `ddLogEcX` at its exponentials -/
theorem ddLogEc_eq_X (D Dp φb tb Em E δ b ξ : ℝ) (B : ℤ) :
    ddLogEc p D Dp φb tb Em E δ b ξ B = ddLogEcX p D Dp φb tb Em ξ (Real.exp (b + δ) - 1 - (b + δ))
      (Real.exp (b + δ)) (Real.exp (E + δ) - 1) (Real.exp E) (Real.exp δ - 1) (Real.exp E - 1) B := rfl

/-- the bound is `ddLogBoundX` at its exponentials -/
theorem ddLogBoundG_eq_X (η ηx ηp ηc ℓ E tb φb ξ b δ : ℝ) (φF : ℕ → ℝ) (d' : ℕ) (φ' : ℕ → ℝ) (q : ℕ) (B : ℤ) :
    ddLogBoundG p η ηx ηp ηc ℓ E tb φb ξ b δ φF d' φ' q B =
      ddLogBoundX p η ηx ηp ηc ℓ tb φb ξ b (Real.exp (b + δ) - 1 - (b + δ)) (Real.exp (b + δ))
        (Real.exp (E + δ) - 1) (Real.exp E) (Real.exp δ - 1) (Real.exp E - 1) φF d' φ' q B := rfl

variable {s : Set ℝ}

/-- `ddLogEcX` is in the class with its arguments -/
theorem cvx_ddLogEcX (hu : 4 * u p < 1) {φb tb Em ξ X1 X2 X3 X4 X5 X6 : ℝ → ℝ} (hφb : Cvx s φb) (htb : Cvx s tb)
    (hEm : Cvx s Em) (hξ : Cvx s ξ) (h1 : Cvx s X1) (h2 : Cvx s X2) (h3 : Cvx s X3) (h4 : Cvx s X4)
    (h5 : Cvx s X5) (h6 : Cvx s X6) {D Dp : ℝ} (hD : 0 ≤ D) (hDp : 0 ≤ Dp) (B : ℤ) :
    Cvx s fun x => ddLogEcX p D Dp (φb x) (tb x) (Em x) (ξ x) (X1 x) (X2 x) (X3 x) (X4 x) (X5 x) (X6 x) B := by
  have hs := hφb.convex.1
  have heA := eA_nonneg p hu
  have heP := eP_nonneg p
  have htE := htb.add hEm
  have hεφt := (((hφb.mul htE).const_mul heP).add (Cvx.const hs hDp)).add
    ((hφb.max htE).const_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (-B - 12)))
  have hεs := ((((h1.const_mul (by norm_num : (0 : ℝ) ≤ 2)).add (h2.mul h3)).add hEm).add
    (Cvx.const hs hD)).const_mul heA
  have hEδ := (h4.mul h5).add ((((Cvx.const hs zero_le_one).add htb).add hEm).const_mul hD)
  have hεc := ((((h6.add (hξ.mul hEm)).add hEδ).add hεφt).add hεs).const_mul heA
  exact (((((hξ.mul hEm).add hEδ).add hεφt).add hεs).add hεc).congr fun x _ => rfl

/-- `ddLogBoundX` is in the class with its arguments, where `b < d' + 2` and `C = X_6 + E_c < 1` -/
theorem cvx_ddLogBoundX (hu : 4 * u p < 1) {L tb φb ξ b X1 X2 X3 X4 X5 X6 : ℝ → ℝ} (hL : Cvx s L)
    (htb : Cvx s tb) (hφb : Cvx s φb) (hξ : Cvx s ξ) (hb : Cvx s b) (h1 : Cvx s X1) (h2 : Cvx s X2)
    (h3 : Cvx s X3) (h4 : Cvx s X4) (h5 : Cvx s X5) (h6 : Cvx s X6) {η ηx ηp ηc : ℝ} (hη : 0 ≤ η) (hηx : 0 ≤ ηx)
    (hηp : 0 ≤ ηp) (hηc : 0 ≤ ηc) {φF : ℕ → ℝ} (hφF : ∀ k, 0 ≤ φF k) (d' : ℕ) (hbd : ∀ x ∈ s, b x < d' + 2)
    {φ' : ℕ → ℝ} (hφ' : ∀ k, 0 ≤ φ' k) (q : ℕ) (B : ℤ)
    (hC : ∀ x ∈ s, X6 x + ddLogEcX p (2 * ηx) (2 * ηp) (φb x) (tb x) (ddCoreE p (tb x) η (b x) φF d') (ξ x)
      (X1 x) (X2 x) (X3 x) (X4 x) (X5 x) (X6 x) B < 1) :
    Cvx s fun x => ddLogBoundX p η ηx ηp ηc (L x) (tb x) (φb x) (ξ x) (b x) (X1 x) (X2 x) (X3 x) (X4 x) (X5 x)
      (X6 x) φF d' φ' q B := by
  have heF := eF_nonneg p
  have hEm := cvx_ddCoreE p hu htb hb hη hφF d' hbd
  have hEc := cvx_ddLogEcX p hu hφb htb hEm hξ h1 h2 h3 h4 h5 h6 (by linarith : (0 : ℝ) ≤ 2 * ηx)
    (by linarith : (0 : ℝ) ≤ 2 * ηp) B
  have hP := cvx_ddLogP p hu (h6.add hEc) hEc hC (by linarith : (0 : ℝ) ≤ 2 * ηc) hφ' q B
  exact (((hL.add hP).const_mul heF).add hP).congr fun x _ => rfl

/-- `ddLogBoundX` and its `C` grow with `ℓ`, `t̄`, `φ̄`, `ξ` and the exponentials, for nonnegative arguments with
`b < d' + 2` and `C < 1` at the larger ones -/
theorem ddLogBoundX_le (hu : 4 * u p < 1) {η ηx ηp ηc b : ℝ} {ℓ ℓ' tb tb' φb φb' ξ ξ' X1 X1' X2 X2' X3 X3' X4 X4'
    X5 X5' X6 X6' : ℝ} (hη : 0 ≤ η) (hηx : 0 ≤ ηx) (hηp : 0 ≤ ηp) (hηc : 0 ≤ ηc) (hb : 0 ≤ b) (l0 : 0 ≤ ℓ)
    (l1 : ℓ ≤ ℓ') (t0 : 0 ≤ tb) (t1 : tb ≤ tb') (p0 : 0 ≤ φb) (p1 : φb ≤ φb') (x0 : 0 ≤ ξ) (x1 : ξ ≤ ξ')
    (a0 : 0 ≤ X1) (a1 : X1 ≤ X1') (b0 : 0 ≤ X2) (b1 : X2 ≤ X2') (c0 : 0 ≤ X3) (c1 : X3 ≤ X3') (d0 : 0 ≤ X4)
    (d1 : X4 ≤ X4') (e0 : 0 ≤ X5) (e1 : X5 ≤ X5') (f0 : 0 ≤ X6) (f1 : X6 ≤ X6') {φF : ℕ → ℝ}
    (hφF : ∀ k, 0 ≤ φF k) (d' : ℕ) (hbd : b < d' + 2) {φ' : ℕ → ℝ} (hφ' : ∀ k, 0 ≤ φ' k) (q : ℕ) (B : ℤ)
    (hC : X6' + ddLogEcX p (2 * ηx) (2 * ηp) φb' tb' (ddCoreE p tb' η b φF d') ξ' X1' X2' X3' X4' X5' X6' B < 1) :
    ddLogBoundX p η ηx ηp ηc ℓ tb φb ξ b X1 X2 X3 X4 X5 X6 φF d' φ' q B ≤
        ddLogBoundX p η ηx ηp ηc ℓ' tb' φb' ξ' b X1' X2' X3' X4' X5' X6' φF d' φ' q B ∧
      X6 + ddLogEcX p (2 * ηx) (2 * ηp) φb tb (ddCoreE p tb η b φF d') ξ X1 X2 X3 X4 X5 X6 B ≤
        X6' + ddLogEcX p (2 * ηx) (2 * ηp) φb' tb' (ddCoreE p tb' η b φF d') ξ' X1' X2' X3' X4' X5' X6' B := by
  have hs : Convex ℝ (Icc (0 : ℝ) 1) := convex_Icc 0 1
  have sL := cvx_segment l0 l1
  have st := cvx_segment t0 t1
  have sp := cvx_segment p0 p1
  have sx := cvx_segment x0 x1
  have s1 := cvx_segment a0 a1
  have s2 := cvx_segment b0 b1
  have s3 := cvx_segment c0 c1
  have s4 := cvx_segment d0 d1
  have s5 := cvx_segment e0 e1
  have s6 := cvx_segment f0 f1
  have sb := Cvx.const hs hb
  have hCv := s6.add (cvx_ddLogEcX p hu sp st (cvx_ddCoreE p hu st sb hη hφF d' (fun _ _ => hbd)) sx s1 s2 s3 s4 s5
    s6 (by linarith : (0 : ℝ) ≤ 2 * ηx) (by linarith : (0 : ℝ) ≤ 2 * ηp) B)
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.mpr zero_le_one
  have hCt : ∀ t ∈ Icc (0 : ℝ) 1, X6 + (X6' - X6) * t + ddLogEcX p (2 * ηx) (2 * ηp) (φb + (φb' - φb) * t)
      (tb + (tb' - tb) * t) (ddCoreE p (tb + (tb' - tb) * t) η b φF d') (ξ + (ξ' - ξ) * t)
      (X1 + (X1' - X1) * t) (X2 + (X2' - X2) * t) (X3 + (X3' - X3) * t) (X4 + (X4' - X4) * t)
      (X5 + (X5' - X5) * t) (X6 + (X6' - X6) * t) B < 1 := fun t ht => by
    have h := hCv.mono ht h1 ht.2
    simp only [mul_one, add_sub_cancel] at h
    exact lt_of_le_of_lt h hC
  have hF := cvx_ddLogBoundX p hu sL st sp sx sb s1 s2 s3 s4 s5 s6 hη hηx hηp hηc hφF d' (fun _ _ => hbd) hφ' q B
    hCt
  have h := hF.zero_le_one.2
  have h' := hCv.zero_le_one.2
  simp only [mul_zero, add_zero, mul_one, add_sub_cancel] at h h'
  exact ⟨h, h'⟩

/-! ## The mirrors over `ℚ` -/

/-- `v_i = ∑_{l ≤ q - i} C^l/(i + l)` over `ℚ` -/
def ddLogVQ (C : ℚ) (q i : ℕ) : ℚ := ∑ l ∈ Finset.range (q + 1 - i), C ^ l / ((i + l : ℕ) : ℚ)

/-- `ddLogEcX` over `ℚ` -/
def ddLogEcXQ (uq D Dp φb tb Em ξ X1 X2 X3 X4 X5 X6 : ℚ) (B : ℤ) : ℚ :=
  let εφt := ePQ uq * (φb * (tb + Em)) + Dp + (2 : ℚ) ^ (-B - 12) * max φb (tb + Em)
  let εs := eAQ uq * (2 * X1 + X2 * X3 + Em + D)
  let Eδ := X4 * X5 + D * (1 + tb + Em)
  let εc := eAQ uq * (X6 + ξ * Em + Eδ + εφt + εs)
  ξ * Em + Eδ + εφt + εs + εc

/-- step (5)'s `P` over `ℚ` -/
def ddLogPQ (uq Dc C Ec : ℚ) (φ' : ℕ → ℚ) (q : ℕ) (B : ℤ) : ℚ :=
  let e2 := ddHornerBQ uq C Dc φ' (ddLogVQ C q) q (q - 2)
  let Zh := C * (ddLogVQ C q 2 + e2)
  let εh := ePQ uq * Zh + Dc
  let hb := Zh + εh
  let εg := eFQ uq * (1 + hb)
  let εr := ePQ uq * (C * (1 + hb + εg)) + Dc
  εr + C * (εg + εh + C * e2) + max (C ^ (q + 1) / (q + 1)) ((2 : ℚ) ^ (-B - 13) * C) / (1 - C) + Ec / (1 - C)

/-- `C = X_6 + E_c` over `ℚ` -/
def ddLogCXQ (uq η ηx ηp tb φb ξ b X1 X2 X3 X4 X5 X6 : ℚ) (φF : ℕ → ℚ) (d' : ℕ) (B : ℤ) : ℚ :=
  X6 + ddLogEcXQ uq (2 * ηx) (2 * ηp) φb tb (ddCoreEQ uq tb η b φF d') ξ X1 X2 X3 X4 X5 X6 B

/-- `ddLogBoundX` over `ℚ` -/
def ddLogBoundXQ (uq η ηx ηp ηc ℓ tb φb ξ b X1 X2 X3 X4 X5 X6 : ℚ) (φF : ℕ → ℚ) (d' : ℕ) (φ' : ℕ → ℚ) (q : ℕ)
    (B : ℤ) : ℚ :=
  let Em := ddCoreEQ uq tb η b φF d'
  let Ec := ddLogEcXQ uq (2 * ηx) (2 * ηp) φb tb Em ξ X1 X2 X3 X4 X5 X6 B
  let P := ddLogPQ uq (2 * ηc) (X6 + Ec) Ec φ' q B
  eFQ uq * (ℓ + P) + P

/-- `ddLogVQ`, cast to `ℝ`, is `v_i` -/
theorem cast_ddLogVQ (C : ℚ) (q i : ℕ) : ((ddLogVQ C q i : ℚ) : ℝ) = logV (C : ℝ) q i := by
  simp [ddLogVQ, logV]

variable {uq : ℚ} (h : (uq : ℝ) = u p)

include h in
/-- `ddLogEcXQ`, cast to `ℝ`, is `ddLogEcX` at the cast arguments -/
theorem cast_ddLogEcXQ (D Dp φb tb Em ξ X1 X2 X3 X4 X5 X6 : ℚ) (B : ℤ) :
    ((ddLogEcXQ uq D Dp φb tb Em ξ X1 X2 X3 X4 X5 X6 B : ℚ) : ℝ) =
      ddLogEcX p D Dp φb tb Em ξ X1 X2 X3 X4 X5 X6 B := by
  simp only [ddLogEcXQ, ddLogEcX]
  push_cast
  rw [cast_ePQ p h, cast_eAQ p h]

include h in
/-- `ddLogPQ`, cast to `ℝ`, is `P` at the cast arguments -/
theorem cast_ddLogPQ (Dc C Ec : ℚ) (φ' : ℕ → ℚ) (q : ℕ) (B : ℤ) :
    ((ddLogPQ uq Dc C Ec φ' q B : ℚ) : ℝ) = ddLogP p Dc C Ec (fun k => φ' k) q B := by
  have hv : (fun k => ((ddLogVQ C q k : ℚ) : ℝ)) = logV (C : ℝ) q := funext fun k => cast_ddLogVQ C q k
  simp only [ddLogPQ, ddLogP]
  push_cast
  rw [cast_ddHornerBQ p h, hv, cast_ePQ p h, cast_eFQ p h, cast_ddLogVQ]

include h in
/-- `ddLogCXQ`, cast to `ℝ`, is `C` at the cast arguments -/
theorem cast_ddLogCXQ (η ηx ηp tb φb ξ b X1 X2 X3 X4 X5 X6 : ℚ) (φF : ℕ → ℚ) (d' : ℕ) (B : ℤ) :
    ((ddLogCXQ uq η ηx ηp tb φb ξ b X1 X2 X3 X4 X5 X6 φF d' B : ℚ) : ℝ) =
      X6 + ddLogEcX p (2 * ηx) (2 * ηp) φb tb (ddCoreE p tb η b (fun k => φF k) d') ξ X1 X2 X3 X4 X5 X6 B := by
  unfold ddLogCXQ
  rw [Rat.cast_add, cast_ddLogEcXQ p h, cast_ddCoreEQ p h]
  push_cast
  rfl

include h in
/-- `ddLogBoundXQ`, cast to `ℝ`, is `ddLogBoundX` at the cast arguments -/
theorem cast_ddLogBoundXQ (η ηx ηp ηc ℓ tb φb ξ b X1 X2 X3 X4 X5 X6 : ℚ) (φF : ℕ → ℚ) (d' : ℕ) (φ' : ℕ → ℚ)
    (q : ℕ) (B : ℤ) :
    ((ddLogBoundXQ uq η ηx ηp ηc ℓ tb φb ξ b X1 X2 X3 X4 X5 X6 φF d' φ' q B : ℚ) : ℝ) =
      ddLogBoundX p η ηx ηp ηc ℓ tb φb ξ b X1 X2 X3 X4 X5 X6 (fun k => φF k) d' (fun k => φ' k) q B := by
  simp only [ddLogBoundXQ, ddLogBoundX]
  push_cast
  rw [cast_ddLogPQ p h, cast_eFQ p h]
  push_cast
  rw [cast_ddLogEcXQ p h, cast_ddCoreEQ p h]
  push_cast
  rfl

/-! ## The convex mode on the enclosure of `e^z` -/

/-- `t̄` of the convex mode over `ℚ`: `e^b - 1` from the enclosure for `r ≥ 0`, `b` for `r ≤ 0` -/
def ddTbCQ (pos : Bool) (b : ℚ) : ℚ := if pos then expUpQ b - 1 else b

/-- `ξ` over `ℚ`, on the enclosure -/
def ddXiQ (D : ℚ) (pos : Bool) (E a b δ : ℚ) : ℚ := (if pos then expUpQ (E + δ - a) else expUpQ (E + b + δ)) + D

/-- `φ̄` of the convex mode over `ℚ` -/
def ddPhiCQ (D : ℚ) (pos : Bool) (E a b δ : ℚ) : ℚ := max (ddXiQ D pos E a b δ - 1) (E + b + δ + D)

/-- `C` of the convex mode over `ℚ`, each exponential from the upper end of its enclosure -/
def ddLogCCQ (uq η ηx ηp E : ℚ) (pos : Bool) (a b δ : ℚ) (φF : ℕ → ℚ) (d' : ℕ) (B : ℤ) : ℚ :=
  ddLogCXQ uq η ηx ηp (ddTbCQ pos b) (ddPhiCQ (2 * ηx) pos E a b δ) (ddXiQ (2 * ηx) pos E a b δ) b
    (expUpQ (b + δ) - 1 - (b + δ)) (expUpQ (b + δ)) (expUpQ (E + δ) - 1) (expUpQ E) (expUpQ δ - 1) (expUpQ E - 1)
    φF d' B

/-- the bound of the convex mode over `ℚ`, each exponential from the upper end of its enclosure -/
def ddLogBoundCQ (uq η ηx ηp ηc ℓ E : ℚ) (pos : Bool) (a b δ : ℚ) (φF : ℕ → ℚ) (d' : ℕ) (φ' : ℕ → ℚ) (q : ℕ)
    (B : ℤ) : ℚ :=
  ddLogBoundXQ uq η ηx ηp ηc ℓ (ddTbCQ pos b) (ddPhiCQ (2 * ηx) pos E a b δ) (ddXiQ (2 * ηx) pos E a b δ) b
    (expUpQ (b + δ) - 1 - (b + δ)) (expUpQ (b + δ)) (expUpQ (E + δ) - 1) (expUpQ E) (expUpQ δ - 1) (expUpQ E - 1)
    φF d' φ' q B

/-- `ξ` is nonnegative and at most its mirror, for `0 ≤ a ≤ 1` and nonnegative `E`, `b`, `δ` with
`E + b + δ ≤ 1` -/
theorem ddXi_le {D E a b δ : ℚ} (hD : 0 ≤ D) (hE : 0 ≤ E) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hδ : 0 ≤ δ)
    (hs : E + b + δ ≤ 1) (pos : Bool) :
    0 ≤ logXi (D : ℝ) pos E a b δ ∧ logXi (D : ℝ) pos E a b δ ≤ ((ddXiQ D pos E a b δ : ℚ) : ℝ) := by
  have hDr : (0 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  unfold logXi ddXiQ
  cases pos with
  | true =>
    simp only [↓reduceIte]
    have e := (exp_enclosure (E + δ - a) (by rw [abs_le]; constructor <;> linarith)).2
    push_cast at e ⊢
    exact ⟨by linarith [Real.exp_pos ((E : ℝ) + δ - a)], by linarith⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have e := (exp_enclosure (E + b + δ) (by rw [abs_le]; constructor <;> linarith)).2
    push_cast at e ⊢
    exact ⟨by linarith [Real.exp_pos ((E : ℝ) + b + δ)], by linarith⟩

include h in
/-- the bound of the convex mode and its `C` are at most their mirrors' values: for nonnegative arguments with
`a ≤ 1` and `E + b + δ ≤ 1`, and the mirror's `C < 1` -/
theorem ddLogBoundC_le (hu : 4 * u p < 1) {η ηx ηp ηc ℓ E a b δ : ℚ} (hη : 0 ≤ η) (hηx : 0 ≤ ηx) (hηp : 0 ≤ ηp)
    (hηc : 0 ≤ ηc) (hℓ : 0 ≤ ℓ) (hE : 0 ≤ E) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hδ : 0 ≤ δ)
    (hs : E + b + δ ≤ 1) (pos : Bool) {φF : ℕ → ℚ} (hφF : ∀ k, 0 ≤ φF k) (d' : ℕ) {φ' : ℕ → ℚ}
    (hφ' : ∀ k, 0 ≤ φ' k) (q : ℕ) (B : ℤ) (hC : ddLogCCQ uq η ηx ηp E pos a b δ φF d' B < 1) :
    ddLogBoundC p η ηx ηp ηc ℓ E pos a b δ (fun k => φF k) d' (fun k => φ' k) q B ≤
        ((ddLogBoundCQ uq η ηx ηp ηc ℓ E pos a b δ φF d' φ' q B : ℚ) : ℝ) ∧
      ddLogCC p η ηx ηp E pos a b δ (fun k => φF k) d' B ≤ ((ddLogCCQ uq η ηx ηp E pos a b δ φF d' B : ℚ) : ℝ) := by
  have hηr : (0 : ℝ) ≤ (η : ℝ) := by exact_mod_cast hη
  have hηxr : (0 : ℝ) ≤ (ηx : ℝ) := by exact_mod_cast hηx
  have hηpr : (0 : ℝ) ≤ (ηp : ℝ) := by exact_mod_cast hηp
  have hηcr : (0 : ℝ) ≤ (ηc : ℝ) := by exact_mod_cast hηc
  have hℓr : (0 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hEr : (0 : ℝ) ≤ (E : ℝ) := by exact_mod_cast hE
  have hbr : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hδr : (0 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ
  have hsr : (E : ℝ) + b + δ ≤ 1 := by exact_mod_cast hs
  have hD : (0 : ℚ) ≤ 2 * ηx := by linarith
  -- `t̄`
  have t0 : 0 ≤ ddTbC pos (b : ℝ) := by
    unfold ddTbC
    split_ifs
    · linarith [Real.one_le_exp hbr]
    · exact hbr
  have t1 : ddTbC pos (b : ℝ) ≤ ((ddTbCQ pos b : ℚ) : ℝ) := by
    unfold ddTbC ddTbCQ
    cases pos with
    | true =>
      simp only [↓reduceIte]
      have e := (exp_enclosure b (by rw [abs_le]; constructor <;> linarith)).2
      push_cast
      linarith
    | false => simp
  -- `ξ` and `φ̄`
  obtain ⟨x0, x1'⟩ := ddXi_le hD hE ha ha1 hb hδ hs pos
  have x1 : logXi (2 * (ηx : ℝ)) pos E a b δ ≤ ((ddXiQ (2 * ηx) pos E a b δ : ℚ) : ℝ) := by
    have := x1'
    push_cast at this
    exact this
  have x0' : 0 ≤ logXi (2 * (ηx : ℝ)) pos E a b δ := by
    have := x0
    push_cast at this
    exact this
  have p0 : 0 ≤ ddPhiC (2 * (ηx : ℝ)) pos E a b δ := by
    unfold ddPhiC
    exact le_max_of_le_right (by linarith)
  have p1 : ddPhiC (2 * (ηx : ℝ)) pos E a b δ ≤ ((ddPhiCQ (2 * ηx) pos E a b δ : ℚ) : ℝ) := by
    unfold ddPhiC ddPhiCQ
    push_cast
    exact max_le_max (by linarith) le_rfl
  -- the exponentials
  have eb := (exp_enclosure (b + δ) (by rw [abs_le]; constructor <;> linarith)).2
  have eE := (exp_enclosure (E + δ) (by rw [abs_le]; constructor <;> linarith)).2
  have e4 := (exp_enclosure E (by rw [abs_le]; constructor <;> linarith)).2
  have e5 := (exp_enclosure δ (by rw [abs_le]; constructor <;> linarith)).2
  push_cast at eb eE
  have a0 : 0 ≤ Real.exp ((b : ℝ) + δ) - 1 - (b + δ) := by linarith [Real.add_one_le_exp ((b : ℝ) + δ)]
  have a1 : Real.exp ((b : ℝ) + δ) - 1 - (b + δ) ≤ ((expUpQ (b + δ) - 1 - (b + δ) : ℚ) : ℝ) := by
    push_cast
    linarith
  have b0 : 0 ≤ Real.exp ((b : ℝ) + δ) := (Real.exp_pos _).le
  have c0 : 0 ≤ Real.exp ((E : ℝ) + δ) - 1 := by linarith [Real.one_le_exp (by linarith : (0 : ℝ) ≤ (E : ℝ) + δ)]
  have c1 : Real.exp ((E : ℝ) + δ) - 1 ≤ ((expUpQ (E + δ) - 1 : ℚ) : ℝ) := by
    push_cast
    linarith
  have d0 : 0 ≤ Real.exp (E : ℝ) := (Real.exp_pos _).le
  have e0 : 0 ≤ Real.exp (δ : ℝ) - 1 := by linarith [Real.one_le_exp hδr]
  have e1 : Real.exp (δ : ℝ) - 1 ≤ ((expUpQ δ - 1 : ℚ) : ℝ) := by
    push_cast
    linarith
  have f0 : 0 ≤ Real.exp (E : ℝ) - 1 := by linarith [Real.one_le_exp hEr]
  have f1 : Real.exp (E : ℝ) - 1 ≤ ((expUpQ E - 1 : ℚ) : ℝ) := by
    push_cast
    linarith
  have hbd : (b : ℝ) < (d' : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (d' : ℝ) := Nat.cast_nonneg d'
    linarith
  have hCr := (Rat.cast_lt (K := ℝ)).mpr hC
  rw [ddLogCCQ, cast_ddLogCXQ p h, Rat.cast_one] at hCr
  have hφFr : ∀ k, (0 : ℝ) ≤ ((φF k : ℚ) : ℝ) := fun k => by exact_mod_cast hφF k
  have hφ'r : ∀ k, (0 : ℝ) ≤ ((φ' k : ℚ) : ℝ) := fun k => by exact_mod_cast hφ' k
  obtain ⟨m1, m2⟩ := ddLogBoundX_le p hu hηr hηxr hηpr hηcr hbr hℓr le_rfl t0 t1 p0 p1 x0' x1 a0 a1 b0 eb c0 c1 d0 e4
    e0 e1 f0 f1 hφFr d' hbd hφ'r q B hCr
  constructor
  · rw [ddLogBoundCQ, cast_ddLogBoundXQ p h]
    exact m1
  · rw [ddLogCCQ, cast_ddLogCXQ p h]
    exact m2

end ExpansionBounds
