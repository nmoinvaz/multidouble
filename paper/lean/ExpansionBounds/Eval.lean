import ExpansionBounds.AccSum

/-!
# The bounds in rational arithmetic, evaluated by the kernel

The constants of the appendix are rational: each is a recursion of sums, products, quotients, minima and maxima from
`u = 2^{-p}`, the `θ` of the ladder and natural numbers. Each definition here mirrors one of those bounds over `ℚ`,
with the same recursion, and its `cast_` theorem shows that the mirror's value, cast to `ℝ`, is the bound at the cast
arguments. An inequality between two such rationals is then decided by the kernel, which computes with
arbitrary-precision integers, in place of rewriting the real expression step by step. This file mirrors Lemma 13's
bounds, ADDF's, MUL's `L_m`, the accumulator's closed forms and the part bounds along FINISH.
-/

namespace ExpansionBounds

open Finset

/-! ### The mirrors -/

section Mirrors

variable (uq : ℚ) (n : ℕ)

/-- `ū = u/(1 + u)` -/
def usQ : ℚ := uq / (1 + uq)

/-- `σ_l = ∑_{m ≥ l} X_m` -/
def sigmaXQ (X : ℕ → ℚ) (l : ℕ) : ℚ := ∑ m ∈ Ico l (n + 1), X m

/-- `V_j = min(X_{j-1}, ū(1 + u)^{n-j} σ_{j-1})` -/
def VbQ (X : ℕ → ℚ) (j : ℕ) : ℚ := min (X (j - 1)) (usQ uq * (1 + uq) ^ (n - j) * sigmaXQ n X (j - 1))

/-- the part bounds of Lemma 13 (b) -/
def gPartsQ (X : ℕ → ℚ) (Zb Fb : ℚ) : ℕ → ℚ
  | 0 => (1 + uq) * (Zb + Fb + ∑ j ∈ Ioc 1 n, VbQ uq n X j)
  | i + 1 => if i + 1 < n then (1 + uq) * (uq * gPartsQ X Zb Fb i + ∑ j ∈ Ioc (i + 1) n, VbQ uq n X j) else 0

/-- the error bound of Lemma 13 (a) -/
def gErrQ (X : ℕ → ℚ) (Zb Fb : ℚ) : ℚ :=
  uq ^ n * Zb + (1 + uq ^ n) * Fb + ∑ j ∈ Ioc 0 n, (uq ^ n + uq ^ (n + 1 - j)) * VbQ uq n X j

/-- ADDF's carry bounds -/
def addfEpsQ (α : ℕ → ℚ) (lam0 : ℚ) : ℕ → ℚ
  | 0 => uq * lam0
  | m + 1 => uq * (α (m + 1) + addfEpsQ α lam0 m)

/-- ADDF's level bounds -/
def addfXQ (α : ℕ → ℚ) (lam0 : ℚ) (m : ℕ) : ℚ :=
  if m = 0 then (1 + uq) * lam0
  else if m < n then (1 + uq) * (α m + addfEpsQ uq α lam0 (m - 1))
  else if m = n then addfEpsQ uq α lam0 (n - 1) else 0

/-- `G_ADDF`'s error bound -/
def GaddfEQ (α : ℕ → ℚ) (β0 Zb : ℚ) : ℚ := gErrQ uq n (addfXQ uq n α (α 0 + β0)) Zb 0

/-- `G_ADDF`'s part bounds -/
def GaddfPQ (α : ℕ → ℚ) (β0 Zb : ℚ) : ℕ → ℚ := gPartsQ uq n (addfXQ uq n α (α 0 + β0)) Zb 0

/-- the part bounds along FINISH -/
def finishPQ (S : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0 => fun i => if i = 0 then S 0 else 0
  | l + 1 => GaddfPQ uq n (finishPQ S l) (S (l + 1)) (∑ m ∈ range (l + 2), S m)

/-- the rising factorial -/
def riseQ (k : ℚ) (r : ℕ) : ℚ := ∏ i ∈ range r, (k + i)

/-- `S_m(k)` in closed form -/
def accSclosedQ (τ : ℕ → ℚ) (W Γ uu : ℚ) (m k : ℕ) : ℚ :=
  Γ * W * ∑ l ∈ range (m + 1), (m.choose l : ℚ) * τ l * (Γ * uu) ^ (m - l) * riseQ k (m - l)

/-- `Ē_lev` -/
def accEQ (τ : ℕ → ℚ) (W Γ uu : ℚ) (n K : ℕ) : ℚ :=
  W * ∑ l ∈ range (n + 1), ((n + 1).choose l : ℚ) * τ l * (Γ * uu) ^ (n + 1 - l) * riseQ K (n + 1 - l)

/-- `d_m` of Theorem 14 -/
def thmDQ (Ah : ℕ → ℚ) (T : ℕ → ℕ) (θ : ℚ) : ℕ → ℚ
  | 0 => Ah 0
  | m + 1 => Ah (m + 1) + T m * thmDQ Ah T θ m / (θ * (1 - T m * uq))

/-- `L_m` of Theorem 14 -/
def thmLQ (Ah : ℕ → ℚ) (T : ℕ → ℕ) (θ : ℚ) (Q : ℕ) (m : ℕ) : ℚ :=
  if m < n then θ ^ m * thmDQ uq Ah T θ m / (1 - T m * uq) else θ ^ n * thmDQ uq Ah T θ n / (1 - Q * uq)

/-- `Â_m` for MUL -/
def hatAmulQ (θ : ℚ) (m : ℕ) : ℚ :=
  if m < n then (1 + uq) * (m + 1) + m / θ else if m = n then (n - 1 : ℚ) + n / θ else 0

/-- MUL's `L_m` -/
def mulLQ (θ : ℚ) (m : ℕ) : ℚ := thmLQ uq n (hatAmulQ uq n θ) mulT θ (n ^ 2 + n - 1) m

/-- `τ_l = max(L_l u^l, ρ^l)` -/
def accTauQ (θ : ℚ) : ℕ → ℚ := fun l => max (mulLQ uq n θ l * uq ^ l) ((θ * uq) ^ l)

/-- `Γ = 1/(1 - (n + 1)Ku)` -/
def accGammaQ (K : ℕ) : ℚ := 1 / (1 - ((n : ℚ) + 1) * K * uq)

/-- `S_m(K)` in units of `W` -/
def accS1Q (θ : ℚ) (K m : ℕ) : ℚ := accSclosedQ (accTauQ uq n θ) 1 (accGammaQ uq n K) uq m K

/-- `Φ` in units of `W` -/
def accPhiQ (θ : ℚ) (K : ℕ) : ℚ :=
  GaddfEQ uq n (finishPQ uq n (accS1Q uq n θ K) (n - 1)) (accS1Q uq n θ K n) 0

end Mirrors

/-! ### Each mirror, cast to `ℝ`, is its bound -/

section Casts

variable (p : ℤ) (n : ℕ) {uq : ℚ} (h : (uq : ℝ) = u p)

include h

theorem cast_us : ((usQ uq : ℚ) : ℝ) = us p := by
  simp [usQ, us, h]

omit h in
theorem cast_sigmaX (X : ℕ → ℚ) (l : ℕ) : ((sigmaXQ n X l : ℚ) : ℝ) = sigmaX n (fun m => (X m : ℝ)) l := by
  simp [sigmaXQ, sigmaX]

theorem cast_Vb (X : ℕ → ℚ) (j : ℕ) : ((VbQ uq n X j : ℚ) : ℝ) = Vb p n (fun m => (X m : ℝ)) j := by
  simp [VbQ, Vb, Rat.cast_min, cast_us p h, cast_sigmaX, h]

theorem cast_gParts (X : ℕ → ℚ) (Zb Fb : ℚ) :
    ∀ i, ((gPartsQ uq n X Zb Fb i : ℚ) : ℝ) = gParts p n (fun m => (X m : ℝ)) Zb Fb i
  | 0 => by simp [gPartsQ, gParts, cast_Vb p n h, h]
  | i + 1 => by
    simp only [gPartsQ, gParts]
    split_ifs
    · simp [cast_gParts X Zb Fb i, cast_Vb p n h, h]
    · simp

theorem cast_gErr (X : ℕ → ℚ) (Zb Fb : ℚ) :
    ((gErrQ uq n X Zb Fb : ℚ) : ℝ) = gErr p n (fun m => (X m : ℝ)) Zb Fb := by
  simp [gErrQ, gErr, cast_Vb p n h, h]

theorem cast_addfEps (α : ℕ → ℚ) (lam0 : ℚ) :
    ∀ m, ((addfEpsQ uq α lam0 m : ℚ) : ℝ) = addfEps p (fun i => (α i : ℝ)) lam0 m
  | 0 => by simp [addfEpsQ, addfEps, h]
  | m + 1 => by simp [addfEpsQ, addfEps, cast_addfEps α lam0 m, h]

theorem cast_addfX (α : ℕ → ℚ) (lam0 : ℚ) (m : ℕ) :
    ((addfXQ uq n α lam0 m : ℚ) : ℝ) = addfX p n (fun i => (α i : ℝ)) lam0 m := by
  simp only [addfXQ, addfX]
  split_ifs <;> simp [cast_addfEps p h, h]

theorem cast_GaddfE (α : ℕ → ℚ) (β0 Zb : ℚ) :
    ((GaddfEQ uq n α β0 Zb : ℚ) : ℝ) = GaddfE p n (fun i => (α i : ℝ)) β0 Zb := by
  have hX : (fun m => ((addfXQ uq n α (α 0 + β0) m : ℚ) : ℝ)) = addfX p n (fun i => (α i : ℝ)) ((α 0 : ℝ) + β0) := by
    funext m
    rw [cast_addfX p n h]
    push_cast
    rfl
  simp only [GaddfEQ, GaddfE, cast_gErr p n h, hX, Rat.cast_zero]

theorem cast_GaddfP (α : ℕ → ℚ) (β0 Zb : ℚ) (i : ℕ) :
    ((GaddfPQ uq n α β0 Zb i : ℚ) : ℝ) = GaddfP p n (fun i => (α i : ℝ)) β0 Zb i := by
  have hX : (fun m => ((addfXQ uq n α (α 0 + β0) m : ℚ) : ℝ)) = addfX p n (fun i => (α i : ℝ)) ((α 0 : ℝ) + β0) := by
    funext m
    rw [cast_addfX p n h]
    push_cast
    rfl
  simp only [GaddfPQ, GaddfP, cast_gParts p n h, hX, Rat.cast_zero]

theorem cast_finishP (S : ℕ → ℚ) :
    ∀ l i, ((finishPQ uq n S l i : ℚ) : ℝ) = finishP p n (fun m => (S m : ℝ)) l i
  | 0, i => by
    simp only [finishPQ, finishP]
    split_ifs <;> simp
  | l + 1, i => by
    have hP : (fun i => ((finishPQ uq n S l i : ℚ) : ℝ)) = finishP p n (fun m => (S m : ℝ)) l :=
      funext (cast_finishP S l)
    simp only [finishPQ, finishP, cast_GaddfP p n h, hP, Rat.cast_sum]

omit h in
theorem cast_rise (k : ℚ) (r : ℕ) : ((riseQ k r : ℚ) : ℝ) = rise (k : ℝ) r := by
  simp [riseQ, rise]

omit h in
theorem cast_accSclosed (τ : ℕ → ℚ) (W Γ uu : ℚ) (m k : ℕ) :
    ((accSclosedQ τ W Γ uu m k : ℚ) : ℝ) = accSclosed (fun l => (τ l : ℝ)) W Γ uu m k := by
  simp [accSclosedQ, accSclosed, cast_rise]

omit h in
theorem cast_accE (τ : ℕ → ℚ) (W Γ uu : ℚ) (n K : ℕ) :
    ((accEQ τ W Γ uu n K : ℚ) : ℝ) = accE (fun l => (τ l : ℝ)) W Γ uu n K := by
  simp [accEQ, accE, cast_rise]

theorem cast_thmD (Ah : ℕ → ℚ) (T : ℕ → ℕ) (θ : ℚ) :
    ∀ m, ((thmDQ uq Ah T θ m : ℚ) : ℝ) = thmD p (fun k => (Ah k : ℝ)) T θ m
  | 0 => by simp [thmDQ, thmD]
  | m + 1 => by simp [thmDQ, thmD, cast_thmD Ah T θ m, h]

theorem cast_thmL (Ah : ℕ → ℚ) (T : ℕ → ℕ) (θ : ℚ) (Q m : ℕ) :
    ((thmLQ uq n Ah T θ Q m : ℚ) : ℝ) = thmL p n (fun k => (Ah k : ℝ)) T θ Q m := by
  simp only [thmLQ, thmL]
  split_ifs <;> simp [cast_thmD p h, h]

theorem cast_hatAmul (θ : ℚ) (m : ℕ) : ((hatAmulQ uq n θ m : ℚ) : ℝ) = hatAmul p n θ m := by
  simp only [hatAmulQ, hatAmul]
  split_ifs <;> simp [h]

theorem cast_mulL (θ : ℚ) (m : ℕ) : ((mulLQ uq n θ m : ℚ) : ℝ) = mulL p n θ m := by
  have hA : (fun k => ((hatAmulQ uq n θ k : ℚ) : ℝ)) = hatAmul p n θ := funext (cast_hatAmul p n h θ)
  simp only [mulLQ, mulL, cast_thmL p n h, hA]

theorem cast_accTau (θ : ℚ) (l : ℕ) : ((accTauQ uq n θ l : ℚ) : ℝ) = accTau p n θ l := by
  simp [accTauQ, accTau, Rat.cast_max, cast_mulL p n h, h]

theorem cast_accGamma (K : ℕ) : ((accGammaQ uq n K : ℚ) : ℝ) = accGamma p n K := by
  simp [accGammaQ, accGamma, h]

theorem cast_accS1 (θ : ℚ) (K m : ℕ) : ((accS1Q uq n θ K m : ℚ) : ℝ) = accS1 p n θ K m := by
  have hτ : (fun l => ((accTauQ uq n θ l : ℚ) : ℝ)) = accTau p n θ := funext (cast_accTau p n h θ)
  simp only [accS1Q, accS1, cast_accSclosed, hτ, cast_accGamma p n h, Rat.cast_one, h]

theorem cast_accPhi (θ : ℚ) (K : ℕ) : ((accPhiQ uq n θ K : ℚ) : ℝ) = accPhi p n θ K := by
  have hS : (fun m => ((accS1Q uq n θ K m : ℚ) : ℝ)) = accS1 p n θ K := funext (cast_accS1 p n h θ K)
  have hP : (fun i => ((finishPQ uq n (accS1Q uq n θ K) (n - 1) i : ℚ) : ℝ)) =
      finishP p n (accS1 p n θ K) (n - 1) := by
    funext i
    rw [cast_finishP p n h, hS]
  simp only [accPhiQ, accPhi, cast_GaddfE p n h, hP, cast_accS1 p n h, Rat.cast_zero]

end Casts

end ExpansionBounds
