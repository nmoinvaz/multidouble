import ExpansionBounds.Convex
import ExpansionBounds.GMono
import ExpansionBounds.LogThm

/-!
# The convex variant of Lemma 13's bounds

Theorem 42's proof (`thm:log`), paragraph "Convexity", evaluates the bounds with VecSum's second bound alone in
Lemma 13, `V_j = ū(1 + u)^{n-j} σ_{j-1}`, which is larger than the minimum of Theorem 9 (d) and linear in the level
bounds. `Vc`, `gPartsC` and `gErrC` are `Vb`, `gParts` and `gErr` with that `V_j`: they are at least the bounds of
Lemma 13 (`gErr_le_gErrC`, `gParts_le_gPartsC`), and they stay in the class `Cvx` of nonnegative, nondecreasing,
convex functions of `ℓ` when the level bounds, `Z̄` and `F` are in it (`gErrC_cvx`, `gPartsC_cvx`). The level bounds
of MUL, ADD and ADDF have no minimum and are in the class when the part bounds are (`mulX_cvx`, `pairX_cvx`,
`addfX_cvx`), so `G_MUL`, `G_ADD` and `G_ADDF` with that `V_j` (`GmulEC`, `GmulPC`, `GaddEC`, `GaddPC`, `GaddfEC`,
`GaddfPC`) are at least the paper's and keep the class.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) (n : ℕ)

/-- `V_j = ū(1 + u)^{n-j} σ_{j-1}`: VecSum's second bound alone, without the minimum with `X_{j-1}` -/
noncomputable def Vc (X : ℕ → ℝ) (j : ℕ) : ℝ := us p * (1 + u p) ^ (n - j) * sigmaX n X (j - 1)

/-- Lemma 13 (b)'s part bounds with `V_j` VecSum's second bound alone -/
noncomputable def gPartsC (X : ℕ → ℝ) (Zb Fb : ℝ) : ℕ → ℝ
  | 0 => (1 + u p) * (Zb + Fb + ∑ j ∈ Ioc 1 n, Vc p n X j)
  | i + 1 => if i + 1 < n then (1 + u p) * (u p * gPartsC X Zb Fb i + ∑ j ∈ Ioc (i + 1) n, Vc p n X j) else 0

/-- Lemma 13 (a)'s error bound with `V_j` VecSum's second bound alone -/
noncomputable def gErrC (X : ℕ → ℝ) (Zb Fb : ℝ) : ℝ :=
  u p ^ n * Zb + (1 + u p ^ n) * Fb + ∑ j ∈ Ioc 0 n, (u p ^ n + u p ^ (n + 1 - j)) * Vc p n X j

/-- The minimum of Theorem 9 (d) is at most its second bound. -/
theorem Vb_le_Vc (X : ℕ → ℝ) (j : ℕ) : Vb p n X j ≤ Vc p n X j :=
  min_le_right _ _

/-- Lemma 13 (a)'s bound is at most its convex variant. -/
theorem gErr_le_gErrC (X : ℕ → ℝ) (Zb Fb : ℝ) : gErr p n X Zb Fb ≤ gErrC p n X Zb Fb := by
  have hu := u_pos p
  simp only [gErr, gErrC]
  have h : ∑ j ∈ Ioc 0 n, (u p ^ n + u p ^ (n + 1 - j)) * Vb p n X j ≤
      ∑ j ∈ Ioc 0 n, (u p ^ n + u p ^ (n + 1 - j)) * Vc p n X j :=
    sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (Vb_le_Vc p n X j) (by positivity)
  linarith

/-- Lemma 13 (b)'s bounds are at most their convex variants. -/
theorem gParts_le_gPartsC (X : ℕ → ℝ) (Zb Fb : ℝ) : ∀ i, gParts p n X Zb Fb i ≤ gPartsC p n X Zb Fb i
  | 0 => by
    simp only [gParts, gPartsC]
    exact mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (sum_le_sum fun j _ => Vb_le_Vc p n X j)) (by linarith [u_pos p])
  | i + 1 => by
    simp only [gParts, gPartsC]
    split_ifs
    · exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (gParts_le_gPartsC X Zb Fb i) (u_pos p).le)
          (sum_le_sum fun j _ => Vb_le_Vc p n X j)) (by linarith [u_pos p])
    · exact le_rfl

/-! ### The class `Cvx` along Lemma 13 -/

variable {s : Set ℝ}

/-- `V_j` of level bounds in the class is in the class. -/
theorem Vc_cvx (hs : Convex ℝ s) {X : ℝ → ℕ → ℝ} (hX : ∀ m, Cvx s fun l => X l m) (j : ℕ) :
    Cvx s fun l => Vc p n (X l) j := by
  have hu := u_pos p
  simp only [Vc, sigmaX]
  exact (Cvx.sum hs _ fun m _ => hX m).const_mul (mul_nonneg (us_nonneg p) (by positivity))

/-- Lemma 13 (a)'s convex bound of level bounds, `Z̄` and `F` in the class is in the class. -/
theorem gErrC_cvx (hs : Convex ℝ s) {X : ℝ → ℕ → ℝ} (hX : ∀ m, Cvx s fun l => X l m) {Zb Fb : ℝ → ℝ}
    (hZ : Cvx s Zb) (hF : Cvx s Fb) : Cvx s fun l => gErrC p n (X l) (Zb l) (Fb l) := by
  have hu := u_pos p
  simp only [gErrC]
  exact ((hZ.const_mul (by positivity)).add (hF.const_mul (by positivity))).add
    (Cvx.sum hs _ fun j _ => (Vc_cvx p n hs hX j).const_mul (by positivity))

/-- Lemma 13 (b)'s convex bounds of level bounds, `Z̄` and `F` in the class are in the class. -/
theorem gPartsC_cvx (hs : Convex ℝ s) {X : ℝ → ℕ → ℝ} (hX : ∀ m, Cvx s fun l => X l m) {Zb Fb : ℝ → ℝ}
    (hZ : Cvx s Zb) (hF : Cvx s Fb) : ∀ i, Cvx s fun l => gPartsC p n (X l) (Zb l) (Fb l) i
  | 0 => by
    have hu := u_pos p
    simp only [gPartsC]
    exact ((hZ.add hF).add (Cvx.sum hs _ fun j _ => Vc_cvx p n hs hX j)).const_mul (by positivity)
  | i + 1 => by
    have hu := u_pos p
    simp only [gPartsC]
    split_ifs
    · exact (((gPartsC_cvx hs hX hZ hF i).const_mul hu.le).add
        (Cvx.sum hs _ fun j _ => Vc_cvx p n hs hX j)).const_mul (by positivity)
    · exact Cvx.const hs le_rfl

/-! ### Lemma 11's level bounds along the class -/

/-- `D_m` of inputs `A_m` in the class is in the class, for `T_k u < 1` below `m`. -/
theorem levD_cvx {A : ℝ → ℕ → ℝ} (hA : ∀ m, Cvx s fun l => A l m) (T : ℕ → ℕ) {uu : ℝ} (hu : 0 ≤ uu) (N : ℕ)
    (hT : ∀ m < N, (T m : ℝ) * uu < 1) : ∀ m ≤ N, Cvx s fun l => levD (A l) T uu m
  | 0, _ => by simpa only [levD] using hA 0
  | m + 1, hm => by
    simp only [levD]
    have h1 := hT m (by omega)
    exact (hA (m + 1)).add (((levD_cvx hA T hu N hT m (by omega)).const_mul
      (mul_nonneg (Nat.cast_nonneg _) hu)).div_const (by linarith))

variable {α β : ℝ → ℕ → ℝ}

/-- `P_m` of part bounds in the class is in the class. -/
theorem mulP_cvx (hs : Convex ℝ s) (hα : ∀ i, Cvx s fun l => α l i) (hβ : ∀ i, Cvx s fun l => β l i) (m : ℕ) :
    Cvx s fun l => mulP n (α l) (β l) m := by
  simp only [mulP]
  exact Cvx.sum hs _ fun i _ => Cvx.sum hs _ fun j _ =>
    Cvx.ite _ (fun _ => (hα i).mul (hβ j)) fun _ => Cvx.const hs le_rfl

/-- MUL's `A_m` of part bounds in the class is in the class. -/
theorem mulA_cvx (hs : Convex ℝ s) (hα : ∀ i, Cvx s fun l => α l i) (hβ : ∀ i, Cvx s fun l => β l i) (m : ℕ) :
    Cvx s fun l => mulA p n (α l) (β l) m := by
  have hu := u_pos p
  simp only [mulA]
  refine Cvx.ite _ (fun _ => ?_) fun _ => Cvx.ite _ (fun _ => ?_) fun _ => Cvx.const hs le_rfl
  · exact ((mulP_cvx n hs hα hβ m).const_mul (by positivity)).add
      (Cvx.ite _ (fun _ => Cvx.const hs le_rfl) fun _ => (mulP_cvx n hs hα hβ (m - 1)).const_mul hu.le)
  · exact (mulP_cvx n hs hα hβ n).add ((mulP_cvx n hs hα hβ (n - 1)).const_mul hu.le)

/-- MUL's level bounds `X_m` of part bounds in the class are in the class. -/
theorem mulX_cvx (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (hs : Convex ℝ s) (hα : ∀ i, Cvx s fun l => α l i)
    (hβ : ∀ i, Cvx s fun l => β l i) (m : ℕ) : Cvx s fun l => mulX p n (α l) (β l) m := by
  have hu := u_pos p
  simp only [mulX, levX]
  refine Cvx.ite _ (fun hm => ?_) fun _ => ?_
  · exact (levD_cvx (fun k => mulA_cvx p n hs hα hβ k) mulT hu.le n (mulT_u_lt p n hA3) m hm.le).div_const
      (by linarith [mulT_u_lt p n hA3 m hm])
  · exact (levD_cvx (fun k => mulA_cvx p n hs hα hβ k) mulT hu.le n (mulT_u_lt p n hA3) n le_rfl).div_const
      (by linarith [mulQ_u_lt p n hA3])

/-- MUL's `R` of part bounds in the class is in the class. -/
theorem mulR_cvx (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (hs : Convex ℝ s) (hα : ∀ i, Cvx s fun l => α l i)
    (hβ : ∀ i, Cvx s fun l => β l i) : Cvx s fun l => mulR p n (α l) (β l) := by
  simp only [mulR]
  exact (mulX_cvx p n hA3 hs hα hβ n).const_mul (mul_nonneg (Nat.cast_nonneg _) (u_pos p).le)

/-- MUL's `Δ` of part bounds in the class is in the class. -/
theorem mulDelta_cvx (hs : Convex ℝ s) (hα : ∀ i, Cvx s fun l => α l i) (hβ : ∀ i, Cvx s fun l => β l i) :
    Cvx s fun l => mulDelta n (α l) (β l) := by
  simp only [mulDelta]
  exact Cvx.sum hs _ fun i _ => Cvx.sum hs _ fun j _ =>
    Cvx.ite _ (fun _ => (hα i).mul (hβ j)) fun _ => Cvx.const hs le_rfl

/-! ### `G_MUL` with VecSum's second bound alone -/

/-- `G_MUL(α, β; Z̄)`'s error bound with VecSum's second bound alone -/
noncomputable def GmulEC (α β : ℕ → ℝ) (Zb : ℝ) : ℝ :=
  gErrC p n (mulX p n α β) Zb (mulR p n α β + mulDelta n α β)

/-- `G_MUL(α, β; Z̄)`'s part bounds with VecSum's second bound alone -/
noncomputable def GmulPC (α β : ℕ → ℝ) (Zb : ℝ) : ℕ → ℝ :=
  gPartsC p n (mulX p n α β) Zb (mulR p n α β + mulDelta n α β)

/-- `G_MUL`'s error bound is at most its convex variant. -/
theorem GmulE_le_GmulEC (a b : ℕ → ℝ) (Zb : ℝ) : GmulE p n a b Zb ≤ GmulEC p n a b Zb :=
  gErr_le_gErrC p n _ _ _

/-- `G_MUL`'s part bounds are at most their convex variants. -/
theorem GmulP_le_GmulPC (a b : ℕ → ℝ) (Zb : ℝ) (i : ℕ) : GmulP p n a b Zb i ≤ GmulPC p n a b Zb i :=
  gParts_le_gPartsC p n _ _ _ i

/-- The convex `G_MUL`'s error bound of part bounds and `Z̄` in the class is in the class. -/
theorem GmulEC_cvx (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (hs : Convex ℝ s) (hα : ∀ i, Cvx s fun l => α l i)
    (hβ : ∀ i, Cvx s fun l => β l i) {Zb : ℝ → ℝ} (hZ : Cvx s Zb) :
    Cvx s fun l => GmulEC p n (α l) (β l) (Zb l) := by
  simp only [GmulEC]
  exact gErrC_cvx p n hs (fun m => mulX_cvx p n hA3 hs hα hβ m) hZ
    ((mulR_cvx p n hA3 hs hα hβ).add (mulDelta_cvx n hs hα hβ))

/-- The convex `G_MUL`'s part bounds of part bounds and `Z̄` in the class are in the class. -/
theorem GmulPC_cvx (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (hs : Convex ℝ s) (hα : ∀ i, Cvx s fun l => α l i)
    (hβ : ∀ i, Cvx s fun l => β l i) {Zb : ℝ → ℝ} (hZ : Cvx s Zb) (i : ℕ) :
    Cvx s fun l => GmulPC p n (α l) (β l) (Zb l) i := by
  simp only [GmulPC]
  exact gPartsC_cvx p n hs (fun m => mulX_cvx p n hA3 hs hα hβ m) hZ
    ((mulR_cvx p n hA3 hs hα hβ).add (mulDelta_cvx n hs hα hβ)) i

/-! ### `G_ADD` and `G_ADDF` with VecSum's second bound alone -/

/-- ADD's `A_m` of `λ_m` in the class is in the class. -/
theorem pairA_cvx (hs : Convex ℝ s) {lam : ℝ → ℕ → ℝ} (hl : ∀ i, Cvx s fun l => lam l i) (m : ℕ) :
    Cvx s fun l => pairA p n (lam l) m := by
  have hu := u_pos p
  simp only [pairA]
  refine Cvx.ite _ (fun _ => ?_) fun _ => Cvx.ite _ (fun _ => (hl (n - 1)).const_mul hu.le) fun _ =>
    Cvx.const hs le_rfl
  exact ((hl m).const_mul (by positivity)).add
    (Cvx.ite _ (fun _ => Cvx.const hs le_rfl) fun _ => (hl (m - 1)).const_mul hu.le)

/-- ADD's level bounds `X_m` of `λ_m` in the class are in the class. -/
theorem pairX_cvx (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (hs : Convex ℝ s) {lam : ℝ → ℕ → ℝ}
    (hl : ∀ i, Cvx s fun l => lam l i) (m : ℕ) : Cvx s fun l => pairX p n (lam l) m := by
  have hu := u_pos p
  simp only [pairX, levX]
  refine Cvx.ite _ (fun hm => ?_) fun _ => ?_
  · exact (levD_cvx (fun k => pairA_cvx p n hs hl k) id hu.le n (pairT_u_lt p n hA3) m hm.le).div_const
      (by linarith [pairT_u_lt p n hA3 m hm])
  · exact (levD_cvx (fun k => pairA_cvx p n hs hl k) id hu.le n (pairT_u_lt p n hA3) n le_rfl).div_const
      (by linarith [pairQ_u_lt p n hA3])

/-- ADD's `R` of `λ_m` in the class is in the class. -/
theorem pairR_cvx (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (hs : Convex ℝ s) {lam : ℝ → ℕ → ℝ}
    (hl : ∀ i, Cvx s fun l => lam l i) : Cvx s fun l => pairR p n (lam l) := by
  simp only [pairR]
  exact (pairX_cvx p n hA3 hs hl n).const_mul (mul_nonneg (Nat.cast_nonneg _) (u_pos p).le)

/-- `G_ADD(α, β; Z̄)`'s error bound with VecSum's second bound alone -/
noncomputable def GaddEC (α β : ℕ → ℝ) (Zb : ℝ) : ℝ :=
  gErrC p n (pairX p n fun m => α m + β m) Zb (pairR p n fun m => α m + β m)

/-- `G_ADD(α, β; Z̄)`'s part bounds with VecSum's second bound alone -/
noncomputable def GaddPC (α β : ℕ → ℝ) (Zb : ℝ) : ℕ → ℝ :=
  gPartsC p n (pairX p n fun m => α m + β m) Zb (pairR p n fun m => α m + β m)

/-- `G_ADD`'s error bound is at most its convex variant. -/
theorem GaddE_le_GaddEC (a b : ℕ → ℝ) (Zb : ℝ) : GaddE p n a b Zb ≤ GaddEC p n a b Zb :=
  gErr_le_gErrC p n _ _ _

/-- `G_ADD`'s part bounds are at most their convex variants. -/
theorem GaddP_le_GaddPC (a b : ℕ → ℝ) (Zb : ℝ) (i : ℕ) : GaddP p n a b Zb i ≤ GaddPC p n a b Zb i :=
  gParts_le_gPartsC p n _ _ _ i

/-- The convex `G_ADD`'s error bound of part bounds and `Z̄` in the class is in the class. -/
theorem GaddEC_cvx (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (hs : Convex ℝ s) (hα : ∀ i, Cvx s fun l => α l i)
    (hβ : ∀ i, Cvx s fun l => β l i) {Zb : ℝ → ℝ} (hZ : Cvx s Zb) :
    Cvx s fun l => GaddEC p n (α l) (β l) (Zb l) := by
  simp only [GaddEC]
  exact gErrC_cvx p n hs (fun m => pairX_cvx p n hA3 hs (fun i => (hα i).add (hβ i)) m) hZ
    (pairR_cvx p n hA3 hs fun i => (hα i).add (hβ i))

/-- The convex `G_ADD`'s part bounds of part bounds and `Z̄` in the class are in the class. -/
theorem GaddPC_cvx (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (hs : Convex ℝ s) (hα : ∀ i, Cvx s fun l => α l i)
    (hβ : ∀ i, Cvx s fun l => β l i) {Zb : ℝ → ℝ} (hZ : Cvx s Zb) (i : ℕ) :
    Cvx s fun l => GaddPC p n (α l) (β l) (Zb l) i := by
  simp only [GaddPC]
  exact gPartsC_cvx p n hs (fun m => pairX_cvx p n hA3 hs (fun i => (hα i).add (hβ i)) m) hZ
    (pairR_cvx p n hA3 hs fun i => (hα i).add (hβ i)) i

/-- ADDF's `ε_m` of part bounds and `λ_0` in the class is in the class. -/
theorem addfEps_cvx (hα : ∀ i, Cvx s fun l => α l i) {lam0 : ℝ → ℝ} (h0 : Cvx s lam0) :
    ∀ m, Cvx s fun l => addfEps p (α l) (lam0 l) m
  | 0 => by
    simp only [addfEps]
    exact h0.const_mul (u_pos p).le
  | m + 1 => by
    simp only [addfEps]
    exact ((hα (m + 1)).add (addfEps_cvx hα h0 m)).const_mul (u_pos p).le

/-- ADDF's level bounds `X_m` of part bounds and `λ_0` in the class are in the class. -/
theorem addfX_cvx (hs : Convex ℝ s) (hα : ∀ i, Cvx s fun l => α l i) {lam0 : ℝ → ℝ} (h0 : Cvx s lam0) (m : ℕ) :
    Cvx s fun l => addfX p n (α l) (lam0 l) m := by
  have hu := u_pos p
  simp only [addfX]
  exact Cvx.ite _ (fun _ => h0.const_mul (by positivity)) fun _ =>
    Cvx.ite _ (fun _ => ((hα m).add (addfEps_cvx p hα h0 (m - 1))).const_mul (by positivity)) fun _ =>
      Cvx.ite _ (fun _ => addfEps_cvx p hα h0 (n - 1)) fun _ => Cvx.const hs le_rfl

/-- `G_ADDF(α, 1; Z̄, λ_0)`'s error bound with VecSum's second bound alone -/
noncomputable def GaddfEC (α : ℕ → ℝ) (lam0 Zb : ℝ) : ℝ := gErrC p n (addfX p n α lam0) Zb 0

/-- `G_ADDF(α, 1; Z̄, λ_0)`'s part bounds with VecSum's second bound alone -/
noncomputable def GaddfPC (α : ℕ → ℝ) (lam0 Zb : ℝ) : ℕ → ℝ := gPartsC p n (addfX p n α lam0) Zb 0

/-- `G_ADDF`'s error bound is at most its convex variant. -/
theorem GaddfE'_le_GaddfEC (a : ℕ → ℝ) (lam0 Zb : ℝ) : GaddfE' p n a lam0 Zb ≤ GaddfEC p n a lam0 Zb :=
  gErr_le_gErrC p n _ _ _

/-- `G_ADDF`'s part bounds are at most their convex variants. -/
theorem GaddfP'_le_GaddfPC (a : ℕ → ℝ) (lam0 Zb : ℝ) (i : ℕ) :
    GaddfP' p n a lam0 Zb i ≤ GaddfPC p n a lam0 Zb i :=
  gParts_le_gPartsC p n _ _ _ i

/-- The convex `G_ADDF`'s error bound of part bounds, `λ_0` and `Z̄` in the class is in the class. -/
theorem GaddfEC_cvx (hs : Convex ℝ s) (hα : ∀ i, Cvx s fun l => α l i) {lam0 Zb : ℝ → ℝ} (h0 : Cvx s lam0)
    (hZ : Cvx s Zb) : Cvx s fun l => GaddfEC p n (α l) (lam0 l) (Zb l) := by
  simp only [GaddfEC]
  exact gErrC_cvx p n hs (fun m => addfX_cvx p n hs hα h0 m) hZ (Cvx.const hs le_rfl)

/-- The convex `G_ADDF`'s part bounds of part bounds, `λ_0` and `Z̄` in the class are in the class. -/
theorem GaddfPC_cvx (hs : Convex ℝ s) (hα : ∀ i, Cvx s fun l => α l i) {lam0 Zb : ℝ → ℝ} (h0 : Cvx s lam0)
    (hZ : Cvx s Zb) (i : ℕ) : Cvx s fun l => GaddfPC p n (α l) (lam0 l) (Zb l) i := by
  simp only [GaddfPC]
  exact gPartsC_cvx p n hs (fun m => addfX_cvx p n hs hα h0 m) hZ (Cvx.const hs le_rfl) i

/-! ### Horner's rule with VecSum's second bound alone -/

/-- Lemma 33's bounds `(e_{d-j}, π^{(d-j)})` with VecSum's second bound alone in each `G_MUL` and `G_ADD` -/
noncomputable def hornerBC (πz : ℕ → ℝ) (zb εz η : ℝ) (Fk : ℕ → ℕ → ℝ) (φ v : ℕ → ℝ) (d : ℕ) :
    ℕ → ℝ × (ℕ → ℝ)
  | 0 => (φ d, fun i => |Fk d i|)
  | j + 1 =>
    let k := d - (j + 1)
    let e1 := (hornerBC πz zb εz η Fk φ v d j).1
    let π1 := (hornerBC πz zb εz η Fk φ v d j).2
    let Zm := (1 + εz) * zb * (v (k + 1) + e1)
    let μ := fun i => GmulPC p n πz π1 Zm i + η
    let D := (1 + εz) * zb * e1 + εz * zb * v (k + 1) + φ k + (GmulEC p n πz π1 Zm + n * η)
    (D + GaddEC p n (fun i => |Fk k i|) μ (v k + D), GaddPC p n (fun i => |Fk k i|) μ (v k + D))

/-- Horner's convex bounds are in the class when `π^z`, `z̄` and the `v_k` are, for constant `ε_z`, `η`, `φ_k ≥ 0`. -/
theorem hornerBC_cvx (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (hs : Convex ℝ s) {πz : ℝ → ℕ → ℝ}
    (hπ : ∀ i, Cvx s fun l => πz l i) {zb : ℝ → ℝ} (hz : Cvx s zb) {εz η : ℝ} (hε : 0 ≤ εz) (hη : 0 ≤ η)
    (Fk : ℕ → ℕ → ℝ) {φ : ℕ → ℝ} (hφ : ∀ k, 0 ≤ φ k) {v : ℝ → ℕ → ℝ} (hv : ∀ k, Cvx s fun l => v l k) (d : ℕ) :
    ∀ j, (Cvx s fun l => (hornerBC p n (πz l) (zb l) εz η Fk φ (v l) d j).1) ∧
      ∀ i, Cvx s fun l => (hornerBC p n (πz l) (zb l) εz η Fk φ (v l) d j).2 i
  | 0 => ⟨by simpa only [hornerBC] using Cvx.const hs (hφ d),
      fun i => by simpa only [hornerBC] using Cvx.const hs (abs_nonneg (Fk d i))⟩
  | j + 1 => by
    obtain ⟨h1, h2⟩ := hornerBC_cvx hA3 hs hπ hz hε hη Fk hφ hv d j
    have hZm := (hz.const_mul (by linarith : (0 : ℝ) ≤ 1 + εz)).mul ((hv (d - (j + 1) + 1)).add h1)
    have hμ := fun i => (GmulPC_cvx p n hA3 hs hπ h2 hZm i).add (Cvx.const hs hη)
    have hD := ((((hz.const_mul (by linarith : (0 : ℝ) ≤ 1 + εz)).mul h1).add
      ((hz.const_mul hε).mul (hv (d - (j + 1) + 1)))).add (Cvx.const hs (hφ (d - (j + 1))))).add
      ((GmulEC_cvx p n hA3 hs hπ h2 hZm).add (Cvx.const hs (mul_nonneg (Nat.cast_nonneg n) hη)))
    have hF : ∀ i, Cvx s fun _ : ℝ => |Fk (d - (j + 1)) i| := fun i => Cvx.const hs (abs_nonneg _)
    refine ⟨?_, fun i => ?_⟩
    · simp only [hornerBC]
      exact hD.add (GaddEC_cvx p n hA3 hs hF hμ ((hv (d - (j + 1))).add hD))
    · simp only [hornerBC]
      exact GaddPC_cvx p n hA3 hs hF hμ ((hv (d - (j + 1))).add hD) i

/-- Lemma 33's bounds are at most their convex variants, for nonnegative `π^z`, `z̄`, `ε_z`, `η`, `φ_k` and `v_k`. -/
theorem hornerB_le_hornerBC (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {πz : ℕ → ℝ} (hπ0 : ∀ i, 0 ≤ πz i) {zb εz η : ℝ}
    (hzb : 0 ≤ zb) (hε0 : 0 ≤ εz) (hη : 0 ≤ η) (Fk : ℕ → ℕ → ℝ) {φ v : ℕ → ℝ} (hφ : ∀ k, 0 ≤ φ k)
    (hv : ∀ k, 0 ≤ v k) (d : ℕ) : ∀ j,
    (hornerB p n πz zb εz η Fk φ v d j).1 ≤ (hornerBC p n πz zb εz η Fk φ v d j).1 ∧
      ∀ i, (hornerB p n πz zb εz η Fk φ v d j).2 i ≤ (hornerBC p n πz zb εz η Fk φ v d j).2 i
  | 0 => ⟨le_rfl, fun _ => le_rfl⟩
  | j + 1 => by
    obtain ⟨i1, i2⟩ := hornerB_le_hornerBC hA3 hπ0 hzb hε0 hη Fk hφ hv d j
    obtain ⟨-, n2⟩ := hornerB_nonneg p n hA3 hπ0 hzb hε0 hη Fk hφ hv d j
    have hc0 : 0 ≤ (1 + εz) * zb := mul_nonneg (by linarith) hzb
    have hZm : (1 + εz) * zb * (v (d - (j + 1) + 1) + (hornerB p n πz zb εz η Fk φ v d j).1) ≤
        (1 + εz) * zb * (v (d - (j + 1) + 1) + (hornerBC p n πz zb εz η Fk φ v d j).1) :=
      mul_le_mul_of_nonneg_left (by linarith) hc0
    obtain ⟨m1, m2⟩ := Gmul_mono p n hA3 hπ0 n2 (fun i => le_refl (πz i)) i2 hZm
    have m1' := m1.trans (GmulE_le_GmulEC p n _ _ _)
    have m2' := fun i => (m2 i).trans (GmulP_le_GmulPC p n _ _ _ i)
    have hD : (1 + εz) * zb * (hornerB p n πz zb εz η Fk φ v d j).1 + εz * zb * v (d - (j + 1) + 1) +
          φ (d - (j + 1)) + (GmulE p n πz (hornerB p n πz zb εz η Fk φ v d j).2
            ((1 + εz) * zb * (v (d - (j + 1) + 1) + (hornerB p n πz zb εz η Fk φ v d j).1)) + n * η) ≤
        (1 + εz) * zb * (hornerBC p n πz zb εz η Fk φ v d j).1 + εz * zb * v (d - (j + 1) + 1) +
          φ (d - (j + 1)) + (GmulEC p n πz (hornerBC p n πz zb εz η Fk φ v d j).2
            ((1 + εz) * zb * (v (d - (j + 1) + 1) + (hornerBC p n πz zb εz η Fk φ v d j).1)) + n * η) := by
      have a1 := mul_le_mul_of_nonneg_left i1 hc0
      linarith
    obtain ⟨g1, g2⟩ := Gadd_mono p n hA3 (fun i => le_refl |Fk (d - (j + 1)) i|)
      (fun i => add_le_add (m2' i) (le_refl η)) (add_le_add (le_refl (v (d - (j + 1)))) hD)
    exact ⟨add_le_add hD (g1.trans (GaddE_le_GaddEC p n _ _ _)),
      fun i => (g2 i).trans (GaddP_le_GaddPC p n _ _ _ i)⟩

end ExpansionBounds
