import ExpansionBounds.AccThm

/-!
# Theorem 27's second term: `c_K W`, growing with `K`

Theorem 27's bound is `u^n|Z|` plus a second term, `(1 + u^n)(Ē_lev + E_prod) + Φ`. Each of its pieces is
homogeneous of degree one in `W`, the sum of the terms' leading sizes: `Ē_lev` and the `S_m(K)` by their closed forms,
`E_prod` as written, and `Φ` because `G_ADDF` is homogeneous along FINISH. So the second term is `c_K W`, with `c_K`
its value at `W = 1`. And `c_K` grows with `K`: `Γ = 1/(1 - (n + 1)Ku)` and the rising factorials `K^{(r)}` grow, and
`G_ADDF` grows with its operands' part bounds. `acc_bound.py` relies on both when it searches for the largest `K`
whose second term is below a threshold.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) (n : ℕ)

/-! ### `G_ADDF` scales with its operands and grows with them -/

theorem addfEps_smul (α : ℕ → ℝ) (lam0 c : ℝ) :
    ∀ m, addfEps p (fun i => c * α i) (c * lam0) m = c * addfEps p α lam0 m
  | 0 => by simp only [addfEps]; ring
  | m + 1 => by
    simp only [addfEps]
    rw [addfEps_smul α lam0 c m]
    ring

theorem addfX_smul (α : ℕ → ℝ) (lam0 c : ℝ) (m : ℕ) :
    addfX p n (fun i => c * α i) (c * lam0) m = c * addfX p n α lam0 m := by
  simp only [addfX, addfEps_smul]
  split_ifs <;> ring

theorem GaddfE_smul (α : ℕ → ℝ) (β0 Zb : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    GaddfE p n (fun i => c * α i) (c * β0) (c * Zb) = c * GaddfE p n α β0 Zb := by
  have hX : addfX p n (fun i => c * α i) (c * α 0 + c * β0) = fun m => c * addfX p n α (α 0 + β0) m := by
    funext m
    rw [← mul_add]
    exact addfX_smul p n α _ c m
  have h := gErr_smul p n (addfX p n α (α 0 + β0)) Zb 0 hc
  rw [mul_zero] at h
  simp only [GaddfE, hX]
  exact h

theorem GaddfP_smul (α : ℕ → ℝ) (β0 Zb : ℝ) {c : ℝ} (hc : 0 ≤ c) (i : ℕ) :
    GaddfP p n (fun i => c * α i) (c * β0) (c * Zb) i = c * GaddfP p n α β0 Zb i := by
  have hX : addfX p n (fun i => c * α i) (c * α 0 + c * β0) = fun m => c * addfX p n α (α 0 + β0) m := by
    funext m
    rw [← mul_add]
    exact addfX_smul p n α _ c m
  have h := gParts_smul p n (addfX p n α (α 0 + β0)) Zb 0 hc i
  rw [mul_zero] at h
  simp only [GaddfP, hX]
  exact h

theorem addfEps_mono {α α' : ℕ → ℝ} (hα : ∀ i, α i ≤ α' i) {lam0 lam0' : ℝ} (hl : lam0 ≤ lam0') :
    ∀ m, addfEps p α lam0 m ≤ addfEps p α' lam0' m
  | 0 => by
    simp only [addfEps]
    exact mul_le_mul_of_nonneg_left hl (u_pos p).le
  | m + 1 => by
    simp only [addfEps]
    exact mul_le_mul_of_nonneg_left (add_le_add (hα _) (addfEps_mono hα hl m)) (u_pos p).le

theorem addfX_mono {α α' : ℕ → ℝ} (hα : ∀ i, α i ≤ α' i) {lam0 lam0' : ℝ} (hl : lam0 ≤ lam0') (m : ℕ) :
    addfX p n α lam0 m ≤ addfX p n α' lam0' m := by
  have hu := u_pos p
  have he := addfEps_mono p hα hl
  simp only [addfX]
  split_ifs
  · exact mul_le_mul_of_nonneg_left hl (by linarith)
  · exact mul_le_mul_of_nonneg_left (add_le_add (hα _) (he _)) (by linarith)
  · exact he _
  · exact le_rfl

theorem sigmaX_mono {X X' : ℕ → ℝ} (hX : ∀ m, X m ≤ X' m) (l : ℕ) : sigmaX n X l ≤ sigmaX n X' l := by
  unfold sigmaX
  exact sum_le_sum fun m _ => hX m

theorem Vb_mono {X X' : ℕ → ℝ} (hX : ∀ m, X m ≤ X' m) (j : ℕ) : Vb p n X j ≤ Vb p n X' j :=
  min_le_min (hX _) (mul_le_mul_of_nonneg_left (sigmaX_mono n hX _)
    (mul_nonneg (us_nonneg p) (pow_nonneg (by linarith [u_pos p]) _)))

theorem gErr_mono {X X' : ℕ → ℝ} (hX : ∀ m, X m ≤ X' m) {Zb Zb' : ℝ} (hZ : Zb ≤ Zb') (Fb : ℝ) :
    gErr p n X Zb Fb ≤ gErr p n X' Zb' Fb := by
  have hu := u_pos p
  simp only [gErr]
  refine add_le_add (add_le_add (mul_le_mul_of_nonneg_left hZ (pow_nonneg hu.le _)) le_rfl)
    (sum_le_sum fun j _ => ?_)
  exact mul_le_mul_of_nonneg_left (Vb_mono p n hX j) (by positivity)

theorem gParts_mono {X X' : ℕ → ℝ} (hX : ∀ m, X m ≤ X' m) {Zb Zb' : ℝ} (hZ : Zb ≤ Zb') (Fb : ℝ) :
    ∀ i, gParts p n X Zb Fb i ≤ gParts p n X' Zb' Fb i
  | 0 => by
    simp only [gParts]
    exact mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add hZ le_rfl) (sum_le_sum fun j _ => Vb_mono p n hX j)) (by linarith [u_pos p])
  | i + 1 => by
    simp only [gParts]
    split_ifs
    · exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (gParts_mono hX hZ Fb i) (u_pos p).le)
          (sum_le_sum fun j _ => Vb_mono p n hX j)) (by linarith [u_pos p])
    · exact le_rfl

theorem GaddfE_mono {α α' : ℕ → ℝ} (hα : ∀ i, α i ≤ α' i) {β0 β0' : ℝ} (hβ : β0 ≤ β0') {Zb Zb' : ℝ}
    (hZ : Zb ≤ Zb') : GaddfE p n α β0 Zb ≤ GaddfE p n α' β0' Zb' :=
  gErr_mono p n (addfX_mono p n hα (add_le_add (hα 0) hβ)) hZ 0

theorem GaddfP_mono {α α' : ℕ → ℝ} (hα : ∀ i, α i ≤ α' i) {β0 β0' : ℝ} (hβ : β0 ≤ β0') {Zb Zb' : ℝ}
    (hZ : Zb ≤ Zb') (i : ℕ) : GaddfP p n α β0 Zb i ≤ GaddfP p n α' β0' Zb' i :=
  gParts_mono p n (addfX_mono p n hα (add_le_add (hα 0) hβ)) hZ 0 i

/-! ### The part bounds along FINISH -/

theorem finishP_smul (S : ℕ → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ∀ l i, finishP p n (fun m => c * S m) l i = c * finishP p n S l i
  | 0, i => by
    simp only [finishP]
    split_ifs <;> simp
  | l + 1, i => by
    have h : finishP p n (fun m => c * S m) l = fun i => c * finishP p n S l i := funext (finishP_smul S hc l)
    simp only [finishP, h, ← mul_sum]
    exact GaddfP_smul p n _ _ _ hc i

theorem finishP_mono {S S' : ℕ → ℝ} (hS : ∀ m, S m ≤ S' m) : ∀ l i, finishP p n S l i ≤ finishP p n S' l i
  | 0, i => by
    simp only [finishP]
    split_ifs
    · exact hS 0
    · exact le_rfl
  | l + 1, i => by
    simp only [finishP]
    exact GaddfP_mono p n (finishP_mono hS l) (hS _) (sum_le_sum fun m _ => hS m) i

theorem finishP_nonneg {S : ℕ → ℝ} (hS : ∀ m, 0 ≤ S m) : ∀ l i, 0 ≤ finishP p n S l i
  | 0, i => by
    simp only [finishP]
    split_ifs
    · exact hS 0
    · exact le_rfl
  | l + 1, i => by
    simp only [finishP]
    exact (Gaddf_nonneg p n (finishP_nonneg hS l) (hS _) (sum_nonneg fun m _ => hS m)).2 i

/-! ### The closed forms of the accumulator's lemma -/

theorem rise_mono {k k' : ℝ} (hk : 0 ≤ k) (hkk : k ≤ k') (r : ℕ) : rise k r ≤ rise k' r := by
  unfold rise
  exact Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => by linarith

/-- a term `t (Γu)^r k^{(r)}` grows with `Γ` and `k` -/
theorem acc_term_mono {t Γ Γ' uu : ℝ} (ht : 0 ≤ t) (hΓ : 0 ≤ Γ) (hΓΓ : Γ ≤ Γ') (hu : 0 ≤ uu) {k k' : ℕ}
    (hk : k ≤ k') (r : ℕ) : t * (Γ * uu) ^ r * rise k r ≤ t * (Γ' * uu) ^ r * rise k' r :=
  mul_le_mul
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hΓ hu) (mul_le_mul_of_nonneg_right hΓΓ hu) r) ht)
    (rise_mono (Nat.cast_nonneg k) (Nat.cast_le.mpr hk) r) (rise_nonneg _ (Nat.cast_nonneg k) r)
    (mul_nonneg ht (pow_nonneg (mul_nonneg (hΓ.trans hΓΓ) hu) r))

theorem acc_term_nonneg {t Γ uu : ℝ} (ht : 0 ≤ t) (hΓ : 0 ≤ Γ) (hu : 0 ≤ uu) (k r : ℕ) :
    0 ≤ t * (Γ * uu) ^ r * rise k r :=
  mul_nonneg (mul_nonneg ht (pow_nonneg (mul_nonneg hΓ hu) r)) (rise_nonneg _ (Nat.cast_nonneg k) r)

theorem accSclosed_smul (τ : ℕ → ℝ) (W Γ uu : ℝ) (m k : ℕ) :
    accSclosed τ W Γ uu m k = W * accSclosed τ 1 Γ uu m k := by
  unfold accSclosed
  ring

theorem accE_smul (τ : ℕ → ℝ) (W Γ uu : ℝ) (n K : ℕ) : accE τ W Γ uu n K = W * accE τ 1 Γ uu n K := by
  unfold accE
  ring

theorem accSclosed_nonneg {τ : ℕ → ℝ} (hτ : ∀ l, 0 ≤ τ l) {Γ uu : ℝ} (hΓ : 0 ≤ Γ) (hu : 0 ≤ uu) (m k : ℕ) :
    0 ≤ accSclosed τ 1 Γ uu m k := by
  unfold accSclosed
  exact mul_nonneg (mul_nonneg hΓ zero_le_one) (sum_nonneg fun l _ =>
    acc_term_nonneg (mul_nonneg (Nat.cast_nonneg _) (hτ l)) hΓ hu k _)

theorem accSclosed_mono {τ : ℕ → ℝ} (hτ : ∀ l, 0 ≤ τ l) {Γ Γ' uu : ℝ} (hΓ : 0 ≤ Γ) (hΓΓ : Γ ≤ Γ') (hu : 0 ≤ uu)
    (m : ℕ) {k k' : ℕ} (hk : k ≤ k') : accSclosed τ 1 Γ uu m k ≤ accSclosed τ 1 Γ' uu m k' := by
  unfold accSclosed
  exact mul_le_mul (mul_le_mul_of_nonneg_right hΓΓ zero_le_one)
    (sum_le_sum fun l _ => acc_term_mono (mul_nonneg (Nat.cast_nonneg _) (hτ l)) hΓ hΓΓ hu hk _)
    (sum_nonneg fun l _ => acc_term_nonneg (mul_nonneg (Nat.cast_nonneg _) (hτ l)) hΓ hu k _)
    (mul_nonneg (hΓ.trans hΓΓ) zero_le_one)

theorem accE_mono {τ : ℕ → ℝ} (hτ : ∀ l, 0 ≤ τ l) {Γ Γ' uu : ℝ} (hΓ : 0 ≤ Γ) (hΓΓ : Γ ≤ Γ') (hu : 0 ≤ uu)
    (n : ℕ) {k k' : ℕ} (hk : k ≤ k') : accE τ 1 Γ uu n k ≤ accE τ 1 Γ' uu n k' := by
  unfold accE
  exact mul_le_mul_of_nonneg_left
    (sum_le_sum fun l _ => acc_term_mono (mul_nonneg (Nat.cast_nonneg _) (hτ l)) hΓ hΓΓ hu hk _) zero_le_one

/-! ### The second term in units of `W` -/

/-- `Γ = 1/(1 - (n + 1)Ku)` -/
noncomputable def accGamma (K : ℕ) : ℝ := 1 / (1 - ((n : ℝ) + 1) * K * u p)

/-- `S_m(K)` in units of `W` -/
noncomputable def accS1 (θ : ℝ) (K m : ℕ) : ℝ := accSclosed (accTau p n θ) 1 (accGamma p n K) (u p) m K

/-- `Φ`, the bound of FINISH's last ADDF, in units of `W` -/
noncomputable def accPhi (θ : ℝ) (K : ℕ) : ℝ :=
  GaddfE p n (finishP p n (accS1 p n θ K) (n - 1)) (accS1 p n θ K n) 0

/-- `Ē_lev + E_prod` in units of `W` -/
noncomputable def accLevProd (θ : ℝ) (K : ℕ) : ℝ :=
  accE (accTau p n θ) 1 (accGamma p n K) (u p) n K +
    (((n ^ 2 + n - 1 : ℕ) : ℝ) * mulL p n θ n + thmDelta p n θ) * u p ^ (n + 1)

/-- `c_K`, Theorem 27's second term in units of `W`: `(1 + u^n)(Ē_lev + E_prod) + Φ` at `W = 1` -/
noncomputable def accC (θ : ℝ) (K : ℕ) : ℝ := (1 + u p ^ n) * accLevProd p n θ K + accPhi p n θ K

theorem accTau_nonneg {θ : ℝ} (hθ : 0 ≤ θ) (l : ℕ) : 0 ≤ accTau p n θ l :=
  le_max_of_le_right (pow_nonneg (mul_nonneg hθ (u_pos p).le) l)

theorem accGamma_pos {K : ℕ} (hK : ((n : ℝ) + 1) * K * u p < 1) : 0 < accGamma p n K := by
  unfold accGamma
  exact one_div_pos.mpr (by linarith)

theorem accGamma_mono {K K' : ℕ} (hKK : K ≤ K') (hK' : ((n : ℝ) + 1) * K' * u p < 1) :
    accGamma p n K ≤ accGamma p n K' := by
  have hu := u_pos p
  have hc : (K : ℝ) ≤ K' := Nat.cast_le.mpr hKK
  have hle : ((n : ℝ) + 1) * K * u p ≤ ((n : ℝ) + 1) * K' * u p :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by positivity)) hu.le
  unfold accGamma
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

/-- `(n + 1)Ku < 1` passes to a smaller `K` -/
theorem acc_hK_of_le {K K' : ℕ} (hKK : K ≤ K') (hK' : ((n : ℝ) + 1) * K' * u p < 1) :
    ((n : ℝ) + 1) * K * u p < 1 := by
  have hu := u_pos p
  have hc : (K : ℝ) ≤ K' := Nat.cast_le.mpr hKK
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by positivity)) hu.le) hK'

theorem accS1_nonneg {θ : ℝ} (hθ : 0 ≤ θ) {K : ℕ} (hK : ((n : ℝ) + 1) * K * u p < 1) (m : ℕ) :
    0 ≤ accS1 p n θ K m :=
  accSclosed_nonneg (accTau_nonneg p n hθ) (accGamma_pos p n hK).le (u_pos p).le m K

theorem accS1_mono {θ : ℝ} (hθ : 0 ≤ θ) {K K' : ℕ} (hKK : K ≤ K') (hK' : ((n : ℝ) + 1) * K' * u p < 1) (m : ℕ) :
    accS1 p n θ K m ≤ accS1 p n θ K' m :=
  accSclosed_mono (accTau_nonneg p n hθ) (accGamma_pos p n (acc_hK_of_le p n hKK hK')).le
    (accGamma_mono p n hKK hK') (u_pos p).le m hKK

theorem accPhi_nonneg {θ : ℝ} (hθ : 0 ≤ θ) {K : ℕ} (hK : ((n : ℝ) + 1) * K * u p < 1) : 0 ≤ accPhi p n θ K :=
  (Gaddf_nonneg p n (finishP_nonneg p n (accS1_nonneg p n hθ hK) _) (accS1_nonneg p n hθ hK n) le_rfl).1

/-- `Φ` grows with `K` -/
theorem accPhi_mono {θ : ℝ} (hθ : 0 ≤ θ) {K K' : ℕ} (hKK : K ≤ K') (hK' : ((n : ℝ) + 1) * K' * u p < 1) :
    accPhi p n θ K ≤ accPhi p n θ K' :=
  GaddfE_mono p n (finishP_mono p n (accS1_mono p n hθ hKK hK') _) (accS1_mono p n hθ hKK hK' n) le_rfl

/-- `Ē_lev + E_prod` grows with `K` -/
theorem accLevProd_mono {θ : ℝ} (hθ : 0 ≤ θ) {K K' : ℕ} (hKK : K ≤ K') (hK' : ((n : ℝ) + 1) * K' * u p < 1) :
    accLevProd p n θ K ≤ accLevProd p n θ K' :=
  add_le_add (accE_mono (accTau_nonneg p n hθ) (accGamma_pos p n (acc_hK_of_le p n hKK hK')).le
    (accGamma_mono p n hKK hK') (u_pos p).le n hKK) le_rfl

/-- `c_K` grows with `K` -/
theorem accC_mono {θ : ℝ} (hθ : 0 ≤ θ) {K K' : ℕ} (hKK : K ≤ K') (hK' : ((n : ℝ) + 1) * K' * u p < 1) :
    accC p n θ K ≤ accC p n θ K' := by
  have hu := u_pos p
  exact add_le_add (mul_le_mul_of_nonneg_left (accLevProd_mono p n hθ hKK hK') (by positivity))
    (accPhi_mono p n hθ hKK hK')

variable [Prec_gt_0 p]

/-- Theorem 27 (`thm:acc`) with its second term as `c_K W`: `|Z - x| ≤ u^n|Z| + c_K W` -/
theorem thm27_scaled (hp : 1 < p) (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (θ : ℝ) (hθ : 0 < θ) (K : ℕ)
    (hK1 : 1 ≤ K) (hK : ((n : ℝ) + 1) * K * u p < 1) (prod : ℕ → Bool) (a b : ℕ → ℕ → ℝ)
    (ha : ∀ k ∈ Icc 1 K, ∀ i < n, F p (a k i)) (hb : ∀ k ∈ Icc 1 K, prod k = true → ∀ j < n, F p (b k j))
    (hHa : ∀ k ∈ Icc 1 K, Htheta p n θ (a k)) (hHb : ∀ k ∈ Icc 1 K, prod k = true → Htheta p n θ (b k)) :
    |accZ n prod a b K - ∑ i ∈ range n, finishR p n (accLev p n prod a b K) n i| ≤
      u p ^ n * |accZ n prod a b K| + accC p n θ K * ∑ j ∈ Icc 1 K, accMu prod a b j := by
  have h := thm27 p n hp hn hA3 θ hθ K hK1 hK prod a b ha hb hHa hHb
  obtain ⟨W, hWd⟩ : ∃ W, W = ∑ j ∈ Icc 1 K, accMu prod a b j := ⟨_, rfl⟩
  have hW : 0 ≤ W := by
    rw [hWd]
    exact sum_nonneg fun k _ => by unfold accMu; split_ifs <;> exact abs_nonneg _
  have hS : accSK p n θ prod a b K = fun m => W * accS1 p n θ K m := by
    funext m
    rw [hWd]
    exact accSclosed_smul _ _ _ _ m K
  have hP : finishP p n (fun m => W * accS1 p n θ K m) (n - 1) = fun i => W * finishP p n (accS1 p n θ K) (n - 1) i :=
    funext (finishP_smul p n _ hW _)
  have hPhi : GaddfE p n (finishP p n (accSK p n θ prod a b K) (n - 1)) (accSK p n θ prod a b K n) 0 =
      W * accPhi p n θ K := by
    rw [hS, hP]
    have := GaddfE_smul p n (finishP p n (accS1 p n θ K) (n - 1)) (accS1 p n θ K n) 0 hW
    rwa [mul_zero] at this
  rw [hPhi, ← hWd, accE_smul] at h
  rw [← hWd]
  refine h.trans (le_of_eq ?_)
  unfold accC accLevProd accGamma
  ring

end ExpansionBounds
