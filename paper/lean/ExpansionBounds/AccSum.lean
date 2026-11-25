import ExpansionBounds.AccK

/-!
# Theorem 27 for sums

"If all terms are ADDX": a deposit is the parts of its operand, within `ρ^l μ_k` with `μ_k = |a_0|`, nothing goes to
level `n`, and the parts sum to the term exactly. So the accumulator's lemma applies with `τ_l = ρ^l`, `τ_n = 0` and
`E_prod = 0`, and `|Z - x| ≤ u^n|Z| + c^X_K W` with `c^X_K = (1 + u^n)Ē_lev + Φ` at `W = 1`. `c^X_K` grows with `K`,
and its `Φ` is at most that of Theorem 27 for products, whose `τ_l` are larger.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) (n : ℕ)

/-- `τ_l = ρ^l` for `l < n` and `τ_n = 0`: the deposits of ADDX -/
noncomputable def accTauX (θ : ℝ) : ℕ → ℝ := fun l => if l < n then (θ * u p) ^ l else 0

theorem accTauX_nonneg {θ : ℝ} (hθ : 0 ≤ θ) (l : ℕ) : 0 ≤ accTauX p n θ l := by
  unfold accTauX
  split_ifs
  · exact pow_nonneg (mul_nonneg hθ (u_pos p).le) l
  · exact le_rfl

/-- ADDX's `τ_l` are at most those of Theorem 27 for products, `max(L_l u^l, ρ^l)` -/
theorem accTauX_le {θ : ℝ} (hθ : 0 ≤ θ) (l : ℕ) : accTauX p n θ l ≤ accTau p n θ l := by
  unfold accTauX
  split_ifs
  · exact le_max_right _ _
  · exact accTau_nonneg p n hθ l

/-- `S_m(k)` grows with the `τ_l` -/
theorem accSclosed_mono_tau {τ τ' : ℕ → ℝ} (hττ : ∀ l, τ l ≤ τ' l) {Γ uu : ℝ} (hΓ : 0 ≤ Γ) (hu : 0 ≤ uu)
    (m k : ℕ) : accSclosed τ 1 Γ uu m k ≤ accSclosed τ' 1 Γ uu m k := by
  unfold accSclosed
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun l _ => ?_) (mul_nonneg hΓ zero_le_one)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hττ l) (Nat.cast_nonneg _)) (pow_nonneg (mul_nonneg hΓ hu) _))
    (rise_nonneg _ (Nat.cast_nonneg k) _)

/-- `S_m(K)` in units of `W` for sums -/
noncomputable def accS1X (θ : ℝ) (K m : ℕ) : ℝ := accSclosed (accTauX p n θ) 1 (accGamma p n K) (u p) m K

/-- `Φ` in units of `W` for sums -/
noncomputable def accPhiX (θ : ℝ) (K : ℕ) : ℝ :=
  GaddfE p n (finishP p n (accS1X p n θ K) (n - 1)) (accS1X p n θ K n) 0

/-- `c^X_K`, the second term in units of `W` for sums: `(1 + u^n)Ē_lev + Φ` at `W = 1` -/
noncomputable def accCX (θ : ℝ) (K : ℕ) : ℝ :=
  (1 + u p ^ n) * accE (accTauX p n θ) 1 (accGamma p n K) (u p) n K + accPhiX p n θ K

theorem accS1X_nonneg {θ : ℝ} (hθ : 0 ≤ θ) {K : ℕ} (hK : ((n : ℝ) + 1) * K * u p < 1) (m : ℕ) :
    0 ≤ accS1X p n θ K m :=
  accSclosed_nonneg (accTauX_nonneg p n hθ) (accGamma_pos p n hK).le (u_pos p).le m K

theorem accS1X_le {θ : ℝ} (hθ : 0 ≤ θ) {K : ℕ} (hK : ((n : ℝ) + 1) * K * u p < 1) (m : ℕ) :
    accS1X p n θ K m ≤ accS1 p n θ K m :=
  accSclosed_mono_tau (accTauX_le p n hθ) (accGamma_pos p n hK).le (u_pos p).le m K

theorem accS1X_mono {θ : ℝ} (hθ : 0 ≤ θ) {K K' : ℕ} (hKK : K ≤ K') (hK' : ((n : ℝ) + 1) * K' * u p < 1) (m : ℕ) :
    accS1X p n θ K m ≤ accS1X p n θ K' m :=
  accSclosed_mono (accTauX_nonneg p n hθ) (accGamma_pos p n (acc_hK_of_le p n hKK hK')).le
    (accGamma_mono p n hKK hK') (u_pos p).le m hKK

theorem accPhiX_nonneg {θ : ℝ} (hθ : 0 ≤ θ) {K : ℕ} (hK : ((n : ℝ) + 1) * K * u p < 1) : 0 ≤ accPhiX p n θ K :=
  (Gaddf_nonneg p n (finishP_nonneg p n (accS1X_nonneg p n hθ hK) _) (accS1X_nonneg p n hθ hK n) le_rfl).1

/-- `Φ` for sums is at most `Φ` for products -/
theorem accPhiX_le {θ : ℝ} (hθ : 0 ≤ θ) {K : ℕ} (hK : ((n : ℝ) + 1) * K * u p < 1) :
    accPhiX p n θ K ≤ accPhi p n θ K :=
  GaddfE_mono p n (finishP_mono p n (accS1X_le p n hθ hK) _) (accS1X_le p n hθ hK n) le_rfl

/-- `Φ` for sums grows with `K` -/
theorem accPhiX_mono {θ : ℝ} (hθ : 0 ≤ θ) {K K' : ℕ} (hKK : K ≤ K') (hK' : ((n : ℝ) + 1) * K' * u p < 1) :
    accPhiX p n θ K ≤ accPhiX p n θ K' :=
  GaddfE_mono p n (finishP_mono p n (accS1X_mono p n hθ hKK hK') _) (accS1X_mono p n hθ hKK hK' n) le_rfl

/-- `c^X_K` grows with `K` -/
theorem accCX_mono {θ : ℝ} (hθ : 0 ≤ θ) {K K' : ℕ} (hKK : K ≤ K') (hK' : ((n : ℝ) + 1) * K' * u p < 1) :
    accCX p n θ K ≤ accCX p n θ K' := by
  have hu := u_pos p
  exact add_le_add (mul_le_mul_of_nonneg_left
    (accE_mono (accTauX_nonneg p n hθ) (accGamma_pos p n (acc_hK_of_le p n hKK hK')).le
      (accGamma_mono p n hKK hK') hu.le n hKK) (by positivity)) (accPhiX_mono p n hθ hKK hK')

variable [Prec_gt_0 p]

/-- the levels after `K` ADDX terms -/
noncomputable def accLevX (a : ℕ → ℕ → ℝ) (K : ℕ) : ℕ → ℝ :=
  (runOps p n (accOps n a (fun _ => false) K) LState.init).2.s

/-- Theorem 27 (`thm:acc`) when all terms are ADDX, of operands on `H(θ)`: then FINISH gives
`|Z - x| ≤ u^n|Z| + c^X_K W` with `W = ∑|a_0|` -/
theorem thm27_addx (hp : 1 < p) (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 < θ) (K : ℕ) (hK1 : 1 ≤ K)
    (hK : ((n : ℝ) + 1) * K * u p < 1) (a : ℕ → ℕ → ℝ) (ha : ∀ k ∈ Icc 1 K, ∀ i < n, F p (a k i))
    (hHa : ∀ k ∈ Icc 1 K, Htheta p n θ (a k)) :
    |∑ k ∈ Icc 1 K, ∑ i ∈ range n, a k i - ∑ i ∈ range n, finishR p n (accLevX p n a K) n i| ≤
      u p ^ n * |∑ k ∈ Icc 1 K, ∑ i ∈ range n, a k i| + accCX p n θ K * ∑ k ∈ Icc 1 K, |a k 0| := by
  obtain ⟨W, hWd⟩ : ∃ W, W = ∑ k ∈ Icc 1 K, |a k 0| := ⟨_, rfl⟩
  have hW : 0 ≤ W := by
    rw [hWd]
    exact sum_nonneg fun k _ => abs_nonneg _
  have ht : ∀ k ∈ Icc 1 K, ∀ l < n, F p (a k l) ∧ |a k l| ≤ accTauX p n θ l * |a k 0| := fun k hk l hl => by
    refine ⟨ha k hk l hl, ?_⟩
    unfold accTauX
    simp only [hl, ↓reduceIte]
    exact Htheta_le p n (hHa k hk) l hl
  have h := acc_finish p n hp hn K hK1 hK a (fun _ => false) (accTauX p n θ) (fun k => |a k 0|)
    (accTauX_nonneg p n hθ.le) (fun k => abs_nonneg _) ht (fun k _ h => by simp at h)
    (fun k => ∑ i ∈ range n, a k i) 0 (fun k _ => by simp) W hWd (fun m => W * accS1X p n θ K m)
    (fun m => (accSclosed_smul _ _ _ _ m K).symm)
  have hP : finishP p n (fun m => W * accS1X p n θ K m) (n - 1) =
      fun i => W * finishP p n (accS1X p n θ K) (n - 1) i := funext (finishP_smul p n _ hW _)
  have hPhi : GaddfE p n (finishP p n (fun m => W * accS1X p n θ K m) (n - 1)) (W * accS1X p n θ K n) 0 =
      W * accPhiX p n θ K := by
    rw [hP]
    have := GaddfE_smul p n (finishP p n (accS1X p n θ K) (n - 1)) (accS1X p n θ K n) 0 hW
    rwa [mul_zero] at this
  rw [hPhi, accE_smul] at h
  rw [← hWd]
  refine h.trans (le_of_eq ?_)
  unfold accCX accGamma
  ring

end ExpansionBounds
