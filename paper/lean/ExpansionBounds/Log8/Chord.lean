import ExpansionBounds.Log8.Args
import ExpansionBounds.LogChord

/-!
# Theorem 42 at `n = 8` and `p = 53`: a case on its interval of `ℓ`

`log8_chord`: for a run of `LOG_{8,6,43,4}` in a case whose `|ln x|` lies in `[ℓ₁, ℓ₂]`, the kernel's checks at
the two ends give `|y - ln x| ≤ 9.926u^8|ln x|`, plus `2^{-509}` where the checks are those of an interval from
`ℓ = 0`. It is `thm42_chord` with the start's bound `log8E`, `π^y` and `π^x` of the paper, the case's `b`, `δ` and
`π` any functions of `ℓ` in the class `Cvx` that are within the rational bounds of `Log8Leaf` at the ends, and
`log8_eval` at each end.
-/

namespace ExpansionBounds

open Finset Set

variable [Prec_gt_0 (53 : ℤ)]

/-- Theorem 42 (`thm:log`) at `n = 8` for a case on an interval `[ℓ₁, ℓ₂]` of `|ln x|`, from the kernel's checks at
its ends: the start within `E(|ln x|)` of `ln x`, the case's `b`, `δ` and `π` nonnegative, nondecreasing, convex
functions of `ℓ` that bound the run's `|r|`, `|r - r_e|` and `|r_i|` at `ℓ = |ln x|` and lie below the checks'
rational bounds at the ends, and a state above step (3)'s at each end: `|y - ln x| ≤ 9.926u^8|ln x|`, plus
`2^{-509}` for the checks of an interval from zero -/
theorem log8_chord {m : ℕ} {S₁ S₂ Sx Sp Sc : ℝ → ℝ} (hS₁ : Scl 53 ((exp8Eta1 m : ℚ) : ℝ) S₁)
    (hS₂ : Scl 53 ((exp8Eta : ℚ) : ℝ) S₂) (hSx : Scl 53 ((2 * exp8Eta : ℚ) : ℝ) Sx)
    (hSp : Scl 53 ((2 * exp8Eta : ℚ) : ℝ) Sp) (hSc : Scl 53 ((exp8Eta : ℚ) : ℝ) Sc) (x : ℕ → ℝ)
    (hx : ∀ i < 8, F 53 (x i)) (hX0 : 0 < ∑ i ∈ range 8, x i) (hH : Htheta 53 8 2 x) (y0 : ℕ → ℝ)
    (hy0 : ∀ i < 8, F 53 (y0 i)) {l₁ l₂ : ℚ} (h0 : 0 ≤ l₁)
    (hl : |Real.log (∑ i ∈ range 8, x i)| ∈ Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ)) {b δ : ℝ → ℝ} {π : ℝ → ℕ → ℝ}
    (hbc : Cvx (Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ)) b) (hδc : Cvx (Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ)) δ)
    (hπc : ∀ i, Cvx (Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ)) fun l => π l i)
    (hπy : ∀ i < 8, |y0 i| ≤
      logPiY 53 ((log8E0 : ℚ) : ℝ) ((log8E1 : ℚ) : ℝ) |Real.log (∑ i ∈ range 8, x i)| i)
    (hE : |∑ i ∈ range 8, y0 i - Real.log (∑ i ∈ range 8, x i)| ≤ log8E |Real.log (∑ i ∈ range 8, x i)|)
    (r : ℕ → ℝ) (hr : ∀ i < 8, F 53 (r i)) (k : ℤ)
    (hδ : |∑ i ∈ range 8, r i - (-∑ i ∈ range 8, y0 i - k * Real.log 2)| ≤
      δ |Real.log (∑ i ∈ range 8, x i)|)
    (a : ℚ) (ha : ((a : ℚ) : ℝ) ≤ |∑ i ∈ range 8, r i|)
    (hb : |∑ i ∈ range 8, r i| ≤ b |Real.log (∑ i ∈ range 8, x i)|)
    (hπ : ∀ i < 8, |r i| ≤ π |Real.log (∑ i ∈ range 8, x i)| i) (pos : Bool)
    (hsgn : if pos then 0 ≤ ∑ i ∈ range 8, r i else ∑ i ∈ range 8, r i ≤ 0) (e : ℤ)
    (hU : ∑ i ∈ range 8, |r i| < (2 : ℝ) ^ (e + 1)) (d' : ℕ) (hd : 1 ≤ d')
    (hF : ∀ k, ∀ i < 8, F 53 ((exp8F k i : ℚ) : ℝ))
    (hφF : ∀ k, |∑ i ∈ range 8, ((exp8F k i : ℚ) : ℝ) - invF k| ≤ ((exp8Phi k : ℚ) : ℝ))
    (hπx : ∀ i < 8, |Sx ((2 : ℝ) ^ k * x i)| ≤ logPiX 8 (2 * u 53) ((2 * exp8Eta : ℚ) : ℝ)
      (logXi ((8 : ℕ) * ((2 * exp8Eta : ℚ) : ℝ)) pos (log8E |Real.log (∑ i ∈ range 8, x i)|) ((a : ℚ) : ℝ)
        (b |Real.log (∑ i ∈ range 8, x i)|) (δ |Real.log (∑ i ∈ range 8, x i)|)) i)
    (hSx0 : 1 / 2 ≤ (2 : ℝ) ^ k * x 0 → (2 : ℝ) ^ k * x 0 ≤ 2 → Sx ((2 : ℝ) ^ k * x 0) = (2 : ℝ) ^ k * x 0)
    (eφ et ec : ℤ)
    (hUφ : ∑ i ∈ range 8, |logPhi 53 8 Sx k x i| < (2 : ℝ) ^ (eφ + 1))
    (hUt : ∑ i ∈ range 8, |expCore 53 8 S₁ S₂ e m r (fun k i => ((exp8F k i : ℚ) : ℝ)) d' i| < (2 : ℝ) ^ (et + 1))
    (hUc : ∑ i ∈ range 8, |logC 53 8 Sp 436 eφ et (logPhi 53 8 Sx k x)
      (expCore 53 8 S₁ S₂ e m r (fun k i => ((exp8F k i : ℚ) : ℝ)) d') i| < (2 : ℝ) ^ (ec + 1))
    (hF' : ∀ k, ∀ i < 8, F 53 ((log8F k i : ℚ) : ℝ))
    (hφ' : ∀ k, |∑ i ∈ range 8, ((log8F k i : ℚ) : ℝ) - logFe k| ≤ ((log8Phi k : ℚ) : ℝ))
    (hsh : Log8Shared) {k0 zero : Bool}
    -- the lower end
    {b₁ δ₁ bT₁ : ℚ} {pq₁ : List ℚ} {xi₁ xs₁ cs₁ xd₁ : ℚ} {ph₁ : List ℚ}
    (leaf₁ : Log8Leaf k0 pos m a b₁ δ₁ l₁ bT₁ pq₁ xi₁ xs₁ cs₁ xd₁ ph₁) (hb₁ : b ((l₁ : ℚ) : ℝ) ≤ ((b₁ : ℚ) : ℝ))
    (hδ₁ : δ ((l₁ : ℚ) : ℝ) ≤ ((δ₁ : ℚ) : ℝ)) (t₁ : ℚ × List ℚ)
    (ht₁ : Dom 8
      (core0C 53 8 (coreTC pos (coreBpC 8 m (b ((l₁ : ℚ) : ℝ)) ((exp8Eta1 m : ℚ) : ℝ)) 0)
        (2 * (8 : ℕ) * ((exp8Eta1 m : ℚ) : ℝ)) ((exp8Eta : ℚ) : ℝ)
        (corePiC m (π ((l₁ : ℚ) : ℝ)) ((exp8Eta1 m : ℚ) : ℝ)) (coreBpC 8 m (b ((l₁ : ℚ) : ℝ)) ((exp8Eta1 m : ℚ) : ℝ))
        (fun k i => ((exp8F k i : ℚ) : ℝ)) (fun k => ((exp8Phi k : ℚ) : ℝ)) d').1
      (core0C 53 8 (coreTC pos (coreBpC 8 m (b ((l₁ : ℚ) : ℝ)) ((exp8Eta1 m : ℚ) : ℝ)) 0)
        (2 * (8 : ℕ) * ((exp8Eta1 m : ℚ) : ℝ)) ((exp8Eta : ℚ) : ℝ)
        (corePiC m (π ((l₁ : ℚ) : ℝ)) ((exp8Eta1 m : ℚ) : ℝ)) (coreBpC 8 m (b ((l₁ : ℚ) : ℝ)) ((exp8Eta1 m : ℚ) : ℝ))
        (fun k i => ((exp8F k i : ℚ) : ℝ)) (fun k => ((exp8Phi k : ℚ) : ℝ)) d').2 t₁)
    {sm₁ : ℚ × List ℚ} (hsq₁ : log8SqRun pos m a b₁ m t₁ = sm₁) {sa₁ : (ℚ × ℚ) × (List ℚ × List ℚ)}
    (hA₁ : log8C4a pos m b₁ δ₁ l₁ xi₁ xs₁ ph₁ sm₁ = sa₁) {c4₁ : ℚ × List ℚ}
    (hB₁ : log8C4b pos m b₁ xi₁ cs₁ xd₁ ph₁ sm₁ sa₁ = c4₁) (hend₁ : Log8End zero l₁ cs₁ c4₁)
    -- the upper end
    {b₂ δ₂ bT₂ : ℚ} {pq₂ : List ℚ} {xi₂ xs₂ cs₂ xd₂ : ℚ} {ph₂ : List ℚ}
    (leaf₂ : Log8Leaf k0 pos m a b₂ δ₂ l₂ bT₂ pq₂ xi₂ xs₂ cs₂ xd₂ ph₂) (hb₂ : b ((l₂ : ℚ) : ℝ) ≤ ((b₂ : ℚ) : ℝ))
    (hδ₂ : δ ((l₂ : ℚ) : ℝ) ≤ ((δ₂ : ℚ) : ℝ)) (t₂ : ℚ × List ℚ)
    (ht₂ : Dom 8
      (core0C 53 8 (coreTC pos (coreBpC 8 m (b ((l₂ : ℚ) : ℝ)) ((exp8Eta1 m : ℚ) : ℝ)) 0)
        (2 * (8 : ℕ) * ((exp8Eta1 m : ℚ) : ℝ)) ((exp8Eta : ℚ) : ℝ)
        (corePiC m (π ((l₂ : ℚ) : ℝ)) ((exp8Eta1 m : ℚ) : ℝ)) (coreBpC 8 m (b ((l₂ : ℚ) : ℝ)) ((exp8Eta1 m : ℚ) : ℝ))
        (fun k i => ((exp8F k i : ℚ) : ℝ)) (fun k => ((exp8Phi k : ℚ) : ℝ)) d').1
      (core0C 53 8 (coreTC pos (coreBpC 8 m (b ((l₂ : ℚ) : ℝ)) ((exp8Eta1 m : ℚ) : ℝ)) 0)
        (2 * (8 : ℕ) * ((exp8Eta1 m : ℚ) : ℝ)) ((exp8Eta : ℚ) : ℝ)
        (corePiC m (π ((l₂ : ℚ) : ℝ)) ((exp8Eta1 m : ℚ) : ℝ)) (coreBpC 8 m (b ((l₂ : ℚ) : ℝ)) ((exp8Eta1 m : ℚ) : ℝ))
        (fun k i => ((exp8F k i : ℚ) : ℝ)) (fun k => ((exp8Phi k : ℚ) : ℝ)) d').2 t₂)
    {sm₂ : ℚ × List ℚ} (hsq₂ : log8SqRun pos m a b₂ m t₂ = sm₂) {sa₂ : (ℚ × ℚ) × (List ℚ × List ℚ)}
    (hA₂ : log8C4a pos m b₂ δ₂ l₂ xi₂ xs₂ ph₂ sm₂ = sa₂) {c4₂ : ℚ × List ℚ}
    (hB₂ : log8C4b pos m b₂ xi₂ cs₂ xd₂ ph₂ sm₂ sa₂ = c4₂) (hend₂ : Log8End zero l₂ cs₂ c4₂)
    (hc : b₂ + log8Eq l₂ + δ₂ ≤ 3 / 5) :
    |(logOp 53 8 Sx Sp Sc y0 x k (expCore 53 8 S₁ S₂ e m r (fun k i => ((exp8F k i : ℚ) : ℝ)) d') 436 eφ et ec
        (fun k i => ((log8F k i : ℚ) : ℝ)) 4).sum - Real.log (∑ i ∈ range 8, x i)| ≤
      (if zero then (1 : ℝ) / 2 ^ 509 else 0) + 9926 / 1000 * u 53 ^ 8 * |Real.log (∑ i ∈ range 8, x i)| := by
  have hu : ((red8U : ℚ) : ℝ) = u (53 : ℤ) := by unfold red8U; exact u_53_rat 53 rfl
  have hu53 : u (53 : ℤ) = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  have hA3 : (((8 : ℕ) : ℝ) ^ 2 + (8 : ℕ)) * u (53 : ℤ) < 1 := by rw [hu53]; norm_num
  obtain ⟨he0, he1, -⟩ := log8E_consts
  have he0' : (0 : ℝ) ≤ ((log8E0 : ℚ) : ℝ) := by exact_mod_cast he0
  have he1' : (0 : ℝ) ≤ ((log8E1 : ℚ) : ℝ) := by exact_mod_cast he1
  have hη0 : (0 : ℚ) ≤ exp8Eta := by unfold exp8Eta; positivity
  have hη2 : (0 : ℝ) ≤ ((2 * exp8Eta : ℚ) : ℝ) := by exact_mod_cast (by positivity : (0 : ℚ) ≤ 2 * exp8Eta)
  have hD0 : (0 : ℝ) ≤ ((8 : ℕ) : ℝ) * ((2 * exp8Eta : ℚ) : ℝ) := mul_nonneg (Nat.cast_nonneg 8) hη2
  have hl₁ : (0 : ℝ) ≤ ((l₁ : ℚ) : ℝ) := by exact_mod_cast h0
  have h12 : ((l₁ : ℚ) : ℝ) ≤ ((l₂ : ℚ) : ℝ) := hl.1.trans hl.2
  have hs : Convex ℝ (Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ)) := convex_Icc _ _
  have hpos : ∀ l ∈ Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ), 0 ≤ l := fun l h => hl₁.trans h.1
  have m₁ : ((l₁ : ℚ) : ℝ) ∈ Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ) := left_mem_Icc.mpr h12
  have m₂ : ((l₂ : ℚ) : ℝ) ∈ Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ) := right_mem_Icc.mpr h12
  -- the class of the paper's arguments
  have hEc : Cvx (Icc ((l₁ : ℚ) : ℝ) ((l₂ : ℚ) : ℝ)) log8E := logE_cvx hs hpos he0' he1'
  have hπyc := fun i => logPiY_cvx 53 hs hpos (by rw [hu53]; norm_num) he0' he1' i
  have hξc := logXi_cvx hs hD0 pos ((a : ℚ) : ℝ) hEc hbc hδc
  have hπxc := fun i => logPiX_cvx 8 hs (by rw [hu53]; norm_num : (0 : ℝ) ≤ 2 * u 53)
    (by rw [hu53]; norm_num : 2 * (2 * u 53) < 1) hη2 hξc i
  -- the two ends
  obtain ⟨e₁, -⟩ := log8_eval k0 pos m d' leaf₁ hsh (le_refl ((a : ℚ) : ℝ)) (hbc.nonneg _ m₁) hb₁
    (hδc.nonneg _ m₁) hδ₁ (log8E_nonneg hl₁) (log8E_le l₁) (fun i => (hπc i).nonneg _ m₁)
    (fun i _ => log8PiY_le l₁ i) t₁ ht₁ hsq₁ hA₁ hB₁ hend₁
  obtain ⟨e₂, hC⟩ := log8_eval k0 pos m d' leaf₂ hsh (le_refl ((a : ℚ) : ℝ)) (hbc.nonneg _ m₂) hb₂
    (hδc.nonneg _ m₂) hδ₂ (log8E_nonneg (hl₁.trans h12)) (log8E_le l₂) (fun i => (hπc i).nonneg _ m₂)
    (fun i _ => log8PiY_le l₂ i) t₂ ht₂ hsq₂ hA₂ hB₂ hend₂
  have hcast : ∀ l : ℚ, ((((if zero then 1 / 2 ^ 509 else 0) + 9926 / 1000 * red8U ^ 8 * l : ℚ)) : ℝ) =
      (if zero then (1 : ℝ) / 2 ^ 509 else 0) + 9926 / 1000 * u 53 ^ 8 * ((l : ℚ) : ℝ) := fun l => by
    push_cast
    rw [hu]
    split_ifs <;> simp
  rw [hcast] at e₁ e₂
  -- the hypotheses at the upper end
  obtain ⟨-, -, -, -, hbp₂, hbT₂, h2bT₂, -⟩ := leaf₂
  have h2m : (0 : ℝ) ≤ (2 : ℝ) ^ (-(m : ℤ)) := by positivity
  have hbpr : coreBpC 8 m (b ((l₂ : ℚ) : ℝ)) ((exp8Eta1 m : ℚ) : ℝ) ≤ ((bT₂ : ℚ) : ℝ) := by
    refine le_trans ?_ (Rat.cast_le.mpr hbp₂)
    simp only [coreBpC, log8Bp]
    push_cast
    linarith [mul_le_mul_of_nonneg_left hb₂ h2m]
  have hbT' : ((bT₂ : ℚ) : ℝ) < 1 := by exact_mod_cast hbT₂
  have hbd : coreBpC 8 m (b ((l₂ : ℚ) : ℝ)) ((exp8Eta1 m : ℚ) : ℝ) < (d' : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (d' : ℝ) := Nat.cast_nonneg d'
    linarith
  have hb2 : 0 < ((exp8Eta1 m : ℚ) : ℝ) →
      Real.exp (coreBpC 8 m (b ((l₂ : ℚ) : ℝ)) ((exp8Eta1 m : ℚ) : ℝ)) ≤ 2 := fun hpos1 => by
    have hm : m ≠ 0 := by
      intro h
      rw [h] at hpos1
      simp [exp8Eta1] at hpos1
    have h2 : (2 : ℚ) ≤ 2 ^ m := by
      calc (2 : ℚ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
    have hbq0 : (0 : ℚ) ≤ bT₂ := by
      have h1 : (0 : ℝ) ≤ coreBpC 8 m (b ((l₂ : ℚ) : ℝ)) ((exp8Eta1 m : ℚ) : ℝ) :=
        add_nonneg (mul_nonneg h2m (hbc.nonneg _ m₂)) (mul_nonneg (Nat.cast_nonneg 8) hpos1.le)
      exact_mod_cast h1.trans hbpr
    have hhalf : bT₂ ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_right h2 hbq0
      linarith
    have hhalf' : ((bT₂ : ℚ) : ℝ) ≤ 1 / 2 := by
      have h := (Rat.cast_le (K := ℝ)).mpr hhalf
      push_cast at h
      exact h
    obtain ⟨lA, -⟩ := log_two_600
    have hlA : (1 / 2 : ℝ) ≤ ((ln2A : ℚ) : ℝ) := by
      have h := (Rat.cast_le (K := ℝ)).mpr (by decide +kernel : (1 / 2 : ℚ) ≤ ln2A)
      push_cast at h
      exact h
    calc Real.exp (coreBpC 8 m (b ((l₂ : ℚ) : ℝ)) ((exp8Eta1 m : ℚ) : ℝ)) ≤ Real.exp (Real.log 2) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = 2 := Real.exp_log (by norm_num)
  have hc' : b ((l₂ : ℚ) : ℝ) + log8E ((l₂ : ℚ) : ℝ) + δ ((l₂ : ℚ) : ℝ) ≤ 3 / 5 := by
    have h1 := log8E_le l₂
    have h2 := (Rat.cast_le (K := ℝ)).mpr hc
    push_cast at h2
    linarith
  exact thm42_chord 53 8 (by norm_num) (by norm_num) hA3 hS₁ hS₂ hSx hSp hSc x hx hX0 2 (by norm_num)
    (by rw [hu53]; norm_num) hH y0 hy0 hl₁ hl hEc hbc hδc hπyc hπc hπxc hπy hE r hr k hδ ((a : ℚ) : ℝ) ha hb hc' hπ
    pos hsgn e hU m d' hd hbd hb2 (fun k i => ((exp8F k i : ℚ) : ℝ)) hF (fun k => ((exp8Phi k : ℚ) : ℝ)) hφF hπx
    hSx0 436 eφ et ec hUφ hUt hUc (fun k i => ((log8F k i : ℚ) : ℝ)) hF' (fun k => ((log8Phi k : ℚ) : ℝ)) hφ' 4
    (by norm_num) hC e₁ e₂

end ExpansionBounds
