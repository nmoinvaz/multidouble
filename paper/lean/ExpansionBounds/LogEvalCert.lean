import ExpansionBounds.LogEvalSteps

/-!
# The steps of LOG on a rational state

For the convex variant of Theorem 42's bound: `t̄_j` is at most its mirror (`coreTC_le`); from a state above
`(E_m, ψ_m)`, the two pieces of step (4) give a state above `logC4C`'s `(E_c, χ)` (`logC4C_le`); step (5)'s Horner's
rule, `c ⊗ h` and `ADDF(c ⊗ h, 1)` on a state above `(χ, C)` and its last product on bounds of `(χ, C)` give a state
above `logPC`'s `(P, ω_r)` (`logPC_le`); and from such a state the last ADD's mirror is at least `ε_y + P`
(`logEnd_le`). `logBoundC_cert` joins them with the squarings of `coreEC_cert`: from stored states that follow each
other by these steps, the last ADD's mirror is at least `logBoundC`, the convex `𝓔` of the case.
-/

namespace ExpansionBounds

open Finset

section Bounds

variable (p : ℤ) (n : ℕ) {uq : ℚ} (h : (uq : ℝ) = u p) {ρ : ℚ → ℚ} (hρ : ∀ q, q ≤ ρ q)

include hρ in
/-- The convex `t̄_j` is nonnegative and at most its mirror. -/
theorem coreTC_le {pos : Bool} {b' : ℝ} {bp : ℚ} (hb0 : 0 ≤ b') (hb : b' ≤ ((bp : ℚ) : ℝ)) (j : ℕ)
    (hj : 2 ^ j * bp ≤ 1) : 0 ≤ coreTC pos b' j ∧ coreTC pos b' j ≤ ((coreTCQ ρ pos bp j : ℚ) : ℝ) := by
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have hbp0 : (0 : ℚ) ≤ bp := by exact_mod_cast hb0.trans hb
  have hz0 : (0 : ℚ) ≤ 2 ^ j * bp := mul_nonneg (by positivity) hbp0
  have hle : (2 : ℝ) ^ j * b' ≤ (((2 ^ j * bp : ℚ)) : ℝ) := by
    push_cast
    exact mul_le_mul_of_nonneg_left hb h2.le
  have h0 : 0 ≤ (2 : ℝ) ^ j * b' := mul_nonneg h2.le hb0
  cases pos with
  | true =>
    simp only [coreTC, coreTCQ, ↓reduceIte]
    obtain ⟨-, e2⟩ := exp_enclosure (2 ^ j * bp) (by rw [abs_of_nonneg hz0]; exact hj)
    refine ⟨by linarith [Real.one_le_exp h0], le_trans ?_ (Rat.cast_le.mpr (hρ _))⟩
    push_cast at e2 hle ⊢
    linarith [Real.exp_le_exp.mpr hle]
  | false =>
    simp only [coreTC, coreTCQ, Bool.false_eq_true, ↓reduceIte]
    exact ⟨h0, hle.trans (Rat.cast_le.mpr (hρ _))⟩

include h hρ in
/-- LOG's step (4): from a state above `(E_m, ψ_m)`, its two pieces give a state above `logC4C`'s `(E_c, χ)`; `xs`,
`cs` and `xd` bound `2(e^{b̂} - 1 - b̂) + e^{b̂}(e^{E+δ} - 1)`, `e^E - 1` and `e^E(e^δ - 1)` -/
theorem logC4C_le (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {D η : ℝ} {Dq ηq : ℚ} (hD0 : 0 ≤ D)
    (hD : D ≤ ((Dq : ℚ) : ℝ)) (hη : η ≤ ((ηq : ℚ) : ℝ)) {πφ ψ : ℕ → ℝ} {πφq : ℕ → ℚ} (hπφ0 : ∀ i, 0 ≤ πφ i)
    (hπφ : ∀ i < n, πφ i ≤ ((πφq i : ℚ) : ℝ)) (hψ0 : ∀ i, 0 ≤ ψ i) {φb tb Em E δ b ξ : ℝ}
    {φbq tbq xs cs xd ξq : ℚ} (hφb0 : 0 ≤ φb) (hφb : φb ≤ ((φbq : ℚ) : ℝ)) (htb0 : 0 ≤ tb)
    (htb : tb ≤ ((tbq : ℚ) : ℝ)) (hEm0 : 0 ≤ Em)
    (hxs : 2 * (Real.exp (b + δ) - 1 - (b + δ)) + Real.exp (b + δ) * (Real.exp (E + δ) - 1) ≤ ((xs : ℚ) : ℝ))
    (hcs : Real.exp E - 1 ≤ ((cs : ℚ) : ℝ)) (hxd : Real.exp E * (Real.exp δ - 1) ≤ ((xd : ℚ) : ℝ))
    (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ ((ξq : ℚ) : ℝ)) (B : ℤ) (st0 : ℚ × List ℚ) (hst : Dom n Em ψ st0) :
    Dom n (logC4C p n D η πφ ψ φb tb Em E δ b ξ B).1 (logC4C p n D η πφ ψ φb tb Em E δ b ξ B).2
      (logC4bL uq n ρ Dq πφq tbq cs xd ξq st0 (logC4aL uq n ρ Dq ηq πφq φbq tbq xs B st0)) := by
  obtain ⟨s1, s2⟩ := hst
  have hφq0 : (0 : ℝ) ≤ ((φbq : ℚ) : ℝ) := hφb0.trans hφb
  have hDq0 : (0 : ℝ) ≤ ((Dq : ℚ) : ℝ) := hD0.trans hD
  have hξq0 : (0 : ℝ) ≤ ((ξq : ℚ) : ℝ) := hξ0.trans hξ
  have h2B : (0 : ℝ) ≤ (2 : ℝ) ^ (-B - 12) := by positivity
  simp only [logC4C, logC4bL]
  set sa := logC4aL uq n ρ Dq ηq πφq φbq tbq xs B st0 with hsa
  set Zp := φb * (tb + Em) with hZp
  set ν := fun i => GmulPC p n πφ ψ Zp i + η with hν
  set εφt := GmulEC p n πφ ψ Zp + n * η + (2 : ℝ) ^ (-B - 12) * max φb (tb + Em) with hεφt
  set Zs := 2 * (Real.exp (b + δ) - 1 - (b + δ)) + Real.exp (b + δ) * (Real.exp (E + δ) - 1) + Em + D with hZs
  set Eδ := Real.exp E * (Real.exp δ - 1) + D * (1 + tb + Em) with hEδ
  -- the first piece
  have hZpq : Zp ≤ ((φbq * (tbq + st0.1) : ℚ) : ℝ) := by
    push_cast
    exact mul_le_mul hφb (by linarith) (by linarith) hφq0
  obtain ⟨m1, m2⟩ := GmulC_le_mirror p n h hA3 (fun i _ => hπφ0 i) (fun i _ => hψ0 i) hπφ s2 hZpq
  have hmax : max φb (tb + Em) ≤ max ((φbq : ℚ) : ℝ) (((tbq : ℚ) : ℝ) + ((st0.1 : ℚ) : ℝ)) :=
    max_le_max hφb (by linarith)
  have ha1 : εφt ≤ ((sa.1.1 : ℚ) : ℝ) := by
    rw [hsa]
    simp only [logC4aL]
    refine le_trans ?_ (Rat.cast_le.mpr (hρ _))
    push_cast
    have e1 := mul_le_mul_of_nonneg_left hη (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have e2 := mul_le_mul_of_nonneg_left hmax h2B
    linarith
  have haν : ∀ i < n, ν i ≤ ((sa.2.1.getD i 0 : ℚ) : ℝ) := fun i hi => by
    rw [hsa]
    simp only [logC4aL]
    rw [getD_range_map _ hi]
    refine le_trans ?_ (Rat.cast_le.mpr (hρ _))
    push_cast
    have := m2 i
    show GmulPC p n πφ ψ Zp i + η ≤ _
    linarith
  have hZsq : Zs ≤ ((xs + st0.1 + Dq : ℚ) : ℝ) := by
    push_cast
    linarith
  obtain ⟨a1, a2⟩ := GaddC_le_mirror p n h hn hA3 hπφ s2 hZsq
  set εs := GaddEC p n πφ ψ Zs with hεs
  set πs := GaddPC p n πφ ψ Zs with hπs
  have ha2 : εs ≤ ((sa.1.2 : ℚ) : ℝ) := by
    rw [hsa]
    simp only [logC4aL]
    exact a1.trans (Rat.cast_le.mpr (hρ _))
  have haπ : ∀ i < n, πs i ≤ ((sa.2.2.getD i 0 : ℚ) : ℝ) := fun i hi => by
    rw [hsa]
    simp only [logC4aL]
    rw [getD_range_map _ hi]
    exact (a2 i).trans (Rat.cast_le.mpr (hρ _))
  -- the second piece
  have hEδq : Eδ ≤ ((xd : ℚ) : ℝ) + ((Dq : ℚ) : ℝ) * (1 + ((tbq : ℚ) : ℝ) + ((st0.1 : ℚ) : ℝ)) := by
    have := mul_le_mul hD (by linarith : 1 + tb + Em ≤ 1 + ((tbq : ℚ) : ℝ) + ((st0.1 : ℚ) : ℝ)) (by linarith) hDq0
    linarith
  have hξE : ξ * Em ≤ ((ξq : ℚ) : ℝ) * ((st0.1 : ℚ) : ℝ) := mul_le_mul hξ s1 hEm0 hξq0
  have hZcq : Real.exp E - 1 + ξ * Em + Eδ + εφt + εs ≤
      ((cs + ξq * st0.1 + (xd + Dq * (1 + tbq + st0.1)) + sa.1.1 + sa.1.2 : ℚ) : ℝ) := by
    push_cast
    linarith
  obtain ⟨c1, c2⟩ := GaddC_le_mirror p n h hn hA3 (α := πs) (β := ν) (αq := fun i => sa.2.2.getD i 0)
    (βq := fun i => sa.2.1.getD i 0) haπ haν hZcq
  refine ⟨?_, fun i hi => ?_⟩
  · refine le_trans ?_ (Rat.cast_le.mpr (hρ _))
    push_cast
    linarith
  · rw [getD_range_map _ hi]
    refine le_trans ?_ (Rat.cast_le.mpr (hρ _))
    rw [Rat.cast_max]
    refine max_le_max (c2 i) ?_
    refine (GaddC_le_mirror p n h hn hA3 hπφ s2 ?_).2 i
    push_cast
    linarith

include h in
/-- The last ADD: from a state above `(P, ω_r)`, `logEndL` is at least `ε_y + P`. -/
theorem logEnd_le (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {πy ωr : ℕ → ℝ} {πyq : ℕ → ℚ}
    (hπy : ∀ i < n, πy i ≤ ((πyq i : ℚ) : ℝ)) {l P : ℝ} {lq : ℚ} (hl : l ≤ ((lq : ℚ) : ℝ)) (st : ℚ × List ℚ)
    (hst : Dom n P ωr st) : GaddEC p n πy ωr (l + P) + P ≤ ((logEndL uq n πyq lq st : ℚ) : ℝ) := by
  obtain ⟨s1, s2⟩ := hst
  have hZ : l + P ≤ ((lq + st.1 : ℚ) : ℝ) := by
    push_cast
    linarith
  obtain ⟨a1, -⟩ := GaddC_le_mirror p n h hn hA3 hπy s2 hZ
  simp only [logEndL]
  push_cast
  linarith

omit h hρ in
/-- `logVQ`, cast to `ℝ`, is `logV`. -/
theorem cast_logVQ (C : ℚ) (q i : ℕ) : ((logVQ C q i : ℚ) : ℝ) = logV (C : ℝ) q i := by
  simp [logVQ, logV]

include h hρ in
/-- LOG's step (5): Horner's rule on the series, `c ⊗ h` and `ADDF(c ⊗ h, 1)` run on a state `(χ^M, C^M)` above
`(χ, C)`, and the last product on bounds `(χ_q, C_q)` of `(χ, C)` itself, give a state above `logPC`'s `(P, ω_r)`; so
one run of the first three serves every case below `(χ^M, C^M)` -/
theorem logPC_le (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {η : ℚ} (hη : 0 ≤ η) {χ : ℕ → ℝ}
    {χq χM : ℕ → ℚ} (hχ0 : ∀ i, 0 ≤ χ i) (hχ : ∀ i < n, χ i ≤ ((χq i : ℚ) : ℝ)) (hχM : ∀ i < n, χq i ≤ χM i)
    (hχM0 : ∀ i, 0 ≤ χM i) {C Ec : ℝ} {Cq CM Ecq : ℚ} (hC0 : 0 ≤ C) (hC : C ≤ ((Cq : ℚ) : ℝ)) (hCM : Cq ≤ CM)
    (hCM1 : CM < 1) (hEc0 : 0 ≤ Ec) (hEc : Ec ≤ ((Ecq : ℚ) : ℝ)) (F' : ℕ → ℕ → ℚ)
    (hF0 : ∀ k i, n ≤ i → F' k i = 0) (φ' : ℕ → ℚ) (hφ' : ∀ k, 0 ≤ φ' k) (q : ℕ) (B : ℤ) :
    Dom n (logPC p n (η : ℝ) χ C Ec (fun k i => ((F' k i : ℚ) : ℝ)) (fun k => ((φ' k : ℚ) : ℝ)) q B).1
      (logPC p n (η : ℝ) χ C Ec (fun k i => ((F' k i : ℚ) : ℝ)) (fun k => ((φ' k : ℚ) : ℝ)) q B).2
      (logPL uq n ρ η χq Cq Ecq
        (hornerRunLC uq n ρ χM CM 0 η F' φ' (logVQ CM q) q 0 (q - 2) (hornerInitL n F' φ' q)).1
        (logHL uq n ρ η χM CM q
          (hornerRunLC uq n ρ χM CM 0 η F' φ' (logVQ CM q) q 0 (q - 2) (hornerInitL n F' φ' q))).1.1
        (logHL uq n ρ η χM CM q
          (hornerRunLC uq n ρ χM CM 0 η F' φ' (logVQ CM q) q 0 (q - 2) (hornerInitL n F' φ' q))).1.2 q B
        (logGL uq n ρ (logHL uq n ρ η χM CM q
          (hornerRunLC uq n ρ χM CM 0 η F' φ' (logVQ CM q) q 0 (q - 2) (hornerInitL n F' φ' q))))) := by
  have hη' : (0 : ℝ) ≤ ((η : ℚ) : ℝ) := by exact_mod_cast hη
  have hCq0 : (0 : ℝ) ≤ ((Cq : ℚ) : ℝ) := hC0.trans hC
  have hCM' : ((Cq : ℚ) : ℝ) ≤ ((CM : ℚ) : ℝ) := by exact_mod_cast hCM
  have hCMr0 : (0 : ℝ) ≤ ((CM : ℚ) : ℝ) := hCq0.trans hCM'
  have hCM0 : (0 : ℚ) ≤ CM := by exact_mod_cast hCMr0
  have hCq1 : ((Cq : ℚ) : ℝ) < 1 := by exact_mod_cast lt_of_le_of_lt hCM hCM1
  have hφr : ∀ k, (0 : ℝ) ≤ ((φ' k : ℚ) : ℝ) := fun k => by exact_mod_cast hφ' k
  have hCs : Sand C ((Cq : ℚ) : ℝ) := ⟨hC0, hC⟩
  have hv : ∀ k, 0 ≤ logV C q k ∧ logV C q k ≤ ((logVQ CM q k : ℚ) : ℝ) := fun k => by
    rw [cast_logVQ]
    have := logV_sand (⟨hC0, hC.trans hCM'⟩ : Sand C ((CM : ℚ) : ℝ)) q k
    exact ⟨this.nonneg, this.le⟩
  have hvq0 : ∀ k, (0 : ℚ) ≤ logVQ CM q k := fun k => by
    have := (hv k).1.trans (hv k).2
    exact_mod_cast this
  have hχMr : ∀ i < n, χ i ≤ ((χM i : ℚ) : ℝ) := fun i hi => (hχ i hi).trans (by exact_mod_cast hχM i hi)
  -- Horner's rule on the shared state: below `n`, then at the rational `(χ^M, C^M)` and `v`, then the mirror
  have ht := hornerBC_trunc p n χ C 0 (η : ℝ) (fun k i => ((F' k i : ℚ) : ℝ)) (fun k => ((φ' k : ℚ) : ℝ))
    (logV C q) q (q - 2)
  have hm := hornerBC_mono2 p n hA3 (πz := trunc n χ) (πz' := fun i => ((χM i : ℚ) : ℝ))
    (trunc_nonneg n fun i _ => hχ0 i) (fun i => by
      unfold trunc
      split_ifs with hi
      · exact hχMr i hi
      · exact_mod_cast hχM0 i) hC0 (hC.trans hCM') (le_refl (0 : ℝ)) (le_refl (0 : ℝ)) hη'
    (fun k i => ((F' k i : ℚ) : ℝ)) hφr (fun k => (hv k).1) (fun k => (hv k).2) q (q - 2)
  have hr := hornerRunLC_ge p n h hρ hn hA3 (πz := fun i => ((χM i : ℚ) : ℝ)) (πzq := χM)
    (fun i => by exact_mod_cast hχM0 i) (fun i => le_rfl) hCM0 (εz := 0) (εzq := 0) le_rfl (by simp) hη F' hF0
    hφ' hvq0 q (q - 2)
  rw [ht] at hm
  obtain ⟨hH0, hH20⟩ := hornerBC_nonneg p n hA3 hχ0 hC0 (le_refl (0 : ℝ)) hη' (fun k i => ((F' k i : ℚ) : ℝ))
    hφr (fun k => (hv k).1) q (q - 2)
  obtain ⟨hor, hhor⟩ : ∃ s, s = hornerRunLC uq n ρ χM CM 0 η F' φ' (logVQ CM q) q 0 (q - 2)
    (hornerInitL n F' φ' q) := ⟨_, rfl⟩
  rw [← hhor] at hr ⊢
  obtain ⟨hh, hhh⟩ : ∃ s, s = logHL uq n ρ η χM CM q hor := ⟨_, rfl⟩
  obtain ⟨gg, hgg⟩ : ∃ s, s = logGL uq n ρ hh := ⟨_, rfl⟩
  rw [← hhh, ← hgg]
  simp only [logPC]
  set H := hornerBC p n χ C 0 (η : ℝ) (fun k i => ((F' k i : ℚ) : ℝ)) (fun k => ((φ' k : ℚ) : ℝ)) (logV C q) q
    (q - 2) with hHd
  have hH1 : H.1 ≤ ((hor.1 : ℚ) : ℝ) := hm.1.trans hr.1
  have hH2 : ∀ i, H.2 i ≤ ((hor.2.getD i 0 : ℚ) : ℝ) := fun i => (hm.2 i).trans (hr.2 i)
  set Zh := C * (logV C q 2 + H.1) with hZh
  set ωh := fun i => GmulPC p n χ H.2 Zh i + (η : ℝ) with hωh
  set εh := GmulEC p n χ H.2 Zh + n * (η : ℝ) with hεh
  -- `c ⊗ h`
  have hZhq : Zh ≤ ((CM * (logVQ CM q 2 + hor.1) : ℚ) : ℝ) := by
    push_cast
    exact mul_le_mul (hC.trans hCM') (add_le_add (hv 2).2 hH1) (add_nonneg (hv 2).1 hH0) hCMr0
  obtain ⟨m1, m2⟩ := GmulC_le_mirror p n h hA3 (fun i _ => hχ0 i) (fun i _ => hH20 i) hχMr (fun i _ => hH2 i)
    hZhq
  have hZh0 : 0 ≤ Zh := mul_nonneg hC0 (add_nonneg (hv 2).1 hH0)
  obtain ⟨hm0, hmp0⟩ := GmulC_nonneg p n hA3 hχ0 hH20 hZh0
  have hnη : (0 : ℝ) ≤ n * (η : ℝ) := mul_nonneg (Nat.cast_nonneg n) hη'
  have hεh0 : 0 ≤ εh := add_nonneg hm0 hnη
  have hεhq : εh ≤ ((hh.1.2 : ℚ) : ℝ) := by
    rw [hhh]
    simp only [logHL]
    refine le_trans ?_ (Rat.cast_le.mpr (hρ _))
    push_cast
    linarith
  have hhbq : Zh + εh ≤ ((hh.1.1 : ℚ) : ℝ) := by
    rw [hhh]
    simp only [logHL]
    refine le_trans ?_ (Rat.cast_le.mpr (hρ _))
    push_cast at hZhq ⊢
    linarith
  have hωh0 : ∀ i, 0 ≤ ωh i := fun i => add_nonneg (hmp0 i) hη'
  have hωhq : ∀ i < n, ωh i ≤ ((hh.2.getD i 0 : ℚ) : ℝ) := fun i hi => by
    rw [hhh]
    simp only [logHL]
    rw [getD_range_map _ hi]
    refine le_trans ?_ (Rat.cast_le.mpr (hρ _))
    push_cast
    have := m2 i
    show GmulPC p n χ H.2 Zh i + (η : ℝ) ≤ _
    linarith
  -- `ADDF(c ⊗ h, 1)`
  set hb := Zh + εh with hhb
  have hhb0 : 0 ≤ hb := add_nonneg hZh0 hεh0
  have hsum0 : 0 ≤ ∑ j ∈ Ico 1 n, ωh j := sum_nonneg fun j _ => hωh0 j
  have hsumq : ∑ j ∈ Ico 1 n, ωh j ≤ ∑ j ∈ Ico 1 n, ((hh.2.getD j 0 : ℚ) : ℝ) :=
    sum_le_sum fun j hj => hωhq j (mem_Ico.mp hj).2
  set lam := 1 + hb + ∑ j ∈ Ico 1 n, ωh j with hlam
  have hlq : lam ≤ ((1 + hh.1.1 + ∑ j ∈ Ico 1 n, hh.2.getD j 0 : ℚ) : ℝ) := by
    push_cast
    linarith
  have hZgq : 1 + hb ≤ ((1 + hh.1.1 : ℚ) : ℝ) := by
    push_cast
    linarith
  obtain ⟨g1, g2⟩ := GaddfC_le_mirror p n h hn (α := ωh) (αq := fun i => hh.2.getD i 0) (fun i _ => hωh0 i)
    hωhq (by linarith : 0 ≤ lam) hlq (by linarith : 0 ≤ 1 + hb) hZgq
  obtain ⟨sg1, sg2⟩ := GaddfC_sand p n (α := ωh) (α' := ωh) (fun i => Sand.refl (hωh0 i))
    (Sand.refl (by linarith : 0 ≤ lam)) (Sand.refl (by linarith : 0 ≤ 1 + hb))
  set εg := GaddfEC p n ωh lam (1 + hb) with hεg
  set ωg := GaddfPC p n ωh lam (1 + hb) with hωg
  have hεgq : εg ≤ ((gg.1 : ℚ) : ℝ) := by
    rw [hgg]
    simp only [logGL]
    exact g1.trans (Rat.cast_le.mpr (hρ _))
  have hωgq : ∀ i < n, ωg i ≤ ((gg.2.getD i 0 : ℚ) : ℝ) := fun i hi => by
    rw [hgg]
    simp only [logGL]
    rw [getD_range_map _ hi]
    exact (g2 i).trans (Rat.cast_le.mpr (hρ _))
  -- the last product, on the case's own bounds
  set Zr := C * (1 + hb + εg) with hZr
  have hZrq : Zr ≤ ((Cq * (1 + hh.1.1 + gg.1) : ℚ) : ℝ) := by
    push_cast
    exact mul_le_mul hC (by linarith) (by linarith [sg1.nonneg]) hCq0
  obtain ⟨r1, r2⟩ := GmulC_le_mirror p n h hA3 (fun i _ => hχ0 i) (fun i _ => (sg2 i).nonneg) hχ hωgq hZrq
  have hSC : C * (εg + εh + C * H.1) ≤
      ((Cq : ℚ) : ℝ) * (((gg.1 : ℚ) : ℝ) + ((hh.1.2 : ℚ) : ℝ) + ((Cq : ℚ) : ℝ) * ((hor.1 : ℚ) : ℝ)) :=
    (hCs.mul (((⟨sg1.nonneg, hεgq⟩ : Sand εg ((gg.1 : ℚ) : ℝ)).add ⟨hεh0, hεhq⟩).add (hCs.mul ⟨hH0, hH1⟩))).le
  have hq1 : (0 : ℝ) ≤ (q : ℝ) + 1 := by positivity
  have h2B : (0 : ℝ) ≤ (2 : ℝ) ^ (-B - 13) := by positivity
  have hT := ((((hCs.pow (q + 1)).div_const hq1).max (hCs.const_mul h2B)).div_one_sub hCs hCq1).le
  have hL := (Sand.div_one_sub (⟨hEc0, hEc⟩ : Sand Ec ((Ecq : ℚ) : ℝ)) hCs hCq1).le
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [logPL]
    refine le_trans ?_ (Rat.cast_le.mpr (hρ _))
    push_cast
    linarith
  · simp only [logPL]
    rw [getD_range_map _ hi]
    refine le_trans ?_ (Rat.cast_le.mpr (hρ _))
    rw [Rat.cast_max]
    refine max_le_max ?_ (hχ i hi)
    push_cast
    have := r2 i
    linarith

include hρ in
/-- Step (3) for `d' = 1`, where `t = r'`: the state `(E^tr_1 + D, π')` on rational bounds is above `core0C`'s. -/
theorem core0C_cert_one {π' : ℕ → ℝ} (pq : List ℚ) (hπ : ∀ i < n, π' i ≤ ((pq.getD i 0 : ℚ) : ℝ)) {b' : ℝ}
    {bp : ℚ} (hb0 : 0 ≤ b') (hb : b' ≤ ((bp : ℚ) : ℝ)) (hbp : bp < 1) {D : ℝ} {Dq : ℚ} (hD : D ≤ ((Dq : ℚ) : ℝ))
    (T0 η : ℝ) (Fk : ℕ → ℕ → ℝ) (φ : ℕ → ℝ) :
    Dom n (core0C p n T0 D η π' b' Fk φ 1).1 (core0C p n T0 D η π' b' Fk φ 1).2 (ρ (eTrQ bp 1 + Dq), pq) := by
  have hbp' : ((bp : ℚ) : ℝ) < ((1 : ℕ) : ℝ) + 2 := by
    have : ((bp : ℚ) : ℝ) < 1 := by exact_mod_cast hbp
    push_cast
    linarith
  have he := eTr_le hb0 hb 1 hbp'
  simp only [core0C, ↓reduceIte]
  refine ⟨le_trans ?_ (Rat.cast_le.mpr (hρ _)), hπ⟩
  push_cast
  linarith

include h hρ in
/-- The convex `𝓔` of a case from stored states: from a state `sts 0` above `(E_0, ψ_0)`, the squarings `sts j`, step
(4)'s two pieces `sa` and `c4`, step (5)'s Horner's rule, `c ⊗ h` and `ADDF(c ⊗ h, 1)` on a shared `(χ^M, C^M)` above
`c4`'s `(χ, C)`, its last product `pp`, and the last ADD, with rational bounds of `ξ`, `φ̄`, `π^x`, `π^φ`, `π^y`, `ℓ`
and of the exponentials of step (4): the last ADD's mirror is at least `logBoundC`, and `cs + c4.1` at least the
convex `C = e^E - 1 + E_c` -/
theorem logBoundC_cert (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {η₁ η₂ ηx ηp ηc : ℚ} (hη₁ : 0 ≤ η₁)
    (hη₂ : 0 ≤ η₂) (hηx : 0 ≤ ηx) (hηp : 0 ≤ ηp) (hηc : 0 ≤ ηc) {l E : ℝ} {lq : ℚ} (hl : l ≤ ((lq : ℚ) : ℝ))
    (hE0 : 0 ≤ E) {πy : ℕ → ℝ} {πyq : ℕ → ℚ} (hπy : ∀ i < n, πy i ≤ ((πyq i : ℚ) : ℝ)) (pos : Bool) (m : ℕ)
    {a b δ : ℝ} {ap bpB : ℚ} (hb0 : 0 ≤ b) (hδ0 : 0 ≤ δ) (hap0 : 0 ≤ ap)
    (hap : ((ap : ℚ) : ℝ) ≤ (2 : ℝ) ^ (-(m : ℤ)) * a) (hbp : coreBpC n m b (η₁ : ℝ) ≤ ((bpB : ℚ) : ℝ))
    (hbpl : bpB < 1) (hbp1 : 2 ^ m * bpB ≤ 1) (hap1 : 2 ^ m * ap ≤ 1) {π : ℕ → ℝ} (hπ0 : ∀ i, 0 ≤ π i)
    (Fk : ℕ → ℕ → ℚ) (φF : ℕ → ℚ) (hφF : ∀ k, 0 ≤ φF k) (d' : ℕ) (sts : ℕ → ℚ × List ℚ)
    (hst0 : Dom n
      (core0C p n (coreTC pos (coreBpC n m b (η₁ : ℝ)) 0) (2 * n * (η₁ : ℝ)) (η₂ : ℝ) (corePiC m π (η₁ : ℝ))
        (coreBpC n m b (η₁ : ℝ)) (fun k i => ((Fk k i : ℚ) : ℝ)) (fun k => ((φF k : ℚ) : ℝ)) d').1
      (core0C p n (coreTC pos (coreBpC n m b (η₁ : ℝ)) 0) (2 * n * (η₁ : ℝ)) (η₂ : ℝ) (corePiC m π (η₁ : ℝ))
        (coreBpC n m b (η₁ : ℝ)) (fun k i => ((Fk k i : ℚ) : ℝ)) (fun k => ((φF k : ℚ) : ℝ)) d').2 (sts 0))
    (hstep : ∀ j < m, expSqLC uq n ρ (coreTCQ ρ pos bpB j) (coreTCQ ρ pos bpB (j + 1)) (coreGQ ρ pos ap bpB j)
      (sts j) = sts (j + 1))
    {πx : ℕ → ℝ} {πxq πφq : ℕ → ℚ} (hπx0 : ∀ i, 0 ≤ πx i) (hπx : ∀ i < n, πx i ≤ ((πxq i : ℚ) : ℝ))
    {φbq xs cs xd ξq : ℚ} (hφb : logPhiBC (n * (ηx : ℝ)) pos E a b δ ≤ ((φbq : ℚ) : ℝ))
    (hπφq : ∀ i < n, ρ (GaddfPCQ uq n πxq (φbq + ∑ i ∈ Ico 1 n, πxq i) φbq i) ≤ πφq i)
    (hxs : 2 * (Real.exp (b + δ) - 1 - (b + δ)) + Real.exp (b + δ) * (Real.exp (E + δ) - 1) ≤ ((xs : ℚ) : ℝ))
    (hcs : Real.exp E - 1 ≤ ((cs : ℚ) : ℝ)) (hxd : Real.exp E * (Real.exp δ - 1) ≤ ((xd : ℚ) : ℝ))
    (hξ : logXi (n * (ηx : ℝ)) pos E a b δ ≤ ((ξq : ℚ) : ℝ)) (B : ℤ)
    (sa : (ℚ × ℚ) × (List ℚ × List ℚ))
    (hsa : logC4aL uq n ρ (n * ηx) ηp πφq φbq (coreTCQ ρ pos bpB m) xs B (sts m) = sa) (c4 : ℚ × List ℚ)
    (hc4 : logC4bL uq n ρ (n * ηx) πφq (coreTCQ ρ pos bpB m) cs xd ξq (sts m) sa = c4)
    (F' : ℕ → ℕ → ℚ) (hF'0 : ∀ k i, n ≤ i → F' k i = 0) (φ' : ℕ → ℚ) (hφ' : ∀ k, 0 ≤ φ' k) (q : ℕ)
    {χM : ℕ → ℚ} {CM : ℚ} (hχM0 : ∀ i, 0 ≤ χM i) (hχM : ∀ i < n, c4.2.getD i 0 ≤ χM i) (hCM : cs + c4.1 ≤ CM)
    (hCM1 : CM < 1) (sH : ℚ × List ℚ)
    (hsH : hornerRunLC uq n ρ χM CM 0 ηc F' φ' (logVQ CM q) q 0 (q - 2) (hornerInitL n F' φ' q) = sH)
    (hh : (ℚ × ℚ) × List ℚ) (hhh : logHL uq n ρ ηc χM CM q sH = hh) (gg : ℚ × List ℚ)
    (hgg : logGL uq n ρ hh = gg) (pp : ℚ × List ℚ)
    (hpp : logPL uq n ρ ηc (fun i => c4.2.getD i 0) (cs + c4.1) c4.1 sH.1 hh.1.1 hh.1.2 q B gg = pp) :
    logBoundC p n (η₁ : ℝ) (η₂ : ℝ) (ηx : ℝ) (ηp : ℝ) (ηc : ℝ) l E πy pos m a b δ π
        (fun k i => ((Fk k i : ℚ) : ℝ)) (fun k => ((φF k : ℚ) : ℝ)) d' πx (fun k i => ((F' k i : ℚ) : ℝ))
        (fun k => ((φ' k : ℚ) : ℝ)) q B ≤ ((logEndL uq n πyq lq pp : ℚ) : ℝ) ∧
      Real.exp E - 1 + (logCase4C p n (η₁ : ℝ) (η₂ : ℝ) (ηx : ℝ) (ηp : ℝ) E pos m a b δ π
        (fun k i => ((Fk k i : ℚ) : ℝ)) (fun k => ((φF k : ℚ) : ℝ)) d' πx B).1 ≤ ((cs + c4.1 : ℚ) : ℝ) := by
  have hη₁' : (0 : ℝ) ≤ ((η₁ : ℚ) : ℝ) := by exact_mod_cast hη₁
  have hη₂' : (0 : ℝ) ≤ ((η₂ : ℚ) : ℝ) := by exact_mod_cast hη₂
  have hηx' : (0 : ℝ) ≤ ((ηx : ℚ) : ℝ) := by exact_mod_cast hηx
  have hηp' : (0 : ℝ) ≤ ((ηp : ℚ) : ℝ) := by exact_mod_cast hηp
  have hφFr : ∀ k, (0 : ℝ) ≤ ((φF k : ℚ) : ℝ) := fun k => by exact_mod_cast hφF k
  have hD0 : (0 : ℝ) ≤ n * ((ηx : ℚ) : ℝ) := mul_nonneg (Nat.cast_nonneg n) hηx'
  have h2m : (0 : ℝ) < (2 : ℝ) ^ (-(m : ℤ)) := by positivity
  -- `b'`, `t̄_j` and `g_j`
  set b' := coreBpC n m b (η₁ : ℝ) with hb'
  have hb'0 : 0 ≤ b' := add_nonneg (mul_nonneg h2m.le hb0) (mul_nonneg (Nat.cast_nonneg n) hη₁')
  have hbpB0 : (0 : ℚ) ≤ bpB := by exact_mod_cast hb'0.trans hbp
  have hb'1 : b' < 1 := lt_of_le_of_lt hbp (by exact_mod_cast hbpl)
  have h2j : ∀ j ≤ m, (2 : ℚ) ^ j * bpB ≤ 1 := fun j hj =>
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hbpB0).trans hbp1
  have h2a : ∀ j ≤ m, (2 : ℚ) ^ j * ap ≤ 1 := fun j hj =>
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hap0).trans hap1
  have hT0 : ∀ j, 0 ≤ coreTC pos b' j := fun j => by
    have h2 : (0 : ℝ) ≤ 2 ^ j * b' := mul_nonneg (by positivity) hb'0
    unfold coreTC
    split_ifs
    · linarith [Real.one_le_exp h2]
    · exact h2
  have hT : ∀ j ≤ m, coreTC pos b' j ≤ ((coreTCQ ρ pos bpB j : ℚ) : ℝ) := fun j hj =>
    (coreTC_le hρ hb'0 hbp j (h2j j hj)).2
  have hg : ∀ j, 0 ≤ coreG pos ((2 : ℝ) ^ (-(m : ℤ)) * a) b' j ∧ (j < m →
      coreG pos ((2 : ℝ) ^ (-(m : ℤ)) * a) b' j ≤ ((coreGQ ρ pos ap bpB j : ℚ) : ℝ)) := fun j =>
    ⟨by unfold coreG; split_ifs <;> exact (Real.exp_pos _).le,
      fun hj => (coreG_le hρ hap0 hap hb'0 hbp j (h2a j hj.le) (h2j j hj.le)).2⟩
  -- Lemma 39's convex bounds on the stored states
  obtain ⟨hc00, hc02⟩ := core0C_nonneg p n hA3 (π' := corePiC m π (η₁ : ℝ))
    (fun i => add_nonneg (mul_nonneg h2m.le (hπ0 i)) hη₁') hb'0 hb'1 (hT0 0)
    (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg n)) hη₁') hη₂' (fun k i => ((Fk k i : ℚ) : ℝ))
    (fun k => ((φF k : ℚ) : ℝ)) hφFr d'
  obtain ⟨dm, hcm1, hcm2⟩ := coreEC_cert p n h hρ hn hA3 (T := coreTC pos b')
    (g := coreG pos ((2 : ℝ) ^ (-(m : ℤ)) * a) b') (coreTCQ ρ pos bpB) (coreGQ ρ pos ap bpB) m hT0 hT
    (fun j => (hg j).1) (fun j hj => (hg j).2 hj) hc00 hc02 sts hst0 hstep m le_rfl
  set cm := coreBoundC p n (η₁ : ℝ) (η₂ : ℝ) pos m a b π (fun k i => ((Fk k i : ℚ) : ℝ))
    (fun k => ((φF k : ℚ) : ℝ)) d' with hcm
  have dm' : Dom n cm.1 cm.2 (sts m) := dm
  have hcm1' : 0 ≤ cm.1 := hcm1
  have hcm2' : ∀ i, 0 ≤ cm.2 i := hcm2
  have dψ : Dom n cm.1 (fun i => max (cm.2 i) 0) (sts m) :=
    ⟨dm'.1, fun i hi => (max_eq_left (hcm2' i)).le.trans (dm'.2 i hi)⟩
  -- `φ̄`, `ξ` and `π^φ`
  set φb := logPhiBC (n * (ηx : ℝ)) pos E a b δ with hφbd
  set ξ := logXi (n * (ηx : ℝ)) pos E a b δ with hξd
  have hφb0 : 0 ≤ φb := le_max_of_le_right (by positivity)
  have hξ0 : 0 ≤ ξ := logXi_nonneg hD0 pos E a b δ
  have hsum0 : 0 ≤ ∑ i ∈ Ico 1 n, πx i := sum_nonneg fun i _ => hπx0 i
  have hsumq : ∑ i ∈ Ico 1 n, πx i ≤ ∑ i ∈ Ico 1 n, ((πxq i : ℚ) : ℝ) :=
    sum_le_sum fun i hi => hπx i (mem_Ico.mp hi).2
  have hlq : φb + ∑ i ∈ Ico 1 n, πx i ≤ ((φbq + ∑ i ∈ Ico 1 n, πxq i : ℚ) : ℝ) := by
    push_cast
    linarith
  obtain ⟨-, f2⟩ := GaddfC_le_mirror p n h hn (fun i _ => hπx0 i) hπx (add_nonneg hφb0 hsum0) hlq hφb0 hφb
  obtain ⟨-, f0⟩ := GaddfC_sand p n (α := πx) (α' := πx) (fun i => Sand.refl (hπx0 i))
    (Sand.refl (add_nonneg hφb0 hsum0)) (Sand.refl hφb0)
  set πφ := GaddfPC p n πx (φb + ∑ i ∈ Ico 1 n, πx i) φb with hπφd
  have hπφ : ∀ i < n, πφ i ≤ ((πφq i : ℚ) : ℝ) := fun i hi =>
    ((f2 i).trans (Rat.cast_le.mpr (hρ _))).trans (Rat.cast_le.mpr (hπφq i hi))
  -- step (4)
  have hDq : (n : ℝ) * ((ηx : ℚ) : ℝ) ≤ (((n : ℚ) * ηx : ℚ) : ℝ) := by
    push_cast
    exact le_rfl
  have d4 := logC4C_le p n h hρ hn hA3 hD0 hDq (le_refl ((ηp : ℚ) : ℝ)) (fun i => (f0 i).nonneg) hπφ
    (fun i => le_max_right (cm.2 i) 0) hφb0 hφb (hT0 m) (hT m le_rfl) hcm1' hxs hcs hxd hξ0 hξ B (sts m) dψ
  rw [hsa, hc4] at d4
  obtain ⟨s4a, s4b⟩ := logC4_sand p n hA3 hD0 hηp' (fun i => Sand.refl ((f0 i).nonneg))
    (fun i => Sand.refl (le_max_right (cm.2 i) 0)) (Sand.refl hφb0) (Sand.refl (hT0 m)) (Sand.refl hcm1') hE0 hδ0
    b hξ0 B
  set c4r := logCase4C p n (η₁ : ℝ) (η₂ : ℝ) (ηx : ℝ) (ηp : ℝ) E pos m a b δ π (fun k i => ((Fk k i : ℚ) : ℝ))
    (fun k => ((φF k : ℚ) : ℝ)) d' πx B with hc4r
  have d4' : Dom n c4r.1 c4r.2 c4 := d4
  have hEc0 : 0 ≤ c4r.1 := s4a.nonneg'
  have hχ0 : ∀ i, 0 ≤ c4r.2 i := fun i => (s4b i).nonneg'
  have hC0 : 0 ≤ Real.exp E - 1 + c4r.1 := by
    have := Real.one_le_exp hE0
    linarith
  have hCq : Real.exp E - 1 + c4r.1 ≤ ((cs + c4.1 : ℚ) : ℝ) := by
    push_cast
    linarith [d4'.1]
  -- step (5) and the last ADD
  have d5 := logPC_le p n h hρ hn hA3 hηc hχ0 d4'.2 hχM hχM0 hC0 hCq hCM hCM1 hEc0 d4'.1 F' hF'0 φ' hφ' q B
  rw [hsH, hhh, hgg, hpp] at d5
  exact ⟨logEnd_le p n h hn hA3 hπy hl pp d5, hCq⟩

end Bounds

end ExpansionBounds
