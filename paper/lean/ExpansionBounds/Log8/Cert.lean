import ExpansionBounds.Log8.Defs
import ExpansionBounds.LogArgs

/-!
# Theorem 42 at `n = 8` and `p = 53`: from the kernel's checks to the bound at an end

`log8_eval`: for a case, a sign and an end `ℓ` of its interval, the kernel's checks (`Log8Leaf`, the squarings,
`log8C4a`, `log8C4b`, `Log8End`, and `Log8Shared` once) give, for real arguments below the rational ones, the convex
`𝓔` of `logBoundC` at most `9.926u^8 ℓ` (`+ 2^{-509}` from `ℓ = 0`) and `C = e^E - 1 + E_c < 1`. It is
`logBoundC_cert` at `n = 8` with multidouble's constants; the state of step (3) enters as a hypothesis, which
`log8_head` gives from the kernel's checks of a group's state.
-/

namespace ExpansionBounds

open Finset

/-- the first `j` squarings of a case from a state -/
def log8SqRun (pos : Bool) (m : ℕ) (a b : ℚ) : ℕ → ℚ × List ℚ → ℚ × List ℚ
  | 0, st => st
  | j + 1, st => log8Sq pos m a b j (log8SqRun pos m a b j st)

/-- The parts of `F'_k` stop at eight. -/
theorem log8F_zero : ∀ k i, 8 ≤ i → log8F k i = 0 := by
  have hlen : ∀ t ∈ log8Ser, t.length ≤ 8 := by decide
  intro k i hi
  unfold log8F
  apply dyFn_of_le
  rw [List.getD_eq_getElem?_getD]
  cases hk : log8Ser[k]? with
  | none => simp
  | some t => exact (hlen t (List.mem_of_getElem? hk)).trans hi

/-- The parts of `F_k` stop at eight. -/
theorem exp8F_zero : ∀ k i, 8 ≤ i → exp8F k i = 0 := by
  have hlen : ∀ t ∈ exp8Fact, t.length ≤ 8 := by decide
  intro k i hi
  unfold exp8F
  apply dyFn_of_le
  rw [List.getD_eq_getElem?_getD]
  cases hk : exp8Fact[k]? with
  | none => simp
  | some t => exact (hlen t (List.mem_of_getElem? hk)).trans hi

/-- The state of step (3) from the kernel's checks: Horner's run on a state `(p_q, b_T)`, the two products and the
sum for a sign follow the stored states, and the last one is above `core0C`'s `(E_0, ψ_0)` at any `π'` and `b'`
below `(p_q, b_T)`, for a degree `d' ≠ 1` -/
theorem log8_head (pos : Bool) (m d' : ℕ) (hd : d' ≠ 1) {pq : List ℚ} {bpT : ℚ} (hpq0 : ∀ i, 0 ≤ pq.getD i 0)
    (hbT : bpT < 1) {sH : ℚ × List ℚ} (hrun : log8Run pq bpT d' 0 (d' - 2) (hornerInitL 8 exp8F exp8Phi d') = sH)
    {w : (ℚ × ℚ) × List ℚ} (hw : log8W pq bpT sH = w) {y : ℚ × List ℚ} (hy : log8Y m d' pq bpT w = y)
    {t : ℚ × List ℚ} (ht : log8T pos pq bpT y = t) {π' : ℕ → ℝ} (hπ0 : ∀ i, 0 ≤ π' i)
    (hπ : ∀ i < 8, π' i ≤ ((pq.getD i 0 : ℚ) : ℝ)) {b' : ℝ} (hb0 : 0 ≤ b') (hb : b' ≤ ((bpT : ℚ) : ℝ)) :
    Dom 8
      (core0C 53 8 (coreTC pos b' 0) (2 * (8 : ℕ) * ((exp8Eta1 m : ℚ) : ℝ)) ((exp8Eta : ℚ) : ℝ) π' b'
        (fun k i => ((exp8F k i : ℚ) : ℝ)) (fun k => ((exp8Phi k : ℚ) : ℝ)) d').1
      (core0C 53 8 (coreTC pos b' 0) (2 * (8 : ℕ) * ((exp8Eta1 m : ℚ) : ℝ)) ((exp8Eta : ℚ) : ℝ) π' b'
        (fun k i => ((exp8F k i : ℚ) : ℝ)) (fun k => ((exp8Phi k : ℚ) : ℝ)) d').2 t := by
  have hu : ((red8U : ℚ) : ℝ) = u (53 : ℤ) := by unfold red8U; exact u_53_rat 53 rfl
  have hu53 : u (53 : ℤ) = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  have hA3 : (((8 : ℕ) : ℝ) ^ 2 + (8 : ℕ)) * u (53 : ℤ) < 1 := by rw [hu53]; norm_num
  have hT : coreTC pos b' 0 ≤ ((coreTCQ (upQ 200) pos bpT 0 : ℚ) : ℝ) :=
    (coreTC_le (le_upQ 200) hb0 hb 0 (by simpa using hbT.le)).2
  have hD : 2 * ((8 : ℕ) : ℝ) * ((exp8Eta1 m : ℚ) : ℝ) ≤ ((2 * ((8 : ℕ) : ℚ) * exp8Eta1 m : ℚ) : ℝ) := by
    push_cast
    exact le_rfl
  have h := core0C_cert (53 : ℤ) 8 hu (le_upQ 200) (by norm_num) hA3 pq hπ0 hπ hpq0 hb0 hb hbT hT hD
    (le_refl ((exp8Eta : ℚ) : ℝ)) exp8F exp8F_zero exp8Phi (fun k => by unfold exp8Phi; exact abs_nonneg _) d' hd
  unfold log8Run at hrun
  unfold log8W at hw
  unfold log8Y at hy
  unfold log8T at ht
  rw [hrun, hw, hy, ht] at h
  exact h

/-- An evaluation at `n = 8`: from the kernel's checks of a case, a sign and an end `ℓ`, on a state `t0` above step
(3)'s `(E_0, ψ_0)`, the convex `𝓔` at real arguments within the rational ones is at most `9.926u^8 ℓ`, plus
`2^{-509}` where the interval starts at zero, and the convex `C` is below one -/
theorem log8_eval (k0 pos : Bool) (m d' : ℕ) {a b δ l bpT : ℚ} {pq : List ℚ} {xi xs cs xd : ℚ} {pphi : List ℚ}
    (hleaf : Log8Leaf k0 pos m a b δ l bpT pq xi xs cs xd pphi) (hsh : Log8Shared) {ar br δr E : ℝ}
    (ha : ((a : ℚ) : ℝ) ≤ ar) (hbr0 : 0 ≤ br) (hbr : br ≤ ((b : ℚ) : ℝ)) (hδr0 : 0 ≤ δr)
    (hδr : δr ≤ ((δ : ℚ) : ℝ)) (hE0 : 0 ≤ E) (hE : E ≤ ((log8Eq l : ℚ) : ℝ)) {π πy : ℕ → ℝ}
    (hπ0 : ∀ i, 0 ≤ π i) (hπy : ∀ i < 8, πy i ≤ ((log8PiY l i : ℚ) : ℝ)) (t0 : ℚ × List ℚ)
    (ht0 : Dom 8
      (core0C 53 8 (coreTC pos (coreBpC 8 m br ((exp8Eta1 m : ℚ) : ℝ)) 0) (2 * (8 : ℕ) * ((exp8Eta1 m : ℚ) : ℝ))
        ((exp8Eta : ℚ) : ℝ) (corePiC m π ((exp8Eta1 m : ℚ) : ℝ)) (coreBpC 8 m br ((exp8Eta1 m : ℚ) : ℝ))
        (fun k i => ((exp8F k i : ℚ) : ℝ)) (fun k => ((exp8Phi k : ℚ) : ℝ)) d').1
      (core0C 53 8 (coreTC pos (coreBpC 8 m br ((exp8Eta1 m : ℚ) : ℝ)) 0) (2 * (8 : ℕ) * ((exp8Eta1 m : ℚ) : ℝ))
        ((exp8Eta : ℚ) : ℝ) (corePiC m π ((exp8Eta1 m : ℚ) : ℝ)) (coreBpC 8 m br ((exp8Eta1 m : ℚ) : ℝ))
        (fun k i => ((exp8F k i : ℚ) : ℝ)) (fun k => ((exp8Phi k : ℚ) : ℝ)) d').2 t0)
    {sm : ℚ × List ℚ} (hsq : log8SqRun pos m a b m t0 = sm) {sa : (ℚ × ℚ) × (List ℚ × List ℚ)}
    (hA : log8C4a pos m b δ l xi xs pphi sm = sa) {c4 : ℚ × List ℚ}
    (hB : log8C4b pos m b xi cs xd pphi sm sa = c4) {zero : Bool} (hend : Log8End zero l cs c4) :
    logBoundC 53 8 ((exp8Eta1 m : ℚ) : ℝ) ((exp8Eta : ℚ) : ℝ) ((2 * exp8Eta : ℚ) : ℝ) ((2 * exp8Eta : ℚ) : ℝ)
        ((exp8Eta : ℚ) : ℝ) ((l : ℚ) : ℝ) E πy pos m ar br δr π (fun k i => ((exp8F k i : ℚ) : ℝ))
        (fun k => ((exp8Phi k : ℚ) : ℝ)) d'
        (fun i => logPiX 8 (2 * u 53) ((2 * exp8Eta : ℚ) : ℝ)
          (logXi ((8 : ℕ) * ((2 * exp8Eta : ℚ) : ℝ)) pos E ar br δr) i)
        (fun k i => ((log8F k i : ℚ) : ℝ)) (fun k => ((log8Phi k : ℚ) : ℝ)) 4 436 ≤
        (((if zero then 1 / 2 ^ 509 else 0) + 9926 / 1000 * red8U ^ 8 * l : ℚ) : ℝ) ∧
      Real.exp E - 1 + (logCase4C 53 8 ((exp8Eta1 m : ℚ) : ℝ) ((exp8Eta : ℚ) : ℝ) ((2 * exp8Eta : ℚ) : ℝ)
        ((2 * exp8Eta : ℚ) : ℝ) E pos m ar br δr π (fun k i => ((exp8F k i : ℚ) : ℝ))
        (fun k => ((exp8Phi k : ℚ) : ℝ)) d'
        (fun i => logPiX 8 (2 * u 53) ((2 * exp8Eta : ℚ) : ℝ)
          (logXi ((8 : ℕ) * ((2 * exp8Eta : ℚ) : ℝ)) pos E ar br δr) i) 436).1 < 1 := by
  have hu : ((red8U : ℚ) : ℝ) = u (53 : ℤ) := by unfold red8U; exact u_53_rat 53 rfl
  have hu53 : u (53 : ℤ) = 1 / 9007199254740992 := by rw [← hu]; unfold red8U; norm_num
  have hA3 : (((8 : ℕ) : ℝ) ^ 2 + (8 : ℕ)) * u (53 : ℤ) < 1 := by rw [hu53]; norm_num
  obtain ⟨ha0, hb0, hδ0, -, hbp, hbpT1, h2bp, ha1, -, -, z1, z2, z3, z4, z5, z6, hxi, hxs, hcs, hxd, hph⟩ := hleaf
  obtain ⟨hCM1, hχ0, hsH, hhh, hgg⟩ := hsh
  obtain ⟨hχM, hCM, hfin⟩ := hend
  subst hsq
  have hη0 : (0 : ℚ) ≤ exp8Eta := by unfold exp8Eta; positivity
  have hη1 : (0 : ℚ) ≤ exp8Eta1 m := by unfold exp8Eta1; split_ifs <;> [exact le_rfl; exact hη0]
  have hη2 : (0 : ℚ) ≤ 2 * exp8Eta := by positivity
  have h2m : (0 : ℝ) ≤ (2 : ℝ) ^ (-(m : ℤ)) := by positivity
  have h2mq : (0 : ℚ) ≤ (2 : ℚ) ^ (-(m : ℤ)) := by positivity
  -- the case's `b'` and `2^{-m}a`
  have hbpr : coreBpC 8 m br ((exp8Eta1 m : ℚ) : ℝ) ≤ ((log8Bp m b : ℚ) : ℝ) := by
    simp only [coreBpC, log8Bp]
    push_cast
    linarith [mul_le_mul_of_nonneg_left hbr h2m]
  have hap : ((((2 : ℚ) ^ (-(m : ℤ)) * a : ℚ)) : ℝ) ≤ (2 : ℝ) ^ (-(m : ℤ)) * ar := by
    push_cast
    exact mul_le_mul_of_nonneg_left ha h2m
  have hap1 : (2 : ℚ) ^ m * ((2 : ℚ) ^ (-(m : ℤ)) * a) ≤ 1 := by
    rw [← mul_assoc, zpow_neg, zpow_natCast, mul_inv_cancel₀ (by positivity), one_mul]
    exact ha1
  -- `ξ`, `φ̄`, `π^x` and the exponentials of step (4)
  have hD : ((8 : ℕ) : ℝ) * ((2 * exp8Eta : ℚ) : ℝ) ≤ ((((8 : ℕ) : ℚ) * (2 * exp8Eta) : ℚ) : ℝ) := by
    push_cast
    exact le_rfl
  have hD0 : (0 : ℝ) ≤ ((8 : ℕ) : ℝ) * ((2 * exp8Eta : ℚ) : ℝ) :=
    mul_nonneg (Nat.cast_nonneg 8) (by exact_mod_cast hη2)
  have hξ := (logXi_le hD hE ha hbr hδr pos z1 z2).trans (Rat.cast_le.mpr hxi)
  have hξ0 := logXi_nonneg hD0 pos E ar br δr
  have hφb : logPhiBC ((8 : ℕ) * ((2 * exp8Eta : ℚ) : ℝ)) pos E ar br δr ≤
      ((log8PhiB xi (log8Eq l) b δ : ℚ) : ℝ) :=
    (logPhiBC_le hD hE ha hbr hδr pos z1 z2).trans (Rat.cast_le.mpr (max_le_max (by linarith) le_rfl))
  have h1u : (0 : ℝ) ≤ 1 - 2 * u 53 := by rw [hu53]; norm_num
  have h4u : (0 : ℝ) < 1 - 2 * (2 * u 53) := by rw [hu53]; norm_num
  have hpx : ∀ i, ((log8PiX xi i : ℚ) : ℝ) =
      (2 * u 53) ^ i * (((xi : ℚ) : ℝ) * (1 - 2 * u 53) / (1 - 2 * (2 * u 53))) + ((2 * exp8Eta : ℚ) : ℝ) :=
    fun i => by
      simp only [log8PiX]
      push_cast
      rw [hu]
      ring
  have hπx0 : ∀ i, 0 ≤ logPiX 8 (2 * u 53) ((2 * exp8Eta : ℚ) : ℝ)
      (logXi ((8 : ℕ) * ((2 * exp8Eta : ℚ) : ℝ)) pos E ar br δr) i := fun i => by
    have h2 : (0 : ℝ) ≤ ((2 * exp8Eta : ℚ) : ℝ) := by exact_mod_cast hη2
    have h3 := div_nonneg (mul_nonneg hξ0 h1u) h4u.le
    unfold logPiX ladderB
    split_ifs
    · have := mul_nonneg (pow_nonneg (by rw [hu53]; norm_num : (0 : ℝ) ≤ 2 * u 53) i) h3
      linarith
    · linarith
  have hπx : ∀ i < 8, logPiX 8 (2 * u 53) ((2 * exp8Eta : ℚ) : ℝ)
      (logXi ((8 : ℕ) * ((2 * exp8Eta : ℚ) : ℝ)) pos E ar br δr) i ≤ ((log8PiX xi i : ℚ) : ℝ) := fun i hi => by
    rw [hpx]
    simp only [logPiX, ladderB, hi, ↓reduceIte]
    have := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hξ h1u) h4u.le)
      (pow_nonneg (by rw [hu53]; norm_num : (0 : ℝ) ≤ 2 * u 53) i)
    linarith
  have hxs' := (logXs_le hE hbr hδr (add_nonneg hbr0 hδr0) (add_nonneg hE0 hδr0) z3 z4).trans
    (Rat.cast_le.mpr hxs)
  have hcs' := (logCs_le hE z5).trans (Rat.cast_le.mpr hcs)
  have hxd' := (logXd_le hE hδr0 hδr z5 z6).trans (Rat.cast_le.mpr hxd)
  -- the shared state of step (5)
  have hlen : log8ChiM.length ≤ 8 := by decide
  have hχM0 : ∀ i, 0 ≤ dyFn log8ChiM i := fun i => by
    by_cases hi : i < 8
    · exact hχ0 i hi
    · rw [dyFn_of_le log8ChiM (by omega)]
  obtain ⟨c1, c2⟩ := logBoundC_cert (53 : ℤ) 8 hu (le_upQ 200) (by norm_num) hA3 hη1 hη0 hη2 hη2 hη0
    (le_refl ((l : ℚ) : ℝ)) hE0 hπy pos m hbr0 hδr0 (mul_nonneg h2mq ha0) hap hbpr (lt_of_le_of_lt hbp hbpT1)
    ((mul_le_mul_of_nonneg_left hbp (by positivity)).trans h2bp) hap1 hπ0 exp8F exp8Phi
    (fun k => by unfold exp8Phi; exact abs_nonneg _) d' (fun j => log8SqRun pos m a b j t0) ht0 (fun j _ => rfl)
    hπx0 hπx hφb hph hxs' hcs' hxd' hξ 436 sa hA c4 hB log8F log8F_zero log8Phi
    (fun k => by unfold log8Phi; exact abs_nonneg _) 4 hχM0 hχM hCM hCM1 (dySt log8SH) hsH (dyStW log8HH) hhh
    (dySt log8GG) hgg _ rfl
  refine ⟨c1.trans (Rat.cast_le.mpr hfin), lt_of_le_of_lt c2 ?_⟩
  exact_mod_cast lt_of_le_of_lt hCM hCM1

end ExpansionBounds
