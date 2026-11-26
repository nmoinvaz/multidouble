import ExpansionBounds.DDLogEval

/-!
# Proposition 44 (`prop:ddexplog`): the chords of `DD::ln`'s bound from the kernel's checks

For a fixed case the bound of the convex mode is a function of `ℓ` through the start's error `E(ℓ)`, the reduction's
`δ(ℓ)` and the bound `b(ℓ)` of `|r|`, each nonnegative, nondecreasing and convex on the interval of the case, with
rational values at its two ends. `DDLogEnd` is what the kernel checks at an end beside the bound: the sizes that the
enclosure of `e^z` needs, and `C < 1` on the mirror. From the mirror's bound within `εℓ` at both ends, the real bound
is within `εℓ` on the interval (`dd_log_chord_cert`), and from `Φ` at `0` and `εℓ₂ + Φ` at `ℓ₂`, within `εℓ + Φ` on
`[0, ℓ₂]` (`dd_log_chord_zero_cert`).
-/

namespace ExpansionBounds

open Set

variable (p : ℤ)

/-- what the kernel checks at an end `ℓ` of a chord, beside the bound: nonnegative arguments, `a ≤ 1` and
`E + b + δ ≤ 1` for the enclosures of `e^z`, and `C < 1` on the mirror -/
def DDLogEnd (uq η ηx ηp ℓ E : ℚ) (pos : Bool) (a b δ : ℚ) (φF : ℕ → ℚ) (d' : ℕ) (B : ℤ) : Prop :=
  0 ≤ ℓ ∧ 0 ≤ E ∧ 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ b ∧ 0 ≤ δ ∧ E + b + δ ≤ 1 ∧ ddLogCCQ uq η ηx ηp E pos a b δ φF d' B < 1

instance (uq η ηx ηp ℓ E : ℚ) (pos : Bool) (a b δ : ℚ) (φF : ℕ → ℚ) (d' : ℕ) (B : ℤ) :
    Decidable (DDLogEnd uq η ηx ηp ℓ E pos a b δ φF d' B) := by
  unfold DDLogEnd
  infer_instance

variable {uq : ℚ} (h : (uq : ℝ) = u p)

include h in
/-- Theorem 42's first chord read with `n = 2`, from the kernel's checks at the two ends: with `E`, `δ` and `b` in
the class on `[ℓ₁, ℓ₂]` and rational at its ends, the mirror's bound within `εℓ` at both ends gives the bound of the
convex mode within `εℓ` on the interval -/
theorem dd_log_chord_cert (hu : 4 * u p < 1) {η ηx ηp ηc : ℚ} (hη : 0 ≤ η) (hηx : 0 ≤ ηx) (hηp : 0 ≤ ηp)
    (hηc : 0 ≤ ηc) {l₁ l₂ : ℚ} {E δ b : ℝ → ℝ} (hE : Cvx (Icc (l₁ : ℝ) l₂) E) (hδ : Cvx (Icc (l₁ : ℝ) l₂) δ)
    (hb : Cvx (Icc (l₁ : ℝ) l₂) b) {E1 E2 b1 b2 δ1 δ2 : ℚ} (hE1 : E l₁ = E1) (hE2 : E l₂ = E2) (hb1 : b l₁ = b1)
    (hb2 : b l₂ = b2) (hδ1 : δ l₁ = δ1) (hδ2 : δ l₂ = δ2) (pos : Bool) {a : ℚ} {φF : ℕ → ℚ}
    (hφF : ∀ k, 0 ≤ φF k) (d' : ℕ) {φ' : ℕ → ℚ} (hφ' : ∀ k, 0 ≤ φ' k) (q : ℕ) (B : ℤ)
    (k1 : DDLogEnd uq η ηx ηp l₁ E1 pos a b1 δ1 φF d' B) (k2 : DDLogEnd uq η ηx ηp l₂ E2 pos a b2 δ2 φF d' B)
    {ε : ℚ} (c1 : ddLogBoundCQ uq η ηx ηp ηc l₁ E1 pos a b1 δ1 φF d' φ' q B ≤ ε * l₁)
    (c2 : ddLogBoundCQ uq η ηx ηp ηc l₂ E2 pos a b2 δ2 φF d' φ' q B ≤ ε * l₂) {l : ℝ}
    (hl : l ∈ Icc (l₁ : ℝ) l₂) :
    ddLogBoundC p η ηx ηp ηc l (E l) pos a (b l) (δ l) (fun k => φF k) d' (fun k => φ' k) q B ≤ ε * l := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := k1
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := k2
  obtain ⟨m1, -⟩ := ddLogBoundC_le p h hu hη hηx hηp hηc p1 p2 p3 p4 p5 p6 p7 pos hφF d' hφ' q B p8
  obtain ⟨n1, n2⟩ := ddLogBoundC_le p h hu hη hηx hηp hηc q1 q2 q3 q4 q5 q6 q7 pos hφF d' hφ' q B q8
  have hφFr : ∀ k, (0 : ℝ) ≤ ((φF k : ℚ) : ℝ) := fun k => by exact_mod_cast hφF k
  have hφ'r : ∀ k, (0 : ℝ) ≤ ((φ' k : ℚ) : ℝ) := fun k => by exact_mod_cast hφ' k
  have hbd : b l₂ < (d' : ℝ) + 2 := by
    rw [hb2]
    have h1 : ((b2 : ℚ) : ℝ) ≤ 1 := by exact_mod_cast (by linarith : b2 ≤ 1)
    have h2 : (0 : ℝ) ≤ (d' : ℝ) := Nat.cast_nonneg d'
    linarith
  refine dd_log_chord p hu (by exact_mod_cast p1) hE hδ hb (by exact_mod_cast hη) (by exact_mod_cast hηx)
    (by exact_mod_cast hηp) (by exact_mod_cast hηc) pos a hφFr d' hbd hφ'r q B ?_ ?_ ?_ hl
  · rw [hE2, hb2, hδ2]
    exact lt_of_le_of_lt n2 (by exact_mod_cast q8)
  · rw [hE1, hb1, hδ1]
    exact m1.trans (by exact_mod_cast c1)
  · rw [hE2, hb2, hδ2]
    exact n1.trans (by exact_mod_cast c2)

include h in
/-- Theorem 42's second chord read with `n = 2`, from the kernel's checks at `0` and `ℓ₂`: the mirror's bound within
`Φ` at `0` and within `εℓ₂ + Φ` at `ℓ₂` gives the bound of the convex mode within `εℓ + Φ` on `[0, ℓ₂]` -/
theorem dd_log_chord_zero_cert (hu : 4 * u p < 1) {η ηx ηp ηc : ℚ} (hη : 0 ≤ η) (hηx : 0 ≤ ηx) (hηp : 0 ≤ ηp)
    (hηc : 0 ≤ ηc) {l₂ : ℚ} {E δ b : ℝ → ℝ} (hE : Cvx (Icc (0 : ℝ) l₂) E) (hδ : Cvx (Icc (0 : ℝ) l₂) δ)
    (hb : Cvx (Icc (0 : ℝ) l₂) b) {E1 E2 b1 b2 δ1 δ2 : ℚ} (hE1 : E 0 = E1) (hE2 : E l₂ = E2) (hb1 : b 0 = b1)
    (hb2 : b l₂ = b2) (hδ1 : δ 0 = δ1) (hδ2 : δ l₂ = δ2) (pos : Bool) {a : ℚ} {φF : ℕ → ℚ}
    (hφF : ∀ k, 0 ≤ φF k) (d' : ℕ) {φ' : ℕ → ℚ} (hφ' : ∀ k, 0 ≤ φ' k) (q : ℕ) (B : ℤ)
    (k1 : DDLogEnd uq η ηx ηp 0 E1 pos a b1 δ1 φF d' B) (k2 : DDLogEnd uq η ηx ηp l₂ E2 pos a b2 δ2 φF d' B)
    {ε Φ : ℚ} (c1 : ddLogBoundCQ uq η ηx ηp ηc 0 E1 pos a b1 δ1 φF d' φ' q B ≤ Φ)
    (c2 : ddLogBoundCQ uq η ηx ηp ηc l₂ E2 pos a b2 δ2 φF d' φ' q B ≤ ε * l₂ + Φ) {l : ℝ}
    (hl : l ∈ Icc (0 : ℝ) l₂) :
    ddLogBoundC p η ηx ηp ηc l (E l) pos a (b l) (δ l) (fun k => φF k) d' (fun k => φ' k) q B ≤ ε * l + Φ := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := k1
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := k2
  obtain ⟨m1, -⟩ := ddLogBoundC_le p h hu hη hηx hηp hηc p1 p2 p3 p4 p5 p6 p7 pos hφF d' hφ' q B p8
  obtain ⟨n1, n2⟩ := ddLogBoundC_le p h hu hη hηx hηp hηc q1 q2 q3 q4 q5 q6 q7 pos hφF d' hφ' q B q8
  have hφFr : ∀ k, (0 : ℝ) ≤ ((φF k : ℚ) : ℝ) := fun k => by exact_mod_cast hφF k
  have hφ'r : ∀ k, (0 : ℝ) ≤ ((φ' k : ℚ) : ℝ) := fun k => by exact_mod_cast hφ' k
  have hbd : b l₂ < (d' : ℝ) + 2 := by
    rw [hb2]
    have h1 : ((b2 : ℚ) : ℝ) ≤ 1 := by exact_mod_cast (by linarith : b2 ≤ 1)
    have h2 : (0 : ℝ) ≤ (d' : ℝ) := Nat.cast_nonneg d'
    linarith
  rw [Rat.cast_zero] at m1
  refine dd_log_chord_zero p hu hE hδ hb (by exact_mod_cast hη) (by exact_mod_cast hηx)
    (by exact_mod_cast hηp) (by exact_mod_cast hηc) pos a hφFr d' hbd hφ'r q B ?_ ?_ ?_ hl
  · rw [hE2, hb2, hδ2]
    exact lt_of_le_of_lt n2 (by exact_mod_cast q8)
  · rw [hE1, hb1, hδ1]
    exact m1.trans (by exact_mod_cast c1)
  · rw [hE2, hb2, hδ2]
    exact n1.trans (by exact_mod_cast c2)

end ExpansionBounds
