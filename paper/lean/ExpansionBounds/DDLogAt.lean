import ExpansionBounds.DDLog2

/-!
# Proposition 44 (`prop:ddexplog`): the facts of a case of `DD::ln` at `ℓ`

For each kind of case the start's error `E`, the reduction's `δ` and the bound `b` of `|r|` are functions of `ℓ`
in the class of `Convex.lean`, rational at the ends of the case's interval, so the kernel's checks give `DDLAt` at
every `ℓ` of the interval: for `k ≠ 0`, `E = e_0 + e_1ℓ` with `a`, `b` and `δ` constant (`ddl_at1`); for `k = 0`,
`δ = 0` and `b = ℓ + E(ℓ)`, with `E = e_0 + e_1ℓ` (`ddl_at0`) or, from `ℓ = 0`, `E = ℓ(u(1 + ℓ) + ℓ)` (`ddl_at0s`).
-/

namespace ExpansionBounds

open Set

variable (p : ℤ)

/-- `k ≠ 0`: for an interval `[a, b]` of `|r|` with its checks, the facts of the case hold at every `ℓ` from the
least with `k ≠ 0` to `745.2`, with `E = e_0 + e_1ℓ`, the reduction's `δ` at `r̄ = b + δ*`, and the target
`15.351u²ℓ` -/
theorem ddl_at1 (hp : p = 53) {d : ℕ} {a b : ℚ} (hbin : DDL1Bin d a b) (pos : Bool) {l : ℝ}
    (hl1 : ((dyQ ddlLkS : ℚ) : ℝ) ≤ l) (hl2 : l ≤ ((red8X : ℚ) : ℝ)) :
    DDLAt p pos d a l (((ddlE0 : ℚ) : ℝ) + ((ddlE1 : ℚ) : ℝ) * l) b ((ddlDelta (b + dyQ ddlDStarS) : ℚ) : ℝ)
      (((ddlEps : ℚ) : ℝ) * l) := by
  obtain ⟨-, -, -, -, -, -, -, -, cL0, -, cE1, -, cE0, -, -⟩ := ddl_consts
  have hk : DDLChord pos d a (dyQ ddlLkS) (ddlE (dyQ ddlLkS)) b red8X (ddlE red8X) b
      (ddlDelta (b + dyQ ddlDStarS)) := by
    cases pos
    · exact hbin.2
    · exact hbin.1
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hk.1
  have hs : Convex ℝ (Icc ((dyQ ddlLkS : ℚ) : ℝ) ((red8X : ℚ) : ℝ)) := convex_Icc _ _
  have hL0 : (0 : ℝ) ≤ ((dyQ ddlLkS : ℚ) : ℝ) := by exact_mod_cast cL0
  have hE : Cvx (Icc ((dyQ ddlLkS : ℚ) : ℝ) ((red8X : ℚ) : ℝ)) fun x => ((ddlE0 : ℚ) : ℝ) + ((ddlE1 : ℚ) : ℝ) * x :=
    Cvx.affine hs (fun x hx => hL0.trans hx.1) (by exact_mod_cast cE0) (by exact_mod_cast cE1)
  have hδ : Cvx (Icc ((dyQ ddlLkS : ℚ) : ℝ) ((red8X : ℚ) : ℝ))
      fun _ => ((ddlDelta (b + dyQ ddlDStarS) : ℚ) : ℝ) := Cvx.const hs (by exact_mod_cast q6)
  have hb : Cvx (Icc ((dyQ ddlLkS : ℚ) : ℝ) ((red8X : ℚ) : ℝ)) fun _ => ((b : ℚ) : ℝ) :=
    Cvx.const hs (by exact_mod_cast q5)
  have hEv : ∀ x : ℚ, ((ddlE0 : ℚ) : ℝ) + ((ddlE1 : ℚ) : ℝ) * ((x : ℚ) : ℝ) = ((ddlE x : ℚ) : ℝ) := fun x => by
    unfold ddlE
    push_cast
    ring
  exact ddl_chord p hp hk hE hδ hb (hEv _) (hEv _) rfl rfl rfl rfl ⟨hl1, hl2⟩

/-- `k = 0`, the start's linear piece: for a chord with its checks, the facts of the case hold at every `ℓ` of
`[ℓ₁, ℓ₂]`, with `E = e_0 + e_1ℓ`, `b = ℓ + E(ℓ)`, `δ = 0` and the target `15.351u²ℓ` -/
theorem ddl_at0 (hp : p = 53) {pos : Bool} {d : ℕ} {a l₁ l₂ : ℚ}
    (hk : DDLChord pos d a l₁ (ddlE l₁) (l₁ + ddlE l₁) l₂ (ddlE l₂) (l₂ + ddlE l₂) 0) {l : ℝ}
    (hl1 : (l₁ : ℝ) ≤ l) (hl2 : l ≤ (l₂ : ℝ)) :
    DDLAt p pos d a l (((ddlE0 : ℚ) : ℝ) + ((ddlE1 : ℚ) : ℝ) * l) (((ddlE0 : ℚ) : ℝ) + (1 + ((ddlE1 : ℚ) : ℝ)) * l)
      0 (((ddlEps : ℚ) : ℝ) * l) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, cE1, -, cE0, -, -⟩ := ddl_consts
  obtain ⟨q1, -⟩ := hk.1
  have hs : Convex ℝ (Icc (l₁ : ℝ) (l₂ : ℝ)) := convex_Icc _ _
  have hL0 : (0 : ℝ) ≤ ((l₁ : ℚ) : ℝ) := by exact_mod_cast q1
  have hE0 : (0 : ℝ) ≤ ((ddlE0 : ℚ) : ℝ) := by exact_mod_cast cE0
  have hE1 : (0 : ℝ) ≤ ((ddlE1 : ℚ) : ℝ) := by exact_mod_cast cE1
  have hE : Cvx (Icc (l₁ : ℝ) (l₂ : ℝ)) fun x => ((ddlE0 : ℚ) : ℝ) + ((ddlE1 : ℚ) : ℝ) * x :=
    Cvx.affine hs (fun x hx => hL0.trans hx.1) hE0 hE1
  have hb : Cvx (Icc (l₁ : ℝ) (l₂ : ℝ)) fun x => ((ddlE0 : ℚ) : ℝ) + (1 + ((ddlE1 : ℚ) : ℝ)) * x :=
    Cvx.affine hs (fun x hx => hL0.trans hx.1) hE0 (by linarith)
  have hδ : Cvx (Icc (l₁ : ℝ) (l₂ : ℝ)) fun _ => (0 : ℝ) := Cvx.const hs le_rfl
  have hEv : ∀ x : ℚ, ((ddlE0 : ℚ) : ℝ) + ((ddlE1 : ℚ) : ℝ) * ((x : ℚ) : ℝ) = ((ddlE x : ℚ) : ℝ) := fun x => by
    unfold ddlE
    push_cast
    ring
  have hbv : ∀ x : ℚ, ((ddlE0 : ℚ) : ℝ) + (1 + ((ddlE1 : ℚ) : ℝ)) * ((x : ℚ) : ℝ) = ((x + ddlE x : ℚ) : ℝ) :=
    fun x => by
      unfold ddlE
      push_cast
      ring
  exact ddl_chord p hp hk hE hδ hb (hEv _) (hEv _) (hbv _) (hbv _) Rat.cast_zero.symm Rat.cast_zero.symm ⟨hl1, hl2⟩

/-- `k = 0`, the start's second piece: for a chord from `0` with its checks, the facts of the case hold at every
`ℓ` of `[0, ℓ₂]`, with `E = ℓ(u(1 + ℓ) + ℓ)`, `b = ℓ + E(ℓ)`, `δ = 0` and the target `15.351u²ℓ + 2^{-1071}` -/
theorem ddl_at0s (hp : p = 53) {pos : Bool} {d : ℕ} {a l₂ : ℚ}
    (hk : DDLChord0 pos d a l₂ (ddlEs l₂) (l₂ + ddlEs l₂)) {l : ℝ} (hl0 : 0 ≤ l) (hl2 : l ≤ (l₂ : ℝ)) :
    DDLAt p pos d a l (l * (u p * (1 + l) + l)) (l + l * (u p * (1 + l) + l)) 0
      (((ddlEps : ℚ) : ℝ) * l + ((ddlFl : ℚ) : ℝ)) := by
  have hu := red8U_cast p hp
  have hup := u_pos p
  have hs : Convex ℝ (Icc (0 : ℝ) (l₂ : ℝ)) := convex_Icc _ _
  have hid : Cvx (Icc (0 : ℝ) (l₂ : ℝ)) fun x => x := Cvx.id hs fun x hx => hx.1
  have hE : Cvx (Icc (0 : ℝ) (l₂ : ℝ)) fun x => x * (u p * (1 + x) + x) :=
    ((hid.const_mul hup.le).add ((hid.pow 2).const_mul (by linarith : (0 : ℝ) ≤ 1 + u p))).congr fun x _ => by ring
  have hb : Cvx (Icc (0 : ℝ) (l₂ : ℝ)) fun x => x + x * (u p * (1 + x) + x) := hid.add hE
  have hδ : Cvx (Icc (0 : ℝ) (l₂ : ℝ)) fun _ => (0 : ℝ) := Cvx.const hs le_rfl
  have hEv : ((l₂ : ℚ) : ℝ) * (u p * (1 + ((l₂ : ℚ) : ℝ)) + ((l₂ : ℚ) : ℝ)) = ((ddlEs l₂ : ℚ) : ℝ) := by
    unfold ddlEs
    push_cast
    rw [hu]
  have hbv : ((l₂ : ℚ) : ℝ) + ((l₂ : ℚ) : ℝ) * (u p * (1 + ((l₂ : ℚ) : ℝ)) + ((l₂ : ℚ) : ℝ)) =
      ((l₂ + ddlEs l₂ : ℚ) : ℝ) := by
    rw [Rat.cast_add, ← hEv]
  exact ddl_chord0 p hp hk hE hδ hb (by simp) hEv (by simp) hbv (fun _ => rfl) ⟨hl0, hl2⟩

end ExpansionBounds
