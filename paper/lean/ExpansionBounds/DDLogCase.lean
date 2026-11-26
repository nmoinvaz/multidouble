import ExpansionBounds.DDLog2.Defs
import ExpansionBounds.DDLogSub

/-!
# Proposition 44 (`prop:ddexplog`): from the kernel's checks of a case of `DD::ln` to its bound

`DDLChord` and `DDLChord0` (`DDLog2/Defs.lean`) are what the kernel checks at the two ends of an interval of `ℓ`. For
`E`, `δ` and `b` nonnegative, nondecreasing and convex on the interval, with the checked values at its ends, they
give on the whole interval (`ddl_chord`, `ddl_chord0`): the bound of the convex mode within `15.351u²ℓ`, or within
`15.351u²ℓ + 2^{-1071}`; `C ≤ 2^{-40}`; and the floor of EXP's scaling back. The floors of step (5) are asked at
`C`, and hold at every `C ≤ 2^{-40}` once checked there: `h̄` and `C v_{j+1} + e_j` grow with `C` (`ddLogHb_mono`,
`ddLogLv_mono`).
-/

namespace ExpansionBounds

open Set

/-- step (5)'s `h̄` over `ℚ` -/
def ddLogHbQ (uq Dc C : ℚ) (φ' : ℕ → ℚ) (q : ℕ) : ℚ :=
  C * (ddLogVQ C q 2 + ddHornerBQ uq C Dc φ' (ddLogVQ C q) q (q - 2)) +
    (ePQ uq * (C * (ddLogVQ C q 2 + ddHornerBQ uq C Dc φ' (ddLogVQ C q) q (q - 2))) + Dc)

variable (p : ℤ)

/-- `h̄` grows with `C` -/
theorem ddLogHb_mono (hu : 4 * u p < 1) {C C' Dc : ℝ} (hC0 : 0 ≤ C) (hCC : C ≤ C') (hDc : 0 ≤ Dc) {φ' : ℕ → ℝ}
    (hφ' : ∀ k, 0 ≤ φ' k) (q : ℕ) : ddLogHb p Dc C φ' q ≤ ddLogHb p Dc C' φ' q := by
  have hs : Convex ℝ (Icc 0 C') := convex_Icc 0 C'
  have hid : Cvx (Icc 0 C') fun x => x := Cvx.id hs fun x hx => hx.1
  have hv := fun k => cvx_logV hid q k
  have he2 := cvx_ddHornerB p hu (v := fun k x => logV x q k) hid hv hDc hφ' q (q - 2)
  have hZ := hid.mul ((hv 2).add he2)
  have hF := hZ.add ((hZ.const_mul (eP_nonneg p)).add (Cvx.const hs hDc))
  exact hF.mono ⟨hC0, hCC⟩ ⟨hC0.trans hCC, le_rfl⟩ hCC

/-- `C v_{j+1} + e_j` grows with `C`, so the lower bound `1/j - C v_{j+1} - e_j` of Horner's iterates falls -/
theorem ddLogLv_mono (hu : 4 * u p < 1) {C C' Dc : ℝ} (hC0 : 0 ≤ C) (hCC : C ≤ C') (hDc : 0 ≤ Dc) {φ' : ℕ → ℝ}
    (hφ' : ∀ k, 0 ≤ φ' k) (q j : ℕ) :
    C * logV C q (j + 1) + ddHornerB p C Dc φ' (logV C q) q (q - j) ≤
      C' * logV C' q (j + 1) + ddHornerB p C' Dc φ' (logV C' q) q (q - j) := by
  have hs : Convex ℝ (Icc 0 C') := convex_Icc 0 C'
  have hid : Cvx (Icc 0 C') fun x => x := Cvx.id hs fun x hx => hx.1
  have hv := fun k => cvx_logV hid q k
  have hF := (hid.mul (hv (j + 1))).add
    (cvx_ddHornerB p hu (v := fun k x => logV x q k) hid hv hDc hφ' q (q - j))
  exact hF.mono ⟨hC0, hCC⟩ ⟨hC0.trans hCC, le_rfl⟩ hCC

/-- the convex mode's `t̄` is at most its mirror, for `0 ≤ b ≤ 1` -/
theorem ddTbC_le (pos : Bool) {b : ℚ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : ddTbC pos (b : ℝ) ≤ ((ddTbCQ pos b : ℚ) : ℝ) := by
  unfold ddTbC ddTbCQ
  cases pos with
  | true =>
    simp only [↓reduceIte]
    have e := (exp_enclosure b (by rw [abs_le]; constructor <;> linarith)).2
    push_cast
    linarith
  | false => simp

/-- `E_0` with the theorem's `t̄` is at most the mirror's value with the convex mode's, at any larger `b₂ ≤ 1` -/
theorem ddCoreE_le_of_le (hu : 4 * u p < 1) {uq : ℚ} (h : (uq : ℝ) = u p) (pos : Bool) {b : ℝ} {b2 η : ℚ}
    (hη : 0 ≤ η) (hb0 : 0 ≤ b) (hb : b ≤ b2) (hb1 : b2 ≤ 1) {φ : ℕ → ℚ} (hφ : ∀ k, 0 ≤ φ k) (d : ℕ) :
    ddCoreE p (coreT pos b 0) η b (fun k => φ k) d ≤ ((ddCoreEQ uq (ddTbCQ pos b2) η b2 φ d : ℚ) : ℝ) := by
  have hηr : (0 : ℝ) ≤ ((η : ℚ) : ℝ) := by exact_mod_cast hη
  have hs : Convex ℝ (Icc 0 (b2 : ℝ)) := convex_Icc 0 _
  have hid : Cvx (Icc 0 (b2 : ℝ)) fun x => x := Cvx.id hs fun x hx => hx.1
  have hb2r : ((b2 : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hb1
  have hb20 : (0 : ℚ) ≤ b2 := by exact_mod_cast hb0.trans hb
  have hφr : ∀ k, (0 : ℝ) ≤ ((φ k : ℚ) : ℝ) := fun k => by exact_mod_cast hφ k
  have hF := cvx_ddCoreE p hu (cvx_ddTbC hid pos) hid hηr hφr d (fun x hx => by
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith [hx.2])
  have h1 := ddCoreE_mono p hu (coreT_le_ddTbC pos b) (η : ℝ) b (fun k => ((φ k : ℚ) : ℝ)) d
  have h2 := hF.mono ⟨hb0, hb⟩ ⟨hb0.trans hb, le_rfl⟩ hb
  have h3 := ddCoreE_mono p hu (ddTbC_le pos hb20 hb1) (η : ℝ) (b2 : ℝ) (fun k => ((φ k : ℚ) : ℝ)) d
  rw [cast_ddCoreEQ p h]
  exact h1.trans (h2.trans h3)

variable {uq : ℚ} (h : (uq : ℝ) = u p)

include h in
/-- `ddLogHbQ`, cast to `ℝ`, is `h̄` at the cast arguments -/
theorem cast_ddLogHbQ (Dc C : ℚ) (φ' : ℕ → ℚ) (q : ℕ) :
    ((ddLogHbQ uq Dc C φ' q : ℚ) : ℝ) = ddLogHb p Dc C (fun k => φ' k) q := by
  have hv : (fun k => ((ddLogVQ C q k : ℚ) : ℝ)) = logV (C : ℝ) q := funext fun k => cast_ddLogVQ C q k
  simp only [ddLogHbQ, ddLogHb]
  push_cast
  rw [cast_ddHornerBQ p h, hv, cast_ePQ p h, cast_ddLogVQ]

/-- `(u : ℚ)` at `p = 53` -/
theorem red8U_cast (hp : p = 53) : ((red8U : ℚ) : ℝ) = u p := by unfold red8U; exact u_53_rat p hp

/-- `4u < 1` at `p = 53` -/
theorem four_u_lt (hp : p = 53) : 4 * u p < 1 := by
  rw [u_53 p hp]
  norm_num

/-- what the checks of a case give at an `ℓ` of its interval, with the values `E`, `b` and `δ` there and the
target `T`: the bound of the convex mode within `T`; `0 ≤ C ≤ 2^{-40}`; the floor of EXP's scaling back; and the
sizes `b ≤ 1/2`, `E_0 ≤ 1/4` and `E + b + δ ≤ 1` -/
def DDLAt (pos : Bool) (d : ℕ) (a : ℚ) (l E b δ T : ℝ) : Prop :=
  ddLogBoundC p (dd2Eta : ℚ) ((2 * dd2Eta : ℚ) : ℝ) ((2 * dd2Eta : ℚ) : ℝ) (dd2Eta : ℚ) l E pos a b δ
      (fun k => dd2Phi k) d (fun k => ddlPhi k) 3 118 ≤ T ∧
    0 ≤ ddLogCC p (dd2Eta : ℚ) ((2 * dd2Eta : ℚ) : ℝ) ((2 * dd2Eta : ℚ) : ℝ) E pos a b δ (fun k => dd2Phi k) d 118 ∧
    ddLogCC p (dd2Eta : ℚ) ((2 * dd2Eta : ℚ) : ℝ) ((2 * dd2Eta : ℚ) : ℝ) E pos a b δ (fun k => dd2Phi k) d 118 ≤
      ((ddlCg : ℚ) : ℝ) ∧
    (d ≠ 1 → ((dd2Floor : ℚ) : ℝ) * (1 + u p) ≤
      (a : ℝ) / (1 + a) - ddCoreE p (coreT pos b 0) 0 b (fun k => dd2Phi k) d) ∧
    b ≤ 1 / 2 ∧ ddCoreE p (coreT pos b 0) (dd2Eta : ℚ) b (fun k => dd2Phi k) d ≤ 1 / 4 ∧ E + b + δ ≤ 1

/-- the facts of a case at `ℓ` beside the bound, from the checks at the upper end `ℓ₂` of its interval, for `E`,
`δ` and `b` in the class on `[ℓ₁, ℓ₂]` with the checked values at `ℓ₂` -/
theorem ddl_side (hp : p = 53) {pos : Bool} {d : ℕ} {a l₂ E2 b2 δ2 : ℚ} (k2 : DDLEnd pos d a l₂ E2 b2 δ2)
    (cC : ddlCQ pos d a E2 b2 δ2 ≤ ddlCg) (cF : DDLFloor pos d a b2) (cS : DDLSize pos d b2) {l₁ : ℝ}
    {E δ b : ℝ → ℝ} (hE : Cvx (Icc l₁ (l₂ : ℝ)) E) (hδ : Cvx (Icc l₁ (l₂ : ℝ)) δ) (hb : Cvx (Icc l₁ (l₂ : ℝ)) b)
    (hE2 : E l₂ = E2) (hb2 : b l₂ = b2) (hδ2 : δ l₂ = δ2) {l : ℝ} (hl : l ∈ Icc l₁ (l₂ : ℝ)) :
    0 ≤ ddLogCC p (dd2Eta : ℚ) ((2 * dd2Eta : ℚ) : ℝ) ((2 * dd2Eta : ℚ) : ℝ) (E l) pos a (b l) (δ l)
        (fun k => dd2Phi k) d 118 ∧
      ddLogCC p (dd2Eta : ℚ) ((2 * dd2Eta : ℚ) : ℝ) ((2 * dd2Eta : ℚ) : ℝ) (E l) pos a (b l) (δ l)
        (fun k => dd2Phi k) d 118 ≤ ((ddlCg : ℚ) : ℝ) ∧
      (d ≠ 1 → ((dd2Floor : ℚ) : ℝ) * (1 + u p) ≤
        (a : ℝ) / (1 + a) - ddCoreE p (coreT pos (b l) 0) 0 (b l) (fun k => dd2Phi k) d) ∧
      b l ≤ 1 / 2 ∧ ddCoreE p (coreT pos (b l) 0) (dd2Eta : ℚ) (b l) (fun k => dd2Phi k) d ≤ 1 / 4 ∧
      E l + b l + δ l ≤ 1 := by
  have hu := red8U_cast p hp
  have h4 := four_u_lt p hp
  have hη : (0 : ℚ) ≤ dd2Eta := by unfold dd2Eta; positivity
  have hη2 : (0 : ℚ) ≤ 2 * dd2Eta := by linarith
  have hηr : (0 : ℝ) ≤ ((dd2Eta : ℚ) : ℝ) := by exact_mod_cast hη
  have hη2r : (0 : ℝ) ≤ ((2 * dd2Eta : ℚ) : ℝ) := by exact_mod_cast hη2
  have hφF : ∀ k, 0 ≤ dd2Phi k := fun k => abs_nonneg _
  have hφ' : ∀ k, 0 ≤ ddlPhi k := fun k => abs_nonneg _
  have hφFr : ∀ k, (0 : ℝ) ≤ ((dd2Phi k : ℚ) : ℝ) := fun k => by exact_mod_cast hφF k
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := k2
  obtain ⟨z1, z2⟩ := cS
  have h2 : (l₂ : ℝ) ∈ Icc l₁ (l₂ : ℝ) := right_mem_Icc.mpr (hl.1.trans hl.2)
  have hb2r : ((b2 : ℚ) : ℝ) ≤ 1 / 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr z1
    push_cast at this
    linarith
  have hbl := hb.mono hl h2 hl.2
  have hEl := hE.mono hl h2 hl.2
  have hδl := hδ.mono hl h2 hl.2
  rw [hb2] at hbl
  rw [hE2] at hEl
  rw [hδ2] at hδl
  have hbd : ∀ x ∈ Icc l₁ (l₂ : ℝ), b x < (d : ℝ) + 2 := fun x hx => by
    have h1 := hb.mono hx h2 hx.2
    rw [hb2] at h1
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  have hCv := cvx_ddLogCC p h4 hE hδ hb hηr hη2r hη2r pos (a : ℝ) hφFr d hbd 118
  have hb1 : b2 ≤ 1 := by linarith
  refine ⟨hCv.nonneg l hl, ?_, fun hd => ?_, hbl.trans hb2r, ?_, ?_⟩
  · have hm := hCv.mono hl h2 hl.2
    rw [hE2, hb2, hδ2] at hm
    have hn := (ddLogBoundC_le p hu h4 hη hη2 hη2 hη q1 q2 q3 q4 q5 q6 q7 pos hφF d hφ' 3 118 q8).2
    exact hm.trans (hn.trans (by exact_mod_cast cC))
  · have h1 := ddCoreE_le_of_le p h4 hu pos (le_refl (0 : ℚ)) (hb.nonneg l hl) hbl hb1 hφF d
    rw [Rat.cast_zero] at h1
    have h3 := (Rat.cast_le (K := ℝ)).mpr (cF hd)
    rw [Rat.cast_mul, Rat.cast_add, Rat.cast_one, Rat.cast_sub, Rat.cast_div, Rat.cast_add, Rat.cast_one, hu] at h3
    linarith
  · have h1 := ddCoreE_le_of_le p h4 hu pos hη (hb.nonneg l hl) hbl hb1 hφF d
    have h3 : ((ddCoreEQ red8U (ddTbCQ pos b2) dd2Eta b2 dd2Phi d : ℚ) : ℝ) ≤ 1 / 4 := by
      have := (Rat.cast_le (K := ℝ)).mpr z2
      rw [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at this
      exact this
    exact h1.trans h3
  · have h7 : ((E2 : ℚ) : ℝ) + b2 + δ2 ≤ 1 := by exact_mod_cast q7
    linarith

/-- from the kernel's checks of a chord to the interval: for `E`, `δ` and `b` in the class on `[ℓ₁, ℓ₂]` with the
checked values at its ends, `DDLAt` holds at every `ℓ` of the interval with the target `15.351u²ℓ` -/
theorem ddl_chord (hp : p = 53) {pos : Bool} {d : ℕ} {a l₁ E1 b1 l₂ E2 b2 δq : ℚ}
    (hk : DDLChord pos d a l₁ E1 b1 l₂ E2 b2 δq) {E δ b : ℝ → ℝ} (hE : Cvx (Icc (l₁ : ℝ) l₂) E)
    (hδ : Cvx (Icc (l₁ : ℝ) l₂) δ) (hb : Cvx (Icc (l₁ : ℝ) l₂) b) (hE1 : E l₁ = E1) (hE2 : E l₂ = E2)
    (hb1 : b l₁ = b1) (hb2 : b l₂ = b2) (hδ1 : δ l₁ = δq) (hδ2 : δ l₂ = δq) {l : ℝ} (hl : l ∈ Icc (l₁ : ℝ) l₂) :
    DDLAt p pos d a l (E l) (b l) (δ l) (((ddlEps : ℚ) : ℝ) * l) := by
  have hu := red8U_cast p hp
  have h4 := four_u_lt p hp
  obtain ⟨k1, k2, c1, c2, cC, cF, cS⟩ := hk
  have hη : (0 : ℚ) ≤ dd2Eta := by unfold dd2Eta; positivity
  have hη2 : (0 : ℚ) ≤ 2 * dd2Eta := by linarith
  have hφF : ∀ k, 0 ≤ dd2Phi k := fun k => abs_nonneg _
  have hφ' : ∀ k, 0 ≤ ddlPhi k := fun k => abs_nonneg _
  exact ⟨dd_log_chord_cert p hu h4 hη hη2 hη2 hη hE hδ hb hE1 hE2 hb1 hb2 hδ1 hδ2 pos hφF d hφ' 3 118 k1 k2 c1 c2
    hl, ddl_side p hp k2 cC cF cS hE hδ hb hE2 hb2 hδ2 hl⟩

/-- from the kernel's checks of a chord from `0` to the interval `[0, ℓ₂]`: `DDLAt` holds at every `ℓ` of the
interval with the target `15.351u²ℓ + 2^{-1071}` -/
theorem ddl_chord0 (hp : p = 53) {pos : Bool} {d : ℕ} {a l₂ E2 b2 : ℚ} (hk : DDLChord0 pos d a l₂ E2 b2)
    {E δ b : ℝ → ℝ} (hE : Cvx (Icc (0 : ℝ) l₂) E) (hδ : Cvx (Icc (0 : ℝ) l₂) δ) (hb : Cvx (Icc (0 : ℝ) l₂) b)
    (hE1 : E 0 = 0) (hE2 : E l₂ = E2) (hb1 : b 0 = 0) (hb2 : b l₂ = b2) (hδ0 : ∀ x, δ x = 0) {l : ℝ}
    (hl : l ∈ Icc (0 : ℝ) l₂) :
    DDLAt p pos d a l (E l) (b l) (δ l) (((ddlEps : ℚ) : ℝ) * l + ((ddlFl : ℚ) : ℝ)) := by
  have hu := red8U_cast p hp
  have h4 := four_u_lt p hp
  obtain ⟨k1, k2, c1, c2, cC, cF, cS⟩ := hk
  have hη : (0 : ℚ) ≤ dd2Eta := by unfold dd2Eta; positivity
  have hη2 : (0 : ℚ) ≤ 2 * dd2Eta := by linarith
  have hφF : ∀ k, 0 ≤ dd2Phi k := fun k => abs_nonneg _
  have hφ' : ∀ k, 0 ≤ ddlPhi k := fun k => abs_nonneg _
  have hδ2 : δ l₂ = ((0 : ℚ) : ℝ) := by rw [hδ0, Rat.cast_zero]
  exact ⟨dd_log_chord_zero_cert p hu h4 hη hη2 hη2 hη hE hδ hb (by rw [hE1, Rat.cast_zero]) hE2
    (by rw [hb1, Rat.cast_zero]) hb2 (by rw [hδ0, Rat.cast_zero]) hδ2 pos hφF d hφ' 3 118 k1 k2 c1 c2 hl,
    ddl_side p hp k2 cC cF cS hE hδ hb hE2 hb2 hδ2 hl⟩

end ExpansionBounds
