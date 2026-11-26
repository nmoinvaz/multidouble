import ExpansionBounds.LogEval

/-!
# The steps of the convex bounds on a rational state

The lemmas of `ExpEval.lean` and `TrigEval.lean` for the bounds with VecSum's second bound alone: Horner's convex
bounds grow with `π^z`, `z̄`, `ε_z` and `v` (`hornerBC_mono2`) and are at most their rounded mirrors
(`hornerRunLC_ge`); from a state above Horner's, step (3)'s three steps give a state above `core0C`'s (`core0C_le`,
`core0C_cert`), and a squaring one above `sqBC`'s (`sqBC_le`, `coreEC_cert`). `G_MUL` and `G_ADD` enter the proofs
of the bounds with the minimum only through their monotonicity, their nonnegativity and their mirrors, so the proofs
are the same, and most of this file is a copy under the convex bounds' names:

* of `GMono.lean`: `GmulC_mono` (`Gmul_mono`), `GaddC_mono` (`Gadd_mono`), with `gErrC_mono` and `gPartsC_mono`
  (`gErr_mono'`, `gParts_mono'`) and `Vc_mono` (`Vb_mono` of `AccK.lean`);
* of `ExpEval.lean`: `hornerBC_mono2`, `GmulC_mono_lt`, `GaddC_mono_lt`, `GmulEC_trunc_left`, `GmulPC_trunc_left`,
  `hornerBC_trunc`, `GmulC_le_mirror`, `GaddC_le_mirror`, `core0C_le`, `sqBC_le`, `core0C_cert`, `coreEC_cert` and
  `core0C_nonneg`, each from the lemma of the same name without the `C`;
* of `TrigEval.lean`: `hornerRunLC_add`, `hornerRunLC_succ`, `hornerC_step_le` (`horner_step_le`), `gPartsC_of_le`
  and `hornerRunLC_ge`.

`GmulC_nonneg`, `GaddC_nonneg` and `hornerBC_nonneg` are new: they come from `GmulC_sand`, `GaddC_sand` and
`hornerB_le_hornerBC`.
-/

namespace ExpansionBounds

open Finset

section Generic

variable (p : ℤ) (n : ℕ)

/-- `V_j`, VecSum's second bound alone, grows with the level bounds. -/
theorem Vc_mono {X X' : ℕ → ℝ} (hX : ∀ m, X m ≤ X' m) (j : ℕ) : Vc p n X j ≤ Vc p n X' j :=
  mul_le_mul_of_nonneg_left (sigmaX_mono n hX _)
    (mul_nonneg (us_nonneg p) (pow_nonneg (by linarith [u_pos p]) _))

/-- Lemma 13 (a)'s convex bound grows with the level bounds, `Z̄` and `F`, of any sign. -/
theorem gErrC_mono {X X' : ℕ → ℝ} (hX : ∀ m, X m ≤ X' m) {Zb Zb' : ℝ} (hZ : Zb ≤ Zb') {Fb Fb' : ℝ}
    (hF : Fb ≤ Fb') : gErrC p n X Zb Fb ≤ gErrC p n X' Zb' Fb' := by
  have hu := u_pos p
  simp only [gErrC]
  refine add_le_add (add_le_add (mul_le_mul_of_nonneg_left hZ (pow_nonneg hu.le _))
    (mul_le_mul_of_nonneg_left hF (by positivity))) (sum_le_sum fun j _ => ?_)
  exact mul_le_mul_of_nonneg_left (Vc_mono p n hX j) (by positivity)

/-- Lemma 13 (b)'s convex bounds grow with the level bounds, `Z̄` and `F`, of any sign. -/
theorem gPartsC_mono {X X' : ℕ → ℝ} (hX : ∀ m, X m ≤ X' m) {Zb Zb' : ℝ} (hZ : Zb ≤ Zb') {Fb Fb' : ℝ}
    (hF : Fb ≤ Fb') : ∀ i, gPartsC p n X Zb Fb i ≤ gPartsC p n X' Zb' Fb' i
  | 0 => by
    simp only [gPartsC]
    exact mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add hZ hF) (sum_le_sum fun j _ => Vc_mono p n hX j)) (by linarith [u_pos p])
  | i + 1 => by
    simp only [gPartsC]
    split_ifs
    · exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (gPartsC_mono hX hZ hF i) (u_pos p).le)
          (sum_le_sum fun j _ => Vc_mono p n hX j)) (by linarith [u_pos p])
    · exact le_rfl

/-- The convex `G_MUL` grows with the part bounds of its operands and with `Z̄`, of any sign. -/
theorem GmulC_mono (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {α α' β β' : ℕ → ℝ} (hα0 : ∀ i, 0 ≤ α i)
    (hβ0 : ∀ j, 0 ≤ β j) (hα : ∀ i, α i ≤ α' i) (hβ : ∀ j, β j ≤ β' j) {Zb Zb' : ℝ} (hZ : Zb ≤ Zb') :
    GmulEC p n α β Zb ≤ GmulEC p n α' β' Zb' ∧ ∀ i, GmulPC p n α β Zb i ≤ GmulPC p n α' β' Zb' i := by
  have hX := mulX_mono p n hA3 hα0 hβ0 hα hβ
  have hF : mulR p n α β + mulDelta n α β ≤ mulR p n α' β' + mulDelta n α' β' :=
    add_le_add (mulR_mono p n hA3 hα0 hβ0 hα hβ) (mulDelta_mono n hα0 hβ0 hα hβ)
  exact ⟨gErrC_mono p n hX hZ hF, gPartsC_mono p n hX hZ hF⟩

/-- The convex `G_ADD` grows with the part bounds of its operands and with `Z̄`, of any sign. -/
theorem GaddC_mono (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {α α' β β' : ℕ → ℝ} (hα : ∀ i, α i ≤ α' i)
    (hβ : ∀ j, β j ≤ β' j) {Zb Zb' : ℝ} (hZ : Zb ≤ Zb') :
    GaddEC p n α β Zb ≤ GaddEC p n α' β' Zb' ∧ ∀ i, GaddPC p n α β Zb i ≤ GaddPC p n α' β' Zb' i := by
  have hl : ∀ m, α m + β m ≤ α' m + β' m := fun m => add_le_add (hα m) (hβ m)
  have hX := pairX_mono p n hA3 hl
  have hF : pairR p n (fun m => α m + β m) ≤ pairR p n fun m => α' m + β' m :=
    mul_le_mul_of_nonneg_left (hX n) (mul_nonneg (Nat.cast_nonneg _) (u_pos p).le)
  exact ⟨gErrC_mono p n hX hZ hF, gPartsC_mono p n hX hZ hF⟩

/-- The convex `G_MUL`'s bounds are nonnegative. -/
theorem GmulC_nonneg (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {α β : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i) (hβ : ∀ j, 0 ≤ β j)
    {Zb : ℝ} (hZ : 0 ≤ Zb) : 0 ≤ GmulEC p n α β Zb ∧ ∀ i, 0 ≤ GmulPC p n α β Zb i := by
  obtain ⟨h1, h2⟩ := GmulC_sand p n hA3 (fun i => Sand.refl (hα i)) (fun j => Sand.refl (hβ j)) (Sand.refl hZ)
  exact ⟨h1.nonneg, fun i => (h2 i).nonneg⟩

/-- The convex `G_ADD`'s bounds are nonnegative. -/
theorem GaddC_nonneg (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {α β : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i) (hβ : ∀ j, 0 ≤ β j)
    {Zb : ℝ} (hZ : 0 ≤ Zb) : 0 ≤ GaddEC p n α β Zb ∧ ∀ i, 0 ≤ GaddPC p n α β Zb i := by
  obtain ⟨h1, h2⟩ := GaddC_sand p n hA3 (fun i => Sand.refl (hα i)) (fun j => Sand.refl (hβ j)) (Sand.refl hZ)
  exact ⟨h1.nonneg, fun i => (h2 i).nonneg⟩

/-- Horner's convex bounds are nonnegative. -/
theorem hornerBC_nonneg (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {πz : ℕ → ℝ} (hπz : ∀ i, 0 ≤ πz i) {zb εz η : ℝ}
    (hzb : 0 ≤ zb) (hεz : 0 ≤ εz) (hη : 0 ≤ η) (Fk : ℕ → ℕ → ℝ) {φ v : ℕ → ℝ} (hφ : ∀ k, 0 ≤ φ k)
    (hv : ∀ k, 0 ≤ v k) (d j : ℕ) :
    0 ≤ (hornerBC p n πz zb εz η Fk φ v d j).1 ∧ ∀ i, 0 ≤ (hornerBC p n πz zb εz η Fk φ v d j).2 i := by
  obtain ⟨n1, n2⟩ := hornerB_nonneg p n hA3 hπz hzb hεz hη Fk hφ hv d j
  obtain ⟨c1, c2⟩ := hornerB_le_hornerBC p n hA3 hπz hzb hεz hη Fk hφ hv d j
  exact ⟨n1.trans c1, fun i => (n2 i).trans (c2 i)⟩


/-- Horner's bounds `(e_k, π^{(k)})` of Lemma 33 grow with `π^z`, `z̄`, `ε_z` and `v` -/
theorem hornerBC_mono2 (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {πz πz' : ℕ → ℝ} (hπ0 : ∀ i, 0 ≤ πz i)
    (hπ : ∀ i, πz i ≤ πz' i) {zb zb' εz εz' η : ℝ} (hzb : 0 ≤ zb) (hzz : zb ≤ zb') (hε0 : 0 ≤ εz)
    (hε : εz ≤ εz') (hη : 0 ≤ η) (Fk : ℕ → ℕ → ℝ) {φ v v' : ℕ → ℝ} (hφ : ∀ k, 0 ≤ φ k) (hv : ∀ k, 0 ≤ v k)
    (hvv : ∀ k, v k ≤ v' k) (d : ℕ) : ∀ j,
    (hornerBC p n πz zb εz η Fk φ v d j).1 ≤ (hornerBC p n πz' zb' εz' η Fk φ v' d j).1 ∧
      ∀ i, (hornerBC p n πz zb εz η Fk φ v d j).2 i ≤ (hornerBC p n πz' zb' εz' η Fk φ v' d j).2 i
  | 0 => ⟨le_rfl, fun _ => le_rfl⟩
  | j + 1 => by
    obtain ⟨i1, i2⟩ := hornerBC_mono2 hA3 hπ0 hπ hzb hzz hε0 hε hη Fk hφ hv hvv d j
    obtain ⟨n1, n2⟩ := hornerBC_nonneg p n hA3 hπ0 hzb hε0 hη Fk hφ hv d j
    have hε0' : 0 ≤ εz' := hε0.trans hε
    have hvk := hv (d - (j + 1) + 1)
    have hvk' := hvv (d - (j + 1) + 1)
    have hc : (1 + εz) * zb ≤ (1 + εz') * zb' := mul_le_mul (by linarith) hzz hzb (by linarith)
    have hc0 : 0 ≤ (1 + εz) * zb := mul_nonneg (by linarith) hzb
    have hZm : (1 + εz) * zb * (v (d - (j + 1) + 1) + (hornerBC p n πz zb εz η Fk φ v d j).1) ≤
        (1 + εz') * zb' * (v' (d - (j + 1) + 1) + (hornerBC p n πz' zb' εz' η Fk φ v' d j).1) :=
      mul_le_mul hc (by linarith) (add_nonneg hvk n1) (hc0.trans hc)
    obtain ⟨m1, m2⟩ := GmulC_mono p n hA3 hπ0 n2 hπ i2 hZm
    have hD : (1 + εz) * zb * (hornerBC p n πz zb εz η Fk φ v d j).1 + εz * zb * v (d - (j + 1) + 1) +
          φ (d - (j + 1)) + (GmulEC p n πz (hornerBC p n πz zb εz η Fk φ v d j).2
            ((1 + εz) * zb * (v (d - (j + 1) + 1) + (hornerBC p n πz zb εz η Fk φ v d j).1)) + n * η) ≤
        (1 + εz') * zb' * (hornerBC p n πz' zb' εz' η Fk φ v' d j).1 + εz' * zb' * v' (d - (j + 1) + 1) +
          φ (d - (j + 1)) + (GmulEC p n πz' (hornerBC p n πz' zb' εz' η Fk φ v' d j).2
            ((1 + εz') * zb' * (v' (d - (j + 1) + 1) + (hornerBC p n πz' zb' εz' η Fk φ v' d j).1)) + n * η) := by
      have a1 : (1 + εz) * zb * (hornerBC p n πz zb εz η Fk φ v d j).1 ≤
          (1 + εz') * zb' * (hornerBC p n πz' zb' εz' η Fk φ v' d j).1 := mul_le_mul hc i1 n1 (hc0.trans hc)
      have a2 : εz * zb * v (d - (j + 1) + 1) ≤ εz' * zb' * v' (d - (j + 1) + 1) :=
        mul_le_mul (mul_le_mul hε hzz hzb hε0') hvk' hvk (mul_nonneg hε0' (hzb.trans hzz))
      linarith
    obtain ⟨g1, g2⟩ := GaddC_mono p n hA3 (fun i => le_refl |Fk (d - (j + 1)) i|)
      (fun i => add_le_add (m2 i) (le_refl η)) (add_le_add (hvv (d - (j + 1))) hD)
    exact ⟨add_le_add hD g1, g2⟩

/-- `G_MUL` grows with part bounds compared below `n` -/
theorem GmulC_mono_lt (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {α α' β β' : ℕ → ℝ} (hα0 : ∀ i < n, 0 ≤ α i)
    (hβ0 : ∀ j < n, 0 ≤ β j) (hα : ∀ i < n, α i ≤ α' i) (hβ : ∀ j < n, β j ≤ β' j) {Zb Zb' : ℝ} (hZ : Zb ≤ Zb') :
    GmulEC p n α β Zb ≤ GmulEC p n α' β' Zb' ∧ ∀ i, GmulPC p n α β Zb i ≤ GmulPC p n α' β' Zb' i := by
  have h := GmulC_mono p n hA3 (trunc_nonneg n hα0) (trunc_nonneg n hβ0) (trunc_le n hα) (trunc_le n hβ) hZ
  rw [(GmulC_trunc p n α β Zb).1, (GmulC_trunc p n α β Zb).2, (GmulC_trunc p n α' β' Zb').1,
    (GmulC_trunc p n α' β' Zb').2] at h
  exact h

/-- `G_ADD` grows with part bounds compared below `n` -/
theorem GaddC_mono_lt (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {α α' β β' : ℕ → ℝ}
    (hα : ∀ i < n, α i ≤ α' i) (hβ : ∀ j < n, β j ≤ β' j) {Zb Zb' : ℝ} (hZ : Zb ≤ Zb') :
    GaddEC p n α β Zb ≤ GaddEC p n α' β' Zb' ∧ ∀ i, GaddPC p n α β Zb i ≤ GaddPC p n α' β' Zb' i := by
  have h := GaddC_mono p n hA3 (trunc_le n hα) (trunc_le n hβ) hZ
  rw [(GaddC_trunc p n hn α β Zb).1, (GaddC_trunc p n hn α β Zb).2, (GaddC_trunc p n hn α' β' Zb').1,
    (GaddC_trunc p n hn α' β' Zb').2] at h
  exact h

/-- the convex `G_MUL`'s error bound uses its first operand below `n` only -/
theorem GmulEC_trunc_left (α β : ℕ → ℝ) (Zb : ℝ) : GmulEC p n (trunc n α) β Zb = GmulEC p n α β Zb := by
  rw [← (GmulC_trunc p n (trunc n α) β Zb).1, trunc_trunc, (GmulC_trunc p n α β Zb).1]

/-- the convex `G_MUL`'s part bounds use the first operand below `n` only -/
theorem GmulPC_trunc_left (α β : ℕ → ℝ) (Zb : ℝ) : GmulPC p n (trunc n α) β Zb = GmulPC p n α β Zb := by
  rw [← (GmulC_trunc p n (trunc n α) β Zb).2, trunc_trunc, (GmulC_trunc p n α β Zb).2]

/-- Horner's bounds use `π^z` below `n` only -/
theorem hornerBC_trunc (πz : ℕ → ℝ) (zb εz η : ℝ) (Fk : ℕ → ℕ → ℝ) (φ v : ℕ → ℝ) (d : ℕ) :
    ∀ j, hornerBC p n (trunc n πz) zb εz η Fk φ v d j = hornerBC p n πz zb εz η Fk φ v d j
  | 0 => rfl
  | j + 1 => by
    simp only [hornerBC, hornerBC_trunc πz zb εz η Fk φ v d j, GmulEC_trunc_left, GmulPC_trunc_left]

end Generic

section Runs

variable (uq : ℚ) (n : ℕ) (ρ : ℚ → ℚ)

/-- a run can be cut: `m_1 + m_2` steps are `m_1` steps and then `m_2` -/
theorem hornerRunLC_add (πz : ℕ → ℚ) (zb εz η : ℚ) (Fk : ℕ → ℕ → ℚ) (φ v : ℕ → ℚ) (d : ℕ) :
    ∀ (m1 m2 j0 : ℕ) (st : ℚ × List ℚ), hornerRunLC uq n ρ πz zb εz η Fk φ v d j0 (m1 + m2) st =
      hornerRunLC uq n ρ πz zb εz η Fk φ v d (j0 + m1) m2 (hornerRunLC uq n ρ πz zb εz η Fk φ v d j0 m1 st)
  | 0, m2, j0, st => by simp [hornerRunLC]
  | m1 + 1, m2, j0, st => by
    rw [show m1 + 1 + m2 = (m1 + m2) + 1 by omega]
    simp only [hornerRunLC]
    rw [hornerRunLC_add πz zb εz η Fk φ v d m1 m2 (j0 + 1), show j0 + 1 + m1 = j0 + (m1 + 1) by omega]

/-- the last step of a run from `j_0 = 0` -/
theorem hornerRunLC_succ (πz : ℕ → ℚ) (zb εz η : ℚ) (Fk : ℕ → ℕ → ℚ) (φ v : ℕ → ℚ) (d j : ℕ) (st : ℚ × List ℚ) :
    hornerRunLC uq n ρ πz zb εz η Fk φ v d 0 (j + 1) st =
      hornerStepLC uq n ρ πz zb εz η Fk φ v (d - (j + 1)) (hornerRunLC uq n ρ πz zb εz η Fk φ v d 0 j st) := by
  rw [hornerRunLC_add uq n ρ πz zb εz η Fk φ v d j 1 0 st]
  simp [hornerRunLC]

end Runs

section Bounds

variable (p : ℤ) (n : ℕ) {uq : ℚ} (h : (uq : ℝ) = u p) {ρ : ℚ → ℚ} (hρ : ∀ q, q ≤ ρ q)

include h in
/-- `G_MUL` on real bounds is at most its mirror on rational bounds above them -/
theorem GmulC_le_mirror (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {α β : ℕ → ℝ} {αq βq : ℕ → ℚ}
    (hα0 : ∀ i < n, 0 ≤ α i) (hβ0 : ∀ j < n, 0 ≤ β j) (hα : ∀ i < n, α i ≤ ((αq i : ℚ) : ℝ))
    (hβ : ∀ j < n, β j ≤ ((βq j : ℚ) : ℝ)) {Zb : ℝ} {Zq : ℚ} (hZ : Zb ≤ ((Zq : ℚ) : ℝ)) :
    GmulEC p n α β Zb ≤ ((GmulECQ uq n αq βq Zq : ℚ) : ℝ) ∧
      ∀ i, GmulPC p n α β Zb i ≤ ((GmulPCQ uq n αq βq Zq i : ℚ) : ℝ) := by
  have hm := GmulC_mono_lt p n hA3 hα0 hβ0 hα hβ hZ
  rw [cast_GmulEC p n h]
  exact ⟨hm.1, fun i => by rw [cast_GmulPC p n h]; exact hm.2 i⟩

include h in
/-- `G_ADD` on real bounds is at most its mirror on rational bounds above them -/
theorem GaddC_le_mirror (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {α β : ℕ → ℝ} {αq βq : ℕ → ℚ}
    (hα : ∀ i < n, α i ≤ ((αq i : ℚ) : ℝ)) (hβ : ∀ j < n, β j ≤ ((βq j : ℚ) : ℝ)) {Zb : ℝ} {Zq : ℚ}
    (hZ : Zb ≤ ((Zq : ℚ) : ℝ)) :
    GaddEC p n α β Zb ≤ ((GaddECQ uq n αq βq Zq : ℚ) : ℝ) ∧
      ∀ i, GaddPC p n α β Zb i ≤ ((GaddPCQ uq n αq βq Zq i : ℚ) : ℝ) := by
  have hm := GaddC_mono_lt p n hn hA3 hα hβ hZ
  rw [cast_GaddEC p n h]
  exact ⟨hm.1, fun i => by rw [cast_GaddPC p n h]; exact hm.2 i⟩

include h hρ in
/-- one step of Horner's bounds: from `(e_{k+1}, π^{(k+1)})` below their rounded mirrors to `(e_k, π^{(k)})` -/
theorem hornerC_step_le (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {πz : ℕ → ℝ} {πzq : ℕ → ℚ} (hπ0 : ∀ i, 0 ≤ πz i)
    (hπ : ∀ i, πz i ≤ ((πzq i : ℚ) : ℝ)) {zb : ℚ} (hzb : 0 ≤ zb) {εz : ℝ} {εzq : ℚ} (hε0 : 0 ≤ εz)
    (hε : εz ≤ ((εzq : ℚ) : ℝ)) (η : ℚ) (Fq : ℕ → ℚ) (φk vk : ℚ) {vk1 : ℚ} (hv1 : 0 ≤ vk1) {e1 : ℝ} {e1q : ℚ}
    (he0 : 0 ≤ e1) (he : e1 ≤ ((e1q : ℚ) : ℝ)) {π1 : ℕ → ℝ} {π1q : ℕ → ℚ} (hp0 : ∀ i, 0 ≤ π1 i)
    (hp1 : ∀ i, π1 i ≤ ((π1q i : ℚ) : ℝ)) :
    (1 + εz) * (zb : ℝ) * e1 + εz * (zb : ℝ) * (vk1 : ℝ) + (φk : ℝ) +
          (GmulEC p n πz π1 ((1 + εz) * (zb : ℝ) * ((vk1 : ℝ) + e1)) + (n : ℝ) * (η : ℝ)) +
        GaddEC p n (fun i => |((Fq i : ℚ) : ℝ)|)
          (fun i => GmulPC p n πz π1 ((1 + εz) * (zb : ℝ) * ((vk1 : ℝ) + e1)) i + (η : ℝ))
          ((vk : ℝ) + ((1 + εz) * (zb : ℝ) * e1 + εz * (zb : ℝ) * (vk1 : ℝ) + (φk : ℝ) +
            (GmulEC p n πz π1 ((1 + εz) * (zb : ℝ) * ((vk1 : ℝ) + e1)) + (n : ℝ) * (η : ℝ)))) ≤
        ((ρ ((1 + εzq) * zb * e1q + εzq * zb * vk1 + φk +
            (GmulECQ uq n πzq π1q ((1 + εzq) * zb * (vk1 + e1q)) + n * η) +
          GaddECQ uq n (fun i => |Fq i|) (fun i => GmulPCQ uq n πzq π1q ((1 + εzq) * zb * (vk1 + e1q)) i + η)
            (vk + ((1 + εzq) * zb * e1q + εzq * zb * vk1 + φk +
              (GmulECQ uq n πzq π1q ((1 + εzq) * zb * (vk1 + e1q)) + n * η)))) : ℚ) : ℝ) ∧
      ∀ i, GaddPC p n (fun i => |((Fq i : ℚ) : ℝ)|)
          (fun i => GmulPC p n πz π1 ((1 + εz) * (zb : ℝ) * ((vk1 : ℝ) + e1)) i + (η : ℝ))
          ((vk : ℝ) + ((1 + εz) * (zb : ℝ) * e1 + εz * (zb : ℝ) * (vk1 : ℝ) + (φk : ℝ) +
            (GmulEC p n πz π1 ((1 + εz) * (zb : ℝ) * ((vk1 : ℝ) + e1)) + (n : ℝ) * (η : ℝ)))) i ≤
        ((ρ (GaddPCQ uq n (fun i => |Fq i|)
            (fun i => GmulPCQ uq n πzq π1q ((1 + εzq) * zb * (vk1 + e1q)) i + η)
            (vk + ((1 + εzq) * zb * e1q + εzq * zb * vk1 + φk +
              (GmulECQ uq n πzq π1q ((1 + εzq) * zb * (vk1 + e1q)) + n * η))) i) : ℚ) : ℝ) := by
  have hzb' : (0 : ℝ) ≤ (zb : ℝ) := by exact_mod_cast hzb
  have hv1' : (0 : ℝ) ≤ (vk1 : ℝ) := by exact_mod_cast hv1
  have hεq : (0 : ℝ) ≤ (εzq : ℝ) := hε0.trans hε
  have heq : (0 : ℝ) ≤ (e1q : ℝ) := he0.trans he
  have hc : (1 + εz) * (zb : ℝ) ≤ (1 + (εzq : ℝ)) * (zb : ℝ) := mul_le_mul_of_nonneg_right (by linarith) hzb'
  have hc0 : 0 ≤ (1 + εz) * (zb : ℝ) := mul_nonneg (by linarith) hzb'
  have hZ : (1 + εz) * (zb : ℝ) * ((vk1 : ℝ) + e1) ≤ (((1 + εzq) * zb * (vk1 + e1q) : ℚ) : ℝ) := by
    push_cast
    exact mul_le_mul hc (by linarith) (add_nonneg hv1' he0) (hc0.trans hc)
  obtain ⟨m1, m2⟩ := GmulC_mono p n hA3 hπ0 hp0 hπ hp1 hZ
  have m1' : GmulEC p n πz π1 ((1 + εz) * (zb : ℝ) * ((vk1 : ℝ) + e1)) ≤
      ((GmulECQ uq n πzq π1q ((1 + εzq) * zb * (vk1 + e1q)) : ℚ) : ℝ) := by
    rw [cast_GmulEC p n h]
    exact m1
  have m2' : ∀ i, GmulPC p n πz π1 ((1 + εz) * (zb : ℝ) * ((vk1 : ℝ) + e1)) i + (η : ℝ) ≤
      ((GmulPCQ uq n πzq π1q ((1 + εzq) * zb * (vk1 + e1q)) i + η : ℚ) : ℝ) := fun i => by
    rw [Rat.cast_add, cast_GmulPC p n h]
    exact add_le_add (m2 i) le_rfl
  have hD : (1 + εz) * (zb : ℝ) * e1 + εz * (zb : ℝ) * (vk1 : ℝ) + (φk : ℝ) +
        (GmulEC p n πz π1 ((1 + εz) * (zb : ℝ) * ((vk1 : ℝ) + e1)) + (n : ℝ) * (η : ℝ)) ≤
      (((1 + εzq) * zb * e1q + εzq * zb * vk1 + φk +
        (GmulECQ uq n πzq π1q ((1 + εzq) * zb * (vk1 + e1q)) + n * η) : ℚ) : ℝ) := by
    have a1 : (1 + εz) * (zb : ℝ) * e1 ≤ (1 + (εzq : ℝ)) * (zb : ℝ) * (e1q : ℝ) := mul_le_mul hc he he0 (hc0.trans hc)
    have a2 : εz * (zb : ℝ) * (vk1 : ℝ) ≤ (εzq : ℝ) * (zb : ℝ) * (vk1 : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hε hzb') hv1'
    push_cast
    linarith
  have hvD : (vk : ℝ) + ((1 + εz) * (zb : ℝ) * e1 + εz * (zb : ℝ) * (vk1 : ℝ) + (φk : ℝ) +
        (GmulEC p n πz π1 ((1 + εz) * (zb : ℝ) * ((vk1 : ℝ) + e1)) + (n : ℝ) * (η : ℝ))) ≤
      ((vk + ((1 + εzq) * zb * e1q + εzq * zb * vk1 + φk +
        (GmulECQ uq n πzq π1q ((1 + εzq) * zb * (vk1 + e1q)) + n * η)) : ℚ) : ℝ) := by
    rw [Rat.cast_add]
    exact add_le_add le_rfl hD
  obtain ⟨g1, g2⟩ := GaddC_mono p n hA3 (α := fun i => |((Fq i : ℚ) : ℝ)|) (α' := fun i => ((|Fq i| : ℚ) : ℝ))
    (fun i => (Rat.cast_abs (Fq i)).ge) m2' hvD
  refine ⟨?_, fun i => ?_⟩
  · refine le_trans ?_ ((Rat.cast_le (K := ℝ)).mpr (hρ _))
    rw [Rat.cast_add, cast_GaddEC p n h]
    exact add_le_add hD g1
  · refine le_trans ?_ ((Rat.cast_le (K := ℝ)).mpr (hρ _))
    rw [cast_GaddPC p n h]
    exact g2 i

/-- Lemma 13's part bounds stop at `n` -/
theorem gPartsC_of_le (hn : 1 ≤ n) (X : ℕ → ℝ) (Zb Fb : ℝ) {i : ℕ} (hi : n ≤ i) : gPartsC p n X Zb Fb i = 0 := by
  cases i with
  | zero => omega
  | succ i =>
    have hi' : ¬i + 1 < n := by omega
    simp only [gPartsC, hi', ↓reduceIte]

include h hρ in
/-- Horner's bounds are at most their rounded mirrors, which may start from larger `π^z` and `ε_z` -/
theorem hornerRunLC_ge (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {πz : ℕ → ℝ} {πzq : ℕ → ℚ}
    (hπ0 : ∀ i, 0 ≤ πz i) (hπ : ∀ i, πz i ≤ ((πzq i : ℚ) : ℝ)) {zb : ℚ} (hzb : 0 ≤ zb) {εz : ℝ} {εzq : ℚ}
    (hε0 : 0 ≤ εz) (hε : εz ≤ ((εzq : ℚ) : ℝ)) {η : ℚ} (hη : 0 ≤ η) (Fk : ℕ → ℕ → ℚ)
    (hF0 : ∀ k i, n ≤ i → Fk k i = 0) {φ v : ℕ → ℚ} (hφ : ∀ k, 0 ≤ φ k) (hv : ∀ k, 0 ≤ v k) (d : ℕ) : ∀ j,
    (hornerBC p n πz (zb : ℝ) εz (η : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) (fun k => ((φ k : ℚ) : ℝ))
          (fun k => ((v k : ℚ) : ℝ)) d j).1 ≤
        (((hornerRunLC uq n ρ πzq zb εzq η Fk φ v d 0 j (hornerInitL n Fk φ d)).1 : ℚ) : ℝ) ∧
      ∀ i, (hornerBC p n πz (zb : ℝ) εz (η : ℝ) (fun k i => ((Fk k i : ℚ) : ℝ)) (fun k => ((φ k : ℚ) : ℝ))
          (fun k => ((v k : ℚ) : ℝ)) d j).2 i ≤
        ((((hornerRunLC uq n ρ πzq zb εzq η Fk φ v d 0 j (hornerInitL n Fk φ d)).2.getD i 0 : ℚ)) : ℝ)
  | 0 => by
    refine ⟨le_rfl, fun i => ?_⟩
    simp only [hornerBC, hornerRunLC, hornerInitL]
    rw [getD_map_range]
    split_ifs with hi
    · exact (Rat.cast_abs (Fk d i)).ge
    · rw [hF0 d i (by omega)]
      simp
  | j + 1 => by
    obtain ⟨i1, i2⟩ := hornerRunLC_ge hn hA3 hπ0 hπ hzb hε0 hε hη Fk hF0 hφ hv d j
    have hzb' : (0 : ℝ) ≤ (zb : ℝ) := by exact_mod_cast hzb
    have hη' : (0 : ℝ) ≤ (η : ℝ) := by exact_mod_cast hη
    obtain ⟨n1, n2⟩ := hornerBC_nonneg p n hA3 hπ0 hzb' hε0 hη' (fun k i => ((Fk k i : ℚ) : ℝ))
      (φ := fun k => ((φ k : ℚ) : ℝ)) (v := fun k => ((v k : ℚ) : ℝ)) (fun k => by exact_mod_cast hφ k)
      (fun k => by exact_mod_cast hv k) d j
    obtain ⟨s1, s2⟩ := hornerC_step_le p n h hρ hA3 hπ0 hπ hzb hε0 hε η (Fk (d - (j + 1))) (φ (d - (j + 1)))
      (v (d - (j + 1))) (hv (d - (j + 1) + 1)) n1 i1 n2 i2
    rw [hornerRunLC_succ]
    refine ⟨s1, fun i => ?_⟩
    simp only [hornerStepLC]
    rw [getD_map_range]
    split_ifs with hi
    · exact s2 i
    · rw [Rat.cast_zero]
      exact (gPartsC_of_le p n hn _ _ _ (by omega)).le

include h hρ in
/-- step (3) for `d' ≠ 1`: from a state above Horner's `(e_2, π^q_2)`, the three steps give a state above
`(E_0, ψ_0)` -/
theorem core0C_le (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {π' : ℕ → ℝ} {πq : ℕ → ℚ}
    (hπ0 : ∀ i, 0 ≤ π' i) (hπ : ∀ i < n, π' i ≤ ((πq i : ℚ) : ℝ)) {b' : ℝ} {bp : ℚ} (hb0 : 0 ≤ b')
    (hb : b' ≤ ((bp : ℚ) : ℝ)) (hbp : bp < 1) {T0 D η : ℝ} {T0q Dq ηq : ℚ} (hT : T0 ≤ ((T0q : ℚ) : ℝ))
    (hD : D ≤ ((Dq : ℚ) : ℝ)) (hη : η ≤ ((ηq : ℚ) : ℝ)) (Fk : ℕ → ℕ → ℝ) (φ : ℕ → ℝ) (hφ : ∀ k, 0 ≤ φ k)
    (d : ℕ) (hd : d ≠ 1) (st : ℚ × List ℚ)
    (hst : Dom n (hornerBC p n π' b' 0 0 Fk φ (coreV b' d) d (d - 2)).1
      (hornerBC p n π' b' 0 0 Fk φ (coreV b' d) d (d - 2)).2 st) :
    Dom n (core0C p n T0 D η π' b' Fk φ d).1 (core0C p n T0 D η π' b' Fk φ d).2
      (expTLC uq n ρ πq T0q ηq (expYLC uq n ρ πq bp Dq d (expWLC uq n ρ πq bp st))) := by
  have hbp' : ((bp : ℚ) : ℝ) < 1 := by exact_mod_cast hbp
  have hbp0 : (0 : ℝ) ≤ ((bp : ℚ) : ℝ) := hb0.trans hb
  have hvk : ∀ k, 0 ≤ coreV b' d k := fun k =>
    (coreV_le hb0 hb d k (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])).1
  obtain ⟨hv0, hv⟩ := coreV_le hb0 hb d 2 (by norm_num; linarith)
  rw [← cast_coreVQ] at hv
  obtain ⟨hH0, hH20⟩ := hornerBC_nonneg p n hA3 hπ0 hb0 le_rfl le_rfl Fk hφ hvk d (d - 2)
  obtain ⟨H, hHd⟩ : ∃ H, H = hornerBC p n π' b' 0 0 Fk φ (coreV b' d) d (d - 2) := ⟨_, rfl⟩
  rw [← hHd] at hst hH0 hH20
  obtain ⟨s1, s2⟩ := hst
  -- `w = MUL(r', q)`
  obtain ⟨Zw, hZw⟩ : ∃ Zw, Zw = b' * (coreV b' d 2 + H.1) := ⟨_, rfl⟩
  obtain ⟨Zwq, hZwq⟩ : ∃ Zwq, Zwq = bp * (coreVQ bp 2 + st.1) := ⟨_, rfl⟩
  have hZw0 : 0 ≤ Zw := by rw [hZw]; exact mul_nonneg hb0 (add_nonneg hv0 hH0)
  have hZwle : Zw ≤ ((Zwq : ℚ) : ℝ) := by
    rw [hZw, hZwq]
    push_cast
    exact mul_le_mul hb (add_le_add hv s1) (add_nonneg hv0 hH0) hbp0
  obtain ⟨w1, w2⟩ := GmulC_le_mirror p n h hA3 (fun i _ => hπ0 i) (fun i _ => hH20 i) hπ s2 hZwle
  obtain ⟨hε10, hω10⟩ := GmulC_nonneg p n hA3 hπ0 hH20 hZw0
  obtain ⟨ε1, hε1⟩ : ∃ ε1, ε1 = GmulEC p n π' H.2 Zw := ⟨_, rfl⟩
  obtain ⟨ω1, hω1⟩ : ∃ ω1, ω1 = GmulPC p n π' H.2 Zw := ⟨_, rfl⟩
  rw [← hε1] at w1 hε10
  rw [← hω1] at w2 hω10
  obtain ⟨sW, hsW⟩ : ∃ sW, sW = expWLC uq n ρ πq bp st := ⟨_, rfl⟩
  rw [← hsW]
  have hW11 : Zw + ε1 ≤ ((sW.1.1 : ℚ) : ℝ) := by
    rw [hsW]
    simp only [expWLC]
    rw [← hZwq]
    refine le_trans ?_ (Rat.cast_le.mpr (hρ _))
    push_cast
    linarith
  have hW12 : ε1 + b' * H.1 ≤ ((sW.1.2 : ℚ) : ℝ) := by
    rw [hsW]
    simp only [expWLC]
    rw [← hZwq]
    refine le_trans ?_ (Rat.cast_le.mpr (hρ _))
    push_cast
    linarith [mul_le_mul hb s1 hH0 hbp0]
  have hW2 : ∀ i < n, ω1 i ≤ ((sW.2.getD i 0 : ℚ) : ℝ) := fun i hi => by
    rw [hsW]
    simp only [expWLC]
    rw [getD_range_map _ hi, ← hZwq]
    exact (w2 i).trans (Rat.cast_le.mpr (hρ _))
  -- the second product
  obtain ⟨Zy, hZy⟩ : ∃ Zy, Zy = b' * (Zw + ε1) := ⟨_, rfl⟩
  have hZy0 : 0 ≤ Zy := by rw [hZy]; exact mul_nonneg hb0 (add_nonneg hZw0 hε10)
  have hZyle : Zy ≤ ((bp * sW.1.1 : ℚ) : ℝ) := by
    rw [hZy]
    push_cast
    exact mul_le_mul hb hW11 (add_nonneg hZw0 hε10) hbp0
  obtain ⟨y1, y2⟩ := GmulC_le_mirror p n h hA3 (fun i _ => hπ0 i) (fun i _ => hω10 i) hπ hW2 hZyle
  obtain ⟨hε20, hω0⟩ := GmulC_nonneg p n hA3 hπ0 hω10 hZy0
  obtain ⟨ε2, hε2⟩ : ∃ ε2, ε2 = GmulEC p n π' ω1 Zy := ⟨_, rfl⟩
  obtain ⟨ω, hω⟩ : ∃ ω, ω = GmulPC p n π' ω1 Zy := ⟨_, rfl⟩
  rw [← hε2] at y1 hε20
  rw [← hω] at y2 hω0
  obtain ⟨Em, hEm⟩ : ∃ Em, Em = ε2 + b' * (ε1 + b' * H.1) + eTr b' d + D := ⟨_, rfl⟩
  obtain ⟨sY, hsY⟩ : ∃ sY, sY = expYLC uq n ρ πq bp Dq d sW := ⟨_, rfl⟩
  rw [← hsY]
  have hbd : ((bp : ℚ) : ℝ) < d + 2 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hY1 : Em ≤ ((sY.1 : ℚ) : ℝ) := by
    rw [hsY]
    simp only [expYLC]
    refine le_trans ?_ (Rat.cast_le.mpr (hρ _))
    push_cast
    rw [hEm]
    have a1 := mul_le_mul hb hW12 (add_nonneg hε10 (mul_nonneg hb0 hH0)) hbp0
    linarith [eTr_le hb0 hb d hbd]
  have hY2 : ∀ i < n, ω i ≤ ((sY.2.getD i 0 : ℚ) : ℝ) := fun i hi => by
    rw [hsY]
    simp only [expYLC]
    rw [getD_range_map _ hi]
    exact (y2 i).trans (Rat.cast_le.mpr (hρ _))
  -- the sum and its scaling back
  have hZt : T0 + Em ≤ ((T0q + sY.1 : ℚ) : ℝ) := by push_cast; linarith
  obtain ⟨t1, t2⟩ := GaddC_le_mirror p n h hn hA3 hπ hY2 hZt
  have hcore : core0C p n T0 D η π' b' Fk φ d =
      (Em + GaddEC p n π' ω (T0 + Em) + n * η, fun i => GaddPC p n π' ω (T0 + Em) i + η) := by
    simp only [core0C, hd, ↓reduceIte]
    rw [hEm, hε2, hω, hZy, hε1, hω1, hZw, hHd]
  rw [hcore]
  refine ⟨?_, fun i hi => ?_⟩
  · show Em + GaddEC p n π' ω (T0 + Em) + n * η ≤ _
    simp only [expTLC]
    refine le_trans ?_ (Rat.cast_le.mpr (hρ _))
    push_cast
    linarith [mul_le_mul_of_nonneg_left hη (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · show GaddPC p n π' ω (T0 + Em) i + η ≤ _
    simp only [expTLC]
    rw [getD_range_map _ hi]
    refine le_trans ?_ (Rat.cast_le.mpr (hρ _))
    push_cast
    linarith [t2 i]

include h hρ in
/-- one squaring: a state above `(E, ψ)` gives one above `sqBC`'s -/
theorem sqBC_le (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {T T' g E : ℝ} {ψ : ℕ → ℝ} {Tq T'q gq : ℚ}
    (hT0 : 0 ≤ T) (hT : T ≤ ((Tq : ℚ) : ℝ)) (hT' : T' ≤ ((T'q : ℚ) : ℝ)) (hg0 : 0 ≤ g) (hg : g ≤ ((gq : ℚ) : ℝ))
    (hE0 : 0 ≤ E) (hψ0 : ∀ i, 0 ≤ ψ i) (st : ℚ × List ℚ) (hst : Dom n E ψ st) :
    Dom n (sqBC p n T T' g E ψ).1 (sqBC p n T T' g E ψ).2 (expSqLC uq n ρ Tq T'q gq st) := by
  obtain ⟨s1, s2⟩ := hst
  have hEq0 : (0 : ℝ) ≤ ((st.1 : ℚ) : ℝ) := hE0.trans s1
  have hZm : (T + E) ^ 2 ≤ (((Tq + st.1) ^ 2 : ℚ) : ℝ) := by
    push_cast
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  obtain ⟨m1, m2⟩ := GmulC_le_mirror p n h hA3 (fun i _ => hψ0 i) (fun i _ => hψ0 i) s2 s2 hZm
  obtain ⟨hεm0, -⟩ := GmulC_nonneg p n hA3 hψ0 hψ0 (Zb := (T + E) ^ 2) (by positivity)
  obtain ⟨εm, hεm⟩ : ∃ εm, εm = GmulEC p n ψ ψ ((T + E) ^ 2) := ⟨_, rfl⟩
  rw [← hεm] at m1 hεm0
  have hE2 : E ^ 2 ≤ ((st.1 : ℚ) : ℝ) ^ 2 := pow_le_pow_left₀ hE0 s1 2
  have hET : 2 * E * (1 + T) ≤ 2 * ((st.1 : ℚ) : ℝ) * (1 + ((Tq : ℚ) : ℝ)) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hZs : T' + 2 * E * (1 + T) + E ^ 2 + εm ≤ ((T'q + 2 * st.1 * (1 + Tq) + st.1 ^ 2 +
      GmulECQ uq n (fun i => st.2.getD i 0) (fun i => st.2.getD i 0) ((Tq + st.1) ^ 2) : ℚ) : ℝ) := by
    push_cast
    linarith
  obtain ⟨a1, a2⟩ := GaddC_le_mirror p n h hn hA3 (α := fun i => 2 * ψ i)
    (αq := fun i => 2 * st.2.getD i 0) (fun i hi => by push_cast; linarith [s2 i hi]) (fun j _ => m2 j) hZs
  have hgE : 2 * g * E ≤ 2 * ((gq : ℚ) : ℝ) * ((st.1 : ℚ) : ℝ) :=
    mul_le_mul (by linarith) s1 hE0 (by linarith)
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [sqBC, expSqLC]
    rw [← hεm]
    refine le_trans ?_ (Rat.cast_le.mpr (hρ _))
    push_cast
    linarith
  · simp only [sqBC, expSqLC]
    rw [getD_range_map _ hi, ← hεm]
    exact (a2 i).trans (Rat.cast_le.mpr (hρ _))

include h hρ in
/-- step (3) from Horner's run: the three steps on the last state of `hornerRunLC`, with `π^z` a list and `v_k`
replaced by its bound, give a state above `(E_0, ψ_0)` -/
theorem core0C_cert (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {π' : ℕ → ℝ} (pq : List ℚ)
    (hπ0 : ∀ i, 0 ≤ π' i) (hπ : ∀ i < n, π' i ≤ ((pq.getD i 0 : ℚ) : ℝ)) (hpq0 : ∀ i, 0 ≤ pq.getD i 0)
    {b' : ℝ} {bp : ℚ} (hb0 : 0 ≤ b') (hb : b' ≤ ((bp : ℚ) : ℝ)) (hbp : bp < 1) {T0 D η : ℝ} {T0q Dq ηq : ℚ}
    (hT : T0 ≤ ((T0q : ℚ) : ℝ)) (hD : D ≤ ((Dq : ℚ) : ℝ)) (hη : η ≤ ((ηq : ℚ) : ℝ)) (Fk : ℕ → ℕ → ℚ)
    (hF0 : ∀ k i, n ≤ i → Fk k i = 0) (φ : ℕ → ℚ) (hφ : ∀ k, 0 ≤ φ k) (d : ℕ) (hd : d ≠ 1) :
    Dom n (core0C p n T0 D η π' b' (fun k i => ((Fk k i : ℚ) : ℝ)) (fun k => ((φ k : ℚ) : ℝ)) d).1
      (core0C p n T0 D η π' b' (fun k i => ((Fk k i : ℚ) : ℝ)) (fun k => ((φ k : ℚ) : ℝ)) d).2
      (expTLC uq n ρ (fun i => pq.getD i 0) T0q ηq (expYLC uq n ρ (fun i => pq.getD i 0) bp Dq d
        (expWLC uq n ρ (fun i => pq.getD i 0) bp
          (hornerRunLC uq n ρ (fun i => pq.getD i 0) bp 0 0 Fk φ (coreVQ bp) d 0 (d - 2)
            (hornerInitL n Fk φ d))))) := by
  have hbp' : ((bp : ℚ) : ℝ) < 1 := by exact_mod_cast hbp
  have hbp0 : (0 : ℝ) ≤ ((bp : ℚ) : ℝ) := hb0.trans hb
  have hbpq0 : (0 : ℚ) ≤ bp := by exact_mod_cast hbp0
  have hφ' : ∀ k, (0 : ℝ) ≤ ((φ k : ℚ) : ℝ) := fun k => by exact_mod_cast hφ k
  have hvk : ∀ k, 0 ≤ coreV b' d k ∧ coreV b' d k ≤ ((coreVQ bp k : ℚ) : ℝ) := fun k => by
    rw [cast_coreVQ]
    exact coreV_le hb0 hb d k (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hvq0 : ∀ k, (0 : ℚ) ≤ coreVQ bp k := fun k => by
    have := (hvk k).1.trans (hvk k).2
    exact_mod_cast this
  refine core0C_le p n h hρ hn hA3 hπ0 hπ hb0 hb hbp hT hD hη _ _ hφ' d hd _ ?_
  -- Horner's bounds: below `n`, then at the rational `z̄` and `v`, then their rounded mirrors
  have ht := hornerBC_trunc p n π' b' 0 0 (fun k i => ((Fk k i : ℚ) : ℝ)) (fun k => ((φ k : ℚ) : ℝ)) (coreV b' d) d
    (d - 2)
  have hm := hornerBC_mono2 p n hA3 (πz := trunc n π') (πz' := fun i => ((pq.getD i 0 : ℚ) : ℝ))
    (trunc_nonneg n fun i _ => hπ0 i) (fun i => by
      unfold trunc
      split_ifs with hi
      · exact hπ i hi
      · exact_mod_cast hpq0 i) hb0 hb (le_refl (0 : ℝ)) (le_refl (0 : ℝ)) (le_refl (0 : ℝ))
    (fun k i => ((Fk k i : ℚ) : ℝ)) hφ' (fun k => (hvk k).1) (fun k => (hvk k).2) d (d - 2)
  have hr := hornerRunLC_ge p n h hρ hn hA3 (πz := fun i => ((pq.getD i 0 : ℚ) : ℝ))
    (πzq := fun i => pq.getD i 0) (fun i => by exact_mod_cast hpq0 i) (fun i => le_rfl) hbpq0 (εz := 0)
    (εzq := 0) le_rfl (by simp) (η := 0) le_rfl Fk hF0 hφ hvq0 d (d - 2)
  simp only [Rat.cast_zero] at hr
  rw [ht] at hm
  exact ⟨hm.1.trans hr.1, fun i _ => (hm.2 i).trans (hr.2 i)⟩

include h hρ in
/-- the squarings: from a state above `(E_0, ψ_0)`, states that follow each other by `expSqLC` stay above `coreEC`'s -/
theorem coreEC_cert (hn : 1 ≤ n) (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {T g : ℕ → ℝ} {E0 : ℝ} {ψ0 : ℕ → ℝ}
    (Tq gq : ℕ → ℚ) (m : ℕ) (hT0 : ∀ j, 0 ≤ T j) (hT : ∀ j ≤ m, T j ≤ ((Tq j : ℚ) : ℝ)) (hg0 : ∀ j, 0 ≤ g j)
    (hg : ∀ j < m, g j ≤ ((gq j : ℚ) : ℝ)) (hE0 : 0 ≤ E0) (hψ0 : ∀ i, 0 ≤ ψ0 i) (sts : ℕ → ℚ × List ℚ)
    (h0 : Dom n E0 ψ0 (sts 0))
    (hstep : ∀ j < m, expSqLC uq n ρ (Tq j) (Tq (j + 1)) (gq j) (sts j) = sts (j + 1)) :
    ∀ j ≤ m, Dom n (coreEC p n T g E0 ψ0 j).1 (coreEC p n T g E0 ψ0 j).2 (sts j) ∧
      0 ≤ (coreEC p n T g E0 ψ0 j).1 ∧ ∀ i, 0 ≤ (coreEC p n T g E0 ψ0 j).2 i
  | 0, _ => ⟨h0, hE0, hψ0⟩
  | j + 1, hj => by
    obtain ⟨i1, i2, i3⟩ := coreEC_cert hn hA3 Tq gq m hT0 hT hg0 hg hE0 hψ0 sts h0 hstep j (by omega)
    obtain ⟨E, hE⟩ : ∃ E, E = (coreEC p n T g E0 ψ0 j).1 := ⟨_, rfl⟩
    obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = (coreEC p n T g E0 ψ0 j).2 := ⟨_, rfl⟩
    rw [← hE, ← hψ] at i1
    rw [← hE] at i2
    rw [← hψ] at i3
    have hs := sqBC_le p n h hρ hn hA3 (hT0 j) (hT j (by omega)) (hT (j + 1) hj) (hg0 j) (hg j (by omega)) i2 i3
      (sts j) i1
    rw [hstep j (by omega)] at hs
    have hce : coreEC p n T g E0 ψ0 (j + 1) = sqBC p n (T j) (T (j + 1)) (g j) E ψ := by
      rw [hE, hψ]
      rfl
    rw [hce]
    refine ⟨hs, ?_, ?_⟩
    · obtain ⟨hεm0, hν0⟩ := GmulC_nonneg p n hA3 i3 i3 (Zb := (T j + E) ^ 2) (by positivity)
      have hZs : 0 ≤ T (j + 1) + 2 * E * (1 + T j) + E ^ 2 + GmulEC p n ψ ψ ((T j + E) ^ 2) := by
        have := hT0 j
        have := hT0 (j + 1)
        positivity
      obtain ⟨hεa0, -⟩ := GaddC_nonneg p n hA3 (α := fun i => 2 * ψ i) (fun i => by linarith [i3 i]) hν0 hZs
      simp only [sqBC]
      have := hg0 j
      positivity
    · obtain ⟨hεm0, hν0⟩ := GmulC_nonneg p n hA3 i3 i3 (Zb := (T j + E) ^ 2) (by positivity)
      have hZs : 0 ≤ T (j + 1) + 2 * E * (1 + T j) + E ^ 2 + GmulEC p n ψ ψ ((T j + E) ^ 2) := by
        have := hT0 j
        have := hT0 (j + 1)
        positivity
      obtain ⟨-, hπa0⟩ := GaddC_nonneg p n hA3 (α := fun i => 2 * ψ i) (fun i => by linarith [i3 i]) hν0 hZs
      simp only [sqBC]
      exact hπa0

/-- `(E_0, ψ_0)` is nonnegative -/
theorem core0C_nonneg (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {π' : ℕ → ℝ} (hπ0 : ∀ i, 0 ≤ π' i) {b' T0 D η : ℝ}
    (hb0 : 0 ≤ b') (hb1 : b' < 1) (hT0 : 0 ≤ T0) (hD0 : 0 ≤ D) (hη0 : 0 ≤ η) (Fk : ℕ → ℕ → ℝ) (φ : ℕ → ℝ)
    (hφ : ∀ k, 0 ≤ φ k) (d : ℕ) :
    0 ≤ (core0C p n T0 D η π' b' Fk φ d).1 ∧ ∀ i, 0 ≤ (core0C p n T0 D η π' b' Fk φ d).2 i := by
  have htr : ∀ d : ℕ, 0 ≤ eTr b' d := fun d => by
    unfold eTr
    have hd2 : (0 : ℝ) < d + 2 := by positivity
    have h1 : 0 < 1 - b' / (d + 2) := by
      rw [sub_pos, div_lt_one hd2]
      linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    positivity
  by_cases hd : d = 1
  · subst hd
    simp only [core0C, ↓reduceIte]
    exact ⟨add_nonneg (htr 1) hD0, hπ0⟩
  · have hvk : ∀ k, 0 ≤ coreV b' d k := fun k =>
      (coreV_le hb0 le_rfl d k (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])).1
    obtain ⟨hH0, hH20⟩ := hornerBC_nonneg p n hA3 hπ0 hb0 le_rfl le_rfl Fk hφ hvk d (d - 2)
    obtain ⟨H, hHd⟩ : ∃ H, H = hornerBC p n π' b' 0 0 Fk φ (coreV b' d) d (d - 2) := ⟨_, rfl⟩
    rw [← hHd] at hH0 hH20
    have hZw0 : 0 ≤ b' * (coreV b' d 2 + H.1) := mul_nonneg hb0 (add_nonneg (hvk 2) hH0)
    obtain ⟨hε10, hω10⟩ := GmulC_nonneg p n hA3 hπ0 hH20 hZw0
    have hZy0 : 0 ≤ b' * (b' * (coreV b' d 2 + H.1) + GmulEC p n π' H.2 (b' * (coreV b' d 2 + H.1))) :=
      mul_nonneg hb0 (add_nonneg hZw0 hε10)
    obtain ⟨hε20, hω0⟩ := GmulC_nonneg p n hA3 hπ0 hω10 hZy0
    obtain ⟨Em, hEm⟩ : ∃ Em, Em = GmulEC p n π' (GmulPC p n π' H.2 (b' * (coreV b' d 2 + H.1)))
        (b' * (b' * (coreV b' d 2 + H.1) + GmulEC p n π' H.2 (b' * (coreV b' d 2 + H.1)))) +
        b' * (GmulEC p n π' H.2 (b' * (coreV b' d 2 + H.1)) + b' * H.1) + eTr b' d + D := ⟨_, rfl⟩
    have hEm0 : 0 ≤ Em := by
      rw [hEm]
      have := htr d
      have := mul_nonneg hb0 (add_nonneg hε10 (mul_nonneg hb0 hH0))
      linarith
    obtain ⟨ha0, hpa0⟩ := GaddC_nonneg p n hA3 hπ0 hω0 (Zb := T0 + Em) (by linarith)
    have hcore : core0C p n T0 D η π' b' Fk φ d = (Em + GaddEC p n π'
        (GmulPC p n π' (GmulPC p n π' H.2 (b' * (coreV b' d 2 + H.1)))
          (b' * (b' * (coreV b' d 2 + H.1) + GmulEC p n π' H.2 (b' * (coreV b' d 2 + H.1))))) (T0 + Em) + n * η,
        fun i => GaddPC p n π' (GmulPC p n π' (GmulPC p n π' H.2 (b' * (coreV b' d 2 + H.1)))
          (b' * (b' * (coreV b' d 2 + H.1) + GmulEC p n π' H.2 (b' * (coreV b' d 2 + H.1))))) (T0 + Em) i + η) := by
      simp only [core0C, hd, ↓reduceIte]
      rw [hEm, hHd]
    rw [hcore]
    refine ⟨?_, fun i => add_nonneg (hpa0 i) hη0⟩
    have := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hη0
    show 0 ≤ Em + GaddEC p n π' _ (T0 + Em) + n * η
    linarith

end Bounds

end ExpansionBounds
