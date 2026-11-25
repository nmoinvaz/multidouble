import ExpansionBounds.AccK
import ExpansionBounds.SinCos

/-!
# Lemma 13's bounds grow with their arguments

`G_MUL` and `G_ADD` grow with the part bounds of their operands and with `Z̄`: the products `P_m`, the `A_m`, the level
bounds `X_m`, `R`, `Δ`, and then the error bound and the part bounds of Lemma 13. So a bound computed from larger
arguments is still a bound, and a script, or the kernel, may round the values it carries up. The paper's scripts rely
on this where they round up to 200 bits (`up` of `sqrt_consts.py`). Horner's bounds `(e_k, π^{(k)})` of Lemma 33 grow
in the same way with `π^z` and `ε_z`.
-/

namespace ExpansionBounds

open Finset

variable (p : ℤ) (n : ℕ)

/-! ### Lemma 13's bounds from the level bounds -/

theorem gErr_mono' {X X' : ℕ → ℝ} (hX : ∀ m, X m ≤ X' m) {Zb Zb' : ℝ} (hZ : Zb ≤ Zb') {Fb Fb' : ℝ} (hF : Fb ≤ Fb') :
    gErr p n X Zb Fb ≤ gErr p n X' Zb' Fb' := by
  have hu := u_pos p
  refine (gErr_mono p n hX hZ Fb).trans ?_
  have h : (1 + u p ^ n) * Fb ≤ (1 + u p ^ n) * Fb' := mul_le_mul_of_nonneg_left hF (by positivity)
  simp only [gErr]
  linarith

theorem gParts_mono' {X X' : ℕ → ℝ} (hX : ∀ m, X m ≤ X' m) {Zb Zb' : ℝ} (hZ : Zb ≤ Zb') {Fb Fb' : ℝ}
    (hF : Fb ≤ Fb') : ∀ i, gParts p n X Zb Fb i ≤ gParts p n X' Zb' Fb' i
  | 0 => by
    simp only [gParts]
    exact mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add hZ hF) (sum_le_sum fun j _ => Vb_mono p n hX j)) (by linarith [u_pos p])
  | i + 1 => by
    simp only [gParts]
    split_ifs
    · exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (gParts_mono' hX hZ hF i) (u_pos p).le)
          (sum_le_sum fun j _ => Vb_mono p n hX j)) (by linarith [u_pos p])
    · exact le_rfl

/-! ### `G_MUL` -/

theorem mulP_mono {α α' β β' : ℕ → ℝ} (hα0 : ∀ i, 0 ≤ α i) (hβ0 : ∀ j, 0 ≤ β j) (hα : ∀ i, α i ≤ α' i)
    (hβ : ∀ j, β j ≤ β' j) (m : ℕ) : mulP n α β m ≤ mulP n α' β' m := by
  unfold mulP
  refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
  split_ifs
  · exact mul_le_mul (hα i) (hβ j) (hβ0 j) ((hα0 i).trans (hα i))
  · exact le_rfl

theorem mulDelta_mono {α α' β β' : ℕ → ℝ} (hα0 : ∀ i, 0 ≤ α i) (hβ0 : ∀ j, 0 ≤ β j) (hα : ∀ i, α i ≤ α' i)
    (hβ : ∀ j, β j ≤ β' j) : mulDelta n α β ≤ mulDelta n α' β' := by
  unfold mulDelta
  refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
  split_ifs
  · exact mul_le_mul (hα i) (hβ j) (hβ0 j) ((hα0 i).trans (hα i))
  · exact le_rfl

theorem mulA_mono {α α' β β' : ℕ → ℝ} (hα0 : ∀ i, 0 ≤ α i) (hβ0 : ∀ j, 0 ≤ β j) (hα : ∀ i, α i ≤ α' i)
    (hβ : ∀ j, β j ≤ β' j) (m : ℕ) : mulA p n α β m ≤ mulA p n α' β' m := by
  have hu := u_pos p
  have h1 : 0 ≤ 1 + u p := by linarith
  have hP := mulP_mono n hα0 hβ0 hα hβ
  simp only [mulA]
  split_ifs
  · exact add_le_add (mul_le_mul_of_nonneg_left (hP m) h1) le_rfl
  · exact add_le_add (mul_le_mul_of_nonneg_left (hP m) h1) (mul_le_mul_of_nonneg_left (hP _) hu.le)
  · exact add_le_add (hP n) (mul_le_mul_of_nonneg_left (hP _) hu.le)
  · exact le_rfl

/-- (A3) keeps MUL's `T_m u` below one -/
theorem mulT_u_lt (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) : ∀ k < n, (mulT k : ℝ) * u p < 1 := fun k hk => by
  have hu := u_pos p
  have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
  have : (mulT k : ℝ) ≤ (n : ℝ) ^ 2 + n := by
    simp only [mulT]
    push_cast
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  nlinarith

/-- (A3) keeps MUL's `Q u` below one -/
theorem mulQ_u_lt (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) : ((n ^ 2 + n - 1 : ℕ) : ℝ) * u p < 1 := by
  have hu := u_pos p
  have : ((n ^ 2 + n - 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 + n := by exact_mod_cast Nat.sub_le (n ^ 2 + n) 1
  nlinarith

theorem mulX_mono (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {α α' β β' : ℕ → ℝ} (hα0 : ∀ i, 0 ≤ α i)
    (hβ0 : ∀ j, 0 ≤ β j) (hα : ∀ i, α i ≤ α' i) (hβ : ∀ j, β j ≤ β' j) (m : ℕ) :
    mulX p n α β m ≤ mulX p n α' β' m := by
  have hT := mulT_u_lt p n hA3
  have hQ := mulQ_u_lt p n hA3
  have hD := levD_mono (T := mulT) (u_pos p).le (mulA_mono p n hα0 hβ0 hα hβ) n hT
  simp only [mulX, levX]
  split_ifs with hm
  · exact div_le_div_of_nonneg_right (hD m hm.le) (by linarith [hT m hm])
  · exact div_le_div_of_nonneg_right (hD n le_rfl) (by linarith)

theorem mulR_mono (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {α α' β β' : ℕ → ℝ} (hα0 : ∀ i, 0 ≤ α i)
    (hβ0 : ∀ j, 0 ≤ β j) (hα : ∀ i, α i ≤ α' i) (hβ : ∀ j, β j ≤ β' j) : mulR p n α β ≤ mulR p n α' β' :=
  mul_le_mul_of_nonneg_left (mulX_mono p n hA3 hα0 hβ0 hα hβ n) (mul_nonneg (Nat.cast_nonneg _) (u_pos p).le)

/-- `G_MUL` grows with its operands' part bounds and with `Z̄` -/
theorem Gmul_mono (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {α α' β β' : ℕ → ℝ} (hα0 : ∀ i, 0 ≤ α i)
    (hβ0 : ∀ j, 0 ≤ β j) (hα : ∀ i, α i ≤ α' i) (hβ : ∀ j, β j ≤ β' j) {Zb Zb' : ℝ} (hZ : Zb ≤ Zb') :
    GmulE p n α β Zb ≤ GmulE p n α' β' Zb' ∧ ∀ i, GmulP p n α β Zb i ≤ GmulP p n α' β' Zb' i := by
  have hX := mulX_mono p n hA3 hα0 hβ0 hα hβ
  have hF : mulR p n α β + mulDelta n α β ≤ mulR p n α' β' + mulDelta n α' β' :=
    add_le_add (mulR_mono p n hA3 hα0 hβ0 hα hβ) (mulDelta_mono n hα0 hβ0 hα hβ)
  exact ⟨gErr_mono' p n hX hZ hF, gParts_mono' p n hX hZ hF⟩

/-! ### `G_ADD` -/

theorem pairA_mono {lam lam' : ℕ → ℝ} (hl : ∀ m, lam m ≤ lam' m) (m : ℕ) : pairA p n lam m ≤ pairA p n lam' m := by
  have hu := u_pos p
  have h1 : 0 ≤ 1 + u p := by linarith
  simp only [pairA]
  split_ifs
  · exact add_le_add (mul_le_mul_of_nonneg_left (hl m) h1) le_rfl
  · exact add_le_add (mul_le_mul_of_nonneg_left (hl m) h1) (mul_le_mul_of_nonneg_left (hl _) hu.le)
  · exact mul_le_mul_of_nonneg_left (hl _) hu.le
  · exact le_rfl

/-- (A3) keeps ADD's `T_m u` below one -/
theorem pairT_u_lt (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) : ∀ k < n, ((id k : ℕ) : ℝ) * u p < 1 := fun k hk => by
  have hu := u_pos p
  have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk.le
  have : (k : ℝ) ≤ (n : ℝ) ^ 2 + n := by nlinarith
  simp only [id]
  nlinarith

/-- (A3) keeps ADD's `Q u` below one -/
theorem pairQ_u_lt (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) : ((n - 1 : ℕ) : ℝ) * u p < 1 := by
  have hu := u_pos p
  have h1 : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
  have : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 + n := by nlinarith
  nlinarith

theorem pairX_mono (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {lam lam' : ℕ → ℝ} (hl : ∀ m, lam m ≤ lam' m) (m : ℕ) :
    pairX p n lam m ≤ pairX p n lam' m := by
  have hT := pairT_u_lt p n hA3
  have hQ := pairQ_u_lt p n hA3
  have hD := levD_mono (T := id) (u_pos p).le (pairA_mono p n hl) n hT
  simp only [pairX, levX]
  split_ifs with hm
  · exact div_le_div_of_nonneg_right (hD m hm.le) (by linarith [hT m hm])
  · exact div_le_div_of_nonneg_right (hD n le_rfl) (by linarith)

/-- `G_ADD` grows with its operands' part bounds and with `Z̄` -/
theorem Gadd_mono (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {α α' β β' : ℕ → ℝ} (hα : ∀ i, α i ≤ α' i)
    (hβ : ∀ j, β j ≤ β' j) {Zb Zb' : ℝ} (hZ : Zb ≤ Zb') :
    GaddE p n α β Zb ≤ GaddE p n α' β' Zb' ∧ ∀ i, GaddP p n α β Zb i ≤ GaddP p n α' β' Zb' i := by
  have hl : ∀ m, α m + β m ≤ α' m + β' m := fun m => add_le_add (hα m) (hβ m)
  have hX := pairX_mono p n hA3 hl
  have hF : pairR p n (fun m => α m + β m) ≤ pairR p n fun m => α' m + β' m :=
    mul_le_mul_of_nonneg_left (hX n) (mul_nonneg (Nat.cast_nonneg _) (u_pos p).le)
  exact ⟨gErr_mono' p n hX hZ hF, gParts_mono' p n hX hZ hF⟩

/-! ### Horner's bounds -/

/-- Horner's bounds `(e_k, π^{(k)})` of Lemma 33 grow with `π^z` and `ε_z` -/
theorem hornerB_mono (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {πz πz' : ℕ → ℝ} (hπ0 : ∀ i, 0 ≤ πz i)
    (hπ : ∀ i, πz i ≤ πz' i) {zb εz εz' η : ℝ} (hzb : 0 ≤ zb) (hε0 : 0 ≤ εz) (hε : εz ≤ εz') (hη : 0 ≤ η)
    (Fk : ℕ → ℕ → ℝ) {φ v : ℕ → ℝ} (hφ : ∀ k, 0 ≤ φ k) (hv : ∀ k, 0 ≤ v k) (d : ℕ) : ∀ j,
    (hornerB p n πz zb εz η Fk φ v d j).1 ≤ (hornerB p n πz' zb εz' η Fk φ v d j).1 ∧
      ∀ i, (hornerB p n πz zb εz η Fk φ v d j).2 i ≤ (hornerB p n πz' zb εz' η Fk φ v d j).2 i
  | 0 => ⟨le_rfl, fun _ => le_rfl⟩
  | j + 1 => by
    obtain ⟨i1, i2⟩ := hornerB_mono hA3 hπ0 hπ hzb hε0 hε hη Fk hφ hv d j
    obtain ⟨n1, n2⟩ := hornerB_nonneg p n hA3 hπ0 hzb hε0 hη Fk hφ hv d j
    have hε0' : 0 ≤ εz' := hε0.trans hε
    have hvk := hv (d - (j + 1) + 1)
    have hc : (1 + εz) * zb ≤ (1 + εz') * zb := mul_le_mul_of_nonneg_right (by linarith) hzb
    have hc0 : 0 ≤ (1 + εz) * zb := mul_nonneg (by linarith) hzb
    have hZm : (1 + εz) * zb * (v (d - (j + 1) + 1) + (hornerB p n πz zb εz η Fk φ v d j).1) ≤
        (1 + εz') * zb * (v (d - (j + 1) + 1) + (hornerB p n πz' zb εz' η Fk φ v d j).1) :=
      mul_le_mul hc (by linarith) (add_nonneg hvk n1) (hc0.trans hc)
    obtain ⟨m1, m2⟩ := Gmul_mono p n hA3 hπ0 n2 hπ i2 hZm
    have hD : (1 + εz) * zb * (hornerB p n πz zb εz η Fk φ v d j).1 + εz * zb * v (d - (j + 1) + 1) +
          φ (d - (j + 1)) + (GmulE p n πz (hornerB p n πz zb εz η Fk φ v d j).2
            ((1 + εz) * zb * (v (d - (j + 1) + 1) + (hornerB p n πz zb εz η Fk φ v d j).1)) + n * η) ≤
        (1 + εz') * zb * (hornerB p n πz' zb εz' η Fk φ v d j).1 + εz' * zb * v (d - (j + 1) + 1) +
          φ (d - (j + 1)) + (GmulE p n πz' (hornerB p n πz' zb εz' η Fk φ v d j).2
            ((1 + εz') * zb * (v (d - (j + 1) + 1) + (hornerB p n πz' zb εz' η Fk φ v d j).1)) + n * η) := by
      have a1 : (1 + εz) * zb * (hornerB p n πz zb εz η Fk φ v d j).1 ≤
          (1 + εz') * zb * (hornerB p n πz' zb εz' η Fk φ v d j).1 := mul_le_mul hc i1 n1 (hc0.trans hc)
      have a2 : εz * zb * v (d - (j + 1) + 1) ≤ εz' * zb * v (d - (j + 1) + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hε hzb) hvk
      linarith
    obtain ⟨g1, g2⟩ := Gadd_mono p n hA3 (fun i => le_refl |Fk (d - (j + 1)) i|)
      (fun i => add_le_add (m2 i) (le_refl η)) (add_le_add (le_refl (v (d - (j + 1)))) hD)
    exact ⟨add_le_add hD g1, g2⟩

end ExpansionBounds
