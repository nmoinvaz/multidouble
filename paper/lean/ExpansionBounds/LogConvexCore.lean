import ExpansionBounds.LogConvex
import ExpansionBounds.ExpEval

/-!
# The convex variant of Lemma 39's bounds

Theorem 42's proof (`thm:log`), paragraph "Convexity", evaluates Lemma 39 (`lem:core`) with `b' = 2^{-m}b + nη_0` and
`π'_i = 2^{-m}π_i + η_0` without their minima with `c̄`, with `t̄_j = 2^jb'` for `r ≤ 0`, and with VecSum's second
bound alone in Lemma 13: `coreBpC`, `corePiC`, `coreTC`, `core0C`, `sqBC`, `coreEC` and `coreBoundC`. Each bound of
Lemma 39 is nonnegative and at most its convex variant at larger arguments (`Sand`, `coreBound_sand`), and the convex
variants are in the class `Cvx` as functions of `ℓ` when `b` and the `π_i` are (`coreBoundC_cvx`).
-/

namespace ExpansionBounds

open Finset Set

variable (p : ℤ) (n : ℕ)

/-- `0 ≤ x ≤ y`: a bound of the paper, `x`, is nonnegative and at most its convex variant, `y`. -/
structure Sand (x y : ℝ) : Prop where
  /-- `0 ≤ x` -/
  nonneg : 0 ≤ x
  /-- `x ≤ y` -/
  le : x ≤ y

namespace Sand

variable {x y x' y' : ℝ}

/-- A nonnegative number is between `0` and itself. -/
theorem refl (h : 0 ≤ x) : Sand x x := ⟨h, le_rfl⟩

/-- The larger number is nonnegative too. -/
theorem nonneg' (h : Sand x y) : 0 ≤ y := h.nonneg.trans h.le

/-- Sums keep the relation. -/
theorem add (h : Sand x y) (h' : Sand x' y') : Sand (x + x') (y + y') :=
  ⟨add_nonneg h.nonneg h'.nonneg, add_le_add h.le h'.le⟩

/-- Products keep the relation. -/
theorem mul (h : Sand x y) (h' : Sand x' y') : Sand (x * x') (y * y') :=
  ⟨mul_nonneg h.nonneg h'.nonneg, mul_le_mul h.le h'.le h'.nonneg h.nonneg'⟩

/-- Multiplication by a nonnegative constant keeps the relation. -/
theorem const_mul (h : Sand x y) {c : ℝ} (hc : 0 ≤ c) : Sand (c * x) (c * y) :=
  (refl hc).mul h

/-- Powers keep the relation. -/
theorem pow (h : Sand x y) (k : ℕ) : Sand (x ^ k) (y ^ k) :=
  ⟨pow_nonneg h.nonneg k, pow_le_pow_left₀ h.nonneg h.le k⟩

/-- Maxima keep the relation. -/
theorem max (h : Sand x y) (h' : Sand x' y') : Sand (max x x') (max y y') :=
  ⟨le_max_of_le_left h.nonneg, max_le_max h.le h'.le⟩

/-- Finite sums keep the relation. -/
theorem sum {ι : Type*} (I : Finset ι) {f g : ι → ℝ} (h : ∀ i ∈ I, Sand (f i) (g i)) :
    Sand (∑ i ∈ I, f i) (∑ i ∈ I, g i) :=
  ⟨sum_nonneg fun i hi => (h i hi).nonneg, sum_le_sum fun i hi => (h i hi).le⟩

/-- A function of one argument that keeps the class `Cvx` along a segment keeps the relation: the class is
nonnegative and nondecreasing. `hG` may use that the segment stays below `y`. -/
theorem of_cvx {G : ℝ → ℝ} (h : Sand x y)
    (hG : ∀ f : ℝ → ℝ, Cvx (Icc 0 1) f → (∀ t ∈ Icc (0 : ℝ) 1, f t ≤ y) → Cvx (Icc 0 1) fun t => G (f t)) :
    Sand (G x) (G y) := by
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + (y - x) * t ≤ y := fun t ht => by
    have := mul_le_mul_of_nonneg_left ht.2 (sub_nonneg.mpr h.le)
    linarith
  have h01 := (hG _ (cvx_segment h.nonneg h.le) hseg).zero_le_one
  simp only [mul_zero, add_zero, mul_one, add_sub_cancel] at h01
  exact ⟨h01.1, h01.2⟩

end Sand

/-! ### Lemma 13's bounds and their convex variants -/

/-- `G_MUL`'s bounds are nonnegative and at most their convex variants at larger arguments. -/
theorem Gmul_sand (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {α α' β β' : ℕ → ℝ} (hα : ∀ i, Sand (α i) (α' i))
    (hβ : ∀ j, Sand (β j) (β' j)) {Zb Zb' : ℝ} (hZ : Sand Zb Zb') :
    Sand (GmulE p n α β Zb) (GmulEC p n α' β' Zb') ∧ ∀ i, Sand (GmulP p n α β Zb i) (GmulPC p n α' β' Zb' i) := by
  obtain ⟨n1, n2⟩ := Gmul_nonneg p n hA3 (fun i => (hα i).nonneg) (fun j => (hβ j).nonneg) hZ.nonneg
  obtain ⟨m1, m2⟩ := Gmul_mono p n hA3 (fun i => (hα i).nonneg) (fun j => (hβ j).nonneg) (fun i => (hα i).le)
    (fun j => (hβ j).le) hZ.le
  exact ⟨⟨n1, m1.trans (GmulE_le_GmulEC p n _ _ _)⟩, fun i => ⟨n2 i, (m2 i).trans (GmulP_le_GmulPC p n _ _ _ i)⟩⟩

/-- `G_ADD`'s bounds are nonnegative and at most their convex variants at larger arguments. -/
theorem Gadd_sand (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {α α' β β' : ℕ → ℝ} (hα : ∀ i, Sand (α i) (α' i))
    (hβ : ∀ j, Sand (β j) (β' j)) {Zb Zb' : ℝ} (hZ : Sand Zb Zb') :
    Sand (GaddE p n α β Zb) (GaddEC p n α' β' Zb') ∧ ∀ i, Sand (GaddP p n α β Zb i) (GaddPC p n α' β' Zb' i) := by
  obtain ⟨n1, n2⟩ := Gadd_nonneg p n hA3 (fun i => (hα i).nonneg) (fun j => (hβ j).nonneg) hZ.nonneg
  obtain ⟨m1, m2⟩ := Gadd_mono p n hA3 (fun i => (hα i).le) (fun j => (hβ j).le) hZ.le
  exact ⟨⟨n1, m1.trans (GaddE_le_GaddEC p n _ _ _)⟩, fun i => ⟨n2 i, (m2 i).trans (GaddP_le_GaddPC p n _ _ _ i)⟩⟩

/-- `G_ADDF`'s bounds are nonnegative and at most their convex variants at larger arguments. -/
theorem Gaddf_sand {α α' : ℕ → ℝ} (hα : ∀ i, Sand (α i) (α' i)) {lam0 lam0' Zb Zb' : ℝ} (hl : Sand lam0 lam0')
    (hZ : Sand Zb Zb') : Sand (GaddfE' p n α lam0 Zb) (GaddfEC p n α' lam0' Zb') ∧
      ∀ i, Sand (GaddfP' p n α lam0 Zb i) (GaddfPC p n α' lam0' Zb' i) := by
  have hX0 := addfX_nonneg p n (fun i => (hα i).nonneg) hl.nonneg
  have hX := addfX_mono p n (fun i => (hα i).le) hl.le
  exact ⟨⟨gErr_nonneg p n hX0 hZ.nonneg le_rfl,
      (gErr_mono' p n hX hZ.le le_rfl).trans (gErr_le_gErrC p n _ _ _)⟩,
    fun i => ⟨gParts_nonneg p n hX0 hZ.nonneg le_rfl i,
      (gParts_mono' p n hX hZ.le le_rfl i).trans (gParts_le_gPartsC p n _ _ _ i)⟩⟩

/-- Horner's bounds are nonnegative and at most their convex variants at larger `π^z`, `z̄` and `v_k`. -/
theorem hornerB_sand (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {πz πz' : ℕ → ℝ} (hπ : ∀ i, Sand (πz i) (πz' i))
    {zb zb' εz η : ℝ} (hz : Sand zb zb') (hε : 0 ≤ εz) (hη : 0 ≤ η) (Fk : ℕ → ℕ → ℝ) {φ v v' : ℕ → ℝ}
    (hφ : ∀ k, 0 ≤ φ k) (hv : ∀ k, Sand (v k) (v' k)) (d j : ℕ) :
    Sand (hornerB p n πz zb εz η Fk φ v d j).1 (hornerBC p n πz' zb' εz η Fk φ v' d j).1 ∧
      ∀ i, Sand ((hornerB p n πz zb εz η Fk φ v d j).2 i) ((hornerBC p n πz' zb' εz η Fk φ v' d j).2 i) := by
  obtain ⟨n1, n2⟩ := hornerB_nonneg p n hA3 (fun i => (hπ i).nonneg) hz.nonneg hε hη Fk hφ
    (fun k => (hv k).nonneg) d j
  obtain ⟨m1, m2⟩ := hornerB_mono2 p n hA3 (fun i => (hπ i).nonneg) (fun i => (hπ i).le) hz.nonneg hz.le hε
    le_rfl hη Fk hφ (fun k => (hv k).nonneg) (fun k => (hv k).le) d j
  obtain ⟨c1, c2⟩ := hornerB_le_hornerBC p n hA3 (fun i => (hπ i).nonneg') hz.nonneg' hε hη Fk hφ
    (fun k => (hv k).nonneg') d j
  exact ⟨⟨n1, m1.trans c1⟩, fun i => ⟨n2 i, (m2 i).trans (c2 i)⟩⟩

/-! ### `b'`, `π'`, `t̄_j`, `g_j`, `v_k` and `E^tr` -/

/-- `b' = 2^{-m} b + nη`, without the minimum with `c̄` -/
noncomputable def coreBpC (m : ℕ) (b η : ℝ) : ℝ := (2 : ℝ) ^ (-(m : ℤ)) * b + n * η

/-- `π'_i = 2^{-m} π_i + η`, without the minimum with `c̄` -/
noncomputable def corePiC (m : ℕ) (π : ℕ → ℝ) (η : ℝ) : ℕ → ℝ := fun i => (2 : ℝ) ^ (-(m : ℤ)) * π i + η

/-- `t̄_j = e^{2^j b'} - 1` for `r ≥ 0` and `2^j b'` for `r ≤ 0`, which is at least `1 - e^{-2^j b'}` -/
noncomputable def coreTC (pos : Bool) (b' : ℝ) (j : ℕ) : ℝ :=
  if pos then Real.exp (2 ^ j * b') - 1 else 2 ^ j * b'

/-- `b'` is nonnegative and at most its variant without the minimum. -/
theorem coreBp_sand (e : ℤ) (m : ℕ) {b b₁ η : ℝ} (hb : Sand b b₁) (hη : 0 ≤ η) :
    Sand (coreBp n e m b η) (coreBpC n m b₁ η) := by
  have h2 : (0 : ℝ) ≤ 2 ^ (-(m : ℤ)) := by positivity
  have hm : Sand (min b ((2 : ℝ) ^ (e + 1))) b₁ := ⟨le_min hb.nonneg (by positivity), (min_le_left _ _).trans hb.le⟩
  exact (hm.const_mul h2).add (Sand.refl (mul_nonneg (Nat.cast_nonneg n) hη))

/-- `π'_i` is nonnegative and at most its variant without the minimum. -/
theorem corePi_sand (e : ℤ) (m : ℕ) {π π₁ : ℕ → ℝ} (hπ : ∀ i, Sand (π i) (π₁ i)) {η : ℝ} (hη : 0 ≤ η) (i : ℕ) :
    Sand (corePi e m π η i) (corePiC m π₁ η i) := by
  have h2 : (0 : ℝ) ≤ 2 ^ (-(m : ℤ)) := by positivity
  have hm : Sand (min (π i) ((2 : ℝ) ^ (e + 1))) (π₁ i) :=
    ⟨le_min (hπ i).nonneg (by positivity), (min_le_left _ _).trans (hπ i).le⟩
  exact (hm.const_mul h2).add (Sand.refl hη)

/-- `t̄_j` is nonnegative and at most its convex variant: `1 - e^{-z} ≤ z`. -/
theorem coreT_sand {b' b₁ : ℝ} (h : Sand b' b₁) (pos : Bool) (j : ℕ) :
    Sand (coreT pos b' j) (coreTC pos b₁ j) := by
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have hz : 0 ≤ 2 ^ j * b' := mul_nonneg h2.le h.nonneg
  have hzz : 2 ^ j * b' ≤ 2 ^ j * b₁ := mul_le_mul_of_nonneg_left h.le h2.le
  cases pos with
  | true =>
    simp only [coreT, coreTC, ↓reduceIte]
    have := Real.one_le_exp hz
    have := Real.exp_le_exp.mpr hzz
    exact ⟨by linarith, by linarith⟩
  | false =>
    simp only [coreT, coreTC, Bool.false_eq_true, ↓reduceIte]
    have := Real.add_one_le_exp (-(2 ^ j * b'))
    have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz)
    exact ⟨by linarith, by linarith⟩

/-- `g_j` is nonnegative and grows with `b'`. -/
theorem coreG_sand {b' b₁ : ℝ} (h : Sand b' b₁) (pos : Bool) (a' : ℝ) (j : ℕ) :
    Sand (coreG pos a' b' j) (coreG pos a' b₁ j) := by
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  cases pos with
  | true =>
    simp only [coreG, ↓reduceIte]
    exact ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h.le h2.le)⟩
  | false =>
    simp only [coreG, Bool.false_eq_true, ↓reduceIte]
    exact Sand.refl (Real.exp_pos _).le

variable {s : Set ℝ}

/-- `b'` without the minimum is in the class when `b` is. -/
theorem coreBpC_cvx (hs : Convex ℝ s) (m : ℕ) {b : ℝ → ℝ} (hb : Cvx s b) {η : ℝ} (hη : 0 ≤ η) :
    Cvx s fun l => coreBpC n m (b l) η :=
  (hb.const_mul (by positivity)).add (Cvx.const hs (mul_nonneg (Nat.cast_nonneg n) hη))

/-- `π'_i` without the minimum is in the class when `π_i` is. -/
theorem corePiC_cvx (hs : Convex ℝ s) (m : ℕ) {π : ℝ → ℕ → ℝ} (hπ : ∀ i, Cvx s fun l => π l i) {η : ℝ}
    (hη : 0 ≤ η) (i : ℕ) : Cvx s fun l => corePiC m (π l) η i :=
  ((hπ i).const_mul (by positivity)).add (Cvx.const hs hη)

/-- The convex `t̄_j` is in the class when `b'` is. -/
theorem coreTC_cvx (pos : Bool) {b' : ℝ → ℝ} (hb : Cvx s b') (j : ℕ) : Cvx s fun l => coreTC pos (b' l) j := by
  simp only [coreTC]
  exact Cvx.ite _ (fun _ => (hb.const_mul (by positivity)).exp_sub_one) fun _ => hb.const_mul (by positivity)

/-- `g_j` is in the class when `b'` is: `e^{2^j b'}` for `r ≥ 0`, and a constant for `r ≤ 0`. -/
theorem coreG_cvx (pos : Bool) (a' : ℝ) {b' : ℝ → ℝ} (hb : Cvx s b') (j : ℕ) :
    Cvx s fun l => coreG pos a' (b' l) j := by
  simp only [coreG]
  exact Cvx.ite _ (fun _ => (hb.const_mul (by positivity)).exp) fun _ => Cvx.const hb.convex.1 (Real.exp_pos _).le

/-- `v_k`, a polynomial in `b'` with nonnegative coefficients, is in the class when `b'` is. -/
theorem coreV_cvx {b' : ℝ → ℝ} (hb : Cvx s b') (d k : ℕ) : Cvx s fun l => coreV (b' l) d k := by
  simp only [coreV, hornerE]
  exact Cvx.sum hb.convex.1 _ fun l _ => (hb.pow l).const_mul (by unfold invF; positivity)

/-- `E^tr_d` is in the class when `b'` is, where `b' < d + 2`. -/
theorem eTr_cvx {b' : ℝ → ℝ} (hb : Cvx s b') (d : ℕ) (hbd : ∀ l ∈ s, b' l < d + 2) :
    Cvx s fun l => eTr (b' l) d := by
  have hd2 : (0 : ℝ) < d + 2 := by positivity
  have h1 : ∀ l ∈ s, b' l / (d + 2) < 1 := fun l hl => by
    rw [div_lt_one hd2]
    exact hbd l hl
  have h := ((hb.pow (d + 1)).mul ((hb.div_const hd2.le).one_div_one_sub h1)).div_const
    (Nat.cast_nonneg (d + 1).factorial)
  refine h.congr fun l _ => ?_
  simp only [eTr]
  rw [mul_one_div, div_div, mul_comm]

/-- `v_k` is nonnegative and grows with `b'`. -/
theorem coreV_sand {b' b₁ : ℝ} (h : Sand b' b₁) (d k : ℕ) : Sand (coreV b' d k) (coreV b₁ d k) :=
  h.of_cvx (G := fun z => coreV z d k) fun _ hf _ => coreV_cvx hf d k

/-- `E^tr_d` is nonnegative and grows with `b'` below `d + 2`. -/
theorem eTr_sand {b' b₁ : ℝ} (h : Sand b' b₁) (d : ℕ) (hbd : b₁ < d + 2) : Sand (eTr b' d) (eTr b₁ d) :=
  h.of_cvx (G := fun z => eTr z d) fun _ hf hle => eTr_cvx hf d fun t ht => (hle t ht).trans_lt hbd

/-! ### `(E_0, ψ_0)` -/

/-- `(E_0, ψ_0)` of Lemma 39 with VecSum's second bound alone in each `G_MUL` and `G_ADD` -/
noncomputable def core0C (T0 D η : ℝ) (π' : ℕ → ℝ) (b' : ℝ) (Fk : ℕ → ℕ → ℝ) (φ : ℕ → ℝ) (d' : ℕ) :
    ℝ × (ℕ → ℝ) :=
  if d' = 1 then (eTr b' 1 + D, π') else
    let H := hornerBC p n π' b' 0 0 Fk φ (coreV b' d') d' (d' - 2)
    let Zw := b' * (coreV b' d' 2 + H.1)
    let ε1 := GmulEC p n π' H.2 Zw
    let Zy := b' * (Zw + ε1)
    let ω := GmulPC p n π' (GmulPC p n π' H.2 Zw) Zy
    let Em := GmulEC p n π' (GmulPC p n π' H.2 Zw) Zy + b' * (ε1 + b' * H.1) + eTr b' d' + D
    (Em + GaddEC p n π' ω (T0 + Em) + n * η, fun i => GaddPC p n π' ω (T0 + Em) i + η)

/-- `(E_0, ψ_0)` is nonnegative and at most its convex variant at larger `t̄_0`, `π'` and `b' < d' + 2`. -/
theorem core0_sand (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {T0 T₁ D η : ℝ} (hT : Sand T0 T₁) (hD : 0 ≤ D)
    (hη : 0 ≤ η) {π' π₁ : ℕ → ℝ} (hπ : ∀ i, Sand (π' i) (π₁ i)) {b' b₁ : ℝ} (hb : Sand b' b₁) (Fk : ℕ → ℕ → ℝ)
    {φ : ℕ → ℝ} (hφ : ∀ k, 0 ≤ φ k) (d' : ℕ) (hbd : b₁ < d' + 2) :
    Sand (core0 p n T0 D η π' b' Fk φ d').1 (core0C p n T₁ D η π₁ b₁ Fk φ d').1 ∧
      ∀ i, Sand ((core0 p n T0 D η π' b' Fk φ d').2 i) ((core0C p n T₁ D η π₁ b₁ Fk φ d').2 i) := by
  by_cases hd : d' = 1
  · subst hd
    simp only [core0, core0C, ↓reduceIte]
    exact ⟨(eTr_sand hb 1 hbd).add (Sand.refl hD), hπ⟩
  · have hv : ∀ k, Sand (coreV b' d' k) (coreV b₁ d' k) := fun k => coreV_sand hb d' k
    obtain ⟨hH1, hH2⟩ := hornerB_sand p n hA3 hπ hb (le_refl (0 : ℝ)) (le_refl (0 : ℝ)) Fk hφ hv d' (d' - 2)
    have hZw := hb.mul ((hv 2).add hH1)
    obtain ⟨hε1, hω1⟩ := Gmul_sand p n hA3 hπ hH2 hZw
    have hZy := hb.mul (hZw.add hε1)
    obtain ⟨hε2, hω⟩ := Gmul_sand p n hA3 hπ hω1 hZy
    have hEm := ((hε2.add (hb.mul (hε1.add (hb.mul hH1)))).add (eTr_sand hb d' hbd)).add (Sand.refl hD)
    obtain ⟨hε3, hψ⟩ := Gadd_sand p n hA3 hπ hω (hT.add hEm)
    simp only [core0, core0C, hd, ↓reduceIte]
    exact ⟨(hEm.add hε3).add (Sand.refl (mul_nonneg (Nat.cast_nonneg n) hη)),
      fun i => (hψ i).add (Sand.refl hη)⟩

/-- The convex `(E_0, ψ_0)` is in the class when `t̄_0`, `π'` and `b'` are, where `b' < d' + 2`. -/
theorem core0C_cvx (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (hs : Convex ℝ s) {T0 : ℝ → ℝ} (hT : Cvx s T0) {D η : ℝ}
    (hD : 0 ≤ D) (hη : 0 ≤ η) {π' : ℝ → ℕ → ℝ} (hπ : ∀ i, Cvx s fun l => π' l i) {b' : ℝ → ℝ} (hb : Cvx s b')
    (Fk : ℕ → ℕ → ℝ) {φ : ℕ → ℝ} (hφ : ∀ k, 0 ≤ φ k) (d' : ℕ) (hbd : ∀ l ∈ s, b' l < d' + 2) :
    (Cvx s fun l => (core0C p n (T0 l) D η (π' l) (b' l) Fk φ d').1) ∧
      ∀ i, Cvx s fun l => (core0C p n (T0 l) D η (π' l) (b' l) Fk φ d').2 i := by
  by_cases hd : d' = 1
  · subst hd
    simp only [core0C, ↓reduceIte]
    exact ⟨(eTr_cvx hb 1 hbd).add (Cvx.const hs hD), hπ⟩
  · have hv : ∀ k, Cvx s fun l => coreV (b' l) d' k := fun k => coreV_cvx hb d' k
    obtain ⟨hH1, hH2⟩ := hornerBC_cvx p n hA3 hs hπ hb (le_refl (0 : ℝ)) (le_refl (0 : ℝ)) Fk hφ hv d' (d' - 2)
    have hZw := hb.mul ((hv 2).add hH1)
    have hε1 := GmulEC_cvx p n hA3 hs hπ hH2 hZw
    have hω1 := fun i => GmulPC_cvx p n hA3 hs hπ hH2 hZw i
    have hZy := hb.mul (hZw.add hε1)
    have hε2 := GmulEC_cvx p n hA3 hs hπ hω1 hZy
    have hω := fun i => GmulPC_cvx p n hA3 hs hπ hω1 hZy i
    have hEm := ((hε2.add (hb.mul (hε1.add (hb.mul hH1)))).add (eTr_cvx hb d' hbd)).add (Cvx.const hs hD)
    have hZ := hT.add hEm
    refine ⟨?_, fun i => ?_⟩
    · simp only [core0C, hd, ↓reduceIte]
      exact (hEm.add (GaddEC_cvx p n hA3 hs hπ hω hZ)).add (Cvx.const hs (mul_nonneg (Nat.cast_nonneg n) hη))
    · simp only [core0C, hd, ↓reduceIte]
      exact (GaddPC_cvx p n hA3 hs hπ hω hZ i).add (Cvx.const hs hη)

/-! ### The squarings -/

/-- one squaring's bounds with VecSum's second bound alone -/
noncomputable def sqBC (T T' g E : ℝ) (ψ : ℕ → ℝ) : ℝ × (ℕ → ℝ) :=
  let εm := GmulEC p n ψ ψ ((T + E) ^ 2)
  let Zs := T' + 2 * E * (1 + T) + E ^ 2 + εm
  (2 * g * E + E ^ 2 + εm + GaddEC p n (fun i => 2 * ψ i) (GmulPC p n ψ ψ ((T + E) ^ 2)) Zs,
    GaddPC p n (fun i => 2 * ψ i) (GmulPC p n ψ ψ ((T + E) ^ 2)) Zs)

/-- `(E_j, ψ_j)` with VecSum's second bound alone, from `(E_0, ψ_0)` by `sqBC` -/
noncomputable def coreEC (T g : ℕ → ℝ) (E0 : ℝ) (ψ0 : ℕ → ℝ) : ℕ → ℝ × (ℕ → ℝ)
  | 0 => (E0, ψ0)
  | j + 1 => sqBC p n (T j) (T (j + 1)) (g j) (coreEC T g E0 ψ0 j).1 (coreEC T g E0 ψ0 j).2

/-- One squaring's bounds are nonnegative and at most their convex variants at larger arguments. -/
theorem sqB_sand (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {T T₁ T' T₁' g g₁ E E₁ : ℝ} (hT : Sand T T₁)
    (hT' : Sand T' T₁') (hg : Sand g g₁) (hE : Sand E E₁) {ψ ψ₁ : ℕ → ℝ} (hψ : ∀ i, Sand (ψ i) (ψ₁ i)) :
    Sand (sqB p n T T' g E ψ).1 (sqBC p n T₁ T₁' g₁ E₁ ψ₁).1 ∧
      ∀ i, Sand ((sqB p n T T' g E ψ).2 i) ((sqBC p n T₁ T₁' g₁ E₁ ψ₁).2 i) := by
  have h2 : (0 : ℝ) ≤ 2 := zero_le_two
  have hZm := (hT.add hE).pow 2
  obtain ⟨hεm, hν⟩ := Gmul_sand p n hA3 hψ hψ hZm
  have hZs := ((hT'.add ((hE.const_mul h2).mul ((Sand.refl zero_le_one).add hT))).add (hE.pow 2)).add hεm
  obtain ⟨hεs, hψ'⟩ := Gadd_sand p n hA3 (fun i => (hψ i).const_mul h2) hν hZs
  simp only [sqB, sqBC]
  exact ⟨((((hg.const_mul h2).mul hE).add (hE.pow 2)).add hεm).add hεs, hψ'⟩

/-- The convex bounds of one squaring are in the class when their arguments are. -/
theorem sqBC_cvx (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (hs : Convex ℝ s) {T T' g E : ℝ → ℝ} (hT : Cvx s T)
    (hT' : Cvx s T') (hg : Cvx s g) (hE : Cvx s E) {ψ : ℝ → ℕ → ℝ} (hψ : ∀ i, Cvx s fun l => ψ l i) :
    (Cvx s fun l => (sqBC p n (T l) (T' l) (g l) (E l) (ψ l)).1) ∧
      ∀ i, Cvx s fun l => (sqBC p n (T l) (T' l) (g l) (E l) (ψ l)).2 i := by
  have h2 : (0 : ℝ) ≤ 2 := zero_le_two
  have hZm := (hT.add hE).pow 2
  have hεm := GmulEC_cvx p n hA3 hs hψ hψ hZm
  have hν := fun i => GmulPC_cvx p n hA3 hs hψ hψ hZm i
  have hZs := ((hT'.add ((hE.const_mul h2).mul ((Cvx.const hs zero_le_one).add hT))).add (hE.pow 2)).add hεm
  have h2ψ := fun i => (hψ i).const_mul h2
  refine ⟨?_, fun i => ?_⟩
  · simp only [sqBC]
    exact ((((hg.const_mul h2).mul hE).add (hE.pow 2)).add hεm).add (GaddEC_cvx p n hA3 hs h2ψ hν hZs)
  · simp only [sqBC]
    exact GaddPC_cvx p n hA3 hs h2ψ hν hZs i

/-- `(E_j, ψ_j)` is nonnegative and at most its convex variant at larger `t̄_j`, `g_j` and `(E_0, ψ_0)`. -/
theorem coreE_sand (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {T T₁ g g₁ : ℕ → ℝ} (hT : ∀ j, Sand (T j) (T₁ j))
    (hg : ∀ j, Sand (g j) (g₁ j)) {E0 E₁ : ℝ} (hE : Sand E0 E₁) {ψ0 ψ₁ : ℕ → ℝ} (hψ : ∀ i, Sand (ψ0 i) (ψ₁ i)) :
    ∀ j, Sand (coreE p n T g E0 ψ0 j).1 (coreEC p n T₁ g₁ E₁ ψ₁ j).1 ∧
      ∀ i, Sand ((coreE p n T g E0 ψ0 j).2 i) ((coreEC p n T₁ g₁ E₁ ψ₁ j).2 i)
  | 0 => ⟨hE, hψ⟩
  | j + 1 => by
    obtain ⟨h1, h2⟩ := coreE_sand hA3 hT hg hE hψ j
    exact sqB_sand p n hA3 (hT j) (hT (j + 1)) (hg j) h1 h2

/-- The convex `(E_j, ψ_j)` is in the class when `t̄_j`, `g_j` and `(E_0, ψ_0)` are. -/
theorem coreEC_cvx (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (hs : Convex ℝ s) {T g : ℝ → ℕ → ℝ}
    (hT : ∀ j, Cvx s fun l => T l j) (hg : ∀ j, Cvx s fun l => g l j) {E0 : ℝ → ℝ} (hE : Cvx s E0)
    {ψ0 : ℝ → ℕ → ℝ} (hψ : ∀ i, Cvx s fun l => ψ0 l i) :
    ∀ j, (Cvx s fun l => (coreEC p n (T l) (g l) (E0 l) (ψ0 l) j).1) ∧
      ∀ i, Cvx s fun l => (coreEC p n (T l) (g l) (E0 l) (ψ0 l) j).2 i
  | 0 => ⟨hE, hψ⟩
  | j + 1 => by
    obtain ⟨h1, h2⟩ := coreEC_cvx hA3 hs hT hg hE hψ j
    exact sqBC_cvx p n hA3 hs (hT j) (hT (j + 1)) (hg j) h1 h2

/-! ### Lemma 39's bounds -/

/-- `(E_m, ψ_m)` of Lemma 39 for the convex variant: `b'` and `π'` without their minima, `t̄_j = 2^j b'` for
`r ≤ 0`, and VecSum's second bound alone; the exponent `e` of a case no longer enters -/
noncomputable def coreBoundC (η₁ η₂ : ℝ) (pos : Bool) (m : ℕ) (a b : ℝ) (π : ℕ → ℝ) (Fk : ℕ → ℕ → ℝ)
    (φ : ℕ → ℝ) (d' : ℕ) : ℝ × (ℕ → ℝ) :=
  coreEC p n (coreTC pos (coreBpC n m b η₁)) (coreG pos ((2 : ℝ) ^ (-(m : ℤ)) * a) (coreBpC n m b η₁))
    (core0C p n (coreTC pos (coreBpC n m b η₁) 0) (2 * n * η₁) η₂ (corePiC m π η₁) (coreBpC n m b η₁) Fk φ d').1
    (core0C p n (coreTC pos (coreBpC n m b η₁) 0) (2 * n * η₁) η₂ (corePiC m π η₁) (coreBpC n m b η₁) Fk φ d').2 m

/-- Lemma 39's `(E_m, ψ_m)` is nonnegative and at most its convex variant at larger `b` and `π`, where the convex
`b'` is below `d' + 2`. -/
theorem coreBound_sand (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {η₁ η₂ : ℝ} (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂) (pos : Bool)
    (e : ℤ) (m : ℕ) (a : ℝ) {b b₁ : ℝ} (hb : Sand b b₁) {π π₁ : ℕ → ℝ} (hπ : ∀ i, Sand (π i) (π₁ i))
    (Fk : ℕ → ℕ → ℝ) {φ : ℕ → ℝ} (hφ : ∀ k, 0 ≤ φ k) (d' : ℕ) (hbd : coreBpC n m b₁ η₁ < d' + 2) :
    Sand (coreBound p n η₁ η₂ pos e m a b π Fk φ d').1 (coreBoundC p n η₁ η₂ pos m a b₁ π₁ Fk φ d').1 ∧
      ∀ i, Sand ((coreBound p n η₁ η₂ pos e m a b π Fk φ d').2 i)
        ((coreBoundC p n η₁ η₂ pos m a b₁ π₁ Fk φ d').2 i) := by
  have hbp := coreBp_sand n e m hb hη₁
  have hD : (0 : ℝ) ≤ 2 * n * η₁ := mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg n)) hη₁
  obtain ⟨h1, h2⟩ := core0_sand p n hA3 (coreT_sand hbp pos 0) hD hη₂ (fun i => corePi_sand e m hπ hη₁ i) hbp
    Fk hφ d' hbd
  exact coreE_sand p n hA3 (fun j => coreT_sand hbp pos j) (fun j => coreG_sand hbp pos _ j) h1 h2 m

/-- The convex `(E_m, ψ_m)` is in the class as a function of `ℓ` when `b` and the `π_i` are, for a fixed case and
where the convex `b'` is below `d' + 2`. -/
theorem coreBoundC_cvx (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (hs : Convex ℝ s) {η₁ η₂ : ℝ} (hη₁ : 0 ≤ η₁)
    (hη₂ : 0 ≤ η₂) (pos : Bool) (m : ℕ) (a : ℝ) {b : ℝ → ℝ} (hb : Cvx s b) {π : ℝ → ℕ → ℝ}
    (hπ : ∀ i, Cvx s fun l => π l i) (Fk : ℕ → ℕ → ℝ) {φ : ℕ → ℝ} (hφ : ∀ k, 0 ≤ φ k) (d' : ℕ)
    (hbd : ∀ l ∈ s, coreBpC n m (b l) η₁ < d' + 2) :
    (Cvx s fun l => (coreBoundC p n η₁ η₂ pos m a (b l) (π l) Fk φ d').1) ∧
      ∀ i, Cvx s fun l => (coreBoundC p n η₁ η₂ pos m a (b l) (π l) Fk φ d').2 i := by
  have hbp := coreBpC_cvx n hs m hb hη₁
  have hD : (0 : ℝ) ≤ 2 * n * η₁ := mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg n)) hη₁
  obtain ⟨h1, h2⟩ := core0C_cvx p n hA3 hs (coreTC_cvx pos hbp 0) hD hη₂ (fun i => corePiC_cvx hs m hπ hη₁ i) hbp
    Fk hφ d' hbd
  exact coreEC_cvx p n hA3 hs (fun j => coreTC_cvx pos hbp j) (fun j => coreG_cvx pos _ hbp j) h1 h2 m

end ExpansionBounds
