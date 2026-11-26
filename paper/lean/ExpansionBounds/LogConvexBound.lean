import ExpansionBounds.LogConvexCore

/-!
# The convex variant of Theorem 42's bound

Theorem 42's proof (`thm:log`), paragraph "Convexity": `logBoundC` is the bound `𝓔(ℓ)` of a case evaluated with
VecSum's second bound alone in Lemma 13, with `b'` and `π'` of Lemma 39 without their minima, `t̄_j = 2^jb'` for
`r ≤ 0`, and `φ̄ = max(ξ - 1, E + b + δ + 2nη_0)` (`logPhiBC`, `logC4C`, `logCase4C`, `logPC`). It is at least the
bound `logBound` of `thm42_case` (`logBound_sand`), and for a fixed case it is nonnegative, nondecreasing and convex
in `ℓ` when `E`, `b`, `δ` and the part bounds `π`, `π^y` and `π^x` are (`logBoundC_cvx`), on an interval where
`b' < d' + 2` and `C < 1` at its right end (`logBoundC_cvx_Icc`).
-/

namespace ExpansionBounds

open Finset Set

variable (p : ℤ) (n : ℕ) {s : Set ℝ}

/-! ### More of the class and of the relation -/

/-- A function of the class less a constant is nondecreasing. -/
theorem Cvx.sub_const_mono {f : ℝ → ℝ} (hf : Cvx s f) (c : ℝ) : MonotoneOn (fun x => f x - c) s :=
  fun _ hx _ hy h => sub_le_sub_right (hf.mono hx hy h) c

/-- A function of the class less a constant is convex. -/
theorem Cvx.sub_const_convex {f : ℝ → ℝ} (hf : Cvx s f) (c : ℝ) : ConvexOn ℝ s fun x => f x - c := by
  refine ⟨hf.convex.1, fun x hx y hy a b ha hb hab => ?_⟩
  have h := hf.convex.2 hx hy ha hb hab
  have hc : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
  simp only [smul_eq_mul] at h ⊢
  linarith

/-- Division by a nonnegative constant keeps the relation. -/
theorem Sand.div_const {x y : ℝ} (h : Sand x y) {c : ℝ} (hc : 0 ≤ c) : Sand (x / c) (y / c) :=
  ⟨div_nonneg h.nonneg hc, div_le_div_of_nonneg_right h.le hc⟩

/-- Division by `1 - C` keeps the relation where the larger `C` is below one. -/
theorem Sand.div_one_sub {x x' C C₁ : ℝ} (hx : Sand x x') (hC : Sand C C₁) (hC1 : C₁ < 1) :
    Sand (x / (1 - C)) (x' / (1 - C₁)) := by
  have hinv : Sand (1 / (1 - C)) (1 / (1 - C₁)) :=
    hC.of_cvx (G := fun z => 1 / (1 - z)) fun _ hf hle => hf.one_div_one_sub fun t ht => (hle t ht).trans_lt hC1
  have h := hx.mul hinv
  rwa [mul_one_div, mul_one_div] at h

/-! ### `ξ`, `φ̄` and `v_i` -/

/-- `φ̄ = max(ξ - 1, E + b + δ + D)`, with `E + b + δ` in place of `1 - e^{-(E+b+δ)}` -/
noncomputable def logPhiBC (D : ℝ) (pos : Bool) (E a b δ : ℝ) : ℝ :=
  max (logXi D pos E a b δ - 1) (E + b + δ + D)

/-- `ξ` is nonnegative. -/
theorem logXi_nonneg {D : ℝ} (hD : 0 ≤ D) (pos : Bool) (E a b δ : ℝ) : 0 ≤ logXi D pos E a b δ := by
  unfold logXi
  split_ifs <;> positivity

/-- `ξ` is in the class when `E`, `b` and `δ` are, for a fixed `a`. -/
theorem logXi_cvx (hs : Convex ℝ s) {D : ℝ} (hD : 0 ≤ D) (pos : Bool) (a : ℝ) {E b δ : ℝ → ℝ} (hE : Cvx s E)
    (hb : Cvx s b) (hδ : Cvx s δ) : Cvx s fun l => logXi D pos (E l) a (b l) (δ l) := by
  simp only [logXi]
  exact (Cvx.ite _ (fun _ => Cvx.exp_of ((hE.add hδ).sub_const_mono a) ((hE.add hδ).sub_const_convex a))
    fun _ => ((hE.add hb).add hδ).exp).add (Cvx.const hs hD)

/-- `φ̄` is nonnegative and at most its convex variant: `1 - e^{-z} ≤ z`. -/
theorem logPhiB_sand {D E b δ : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E) (hb : 0 ≤ b) (hδ : 0 ≤ δ) (pos : Bool) (a : ℝ) :
    Sand (logPhiB D pos E a b δ) (logPhiBC D pos E a b δ) := by
  have hz : 0 ≤ E + b + δ := add_nonneg (add_nonneg hE hb) hδ
  have h1 := Real.add_one_le_exp (-(E + b + δ))
  have h2 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz)
  simp only [logPhiB, logPhiBC]
  exact ⟨le_max_of_le_right (by linarith), max_le_max le_rfl (by linarith)⟩

/-- The convex `φ̄` is in the class when `E`, `b` and `δ` are, for a fixed `a`: `ξ - 1` may be negative. -/
theorem logPhiBC_cvx (hs : Convex ℝ s) {D : ℝ} (hD : 0 ≤ D) (pos : Bool) (a : ℝ) {E b δ : ℝ → ℝ} (hE : Cvx s E)
    (hb : Cvx s b) (hδ : Cvx s δ) : Cvx s fun l => logPhiBC D pos (E l) a (b l) (δ l) := by
  have hξ := logXi_cvx hs hD pos a hE hb hδ
  simp only [logPhiBC]
  exact Cvx.max_left (hξ.sub_const_mono 1) (hξ.sub_const_convex 1) (((hE.add hb).add hδ).add (Cvx.const hs hD))

/-- `v_i` of step (5) is nonnegative and grows with `C`. -/
theorem logV_sand {C C₁ : ℝ} (h : Sand C C₁) (q k : ℕ) : Sand (logV C q k) (logV C₁ q k) :=
  Sand.sum _ fun l _ => (h.pow l).div_const (Nat.cast_nonneg _)

/-- `v_i` of step (5), a polynomial in `C` with nonnegative coefficients, is in the class when `C` is. -/
theorem logV_cvx {C : ℝ → ℝ} (hC : Cvx s C) (q k : ℕ) : Cvx s fun l => logV (C l) q k := by
  simp only [logV]
  exact Cvx.sum hC.convex.1 _ fun l _ => (hC.pow l).div_const (Nat.cast_nonneg _)

/-! ### Step (4) -/

/-- step (4)'s bounds with VecSum's second bound alone in each `G_MUL` and `G_ADD` -/
noncomputable def logC4C (D η : ℝ) (πφ ψ : ℕ → ℝ) (φb tb Em E δ b ξ : ℝ) (B : ℤ) : ℝ × (ℕ → ℝ) :=
  let Zp := φb * (tb + Em)
  let εφt := GmulEC p n πφ ψ Zp + n * η + (2 : ℝ) ^ (-B - 12) * max φb (tb + Em)
  let ν := fun i => GmulPC p n πφ ψ Zp i + η
  let Zs := 2 * (Real.exp (b + δ) - 1 - (b + δ)) + Real.exp (b + δ) * (Real.exp (E + δ) - 1) + Em + D
  let Eδ := Real.exp E * (Real.exp δ - 1) + D * (1 + tb + Em)
  let Zc := (Real.exp E - 1) + ξ * Em + Eδ + εφt + GaddEC p n πφ ψ Zs
  let Ec := ξ * Em + Eδ + εφt + GaddEC p n πφ ψ Zs + GaddEC p n (GaddPC p n πφ ψ Zs) ν Zc
  (Ec, fun i => max (GaddPC p n (GaddPC p n πφ ψ Zs) ν Zc i) (GaddPC p n πφ ψ (Real.exp E - 1 + Ec) i))

/-- Step (4)'s bounds are nonnegative and at most their convex variants at larger `π^φ`, `ψ`, `φ̄`, `t̄` and
`E_m`. -/
theorem logC4_sand (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {D η : ℝ} (hD : 0 ≤ D) (hη : 0 ≤ η) {πφ πφ₁ ψ ψ₁ : ℕ → ℝ}
    (hπφ : ∀ i, Sand (πφ i) (πφ₁ i)) (hψ : ∀ i, Sand (ψ i) (ψ₁ i)) {φb φb₁ tb tb₁ Em Em₁ : ℝ} (hφb : Sand φb φb₁)
    (htb : Sand tb tb₁) (hEm : Sand Em Em₁) {E δ ξ : ℝ} (hE : 0 ≤ E) (hδ : 0 ≤ δ) (b : ℝ) (hξ : 0 ≤ ξ) (B : ℤ) :
    Sand (logC4 p n D η πφ ψ φb tb Em E δ b ξ B).1 (logC4C p n D η πφ₁ ψ₁ φb₁ tb₁ Em₁ E δ b ξ B).1 ∧
      ∀ i, Sand ((logC4 p n D η πφ ψ φb tb Em E δ b ξ B).2 i)
        ((logC4C p n D η πφ₁ ψ₁ φb₁ tb₁ Em₁ E δ b ξ B).2 i) := by
  have hZp := hφb.mul (htb.add hEm)
  obtain ⟨hεp, hν0⟩ := Gmul_sand p n hA3 hπφ hψ hZp
  have h2B : (0 : ℝ) ≤ 2 ^ (-B - 12) := by positivity
  have hεφt := (hεp.add (Sand.refl (mul_nonneg (Nat.cast_nonneg n) hη))).add
    ((hφb.max (htb.add hEm)).const_mul h2B)
  have hν := fun i => (hν0 i).add (Sand.refl hη)
  have hc1 : 0 ≤ 2 * (Real.exp (b + δ) - 1 - (b + δ)) := by
    have := Real.add_one_le_exp (b + δ)
    linarith
  have hc2 : 0 ≤ Real.exp (b + δ) * (Real.exp (E + δ) - 1) := by
    have := Real.one_le_exp (add_nonneg hE hδ)
    exact mul_nonneg (Real.exp_pos _).le (by linarith)
  have hZs := (((Sand.refl hc1).add (Sand.refl hc2)).add hEm).add (Sand.refl hD)
  obtain ⟨hεs, hπs⟩ := Gadd_sand p n hA3 hπφ hψ hZs
  have hc3 : 0 ≤ Real.exp E * (Real.exp δ - 1) := by
    have := Real.one_le_exp hδ
    exact mul_nonneg (Real.exp_pos _).le (by linarith)
  have hEδ := (Sand.refl hc3).add ((((Sand.refl (zero_le_one : (0 : ℝ) ≤ 1)).add htb).add hEm).const_mul hD)
  have hc4 : 0 ≤ Real.exp E - 1 := by
    have := Real.one_le_exp hE
    linarith
  have hξE := (Sand.refl hξ).mul hEm
  have hZc := ((((Sand.refl hc4).add hξE).add hEδ).add hεφt).add hεs
  obtain ⟨hεc, hχ1⟩ := Gadd_sand p n hA3 hπs hν hZc
  have hEc := (((hξE.add hEδ).add hεφt).add hεs).add hεc
  obtain ⟨-, hχ2⟩ := Gadd_sand p n hA3 hπφ hψ ((Sand.refl hc4).add hEc)
  exact ⟨hEc, fun i => (hχ1 i).max (hχ2 i)⟩

/-- Step (4)'s convex bounds are in the class when their arguments are. -/
theorem logC4C_cvx (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (hs : Convex ℝ s) {D η : ℝ} (hD : 0 ≤ D) (hη : 0 ≤ η)
    {πφ ψ : ℝ → ℕ → ℝ} (hπφ : ∀ i, Cvx s fun l => πφ l i) (hψ : ∀ i, Cvx s fun l => ψ l i)
    {φb tb Em E δ b ξ : ℝ → ℝ} (hφb : Cvx s φb) (htb : Cvx s tb) (hEm : Cvx s Em) (hE : Cvx s E) (hδ : Cvx s δ)
    (hb : Cvx s b) (hξ : Cvx s ξ) (B : ℤ) :
    (Cvx s fun l => (logC4C p n D η (πφ l) (ψ l) (φb l) (tb l) (Em l) (E l) (δ l) (b l) (ξ l) B).1) ∧
      ∀ i, Cvx s fun l => (logC4C p n D η (πφ l) (ψ l) (φb l) (tb l) (Em l) (E l) (δ l) (b l) (ξ l) B).2 i := by
  have hZp := hφb.mul (htb.add hEm)
  have hεp := GmulEC_cvx p n hA3 hs hπφ hψ hZp
  have h2B : (0 : ℝ) ≤ 2 ^ (-B - 12) := by positivity
  have hεφt := (hεp.add (Cvx.const hs (mul_nonneg (Nat.cast_nonneg n) hη))).add
    ((hφb.max (htb.add hEm)).const_mul h2B)
  have hν := fun i => (GmulPC_cvx p n hA3 hs hπφ hψ hZp i).add (Cvx.const hs hη)
  have hbδ := hb.add hδ
  have hZs := (((hbδ.exp_sub_one_sub.const_mul (zero_le_two : (0 : ℝ) ≤ 2)).add
    (hbδ.exp.mul (hE.add hδ).exp_sub_one)).add hEm).add (Cvx.const hs hD)
  have hεs := GaddEC_cvx p n hA3 hs hπφ hψ hZs
  have hπs := fun i => GaddPC_cvx p n hA3 hs hπφ hψ hZs i
  have hEδ := (hE.exp.mul hδ.exp_sub_one).add
    ((((Cvx.const hs (zero_le_one : (0 : ℝ) ≤ 1)).add htb).add hEm).const_mul hD)
  have hξE := hξ.mul hEm
  have hZc := (((hE.exp_sub_one.add hξE).add hEδ).add hεφt).add hεs
  have hεc := GaddEC_cvx p n hA3 hs hπs hν hZc
  have hEc := (((hξE.add hEδ).add hεφt).add hεs).add hεc
  exact ⟨hEc, fun i => (GaddPC_cvx p n hA3 hs hπs hν hZc i).max
    (GaddPC_cvx p n hA3 hs hπφ hψ (hE.exp_sub_one.add hEc) i)⟩

/-- step (4)'s bounds for a case with the convex variants of `φ̄`, `G_ADDF` and Lemma 39's `(E_m, ψ_m)` and `t̄_m` -/
noncomputable def logCase4C (η₁ η₂ ηx ηp E : ℝ) (pos : Bool) (m : ℕ) (a b δ : ℝ) (π : ℕ → ℝ)
    (Fk : ℕ → ℕ → ℝ) (φF : ℕ → ℝ) (d' : ℕ) (πx : ℕ → ℝ) (B : ℤ) : ℝ × (ℕ → ℝ) :=
  logC4C p n (n * ηx) ηp
    (GaddfPC p n πx (logPhiBC (n * ηx) pos E a b δ + ∑ i ∈ Ico 1 n, πx i) (logPhiBC (n * ηx) pos E a b δ))
    (fun i => max ((coreBoundC p n η₁ η₂ pos m a b π Fk φF d').2 i) 0) (logPhiBC (n * ηx) pos E a b δ)
    (coreTC pos (coreBpC n m b η₁) m) (coreBoundC p n η₁ η₂ pos m a b π Fk φF d').1 E δ b
    (logXi (n * ηx) pos E a b δ) B

/-- Step (4)'s bounds for a case are nonnegative and at most their convex variants, where the convex `b'` is below
`d' + 2`. -/
theorem logCase4_sand (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {η₁ η₂ ηx ηp E : ℝ} (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂)
    (hηx : 0 ≤ ηx) (hηp : 0 ≤ ηp) (hE : 0 ≤ E) (pos : Bool) (e : ℤ) (m : ℕ) (a : ℝ) {b δ : ℝ} (hb : 0 ≤ b)
    (hδ : 0 ≤ δ) {π : ℕ → ℝ} (hπ : ∀ i, 0 ≤ π i) (Fk : ℕ → ℕ → ℝ) {φF : ℕ → ℝ} (hφF : ∀ k, 0 ≤ φF k) (d' : ℕ)
    {πx : ℕ → ℝ} (hπx : ∀ i, 0 ≤ πx i) (B : ℤ) (hbd : coreBpC n m b η₁ < d' + 2) :
    Sand (logCase4 p n η₁ η₂ ηx ηp E pos e m a b δ π Fk φF d' πx B).1
        (logCase4C p n η₁ η₂ ηx ηp E pos m a b δ π Fk φF d' πx B).1 ∧
      ∀ i, Sand ((logCase4 p n η₁ η₂ ηx ηp E pos e m a b δ π Fk φF d' πx B).2 i)
        ((logCase4C p n η₁ η₂ ηx ηp E pos m a b δ π Fk φF d' πx B).2 i) := by
  have hD : (0 : ℝ) ≤ n * ηx := mul_nonneg (Nat.cast_nonneg n) hηx
  have hφb := logPhiB_sand hD hE hb hδ pos a
  have hsum : Sand (∑ i ∈ Ico 1 n, πx i) (∑ i ∈ Ico 1 n, πx i) := Sand.refl (sum_nonneg fun i _ => hπx i)
  obtain ⟨-, hπφ⟩ := Gaddf_sand p n (fun i => Sand.refl (hπx i)) (hφb.add hsum) hφb
  obtain ⟨hEm, hψ0⟩ := coreBound_sand p n hA3 hη₁ hη₂ pos e m a (Sand.refl hb) (fun i => Sand.refl (hπ i)) Fk
    hφF d' hbd
  have hψ := fun i => (hψ0 i).max (Sand.refl (le_refl (0 : ℝ)))
  have htb := coreT_sand (coreBp_sand n e m (Sand.refl hb) hη₁) pos m
  exact logC4_sand p n hA3 hD hηp hπφ hψ hφb htb hEm hE hδ b (logXi_nonneg hD pos E a b δ) B

/-- Step (4)'s convex bounds for a fixed case are in the class as functions of `ℓ` when `E`, `b`, `δ`, `π` and
`π^x` are, where the convex `b'` is below `d' + 2`. -/
theorem logCase4C_cvx (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (hs : Convex ℝ s) {η₁ η₂ ηx ηp : ℝ} (hη₁ : 0 ≤ η₁)
    (hη₂ : 0 ≤ η₂) (hηx : 0 ≤ ηx) (hηp : 0 ≤ ηp) {E : ℝ → ℝ} (hE : Cvx s E) (pos : Bool) (m : ℕ) (a : ℝ)
    {b δ : ℝ → ℝ} (hb : Cvx s b) (hδ : Cvx s δ) {π : ℝ → ℕ → ℝ} (hπ : ∀ i, Cvx s fun l => π l i)
    (Fk : ℕ → ℕ → ℝ) {φF : ℕ → ℝ} (hφF : ∀ k, 0 ≤ φF k) (d' : ℕ) {πx : ℝ → ℕ → ℝ}
    (hπx : ∀ i, Cvx s fun l => πx l i) (B : ℤ) (hbd : ∀ l ∈ s, coreBpC n m (b l) η₁ < d' + 2) :
    (Cvx s fun l => (logCase4C p n η₁ η₂ ηx ηp (E l) pos m a (b l) (δ l) (π l) Fk φF d' (πx l) B).1) ∧
      ∀ i, Cvx s fun l => (logCase4C p n η₁ η₂ ηx ηp (E l) pos m a (b l) (δ l) (π l) Fk φF d' (πx l) B).2 i := by
  have hD : (0 : ℝ) ≤ n * ηx := mul_nonneg (Nat.cast_nonneg n) hηx
  have hφb := logPhiBC_cvx hs hD pos a hE hb hδ
  have hsum := Cvx.sum hs (Ico 1 n) fun i _ => hπx i
  have hπφ := fun i => GaddfPC_cvx p n hs hπx (hφb.add hsum) hφb i
  obtain ⟨hEm, hψ0⟩ := coreBoundC_cvx p n hA3 hs hη₁ hη₂ pos m a hb hπ Fk hφF d' hbd
  have hψ := fun i => (hψ0 i).max (Cvx.const hs (le_refl (0 : ℝ)))
  have htb := coreTC_cvx pos (coreBpC_cvx n hs m hb hη₁) m
  exact logC4C_cvx p n hA3 hs hD hηp hπφ hψ hφb htb hEm hE hδ hb (logXi_cvx hs hD pos a hE hb hδ) B

/-! ### Step (5) -/

/-- step (5)'s bounds with VecSum's second bound alone in Horner's rule and in each `G_MUL` and `G_ADDF` -/
noncomputable def logPC (η : ℝ) (χ : ℕ → ℝ) (C Ec : ℝ) (F' : ℕ → ℕ → ℝ) (φ' : ℕ → ℝ) (q : ℕ) (B : ℤ) :
    ℝ × (ℕ → ℝ) :=
  let H := hornerBC p n χ C 0 η F' φ' (logV C q) q (q - 2)
  let Zh := C * (logV C q 2 + H.1)
  let ωh := fun i => GmulPC p n χ H.2 Zh i + η
  let εh := GmulEC p n χ H.2 Zh + n * η
  let hb := Zh + εh
  let εg := GaddfEC p n ωh (1 + hb + ∑ j ∈ Ico 1 n, ωh j) (1 + hb)
  let ωg := GaddfPC p n ωh (1 + hb + ∑ j ∈ Ico 1 n, ωh j) (1 + hb)
  let Zr := C * (1 + hb + εg)
  (GmulEC p n χ ωg Zr + n * η + C * (εg + εh + C * H.1) +
      max (C ^ (q + 1) / (q + 1)) ((2 : ℝ) ^ (-B - 13) * C) / (1 - C) + Ec / (1 - C),
    fun i => max (GmulPC p n χ ωg Zr i + η) (χ i))

/-- Step (5)'s bounds are nonnegative and at most their convex variants at larger `χ`, `C` and `E_c`, where the
larger `C` is below one. -/
theorem logP_sand (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {η : ℝ} (hη : 0 ≤ η) {χ χ₁ : ℕ → ℝ}
    (hχ : ∀ i, Sand (χ i) (χ₁ i)) {C C₁ Ec Ec₁ : ℝ} (hC : Sand C C₁) (hC1 : C₁ < 1) (hEc : Sand Ec Ec₁)
    (F' : ℕ → ℕ → ℝ) {φ' : ℕ → ℝ} (hφ' : ∀ k, 0 ≤ φ' k) (q : ℕ) (B : ℤ) :
    Sand (logP p n η χ C Ec F' φ' q B).1 (logPC p n η χ₁ C₁ Ec₁ F' φ' q B).1 ∧
      ∀ i, Sand ((logP p n η χ C Ec F' φ' q B).2 i) ((logPC p n η χ₁ C₁ Ec₁ F' φ' q B).2 i) := by
  have hv : ∀ k, Sand (logV C q k) (logV C₁ q k) := fun k => logV_sand hC q k
  obtain ⟨hH1, hH2⟩ := hornerB_sand p n hA3 hχ hC (le_refl (0 : ℝ)) hη F' hφ' hv q (q - 2)
  have hZh := hC.mul ((hv 2).add hH1)
  obtain ⟨hεh0, hωh0⟩ := Gmul_sand p n hA3 hχ hH2 hZh
  have hnη := Sand.refl (mul_nonneg (Nat.cast_nonneg n) hη)
  have hωh := fun i => (hωh0 i).add (Sand.refl hη)
  have hεh := hεh0.add hnη
  have hhb := hZh.add hεh
  have h1 := Sand.refl (zero_le_one : (0 : ℝ) ≤ 1)
  have hsum := Sand.sum (Ico 1 n) fun j _ => hωh j
  obtain ⟨hεg, hωg⟩ := Gaddf_sand p n hωh ((h1.add hhb).add hsum) (h1.add hhb)
  have hZr := hC.mul ((h1.add hhb).add hεg)
  obtain ⟨hεr, hωr⟩ := Gmul_sand p n hA3 hχ hωg hZr
  have hq1 : (0 : ℝ) ≤ q + 1 := by positivity
  have h2B : (0 : ℝ) ≤ 2 ^ (-B - 13) := by positivity
  exact ⟨(((hεr.add hnη).add (hC.mul ((hεg.add hεh).add (hC.mul hH1)))).add
      ((((hC.pow (q + 1)).div_const hq1).max (hC.const_mul h2B)).div_one_sub hC hC1)).add
      (hEc.div_one_sub hC hC1), fun i => ((hωr i).add (Sand.refl hη)).max (hχ i)⟩

/-- Step (5)'s convex bounds are in the class when `χ`, `C` and `E_c` are, where `C < 1`. -/
theorem logPC_cvx (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (hs : Convex ℝ s) {η : ℝ} (hη : 0 ≤ η) {χ : ℝ → ℕ → ℝ}
    (hχ : ∀ i, Cvx s fun l => χ l i) {C Ec : ℝ → ℝ} (hC : Cvx s C) (hC1 : ∀ l ∈ s, C l < 1) (hEc : Cvx s Ec)
    (F' : ℕ → ℕ → ℝ) {φ' : ℕ → ℝ} (hφ' : ∀ k, 0 ≤ φ' k) (q : ℕ) (B : ℤ) :
    (Cvx s fun l => (logPC p n η (χ l) (C l) (Ec l) F' φ' q B).1) ∧
      ∀ i, Cvx s fun l => (logPC p n η (χ l) (C l) (Ec l) F' φ' q B).2 i := by
  have hv := fun k => logV_cvx hC q k
  obtain ⟨hH1, hH2⟩ := hornerBC_cvx p n hA3 hs hχ hC (le_refl (0 : ℝ)) hη F' hφ' hv q (q - 2)
  have hZh := hC.mul ((hv 2).add hH1)
  have hnη := Cvx.const hs (mul_nonneg (Nat.cast_nonneg n) hη)
  have hωh := fun i => (GmulPC_cvx p n hA3 hs hχ hH2 hZh i).add (Cvx.const hs hη)
  have hεh := (GmulEC_cvx p n hA3 hs hχ hH2 hZh).add hnη
  have hhb := hZh.add hεh
  have h1 := Cvx.const hs (zero_le_one : (0 : ℝ) ≤ 1)
  have hsum := Cvx.sum hs (Ico 1 n) fun j _ => hωh j
  have hεg := GaddfEC_cvx p n hs hωh ((h1.add hhb).add hsum) (h1.add hhb)
  have hωg := fun i => GaddfPC_cvx p n hs hωh ((h1.add hhb).add hsum) (h1.add hhb) i
  have hZr := hC.mul ((h1.add hhb).add hεg)
  have hεr := GmulEC_cvx p n hA3 hs hχ hωg hZr
  have hq1 : (0 : ℝ) ≤ q + 1 := by positivity
  have h2B : (0 : ℝ) ≤ 2 ^ (-B - 13) := by positivity
  exact ⟨(((hεr.add hnη).add (hC.mul ((hεg.add hεh).add (hC.mul hH1)))).add
      ((((hC.pow (q + 1)).div_const hq1).max (hC.const_mul h2B)).div_one_sub hC hC1)).add
      (hEc.div_one_sub hC hC1),
    fun i => ((GmulPC_cvx p n hA3 hs hχ hωg hZr i).add (Cvx.const hs hη)).max (hχ i)⟩

/-! ### The bound `𝓔(ℓ)` -/

/-- `𝓔(ℓ)` of a case with the four changes of the paragraph "Convexity"; the exponent `e` no longer enters -/
noncomputable def logBoundC (η₁ η₂ ηx ηp ηc ℓ E : ℝ) (πy : ℕ → ℝ) (pos : Bool) (m : ℕ) (a b δ : ℝ)
    (π : ℕ → ℝ) (Fk : ℕ → ℕ → ℝ) (φF : ℕ → ℝ) (d' : ℕ) (πx : ℕ → ℝ) (F' : ℕ → ℕ → ℝ) (φ' : ℕ → ℝ) (q : ℕ)
    (B : ℤ) : ℝ :=
  let c4 := logCase4C p n η₁ η₂ ηx ηp E pos m a b δ π Fk φF d' πx B
  let P := logPC p n ηc c4.2 (Real.exp E - 1 + c4.1) c4.1 F' φ' q B
  GaddEC p n πy P.2 (ℓ + P.1) + P.1

/-- Theorem 42's proof (`thm:log`), "Convexity": the bound `𝓔(ℓ)` of `thm42_case` is nonnegative and at most its
convex variant at the same arguments, where the convex `b'` is below `d' + 2` and the convex `C` below one. -/
theorem logBound_sand (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {η₁ η₂ ηx ηp ηc ℓ E : ℝ} (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂)
    (hηx : 0 ≤ ηx) (hηp : 0 ≤ ηp) (hηc : 0 ≤ ηc) (hℓ : 0 ≤ ℓ) (hE : 0 ≤ E) {πy : ℕ → ℝ} (hπy : ∀ i, 0 ≤ πy i)
    (pos : Bool) (e : ℤ) (m : ℕ) (a : ℝ) {b δ : ℝ} (hb : 0 ≤ b) (hδ : 0 ≤ δ) {π : ℕ → ℝ} (hπ : ∀ i, 0 ≤ π i)
    (Fk : ℕ → ℕ → ℝ) {φF : ℕ → ℝ} (hφF : ∀ k, 0 ≤ φF k) (d' : ℕ) {πx : ℕ → ℝ} (hπx : ∀ i, 0 ≤ πx i)
    (F' : ℕ → ℕ → ℝ) {φ' : ℕ → ℝ} (hφ' : ∀ k, 0 ≤ φ' k) (q : ℕ) (B : ℤ) (hbd : coreBpC n m b η₁ < d' + 2)
    (hC : Real.exp E - 1 + (logCase4C p n η₁ η₂ ηx ηp E pos m a b δ π Fk φF d' πx B).1 < 1) :
    Sand (logBound p n η₁ η₂ ηx ηp ηc ℓ E πy pos e m a b δ π Fk φF d' πx F' φ' q B)
      (logBoundC p n η₁ η₂ ηx ηp ηc ℓ E πy pos m a b δ π Fk φF d' πx F' φ' q B) := by
  obtain ⟨hEc, hχ⟩ := logCase4_sand p n hA3 hη₁ hη₂ hηx hηp hE pos e m a hb hδ hπ Fk hφF d' hπx B hbd
  have hc4 : (0 : ℝ) ≤ Real.exp E - 1 := by
    have := Real.one_le_exp hE
    linarith
  obtain ⟨hP1, hP2⟩ := logP_sand p n hA3 hηc hχ ((Sand.refl hc4).add hEc) hC hEc F' hφ' q B
  obtain ⟨hεy, -⟩ := Gadd_sand p n hA3 (fun i => Sand.refl (hπy i)) hP2 ((Sand.refl hℓ).add hP1)
  exact hεy.add hP1

/-- Theorem 42's proof (`thm:log`), "Convexity": for a fixed case the convex `𝓔` is nonnegative, nondecreasing and
convex in `ℓ ≥ 0` when `E`, `b`, `δ` and the part bounds `π`, `π^y` and `π^x` are, where `b' < d' + 2` and
`C < 1`. -/
theorem logBoundC_cvx (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) (hs : Convex ℝ s) (h0 : ∀ l ∈ s, 0 ≤ l)
    {η₁ η₂ ηx ηp ηc : ℝ} (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂) (hηx : 0 ≤ ηx) (hηp : 0 ≤ ηp) (hηc : 0 ≤ ηc)
    {E : ℝ → ℝ} (hE : Cvx s E) {πy : ℝ → ℕ → ℝ} (hπy : ∀ i, Cvx s fun l => πy l i) (pos : Bool) (m : ℕ) (a : ℝ)
    {b δ : ℝ → ℝ} (hb : Cvx s b) (hδ : Cvx s δ) {π : ℝ → ℕ → ℝ} (hπ : ∀ i, Cvx s fun l => π l i)
    (Fk : ℕ → ℕ → ℝ) {φF : ℕ → ℝ} (hφF : ∀ k, 0 ≤ φF k) (d' : ℕ) {πx : ℝ → ℕ → ℝ}
    (hπx : ∀ i, Cvx s fun l => πx l i) (F' : ℕ → ℕ → ℝ) {φ' : ℕ → ℝ} (hφ' : ∀ k, 0 ≤ φ' k) (q : ℕ) (B : ℤ)
    (hbd : ∀ l ∈ s, coreBpC n m (b l) η₁ < d' + 2)
    (hC : ∀ l ∈ s, Real.exp (E l) - 1 +
      (logCase4C p n η₁ η₂ ηx ηp (E l) pos m a (b l) (δ l) (π l) Fk φF d' (πx l) B).1 < 1) :
    Cvx s fun l =>
      logBoundC p n η₁ η₂ ηx ηp ηc l (E l) (πy l) pos m a (b l) (δ l) (π l) Fk φF d' (πx l) F' φ' q B := by
  obtain ⟨hEc, hχ⟩ := logCase4C_cvx p n hA3 hs hη₁ hη₂ hηx hηp hE pos m a hb hδ hπ Fk hφF d' hπx B hbd
  obtain ⟨hP1, hP2⟩ := logPC_cvx p n hA3 hs hηc hχ (hE.exp_sub_one.add hEc) hC hEc F' hφ' q B
  exact (GaddEC_cvx p n hA3 hs hπy hP2 ((Cvx.id hs h0).add hP1)).add hP1

/-- `logBoundC_cvx` on an interval `[ℓ₁, ℓ₂]` of nonnegative `ℓ`, with `b' < d' + 2` and `C < 1` asked at `ℓ₂`
only: both grow with `ℓ`. -/
theorem logBoundC_cvx_Icc (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {l₁ l₂ : ℝ} (h0 : 0 ≤ l₁) (h12 : l₁ ≤ l₂)
    {η₁ η₂ ηx ηp ηc : ℝ} (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂) (hηx : 0 ≤ ηx) (hηp : 0 ≤ ηp) (hηc : 0 ≤ ηc)
    {E : ℝ → ℝ} (hE : Cvx (Icc l₁ l₂) E) {πy : ℝ → ℕ → ℝ} (hπy : ∀ i, Cvx (Icc l₁ l₂) fun l => πy l i)
    (pos : Bool) (m : ℕ) (a : ℝ) {b δ : ℝ → ℝ} (hb : Cvx (Icc l₁ l₂) b) (hδ : Cvx (Icc l₁ l₂) δ)
    {π : ℝ → ℕ → ℝ} (hπ : ∀ i, Cvx (Icc l₁ l₂) fun l => π l i) (Fk : ℕ → ℕ → ℝ) {φF : ℕ → ℝ}
    (hφF : ∀ k, 0 ≤ φF k) (d' : ℕ) {πx : ℝ → ℕ → ℝ} (hπx : ∀ i, Cvx (Icc l₁ l₂) fun l => πx l i)
    (F' : ℕ → ℕ → ℝ) {φ' : ℕ → ℝ} (hφ' : ∀ k, 0 ≤ φ' k) (q : ℕ) (B : ℤ)
    (hbd : coreBpC n m (b l₂) η₁ < d' + 2)
    (hC : Real.exp (E l₂) - 1 +
      (logCase4C p n η₁ η₂ ηx ηp (E l₂) pos m a (b l₂) (δ l₂) (π l₂) Fk φF d' (πx l₂) B).1 < 1) :
    Cvx (Icc l₁ l₂) fun l =>
      logBoundC p n η₁ η₂ ηx ηp ηc l (E l) (πy l) pos m a (b l) (δ l) (π l) Fk φF d' (πx l) F' φ' q B := by
  have hs : Convex ℝ (Icc l₁ l₂) := convex_Icc l₁ l₂
  have hr : l₂ ∈ Icc l₁ l₂ := right_mem_Icc.mpr h12
  have hbd' : ∀ l ∈ Icc l₁ l₂, coreBpC n m (b l) η₁ < d' + 2 := fun l hl =>
    ((coreBpC_cvx n hs m hb hη₁).mono hl hr hl.2).trans_lt hbd
  obtain ⟨hEc, -⟩ := logCase4C_cvx p n hA3 hs hη₁ hη₂ hηx hηp hE pos m a hb hδ hπ Fk hφF d' hπx B hbd'
  have hC' := fun l (hl : l ∈ Icc l₁ l₂) => ((hE.exp_sub_one.add hEc).mono hl hr hl.2).trans_lt hC
  exact logBoundC_cvx p n hA3 hs (fun l hl => h0.trans hl.1) hη₁ hη₂ hηx hηp hηc hE hπy pos m a hb hδ hπ Fk hφF
    d' hπx F' hφ' q B hbd' hC'

end ExpansionBounds
