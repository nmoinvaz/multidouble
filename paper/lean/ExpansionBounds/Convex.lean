import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

/-!
# Nonnegative, nondecreasing, convex functions and their chords

The paragraph "Convexity" of Theorem 42's proof (`thm:log`): for a fixed case the bound `𝓔(ℓ)` is built from `ℓ` by
sums with nonnegative coefficients, products, maxima, and `z ↦ e^z`, `z ↦ e^z - 1 - z`, `z ↦ z^{q+1}/(1 - z)` and
`z ↦ 1/(1 - z)` for `z < 1`. `Cvx s f` says that `f` is nonnegative, nondecreasing and convex on `s`; the class is
closed under each of these (`Cvx.add`, `Cvx.const_mul`, `Cvx.mul`, `Cvx.max`, `Cvx.exp`, `Cvx.exp_sub_one_sub`,
`Cvx.pow_div_one_sub`, `Cvx.one_div_one_sub`). A convex function lies below its chord (`chord_affine`), which gives
the paper's two bounds: `𝓔(ℓ)/ℓ ≤ max(𝓔(ℓ₁)/ℓ₁, 𝓔(ℓ₂)/ℓ₂)` on `[ℓ₁, ℓ₂]` with `ℓ₁ > 0` (`chord_ratio`) and
`𝓔(ℓ) ≤ 𝓔(0) + ℓ(𝓔(ℓ₂) - 𝓔(0))/ℓ₂` on `[0, ℓ₂]` (`chord_zero`).
-/

namespace ExpansionBounds

open Set

/-- `f` is nonnegative, nondecreasing and convex on `s`: the class of Theorem 42's bounds as functions of `ℓ`. -/
structure Cvx (s : Set ℝ) (f : ℝ → ℝ) : Prop where
  /-- `f ≥ 0` on `s` -/
  nonneg : ∀ x ∈ s, 0 ≤ f x
  /-- `f` is nondecreasing on `s` -/
  mono : MonotoneOn f s
  /-- `f` is convex on `s`, a convex set -/
  convex : ConvexOn ℝ s f

/-- A nondecreasing convex `g` after a nondecreasing convex `f` that maps `s` into `g`'s domain is convex. -/
theorem convexOn_comp_mapsTo {s t : Set ℝ} {f g : ℝ → ℝ} (hgm : MonotoneOn g t) (hgc : ConvexOn ℝ t g)
    (hfc : ConvexOn ℝ s f) (hst : MapsTo f s t) : ConvexOn ℝ s fun x => g (f x) := by
  refine ⟨hfc.1, fun x hx y hy a b ha hb hab => ?_⟩
  have h1 := hfc.2 hx hy ha hb hab
  have hm : a • x + b • y ∈ s := hfc.1 hx hy ha hb hab
  have h2 : a • f x + b • f y ∈ t := hgc.1 (hst hx) (hst hy) ha hb hab
  exact (hgm (hst hm) h2 h1).trans (hgc.2 (hst hx) (hst hy) ha hb hab)

namespace Cvx

variable {s t : Set ℝ} {f g : ℝ → ℝ}

/-! ### Constants, the identity, restriction -/

/-- A nonnegative constant is in the class. -/
theorem const (hs : Convex ℝ s) {c : ℝ} (hc : 0 ≤ c) : Cvx s fun _ => c :=
  ⟨fun _ _ => hc, monotoneOn_const, convexOn_const c hs⟩

/-- `ℓ` itself is in the class on a convex set of nonnegative numbers. -/
theorem id (hs : Convex ℝ s) (h0 : ∀ x ∈ s, 0 ≤ x) : Cvx s fun x => x :=
  ⟨h0, fun _ _ _ _ h => h, convexOn_id hs⟩

/-- The class on `t` restricts to a convex subset. -/
theorem subset (h : Cvx t f) (hst : s ⊆ t) (hs : Convex ℝ s) : Cvx s f :=
  ⟨fun x hx => h.nonneg x (hst hx), h.mono.mono hst, h.convex.subset hst hs⟩

/-- A function equal on `s` to one of the class is in the class. -/
theorem congr (h : Cvx s f) (hfg : ∀ x ∈ s, g x = f x) : Cvx s g :=
  ⟨fun x hx => (hfg x hx).symm ▸ h.nonneg x hx, h.mono.congr fun x hx => (hfg x hx).symm,
    h.convex.congr fun x hx => (hfg x hx).symm⟩

/-! ### Sums with nonnegative coefficients, products, maxima -/

/-- The class is closed under sums. -/
theorem add (hf : Cvx s f) (hg : Cvx s g) : Cvx s fun x => f x + g x :=
  ⟨fun x hx => add_nonneg (hf.nonneg x hx) (hg.nonneg x hx), hf.mono.add hg.mono, hf.convex.add hg.convex⟩

/-- The class is closed under multiplication by a nonnegative constant. -/
theorem const_mul (hf : Cvx s f) {c : ℝ} (hc : 0 ≤ c) : Cvx s fun x => c * f x :=
  ⟨fun x hx => mul_nonneg hc (hf.nonneg x hx),
    fun _ hx _ hy hxy => mul_le_mul_of_nonneg_left (hf.mono hx hy hxy) hc, hf.convex.smul hc⟩

/-- The class is closed under multiplication by a nonnegative constant on the right. -/
theorem mul_const (hf : Cvx s f) {c : ℝ} (hc : 0 ≤ c) : Cvx s fun x => f x * c :=
  (hf.const_mul hc).congr fun x _ => mul_comm (f x) c

/-- The class is closed under division by a nonnegative constant. -/
theorem div_const (hf : Cvx s f) {c : ℝ} (hc : 0 ≤ c) : Cvx s fun x => f x / c :=
  (hf.mul_const (inv_nonneg.mpr hc)).congr fun x _ => div_eq_mul_inv (f x) c

/-- The class is closed under finite sums. -/
theorem sum {ι : Type*} (hs : Convex ℝ s) (I : Finset ι) {F : ι → ℝ → ℝ} (h : ∀ i ∈ I, Cvx s (F i)) :
    Cvx s fun x => ∑ i ∈ I, F i x := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using const hs le_rfl
  | insert i I hi ih =>
    have h1 := (h i (Finset.mem_insert_self i I)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    exact h1.congr fun x _ => Finset.sum_insert hi

/-- The product of two nonnegative, nondecreasing, convex functions is one. -/
theorem mul (hf : Cvx s f) (hg : Cvx s g) : Cvx s fun x => f x * g x :=
  ⟨fun x hx => mul_nonneg (hf.nonneg x hx) (hg.nonneg x hx),
    fun x hx y hy hxy => mul_le_mul (hf.mono hx hy hxy) (hg.mono hx hy hxy) (hg.nonneg x hx) (hf.nonneg y hy),
    hf.convex.mul hg.convex (fun x hx => hf.nonneg x hx) (fun x hx => hg.nonneg x hx)
      (hf.mono.monovaryOn hg.mono)⟩

/-- The class is closed under powers. -/
theorem pow (hf : Cvx s f) : ∀ k : ℕ, Cvx s fun x => f x ^ k
  | 0 => (const hf.convex.1 zero_le_one).congr fun x _ => pow_zero (f x)
  | k + 1 => ((hf.pow k).mul hf).congr fun x _ => pow_succ (f x) k

/-- The maximum of a nondecreasing convex function and one of the class is in the class: `max(ξ - 1, ·)`. -/
theorem max_left (hfm : MonotoneOn f s) (hfc : ConvexOn ℝ s f) (hg : Cvx s g) : Cvx s fun x => max (f x) (g x) :=
  ⟨fun x hx => le_max_of_le_right (hg.nonneg x hx),
    fun _ hx _ hy hxy => max_le_max (hfm hx hy hxy) (hg.mono hx hy hxy), hfc.sup hg.convex⟩

/-- The class is closed under maxima. -/
theorem max (hf : Cvx s f) (hg : Cvx s g) : Cvx s fun x => max (f x) (g x) :=
  max_left hf.mono hf.convex hg

/-! ### Composition -/

/-- A function of the class on `t` after a nondecreasing convex one that maps `s` into `t` is in the class. -/
theorem comp_of (hg : Cvx t g) (hfm : MonotoneOn f s) (hfc : ConvexOn ℝ s f) (hst : MapsTo f s t) :
    Cvx s fun x => g (f x) :=
  ⟨fun _ hx => hg.nonneg _ (hst hx), fun _ hx _ hy hxy => hg.mono (hst hx) (hst hy) (hfm hx hy hxy),
    convexOn_comp_mapsTo hg.mono hg.convex hfc hst⟩

/-- The class is closed under composition. -/
theorem comp (hg : Cvx t g) (hf : Cvx s f) (hst : MapsTo f s t) : Cvx s fun x => g (f x) :=
  hg.comp_of hf.mono hf.convex hst

end Cvx

/-! ### The four functions of the paper -/

/-- `e^z` is in the class on the line. -/
theorem cvx_exp : Cvx univ Real.exp :=
  ⟨fun _ _ => (Real.exp_pos _).le, Real.exp_monotone.monotoneOn _, convexOn_exp⟩

/-- `e^z - 1` is in the class on `z ≥ 0`. -/
theorem cvx_exp_sub_one : Cvx (Ici 0) fun z => Real.exp z - 1 := by
  refine ⟨fun z hz => ?_, fun x _ y _ hxy => ?_, convex_Ici 0, fun x _ y _ a b ha hb hab => ?_⟩
  · have := Real.one_le_exp (mem_Ici.mp hz)
    linarith
  · have := Real.exp_le_exp.mpr hxy
    linarith
  · have h := convexOn_exp.2 (mem_univ x) (mem_univ y) ha hb hab
    simp only [smul_eq_mul] at h ⊢
    linarith

/-- `e^z - 1 - z` is in the class on `z ≥ 0`. -/
theorem cvx_exp_sub_one_sub : Cvx (Ici 0) fun z => Real.exp z - 1 - z := by
  refine ⟨fun z _ => ?_, fun x hx y _ hxy => ?_, convex_Ici 0, fun x _ y _ a b ha hb hab => ?_⟩
  · have := Real.add_one_le_exp z
    linarith
  · have h1 : y - x + 1 ≤ Real.exp (y - x) := Real.add_one_le_exp _
    have h2 : 1 ≤ Real.exp x := Real.one_le_exp (mem_Ici.mp hx)
    have h3 : Real.exp y = Real.exp x * Real.exp (y - x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h4 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos x).le
    have h5 := mul_le_mul_of_nonneg_right h2 (sub_nonneg.mpr hxy)
    linarith
  · have h := convexOn_exp.2 (mem_univ x) (mem_univ y) ha hb hab
    simp only [smul_eq_mul] at h ⊢
    linarith

/-- `1/(aX + bY) ≤ a/X + b/Y` for positive `X`, `Y` and weights `a + b = 1`: the difference is
`ab(X - Y)²/(XY(aX + bY))`. -/
theorem one_div_combo_le {X Y a b : ℝ} (hX : 0 < X) (hY : 0 < Y) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    1 / (a * X + b * Y) ≤ a * (1 / X) + b * (1 / Y) := by
  obtain rfl : b = 1 - a := by linarith
  have hD : 0 < a * X + (1 - a) * Y := by
    rcases ha.eq_or_lt with h | h
    · subst h
      simpa using hY
    · have := mul_pos h hX
      have := mul_nonneg hb hY.le
      linarith
  have key : a * (1 / X) + (1 - a) * (1 / Y) - 1 / (a * X + (1 - a) * Y)
      = a * (1 - a) * (X - Y) ^ 2 / (X * Y * (a * X + (1 - a) * Y)) := by
    field_simp
    ring
  have h0 : 0 ≤ a * (1 - a) * (X - Y) ^ 2 / (X * Y * (a * X + (1 - a) * Y)) :=
    div_nonneg (mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)) (mul_pos (mul_pos hX hY) hD).le
  linarith

/-- `1/(1 - z)` is in the class on `z < 1`. -/
theorem cvx_one_div_one_sub : Cvx (Iio 1) fun z => 1 / (1 - z) := by
  refine ⟨fun z hz => ?_, fun x _ y hy hxy => ?_, convex_Iio 1, fun x hx y hy a b ha hb hab => ?_⟩
  · exact (one_div_pos.mpr (sub_pos.mpr (mem_Iio.mp hz))).le
  · exact one_div_le_one_div_of_le (sub_pos.mpr (mem_Iio.mp hy)) (by linarith)
  · have h := one_div_combo_le (sub_pos.mpr (mem_Iio.mp hx)) (sub_pos.mpr (mem_Iio.mp hy)) ha hb hab
    have e : 1 - (a * x + b * y) = a * (1 - x) + b * (1 - y) := by
      calc 1 - (a * x + b * y) = (a + b) - (a * x + b * y) := by rw [hab]
        _ = _ := by ring
    simp only [smul_eq_mul]
    rw [e]
    exact h

namespace Cvx

variable {s : Set ℝ} {f g : ℝ → ℝ}

/-- `e^f` is in the class for a nondecreasing convex `f` of any sign: `e^{E + δ - a}`. -/
theorem exp_of (hfm : MonotoneOn f s) (hfc : ConvexOn ℝ s f) : Cvx s fun x => Real.exp (f x) :=
  cvx_exp.comp_of hfm hfc fun _ _ => mem_univ _

/-- `e^f` is in the class. -/
theorem exp (hf : Cvx s f) : Cvx s fun x => Real.exp (f x) :=
  exp_of hf.mono hf.convex

/-- `e^f - 1` is in the class. -/
theorem exp_sub_one (hf : Cvx s f) : Cvx s fun x => Real.exp (f x) - 1 :=
  cvx_exp_sub_one.comp hf fun x hx => hf.nonneg x hx

/-- `e^f - 1 - f` is in the class. -/
theorem exp_sub_one_sub (hf : Cvx s f) : Cvx s fun x => Real.exp (f x) - 1 - f x :=
  cvx_exp_sub_one_sub.comp hf fun x hx => hf.nonneg x hx

/-- `1/(1 - f)` is in the class where `f < 1`. -/
theorem one_div_one_sub (hf : Cvx s f) (h1 : ∀ x ∈ s, f x < 1) : Cvx s fun x => 1 / (1 - f x) :=
  cvx_one_div_one_sub.comp hf fun x hx => h1 x hx

/-- `g/(1 - f)` is in the class where `f < 1`: `E_c/(1 - C)`. -/
theorem div_one_sub (hg : Cvx s g) (hf : Cvx s f) (h1 : ∀ x ∈ s, f x < 1) : Cvx s fun x => g x / (1 - f x) :=
  (hg.mul (hf.one_div_one_sub h1)).congr fun x _ => div_eq_mul_one_div (g x) (1 - f x)

/-- `f^k/(1 - f)` is in the class where `f < 1`: `C^{q+1}/(1 - C)`. -/
theorem pow_div_one_sub (hf : Cvx s f) (h1 : ∀ x ∈ s, f x < 1) (k : ℕ) : Cvx s fun x => f x ^ k / (1 - f x) :=
  (hf.pow k).div_one_sub hf h1

/-- A function given by cases on a proposition that does not depend on `ℓ` is in the class when each case is. -/
theorem ite (c : Prop) [Decidable c] (hf : c → Cvx s f) (hg : ¬c → Cvx s g) :
    Cvx s fun x => if c then f x else g x := by
  by_cases h : c
  · simpa only [h, ↓reduceIte] using hf h
  · simpa only [h, ↓reduceIte] using hg h

/-- `a + bℓ` with `a, b ≥ 0` is in the class on a convex set of nonnegative numbers: `E(ℓ)` and `ȳ = ℓ + E(ℓ)`. -/
theorem affine (hs : Convex ℝ s) (h0 : ∀ x ∈ s, 0 ≤ x) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Cvx s fun x => a + b * x :=
  (const hs ha).add ((id hs h0).const_mul hb)

/-- A function of the class on `[0, 1]` is nonnegative at `0` and no larger there than at `1`. -/
theorem zero_le_one {F : ℝ → ℝ} (h : Cvx (Icc 0 1) F) : 0 ≤ F 0 ∧ F 0 ≤ F 1 :=
  ⟨h.nonneg 0 (left_mem_Icc.mpr _root_.zero_le_one),
    h.mono (left_mem_Icc.mpr _root_.zero_le_one) (right_mem_Icc.mpr _root_.zero_le_one) _root_.zero_le_one⟩

end Cvx

/-- The segment from `a ≥ 0` up to `b ≥ a` is in the class on `[0, 1]`. With `Cvx.zero_le_one`, a bound built from its
arguments by the operations of the class is nonnegative and grows with them, which the rounding up of a rational
mirror needs. -/
theorem cvx_segment {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : Cvx (Icc 0 1) fun t => a + (b - a) * t :=
  Cvx.affine (convex_Icc 0 1) (fun _ h => h.1) ha (sub_nonneg.mpr hab)

/-! ### Chords -/

/-- A convex function that is below an affine one at both ends of an interval is below it on the interval. Values
rounded up at the ends keep the chord above the function. -/
theorem chord_affine {f : ℝ → ℝ} {l₁ l₂ α β : ℝ} (hf : ConvexOn ℝ (Icc l₁ l₂) f) (h₁ : f l₁ ≤ α + β * l₁)
    (h₂ : f l₂ ≤ α + β * l₂) {l : ℝ} (hl : l ∈ Icc l₁ l₂) : f l ≤ α + β * l := by
  have h12 : l₁ ≤ l₂ := hl.1.trans hl.2
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := (Convex.mem_Icc h12).mp hl
  have hc := hf.2 (left_mem_Icc.mpr h12) (right_mem_Icc.mpr h12) ha hb hab
  simp only [smul_eq_mul] at hc
  have e1 := mul_le_mul_of_nonneg_left h₁ ha
  have e2 := mul_le_mul_of_nonneg_left h₂ hb
  have e3 : a * (α + β * l₁) + b * (α + β * l₂) = α + β * (a * l₁ + b * l₂) := by
    calc a * (α + β * l₁) + b * (α + β * l₂) = (a + b) * α + β * (a * l₁ + b * l₂) := by ring
      _ = _ := by rw [hab, one_mul]
  linarith

/-- Theorem 42's proof, the first chord: for `𝓔` convex on `[ℓ₁, ℓ₂]` with `ℓ₁ > 0`,
`𝓔(ℓ)/ℓ ≤ max(𝓔(ℓ₁)/ℓ₁, 𝓔(ℓ₂)/ℓ₂)`. -/
theorem chord_ratio {f : ℝ → ℝ} {l₁ l₂ : ℝ} (hf : ConvexOn ℝ (Icc l₁ l₂) f) (h0 : 0 < l₁) {l : ℝ}
    (hl : l ∈ Icc l₁ l₂) : f l / l ≤ max (f l₁ / l₁) (f l₂ / l₂) := by
  have h2 : 0 < l₂ := h0.trans_le (hl.1.trans hl.2)
  have e1 : f l₁ ≤ 0 + max (f l₁ / l₁) (f l₂ / l₂) * l₁ := by
    rw [zero_add, ← div_le_iff₀ h0]
    exact le_max_left _ _
  have e2 : f l₂ ≤ 0 + max (f l₁ / l₁) (f l₂ / l₂) * l₂ := by
    rw [zero_add, ← div_le_iff₀ h2]
    exact le_max_right _ _
  have h := chord_affine hf e1 e2 hl
  rw [zero_add] at h
  exact (div_le_iff₀ (h0.trans_le hl.1)).mpr h

/-- Theorem 42's proof, the second chord: for `𝓔` convex on `[0, ℓ₂]`,
`𝓔(ℓ) ≤ 𝓔(0) + ℓ(𝓔(ℓ₂) - 𝓔(0))/ℓ₂`. -/
theorem chord_zero {f : ℝ → ℝ} {l₂ : ℝ} (hf : ConvexOn ℝ (Icc 0 l₂) f) (h0 : 0 < l₂) {l : ℝ}
    (hl : l ∈ Icc 0 l₂) : f l ≤ f 0 + l * ((f l₂ - f 0) / l₂) := by
  have e1 : f 0 ≤ f 0 + (f l₂ - f 0) / l₂ * 0 := by rw [mul_zero, add_zero]
  have e2 : f l₂ ≤ f 0 + (f l₂ - f 0) / l₂ * l₂ := by
    rw [div_mul_cancel₀ _ h0.ne']
    linarith
  have h := chord_affine hf e1 e2 hl
  rw [mul_comm] at h
  exact h

/-- The form Theorem 42 takes from the first chord: `𝓔 ≤ εℓ` at both ends of `[ℓ₁, ℓ₂]` gives it on the interval,
whatever the sign of `ℓ₁`. -/
theorem chord_le_mul {f : ℝ → ℝ} {l₁ l₂ ε : ℝ} (hf : ConvexOn ℝ (Icc l₁ l₂) f) (h₁ : f l₁ ≤ ε * l₁)
    (h₂ : f l₂ ≤ ε * l₂) {l : ℝ} (hl : l ∈ Icc l₁ l₂) : f l ≤ ε * l := by
  have h := chord_affine (α := 0) (β := ε) hf (by linarith) (by linarith) hl
  linarith

/-- The form Theorem 42 takes from the second chord: `𝓔(0) ≤ Φ` and `𝓔(ℓ₂) ≤ εℓ₂ + Φ` give
`𝓔(ℓ) ≤ εℓ + Φ` on `[0, ℓ₂]`. -/
theorem chord_le_mul_add {f : ℝ → ℝ} {l₂ ε Φ : ℝ} (hf : ConvexOn ℝ (Icc 0 l₂) f) (h₁ : f 0 ≤ Φ)
    (h₂ : f l₂ ≤ ε * l₂ + Φ) {l : ℝ} (hl : l ∈ Icc 0 l₂) : f l ≤ ε * l + Φ := by
  have h := chord_affine (α := Φ) (β := ε) hf (by linarith) (by linarith) hl
  linarith

end ExpansionBounds
