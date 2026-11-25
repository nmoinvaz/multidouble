import ExpansionBounds.Div
import ExpansionBounds.Eval

/-!
# `κ_DIV` in rational arithmetic

The mirrors over `ℚ` of the recursion that defines `κ_DIV` (Theorem 19): SMF's level bounds, the minimum of Theorem
9 (b)'s bounds over `k`, the remainders' part bounds `P^{(k)}`, `Θ` and `Ξ`. `cast_kdiv` shows that `kdivQ`, cast to
`ℝ`, is `κ_DIV`, so the kernel can evaluate it at any `n`.
-/

namespace ExpansionBounds

open Finset

section Mirrors

variable (uq : ℚ) (n : ℕ) (ρ : ℚ)

/-- `G_i`, the bounds on `|r_i - p_i|` -/
def divGQ (P : ℕ → ℚ) (qb : ℚ) (i : ℕ) : ℚ :=
  if i = 0 then uq * (P 0 + qb) else P i + (1 + uq) * ρ ^ i * qb

/-- SMF's `A_m` -/
def divAQ (P : ℕ → ℚ) (qb : ℚ) (m : ℕ) : ℚ :=
  if m < n then
    (1 + uq) * divGQ uq ρ P qb m + (if m = 0 then 0 else uq * divGQ uq ρ P qb (m - 1) + uq * ρ ^ (m - 1) * qb)
  else if m = n then uq * divGQ uq ρ P qb (n - 1) + uq * ρ ^ (n - 1) * qb else 0

/-- SMF's `X_m` -/
def divXQ (P : ℕ → ℚ) (m : ℕ) : ℚ :=
  if m < n then levXQ (divAQ uq n ρ P ((1 + uq) * P 0)) divT uq m
  else levDQ (divAQ uq n ρ P ((1 + uq) * P 0)) divT uq n / (1 - ((2 * n - 1 : ℕ) : ℚ) * uq)

/-- `R = QuX_n` -/
def divRQ (P : ℕ → ℚ) : ℚ := ((2 * n - 1 : ℕ) : ℚ) * uq * divXQ uq n ρ P n

/-- `V_0 = (1 + u)^n σ_0` and the `V_j` for `j ≥ 1` -/
def vBQ (X : ℕ → ℚ) (j : ℕ) : ℚ := if j = 0 then (1 + uq) ^ n * sigmaXQ n X 0 else VbQ uq n X j

/-- Theorem 9 (b)'s bound at `k` -/
def renBQ (X : ℕ → ℚ) (k : ℕ) : ℚ :=
  usQ uq ^ (n - k) * vBQ uq n X k + ∑ j ∈ Ioc k n, usQ uq ^ (n + 1 - j) * vBQ uq n X j

/-- the minimum over `k` of Theorem 9 (b)'s bounds -/
def renMinQ (X : ℕ → ℚ) : ℚ := (range (n + 1)).inf' nonempty_range_add_one (renBQ uq n X)

/-- the update's error `ε` -/
def divEpsQ (P : ℕ → ℚ) : ℚ := divRQ uq n ρ P + renMinQ uq n (divXQ uq n ρ P)

/-- the next remainder's part bounds -/
def divP'Q (P : ℕ → ℚ) : ℕ → ℚ := gPartsQ uq n (divXQ uq n ρ P) (sigmaXQ n (divXQ uq n ρ P) 0) 0

/-- the remainders' part bounds `P^{(k)}` -/
def divPkQ : ℕ → ℕ → ℚ
  | 0 => fun i => ρ ^ i
  | k + 1 => divP'Q uq n ρ (divPkQ k)

/-- `q̄_k = (1 + u)P^{(k)}_0` -/
def divQbQ (k : ℕ) : ℚ := (1 + uq) * divPkQ uq n ρ k 0

/-- `Θ` -/
def divThetaQ : ℚ :=
  ∑ i ∈ range (n - 1), divPkQ uq n ρ n (i + 1) + uq * divPkQ uq n ρ n 0 + divQbQ uq n ρ n * (ρ / (1 - ρ)) +
    ∑ k ∈ range n, divEpsQ uq n ρ (divPkQ uq n ρ k)

/-- `Ξ` -/
def divXiQ : ℚ := ∑ j ∈ Ioc 0 n, (uq ^ n + uq ^ (n + 1 - j)) * VbQ uq n (divQbQ uq n ρ) j

/-- `κ_DIV` -/
def kdivQ : ℚ :=
  ((1 + uq ^ n) * divThetaQ uq n ρ * ((1 - ρ) / (1 - 2 * ρ)) + divXiQ uq n ρ) / ((1 - 2 * ρ) * uq ^ (n + 1))

end Mirrors

section Casts

variable (p : ℤ) (n : ℕ) {uq : ℚ} (h : (uq : ℝ) = u p) (ρ : ℚ)

include h

theorem cast_divG (P : ℕ → ℚ) (qb : ℚ) (i : ℕ) :
    ((divGQ uq ρ P qb i : ℚ) : ℝ) = divG p ρ (fun k => (P k : ℝ)) qb i := by
  simp only [divGQ, divG]
  split_ifs <;> simp [h]

theorem cast_divA (P : ℕ → ℚ) (qb : ℚ) (m : ℕ) :
    ((divAQ uq n ρ P qb m : ℚ) : ℝ) = divA p n ρ (fun k => (P k : ℝ)) qb m := by
  simp only [divAQ, divA]
  split_ifs <;> simp [cast_divG p h, h]

theorem cast_divX (P : ℕ → ℚ) (m : ℕ) :
    ((divXQ uq n ρ P m : ℚ) : ℝ) = divX p n ρ (fun k => (P k : ℝ)) m := by
  have hA : (fun k => ((divAQ uq n ρ P ((1 + uq) * P 0) k : ℚ) : ℝ)) =
      divA p n ρ (fun k => (P k : ℝ)) ((1 + u p) * (P 0 : ℝ)) := by
    funext k
    rw [cast_divA p n h]
    push_cast
    rw [h]
  simp only [divXQ, divX]
  split_ifs <;> simp [cast_levX, cast_levD, hA, h]

theorem cast_divR (P : ℕ → ℚ) : ((divRQ uq n ρ P : ℚ) : ℝ) = divR p n ρ (fun k => (P k : ℝ)) := by
  simp [divRQ, divR, cast_divX p n h, h]

theorem cast_vB (X : ℕ → ℚ) (j : ℕ) : ((vBQ uq n X j : ℚ) : ℝ) = vB p n (fun m => (X m : ℝ)) j := by
  simp only [vBQ, vB]
  split_ifs <;> simp [cast_sigmaX, cast_Vb p n h, h]

theorem cast_renB (X : ℕ → ℚ) (k : ℕ) : ((renBQ uq n X k : ℚ) : ℝ) = renB p n (fun m => (X m : ℝ)) k := by
  simp [renBQ, renB, cast_us p h, cast_vB p n h]

theorem cast_renMin (X : ℕ → ℚ) : ((renMinQ uq n X : ℚ) : ℝ) = renMin p n (fun m => (X m : ℝ)) := by
  unfold renMinQ renMin
  rw [Finset.apply_inf'_eq_inf'_comp nonempty_range_add_one (fun q : ℚ => (q : ℝ)) fun x y => Rat.cast_min x y]
  congr 1
  funext k
  exact cast_renB p n h X k

theorem cast_divEps (P : ℕ → ℚ) : ((divEpsQ uq n ρ P : ℚ) : ℝ) = divEps p n ρ (fun k => (P k : ℝ)) := by
  have hX : (fun m => ((divXQ uq n ρ P m : ℚ) : ℝ)) = divX p n ρ (fun k => (P k : ℝ)) :=
    funext (cast_divX p n h ρ P)
  simp only [divEpsQ, divEps, Rat.cast_add, cast_divR p n h, cast_renMin p n h, hX]

theorem cast_divP' (P : ℕ → ℚ) (i : ℕ) :
    ((divP'Q uq n ρ P i : ℚ) : ℝ) = divP' p n ρ (fun k => (P k : ℝ)) i := by
  have hX : (fun m => ((divXQ uq n ρ P m : ℚ) : ℝ)) = divX p n ρ (fun k => (P k : ℝ)) :=
    funext (cast_divX p n h ρ P)
  simp only [divP'Q, divP', cast_gParts p n h, cast_sigmaX, hX, Rat.cast_zero]

theorem cast_divPk : ∀ k i, ((divPkQ uq n ρ k i : ℚ) : ℝ) = divPk p n ρ k i
  | 0, i => by simp [divPkQ, divPk]
  | k + 1, i => by
    have hP : (fun i => ((divPkQ uq n ρ k i : ℚ) : ℝ)) = divPk p n ρ k := funext (cast_divPk k)
    simp only [divPkQ, divPk, cast_divP' p n h, hP]

theorem cast_divQb (k : ℕ) : ((divQbQ uq n ρ k : ℚ) : ℝ) = divQb p n ρ k := by
  simp [divQbQ, divQb, cast_divPk p n h, h]

theorem cast_divTheta : ((divThetaQ uq n ρ : ℚ) : ℝ) = divTheta p n ρ := by
  simp [divThetaQ, divTheta, cast_divPk p n h, cast_divQb p n h, cast_divEps p n h, h]

theorem cast_divXi : ((divXiQ uq n ρ : ℚ) : ℝ) = divXi p n ρ := by
  have hQ : (fun k => ((divQbQ uq n ρ k : ℚ) : ℝ)) = divQb p n ρ := funext (cast_divQb p n h ρ)
  simp [divXiQ, divXi, cast_Vb p n h, hQ, h]

/-- `kdivQ`, cast to `ℝ`, is `κ_DIV` -/
theorem cast_kdiv : ((kdivQ uq n ρ : ℚ) : ℝ) = kdiv p n ρ := by
  simp [kdivQ, kdiv, cast_divTheta p n h, cast_divXi p n h, h]

end Casts

end ExpansionBounds
