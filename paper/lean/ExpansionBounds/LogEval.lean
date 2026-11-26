import ExpansionBounds.LogConvexBound

/-!
# The convex variant of Theorem 42's bound in rational arithmetic

The mirrors over `ℚ` of Lemma 13's bounds with VecSum's second bound alone (`VcQ`, `gPartsCQ`, `gErrCQ`, `GmulECQ`,
`GmulPCQ`, `GaddECQ`, `GaddPCQ`, `GaddfECQ`, `GaddfPCQ`), each of which, cast to `ℝ`, is its bound (`cast_GmulEC` and
the like), and the steps the kernel evaluates on a state, a bound and a list of part bounds, each rounded up by `ρ`:
Horner's rule (`hornerStepLC`, `hornerRunLC`), step (3) of EXP's core (`expWLC`, `expYLC`, `expTLC`), a squaring
(`expSqLC`), LOG's step (4) in two pieces (`logC4aL`, `logC4bL`), its step (5) after Horner's rule in three
(`logHL`, `logGL`, `logPL`), and the last ADD (`logEndL`).
-/

namespace ExpansionBounds

open Finset Set

section Mirrors

variable (uq : ℚ) (n : ℕ)

/-- `V_j = ū(1 + u)^{n-j} σ_{j-1}` over `ℚ` -/
def VcQ (X : ℕ → ℚ) (j : ℕ) : ℚ := usQ uq * (1 + uq) ^ (n - j) * sigmaXQ n X (j - 1)

/-- Lemma 13 (b)'s part bounds with VecSum's second bound alone, over `ℚ` -/
def gPartsCQ (X : ℕ → ℚ) (Zb Fb : ℚ) : ℕ → ℚ
  | 0 => (1 + uq) * (Zb + Fb + ∑ j ∈ Ioc 1 n, VcQ uq n X j)
  | i + 1 => if i + 1 < n then (1 + uq) * (uq * gPartsCQ X Zb Fb i + ∑ j ∈ Ioc (i + 1) n, VcQ uq n X j) else 0

/-- Lemma 13 (a)'s error bound with VecSum's second bound alone, over `ℚ` -/
def gErrCQ (X : ℕ → ℚ) (Zb Fb : ℚ) : ℚ :=
  uq ^ n * Zb + (1 + uq ^ n) * Fb + ∑ j ∈ Ioc 0 n, (uq ^ n + uq ^ (n + 1 - j)) * VcQ uq n X j

/-- the convex `G_MUL`'s error bound over `ℚ` -/
def GmulECQ (α β : ℕ → ℚ) (Zb : ℚ) : ℚ := gErrCQ uq n (mulXQ uq n α β) Zb (mulRQ uq n α β + mulDeltaQ n α β)

/-- the convex `G_MUL`'s part bounds over `ℚ` -/
def GmulPCQ (α β : ℕ → ℚ) (Zb : ℚ) : ℕ → ℚ :=
  gPartsCQ uq n (mulXQ uq n α β) Zb (mulRQ uq n α β + mulDeltaQ n α β)

/-- the convex `G_ADD`'s error bound over `ℚ` -/
def GaddECQ (α β : ℕ → ℚ) (Zb : ℚ) : ℚ :=
  gErrCQ uq n (pairXQ uq n fun m => α m + β m) Zb (pairRQ uq n fun m => α m + β m)

/-- the convex `G_ADD`'s part bounds over `ℚ` -/
def GaddPCQ (α β : ℕ → ℚ) (Zb : ℚ) : ℕ → ℚ :=
  gPartsCQ uq n (pairXQ uq n fun m => α m + β m) Zb (pairRQ uq n fun m => α m + β m)

/-- the convex `G_ADDF`'s error bound over `ℚ`, with a given `λ_0` -/
def GaddfECQ (α : ℕ → ℚ) (lam0 Zb : ℚ) : ℚ := gErrCQ uq n (addfXQ uq n α lam0) Zb 0

/-- the convex `G_ADDF`'s part bounds over `ℚ`, with a given `λ_0` -/
def GaddfPCQ (α : ℕ → ℚ) (lam0 Zb : ℚ) : ℕ → ℚ := gPartsCQ uq n (addfXQ uq n α lam0) Zb 0

/-- `v_i` of LOG's step (5) over `ℚ` -/
def logVQ (C : ℚ) (q i : ℕ) : ℚ := ∑ l ∈ range (q + 1 - i), C ^ l / ((i + l : ℕ) : ℚ)

variable (ρ : ℚ → ℚ)

/-- one step of Horner's convex bounds over `ℚ`, from `(e_{k+1}, π^{(k+1)})` to `(e_k, π^{(k)})`, rounded by `ρ` -/
def hornerStepLC (πz : ℕ → ℚ) (zb εz η : ℚ) (Fk : ℕ → ℕ → ℚ) (φ v : ℕ → ℚ) (k : ℕ) (st : ℚ × List ℚ) :
    ℚ × List ℚ :=
  (ρ ((1 + εz) * zb * st.1 + εz * zb * v (k + 1) + φ k +
        (GmulECQ uq n πz (fun i => st.2.getD i 0) ((1 + εz) * zb * (v (k + 1) + st.1)) + n * η) +
      GaddECQ uq n (fun i => |Fk k i|)
        (fun i => GmulPCQ uq n πz (fun i => st.2.getD i 0) ((1 + εz) * zb * (v (k + 1) + st.1)) i + η)
        (v k + ((1 + εz) * zb * st.1 + εz * zb * v (k + 1) + φ k +
          (GmulECQ uq n πz (fun i => st.2.getD i 0) ((1 + εz) * zb * (v (k + 1) + st.1)) + n * η)))),
    (List.range n).map fun i => ρ (GaddPCQ uq n (fun i => |Fk k i|)
      (fun i => GmulPCQ uq n πz (fun i => st.2.getD i 0) ((1 + εz) * zb * (v (k + 1) + st.1)) i + η)
      (v k + ((1 + εz) * zb * st.1 + εz * zb * v (k + 1) + φ k +
        (GmulECQ uq n πz (fun i => st.2.getD i 0) ((1 + εz) * zb * (v (k + 1) + st.1)) + n * η))) i))

/-- the steps `j_0 ≤ j < j_0 + m` of Horner's convex bounds down from degree `d`, from a given state -/
def hornerRunLC (πz : ℕ → ℚ) (zb εz η : ℚ) (Fk : ℕ → ℕ → ℚ) (φ v : ℕ → ℚ) (d : ℕ) :
    ℕ → ℕ → ℚ × List ℚ → ℚ × List ℚ
  | _, 0, st => st
  | j0, m + 1, st =>
    hornerRunLC πz zb εz η Fk φ v d (j0 + 1) m (hornerStepLC uq n ρ πz zb εz η Fk φ v (d - (j0 + 1)) st)

/-- step (3)'s first product of EXP's core, convex: from Horner's `(e_2, π^q_2)` to `((Z̄_w + ε', ε' + b'e_2), ω')` -/
def expWLC (πq : ℕ → ℚ) (bp : ℚ) (st : ℚ × List ℚ) : (ℚ × ℚ) × List ℚ :=
  ((ρ (bp * (coreVQ bp 2 + st.1) + GmulECQ uq n πq (fun i => st.2.getD i 0) (bp * (coreVQ bp 2 + st.1))),
      ρ (GmulECQ uq n πq (fun i => st.2.getD i 0) (bp * (coreVQ bp 2 + st.1)) + bp * st.1)),
    (List.range n).map fun i => ρ (GmulPCQ uq n πq (fun i => st.2.getD i 0) (bp * (coreVQ bp 2 + st.1)) i))

/-- step (3)'s second product, convex: to `(E^-, ω)` -/
def expYLC (πq : ℕ → ℚ) (bp D : ℚ) (d : ℕ) (st : (ℚ × ℚ) × List ℚ) : ℚ × List ℚ :=
  (ρ (GmulECQ uq n πq (fun i => st.2.getD i 0) (bp * st.1.1) + bp * st.1.2 + eTrQ bp d + D),
    (List.range n).map fun i => ρ (GmulPCQ uq n πq (fun i => st.2.getD i 0) (bp * st.1.1) i))

/-- step (3)'s sum and its scaling back, convex: to `(E_0, ψ_0)` -/
def expTLC (πq : ℕ → ℚ) (T0 η : ℚ) (st : ℚ × List ℚ) : ℚ × List ℚ :=
  (ρ (st.1 + GaddECQ uq n πq (fun i => st.2.getD i 0) (T0 + st.1) + n * η),
    (List.range n).map fun i => ρ (GaddPCQ uq n πq (fun i => st.2.getD i 0) (T0 + st.1) i + η))

/-- one squaring, `sqBC` -/
def expSqLC (T T' g : ℚ) (st : ℚ × List ℚ) : ℚ × List ℚ :=
  (ρ (2 * g * st.1 + st.1 ^ 2 + GmulECQ uq n (fun i => st.2.getD i 0) (fun i => st.2.getD i 0) ((T + st.1) ^ 2) +
      GaddECQ uq n (fun i => 2 * st.2.getD i 0)
        (GmulPCQ uq n (fun i => st.2.getD i 0) (fun i => st.2.getD i 0) ((T + st.1) ^ 2))
        (T' + 2 * st.1 * (1 + T) + st.1 ^ 2 +
          GmulECQ uq n (fun i => st.2.getD i 0) (fun i => st.2.getD i 0) ((T + st.1) ^ 2))),
    (List.range n).map fun i => ρ (GaddPCQ uq n (fun i => 2 * st.2.getD i 0)
      (GmulPCQ uq n (fun i => st.2.getD i 0) (fun i => st.2.getD i 0) ((T + st.1) ^ 2))
      (T' + 2 * st.1 * (1 + T) + st.1 ^ 2 +
        GmulECQ uq n (fun i => st.2.getD i 0) (fun i => st.2.getD i 0) ((T + st.1) ^ 2)) i))

/-- the convex `t̄_j`'s bound: `e^{2^j b'} - 1` for `r ≥ 0`, on the enclosure of `e^z`, and `2^j b'` for `r ≤ 0` -/
def coreTCQ (pos : Bool) (bp : ℚ) (j : ℕ) : ℚ := ρ (if pos then expUpQ (2 ^ j * bp) - 1 else 2 ^ j * bp)

/-- LOG's step (4), first piece: from `(E_m, ψ_m)` to `((ε_{φt}, ε_{φ+t}), (ν, π^s))`; `xs` bounds
`2(e^{b̂} - 1 - b̂) + e^{b̂}(e^{E+δ} - 1)` -/
def logC4aL (D η : ℚ) (πφ : ℕ → ℚ) (φb tb xs : ℚ) (B : ℤ) (st : ℚ × List ℚ) : (ℚ × ℚ) × (List ℚ × List ℚ) :=
  ((ρ (GmulECQ uq n πφ (fun i => st.2.getD i 0) (φb * (tb + st.1)) + n * η +
        (2 : ℚ) ^ (-B - 12) * max φb (tb + st.1)),
      ρ (GaddECQ uq n πφ (fun i => st.2.getD i 0) (xs + st.1 + D))),
    ((List.range n).map fun i => ρ (GmulPCQ uq n πφ (fun i => st.2.getD i 0) (φb * (tb + st.1)) i + η),
      (List.range n).map fun i => ρ (GaddPCQ uq n πφ (fun i => st.2.getD i 0) (xs + st.1 + D) i)))

/-- LOG's step (4), second piece: to `(E_c, χ)`; `cs` bounds `e^E - 1`, `xd` bounds `e^E(e^δ - 1)`, and `st0` is
`(E_m, ψ_m)` -/
def logC4bL (D : ℚ) (πφ : ℕ → ℚ) (tb cs xd ξ : ℚ) (st0 : ℚ × List ℚ) (st : (ℚ × ℚ) × (List ℚ × List ℚ)) :
    ℚ × List ℚ :=
  (ρ (ξ * st0.1 + (xd + D * (1 + tb + st0.1)) + st.1.1 + st.1.2 +
      GaddECQ uq n (fun i => st.2.2.getD i 0) (fun i => st.2.1.getD i 0)
        (cs + ξ * st0.1 + (xd + D * (1 + tb + st0.1)) + st.1.1 + st.1.2)),
    (List.range n).map fun i => ρ (max
      (GaddPCQ uq n (fun i => st.2.2.getD i 0) (fun i => st.2.1.getD i 0)
        (cs + ξ * st0.1 + (xd + D * (1 + tb + st0.1)) + st.1.1 + st.1.2) i)
      (GaddPCQ uq n πφ (fun i => st0.2.getD i 0) (cs + (ξ * st0.1 + (xd + D * (1 + tb + st0.1)) + st.1.1 + st.1.2 +
        GaddECQ uq n (fun i => st.2.2.getD i 0) (fun i => st.2.1.getD i 0)
          (cs + ξ * st0.1 + (xd + D * (1 + tb + st0.1)) + st.1.1 + st.1.2))) i)))

/-- LOG's step (5) after Horner's rule, first piece: from `(e_2, π^h_2)` to `((h̄, ε^h), ω^h)` -/
def logHL (η : ℚ) (χ : ℕ → ℚ) (C : ℚ) (q : ℕ) (st : ℚ × List ℚ) : (ℚ × ℚ) × List ℚ :=
  ((ρ (C * (logVQ C q 2 + st.1) + (GmulECQ uq n χ (fun i => st.2.getD i 0) (C * (logVQ C q 2 + st.1)) + n * η)),
      ρ (GmulECQ uq n χ (fun i => st.2.getD i 0) (C * (logVQ C q 2 + st.1)) + n * η)),
    (List.range n).map fun i => ρ (GmulPCQ uq n χ (fun i => st.2.getD i 0) (C * (logVQ C q 2 + st.1)) i + η))

/-- LOG's step (5), second piece: `(ε^g, ω^g) = G_ADDF(ω^h, 1; 1 + h̄, 1 + h̄ + ∑_{j≥1}ω^h_j)` -/
def logGL (st : (ℚ × ℚ) × List ℚ) : ℚ × List ℚ :=
  (ρ (GaddfECQ uq n (fun i => st.2.getD i 0) (1 + st.1.1 + ∑ j ∈ Ico 1 n, st.2.getD j 0) (1 + st.1.1)),
    (List.range n).map fun i =>
      ρ (GaddfPCQ uq n (fun i => st.2.getD i 0) (1 + st.1.1 + ∑ j ∈ Ico 1 n, st.2.getD j 0) (1 + st.1.1) i))

/-- LOG's step (5), third piece: to `(P, ω_r)`, from `e_2`, `(h̄, ε^h)` and `(ε^g, ω^g)` -/
def logPL (η : ℚ) (χ : ℕ → ℚ) (C Ec e2 hb εh : ℚ) (q : ℕ) (B : ℤ) (st : ℚ × List ℚ) : ℚ × List ℚ :=
  (ρ (GmulECQ uq n χ (fun i => st.2.getD i 0) (C * (1 + hb + st.1)) + n * η + C * (st.1 + εh + C * e2) +
      max (C ^ (q + 1) / (q + 1)) ((2 : ℚ) ^ (-B - 13) * C) / (1 - C) + Ec / (1 - C)),
    (List.range n).map fun i =>
      ρ (max (GmulPCQ uq n χ (fun i => st.2.getD i 0) (C * (1 + hb + st.1)) i + η) (χ i)))

/-- the last ADD: `𝓔 = ε_y + P` with `(ε_y, ·) = G_ADD(π^y, ω_r; ℓ + P)` -/
def logEndL (πy : ℕ → ℚ) (l : ℚ) (st : ℚ × List ℚ) : ℚ :=
  GaddECQ uq n πy (fun i => st.2.getD i 0) (l + st.1) + st.1

end Mirrors

/-! ### Each mirror, cast to `ℝ`, is its bound -/

section Casts

variable (p : ℤ) (n : ℕ) {uq : ℚ} (h : (uq : ℝ) = u p)

include h

/-- `VcQ`, cast to `ℝ`, is `Vc`. -/
theorem cast_Vc (X : ℕ → ℚ) (j : ℕ) : ((VcQ uq n X j : ℚ) : ℝ) = Vc p n (fun m => (X m : ℝ)) j := by
  simp [VcQ, Vc, cast_us p h, cast_sigmaX, h]

/-- `gPartsCQ`, cast to `ℝ`, is `gPartsC`. -/
theorem cast_gPartsC (X : ℕ → ℚ) (Zb Fb : ℚ) :
    ∀ i, ((gPartsCQ uq n X Zb Fb i : ℚ) : ℝ) = gPartsC p n (fun m => (X m : ℝ)) Zb Fb i
  | 0 => by simp [gPartsCQ, gPartsC, cast_Vc p n h, h]
  | i + 1 => by
    simp only [gPartsCQ, gPartsC]
    split_ifs
    · simp [cast_gPartsC X Zb Fb i, cast_Vc p n h, h]
    · simp

/-- `gErrCQ`, cast to `ℝ`, is `gErrC`. -/
theorem cast_gErrC (X : ℕ → ℚ) (Zb Fb : ℚ) :
    ((gErrCQ uq n X Zb Fb : ℚ) : ℝ) = gErrC p n (fun m => (X m : ℝ)) Zb Fb := by
  simp [gErrCQ, gErrC, cast_Vc p n h, h]

/-- The convex `G_MUL`'s error bound over `ℚ`, cast to `ℝ`, is `GmulEC`. -/
theorem cast_GmulEC (α β : ℕ → ℚ) (Zb : ℚ) :
    ((GmulECQ uq n α β Zb : ℚ) : ℝ) = GmulEC p n (fun i => (α i : ℝ)) (fun j => (β j : ℝ)) Zb := by
  have hX : (fun m => ((mulXQ uq n α β m : ℚ) : ℝ)) = mulX p n (fun i => (α i : ℝ)) (fun j => (β j : ℝ)) :=
    funext (cast_mulX p n h α β)
  simp only [GmulECQ, GmulEC, cast_gErrC p n h, hX, Rat.cast_add, cast_mulR p n h, cast_mulDelta]

/-- The convex `G_MUL`'s part bounds over `ℚ`, cast to `ℝ`, are `GmulPC`. -/
theorem cast_GmulPC (α β : ℕ → ℚ) (Zb : ℚ) (i : ℕ) :
    ((GmulPCQ uq n α β Zb i : ℚ) : ℝ) = GmulPC p n (fun i => (α i : ℝ)) (fun j => (β j : ℝ)) Zb i := by
  have hX : (fun m => ((mulXQ uq n α β m : ℚ) : ℝ)) = mulX p n (fun i => (α i : ℝ)) (fun j => (β j : ℝ)) :=
    funext (cast_mulX p n h α β)
  simp only [GmulPCQ, GmulPC, cast_gPartsC p n h, hX, Rat.cast_add, cast_mulR p n h, cast_mulDelta]

/-- The convex `G_ADD`'s error bound over `ℚ`, cast to `ℝ`, is `GaddEC`. -/
theorem cast_GaddEC (α β : ℕ → ℚ) (Zb : ℚ) :
    ((GaddECQ uq n α β Zb : ℚ) : ℝ) = GaddEC p n (fun i => (α i : ℝ)) (fun j => (β j : ℝ)) Zb := by
  have hX : (fun m => ((pairXQ uq n (fun m => α m + β m) m : ℚ) : ℝ)) =
      pairX p n fun m => (α m : ℝ) + (β m : ℝ) := by
    funext m
    rw [cast_pairX p n h]
    simp only [Rat.cast_add]
  simp only [GaddECQ, GaddEC, cast_gErrC p n h, hX, cast_pairR p n h, Rat.cast_add]

/-- The convex `G_ADD`'s part bounds over `ℚ`, cast to `ℝ`, are `GaddPC`. -/
theorem cast_GaddPC (α β : ℕ → ℚ) (Zb : ℚ) (i : ℕ) :
    ((GaddPCQ uq n α β Zb i : ℚ) : ℝ) = GaddPC p n (fun i => (α i : ℝ)) (fun j => (β j : ℝ)) Zb i := by
  have hX : (fun m => ((pairXQ uq n (fun m => α m + β m) m : ℚ) : ℝ)) =
      pairX p n fun m => (α m : ℝ) + (β m : ℝ) := by
    funext m
    rw [cast_pairX p n h]
    simp only [Rat.cast_add]
  simp only [GaddPCQ, GaddPC, cast_gPartsC p n h, hX, cast_pairR p n h, Rat.cast_add]

/-- The convex `G_ADDF`'s error bound over `ℚ`, cast to `ℝ`, is `GaddfEC`. -/
theorem cast_GaddfEC (α : ℕ → ℚ) (lam0 Zb : ℚ) :
    ((GaddfECQ uq n α lam0 Zb : ℚ) : ℝ) = GaddfEC p n (fun i => (α i : ℝ)) lam0 Zb := by
  have hX : (fun m => ((addfXQ uq n α lam0 m : ℚ) : ℝ)) = addfX p n (fun i => (α i : ℝ)) lam0 :=
    funext (cast_addfX p n h α lam0)
  simp only [GaddfECQ, GaddfEC, cast_gErrC p n h, hX, Rat.cast_zero]

/-- The convex `G_ADDF`'s part bounds over `ℚ`, cast to `ℝ`, are `GaddfPC`. -/
theorem cast_GaddfPC (α : ℕ → ℚ) (lam0 Zb : ℚ) (i : ℕ) :
    ((GaddfPCQ uq n α lam0 Zb i : ℚ) : ℝ) = GaddfPC p n (fun i => (α i : ℝ)) lam0 Zb i := by
  have hX : (fun m => ((addfXQ uq n α lam0 m : ℚ) : ℝ)) = addfX p n (fun i => (α i : ℝ)) lam0 :=
    funext (cast_addfX p n h α lam0)
  simp only [GaddfPCQ, GaddfPC, cast_gPartsC p n h, hX, Rat.cast_zero]

end Casts

/-! ### The convex bounds grow with their arguments, and are at most their mirrors -/

section Mono

variable (p : ℤ) (n : ℕ)

/-- The convex `G_MUL` is nonnegative and grows with its arguments: the class `Cvx` along a segment. -/
theorem GmulC_sand (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {α α' β β' : ℕ → ℝ} (hα : ∀ i, Sand (α i) (α' i))
    (hβ : ∀ j, Sand (β j) (β' j)) {Zb Zb' : ℝ} (hZ : Sand Zb Zb') :
    Sand (GmulEC p n α β Zb) (GmulEC p n α' β' Zb') ∧
      ∀ i, Sand (GmulPC p n α β Zb i) (GmulPC p n α' β' Zb' i) := by
  have hs : Convex ℝ (Icc (0 : ℝ) 1) := convex_Icc 0 1
  have hα' := fun i => cvx_segment (hα i).nonneg (hα i).le
  have hβ' := fun j => cvx_segment (hβ j).nonneg (hβ j).le
  have hZ' := cvx_segment hZ.nonneg hZ.le
  have h1 := (GmulEC_cvx p n hA3 hs hα' hβ' hZ').zero_le_one
  have h2 := fun i => (GmulPC_cvx p n hA3 hs hα' hβ' hZ' i).zero_le_one
  simp only [mul_zero, add_zero, mul_one, add_sub_cancel] at h1 h2
  exact ⟨⟨h1.1, h1.2⟩, fun i => ⟨(h2 i).1, (h2 i).2⟩⟩

/-- The convex `G_ADD` is nonnegative and grows with its arguments. -/
theorem GaddC_sand (hA3 : ((n : ℝ) ^ 2 + n) * u p < 1) {α α' β β' : ℕ → ℝ} (hα : ∀ i, Sand (α i) (α' i))
    (hβ : ∀ j, Sand (β j) (β' j)) {Zb Zb' : ℝ} (hZ : Sand Zb Zb') :
    Sand (GaddEC p n α β Zb) (GaddEC p n α' β' Zb') ∧
      ∀ i, Sand (GaddPC p n α β Zb i) (GaddPC p n α' β' Zb' i) := by
  have hs : Convex ℝ (Icc (0 : ℝ) 1) := convex_Icc 0 1
  have hα' := fun i => cvx_segment (hα i).nonneg (hα i).le
  have hβ' := fun j => cvx_segment (hβ j).nonneg (hβ j).le
  have hZ' := cvx_segment hZ.nonneg hZ.le
  have h1 := (GaddEC_cvx p n hA3 hs hα' hβ' hZ').zero_le_one
  have h2 := fun i => (GaddPC_cvx p n hA3 hs hα' hβ' hZ' i).zero_le_one
  simp only [mul_zero, add_zero, mul_one, add_sub_cancel] at h1 h2
  exact ⟨⟨h1.1, h1.2⟩, fun i => ⟨(h2 i).1, (h2 i).2⟩⟩

/-- The convex `G_ADDF` is nonnegative and grows with its arguments. -/
theorem GaddfC_sand {α α' : ℕ → ℝ} (hα : ∀ i, Sand (α i) (α' i)) {lam0 lam0' Zb Zb' : ℝ} (hl : Sand lam0 lam0')
    (hZ : Sand Zb Zb') : Sand (GaddfEC p n α lam0 Zb) (GaddfEC p n α' lam0' Zb') ∧
      ∀ i, Sand (GaddfPC p n α lam0 Zb i) (GaddfPC p n α' lam0' Zb' i) := by
  have hs : Convex ℝ (Icc (0 : ℝ) 1) := convex_Icc 0 1
  have hα' := fun i => cvx_segment (hα i).nonneg (hα i).le
  have hl' := cvx_segment hl.nonneg hl.le
  have hZ' := cvx_segment hZ.nonneg hZ.le
  have h1 := (GaddfEC_cvx p n hs hα' hl' hZ').zero_le_one
  have h2 := fun i => (GaddfPC_cvx p n hs hα' hl' hZ' i).zero_le_one
  simp only [mul_zero, add_zero, mul_one, add_sub_cancel] at h1 h2
  exact ⟨⟨h1.1, h1.2⟩, fun i => ⟨(h2 i).1, (h2 i).2⟩⟩

/-- The convex `G_MUL` uses the part bounds below `n` only. -/
theorem GmulC_trunc (α β : ℕ → ℝ) (Zb : ℝ) : GmulEC p n (trunc n α) (trunc n β) Zb = GmulEC p n α β Zb ∧
    GmulPC p n (trunc n α) (trunc n β) Zb = GmulPC p n α β Zb := by
  have hD : mulDelta n (trunc n α) (trunc n β) = mulDelta n α β := by
    unfold mulDelta
    refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
    rw [trunc_lt n α (mem_range.mp hi), trunc_lt n β (mem_range.mp hj)]
  simp only [GmulEC, GmulPC, mulR, mulX_trunc p n α β, hD, and_self]

/-- The convex `G_ADD` uses the part bounds below `n` only. -/
theorem GaddC_trunc (hn : 1 ≤ n) (α β : ℕ → ℝ) (Zb : ℝ) :
    GaddEC p n (trunc n α) (trunc n β) Zb = GaddEC p n α β Zb ∧
      GaddPC p n (trunc n α) (trunc n β) Zb = GaddPC p n α β Zb := by
  have hX : pairX p n (fun m => trunc n α m + trunc n β m) = pairX p n (fun m => α m + β m) := by
    funext m
    simp only [pairX, pairA_trunc p n hn α β]
  simp only [GaddEC, GaddPC, pairR, hX, and_self]

/-- The convex `G_ADDF` uses the part bounds below `n` only. -/
theorem GaddfC_trunc (hn : 1 ≤ n) (α : ℕ → ℝ) (lam0 Zb : ℝ) :
    GaddfEC p n (trunc n α) lam0 Zb = GaddfEC p n α lam0 Zb ∧
      GaddfPC p n (trunc n α) lam0 Zb = GaddfPC p n α lam0 Zb := by
  simp only [GaddfEC, GaddfPC, addfX_trunc p n hn α lam0, and_self]

/-- Truncations of nonnegative bounds compared below `n` are in the relation. -/
theorem trunc_sand {f g : ℕ → ℝ} (h0 : ∀ i < n, 0 ≤ f i) (hfg : ∀ i < n, f i ≤ g i) (i : ℕ) :
    Sand (trunc n f i) (trunc n g i) := by
  unfold trunc
  split_ifs with hi
  · exact ⟨h0 i hi, hfg i hi⟩
  · exact Sand.refl le_rfl

variable {uq : ℚ} (h : (uq : ℝ) = u p)

include h

/-- The convex `G_ADDF` on real bounds is at most its mirror on rational bounds above them. -/
theorem GaddfC_le_mirror (hn : 1 ≤ n) {α : ℕ → ℝ} {αq : ℕ → ℚ} (hα0 : ∀ i < n, 0 ≤ α i)
    (hα : ∀ i < n, α i ≤ ((αq i : ℚ) : ℝ)) {lam0 Zb : ℝ} {lq Zq : ℚ} (hl0 : 0 ≤ lam0)
    (hl : lam0 ≤ ((lq : ℚ) : ℝ)) (hZ0 : 0 ≤ Zb) (hZ : Zb ≤ ((Zq : ℚ) : ℝ)) :
    GaddfEC p n α lam0 Zb ≤ ((GaddfECQ uq n αq lq Zq : ℚ) : ℝ) ∧
      ∀ i, GaddfPC p n α lam0 Zb i ≤ ((GaddfPCQ uq n αq lq Zq i : ℚ) : ℝ) := by
  have hm := GaddfC_sand p n (trunc_sand n hα0 hα) ⟨hl0, hl⟩ ⟨hZ0, hZ⟩
  rw [(GaddfC_trunc p n hn α lam0 Zb).1, (GaddfC_trunc p n hn α lam0 Zb).2, (GaddfC_trunc p n hn _ _ _).1,
    (GaddfC_trunc p n hn _ _ _).2] at hm
  rw [cast_GaddfEC p n h]
  exact ⟨hm.1.le, fun i => by rw [cast_GaddfPC p n h]; exact (hm.2 i).le⟩

end Mono

end ExpansionBounds
