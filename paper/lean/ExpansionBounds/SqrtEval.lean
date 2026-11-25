import ExpansionBounds.SqrtDD
import ExpansionBounds.Eval

/-!
# `G_MUL`, `G_ADD` and the square root's recursions in rational arithmetic

The mirrors over `ℚ` of Lemma 13's bounds for MUL and for ADD, `G_MUL` and `G_ADD`, of `G_ADDF` with a given `λ_0`, and
of the recursions that define `δ_J` (Theorem 21) and `δ^DD` (Theorem 22): the Newton step `sqrtB`, the second-order
step `sqrtB2`, and the starts `E_0`. `cast_sqrtDelta` and `cast_ddDelta` show that `sqrtDeltaQ` and `ddDeltaQ`, cast to
`ℝ`, are `δ_J` and `δ^DD`.
-/

namespace ExpansionBounds

open Finset

section Mirrors

variable (uq : ℚ) (n : ℕ)

/-- the products of level `m` -/
def mulPQ (α β : ℕ → ℚ) (m : ℕ) : ℚ := ∑ i ∈ range n, ∑ j ∈ range n, if i + j = m then α i * β j else 0

/-- MUL's `A_m` -/
def mulAQ (α β : ℕ → ℚ) (m : ℕ) : ℚ :=
  if m < n then (1 + uq) * mulPQ n α β m + (if m = 0 then 0 else uq * mulPQ n α β (m - 1))
  else if m = n then mulPQ n α β n + uq * mulPQ n α β (n - 1) else 0

/-- the dropped products `Δ` -/
def mulDeltaQ (α β : ℕ → ℚ) : ℚ := ∑ i ∈ range n, ∑ j ∈ range n, if n < i + j then α i * β j else 0

/-- MUL's `X_m` -/
def mulXQ (α β : ℕ → ℚ) (m : ℕ) : ℚ :=
  if m < n then levXQ (mulAQ uq n α β) mulT uq m
  else levDQ (mulAQ uq n α β) mulT uq n / (1 - ((n ^ 2 + n - 1 : ℕ) : ℚ) * uq)

/-- MUL's `R = QuX_n` -/
def mulRQ (α β : ℕ → ℚ) : ℚ := ((n ^ 2 + n - 1 : ℕ) : ℚ) * uq * mulXQ uq n α β n

/-- `G_MUL`'s error bound -/
def GmulEQ (α β : ℕ → ℚ) (Zb : ℚ) : ℚ := gErrQ uq n (mulXQ uq n α β) Zb (mulRQ uq n α β + mulDeltaQ n α β)

/-- `G_MUL`'s part bounds -/
def GmulPQ (α β : ℕ → ℚ) (Zb : ℚ) : ℕ → ℚ := gPartsQ uq n (mulXQ uq n α β) Zb (mulRQ uq n α β + mulDeltaQ n α β)

/-- ADD's and MULF's `A_m` -/
def pairAQ (lam : ℕ → ℚ) (m : ℕ) : ℚ :=
  if m < n then (1 + uq) * lam m + (if m = 0 then 0 else uq * lam (m - 1))
  else if m = n then uq * lam (n - 1) else 0

/-- ADD's and MULF's `X_m` -/
def pairXQ (lam : ℕ → ℚ) (m : ℕ) : ℚ :=
  if m < n then levXQ (pairAQ uq n lam) id uq m
  else levDQ (pairAQ uq n lam) id uq n / (1 - ((n - 1 : ℕ) : ℚ) * uq)

/-- ADD's and MULF's `R` -/
def pairRQ (lam : ℕ → ℚ) : ℚ := ((n - 1 : ℕ) : ℚ) * uq * pairXQ uq n lam n

/-- `G_ADD`'s error bound -/
def GaddEQ (α β : ℕ → ℚ) (Zb : ℚ) : ℚ :=
  gErrQ uq n (pairXQ uq n fun m => α m + β m) Zb (pairRQ uq n fun m => α m + β m)

/-- `G_ADD`'s part bounds -/
def GaddPQ (α β : ℕ → ℚ) (Zb : ℚ) : ℕ → ℚ :=
  gPartsQ uq n (pairXQ uq n fun m => α m + β m) Zb (pairRQ uq n fun m => α m + β m)

/-- `G_ADDF`'s error bound with a given `λ_0` -/
def GaddfE'Q (α : ℕ → ℚ) (lam0 Zb : ℚ) : ℚ := gErrQ uq n (addfXQ uq n α lam0) Zb 0

/-- `G_ADDF`'s part bounds with a given `λ_0` -/
def GaddfP'Q (α : ℕ → ℚ) (lam0 Zb : ℚ) : ℕ → ℚ := gPartsQ uq n (addfXQ uq n α lam0) Zb 0

/-- `ε_m` -/
def sqrtEmQ (E : ℚ) (π : ℕ → ℚ) : ℚ := GmulEQ uq n π π ((1 + E) ^ 2)

/-- `ε_g` -/
def sqrtEgQ (hb : ℕ → ℚ) (E : ℚ) (π : ℕ → ℚ) : ℚ :=
  GmulEQ uq n hb (GmulPQ uq n π π ((1 + E) ^ 2)) (((1 + E) ^ 2 + sqrtEmQ uq n E π) / 2)

/-- `π^g` -/
def sqrtPgQ (hb : ℕ → ℚ) (E : ℚ) (π : ℕ → ℚ) : ℕ → ℚ :=
  GmulPQ uq n hb (GmulPQ uq n π π ((1 + E) ^ 2)) (((1 + E) ^ 2 + sqrtEmQ uq n E π) / 2)

/-- `Z̄_c` -/
def sqrtZcQ (hb : ℕ → ℚ) (E : ℚ) (π : ℕ → ℚ) : ℚ :=
  (2 * E + E ^ 2) / 2 + sqrtEmQ uq n E π / 2 + sqrtEgQ uq n hb E π

/-- `λ_0` of the step's ADDF -/
def sqrtL0Q (hb : ℕ → ℚ) (E : ℚ) (π : ℕ → ℚ) : ℚ :=
  sqrtZcQ uq n hb E π + ∑ i ∈ Ico 1 n, sqrtPgQ uq n hb E π i

/-- `ε_c` -/
def sqrtEcQ (hb : ℕ → ℚ) (E : ℚ) (π : ℕ → ℚ) : ℚ :=
  GaddfE'Q uq n (sqrtPgQ uq n hb E π) (sqrtL0Q uq n hb E π) (sqrtZcQ uq n hb E π)

/-- `χ` -/
def sqrtChiQ (hb : ℕ → ℚ) (E : ℚ) (π : ℕ → ℚ) : ℕ → ℚ :=
  GaddfP'Q uq n (sqrtPgQ uq n hb E π) (sqrtL0Q uq n hb E π) (sqrtZcQ uq n hb E π)

/-- one Newton step: the next `E` and `π` -/
def sqrtBQ (hb : ℕ → ℚ) (E : ℚ) (π : ℕ → ℚ) : ℚ × (ℕ → ℚ) :=
  let εmgc := sqrtEmQ uq n E π / 2 + sqrtEgQ uq n hb E π + sqrtEcQ uq n hb E π
  let cb := sqrtZcQ uq n hb E π + sqrtEcQ uq n hb E π
  let εd := GmulEQ uq n (sqrtChiQ uq n hb E π) π (cb * (1 + E))
  let δ := GmulPQ uq n (sqrtChiQ uq n hb E π) π (cb * (1 + E))
  let Zr := (1 + E) + cb * (1 + E) + εd
  (3 / 2 * E ^ 2 + E ^ 3 / 2 + (1 + E) * εmgc + εd + GaddEQ uq n π δ Zr, GaddPQ uq n π δ Zr)

/-- `ā_i = ρ^i(1 - ρ)/(1 - 2ρ)` -/
def abarQ (ρ : ℚ) (i : ℕ) : ℚ := ρ ^ i * ((1 - ρ) / (1 - 2 * ρ))

/-- `E_0` of SQRT_{n,J} -/
def sqrtE0Q (ρ : ℚ) : ℚ := max ((1 + 2 * uq) / (1 - ρ) - 1) (1 - (1 - 2 * uq) * (1 - 2 * ρ) / (1 - ρ))

/-- `(E_k, π^{(k)})` -/
def sqrtBkQ (ρ : ℚ) : ℕ → ℚ × (ℕ → ℚ)
  | 0 => (sqrtE0Q uq ρ, fun i => if i = 0 then 1 + sqrtE0Q uq ρ else 0)
  | k + 1 => sqrtBQ uq n (fun i => abarQ ρ i / 2) (sqrtBkQ ρ k).1 (sqrtBkQ ρ k).2

/-- `δ_J` -/
def sqrtDeltaQ (ρ : ℚ) (J : ℕ) : ℚ :=
  (sqrtBkQ uq n ρ J).1 + GmulEQ uq n (sqrtBkQ uq n ρ J).2 (abarQ ρ) (1 + (sqrtBkQ uq n ρ J).1)

/-- `η_1 = 25u²/8` -/
def ddEta1Q : ℚ := 25 / 8 * uq ^ 2

/-- `η_2 = 15u² + 56u³` -/
def ddEta2Q : ℚ := 15 * uq ^ 2 + 56 * uq ^ 3

/-- `η_3 = ρ²/(1 - ρ)²` -/
def ddEta3Q (ρ : ℚ) : ℚ := ρ ^ 2 / (1 - ρ) ^ 2

/-- `E_0` of SQRT^DD -/
def ddE0Q (ρ : ℚ) : ℚ :=
  max ((1 + ddEta3Q ρ / 2) * (1 + ddEta2Q uq) / (1 - ddEta1Q uq) - 1)
    (1 - (1 - ddEta3Q ρ) * (1 - ddEta2Q uq) / (1 + ddEta1Q uq))

/-- `π^{(0)}` of SQRT^DD -/
def ddPi0Q (ρ : ℚ) (i : ℕ) : ℚ :=
  if i = 0 then (1 + ddE0Q uq ρ) / (1 - uq) else if i = 1 then uq * (1 + ddE0Q uq ρ) / (1 - uq) else 0

/-- the second-order step: the next `E` and `π` -/
def sqrtB2Q (hb : ℕ → ℚ) (E : ℚ) (π : ℕ → ℚ) : ℚ × (ℕ → ℚ) :=
  let εmgc := sqrtEmQ uq n E π / 2 + sqrtEgQ uq n hb E π + sqrtEcQ uq n hb E π
  let cb := sqrtZcQ uq n hb E π + sqrtEcQ uq n hb E π
  let χ := sqrtChiQ uq n hb E π
  let εq := GmulEQ uq n χ χ (cb ^ 2)
  let ν := GmulPQ uq n χ χ (cb ^ 2)
  let qb := cb ^ 2 + εq
  let εt := GaddEQ uq n ν (fun i => ν i / 2) (3 / 2 * qb)
  let ϑ := GaddPQ uq n ν (fun i => ν i / 2) (3 / 2 * qb)
  let tb := 3 / 2 * qb + εt
  let εw := GaddEQ uq n χ ϑ (cb + tb)
  let ω := GaddPQ uq n χ ϑ (cb + tb)
  let wb := cb + tb + εw
  let εd := GmulEQ uq n ω π (wb * (1 + E))
  let δ := GmulPQ uq n ω π (wb * (1 + E))
  let Zr := (1 + E) + wb * (1 + E) + εd
  (5 / 2 * E ^ 3 + 15 / 8 * E ^ 4 + 3 / 8 * E ^ 5 + εd + GaddEQ uq n π δ Zr +
    (1 + E) * (εmgc * (1 + 3 * (E + E ^ 2 / 2) + 3 / 2 * εmgc) + 3 / 2 * εq + εt + εw), GaddPQ uq n π δ Zr)

/-- `E_1` of SQRT^DD: the second-order step from the double-word start -/
def ddE1Q (ρ : ℚ) : ℚ := (sqrtB2Q uq n (fun i => abarQ ρ i / 2) (ddE0Q uq ρ) (ddPi0Q uq ρ)).1

/-- `δ^DD` -/
def ddDeltaQ (ρ : ℚ) : ℚ :=
  (sqrtBQ uq n (fun i => abarQ ρ i / 2) (sqrtB2Q uq n (fun i => abarQ ρ i / 2) (ddE0Q uq ρ) (ddPi0Q uq ρ)).1
      (sqrtB2Q uq n (fun i => abarQ ρ i / 2) (ddE0Q uq ρ) (ddPi0Q uq ρ)).2).1 +
    GmulEQ uq n (sqrtBQ uq n (fun i => abarQ ρ i / 2) (sqrtB2Q uq n (fun i => abarQ ρ i / 2) (ddE0Q uq ρ) (ddPi0Q uq ρ)).1
      (sqrtB2Q uq n (fun i => abarQ ρ i / 2) (ddE0Q uq ρ) (ddPi0Q uq ρ)).2).2 (abarQ ρ)
      (1 + (sqrtBQ uq n (fun i => abarQ ρ i / 2) (sqrtB2Q uq n (fun i => abarQ ρ i / 2) (ddE0Q uq ρ) (ddPi0Q uq ρ)).1
        (sqrtB2Q uq n (fun i => abarQ ρ i / 2) (ddE0Q uq ρ) (ddPi0Q uq ρ)).2).1)

end Mirrors

section Casts

variable (p : ℤ) (n : ℕ) {uq : ℚ} (h : (uq : ℝ) = u p)

theorem cast_mulP (α β : ℕ → ℚ) (m : ℕ) :
    ((mulPQ n α β m : ℚ) : ℝ) = mulP n (fun i => (α i : ℝ)) (fun j => (β j : ℝ)) m := by
  simp only [mulPQ, mulP, Rat.cast_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem cast_mulDelta (α β : ℕ → ℚ) :
    ((mulDeltaQ n α β : ℚ) : ℝ) = mulDelta n (fun i => (α i : ℝ)) (fun j => (β j : ℝ)) := by
  simp only [mulDeltaQ, mulDelta, Rat.cast_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

include h

theorem cast_mulA (α β : ℕ → ℚ) (m : ℕ) :
    ((mulAQ uq n α β m : ℚ) : ℝ) = mulA p n (fun i => (α i : ℝ)) (fun j => (β j : ℝ)) m := by
  simp only [mulAQ, mulA]
  split_ifs <;> simp [cast_mulP, h]

theorem cast_mulX (α β : ℕ → ℚ) (m : ℕ) :
    ((mulXQ uq n α β m : ℚ) : ℝ) = mulX p n (fun i => (α i : ℝ)) (fun j => (β j : ℝ)) m := by
  have hA : (fun k => ((mulAQ uq n α β k : ℚ) : ℝ)) = mulA p n (fun i => (α i : ℝ)) (fun j => (β j : ℝ)) :=
    funext (cast_mulA p n h α β)
  simp only [mulXQ, mulX]
  split_ifs <;> simp [cast_levX, cast_levD, hA, h]

theorem cast_mulR (α β : ℕ → ℚ) :
    ((mulRQ uq n α β : ℚ) : ℝ) = mulR p n (fun i => (α i : ℝ)) (fun j => (β j : ℝ)) := by
  simp [mulRQ, mulR, cast_mulX p n h, h]

theorem cast_GmulE (α β : ℕ → ℚ) (Zb : ℚ) :
    ((GmulEQ uq n α β Zb : ℚ) : ℝ) = GmulE p n (fun i => (α i : ℝ)) (fun j => (β j : ℝ)) Zb := by
  have hX : (fun m => ((mulXQ uq n α β m : ℚ) : ℝ)) = mulX p n (fun i => (α i : ℝ)) (fun j => (β j : ℝ)) :=
    funext (cast_mulX p n h α β)
  simp only [GmulEQ, GmulE, cast_gErr p n h, hX, Rat.cast_add, cast_mulR p n h, cast_mulDelta]

theorem cast_GmulP (α β : ℕ → ℚ) (Zb : ℚ) (i : ℕ) :
    ((GmulPQ uq n α β Zb i : ℚ) : ℝ) = GmulP p n (fun i => (α i : ℝ)) (fun j => (β j : ℝ)) Zb i := by
  have hX : (fun m => ((mulXQ uq n α β m : ℚ) : ℝ)) = mulX p n (fun i => (α i : ℝ)) (fun j => (β j : ℝ)) :=
    funext (cast_mulX p n h α β)
  simp only [GmulPQ, GmulP, cast_gParts p n h, hX, Rat.cast_add, cast_mulR p n h, cast_mulDelta]

theorem cast_pairA (lam : ℕ → ℚ) (m : ℕ) :
    ((pairAQ uq n lam m : ℚ) : ℝ) = pairA p n (fun k => (lam k : ℝ)) m := by
  simp only [pairAQ, pairA]
  split_ifs <;> simp [h]

theorem cast_pairX (lam : ℕ → ℚ) (m : ℕ) :
    ((pairXQ uq n lam m : ℚ) : ℝ) = pairX p n (fun k => (lam k : ℝ)) m := by
  have hA : (fun k => ((pairAQ uq n lam k : ℚ) : ℝ)) = pairA p n (fun k => (lam k : ℝ)) :=
    funext (cast_pairA p n h lam)
  simp only [pairXQ, pairX]
  split_ifs <;> simp [cast_levX, cast_levD, hA, h]

theorem cast_pairR (lam : ℕ → ℚ) : ((pairRQ uq n lam : ℚ) : ℝ) = pairR p n (fun k => (lam k : ℝ)) := by
  simp [pairRQ, pairR, cast_pairX p n h, h]

theorem cast_GaddE (α β : ℕ → ℚ) (Zb : ℚ) :
    ((GaddEQ uq n α β Zb : ℚ) : ℝ) = GaddE p n (fun i => (α i : ℝ)) (fun j => (β j : ℝ)) Zb := by
  have hX : (fun m => ((pairXQ uq n (fun m => α m + β m) m : ℚ) : ℝ)) =
      pairX p n fun m => (α m : ℝ) + (β m : ℝ) := by
    funext m
    rw [cast_pairX p n h]
    simp only [Rat.cast_add]
  simp only [GaddEQ, GaddE, cast_gErr p n h, hX, cast_pairR p n h, Rat.cast_add]

theorem cast_GaddP (α β : ℕ → ℚ) (Zb : ℚ) (i : ℕ) :
    ((GaddPQ uq n α β Zb i : ℚ) : ℝ) = GaddP p n (fun i => (α i : ℝ)) (fun j => (β j : ℝ)) Zb i := by
  have hX : (fun m => ((pairXQ uq n (fun m => α m + β m) m : ℚ) : ℝ)) =
      pairX p n fun m => (α m : ℝ) + (β m : ℝ) := by
    funext m
    rw [cast_pairX p n h]
    simp only [Rat.cast_add]
  simp only [GaddPQ, GaddP, cast_gParts p n h, hX, cast_pairR p n h, Rat.cast_add]

theorem cast_GaddfE' (α : ℕ → ℚ) (lam0 Zb : ℚ) :
    ((GaddfE'Q uq n α lam0 Zb : ℚ) : ℝ) = GaddfE' p n (fun i => (α i : ℝ)) lam0 Zb := by
  have hX : (fun m => ((addfXQ uq n α lam0 m : ℚ) : ℝ)) = addfX p n (fun i => (α i : ℝ)) lam0 :=
    funext (cast_addfX p n h α lam0)
  simp only [GaddfE'Q, GaddfE', cast_gErr p n h, hX, Rat.cast_zero]

theorem cast_GaddfP' (α : ℕ → ℚ) (lam0 Zb : ℚ) (i : ℕ) :
    ((GaddfP'Q uq n α lam0 Zb i : ℚ) : ℝ) = GaddfP' p n (fun i => (α i : ℝ)) lam0 Zb i := by
  have hX : (fun m => ((addfXQ uq n α lam0 m : ℚ) : ℝ)) = addfX p n (fun i => (α i : ℝ)) lam0 :=
    funext (cast_addfX p n h α lam0)
  simp only [GaddfP'Q, GaddfP', cast_gParts p n h, hX, Rat.cast_zero]

theorem cast_sqrtEm (E : ℚ) (π : ℕ → ℚ) : ((sqrtEmQ uq n E π : ℚ) : ℝ) = sqrtEm p n E (fun i => (π i : ℝ)) := by
  simp [sqrtEmQ, sqrtEm, cast_GmulE p n h]

/-- `G_MUL(π, π; (1 + E)²)`'s part bounds, cast -/
theorem cast_sqrtMu (E : ℚ) (π : ℕ → ℚ) :
    (fun i => ((GmulPQ uq n π π ((1 + E) ^ 2) i : ℚ) : ℝ)) =
      GmulP p n (fun i => (π i : ℝ)) (fun i => (π i : ℝ)) ((1 + (E : ℝ)) ^ 2) := by
  funext i
  rw [cast_GmulP p n h]
  push_cast
  rfl

theorem cast_sqrtEg (hb : ℕ → ℚ) (E : ℚ) (π : ℕ → ℚ) :
    ((sqrtEgQ uq n hb E π : ℚ) : ℝ) = sqrtEg p n (fun i => (hb i : ℝ)) E (fun i => (π i : ℝ)) := by
  simp [sqrtEgQ, sqrtEg, cast_GmulE p n h, cast_sqrtMu p n h, cast_sqrtEm p n h]

theorem cast_sqrtPg (hb : ℕ → ℚ) (E : ℚ) (π : ℕ → ℚ) (i : ℕ) :
    ((sqrtPgQ uq n hb E π i : ℚ) : ℝ) = sqrtPg p n (fun i => (hb i : ℝ)) E (fun i => (π i : ℝ)) i := by
  simp [sqrtPgQ, sqrtPg, cast_GmulP p n h, cast_sqrtEm p n h]

theorem cast_sqrtZc (hb : ℕ → ℚ) (E : ℚ) (π : ℕ → ℚ) :
    ((sqrtZcQ uq n hb E π : ℚ) : ℝ) = sqrtZc p n (fun i => (hb i : ℝ)) E (fun i => (π i : ℝ)) := by
  simp [sqrtZcQ, sqrtZc, cast_sqrtEm p n h, cast_sqrtEg p n h]

theorem cast_sqrtL0 (hb : ℕ → ℚ) (E : ℚ) (π : ℕ → ℚ) :
    ((sqrtL0Q uq n hb E π : ℚ) : ℝ) = sqrtL0 p n (fun i => (hb i : ℝ)) E (fun i => (π i : ℝ)) := by
  simp [sqrtL0Q, sqrtL0, cast_sqrtZc p n h, cast_sqrtPg p n h]

theorem cast_sqrtEc (hb : ℕ → ℚ) (E : ℚ) (π : ℕ → ℚ) :
    ((sqrtEcQ uq n hb E π : ℚ) : ℝ) = sqrtEc p n (fun i => (hb i : ℝ)) E (fun i => (π i : ℝ)) := by
  have hP : (fun i => ((sqrtPgQ uq n hb E π i : ℚ) : ℝ)) = sqrtPg p n (fun i => (hb i : ℝ)) E (fun i => (π i : ℝ)) :=
    funext (cast_sqrtPg p n h hb E π)
  simp only [sqrtEcQ, sqrtEc, cast_GaddfE' p n h, hP, cast_sqrtL0 p n h, cast_sqrtZc p n h]

theorem cast_sqrtChi (hb : ℕ → ℚ) (E : ℚ) (π : ℕ → ℚ) (i : ℕ) :
    ((sqrtChiQ uq n hb E π i : ℚ) : ℝ) = sqrtChi p n (fun i => (hb i : ℝ)) E (fun i => (π i : ℝ)) i := by
  have hP : (fun i => ((sqrtPgQ uq n hb E π i : ℚ) : ℝ)) = sqrtPg p n (fun i => (hb i : ℝ)) E (fun i => (π i : ℝ)) :=
    funext (cast_sqrtPg p n h hb E π)
  simp only [sqrtChiQ, sqrtChi, cast_GaddfP' p n h, hP, cast_sqrtL0 p n h, cast_sqrtZc p n h]

/-- the Newton step's `(E, π)`, cast: both components -/
theorem cast_sqrtB (hb : ℕ → ℚ) (E : ℚ) (π : ℕ → ℚ) :
    (((sqrtBQ uq n hb E π).1 : ℚ) : ℝ) = (sqrtB p n (fun i => (hb i : ℝ)) E (fun i => (π i : ℝ))).1 ∧
      ∀ i, (((sqrtBQ uq n hb E π).2 i : ℚ) : ℝ) = (sqrtB p n (fun i => (hb i : ℝ)) E (fun i => (π i : ℝ))).2 i := by
  have hχ : (fun i => ((sqrtChiQ uq n hb E π i : ℚ) : ℝ)) =
      sqrtChi p n (fun i => (hb i : ℝ)) E (fun i => (π i : ℝ)) := funext (cast_sqrtChi p n h hb E π)
  have hδ : ∀ Z : ℚ, (fun i => ((GmulPQ uq n (sqrtChiQ uq n hb E π) π Z i : ℚ) : ℝ)) =
      GmulP p n (sqrtChi p n (fun i => (hb i : ℝ)) E (fun i => (π i : ℝ))) (fun i => (π i : ℝ)) Z := fun Z => by
    funext i
    rw [cast_GmulP p n h, hχ]
  refine ⟨?_, fun i => ?_⟩
  · simp only [sqrtBQ, sqrtB]
    push_cast [cast_GaddE p n h, cast_GmulE p n h, hχ, hδ, cast_sqrtEm p n h, cast_sqrtEg p n h, cast_sqrtEc p n h,
      cast_sqrtZc p n h]
    rfl
  · simp only [sqrtBQ, sqrtB]
    rw [cast_GaddP p n h, hδ]
    push_cast [cast_GmulE p n h, hχ, cast_sqrtEc p n h, cast_sqrtZc p n h]
    rfl

omit h in
theorem cast_abar (ρ : ℚ) (i : ℕ) : ((abarQ ρ i : ℚ) : ℝ) = abar ρ i := by
  simp [abarQ, abar]

theorem cast_sqrtE0 (ρ : ℚ) : ((sqrtE0Q uq ρ : ℚ) : ℝ) = sqrtE0 p ρ := by
  simp [sqrtE0Q, sqrtE0, Rat.cast_max, h]

omit h in
/-- `ā/2`, cast -/
theorem cast_hbar (ρ : ℚ) : (fun i => ((abarQ ρ i / 2 : ℚ) : ℝ)) = fun i => abar (ρ : ℝ) i / 2 := by
  funext i
  simp [cast_abar]

theorem cast_sqrtBk (ρ : ℚ) : ∀ k, (((sqrtBkQ uq n ρ k).1 : ℚ) : ℝ) = (sqrtBk p n ρ k).1 ∧
    ∀ i, (((sqrtBkQ uq n ρ k).2 i : ℚ) : ℝ) = (sqrtBk p n ρ k).2 i
  | 0 => by
    refine ⟨by simp [sqrtBkQ, sqrtBk, cast_sqrtE0 p h], fun i => ?_⟩
    simp only [sqrtBkQ, sqrtBk]
    split_ifs <;> simp [cast_sqrtE0 p h]
  | k + 1 => by
    obtain ⟨i1, i2⟩ := cast_sqrtBk ρ k
    have hπ : (fun i => (((sqrtBkQ uq n ρ k).2 i : ℚ) : ℝ)) = (sqrtBk p n ρ k).2 := funext i2
    obtain ⟨s1, s2⟩ := cast_sqrtB p n h (fun i => abarQ ρ i / 2) (sqrtBkQ uq n ρ k).1 (sqrtBkQ uq n ρ k).2
    rw [cast_hbar, i1, hπ] at s1 s2
    exact ⟨s1, s2⟩

/-- `sqrtDeltaQ`, cast to `ℝ`, is `δ_J` -/
theorem cast_sqrtDelta (ρ : ℚ) (J : ℕ) : ((sqrtDeltaQ uq n ρ J : ℚ) : ℝ) = sqrtDelta p n ρ J := by
  obtain ⟨i1, i2⟩ := cast_sqrtBk p n h ρ J
  have hπ : (fun i => (((sqrtBkQ uq n ρ J).2 i : ℚ) : ℝ)) = (sqrtBk p n ρ J).2 := funext i2
  have ha : (fun i => ((abarQ ρ i : ℚ) : ℝ)) = abar (ρ : ℝ) := funext (cast_abar ρ)
  simp only [sqrtDeltaQ, sqrtDelta, Rat.cast_add, cast_GmulE p n h, i1, hπ, ha, Rat.cast_one]

theorem cast_ddEta1 : ((ddEta1Q uq : ℚ) : ℝ) = ddEta1 p := by
  simp [ddEta1Q, ddEta1, h]

theorem cast_ddEta2 : ((ddEta2Q uq : ℚ) : ℝ) = ddEta2 p := by
  simp [ddEta2Q, ddEta2, h]

omit h in
theorem cast_ddEta3 (ρ : ℚ) : ((ddEta3Q ρ : ℚ) : ℝ) = ddEta3 ρ := by
  simp [ddEta3Q, ddEta3]

theorem cast_ddE0 (ρ : ℚ) : ((ddE0Q uq ρ : ℚ) : ℝ) = ddE0 p ρ := by
  simp [ddE0Q, ddE0, Rat.cast_max, cast_ddEta1 p h, cast_ddEta2 p h, cast_ddEta3]

theorem cast_ddPi0 (ρ : ℚ) (i : ℕ) : ((ddPi0Q uq ρ i : ℚ) : ℝ) = ddPi0 p ρ i := by
  simp only [ddPi0Q, ddPi0]
  split_ifs <;> simp [cast_ddE0 p h, h]

/-- the second-order step's `(E, π)`, cast: both components -/
theorem cast_sqrtB2 (hb : ℕ → ℚ) (E : ℚ) (π : ℕ → ℚ) :
    (((sqrtB2Q uq n hb E π).1 : ℚ) : ℝ) = (sqrtB2 p n (fun i => (hb i : ℝ)) E (fun i => (π i : ℝ))).1 ∧
      ∀ i, (((sqrtB2Q uq n hb E π).2 i : ℚ) : ℝ) = (sqrtB2 p n (fun i => (hb i : ℝ)) E (fun i => (π i : ℝ))).2 i := by
  have hχ : (fun i => ((sqrtChiQ uq n hb E π i : ℚ) : ℝ)) =
      sqrtChi p n (fun i => (hb i : ℝ)) E (fun i => (π i : ℝ)) := funext (cast_sqrtChi p n h hb E π)
  refine ⟨?_, fun i => ?_⟩
  · simp only [sqrtB2Q, sqrtB2]
    push_cast [cast_GaddE p n h, cast_GaddP p n h, cast_GmulE p n h, cast_GmulP p n h, hχ, cast_sqrtEm p n h,
      cast_sqrtEg p n h, cast_sqrtEc p n h, cast_sqrtZc p n h]
    try rfl
  · simp only [sqrtB2Q, sqrtB2]
    push_cast [cast_GaddE p n h, cast_GaddP p n h, cast_GmulE p n h, cast_GmulP p n h, hχ, cast_sqrtEm p n h,
      cast_sqrtEg p n h, cast_sqrtEc p n h, cast_sqrtZc p n h]
    try rfl

/-- the second-order step from SQRT^DD's start, cast: both components -/
theorem cast_ddB2 (ρ : ℚ) :
    (((sqrtB2Q uq n (fun i => abarQ ρ i / 2) (ddE0Q uq ρ) (ddPi0Q uq ρ)).1 : ℚ) : ℝ) =
        (sqrtB2 p n (fun i => abar (ρ : ℝ) i / 2) (ddE0 p ρ) (ddPi0 p ρ)).1 ∧
      ∀ i, (((sqrtB2Q uq n (fun i => abarQ ρ i / 2) (ddE0Q uq ρ) (ddPi0Q uq ρ)).2 i : ℚ) : ℝ) =
        (sqrtB2 p n (fun i => abar (ρ : ℝ) i / 2) (ddE0 p ρ) (ddPi0 p ρ)).2 i := by
  have hπ0 : (fun i => ((ddPi0Q uq ρ i : ℚ) : ℝ)) = ddPi0 p ρ := funext (cast_ddPi0 p h ρ)
  obtain ⟨b1, b2⟩ := cast_sqrtB2 p n h (fun i => abarQ ρ i / 2) (ddE0Q uq ρ) (ddPi0Q uq ρ)
  rw [cast_hbar, cast_ddE0 p h, hπ0] at b1 b2
  exact ⟨b1, b2⟩

/-- `ddE1Q`, cast to `ℝ`, is `E_1` of SQRT^DD -/
theorem cast_ddE1 (ρ : ℚ) :
    ((ddE1Q uq n ρ : ℚ) : ℝ) = (sqrtB2 p n (fun i => abar (ρ : ℝ) i / 2) (ddE0 p ρ) (ddPi0 p ρ)).1 :=
  (cast_ddB2 p n h ρ).1

/-- `ddDeltaQ`, cast to `ℝ`, is `δ^DD` -/
theorem cast_ddDelta (ρ : ℚ) : ((ddDeltaQ uq n ρ : ℚ) : ℝ) = ddDelta p n ρ := by
  have ha : (fun i => ((abarQ ρ i : ℚ) : ℝ)) = abar (ρ : ℝ) := funext (cast_abar ρ)
  obtain ⟨b1, b2⟩ := cast_ddB2 p n h ρ
  have hπ1 := funext b2
  obtain ⟨s1, s2⟩ := cast_sqrtB p n h (fun i => abarQ ρ i / 2)
    (sqrtB2Q uq n (fun i => abarQ ρ i / 2) (ddE0Q uq ρ) (ddPi0Q uq ρ)).1
    (sqrtB2Q uq n (fun i => abarQ ρ i / 2) (ddE0Q uq ρ) (ddPi0Q uq ρ)).2
  rw [cast_hbar, b1, hπ1] at s1 s2
  have hπ2 := funext s2
  simp only [ddDeltaQ, ddDelta, Rat.cast_add, cast_GmulE p n h, s1, hπ2, ha, Rat.cast_one]

end Casts

end ExpansionBounds
