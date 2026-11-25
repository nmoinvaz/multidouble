import ExpansionBounds.DivEval
import ExpansionBounds.TanEval
import ExpansionBounds.Trig8.All

/-!
# Theorem 35 for the tangent at `n = 8` and `p = 53`: what the kernel evaluates

The quotient of the computed sine and cosine needs them on a ladder `H(θ)`: `θ = 1.4143` serves in the top bucket and
`θ = 3` below it, with `κ_DIV(θu)` at most `103232124` and `461400803` (`tan8_kdiv`). `tan8Chk` is what remains to
check from bounds on `δ_S`, `δ_C` and on the parts of SINR's and COSR's results, and `tan8Ok` is `tan8Chk` on the last
states of Horner's runs, which `Trig8/Run0.lean` to `Run7.lean` check.
-/

namespace ExpansionBounds

open Finset

/-- the quotient's ladder `H(θ)`: `θ = 1.4143` in the top bucket and `3` below -/
def tan8Th (j : ℕ) : ℚ := if j = 0 then 14143 / 10000 else 3

/-- a bound on `κ_DIV(θu)` at those `θ` -/
def tan8Kd (j : ℕ) : ℚ := if j = 0 then 103232124 else 461400803

/-- from bounds `δ_S`, `δ_C`, `ψ_s` and `ψ_c` at `r̄ ≤ 0.8` with `cos₋ r̄ > 0`: `δ_S, δ_C ≤ 1/10`, the leading parts of
the computed sine and cosine are at least `λ_s, λ_c > 0` and their parts within `(θu)^i λ`, and `C^T` with
`δ_D = u^8 + K_d u^9` is at most `6.418350521u^8` -/
def tan8Chk (rb dS dC : ℚ) (ψs ψc : ℕ → ℚ) (θ Kd : ℚ) : Prop :=
  rb ≤ 8 / 10 ∧ 0 < cosLoQ rb ∧ dS ≤ 1 / 10 ∧ dC ≤ 1 / 10 ∧
    0 < (1 - rb ^ 2 / 6) * (1 - dS) - ∑ i ∈ Ico 1 8, ψs i ∧
    (∀ i ∈ Ico 1 8, ψs i ≤ (θ * trig8U) ^ i * ((1 - rb ^ 2 / 6) * (1 - dS) - ∑ i ∈ Ico 1 8, ψs i)) ∧
    0 < cosLoQ rb * (1 - dC) - ∑ i ∈ Ico 1 8, ψc i ∧
    (∀ i ∈ Ico 1 8, ψc i ≤ (θ * trig8U) ^ i * (cosLoQ rb * (1 - dC) - ∑ i ∈ Ico 1 8, ψc i)) ∧
    tanCTQ trig8U 8 dS dC (trig8U ^ 8 + Kd * trig8U ^ 9) rb ≤ 6418350521 / 1000000000 * trig8U ^ 8

instance (rb dS dC : ℚ) (ψs ψc : ℕ → ℚ) (θ Kd : ℚ) : Decidable (tan8Chk rb dS dC ψs ψc θ Kd) := by
  unfold tan8Chk
  infer_instance

/-- `tan8Chk` in bucket `j`, from the last states of Horner's runs for the sine and the cosine -/
def tan8Ok (j Ks Kc : ℕ) (sS sC : ℚ × List ℚ) : Prop :=
  tan8Chk (trig8Rb j) (sinDeltaL trig8U 8 (upQ 200) trig8Ab (trig8Rb j) Ks sS)
    (cosDeltaL trig8U 8 (upQ 200) trig8Ab (trig8Rb j) Kc sC)
    (sinPsiL trig8U 8 (upQ 200) trig8Ab (trig8Rb j) Ks sS) (cosPsiL trig8U 8 (upQ 200) trig8Ab (trig8Rb j) Kc sC)
    (tan8Th j) (tan8Kd j)

instance (j Ks Kc : ℕ) (sS sC : ℚ × List ℚ) : Decidable (tan8Ok j Ks Kc sS sC) := by
  unfold tan8Ok
  infer_instance

/-- bucket `j`, with series of `K_s` and `K_c` terms: Horner's runs end in states on which `tan8Ok` holds -/
def Tan8Group (g : ℕ × ℕ × ℕ) : Prop :=
  ∃ sS sC, trig8Run sinCQ trig8FsQ g.1 (g.2.1 - 1) 0 (g.2.1 - 2) (trig8Init sinCQ trig8FsQ (g.2.1 - 1)) = sS ∧
    trig8Run cosCQ trig8FcQ g.1 (g.2.2 - 1) 0 (g.2.2 - 2) (trig8Init cosCQ trig8FcQ (g.2.2 - 1)) = sC ∧
    tan8Ok g.1 g.2.1 g.2.2 sS sC

set_option maxHeartbeats 4000000 in
/-- `κ_DIV(θu)` at `n = 8` for the two ladders, and `δ_D ≤ 1/10` -/
theorem tan8_kdiv : (0 ≤ kdivQ trig8U 8 (14143 / 10000 * trig8U) ∧ kdivQ trig8U 8 (14143 / 10000 * trig8U) ≤ 103232124) ∧
    (0 ≤ kdivQ trig8U 8 (3 * trig8U) ∧ kdivQ trig8U 8 (3 * trig8U) ≤ 461400803) ∧
    trig8U ^ 8 + 461400803 * trig8U ^ 9 ≤ 1 / 10 := by
  decide +kernel

end ExpansionBounds
