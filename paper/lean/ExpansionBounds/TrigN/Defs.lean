import ExpansionBounds.Tan8.Defs

/-!
# Theorem 35 at any `n` and `p = 53`: what the kernel evaluates

`Trig8/Defs.lean` and `Tan8/Defs.lean` for a table of any number of parts: the series' coefficients and their lengths
by bucket, Horner's run and the bounds that remain to check on its last state, for the sine and cosine (`Ok`) and for
the tangent (`TanOk`). The bucket bounds `r̄_j` (`trig8Rb`), the part bounds `ā` (`trig8Ab`) and the quotient's
ladders (`tan8Th`) do not depend on `n`; the bounds on `κ_DIV` do.
-/

namespace ExpansionBounds

open Finset

/-- the tables of SINR and COSR at `n` parts -/
structure TrigTab where
  /-- the number of parts -/
  n : ℕ
  /-- the parts of SINR's coefficients, as dyadic pairs -/
  fs : List (List (ℤ × ℕ))
  /-- the parts of COSR's coefficients -/
  fc : List (List (ℤ × ℕ))
  /-- `(j, K_s, K_c)` for the first bucket `j` of each run of buckets with the same series lengths -/
  groups : List (ℕ × ℕ × ℕ)

namespace TrigTab

variable (T : TrigTab)

/-- the parts of SINR's coefficient `k` -/
def FsQ (k i : ℕ) : ℚ := dyFn (T.fs.getD k []) i

/-- the parts of COSR's coefficient `k` -/
def FcQ (k i : ℕ) : ℚ := dyFn (T.fc.getD k []) i

/-- Horner's run for the coefficients `F_k` of `C_k` in bucket `j`, rounded to 200 bits -/
abbrev run (C : ℕ → ℚ) (Fk : ℕ → ℕ → ℚ) (j d a m : ℕ) (st : ℚ × List ℚ) : ℚ × List ℚ :=
  hornerRunL trig8U T.n (upQ 200) (fun i => trig8Rb j ^ 2 * scZetaU trig8U T.n (upQ 200) trig8Ab i) (trig8Rb j ^ 2)
    (scEzU trig8U T.n (upQ 200) trig8Ab) 0 Fk (fun k => |∑ i ∈ range T.n, Fk k i - C k|) (fun k => |C k|) d a m st

/-- the start of Horner's run -/
abbrev init (C : ℕ → ℚ) (Fk : ℕ → ℕ → ℚ) (d : ℕ) : ℚ × List ℚ :=
  hornerInitL T.n Fk (fun k => |∑ i ∈ range T.n, Fk k i - C k|) d

/-- two pieces of a run make one -/
theorem run_cut (C : ℕ → ℚ) (Fk : ℕ → ℕ → ℚ) (j d a m1 m2 : ℕ) {st st1 st2 : ℚ × List ℚ}
    (h1 : T.run C Fk j d a m1 st = st1) (h2 : T.run C Fk j d (a + m1) m2 st1 = st2) :
    T.run C Fk j d a (m1 + m2) st = st2 := by
  unfold run at *
  rw [hornerRunL_add, h1, h2]

/-- the bound `c u^n` of Theorem 35, with `δ_S, δ_C ≤ 1/2`, from the last states of Horner's runs for the sine and the
cosine in bucket `j`, whose `r̄` is at most `0.8` with `cos₋ r̄ > 0` -/
def Ok (c : ℚ) (j Ks Kc : ℕ) (sS sC : ℚ × List ℚ) : Prop :=
  sinDeltaL trig8U T.n (upQ 200) trig8Ab (trig8Rb j) Ks sS ≤ 1 / 2 ∧
    cosDeltaL trig8U T.n (upQ 200) trig8Ab (trig8Rb j) Kc sC ≤ 1 / 2 ∧
    trigCQ trig8U T.n (sinDeltaL trig8U T.n (upQ 200) trig8Ab (trig8Rb j) Ks sS)
      (cosDeltaL trig8U T.n (upQ 200) trig8Ab (trig8Rb j) Kc sC) (trig8Rb j) ≤ c * trig8U ^ T.n ∧
    trig8Rb j ≤ 8 / 10 ∧ 0 < cosLoQ (trig8Rb j)

instance (c : ℚ) (j Ks Kc : ℕ) (sS sC : ℚ × List ℚ) : Decidable (T.Ok c j Ks Kc sS sC) := by
  unfold Ok
  infer_instance

/-- bucket `j`, with series of `K_s` and `K_c` terms: Horner's runs end in states on which `Ok` holds -/
def Group (c : ℚ) (g : ℕ × ℕ × ℕ) : Prop :=
  ∃ sS sC, T.run sinCQ T.FsQ g.1 (g.2.1 - 1) 0 (g.2.1 - 2) (T.init sinCQ T.FsQ (g.2.1 - 1)) = sS ∧
    T.run cosCQ T.FcQ g.1 (g.2.2 - 1) 0 (g.2.2 - 2) (T.init cosCQ T.FcQ (g.2.2 - 1)) = sC ∧
    T.Ok c g.1 g.2.1 g.2.2 sS sC

/-- the tables: at most `n` parts to a coefficient, every part in `F`, and series of at least two terms -/
def TabOk : Prop :=
  (∀ t ∈ T.fs, t.length ≤ T.n) ∧ (∀ t ∈ T.fc, t.length ≤ T.n) ∧
    (∀ t ∈ T.fs, ∀ q ∈ t, rnQ 53 (dyQ q) = dyQ q) ∧ (∀ t ∈ T.fc, ∀ q ∈ t, rnQ 53 (dyQ q) = dyQ q) ∧
    ∀ g ∈ T.groups, 2 ≤ g.2.1 ∧ 2 ≤ g.2.2

instance : Decidable T.TabOk := by
  unfold TabOk
  infer_instance

/-- `r̄` below the last bucket: `u^{n/2}(1 + 2^{-50})` -/
def tiny : ℚ := trig8U ^ (T.n / 2) * (1 + 1 / 2 ^ 50)

/-- below the last bucket SINR returns `r` and COSR `1`, within `r̄²/(6 - r̄²)` and `r̄²/(2cos₋ r̄)`, which with `C`
there are at most `c u^n` -/
def TinyOk (c : ℚ) : Prop :=
  T.tiny ≤ 8 / 10 ∧ T.tiny ^ 2 < 6 ∧ 0 < cosLoQ T.tiny ∧ T.tiny ^ 2 / (6 - T.tiny ^ 2) ≤ 1 / 2 ∧
    T.tiny ^ 2 / (2 * cosLoQ T.tiny) ≤ 1 / 2 ∧
    trigCQ trig8U T.n (T.tiny ^ 2 / (6 - T.tiny ^ 2)) (T.tiny ^ 2 / (2 * cosLoQ T.tiny)) T.tiny ≤ c * trig8U ^ T.n ∧
    T.tiny ^ 2 / (6 - T.tiny ^ 2) ≤ c * trig8U ^ T.n ∧ T.tiny ^ 2 / (2 * cosLoQ T.tiny) ≤ c * trig8U ^ T.n

instance (c : ℚ) : Decidable (T.TinyOk c) := by
  unfold TinyOk
  infer_instance

/-- a bound on `κ_DIV(θu)`: `kd0` at `θ = 1.4143`, in the top bucket, and `kd3` at `θ = 3`, below -/
def tanKd (kd0 kd3 : ℚ) (j : ℕ) : ℚ := if j = 0 then kd0 else kd3

/-- from bounds `δ_S`, `δ_C`, `ψ_s` and `ψ_c` at `r̄ ≤ 0.8` with `cos₋ r̄ > 0`: `δ_S, δ_C ≤ 1/10`, the leading parts of
the computed sine and cosine are at least `λ_s, λ_c > 0` and their parts within `(θu)^i λ`, and `C^T` with
`δ_D = u^n + K_d u^{n+1}` is at most `c u^n` -/
def TanChk (c rb dS dC : ℚ) (ψs ψc : ℕ → ℚ) (θ Kd : ℚ) : Prop :=
  rb ≤ 8 / 10 ∧ 0 < cosLoQ rb ∧ dS ≤ 1 / 10 ∧ dC ≤ 1 / 10 ∧
    0 < (1 - rb ^ 2 / 6) * (1 - dS) - ∑ i ∈ Ico 1 T.n, ψs i ∧
    (∀ i ∈ Ico 1 T.n, ψs i ≤ (θ * trig8U) ^ i * ((1 - rb ^ 2 / 6) * (1 - dS) - ∑ i ∈ Ico 1 T.n, ψs i)) ∧
    0 < cosLoQ rb * (1 - dC) - ∑ i ∈ Ico 1 T.n, ψc i ∧
    (∀ i ∈ Ico 1 T.n, ψc i ≤ (θ * trig8U) ^ i * (cosLoQ rb * (1 - dC) - ∑ i ∈ Ico 1 T.n, ψc i)) ∧
    tanCTQ trig8U T.n dS dC (trig8U ^ T.n + Kd * trig8U ^ (T.n + 1)) rb ≤ c * trig8U ^ T.n

instance (c rb dS dC : ℚ) (ψs ψc : ℕ → ℚ) (θ Kd : ℚ) : Decidable (T.TanChk c rb dS dC ψs ψc θ Kd) := by
  unfold TanChk
  infer_instance

/-- `TanChk` in bucket `j`, from the last states of Horner's runs for the sine and the cosine -/
def TanOk (c kd0 kd3 : ℚ) (j Ks Kc : ℕ) (sS sC : ℚ × List ℚ) : Prop :=
  T.TanChk c (trig8Rb j) (sinDeltaL trig8U T.n (upQ 200) trig8Ab (trig8Rb j) Ks sS)
    (cosDeltaL trig8U T.n (upQ 200) trig8Ab (trig8Rb j) Kc sC)
    (sinPsiL trig8U T.n (upQ 200) trig8Ab (trig8Rb j) Ks sS) (cosPsiL trig8U T.n (upQ 200) trig8Ab (trig8Rb j) Kc sC)
    (tan8Th j) (tanKd kd0 kd3 j)

instance (c kd0 kd3 : ℚ) (j Ks Kc : ℕ) (sS sC : ℚ × List ℚ) : Decidable (T.TanOk c kd0 kd3 j Ks Kc sS sC) := by
  unfold TanOk
  infer_instance

/-- bucket `j`, with series of `K_s` and `K_c` terms: Horner's runs end in states on which `TanOk` holds -/
def TanGroup (c kd0 kd3 : ℚ) (g : ℕ × ℕ × ℕ) : Prop :=
  ∃ sS sC, T.run sinCQ T.FsQ g.1 (g.2.1 - 1) 0 (g.2.1 - 2) (T.init sinCQ T.FsQ (g.2.1 - 1)) = sS ∧
    T.run cosCQ T.FcQ g.1 (g.2.2 - 1) 0 (g.2.2 - 2) (T.init cosCQ T.FcQ (g.2.2 - 1)) = sC ∧
    T.TanOk c kd0 kd3 g.1 g.2.1 g.2.2 sS sC

/-- `κ_DIV(θu)` at `n` for the two ladders is at most `kd0` and `kd3`, with `kd0 ≤ kd3` and `δ_D ≤ 1/10` -/
def KdivOk (kd0 kd3 : ℚ) : Prop :=
  (0 ≤ kdivQ trig8U T.n (14143 / 10000 * trig8U) ∧ kdivQ trig8U T.n (14143 / 10000 * trig8U) ≤ kd0) ∧
    (0 ≤ kdivQ trig8U T.n (3 * trig8U) ∧ kdivQ trig8U T.n (3 * trig8U) ≤ kd3) ∧
    trig8U ^ T.n + kd3 * trig8U ^ (T.n + 1) ≤ 1 / 10 ∧ kd0 ≤ kd3

instance (kd0 kd3 : ℚ) : Decidable (T.KdivOk kd0 kd3) := by
  unfold KdivOk
  infer_instance

/-- below the last bucket: `r` itself over `1`, on `H(3)`, and the early return within `tan₊ r̄/r̄ - 1`; `C^T` and the
early return's bound are at most `c u^n` -/
def TanTinyOk (c kd3 : ℚ) : Prop :=
  T.tiny ≤ 8 / 10 ∧ T.tiny ^ 2 < 6 ∧ 0 < cosLoQ T.tiny ∧
    T.TanChk c T.tiny (T.tiny ^ 2 / (6 - T.tiny ^ 2)) (T.tiny ^ 2 / (2 * cosLoQ T.tiny))
      (fun i => if i < T.n then trig8Ab i else 0) (fun i => if i = 0 then 1 else 0) 3 kd3 ∧
    tanHiQ T.tiny / T.tiny - 1 ≤ c * trig8U ^ T.n

instance (c kd3 : ℚ) : Decidable (T.TanTinyOk c kd3) := by
  unfold TanTinyOk
  infer_instance

end TrigTab

end ExpansionBounds
