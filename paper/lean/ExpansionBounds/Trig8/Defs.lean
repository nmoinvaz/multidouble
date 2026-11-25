import ExpansionBounds.Dyadic
import ExpansionBounds.TrigEval
import ExpansionBounds.Trig8.Data

/-!
# Theorem 35 at `n = 8` and `p = 53`: what the kernel evaluates

The octo-double sine and cosine: the series' coefficients `trig8Fs` and `trig8Fc` and their lengths by bucket
(`Trig8/Data.lean`, multidouble's tables), `r̄_j` of Lemma 32's buckets, and Lemma 34's bounds rounded up to 200 bits.
Horner's run is checked in pieces of a few steps against stored states (`Trig8/Run0.lean` to `Run7.lean`), and
`trig8Ok` is what remains to check on the last state of a run.
-/

namespace ExpansionBounds

open Finset

/-- `u = 2^{-53}` -/
def trig8U : ℚ := 1 / 9007199254740992

/-- `ā_i = (2u)^i(1 - 2u)/(1 - 4u)`, the part bounds of `r` on `H(2)` in units of `|r|` -/
def trig8Ab : ℕ → ℚ := abarQ (2 * trig8U)

/-- the parts of SINR's coefficient `k` -/
def trig8FsQ (k i : ℕ) : ℚ := dyFn (trig8Fs.getD k []) i

/-- the parts of COSR's coefficient `k` -/
def trig8FcQ (k i : ℕ) : ℚ := dyFn (trig8Fc.getD k []) i

/-- `r̄_j` of Lemma 32: `0.78541` in the top bucket and `2^{-j}(1 + 2^{-50})` below -/
def trig8Rb (j : ℕ) : ℚ := if j = 0 then 78541 / 100000 else 1 / 2 ^ j * (1 + 1 / 2 ^ 50)

/-- a state of Horner's run, from dyadic pairs -/
def dySt (st : (ℤ × ℕ) × List (ℤ × ℕ)) : ℚ × List ℚ := (dyQ st.1, st.2.map dyQ)

/-- Horner's run for the coefficients `F_k` of `C_k` in bucket `j`, rounded to 200 bits -/
abbrev trig8Run (C : ℕ → ℚ) (Fk : ℕ → ℕ → ℚ) (j d a m : ℕ) (st : ℚ × List ℚ) : ℚ × List ℚ :=
  hornerRunL trig8U 8 (upQ 200) (fun i => trig8Rb j ^ 2 * scZetaU trig8U 8 (upQ 200) trig8Ab i) (trig8Rb j ^ 2)
    (scEzU trig8U 8 (upQ 200) trig8Ab) 0 Fk (fun k => |∑ i ∈ range 8, Fk k i - C k|) (fun k => |C k|) d a m st

/-- the start of Horner's run -/
abbrev trig8Init (C : ℕ → ℚ) (Fk : ℕ → ℕ → ℚ) (d : ℕ) : ℚ × List ℚ :=
  hornerInitL 8 Fk (fun k => |∑ i ∈ range 8, Fk k i - C k|) d

/-- two pieces of a run make one -/
theorem trig8Run_cut (C : ℕ → ℚ) (Fk : ℕ → ℕ → ℚ) (j d a m1 m2 : ℕ) {st st1 st2 : ℚ × List ℚ}
    (h1 : trig8Run C Fk j d a m1 st = st1) (h2 : trig8Run C Fk j d (a + m1) m2 st1 = st2) :
    trig8Run C Fk j d a (m1 + m2) st = st2 := by
  unfold trig8Run at *
  rw [hornerRunL_add, h1, h2]

/-- the bound `3.163167393u^8` of Theorem 35 at `n = 8`, with `δ_S, δ_C ≤ 1/2`, from the last states of Horner's
runs for the sine and the cosine in bucket `j`, whose `r̄` is at most `0.8` with `cos₋ r̄ > 0` -/
def trig8Ok (j Ks Kc : ℕ) (sS sC : ℚ × List ℚ) : Prop :=
  sinDeltaL trig8U 8 (upQ 200) trig8Ab (trig8Rb j) Ks sS ≤ 1 / 2 ∧
    cosDeltaL trig8U 8 (upQ 200) trig8Ab (trig8Rb j) Kc sC ≤ 1 / 2 ∧
    trigCQ trig8U 8 (sinDeltaL trig8U 8 (upQ 200) trig8Ab (trig8Rb j) Ks sS)
      (cosDeltaL trig8U 8 (upQ 200) trig8Ab (trig8Rb j) Kc sC) (trig8Rb j) ≤ 3163167393 / 1000000000 * trig8U ^ 8 ∧
    trig8Rb j ≤ 8 / 10 ∧ 0 < cosLoQ (trig8Rb j)

instance (j Ks Kc : ℕ) (sS sC : ℚ × List ℚ) : Decidable (trig8Ok j Ks Kc sS sC) := by
  unfold trig8Ok
  infer_instance

/-- bucket `j`, with series of `K_s` and `K_c` terms: Horner's runs end in states on which `trig8Ok` holds -/
def Trig8Group (g : ℕ × ℕ × ℕ) : Prop :=
  ∃ sS sC, trig8Run sinCQ trig8FsQ g.1 (g.2.1 - 1) 0 (g.2.1 - 2) (trig8Init sinCQ trig8FsQ (g.2.1 - 1)) = sS ∧
    trig8Run cosCQ trig8FcQ g.1 (g.2.2 - 1) 0 (g.2.2 - 2) (trig8Init cosCQ trig8FcQ (g.2.2 - 1)) = sC ∧
    trig8Ok g.1 g.2.1 g.2.2 sS sC

end ExpansionBounds
