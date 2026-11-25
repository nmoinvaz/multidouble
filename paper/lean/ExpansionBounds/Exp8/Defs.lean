import ExpansionBounds.Trig8.Defs
import ExpansionBounds.ExpEval
import ExpansionBounds.Exp8.Data

/-!
# Theorem 40 at `n = 8` and `p = 53`: what the kernel evaluates

The octo-double exponential, `EXP_{8,6,43}`: the coefficients `F_k` (`Exp8/Data.lean`, multidouble's table) and, for
a group of exponents `e` of step (2) with the same `m` and degree `d'`, the bound of a case rounded up to 200 bits.
Horner's run and step (3)'s products and sum are evaluated once for a group, at bounds `p_q` and `b_T` of `π'` and
`b'` for its largest `|r|` (`Exp8Head`), in pieces checked against stored states (`Exp8/Run0.lean` to `Run11.lean`).
For each interval `[a, b]` of `|r|` and each sign, `Exp8Bin` is the squarings and the bound `3.661u^8`.
-/

namespace ExpansionBounds

open Finset

/-- the parts of `F_k`, the greedy eight parts of `1/k!` -/
def exp8F (k i : ℕ) : ℚ := dyFn (exp8Fact.getD k []) i

/-- `φ_k = |∑_i F_{k,i} - 1/k!|` -/
def exp8Phi (k : ℕ) : ℚ := |∑ i ∈ range 8, exp8F k i - 1 / (k.factorial : ℚ)|

/-- `η_0 = 2^{-1075}` -/
def exp8Eta : ℚ := 1 / 2 ^ 1075

/-- `η_0[m > 0]` -/
def exp8Eta1 (m : ℕ) : ℚ := if m = 0 then 0 else exp8Eta

/-- step (3)'s degree for `|r'| < 2^{e'+1}`: `min(43, ⌈436/(-e' - 1)⌉)` for `e' ≥ -437`, and 1 below -/
def exp8Deg (e' : ℤ) : ℕ := if e' < -437 then 1 else min 43 ((436 + (-e' - 1) - 1) / (-e' - 1)).toNat

/-- `δ`: zero for `k = 0`, and the bound of `δ*` otherwise -/
def exp8Delta (k0 : Bool) : ℚ := if k0 then 0 else dyQ exp8DeltaS

/-- the bound of `|r|` -/
def exp8Top (k0 : Bool) : ℚ := if k0 then dyQ exp8Top0 else dyQ exp8Top1

/-- the bound of `∑_{i ≥ 1} |r_i|` -/
def exp8Tail (k0 : Bool) : ℚ := if k0 then dyQ exp8Tail0 else dyQ exp8Tail1

/-- the part bounds of `r` with `|r| ≤ hi`: on `H(2)` for `k = 0`, and Lemma 38's `π^r` at `r̄ = hi + δ*` otherwise -/
def exp8Pi (k0 : Bool) (hi : ℚ) (i : ℕ) : ℚ :=
  if k0 then abarQ (2 * red8U) i * hi else red8Pi (hi + dyQ exp8DeltaS) i

/-- the state after step (3)'s first product, from dyadic pairs -/
def dyStW (st : ((ℤ × ℕ) × (ℤ × ℕ)) × List (ℤ × ℕ)) : (ℚ × ℚ) × List ℚ :=
  ((dyQ st.1.1, dyQ st.1.2), st.2.map dyQ)

/-- Horner's run on the `F_k`, rounded to 200 bits -/
abbrev exp8Run (pq : List ℚ) (bp : ℚ) (d a m : ℕ) (st : ℚ × List ℚ) : ℚ × List ℚ :=
  hornerRunL red8U 8 (upQ 200) (fun i => pq.getD i 0) bp 0 0 exp8F exp8Phi (coreVQ bp) d a m st

/-- two pieces of a run make one -/
theorem exp8Run_cut (pq : List ℚ) (bp : ℚ) (d a m1 m2 : ℕ) {st st1 st2 : ℚ × List ℚ}
    (h1 : exp8Run pq bp d a m1 st = st1) (h2 : exp8Run pq bp d (a + m1) m2 st1 = st2) :
    exp8Run pq bp d a (m1 + m2) st = st2 := by
  unfold exp8Run at *
  rw [hornerRunL_add, h1, h2]

/-- step (3) for `d' ≠ 1`: Horner's run, then the two products and the sum, give the state `st0` -/
def Exp8HeadH (pos : Bool) (m d : ℕ) (pq : List ℚ) (bp : ℚ) (st0 : ℚ × List ℚ) : Prop :=
  expTL red8U 8 (upQ 200) (fun i => pq.getD i 0) (coreTQ (upQ 200) pos bp 0) exp8Eta
    (expYL red8U 8 (upQ 200) (fun i => pq.getD i 0) bp (2 * ((8 : ℕ) : ℚ) * exp8Eta1 m) d
      (expWL red8U 8 (upQ 200) (fun i => pq.getD i 0) bp
        (exp8Run pq bp d 0 (d - 2) (hornerInitL 8 exp8F exp8Phi d)))) = st0

theorem exp8HeadH_mk {pos : Bool} {m d : ℕ} {pq : List ℚ} {bp : ℚ} {st0 sH sY : ℚ × List ℚ}
    {sW : (ℚ × ℚ) × List ℚ} (hH : exp8Run pq bp d 0 (d - 2) (hornerInitL 8 exp8F exp8Phi d) = sH)
    (hW : expWL red8U 8 (upQ 200) (fun i => pq.getD i 0) bp sH = sW)
    (hY : expYL red8U 8 (upQ 200) (fun i => pq.getD i 0) bp (2 * ((8 : ℕ) : ℚ) * exp8Eta1 m) d sW = sY)
    (hT : expTL red8U 8 (upQ 200) (fun i => pq.getD i 0) (coreTQ (upQ 200) pos bp 0) exp8Eta sY = st0) :
    Exp8HeadH pos m d pq bp st0 := by
  unfold Exp8HeadH
  rw [hH, hW, hY, hT]

/-- the state `(E_0, ψ_0)` of a group and a sign -/
def Exp8Head (pos : Bool) (m d : ℕ) (pq : List ℚ) (bp : ℚ) (st0 : ℚ × List ℚ) : Prop :=
  if d = 1 then st0 = (eTrQ bp 1 + 2 * ((8 : ℕ) : ℚ) * exp8Eta1 m, pq) else Exp8HeadH pos m d pq bp st0

theorem exp8Head_of_ne {pos : Bool} {m d : ℕ} {pq : List ℚ} {bp : ℚ} {st0 : ℚ × List ℚ} (hd : d ≠ 1)
    (h : Exp8HeadH pos m d pq bp st0) : Exp8Head pos m d pq bp st0 := by
  simp only [Exp8Head, hd, ↓reduceIte]
  exact h

theorem exp8Head_one (pos : Bool) (m : ℕ) (pq : List ℚ) (bp : ℚ) :
    Exp8Head pos m 1 pq bp (eTrQ bp 1 + 2 * ((8 : ℕ) : ℚ) * exp8Eta1 m, pq) := by
  simp only [Exp8Head, ↓reduceIte]

/-- `p_q` and `b_T` bound `π'` and `b'` of a group whose `|r|` is at most `hi` and whose exponents are at most
`e_hi` -/
def Exp8Par (k0 : Bool) (m : ℕ) (eHi : ℤ) (hi : ℚ) (pq : List ℚ) (bpT : ℚ) : Prop :=
  (∀ i < 8, (2 : ℚ) ^ (-(m : ℤ)) * min (exp8Pi k0 hi i) ((2 : ℚ) ^ (eHi + 1)) + exp8Eta1 m ≤ pq.getD i 0) ∧
    (∀ q ∈ pq, 0 ≤ q) ∧
    (2 : ℚ) ^ (-(m : ℤ)) * min hi ((2 : ℚ) ^ (eHi + 1)) + ((8 : ℕ) : ℚ) * exp8Eta1 m ≤ bpT ∧ bpT < 1

instance (k0 : Bool) (m : ℕ) (eHi : ℤ) (hi : ℚ) (pq : List ℚ) (bpT : ℚ) : Decidable (Exp8Par k0 m eHi hi pq bpT) := by
  unfold Exp8Par
  infer_instance

/-- the squarings from pass `j` on follow the stored states -/
def exp8SqChk (pos : Bool) (ap bp : ℚ) : ℕ → ℚ × List ℚ → List (ℚ × List ℚ) → Bool
  | _, _, [] => true
  | j, st, s :: rest =>
    decide (expSqL red8U 8 (upQ 200) (coreTQ (upQ 200) pos bp j) (coreTQ (upQ 200) pos bp (j + 1))
      (coreGQ (upQ 200) pos ap bp j) st = s) && exp8SqChk pos ap bp (j + 1) s rest

theorem exp8SqChk_spec (pos : Bool) (ap bp : ℚ) : ∀ (l : List (ℚ × List ℚ)) (j : ℕ) (st : ℚ × List ℚ),
    exp8SqChk pos ap bp j st l = true → ∀ i < l.length,
      expSqL red8U 8 (upQ 200) (coreTQ (upQ 200) pos bp (j + i)) (coreTQ (upQ 200) pos bp (j + i + 1))
        (coreGQ (upQ 200) pos ap bp (j + i)) ((st :: l).getD i (0, [])) = (st :: l).getD (i + 1) (0, [])
  | [], _, _, _, i, hi => absurd hi (by simp)
  | s :: rest, j, st, hc, i, hi => by
    simp only [exp8SqChk, Bool.and_eq_true, decide_eq_true_eq] at hc
    cases i with
    | zero => simpa using hc.1
    | succ i =>
      have h := exp8SqChk_spec pos ap bp rest (j + 1) s hc.2 i (by simpa using hi)
      rw [show j + (i + 1) = j + 1 + i by omega]
      simpa using h

/-- an interval `[a, b]` of `|r|` and a sign: from `(E_0, ψ_0)`'s state the `m` squarings follow the stored states,
at a bound `b_B` of `b'` that is at most the group's `b_T`, and the bound of the case on the last is at most
`3.661u^8` -/
def Exp8Bin (pos : Bool) (m : ℕ) (eHi : ℤ) (δ a b bpB bpT : ℚ) (st0 : ℚ × List ℚ) (l : List (ℚ × List ℚ)) :
    Prop :=
  l.length = m ∧ 0 ≤ a ∧ a ≤ b ∧ b + δ ≤ 1 ∧
    (2 : ℚ) ^ (-(m : ℤ)) * min b ((2 : ℚ) ^ (eHi + 1)) + ((8 : ℕ) : ℚ) * exp8Eta1 m ≤ bpB ∧ bpB ≤ bpT ∧
    2 ^ m * bpB ≤ 1 ∧
    exp8SqChk pos ((2 : ℚ) ^ (-(m : ℤ)) * a) bpB 0 st0 l = true ∧
    0 < (if pos then expLoQ (a - δ) else expLoQ (-b - δ)) ∧
    expEpsL red8U 8 (upQ 200 (if pos then expUpQ b else expUpQ (-a)))
      (if pos then expLoQ (a - δ) else expLoQ (-b - δ)) (expUpQ δ - 1) ((st0 :: l).getD m (0, [])) ≤
      3661 / 1000 * red8U ^ 8

instance (pos : Bool) (m : ℕ) (eHi : ℤ) (δ a b bpB bpT : ℚ) (st0 : ℚ × List ℚ) (l : List (ℚ × List ℚ)) :
    Decidable (Exp8Bin pos m eHi δ a b bpB bpT st0 l) := by
  unfold Exp8Bin
  infer_instance

/-- the intervals of a list follow each other from `lo` to `hi` -/
def exp8ChainB : ℚ → ℚ → List (ℚ × ℚ) → Bool
  | lo, hi, [] => decide (lo = hi)
  | lo, hi, ab :: rest => decide (ab.1 = lo) && exp8ChainB ab.2 hi rest

/-- intervals that follow each other from `lo` to `hi` cover `[lo, hi]` -/
theorem exp8Chain_cover : ∀ (l : List (ℚ × ℚ)) (lo hi : ℚ), exp8ChainB lo hi l = true → l ≠ [] →
    ∀ y : ℝ, ((lo : ℚ) : ℝ) ≤ y → y ≤ ((hi : ℚ) : ℝ) → ∃ ab ∈ l, ((ab.1 : ℚ) : ℝ) ≤ y ∧ y ≤ ((ab.2 : ℚ) : ℝ)
  | [], _, _, _, hne, _, _, _ => absurd rfl hne
  | ab :: rest, lo, hi, hc, _, y, hlo, hhi => by
    simp only [exp8ChainB, Bool.and_eq_true, decide_eq_true_eq] at hc
    by_cases hy : y ≤ ((ab.2 : ℚ) : ℝ)
    · exact ⟨ab, List.mem_cons_self, by rw [hc.1]; exact hlo, hy⟩
    · rcases rest with _ | ⟨ab', rest'⟩
      · simp only [exp8ChainB, decide_eq_true_eq] at hc
        rw [hc.2] at hy
        exact absurd hhi hy
      · obtain ⟨c, hcm, hc1, hc2⟩ := exp8Chain_cover (ab' :: rest') ab.2 hi hc.2 (by simp) y
          (le_of_lt (not_le.mp hy)) hhi
        exact ⟨c, List.mem_cons_of_mem _ hcm, hc1, hc2⟩

/-- what the kernel checks for a group `(m, d', e_lo, e_hi, lo, hi)`, for `k = 0` or not: bounds `p_q` and `b_T`,
`(E_0, ψ_0)`'s state for each sign, and at least one interval, the intervals following each other from `lo` to
`hi`, each with `Exp8Bin` for both signs -/
def Exp8Group (k0 : Bool) (g : ℕ × ℕ × ℤ × ℤ × (ℤ × ℕ) × (ℤ × ℕ)) : Prop :=
  ∃ (pq : List ℚ) (bpT : ℚ) (sp sn : ℚ × List ℚ)
    (bins : List ((ℚ × ℚ) × ℚ × List (ℚ × List ℚ) × List (ℚ × List ℚ))),
    Exp8Par k0 g.1 g.2.2.2.1 (dyQ g.2.2.2.2.2) pq bpT ∧ Exp8Head true g.1 g.2.1 pq bpT sp ∧
      Exp8Head false g.1 g.2.1 pq bpT sn ∧ bins ≠ [] ∧
      exp8ChainB (dyQ g.2.2.2.2.1) (dyQ g.2.2.2.2.2) (bins.map Prod.fst) = true ∧
      ∀ bn ∈ bins, Exp8Bin true g.1 g.2.2.2.1 (exp8Delta k0) bn.1.1 bn.1.2 bn.2.1 bpT sp bn.2.2.1 ∧
        Exp8Bin false g.1 g.2.2.2.1 (exp8Delta k0) bn.1.1 bn.1.2 bn.2.1 bpT sn bn.2.2.2

end ExpansionBounds
