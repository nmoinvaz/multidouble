import ExpansionBounds.Exp8.Defs
import ExpansionBounds.LogEvalLeaf
import ExpansionBounds.Log8.Data

/-!
# Theorem 42 at `n = 8` and `p = 53`: what the kernel evaluates

The octo-double logarithm, `LOG_{8,6,43,4}`, with the convex variant of the bound `𝓔` of a case (`logBoundC`) at an
end `ℓ` of an interval of `|ln x|`: the start's bound `E(ℓ) = e₀ + e₁ℓ` from the quoted `ε_DW = 15.351u²` and
`Φ_DW = 2^{-1071}`, the part bounds `π^y`, Lemma 38's `δ*`, `δ` and `π^r` for the reduction of `-y_0`, and the
predicates and steps of an evaluation. Horner's run and step (3) are evaluated on a state `(p_q, b_T)` shared by the
cases of a group (`log8Run`, `log8W`, `log8Y`, `log8T`), in pieces checked against stored states. For a case, a
sign and an end, `Log8Leaf` holds the rational bounds of the case's own arguments, `log8Sq` is a squaring,
`log8C4a` and `log8C4b` the two pieces of step (4), and `Log8End` the last product, the last ADD and the bound
`9.926u^8 ℓ` (`+ 2^{-509}` at the ends of an interval from `ℓ = 0`). Step (5)'s series, `c ⊗ h` and
`ADDF(c ⊗ h, 1)` are evaluated once, on a state `(χ^M, C^M)` above every case's (`Log8/Data.lean`).
-/

namespace ExpansionBounds

open Finset

/-- the parts of `F'_k`, the greedy eight parts of `(-1)^{k+1}/k` -/
def log8F (k i : ℕ) : ℚ := dyFn (log8Ser.getD k []) i

/-- `φ'_k = |∑_i F'_{k,i} - (-1)^{k+1}/k|` -/
def log8Phi (k : ℕ) : ℚ := |∑ i ∈ range 8, log8F k i - (-1) ^ (k + 1) / (k : ℚ)|

/-- `e_A = 3u²/(1 - 4u)` -/
def log8EA : ℚ := 3 * red8U ^ 2 / (1 - 4 * red8U)

/-- `ε_DW = 15.351u²`, as quoted in Proposition 44 -/
def log8EpsDW : ℚ := 15351 / 1000 * red8U ^ 2

/-- `δ_0 = w/(1 - w)` with `w = gρ/(1 - 2ρ - gρ)`, `g = (n - 2)u/(1 - (n - 2)u)` and `ρ = 2u` -/
def log8D0 : ℚ :=
  (6 * red8U / (1 - 6 * red8U) * (2 * red8U) / (1 - 2 * (2 * red8U) - 6 * red8U / (1 - 6 * red8U) * (2 * red8U))) /
    (1 - 6 * red8U / (1 - 6 * red8U) * (2 * red8U) / (1 - 2 * (2 * red8U) - 6 * red8U / (1 - 6 * red8U) * (2 * red8U)))

/-- a bound of `η_L = |ln 2 - c_{L,0} - c_{L,1}|`, on the enclosure of `ln 2` -/
def log8EtaL : ℚ := max |ln2A - (dyQ log8CL0 + dyQ log8CL1)| |ln2B - (dyQ log8CL0 + dyQ log8CL1)|

/-- `e₁ = ε_DW + e_A` -/
def log8E1 : ℚ := log8EpsDW + log8EA

/-- `e₀ = ε_DW δ_0 + δ_0 + Φ_DW + e_A + η_L + 2^{-2000}`, with `Φ_DW = 2^{-1071}` -/
def log8E0 : ℚ := log8EpsDW * log8D0 + log8D0 + 1 / 2 ^ 1071 + log8EA + log8EtaL + 1 / 2 ^ 2000

/-- `E(ℓ) = e₀ + e₁ℓ`, rounded up to 200 bits -/
def log8Eq (l : ℚ) : ℚ := upQ 200 (log8E0 + log8E1 * l)

/-- `π^y` at `ℓ`: the part bounds of two parts on `H(1)` with value at most `ȳ = ℓ + E(ℓ)` -/
def log8PiY (l : ℚ) (i : ℕ) : ℚ :=
  if i = 0 then (l + log8Eq l) * (1 - red8U) / (1 - 2 * red8U)
  else if i = 1 then red8U * ((l + log8Eq l) * (1 - red8U) / (1 - 2 * red8U)) else 0

/-- `r̄_max` of Lemma 38 at `X = ȳ/(1 - u)` and `x̄_t = 2uȳ` -/
def log8RMax (l : ℚ) : ℚ :=
  (1 / 2 + (l + log8Eq l) / (1 - red8U) * (red8Dl + red8U * cr8)) * ln2B + 2 * red8U * (l + log8Eq l)

/-- Lemma 38's `α` for the reduction of `-y_0` -/
def log8Alpha (l : ℚ) (i : ℕ) : ℚ :=
  if i = 0 then log8RMax l + 2 * red8U * (l + log8Eq l) + 1075 * max |ch8 - ln2A| |ch8 - ln2B| else log8PiY l i

/-- `δ*`: Lemma 38 (b)'s `δ` at `r̄ = r̄_max`, with VecSum's second bound alone, rounded up -/
def log8DeltaS (l : ℚ) : ℚ :=
  upQ 200 (red8E1 + GaddECQ red8U 8 (log8Alpha l) red8Mu (log8RMax l + 1075 * red8Eta + red8E1) + 1075 * red8Eta)

/-- `δ` at `r̄ = b + δ*`, rounded up -/
def log8Delta (l b : ℚ) : ℚ :=
  upQ 200 (red8E1 + GaddECQ red8U 8 (log8Alpha l) red8Mu (b + log8DeltaS l + 1075 * red8Eta + red8E1) +
    1075 * red8Eta)

/-- `π^r` at `r̄ = b + δ*`, rounded up -/
def log8PiR (l b : ℚ) (i : ℕ) : ℚ :=
  upQ 200 (GaddPCQ red8U 8 (log8Alpha l) red8Mu (b + log8DeltaS l + 1075 * red8Eta + red8E1) i)

/-- `b' = 2^{-m} b + 8η_0[m > 0]` -/
def log8Bp (m : ℕ) (b : ℚ) : ℚ := (2 : ℚ) ^ (-(m : ℤ)) * b + ((8 : ℕ) : ℚ) * exp8Eta1 m

/-- `π^x` at a bound of `ξ`: the ladder of `H(2)`, each part plus `2η_0` -/
def log8PiX (xi : ℚ) (i : ℕ) : ℚ := (2 * red8U) ^ i * (xi * (1 - 2 * red8U) / (1 - 4 * red8U)) + 2 * exp8Eta

/-- `φ̄`'s bound from a bound of `ξ` -/
def log8PhiB (xi E b δ : ℚ) : ℚ := max (xi - 1) (E + b + δ + ((8 : ℕ) : ℚ) * (2 * exp8Eta))

/-- a state of step (4)'s first piece, from dyadic pairs -/
def dySt4 (st : ((ℤ × ℕ) × (ℤ × ℕ)) × (List (ℤ × ℕ) × List (ℤ × ℕ))) : (ℚ × ℚ) × (List ℚ × List ℚ) :=
  ((dyQ st.1.1, dyQ st.1.2), (st.2.1.map dyQ, st.2.2.map dyQ))

/-- Horner's convex run on the `F_k`, rounded to 200 bits -/
abbrev log8Run (pq : List ℚ) (bp : ℚ) (d a m : ℕ) (st : ℚ × List ℚ) : ℚ × List ℚ :=
  hornerRunLC red8U 8 (upQ 200) (fun i => pq.getD i 0) bp 0 0 exp8F exp8Phi (coreVQ bp) d a m st

/-- step (3)'s first product on a group's state -/
abbrev log8W (pq : List ℚ) (bp : ℚ) (st : ℚ × List ℚ) : (ℚ × ℚ) × List ℚ :=
  expWLC red8U 8 (upQ 200) (fun i => pq.getD i 0) bp st

/-- step (3)'s second product on a group's state -/
abbrev log8Y (m d : ℕ) (pq : List ℚ) (bp : ℚ) (st : (ℚ × ℚ) × List ℚ) : ℚ × List ℚ :=
  expYLC red8U 8 (upQ 200) (fun i => pq.getD i 0) bp (2 * ((8 : ℕ) : ℚ) * exp8Eta1 m) d st

/-- step (3)'s sum on a group's state, for a sign -/
abbrev log8T (pos : Bool) (pq : List ℚ) (bp : ℚ) (st : ℚ × List ℚ) : ℚ × List ℚ :=
  expTLC red8U 8 (upQ 200) (fun i => pq.getD i 0) (coreTCQ (upQ 200) pos bp 0) exp8Eta st

/-- squaring `j` of a case with `|r| ∈ [a, b]` -/
abbrev log8Sq (pos : Bool) (m : ℕ) (a b : ℚ) (j : ℕ) (st : ℚ × List ℚ) : ℚ × List ℚ :=
  expSqLC red8U 8 (upQ 200) (coreTCQ (upQ 200) pos (log8Bp m b) j) (coreTCQ (upQ 200) pos (log8Bp m b) (j + 1))
    (coreGQ (upQ 200) pos ((2 : ℚ) ^ (-(m : ℤ)) * a) (log8Bp m b) j) st

/-- step (4)'s first piece for a case at `ℓ` -/
abbrev log8C4a (pos : Bool) (m : ℕ) (b δ l xi xs : ℚ) (pphi : List ℚ) (st : ℚ × List ℚ) :
    (ℚ × ℚ) × (List ℚ × List ℚ) :=
  logC4aL red8U 8 (upQ 200) (((8 : ℕ) : ℚ) * (2 * exp8Eta)) (2 * exp8Eta) (fun i => pphi.getD i 0)
    (log8PhiB xi (log8Eq l) b δ) (coreTCQ (upQ 200) pos (log8Bp m b) m) xs 436 st

/-- step (4)'s second piece for a case -/
abbrev log8C4b (pos : Bool) (m : ℕ) (b xi cs xd : ℚ) (pphi : List ℚ) (st : ℚ × List ℚ)
    (sa : (ℚ × ℚ) × (List ℚ × List ℚ)) : ℚ × List ℚ :=
  logC4bL red8U 8 (upQ 200) (((8 : ℕ) : ℚ) * (2 * exp8Eta)) (fun i => pphi.getD i 0)
    (coreTCQ (upQ 200) pos (log8Bp m b) m) cs xd xi st sa

/-- the rational bounds of a case's own arguments at an end `ℓ`: the case's `(π', b')` below the group's state
`(p_q, b_T)`, `δ` (zero for `k = 0`), the exponents within the enclosure of `e^z`, and `ξ`, the three combinations of
exponentials of step (4) and `π^φ` below their stored bounds -/
def Log8Leaf (k0 pos : Bool) (m : ℕ) (a b δ l bpT : ℚ) (pq : List ℚ) (xi xs cs xd : ℚ) (pphi : List ℚ) : Prop :=
  0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ δ ∧ 0 ≤ l ∧ log8Bp m b ≤ bpT ∧ bpT < 1 ∧ 2 ^ m * bpT ≤ 1 ∧ a ≤ 1 ∧
    (if k0 then δ = 0 else log8Delta l b ≤ δ) ∧
    (∀ i < 8, (2 : ℚ) ^ (-(m : ℤ)) * (if k0 then log8PiY l i else log8PiR l b i) + exp8Eta1 m ≤ pq.getD i 0) ∧
    |log8Eq l + δ - a| ≤ 1 ∧ |log8Eq l + b + δ| ≤ 1 ∧ |b + δ| ≤ 1 ∧ |log8Eq l + δ| ≤ 1 ∧ |log8Eq l| ≤ 1 ∧ |δ| ≤ 1 ∧
    logXiQ (((8 : ℕ) : ℚ) * (2 * exp8Eta)) pos (log8Eq l) a b δ ≤ xi ∧ logXsQ (log8Eq l) b δ ≤ xs ∧
    logCsQ (log8Eq l) ≤ cs ∧ logXdQ (log8Eq l) δ ≤ xd ∧
    ∀ i < 8, upQ 200 (GaddfPCQ red8U 8 (log8PiX xi)
      (log8PhiB xi (log8Eq l) b δ + ∑ i ∈ Ico 1 8, log8PiX xi i) (log8PhiB xi (log8Eq l) b δ) i) ≤ pphi.getD i 0

instance (k0 pos : Bool) (m : ℕ) (a b δ l bpT : ℚ) (pq : List ℚ) (xi xs cs xd : ℚ) (pphi : List ℚ) :
    Decidable (Log8Leaf k0 pos m a b δ l bpT pq xi xs cs xd pphi) := by
  unfold Log8Leaf
  infer_instance

/-- step (5)'s last product and the last ADD of a case at `ℓ`, from step (4)'s `(E_c, χ)` below the shared state:
the convex `𝓔` is at most `9.926u^8 ℓ`, plus `2^{-509}` where the interval starts at `ℓ = 0` -/
def Log8End (zero : Bool) (l cs : ℚ) (c4 : ℚ × List ℚ) : Prop :=
  (∀ i < 8, c4.2.getD i 0 ≤ dyFn log8ChiM i) ∧ cs + c4.1 ≤ dyQ log8CM ∧
    logEndL red8U 8 (log8PiY l) l (logPL red8U 8 (upQ 200) exp8Eta (fun i => c4.2.getD i 0) (cs + c4.1) c4.1
      (dySt log8SH).1 (dyStW log8HH).1.1 (dyStW log8HH).1.2 4 436 (dySt log8GG)) ≤
      (if zero then 1 / 2 ^ 509 else 0) + 9926 / 1000 * red8U ^ 8 * l

instance (zero : Bool) (l cs : ℚ) (c4 : ℚ × List ℚ) : Decidable (Log8End zero l cs c4) := by
  unfold Log8End
  infer_instance

/-- step (5) on the shared state: Horner's rule on the series, `c ⊗ h` and `ADDF(c ⊗ h, 1)` follow the stored
states, with `C^M < 1` and `χ^M ≥ 0` -/
def Log8Shared : Prop :=
  dyQ log8CM < 1 ∧ (∀ i < 8, 0 ≤ dyFn log8ChiM i) ∧
    hornerRunLC red8U 8 (upQ 200) (dyFn log8ChiM) (dyQ log8CM) 0 exp8Eta log8F log8Phi (logVQ (dyQ log8CM) 4) 4 0 2
      (hornerInitL 8 log8F log8Phi 4) = dySt log8SH ∧
    logHL red8U 8 (upQ 200) exp8Eta (dyFn log8ChiM) (dyQ log8CM) 4 (dySt log8SH) = dyStW log8HH ∧
    logGL red8U 8 (upQ 200) (dyStW log8HH) = dySt log8GG

instance : Decidable Log8Shared := by
  unfold Log8Shared
  infer_instance

end ExpansionBounds
