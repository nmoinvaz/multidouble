"""Proposition 28 for Lean: the accumulator's run on the constructed terms in exact rationals, written from the Lean
definitions (rnQ, twoSumQ, depSQ, addxQ, finishRQ of lean/ExpansionBounds), and the modules that hold it:
Prop28/Data.lean (the 2048 terms in chunks of 16, the levels after each chunk, FINISH's parts and the exact sums, for
all the terms and for the first 256, 512 and 1024, each as dyadic pairs (m, k) for m/2^k), Prop28/Run0.lean to
Run7.lean (the kernel's run of 16 chunks each, so that they build in parallel) and Prop28.lean (the theorems). A chunk
of 16 terms keeps the kernel's memory small: one of 64 takes 2.7 GB more.

usage: acc_lean.py <terms.txt> <emu_result.txt> [lean/ExpansionBounds]
       prints whether the run gives the stored emulator's result, the error as a multiple of u^8 |Z| for all the terms
       and for the prefixes, and the proposition's claims on W and on the terms. The controls (ties away from zero,
       and each claim on W and the terms made a little stronger) must fail. With a third argument, and when every
       check comes out so, it writes the Lean modules into that directory; they are for K terms."""
import os
import struct
import sys
from fractions import Fraction as Fr

P, N, CHUNK, PER = 53, 8, 16, 16  # PER chunks to a Run module
K = 2048                         # the terms of the Lean modules
# the error of the first 256, 512 and 1024 terms lies between these multiples of u^8 |Z|
PREFIX = {256: ("0.1029", "0.1030"), 512: ("36.39", "36.40"), 1024: ("11805", "11806")}
AWAY = False                     # the control: ties away from zero


def dbl(h):
    return Fr(struct.unpack(">d", bytes.fromhex(h))[0])


def rn(q):
    """RN at precision P with an unbounded exponent range, ties to even (Lean's rnQ)"""
    if q == 0:
        return Fr(0)
    a = abs(q)
    e = a.numerator.bit_length() - a.denominator.bit_length()
    e = e + 1 if Fr(2) ** e <= a else e          # 2^(e-1) <= |q| < 2^e
    c = e - P
    s = q / Fr(2) ** c
    f = s.numerator // s.denominator
    d = s - f
    tie = (f + 1 if s > 0 else f) if AWAY else (f + 1 if f % 2 == 1 else f)
    m = f if d < Fr(1, 2) else f + 1 if d > Fr(1, 2) else tie
    return m * Fr(2) ** c


def mag(q):
    """the e with 2^(e-1) <= |q| < 2^e (Lean's magQ)"""
    a = abs(q)
    e = a.numerator.bit_length() - a.denominator.bit_length()
    return e + 1 if Fr(2) ** e <= a else e


def half_ulp(t, bits=1):
    """each part zero, or at most 2^-bits ulp of the one before"""
    return all(t[i + 1] == 0 or t[i] != 0 and abs(t[i + 1]) <= Fr(2) ** (mag(t[i]) - P - bits) for i in range(N - 1))


def two_sum(a, b):
    s = rn(a + b)
    return s, a + b - s


def addx(t, s):
    """ADDX: a dep of t_l at each level l < N"""
    for l in range(N):
        e = t[l]
        for m in range(l, N):
            s[m], e = two_sum(s[m], e)
        s[N] = rn(s[N] + e)


def addf(a, b):
    lev, e = [], b
    for m in range(N):
        x, e = two_sum(a[m], e)
        lev.append(x)
    lev.append(e)
    v = [None] * (N + 1)                         # VecSum
    s = lev[N]
    for i in range(N - 1, -1, -1):
        s, v[i + 1] = two_sum(lev[i], s)
    v[0] = s
    out, acc, left = [], v[0], N - 1             # the second pass
    for x in v[1:]:
        t, e = two_sum(acc, x)
        if left != 0 and e != 0:
            out.append(t)
            acc = e
            left -= 1
        else:
            acc = t
    out.append(acc)
    return out + [Fr(0)] * (N - len(out))


def finish(s):
    r = [s[0]] + [Fr(0)] * (N - 1)
    for l in range(1, N + 1):
        r = addf(r, s[l])
    return r


def run(terms):
    """the levels after each chunk, and FINISH's parts"""
    s = [Fr(0)] * (N + 1)
    states = [list(s)]
    for k, t in enumerate(terms, 1):
        addx(t, s)
        if k % CHUNK == 0:
            states.append(list(s))
    return states, finish(s)


def pair(q):
    """a dyadic rational as the Lean pair (m, k) for m/2^k"""
    k = q.denominator.bit_length() - 1
    assert q.denominator == 1 << k
    return f"({q.numerator}, {k})"


def wrap(items, sep, indent, width=120):
    """items joined by sep, broken into lines of at most width with the given indent"""
    lines, cur = [], ""
    for it in items:
        piece = it if not cur else cur + sep + it
        if cur and len(piece) + indent + len(sep) > width:
            lines.append(cur + sep.rstrip())
            cur = it
        else:
            cur = piece
    lines.append(cur)
    return ("\n" + " " * indent).join(lines)


DATA = """import ExpansionBounds.AccRun

/-!
# Proposition 28 (`prop:acc-low`): the constructed terms

The terms of `accumulator/out/acc_p53_n8_K2048_terms.txt`, `1` and then `2047` positive octo-doubles of size about
`u`, in chunks of 16, with the accumulator's levels after each chunk, FINISH's parts, and the exact sums, for all the
terms and for the first 256, 512 and 1024. Every number is a dyadic pair `(m, k)` for `m / 2 ^ k`. This file is
written by `accumulator/acc_lean.py`.
-/

namespace ExpansionBounds
"""

RUN = """import ExpansionBounds.Prop28.Data

/-!
# Proposition 28 (`prop:acc-low`): the accumulator's run on the terms FIRST to LAST

The kernel runs the accumulator on each chunk of 16 terms from the levels before it and checks the levels after it.
This file is written by `accumulator/acc_lean.py`.
-/

namespace ExpansionBounds
"""

HEAD = """IMPORTS
import ExpansionBounds.Kappa8

/-!
# Proposition 28 (`prop:acc-low`): the accumulator's growth is real

The accumulator run by the kernel on the constructed terms of `accumulator/out/acc_p53_n8_K2048_terms.txt`: `1` and
then `2047` positive octo-doubles of size about `u`, each part at most half an ulp of the one before
(`prop28_terms`). At `p = 53` and `n = 8` the result of FINISH differs from the exact sum `Z` by between
`14675797u^8|Z|` and `14675798u^8|Z|`, the proposition's `1.4676·10^7u^8|Z|` (`prop28`), and `W` lies between
`|Z|(1 - 2^{-96})` and `|Z|` (`prop28_W`). The first `256`, `512` and `1024` terms give errors of `0.10`, `36` and
`1.2·10^4` times `u^8|Z|` (`prop28_256`, `prop28_512`, `prop28_1024`), so doubling the terms from `1024` multiplies
the error by between `1243` and `1244`, about `2^{10.28}`, the proposition's `2^{10.3}`. The terms are cut in chunks
of 16, and the kernel checks the levels after each chunk from those before it (`Prop28/Run0.lean` to `Run7.lean`),
then FINISH and the exact sums. This file is written by `accumulator/acc_lean.py`.
-/

namespace ExpansionBounds

open Finset

/-! ### The levels after each chunk, as functions -/
"""

CHECKS = """
/-- the number of terms -/
theorem acc28_len : acc28T.length = 2048 := by decide +kernel

/-- the first 2048 terms are all of them -/
theorem acc28_take : acc28T.take 2048 = acc28T := List.take_of_length_le (le_of_eq acc28_len)

set_option maxHeartbeats 4000000 in
/-- every part of every term is in `F`: `rnQ` leaves it as it is -/
theorem acc28_F : ∀ t ∈ acc28T, ∀ q ∈ t, rnQ 53 (dyQ q) = dyQ q := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- every term has a positive leading part, and each part is at most `u` times the one before -/
theorem acc28_ladder : ∀ t ∈ acc28T,
    0 < dyFn t 0 ∧ ∀ i < 7, |dyFn t (i + 1)| ≤ 1 / 9007199254740992 * |dyFn t i| := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the first term is `1` -/
theorem acc28_first : dyFn (acc28T.getD 0 []) 0 = 1 ∧ (∀ i < 8, 1 ≤ i → dyFn (acc28T.getD 0 []) i = 0) ∧
    (acc28T.getD 0 []).length ≤ 8 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the leading parts of the other terms lie in `[(1 - 2^{-42})u, u)` -/
theorem acc28_size : ∀ t ∈ acc28T.tail,
    (1 - 1 / 2 ^ 42) * (1 / 9007199254740992 : ℚ) ≤ dyFn t 0 ∧ dyFn t 0 < 1 / 9007199254740992 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- each part is zero or at most half an ulp of the one before, `2^(e - 54)` for a part in `[2^(e-1), 2^e)` -/
theorem acc28_half : ∀ t ∈ acc28T, ∀ i < 7,
    dyFn t (i + 1) = 0 ∨ dyFn t i ≠ 0 ∧ |dyFn t (i + 1)| ≤ (2 : ℚ) ^ (magQ (dyFn t i) - 53 - 1) := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the exact sum of each chunk -/
theorem acc28_sums :
    List.map (fun T => (T.map fun t => ∑ i ∈ range 8, dyFn t i).sum)
        [CHUNKS] =
      acc28ZS.map dyQ := by
  decide +kernel

/-- the exact sum of the terms -/
theorem acc28_sum : (acc28T.map fun t => ∑ i ∈ range 8, dyFn t i).sum = dyQ acc28Z := by
  have hz : (acc28ZS.map dyQ).sum = dyQ acc28Z := by decide +kernel
  rw [← hz, ← acc28_sums, acc28T]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    add_assoc]

set_option maxHeartbeats 4000000 in
/-- `W`, the sum of the leading parts, lies between `|Z|(1 - 2^{-96})` and `|Z|`; the kernel sums it by chunks, a sum
down one list of 2048 being too deep for it -/
theorem acc28_W : |dyQ acc28Z| * (1 - 1 / 2 ^ 96) < (acc28T.map fun t => |dyFn t 0|).sum ∧
    (acc28T.map fun t => |dyFn t 0|).sum < |dyQ acc28Z| := by
  rw [acc28T]
  simp only [List.map_append, List.sum_append]
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- FINISH on the levels after the 2048 terms -/
theorem acc28_finish : ∑ i ∈ range 8, finishRQ 53 8 (dyFn acc28SLAST) 8 i = (acc28X.map dyQ).sum := by
  decide +kernel

/-- the error: between `14675797u^8|Z|` and `14675798u^8|Z|` -/
theorem acc28_err :
    14675797 * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ acc28Z| ≤ |dyQ acc28Z - (acc28X.map dyQ).sum| ∧
      |dyQ acc28Z - (acc28X.map dyQ).sum| ≤ 14675798 * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ acc28Z| := by
  decide +kernel
"""

PRE_CHECKS = """
set_option maxHeartbeats 4000000 in
/-- the exact sum of the first KP terms, summed by chunks -/
theorem acc28_sumKP : ((acc28T.take KP).map fun t => ∑ i ∈ range 8, dyFn t i).sum = dyQ acc28ZKP := by
  rw [acc28_takeKP]
  simp only [List.map_append, List.sum_append]
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- FINISH on the levels after the first KP terms -/
theorem acc28_finishKP : ∑ i ∈ range 8, finishRQ 53 8 (dyFn acc28SLAST) 8 i = (acc28XKP.map dyQ).sum := by
  decide +kernel

/-- the error after the first KP terms: between `LOu^8|Z|` and `HIu^8|Z|` -/
theorem acc28_errKP :
    LO * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ acc28ZKP| ≤ |dyQ acc28ZKP - (acc28XKP.map dyQ).sum| ∧
      |dyQ acc28ZKP - (acc28XKP.map dyQ).sum| ≤ HI * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ acc28ZKP| := by
  decide +kernel
"""

TAIL = """
variable (p : ℤ) [Prec_gt_0 p]

/-- the terms of Proposition 28: term `k` is the `k`-th row of the data -/
noncomputable def acc28 : ℕ → ℕ → ℝ := dyTerms acc28T

/-- the error after the first `K` terms, from the kernel's checks of them: the levels `S` after them, FINISH's parts
`X` on those, and the exact sum `Z` -/
theorem acc28_prefix (hp : p = 53) (K : ℕ) (hK : K ≤ 2048) (S X : List (ℤ × ℕ)) (Z : ℤ × ℕ) (lo hi : ℚ)
    (hrun : accRunQ 53 8 ((acc28T.take K).map dyFn) (fun _ => 0) = dyFn S)
    (hsum : ((acc28T.take K).map fun t => ∑ i ∈ range 8, dyFn t i).sum = dyQ Z)
    (hfin : ∑ i ∈ range 8, finishRQ 53 8 (dyFn S) 8 i = (X.map dyQ).sum)
    (herr : lo * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ Z| ≤ |dyQ Z - (X.map dyQ).sum| ∧
      |dyQ Z - (X.map dyQ).sum| ≤ hi * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ Z|) :
    (lo : ℝ) * u p ^ 8 * |∑ k ∈ Icc 1 K, ∑ i ∈ range 8, acc28 k i| ≤
        |∑ k ∈ Icc 1 K, ∑ i ∈ range 8, acc28 k i -
          ∑ i ∈ range 8, finishR p 8 (accLevX p 8 acc28 K) 8 i| ∧
      |∑ k ∈ Icc 1 K, ∑ i ∈ range 8, acc28 k i -
          ∑ i ∈ range 8, finishR p 8 (accLevX p 8 acc28 K) 8 i| ≤
        (hi : ℝ) * u p ^ 8 * |∑ k ∈ Icc 1 K, ∑ i ∈ range 8, acc28 k i| := by
  subst hp
  obtain ⟨hfin', hZ⟩ := accRun_prefix 53 8 (by norm_num) acc28T (dyF_of_all 53 acc28T acc28_F) (K := K)
    (hK.trans_eq acc28_len.symm)
  have hx : ∑ i ∈ range 8, finishR 53 8 (accLevX 53 8 acc28 K) 8 i = (((X.map dyQ).sum : ℚ) : ℝ) := by
    rw [← hfin, Rat.cast_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← hrun]
    exact hfin' i
  have hZ' : ∑ k ∈ Icc 1 K, ∑ i ∈ range 8, acc28 k i = ((dyQ Z : ℚ) : ℝ) := by
    rw [← hsum]
    exact hZ
  have hu : u (53 : ℤ) = ((1 / 9007199254740992 : ℚ) : ℝ) := (u_53_rat 53 rfl).symm
  obtain ⟨e1, e2⟩ := herr
  constructor
  · rw [hZ', hx, hu, ← Rat.cast_sub, ← Rat.cast_abs, ← Rat.cast_abs, ← Rat.cast_pow, ← Rat.cast_mul, ← Rat.cast_mul,
      Rat.cast_le]
    exact e1
  · rw [hZ', hx, hu, ← Rat.cast_sub, ← Rat.cast_abs, ← Rat.cast_abs, ← Rat.cast_pow, ← Rat.cast_mul, ← Rat.cast_mul,
      Rat.cast_le]
    exact e2

/-- Proposition 28 (`prop:acc-low`) at `p = 53` and `n = 8`: the `2048` terms are in `F`, on `H(1)` with positive
leading parts, and the accumulator's result differs from their exact sum `Z` by between `14675797u^8|Z|` and
`14675798u^8|Z|` -/
theorem prop28 (hp : p = 53) :
    (∀ k i, F p (acc28 k i)) ∧ (∀ k ∈ Icc 1 2048, Htheta p 8 1 (acc28 k) ∧ 0 < acc28 k 0) ∧
      14675797 * u p ^ 8 * |∑ k ∈ Icc 1 2048, ∑ i ∈ range 8, acc28 k i| ≤
        |∑ k ∈ Icc 1 2048, ∑ i ∈ range 8, acc28 k i -
          ∑ i ∈ range 8, finishR p 8 (accLevX p 8 acc28 2048) 8 i| ∧
      |∑ k ∈ Icc 1 2048, ∑ i ∈ range 8, acc28 k i -
          ∑ i ∈ range 8, finishR p 8 (accLevX p 8 acc28 2048) 8 i| ≤
        14675798 * u p ^ 8 * |∑ k ∈ Icc 1 2048, ∑ i ∈ range 8, acc28 k i| := by
  have herr := acc28_prefix p hp 2048 le_rfl acc28SLAST acc28X acc28Z 14675797 14675798
    (by rw [acc28_take]; exact acc28_run) (by rw [acc28_take]; exact acc28_sum) acc28_finish acc28_err
  rw [Rat.cast_ofNat, Rat.cast_ofNat] at herr
  subst hp
  have hF := dyF_of_all 53 acc28T acc28_F
  have hu : u (53 : ℤ) = ((1 / 9007199254740992 : ℚ) : ℝ) := (u_53_rat 53 rfl).symm
  refine ⟨fun k i => dyTerms_F 53 acc28T hF k i, fun k hk => ?_, herr⟩
  obtain ⟨hk1, hk2⟩ := mem_Icc.mp hk
  obtain ⟨l1, l2⟩ := acc28_ladder _ (getD_mem acc28T [] (j := k - 1) (by rw [acc28_len]; omega))
  refine ⟨Htheta_of_steps 53 8 _ fun i hi => ?_, ?_⟩
  · show |((dyFn (acc28T.getD (k - 1) []) (i + 1) : ℚ) : ℝ)| ≤
      u (53 : ℤ) * |((dyFn (acc28T.getD (k - 1) []) i : ℚ) : ℝ)|
    rw [hu, ← Rat.cast_abs, ← Rat.cast_abs, ← Rat.cast_mul, Rat.cast_le]
    exact l2 i (by omega)
  · show (0 : ℝ) < ((dyFn (acc28T.getD (k - 1) []) 0 : ℚ) : ℝ)
    exact_mod_cast l1

/-- the terms of Proposition 28: the first is `1`, the leading parts of the others lie in `[(1 - 2^{-42})u, u)`, and
each part is zero or at most half an ulp of the one before, `2^(e - p - 1)` for a part in `[2^(e-1), 2^e)` -/
theorem prop28_terms (hp : p = 53) :
    (acc28 1 0 = 1 ∧ ∀ i, 1 ≤ i → acc28 1 i = 0) ∧
      (∀ k ∈ Icc 2 2048, (1 - (2 : ℝ) ^ (-42 : ℤ)) * u p ≤ acc28 k 0 ∧ acc28 k 0 < u p) ∧
      ∀ k ∈ Icc 1 2048, ∀ i < 7, acc28 k (i + 1) = 0 ∨ ∃ e : ℤ, (2 : ℝ) ^ (e - 1) ≤ |acc28 k i| ∧
        |acc28 k i| < (2 : ℝ) ^ e ∧ |acc28 k (i + 1)| ≤ (2 : ℝ) ^ (e - p - 1) := by
  subst hp
  have hu : u (53 : ℤ) = ((1 / 9007199254740992 : ℚ) : ℝ) := (u_53_rat 53 rfl).symm
  obtain ⟨f0, f1, f2⟩ := acc28_first
  refine ⟨⟨?_, fun i hi => ?_⟩, fun k hk => ?_, fun k hk i hi => ?_⟩
  · show ((dyFn (acc28T.getD 0 []) 0 : ℚ) : ℝ) = 1
    rw [f0, Rat.cast_one]
  · show ((dyFn (acc28T.getD 0 []) i : ℚ) : ℝ) = 0
    rcases Nat.lt_or_ge i 8 with h8 | h8
    · rw [f1 i h8 hi, Rat.cast_zero]
    · rw [dyFn_of_le _ (f2.trans h8), Rat.cast_zero]
  · obtain ⟨hk1, hk2⟩ := mem_Icc.mp hk
    obtain ⟨s1, s2⟩ := acc28_size _ (getD_mem_tail acc28T [] hk1 (hk2.trans_eq acc28_len.symm))
    constructor
    · show (1 - (2 : ℝ) ^ (-42 : ℤ)) * u (53 : ℤ) ≤ ((dyFn (acc28T.getD (k - 1) []) 0 : ℚ) : ℝ)
      rw [hu, show (1 - (2 : ℝ) ^ (-42 : ℤ)) = ((1 - 1 / 2 ^ 42 : ℚ) : ℝ) by norm_num, ← Rat.cast_mul, Rat.cast_le]
      exact s1
    · show ((dyFn (acc28T.getD (k - 1) []) 0 : ℚ) : ℝ) < u (53 : ℤ)
      rw [hu, Rat.cast_lt]
      exact s2
  · obtain ⟨hk1, hk2⟩ := mem_Icc.mp hk
    rcases acc28_half _ (getD_mem acc28T [] (j := k - 1) (by rw [acc28_len]; omega)) i hi with h0 | ⟨hq, hh⟩
    · left
      show ((dyFn (acc28T.getD (k - 1) []) (i + 1) : ℚ) : ℝ) = 0
      rw [h0, Rat.cast_zero]
    · right
      exact half_ulp_cast 53 hq hh

/-- Proposition 28's `W`, the sum of the leading parts' sizes: `|Z|(1 - 2^{-96}) < W < |Z|` -/
theorem prop28_W :
    |∑ k ∈ Icc 1 2048, ∑ i ∈ range 8, acc28 k i| * (1 - (2 : ℝ) ^ (-96 : ℤ)) < ∑ k ∈ Icc 1 2048, |acc28 k 0| ∧
      ∑ k ∈ Icc 1 2048, |acc28 k 0| < |∑ k ∈ Icc 1 2048, ∑ i ∈ range 8, acc28 k i| := by
  have hZ : ∑ k ∈ Icc 1 2048, ∑ i ∈ range 8, acc28 k i = ((dyQ acc28Z : ℚ) : ℝ) := by
    rw [← acc28_sum, ← acc28_len]
    exact dyTerms_sum 8 acc28T
  have hW : ∑ k ∈ Icc 1 2048, |acc28 k 0| = (((acc28T.map fun t => |dyFn t 0|).sum : ℚ) : ℝ) := by
    rw [← acc28_len]
    exact dyTerms_lead_sum acc28T
  obtain ⟨w1, w2⟩ := acc28_W
  rw [hZ, hW, ← Rat.cast_abs, show (1 - (2 : ℝ) ^ (-96 : ℤ)) = ((1 - 1 / 2 ^ 96 : ℚ) : ℝ) by norm_num, ← Rat.cast_mul,
    Rat.cast_lt, Rat.cast_lt]
  exact ⟨w1, w2⟩
"""

PRE_THM = """
/-- the first KP terms of Proposition 28: the accumulator's result differs from their exact sum `Z` by between
`LOu^8|Z|` and `HIu^8|Z|` -/
theorem prop28_KP (hp : p = 53) :
    LO * u p ^ 8 * |∑ k ∈ Icc 1 KP, ∑ i ∈ range 8, acc28 k i| ≤
        |∑ k ∈ Icc 1 KP, ∑ i ∈ range 8, acc28 k i -
          ∑ i ∈ range 8, finishR p 8 (accLevX p 8 acc28 KP) 8 i| ∧
      |∑ k ∈ Icc 1 KP, ∑ i ∈ range 8, acc28 k i -
          ∑ i ∈ range 8, finishR p 8 (accLevX p 8 acc28 KP) 8 i| ≤
        HI * u p ^ 8 * |∑ k ∈ Icc 1 KP, ∑ i ∈ range 8, acc28 k i| := by
  have h := acc28_prefix p hp KP (by norm_num) acc28SLAST acc28XKP acc28ZKP (LO) (HI)
    acc28_runKP acc28_sumKP acc28_finishKP acc28_errKP
  push_cast at h
  exact h
"""


def lean_q(d):
    """a decimal as a quotient of integers for Lean"""
    frac = len(d.partition(".")[2])
    return d if frac == 0 else f"{int(d.replace('.', ''))} / {10 ** frac}"


def fill(text, kp, m):
    """a template for the first kp terms, m chunks"""
    lo, hi = PREFIX[kp]
    return (text.replace("acc28SLAST", f"acc28S{m}").replace("KP", str(kp)).replace("`LO", "`" + lo)
            .replace("`HI", "`" + hi).replace("LO", lean_q(lo)).replace("HI", lean_q(hi)))


def lean_modules(terms, states, x, Z, pre):
    """the Lean modules, as a dictionary from each file's path under lean/ExpansionBounds to its text; pre gives
    FINISH's parts and the exact sum for each prefix"""
    nc = len(terms) // CHUNK
    end = "\nend ExpansionBounds\n"
    data = [DATA]
    for c in range(nc):
        rows = ["  [" + ", ".join(pair(q) for q in t) + "]" for t in terms[c * CHUNK:(c + 1) * CHUNK]]
        data.append(f"\n/-- the terms {c * CHUNK + 1} to {(c + 1) * CHUNK} -/\n"
                    f"def acc28T{c} : List (List (ℤ × ℕ)) := [\n" + ",\n".join(rows) + "]\n")
    for c in range(1, nc + 1):
        data.append(f"\n/-- the levels after {c * CHUNK} terms -/\n"
                    f"def acc28S{c} : List (ℤ × ℕ) := [" + ", ".join(pair(q) for q in states[c]) + "]\n")
    data.append("\n/-- FINISH's parts -/\ndef acc28X : List (ℤ × ℕ) := [" + ", ".join(pair(q) for q in x) + "]\n")
    data.append(f"\n/-- the exact sum of the terms -/\ndef acc28Z : ℤ × ℕ := {pair(Z)}\n")
    for kp, (xp, zp) in pre.items():
        data.append(f"\n/-- FINISH's parts after the first {kp} terms -/\ndef acc28X{kp} : List (ℤ × ℕ) := ["
                    + ", ".join(pair(q) for q in xp) + "]\n")
        data.append(f"\n/-- the exact sum of the first {kp} terms -/\ndef acc28Z{kp} : ℤ × ℕ := {pair(zp)}\n")
    zs = [sum(sum(t) for t in terms[c * CHUNK:(c + 1) * CHUNK]) for c in range(nc)]
    data.append("\n/-- the exact sums of the chunks -/\ndef acc28ZS : List (ℤ × ℕ) := ["
                + ", ".join(pair(q) for q in zs) + "]\n")
    data.append("\n/-- the 2048 terms -/\ndef acc28T : List (List (ℤ × ℕ)) :=\n  "
                + wrap([f"acc28T{c}" for c in range(nc)], " ++ ", 2) + "\n")
    files = {"Prop28/Data.lean": "".join(data) + end}
    for r in range(0, nc, PER):
        run = [RUN.replace("FIRST", str(r * CHUNK + 1)).replace("LAST", str((r + PER) * CHUNK))]
        for c in range(r, r + PER):
            start = "fun _ => 0" if c == 0 else f"(dyFn acc28S{c})"
            run.append(f"\nset_option maxHeartbeats 4000000 in\n/-- the levels after the terms {c * CHUNK + 1} to "
                       f"{(c + 1) * CHUNK} -/\ntheorem acc28_c{c} :\n    (List.range 9).map (accRunQ 53 8 "
                       f"(acc28T{c}.map dyFn) {start}) = acc28S{c + 1}.map dyQ := by\n  decide +kernel\n")
        files[f"Prop28/Run{r // PER}.lean"] = "".join(run) + end
    out = [HEAD.replace("IMPORTS", "\n".join(f"import ExpansionBounds.Prop28.Run{i}" for i in range(nc // PER)))]
    for c in range(nc):
        start = "(fun _ => 0)" if c == 0 else f"(dyFn acc28S{c})"
        hs = "fun _ _ => rfl" if c == 0 else f"fun j hj => dyFn_of_le acc28S{c} (show acc28S{c}.length ≤ j from hj)"
        out.append(f"\ntheorem acc28_e{c} : accRunQ 53 8 (acc28T{c}.map dyFn) {start} = dyFn acc28S{c + 1} :=\n"
                   f"  accRunQ_eq_dyFn 53 8 _ _ ({hs})\n    acc28S{c + 1} rfl acc28_c{c}\n")

    def run_thm(name, doc, ts, m, cut):
        return (f"\n/-- {doc} -/\ntheorem {name} : accRunQ 53 8 ({ts}.map dyFn) (fun _ => 0) = dyFn acc28S{m} := by\n"
                + cut + "  simp only [List.map_append, accRunQ_append]\n  rw ["
                + wrap([f"acc28_e{c}" for c in range(m)], ", ", 4) + "]\n")

    out.append(run_thm("acc28_run", "the levels after the 2048 terms", "acc28T", nc, "  rw [acc28T]\n"))
    for kp in pre:
        out.append(f"\n/-- the first {kp} terms, by chunks -/\ntheorem acc28_take{kp} : acc28T.take {kp} =\n    "
                   + wrap([f"acc28T{c}" for c in range(kp // CHUNK)], " ++ ", 4) + " := by\n  decide +kernel\n")
        out.append(run_thm(f"acc28_run{kp}", f"the levels after the first {kp} terms", f"(acc28T.take {kp})",
                           kp // CHUNK, f"  rw [acc28_take{kp}]\n"))
    out.append(CHECKS.replace("CHUNKS", wrap([f"acc28T{c}" for c in range(nc)], ", ", 10))
               .replace("acc28SLAST", f"acc28S{nc}"))
    out += [fill(PRE_CHECKS, kp, kp // CHUNK) for kp in pre]
    out.append(TAIL.replace("acc28SLAST", f"acc28S{nc}"))
    out += [fill(PRE_THM, kp, kp // CHUNK) for kp in pre]
    out.append(end)
    files["Prop28.lean"] = "".join(out)
    return files


if __name__ == "__main__":
    terms = [[dbl(h) for h in line.split()] for line in open(sys.argv[1])]
    for k, t in enumerate(terms, 1):
        if len(t) != N:
            sys.exit(f"term {k} has {len(t)} parts, not {N}")
    if len(sys.argv) > 3 and len(terms) != K:
        sys.exit(f"the Lean modules are for {K} terms, not {len(terms)}")
    want = [dbl(h) for h in open(sys.argv[2]).read().split()[:N]]
    states, x = run(terms)
    AWAY = True
    control = run(terms)[1]
    AWAY = False
    Z = sum(sum(t) for t in terms)
    W = sum(abs(t[0]) for t in terms)
    u = Fr(1, 2 ** P)
    u8 = u ** N
    ok = x == want and control != want
    print("the run gives the stored emulator's result:", x == want)
    print("control, ties away from zero, gives it:", control == want)
    print(f"|Z - x| / (u^8 |Z|) = {float(abs(Z - sum(x)) / (u8 * abs(Z))):.3f}; W/|Z| - 1 = {float(W / abs(Z) - 1):.4g}")
    print("every part in F:", all(rn(q) == q for t in terms for q in t),
          "; leading parts positive:", all(t[0] > 0 for t in terms),
          "; |a_(i+1)| <= u |a_i|:", all(abs(t[i + 1]) <= Fr(1, 2 ** P) * abs(t[i]) for t in terms for i in range(N - 1)))
    pre = {}
    for kp, (lo, hi) in PREFIX.items():
        if kp > len(terms):
            continue
        xp = finish(list(states[kp // CHUNK]))
        zp = sum(sum(t) for t in terms[:kp])
        r = abs(zp - sum(xp)) / (u8 * abs(zp))
        pre[kp] = (xp, zp)
        # the same test on FINISH's sum moved by u must fail
        inside = [Fr(lo) <= abs(zp - s) / (u8 * abs(zp)) <= Fr(hi) for s in (sum(xp), sum(xp) + u)]
        ok = ok and inside[0] and not inside[1]
        print(f"the first {kp} terms: |Z - x| / (u^8 |Z|) = {float(r):.7g}, between {lo} and {hi}: {inside[0]}; "
              f"control, the sum moved by u: {inside[1]}")
    w = [abs(Z) * (1 - Fr(1, 2 ** b)) < W < abs(Z) for b in (96, 97)]
    print(f"|Z|(1 - 2^-96) < W < |Z|: {w[0]}; control, with 2^-97: {w[1]}")
    size = [all((1 - Fr(1, 2 ** b)) * u <= t[0] < u for t in terms[1:]) for b in (42, 43)]
    # the test of the first term, and on a term with a second part of u, which must fail
    first = [t == [Fr(1)] + [Fr(0)] * (N - 1) for t in (terms[0], [Fr(1), u] + [Fr(0)] * (N - 2))]
    print(f"the first term is 1: {first[0]}; control, a second part of u: {first[1]}; "
          f"the other leading parts in [(1 - 2^-42)u, u): {size[0]}; control, with 2^-43: {size[1]}")
    half = [all(half_ulp(t, b) for t in terms) for b in (1, 2)]
    print(f"each part zero or at most half an ulp of the one before: {half[0]}; control, a quarter: {half[1]}")
    ok = (ok and w[0] and not w[1] and first[0] and not first[1] and size[0] and not size[1] and half[0]
          and not half[1])
    if len(sys.argv) > 3 and ok:
        os.makedirs(os.path.join(sys.argv[3], "Prop28"), exist_ok=True)
        for name, text in lean_modules(terms, states, x, Z, pre).items():
            with open(os.path.join(sys.argv[3], name), "w", encoding="utf-8") as f:
                f.write(text)
            print("wrote", os.path.join(sys.argv[3], name))
    sys.exit(0 if ok else 1)
