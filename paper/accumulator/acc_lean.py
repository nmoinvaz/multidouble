"""Proposition 28 for Lean: the accumulator's run on the constructed terms in exact rationals, written from the Lean
definitions (rnQ, twoSumQ, depSQ, addxQ, finishRQ of lean/ExpansionBounds), and the modules that hold it:
Prop28/Data.lean (the 2048 terms in chunks of 16, the levels after each chunk, FINISH's parts and the exact sums, each
as dyadic pairs (m, k) for m/2^k), Prop28/Run0.lean to Run7.lean (the kernel's run of 16 chunks each, so that they
build in parallel) and Prop28.lean (the theorem). A chunk of 16 terms keeps the kernel's memory small: one of 64 takes
2.7 GB more.

usage: acc_lean.py <terms.txt> <emu_result.txt> [lean/ExpansionBounds]
       prints whether the run gives the stored emulator's result, the error as a multiple of u^8 |Z|, and W/|Z| - 1.
       The control rounds ties away from zero and must not give the stored result. With a third argument, and when
       both come out so, it writes the Lean modules into that directory; they are for K terms."""
import os
import struct
import sys
from fractions import Fraction as Fr

P, N, CHUNK, PER = 53, 8, 16, 16  # PER chunks to a Run module
K = 2048                         # the terms of the Lean modules
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
`u`, in chunks of 16, with the accumulator's levels after each chunk, FINISH's parts, and the exact sums. Every number
is a dyadic pair `(m, k)` for `m / 2 ^ k`. This file is written by `accumulator/acc_lean.py`.
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
then `2047` positive octo-doubles of size about `u`, each part at most `u` times the one before. At `p = 53` and
`n = 8` the result of FINISH differs from the exact sum `Z` by between `14675797u^8|Z|` and `14675798u^8|Z|`, the
proposition's `1.4676·10^7u^8|Z|`. The terms are cut in chunks of 16, and the kernel checks the levels after each
chunk from those before it (`Prop28/Run0.lean` to `Run7.lean`), then FINISH and the exact sum. This file is written
by `accumulator/acc_lean.py`.
-/

namespace ExpansionBounds

open Finset
"""

CHECKS = """
set_option maxHeartbeats 4000000 in
/-- every part of every term is in `F`: `rnQ` leaves it as it is -/
theorem acc28_F : ∀ t ∈ acc28T, ∀ q ∈ t, rnQ 53 (dyQ q) = dyQ q := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- every term has a positive leading part, and each part is at most `u` times the one before -/
theorem acc28_ladder : ∀ t ∈ acc28T,
    0 < dyFn t 0 ∧ ∀ i < 7, |dyFn t (i + 1)| ≤ 1 / 9007199254740992 * |dyFn t i| := by decide +kernel

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
/-- FINISH on the levels after the 2048 terms -/
theorem acc28_finish : ∑ i ∈ range 8, finishRQ 53 8 (dyFn acc28SLAST) 8 i = (acc28X.map dyQ).sum := by
  decide +kernel

/-- the error: between `14675797u^8|Z|` and `14675798u^8|Z|` -/
theorem acc28_err :
    14675797 * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ acc28Z| ≤ |dyQ acc28Z - (acc28X.map dyQ).sum| ∧
      |dyQ acc28Z - (acc28X.map dyQ).sum| ≤ 14675798 * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ acc28Z| := by
  decide +kernel
"""

TAIL = """
variable (p : ℤ) [Prec_gt_0 p]

/-- the terms of Proposition 28: term `k` is the `k`-th row of the data -/
noncomputable def acc28 : ℕ → ℕ → ℝ := dyTerms acc28T

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
  subst hp
  have hF := dyF_of_all 53 acc28T acc28_F
  have hlen : acc28T.length = 2048 := by decide +kernel
  obtain ⟨hfin, hZ⟩ := accRun_data 53 8 (by norm_num) acc28T hF
  rw [hlen] at hfin hZ
  obtain ⟨Zq, hZq⟩ : ∃ q, q = dyQ acc28Z := ⟨_, rfl⟩
  obtain ⟨xq, hxq⟩ : ∃ q, q = (acc28X.map dyQ).sum := ⟨_, rfl⟩
  have hx : ∑ i ∈ range 8, finishR 53 8 (accLevX 53 8 acc28 2048) 8 i = (xq : ℝ) := by
    rw [hxq, ← acc28_finish, Rat.cast_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← acc28_run]
    exact hfin i
  have hZ' : ∑ k ∈ Icc 1 2048, ∑ i ∈ range 8, acc28 k i = (Zq : ℝ) := by
    rw [hZq, ← acc28_sum]
    exact hZ
  have hu : u (53 : ℤ) = ((1 / 9007199254740992 : ℚ) : ℝ) := (u_53_rat 53 rfl).symm
  obtain ⟨e1, e2⟩ := acc28_err
  rw [← hZq, ← hxq] at e1 e2
  refine ⟨fun k i => dyTerms_F 53 acc28T hF k i, fun k hk => ?_, ?_, ?_⟩
  · obtain ⟨hk1, hk2⟩ := mem_Icc.mp hk
    have hlt : k - 1 < acc28T.length := by omega
    have hmem : acc28T.getD (k - 1) [] ∈ acc28T := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
      exact List.getElem_mem hlt
    obtain ⟨l1, l2⟩ := acc28_ladder _ hmem
    refine ⟨Htheta_of_steps 53 8 _ fun i hi => ?_, ?_⟩
    · show |((dyFn (acc28T.getD (k - 1) []) (i + 1) : ℚ) : ℝ)| ≤
        u (53 : ℤ) * |((dyFn (acc28T.getD (k - 1) []) i : ℚ) : ℝ)|
      rw [hu, ← Rat.cast_abs, ← Rat.cast_abs, ← Rat.cast_mul, Rat.cast_le]
      exact l2 i (by omega)
    · show (0 : ℝ) < ((dyFn (acc28T.getD (k - 1) []) 0 : ℚ) : ℝ)
      exact_mod_cast l1
  · rw [hZ', hx, hu, ← Rat.cast_sub, ← Rat.cast_abs, ← Rat.cast_abs, ← Rat.cast_pow,
      show (14675797 : ℝ) = ((14675797 : ℚ) : ℝ) by norm_num, ← Rat.cast_mul, ← Rat.cast_mul, Rat.cast_le]
    exact e1
  · rw [hZ', hx, hu, ← Rat.cast_sub, ← Rat.cast_abs, ← Rat.cast_abs, ← Rat.cast_pow,
      show (14675798 : ℝ) = ((14675798 : ℚ) : ℝ) by norm_num, ← Rat.cast_mul, ← Rat.cast_mul, Rat.cast_le]
    exact e2

end ExpansionBounds
"""


def lean_modules(terms, states, x, Z):
    """the Lean modules, as a dictionary from each file's path under lean/ExpansionBounds to its text"""
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
    out.append("\n/-- the levels after the 2048 terms -/\n"
               f"theorem acc28_run : accRunQ 53 8 (acc28T.map dyFn) (fun _ => 0) = dyFn acc28S{nc} := by\n")
    for c in range(nc):
        hs = "fun _ _ => rfl" if c == 0 else f"fun j hj => dyFn_of_le acc28S{c} (show acc28S{c}.length ≤ j from hj)"
        out.append(f"  have e{c} := accRunQ_eq_dyFn 53 8 _ _ ({hs})\n    acc28S{c + 1} rfl acc28_c{c}\n")
    out.append("  rw [acc28T]\n  simp only [List.map_append, accRunQ_append]\n  rw ["
               + wrap([f"e{c}" for c in range(nc)], ", ", 4) + "]\n")
    out.append(CHECKS.replace("CHUNKS", wrap([f"acc28T{c}" for c in range(nc)], ", ", 10)).replace("acc28SLAST", f"acc28S{nc}"))
    out.append(TAIL)
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
    u8 = Fr(1, 2 ** (P * N))
    print("the run gives the stored emulator's result:", x == want)
    print("control, ties away from zero, gives it:", control == want)
    print(f"|Z - x| / (u^8 |Z|) = {float(abs(Z - sum(x)) / (u8 * abs(Z))):.3f}; W/|Z| - 1 = {float(W / abs(Z) - 1):.4g}")
    print("every part in F:", all(rn(q) == q for t in terms for q in t),
          "; leading parts positive:", all(t[0] > 0 for t in terms),
          "; |a_(i+1)| <= u |a_i|:", all(abs(t[i + 1]) <= Fr(1, 2 ** P) * abs(t[i]) for t in terms for i in range(N - 1)))
    ok = x == want and control != want
    if len(sys.argv) > 3 and ok:
        os.makedirs(os.path.join(sys.argv[3], "Prop28"), exist_ok=True)
        for name, text in lean_modules(terms, states, x, Z).items():
            with open(os.path.join(sys.argv[3], name), "w", encoding="utf-8") as f:
                f.write(text)
            print("wrote", os.path.join(sys.argv[3], name))
    sys.exit(0 if ok else 1)
