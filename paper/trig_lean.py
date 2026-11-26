"""Theorem 35 at n = 8 for Lean: the bounds of Lemma 34 by bucket, in exact rationals rounded up to 200 bits, written
from the Lean definitions (Eval.lean, SqrtEval.lean, TrigEval.lean of lean/ExpansionBounds), and the modules that hold
them: Trig8/Data.lean (the coefficients of the series and their lengths by bucket, multidouble's tables),
Trig8/Run0.lean to Run7.lean (Horner's run of every bucket with its own series lengths, in pieces of a few steps
checked by the kernel against the states stored there), Trig8/All.lean (the buckets together), and for the tangent
Tan8/Run0.lean to Run3.lean and Tan8/All.lean (the ladders of the computed sine and cosine and the bound of each
bucket, on the same states). Trig8/Low.lean and Tan8/Low.lean hold the smaller bounds of the buckets below the top
one, for |r_0| < 1/2 and for |r_0| < 2^-5 (the remark after Theorem 35).

The states must be the ones the Lean definitions compute, bit for bit, or the modules do not build. The bound of a
bucket is compared with trig_consts.py, which rounds at other places and agrees to more than 50 digits.

usage: trig_lean.py [lean/ExpansionBounds [12]]
       prints the bound of each run of buckets and the largest; with an argument it writes the Lean modules there,
       and with 12 after it those of n = 12 too, which the default build leaves out.
       The control drops the truncation term and must fall below trig_consts.py; the bounds for |r_0| < 2^-5 must
       not hold from |r_0| < 1/2 on."""
import os
import sys
from fractions import Fraction as Fr

import trig_consts as tc
from rounding import dec_up

P, N, BITS, STEP, MODS = 53, 8, 200, 2, 8  # STEP Horner steps to a kernel check, MODS modules
U = Fr(1, 2 ** P)
US = U / (1 + U)
BOUND = Fr(3163167393, 10 ** 9)
TAN_BOUND = Fr(6418350521, 10 ** 9)
TAN_MODS = 4
# the quotient's ladder H(theta) and a bound on kappa_DIV(theta u), in the top bucket and below (Lean's tan8Th, tan8Kd)
TAN_TH = (Fr(14143, 10000), Fr(3))
TAN_KD = (Fr(103232124), Fr(461400803))
# the bounds of the buckets from j on, for the sine and cosine and for the tangent: (j, C, C^T)
LOW = ((1, Fr(2175822, 10 ** 6), Fr(4800526, 10 ** 6)), (5, Fr(2000706, 10 ** 6), Fr(4002771, 10 ** 6)))
# the remark's bounds at other n, for the sine and cosine and for the tangent: (n, 10^6 C, 10^6 C^T, modules).
# Modules are written where their number is not zero. At n = 12 a Horner step takes the kernel about 20 seconds and
# there are about 1400 of them, so its modules are written on request only (a third argument 12), in pieces of at
# most SPLIT[12] checks, and lake builds them on request (lake build ExpansionBounds.Trig12).
OTHER = ((2, 3168701, 6452138, 1), (4, 3164155, 6426155, 2), (12, 3582787311, 4929367335, 0))
SPLIT = {12: 12}
DROP = False  # the control: no truncation term


# ---------------------------------------------------------------------------------------------------------------
# the Lean definitions, on lists
# ---------------------------------------------------------------------------------------------------------------

def log2(m):
    return m.bit_length() - 1 if m else 0


def mag(q):
    """Lean's magQ"""
    e = log2(abs(q.numerator)) - log2(q.denominator)
    return e + 1 if Fr(2) ** e <= abs(q) else e


def up(q):
    """Lean's upQ BITS"""
    s = Fr(2) ** (BITS - mag(q))
    x = q * s
    return Fr(-((-x.numerator) // x.denominator)) / s


def Vb(X, j):
    return min(X[j - 1], US * (1 + U) ** (N - j) * sum(X[j - 1:N + 1]))


def g_parts(X, Zb, Fb):
    V = [None] + [Vb(X, j) for j in range(1, N + 1)]
    out = [(1 + U) * (Zb + Fb + sum(V[2:N + 1]))]
    for i in range(N - 1):
        out.append((1 + U) * (U * out[i] + sum(V[i + 2:N + 1])))
    return out


def g_err(X, Zb, Fb):
    return U ** N * Zb + (1 + U ** N) * Fb + sum((U ** N + U ** (N + 1 - j)) * Vb(X, j) for j in range(1, N + 1))


def lev_d(A, T):
    D = [A[0]]
    for m in range(N):
        D.append(A[m + 1] + T(m) * U * D[m] / (1 - T(m) * U))
    return D


def mul_x(a, b):
    """(X_0 .. X_n, R + Delta) of MUL"""
    Pm = lambda m: sum(a[i] * b[m - i] for i in range(N) if 0 <= m - i < N)
    A = [(1 + U) * Pm(m) + (U * Pm(m - 1) if m else 0) for m in range(N)] + [Pm(N) + U * Pm(N - 1)]
    T = lambda m: m * (m + 1)
    D = lev_d(A, T)
    Q = N * N + N - 1
    X = [D[m] / (1 - T(m) * U) for m in range(N)] + [D[N] / (1 - Q * U)]
    delta = sum(a[i] * b[j] for i in range(N) for j in range(N) if i + j > N)
    return X, Q * U * X[N] + delta


def pair_x(lam):
    """(X_0 .. X_n, R) of ADD"""
    A = [(1 + U) * lam[m] + (U * lam[m - 1] if m else 0) for m in range(N)] + [U * lam[N - 1]]
    T = lambda m: m
    D = lev_d(A, T)
    X = [D[m] / (1 - T(m) * U) for m in range(N)] + [D[N] / (1 - (N - 1) * U)]
    return X, (N - 1) * U * X[N]


def addf_x(al, lam0):
    e = [U * lam0]
    for m in range(N - 1):
        e.append(U * (al[m + 1] + e[m]))
    return [(1 + U) * lam0] + [(1 + U) * (al[m] + e[m - 1]) for m in range(1, N)] + [e[N - 1]]


def g_mul(a, b, Zb):
    X, F = mul_x(a, b)
    return g_err(X, Zb, F), g_parts(X, Zb, F)


def g_add(a, b, Zb):
    X, F = pair_x([x + y for x, y in zip(a, b)])
    return g_err(X, Zb, F), g_parts(X, Zb, F)


def set_n(n, kd=None):
    """the number of parts, with the part bounds of r and of z = r^2 at that n and the bounds kd on kappa_DIV"""
    global N, AB, EZ, ZETA, TAN_KD
    N = n
    if kd:
        TAN_KD = kd
    AB = [(2 * U) ** i * ((1 - 2 * U) / (1 - 4 * U)) for i in range(N)]
    ez, zeta = g_mul(AB, AB, Fr(1))
    EZ = up(ez)
    ZETA = [up(x) for x in zeta]


set_n(N)


def rbar(j):
    return Fr(78541, 100000) if j == 0 else Fr(1, 2 ** j) * (1 + Fr(1, 2 ** 50))


def coef(sine, k):
    return Fr((-1) ** k, tc.fact(2 * k + 1) if sine else tc.fact(2 * k))


def horner_step(rb, sine, F, k, st):
    """Lean's hornerStepL with pi^z = rb^2 zeta, zb = rb^2, eta = 0"""
    e1, p1 = st
    zb = rb * rb
    pz = [zb * z for z in ZETA]
    v1, vk = abs(coef(sine, k + 1)), abs(coef(sine, k))
    phi = abs(sum(F[k]) - coef(sine, k))
    Zm = (1 + EZ) * zb * (v1 + e1)
    em, mu = g_mul(pz, p1, Zm)
    D = (1 + EZ) * zb * e1 + EZ * zb * v1 + phi + em
    ea, pa = g_add([abs(x) for x in F[k]], mu, vk + D)
    return up(D + ea), [up(x) for x in pa]


def horner_states(rb, sine, F, K):
    """the states of Horner's run after 0, STEP, 2 STEP, ... and K - 2 steps (the first is not dyadic)"""
    d = K - 1
    st = (abs(sum(F[d]) - coef(sine, d)), [abs(x) for x in F[d]])
    out = [(0, st)]
    for j in range(K - 2):
        st = horner_step(rb, sine, F, d - (j + 1), st)
        if (j + 1) % STEP == 0 or j + 1 == K - 2:
            out.append((j + 1, st))
    return out


def tail(rb, sine, K, st):
    """Lean's (sinDeltaL, sinPsiL) or (cosDeltaL, cosPsiL)"""
    c1 = abs(coef(sine, 1))
    Zt = (1 + EZ) * (c1 + st[0])
    et, th = g_mul(ZETA, st[1], Zt)
    th = [up(x) for x in th]
    Et = up((1 + EZ) * st[0] + EZ * c1 + et)
    zb = rb * rb
    if sine:
        ew, om = g_mul(AB, th, c1 + Et)
        om = [up(x) for x in om]
        D = up(zb * (Et + ew) + (0 if DROP else rb ** (2 * K) / tc.fact(2 * K + 1)))
        ey, psi = g_add(AB, [zb * x for x in om], 1 + D)
        return U ** N + (D + ey - U ** N) / (1 - zb / 6), psi
    D = up(zb * Et + (0 if DROP else rb ** (2 * K) / tc.fact(2 * K)))
    al = [zb * x for x in th]
    X = addf_x(al, al[0] + 1)
    return U ** N + (D + g_err(X, 1 + D, Fr(0)) - U ** N) / tc.cos_lo(rb), g_parts(X, 1 + D, Fr(0))


def trig_c(dS, dC, rb):
    eps = 1 + 2 * U ** N
    return eps * max(dS + eps * U ** N, dC + eps * U ** N * (rb * tc.tan_hi(rb)))


def tan_c(j, dS, dC, psS, psC):
    """Lean's tan8Chk: C^T of bucket j, or None if the computed sine and cosine are not on H(theta)"""
    rb = rbar(j)
    th, Kd = TAN_TH[min(j, 1)], TAN_KD[min(j, 1)]
    lamS = (1 - rb * rb / 6) * (1 - dS) - sum(psS[1:])
    lamC = tc.cos_lo(rb) * (1 - dC) - sum(psC[1:])
    ok = (dS <= Fr(1, 10) and dC <= Fr(1, 10) and lamS > 0 and lamC > 0
          and all(psS[i] <= (th * U) ** i * lamS and psC[i] <= (th * U) ** i * lamC for i in range(1, N)))
    dD = U ** N + Kd * U ** (N + 1)
    eps = 1 + 2 * U ** N
    C = eps * (max((1 + dS) * (1 + dD) / (1 - dC), (1 + dC) * (1 + dD) / (1 - dS)) - 1
               + eps * U ** N * (2 * rb / tc.sin_lo(2 * rb)))
    return C if ok else None


# ---------------------------------------------------------------------------------------------------------------
# the tables and the buckets
# ---------------------------------------------------------------------------------------------------------------

def tables():
    """multidouble's coefficients and series lengths, which must be the greedy roundings and trig_consts.py's K"""
    rust = tc.rust_tables()
    ks, kc = rust['KS8'], rust['KC8']
    tc.require(ks == tc.k_table(N, True) and kc == tc.k_table(N, False), 'the series lengths differ')
    kmax = max(max(ks), max(kc))
    F = {}
    for name, sine in (('SIN', True), ('COS', False)):
        F[sine] = [[Fr(x) for x in tc.greedy(coef(sine, k), N)] for k in range(kmax)]
        import struct
        bits = [[struct.unpack('>Q', struct.pack('>d', float(x)))[0] for x in row] for row in F[sine]]
        tc.require(bits == [r[:N] for r in rust[name][:kmax]], f'{name} differs from the greedy rounding')
    groups = []
    for j, pr in enumerate(zip(ks, kc)):
        if not groups or groups[-1][1:] != pr:
            groups.append((j,) + pr)
    return F, groups


def tables_n(n):
    """the greedy coefficients and trig_consts.py's series lengths at n parts"""
    ks, kc = tc.k_table(n, True), tc.k_table(n, False)
    kmax = max(max(ks), max(kc))
    F = {sine: [[Fr(x) for x in tc.greedy(coef(sine, k), n)] for k in range(kmax)] for sine in (True, False)}
    groups = []
    for j, pr in enumerate(zip(ks, kc)):
        if not groups or groups[-1][1:] != pr:
            groups.append((j,) + pr)
    return F, groups


class Names:
    """the Lean names of a table's run: Trig8/Defs.lean at n = 8, TrigN/Defs.lean on the table `trig<n>Tab` otherwise"""

    def __init__(self, n):
        self.pre = f'trig{n}'
        if n == 8:
            self.run, self.init, self.cut = 'trig8Run', 'trig8Init', 'trig8Run_cut'
            self.ok, self.group, self.fs, self.fc = 'trig8Ok', 'Trig8Group', 'trig8FsQ', 'trig8FcQ'
        else:
            tab = f'trig{n}Tab'
            self.run, self.init, self.cut = f'{tab}.run', f'{tab}.init', f'TrigTab.run_cut {tab}'
            self.ok, self.group = f'{tab}.Ok trig{n}C', f'{tab}.Group trig{n}C'
            self.fs, self.fc = f'{tab}.FsQ', f'{tab}.FcQ'
            self.tan = f'trig{n}Ct trig{n}Kd0 trig{n}Kd3'


def pair(q):
    k = q.denominator.bit_length() - 1
    assert q.denominator == 1 << k, 'a state is not dyadic'
    return f'({q.numerator}, {k})'


def wrap(items, sep, indent, width=120):
    lines, cur = [], ''
    for it in items:
        piece = it if not cur else cur + sep + it
        if cur and len(piece) + indent + len(sep) > width:
            lines.append(cur + sep.rstrip())
            cur = it
        else:
            cur = piece
    lines.append(cur)
    return ('\n' + ' ' * indent).join(lines)


DATA = '''import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation

/-!
# Theorem 35 at `n = 8` and `p = 53`: multidouble's tables

The eight parts of the coefficients `s_k = (-1)^k/(2k + 1)!` and `c_k = (-1)^k/(2k)!` of SINR and COSR, each the
greedy rounding to eight binary64 numbers, as dyadic pairs `(m, k)` for `m / 2 ^ k`, and the series lengths: `(j, K_s,
K_c)` for the first bucket `j` of each run of buckets with the same lengths, bucket `j` being `2^{-(j+1)} ≤ |r_0| <
2^{-j}`. They are `SIN`, `COS`, `KS8` and `KC8` of multidouble's `src/trig/tables.rs`. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds
'''

RUN = '''import ExpansionBounds.Trig8.Defs

/-!
# Theorem 35 at `n = 8` and `p = 53`: Horner's runs of the buckets FIRST

Each run is checked by the kernel in pieces of at most STEP steps, from the state before a piece to the state after
it, and then `trig8Ok` on the last states. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds
'''

TAN_RUN = '''import ExpansionBounds.Tan8.Defs

/-!
# Theorem 35 for the tangent at `n = 8` and `p = 53`: the buckets FIRST

`tan8Ok` on the last states of Horner's runs, which `Trig8/Run0.lean` to `Run7.lean` check. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds
'''

ALL = '''IMPORTS

/-!
# Theorem 35 at `n = 8` and `p = 53`: every bucket

`Trig8Group` holds for each run of buckets with the same series lengths. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig8_all : ∀ g ∈ trig8Groups, Trig8Group g := by
  intro g hg
  simp only [trig8Groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with CASES
EXACTS

end ExpansionBounds
'''


LOW_T = '''import ExpansionBounds.%WHAT8.All

/-!
# Theorem 35 %TITLE at `n = 8` and `p = 53`: the buckets below the top one

`%SYM` is at most `%D1u^8` in the runs of buckets with `|r_0| < 1/2` and at most `%D5u^8` in those with
`|r_0| < 2^{-5}`, on the last states of Horner's runs, which `Trig8/Run0.lean` to `Run7.lean` check. This file is
written by `trig_lean.py`.
-/

namespace ExpansionBounds

/-- `%SYM ≤ c u^8` in bucket `j`, from the last states of Horner's runs for the sine and the cosine -/
def %LE (c : ℚ) (j Ks Kc : ℕ) (sS sC : ℚ × List ℚ) : Prop :=
  %BODY ≤ c * trig8U ^ 8

instance (c : ℚ) (j Ks Kc : ℕ) (sS sC : ℚ × List ℚ) : Decidable (%LE c j Ks Kc sS sC) := by
  unfold %LE
  infer_instance

/-- the bound of a run of buckets that starts at `j ≥ 1`: `%D1` below `j = 5` and `%D5` from there on -/
def %LOWF (j : ℕ) : ℚ := if j < 5 then %Q1 else %Q5

/-- a run of buckets from `j ≥ 1`: Horner's runs end in states on which `%SYM ≤ %LOWF j u^8` -/
def %GROUP (g : ℕ × ℕ × ℕ) : Prop :=
  ∃ sS sC, trig8Run sinCQ trig8FsQ g.1 (g.2.1 - 1) 0 (g.2.1 - 2) (trig8Init sinCQ trig8FsQ (g.2.1 - 1)) = sS ∧
    trig8Run cosCQ trig8FcQ g.1 (g.2.2 - 1) 0 (g.2.2 - 2) (trig8Init cosCQ trig8FcQ (g.2.2 - 1)) = sC ∧
    %LE (%LOWF g.1) g.1 g.2.1 g.2.2 sS sC
%CHECKS
/-- every run of buckets from `j = 1` on -/
theorem %ALLNAME : ∀ g ∈ trig8Groups, 1 ≤ g.1 → %GROUP g := by
  intro g hg h1
  simp only [trig8Groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with %CASES
%EXACTS

end ExpansionBounds
'''


def low_text(groups, states, tan):
    """Trig8/Low.lean or Tan8/Low.lean: the kernel's check of the smaller bound in each run of buckets from 1 on"""
    le, lowf, pre = ('tan8CtLe', 'tan8Low', 'tan8') if tan else ('trig8CLe', 'trig8Low', 'trig8')
    deltas = ('(sinDeltaL trig8U 8 (upQ 200) trig8Ab (trig8Rb j) Ks sS)\n'
              '    (cosDeltaL trig8U 8 (upQ 200) trig8Ab (trig8Rb j) Kc sC)')
    body = (f'tanCTQ trig8U 8 {deltas} (trig8U ^ 8 + tan8Kd j * trig8U ^ 9)\n    (trig8Rb j)' if tan
            else f'trigCQ trig8U 8 {deltas} (trig8Rb j)')
    c1, c5 = (LOW[0][2], LOW[1][2]) if tan else (LOW[0][1], LOW[1][1])
    checks = ''.join(f'\nset_option maxHeartbeats 4000000 in\ntheorem {pre}_low{j} : {le} ({lowf} {j}) {j} {Ks} {Kc} '
                     f'{states[j][0]}\n    {states[j][1]} := by\n  decide +kernel\n' for j, Ks, Kc in groups if j >= 1)
    exacts = '\n'.join('  · exact absurd h1 (by decide)' if j == 0 else
                       f'  · exact ⟨_, _, trig8_s{j}, trig8_c{j}, {pre}_low{j}⟩' for j, _, _ in groups)
    fill = {'%WHAT': 'Tan' if tan else 'Trig', '%TITLE': 'for the tangent' if tan else 'for the sine and the cosine',
            '%SYM': 'C^T' if tan else 'C', '%LE': le, '%LOWF': lowf, '%GROUP': 'Tan8Low' if tan else 'Trig8Low',
            '%ALLNAME': f'{pre}_low', '%BODY': body, '%CHECKS': checks, '%EXACTS': exacts,
            '%CASES': wrap(['rfl'] * len(groups), ' | ', 4), '%D1': dec_up(c1, 6), '%D5': dec_up(c5, 6),
            '%Q1': f'{int(c1 * 10 ** 6)} / 1000000', '%Q5': f'{int(c5 * 10 ** 6)} / 1000000'}
    t = LOW_T
    for k, v in fill.items():
        t = t.replace(k, v)
    return t


def group_parts(F, j, Ks, Kc, nm=None):
    """for bucket j, with the Lean names nm: for the sine and for the cosine the stored states, the kernel's checks
    of the pieces of Horner's run and the run's theorem; then the check on the last states and the group's theorem"""
    nm = nm or Names(8)
    q = nm.pre
    rb = rbar(j)
    segs, last = [], {}
    for sine, K, tag, C, Fq in ((True, Ks, 's', 'sinCQ', nm.fs), (False, Kc, 'c', 'cosCQ', nm.fc)):
        sts = horner_states(rb, sine, F[sine], K)
        d = K - 1
        defs = [f'\ndef {q}_{tag}{j}_{a} : (ℤ × ℕ) × List (ℤ × ℕ) :=\n  ({pair(st[0])},\n    ['
                + wrap([pair(x) for x in st[1]], ', ', 5) + '])\n' for a, st in sts[1:]]
        names, pieces = [], []
        for (a, _), (b, _) in zip(sts, sts[1:]):
            start = f'({nm.init} {C} {Fq} {d})' if a == 0 else f'(dySt {q}_{tag}{j}_{a})'
            names.append((f'{q}_{tag}{j}_{a}_{b}', b - a))
            pieces.append(f'\nset_option maxHeartbeats 4000000 in\ntheorem {q}_{tag}{j}_{a}_{b} :\n'
                          f'    {nm.run} {C} {Fq} {j} {d} {a} {b - a} {start} = dySt {q}_{tag}{j}_{b} := by\n'
                          '  decide +kernel\n')
        if K == 2:
            last[tag] = f'({nm.init} {C} {Fq} {d})'
            chain = (f'\ntheorem {q}_{tag}{j} : {nm.run} {C} {Fq} {j} {d} 0 0 ({nm.init} {C} {Fq} {d}) =\n'
                     f'    {nm.init} {C} {Fq} {d} := rfl\n')
        else:
            last[tag] = f'(dySt {q}_{tag}{j}_{K - 2})'
            term = names[-1][0]
            rest = names[-1][1]
            for name, m in reversed(names[:-1]):
                term = f'{nm.cut} {C} {Fq} {j} {d} _ {m} {rest} {name}\n    ({term})'
                rest += m
            chain = (f'\ntheorem {q}_{tag}{j} : {nm.run} {C} {Fq} {j} {d} 0 {K - 2} ({nm.init} {C} {Fq} {d}) =\n'
                     f'    dySt {q}_{tag}{j}_{K - 2} :=\n  {term}\n')
        segs.append((defs, pieces, chain))
        last[tag + 'v'], last[tag + 'p'] = tail(rb, sine, K, sts[-1][1])
    ok = (f'\nset_option maxHeartbeats 4000000 in\ntheorem {q}_ok{j} : {nm.ok} {j} {Ks} {Kc} {last["s"]} {last["c"]} := by\n'
          '  decide +kernel\n')
    grp = f'\ntheorem {q}_g{j} : {nm.group} ({j}, {Ks}, {Kc}) :=\n  ⟨_, _, {q}_s{j}, {q}_c{j}, {q}_ok{j}⟩\n'
    return segs, ok, grp, last, (last['sv'], last['cv'], last['sp'], last['cp'])


def group_text(F, j, Ks, Kc, nm=None):
    """the states, the kernel's checks and the group's theorem for bucket j, with the Lean names nm, as one text"""
    segs, ok, grp, last, deltas = group_parts(F, j, Ks, Kc, nm)
    return ''.join(''.join(d) + ''.join(pc) + ch for d, pc, ch in segs) + ok + grp, last, deltas


DATA_N = '''import ExpansionBounds.TrigN.Defs

/-!
# Theorem 35 at `n = %N` and `p = 53`: the tables

The %N parts of the coefficients `s_k = (-1)^k/(2k + 1)!` and `c_k = (-1)^k/(2k)!` of SINR and COSR, each the greedy
rounding to %N binary64 numbers, as dyadic pairs `(m, k)` for `m / 2 ^ k`, and the series lengths: `(j, K_s, K_c)` for
the first bucket `j` of each run of buckets with the same lengths, bucket `j` being `2^{-(j+1)} ≤ |r_0| < 2^{-j}`.
The lengths are those of `trig_consts.py`. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds
'''

RUN_N = '''import ExpansionBounds.Trig%N.Data

/-!
# Theorem 35 at `n = %N` and `p = 53`: Horner's runs of the buckets FIRST

Each run is checked by the kernel in pieces of at most STEP steps, from the state before a piece to the state after
it, and then `TrigTab.Ok` and, for the tangent, `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds
'''

ALL_N = '''IMPORTS

/-!
# Theorem 35 at `n = %N` and `p = 53`: every bucket

`TrigTab.Group` and `TrigTab.TanGroup` hold for each run of buckets with the same series lengths. This file is
written by `trig_lean.py`.
-/

namespace ExpansionBounds

theorem trig%N_all : ∀ g ∈ trig%NTab.groups, trig%NTab.Group trig%NC g := by
  intro g hg
  change g ∈ trig%NGroups at hg
  simp only [trig%NGroups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with CASES
EXACTS

theorem tan%N_all : ∀ g ∈ trig%NTab.groups, trig%NTab.TanGroup trig%NCt trig%NKd0 trig%NKd3 g := by
  intro g hg
  change g ∈ trig%NGroups at hg
  simp only [trig%NGroups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with CASES
TEXACTS

end ExpansionBounds
'''

TOP_N = '''import ExpansionBounds.Trig%N.All
import ExpansionBounds.TrigN

/-!
# Theorem 35 at `n = %N` and `p = 53`: the sine and the cosine within `%Cu^%N`, the tangent within `%Tu^%N`

The remark after Theorem 35 at `n = %N`: SIN and COS with the coefficients and series lengths of
`Trig%N/Data.lean`, on `x` in `F`, on `H(2)` and with `|x_0| ≤ 2^52`, are within `%Cu^%N` of `sin x` and
`cos x`, relatively, plus `5E_π`, and TAN, for `x` at least `2^{%Np-1074}` away from the nonzero multiples
of `π/2`, within `%Tu^%N + 5E_π/|sin x cos x|` of `tan x`, relatively. The kernel checks the tables,
`κ_DIV` on the quotient's two ladders, the bounds below the last bucket and, in `Trig%N/Run0.lean` on, every
run of buckets; `thm35_sincos_tab` and `thm35_tan_tab` do the rest. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

open Finset

theorem trig%N_tab : trig%NTab.TabOk := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem trig%N_tiny : trig%NTab.TinyOk trig%NC := by decide +kernel

variable (p : ℤ) [Prec_gt_0 p]

/-- the remark after Theorem 35 at `n = %N`: the sine and the cosine are within `%Cu^%N` of `sin x` and `cos x`,
relatively, plus `5E_π` -/
theorem thm35_sincos_%N (hp : p = 53) (x : ℕ → ℝ) (hx : ∀ i < %N, F p (x i)) (hH : Htheta p %N 2 x)
    (hx0 : |x 0| ≤ 2 ^ 52) (es : ℝ → ℤ) :
    |∑ i ∈ range %N, sinN p %N es trig%NTab.Ks trig%NTab.Kc trig%NTab.FsR trig%NTab.FcR x i -
          Real.sin (∑ i ∈ range %N, x i)| ≤
        %Q * u p ^ %N * |Real.sin (∑ i ∈ range %N, x i)| +
          5 * (|(redK p %N x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) ∧
      |∑ i ∈ range %N, cosN p %N es trig%NTab.Ks trig%NTab.Kc trig%NTab.FsR trig%NTab.FcR x i -
          Real.cos (∑ i ∈ range %N, x i)| ≤
        %Q * u p ^ %N * |Real.cos (∑ i ∈ range %N, x i)| +
          5 * (|(redK p %N x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) := by
  have h := thm35_sincos_tab p trig%NTab trig%NC (by decide) (by decide) ⟨_, _, rfl⟩ trig%N_tab trig%N_tiny
    trig%N_all hp x hx hH hx0 es
  rw [show ((trig%NC : ℚ) : ℝ) = %Q by unfold trig%NC; norm_num] at h
  exact h

omit [Prec_gt_0 p] in
set_option maxHeartbeats 4000000 in
theorem trig%N_kdiv : trig%NTab.KdivOk trig%NKd0 trig%NKd3 := by decide +kernel

omit [Prec_gt_0 p] in
set_option maxHeartbeats 4000000 in
theorem tan%N_tiny : trig%NTab.TanTinyOk trig%NCt trig%NKd3 := by decide +kernel

/-- the remark after Theorem 35 at `n = %N`: for `x` at least `2^{%Np-1074}` away from the nonzero multiples of `π/2`,
the tangent is within `%Tu^%N + 5E_π/|sin x cos x|` of `tan x`, relatively -/
theorem thm35_tan_%N (hp : p = 53) (x : ℕ → ℝ) (hx : ∀ i < %N, F p (x i)) (hH : Htheta p %N 2 x)
    (hx0 : |x 0| ≤ 2 ^ 52) (es et : ℝ → ℤ)
    (hfar : redK p %N x ≠ 0 →
      (2 : ℝ) ^ (p * (%N : ℕ) - 1074) ≤ |∑ i ∈ range %N, x i - redK p %N x * (Real.pi / 2)|) :
    |∑ i ∈ range %N, tanN p %N es et trig%NTab.Ks trig%NTab.Kc trig%NTab.FsR trig%NTab.FcR x i -
        Real.tan (∑ i ∈ range %N, x i)| ≤
      (%R * u p ^ %N + 5 * (|(redK p %N x : ℝ)| * (2 : ℝ) ^ (-1217 : ℤ)) /
        |Real.sin (∑ i ∈ range %N, x i) * Real.cos (∑ i ∈ range %N, x i)|) * |Real.tan (∑ i ∈ range %N, x i)| := by
  have h := thm35_tan_tab p trig%NTab trig%NCt trig%NKd0 trig%NKd3 (by decide) (by decide) ⟨_, _, rfl⟩ trig%N_tab
    trig%N_kdiv tan%N_tiny tan%N_all hp x hx hH hx0 es et hfar
  rw [show ((trig%NCt : ℚ) : ℝ) = %R by unfold trig%NCt; norm_num] at h
  exact h

end ExpansionBounds
'''


CONTROLS_N = '''IMPORTS

/-!
# Controls of the remark after Theorem 35: the bounds at `n = 2` and `4`

Each claim below is one of the kernel's checks of `Trig2.lean` and `Trig4.lean` with a bound one unit lower in its
last digit, in the run of buckets where it is largest, or with a bound on `κ_DIV` one unit lower, and the kernel
proves its negation. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

open Finset
'''


# a table outside the default build is outside its audit of axioms, so its controls repeat the audit with its modules
AUDIT_N = '''
open Lean Elab Command in
run_cmd liftCoreM do
  let decls ← Controls.proofDecls
  unless decls.contains ``ExpansionBounds.thm35_sincos_N && decls.contains ``ExpansionBounds.thm35_tan_N do
    throwError "the theorems at n = N are not among the declarations read"
  let mut bad : Array (Name × Array Name) := #[]
  for c in decls do
    let ax ← Controls.otherAxioms c
    unless ax.isEmpty do bad := bad.push (c, ax)
  unless bad.isEmpty do
    throwError "declarations with other axioms: {bad}"
  logInfo m!"{decls.size} declarations with Trig N: no axiom other than propext, Classical.choice and Quot.sound"
'''


def controls_n(n, c, ct, rows, lasts):
    """the controls of the checks at n: each bound one unit lower where it is largest, and kappa_DIV one unit lower"""
    tab = f'trig{n}Tab'
    jc, Ks, Kc = max(rows, key=lambda r: r[5])[:3]
    jt, Kst, Kct = max(rows, key=lambda r: r[6])[:3]
    sS, sC = lasts[jc]
    head = '\nset_option maxHeartbeats 4000000 in\n'
    return (
        f'{head}/-- at `n = {n}`, `C` in bucket {jc} is not below `{dec_up(Fr(c - 1, 10 ** 6), 6)}u^{n}` -/\n'
        f'example : ¬ trigCQ trig8U {n} (sinDeltaL trig8U {n} (upQ 200) trig8Ab (trig8Rb {jc}) {Ks} {sS})\n'
        f'    (cosDeltaL trig8U {n} (upQ 200) trig8Ab (trig8Rb {jc}) {Kc} {sC}) (trig8Rb {jc}) ≤\n'
        f'      {c - 1} / 1000000 * trig8U ^ {n} := by\n  decide +kernel\n'
        f'{head}/-- at `n = {n}`, the tangent\'s check in bucket {jt} fails with `{dec_up(Fr(ct - 1, 10 ** 6), 6)}u^{n}` -/\n'
        f'example : ¬ {tab}.TanOk ({ct - 1} / 1000000) trig{n}Kd0 trig{n}Kd3 {jt} {Kst} {Kct} {lasts[jt][0]}\n'
        f'    {lasts[jt][1]} := by\n  decide +kernel\n'
        f'{head}/-- at `n = {n}`, `κ_DIV(1.4143u)` is not within `{TAN_KD[0] - 1}` -/\n'
        f'example : ¬ {tab}.KdivOk {TAN_KD[0] - 1} trig{n}Kd3 := by\n  decide +kernel\n'
        f'{head}/-- at `n = {n}`, `κ_DIV(3u)` is not within `{TAN_KD[1] - 1}` -/\n'
        f'example : ¬ {tab}.KdivOk trig{n}Kd0 {TAN_KD[1] - 1} := by\n  decide +kernel\n')


def data_n(n, F, groups, q, qt):
    """the text of Trig<n>/Data.lean, less its last line: the tables, the groups and the constants"""
    data = [DATA_N.replace('%N', str(n))]
    for sine, name, what in ((True, f'trig{n}Fs', "SINR's"), (False, f'trig{n}Fc', "COSR's")):
        rows = ['  [' + ', '.join(pair(x) for x in row) + ']' for row in F[sine]]
        # elaborating a long table of long numerals passes the default limit
        data.append(f'\nset_option maxHeartbeats 4000000 in\n/-- the parts of {what} coefficients -/\n'
                    f'def {name} : List (List (ℤ × ℕ)) := [\n' + ',\n'.join(rows) + ']\n')
    data.append('\n/-- `(j, K_s, K_c)` for the first bucket `j` of each run of buckets with the same series lengths -/\n'
                f'def trig{n}Groups : List (ℕ × ℕ × ℕ) :=\n  ['
                + wrap([f'({j}, {a}, {b})' for j, a, b in groups], ', ', 3) + ']\n')
    data.append(f'\n/-- the table at `n = {n}` -/\ndef trig{n}Tab : TrigTab := ⟨{n}, trig{n}Fs, trig{n}Fc, trig{n}Groups⟩\n'
                f'\n/-- the bound of the remark after Theorem 35, in units of `u^{n}` -/\ndef trig{n}C : ℚ := {q}\n'
                f'\n/-- the tangent\'s bound in the remark, in units of `u^{n}` -/\ndef trig{n}Ct : ℚ := {qt}\n'
                f'\n/-- a bound on `κ_DIV(1.4143u)` at `n = {n}` -/\ndef trig{n}Kd0 : ℚ := {TAN_KD[0]}\n'
                f'\n/-- a bound on `κ_DIV(3u)` at `n = {n}` -/\ndef trig{n}Kd3 : ℚ := {TAN_KD[1]}\n')
    return ''.join(data)


def lean_modules_n(n, c, ct, mods):
    """the modules of the remark's bounds c and ct, in millionths, at n: the table, Horner's runs, their union and the
    theorems; N must be n"""
    F, groups = tables_n(n)
    nm = Names(n)
    end = '\nend ExpansionBounds\n'
    q, qt = f'{c} / 1000000', f'{ct} / 1000000'
    cm, ctm, c, ct = c, ct, Fr(c, 10 ** 6), Fr(ct, 10 ** 6)
    files = {f'Trig{n}/Data.lean': data_n(n, F, groups, q, qt) + end}
    cost = lambda g: g[1] + g[2] + 4
    bins = [[] for _ in range(mods)]
    for g in sorted(groups, key=cost, reverse=True):
        min(bins, key=lambda b: sum(cost(x) for x in b)).append(g)
    rows, lasts = [], {}
    for i, b in enumerate(bins):
        b.sort()
        body = [RUN_N.replace('%N', str(n)).replace('FIRST', ', '.join(str(g[0]) for g in b)).replace('STEP', str(STEP))]
        for j, Ks, Kc in b:
            text, last, (dS, dC, psS, psC) = group_text(F, j, Ks, Kc, nm)
            body.append(text)
            body.append(f'\nset_option maxHeartbeats 4000000 in\ntheorem tan{n}_ok{j} :\n'
                        f'    trig{n}Tab.TanOk {nm.tan} {j} {Ks} {Kc} {last["s"]} {last["c"]} := by\n'
                        '  decide +kernel\n'
                        f'\ntheorem tan{n}_g{j} : trig{n}Tab.TanGroup {nm.tan} ({j}, {Ks}, {Kc}) :=\n'
                        f'  ⟨_, _, trig{n}_s{j}, trig{n}_c{j}, tan{n}_ok{j}⟩\n')
            rows.append((j, Ks, Kc, dS, dC, trig_c(dS, dC, rbar(j)), tan_c(j, dS, dC, psS, psC)))
            lasts[j] = (last['s'], last['c'])
        files[f'Trig{n}/Run{i}.lean'] = ''.join(body) + end
    rows.sort()
    files[f'Trig{n}/All.lean'] = (
        ALL_N.replace('IMPORTS', '\n'.join(f'import ExpansionBounds.Trig{n}.Run{i}' for i in range(mods)))
        .replace('%N', str(n)).replace('CASES', wrap(['rfl'] * len(groups), ' | ', 4))
        .replace('TEXACTS', '\n'.join(f'  · exact tan{n}_g{j}' for j, _, _ in groups))
        .replace('EXACTS', '\n'.join(f'  · exact trig{n}_g{j}' for j, _, _ in groups)))
    files[f'Trig{n}.lean'] = (TOP_N.replace('%N', str(n)).replace('%C', str(dec_up(c, 6))).replace('%Q', q)
                              .replace('%T', str(dec_up(ct, 6))).replace('%R', qt))
    return files, rows, controls_n(n, cm, ctm, rows, lasts)


STATES_N = '''import ExpansionBounds.Trig%N.Data

/-!
# Theorem 35 at `n = %N` and `p = 53`: the stored states of Horner's runs in bucket %J

The states after each piece of the sine's and of the cosine's run, as dyadic pairs. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds
'''

PIECES_N = '''import ExpansionBounds.Trig%N.S%J

/-!
# Theorem 35 at `n = %N` and `p = 53`: pieces of Horner's runs in bucket %J

Each piece of at most STEP steps is checked by the kernel, from the state before it to the state after it. A module
holds at most %P of them: at `n = %N` a piece takes the kernel most of a minute, and its memory adds up over a
module. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds
'''

GROUP_N = '''IMPORTS

/-!
# Theorem 35 at `n = %N` and `p = 53`: bucket %J

The pieces of Horner's runs joined, and `TrigTab.Ok` and `TrigTab.TanOk` on the last states. This file is written by
`trig_lean.py`.
-/

namespace ExpansionBounds
'''


def lean_modules_split(n, c, ct, per):
    """the modules of the remark's bounds at an n whose checks are slow: as lean_modules_n, with the states of a
    bucket in Trig<n>/S<j>.lean, its pieces in modules Trig<n>/R<j>_<k>.lean of at most `per` checks, and its
    theorems in Trig<n>/G<j>.lean; N must be n"""
    F, groups = tables_n(n)
    nm = Names(n)
    end = '\nend ExpansionBounds\n'
    q, qt = f'{c} / 1000000', f'{ct} / 1000000'
    cm, ctm, c, ct = c, ct, Fr(c, 10 ** 6), Fr(ct, 10 ** 6)
    files = {f'Trig{n}/Data.lean': data_n(n, F, groups, q, qt) + end}
    fill = lambda t, j: t.replace('%N', str(n)).replace('%J', str(j)).replace('%P', str(per)).replace('STEP', str(STEP))
    rows, lasts = [], {}
    for j, Ks, Kc in groups:
        segs, ok, grp, last, (dS, dC, psS, psC) = group_parts(F, j, Ks, Kc, nm)
        files[f'Trig{n}/S{j}.lean'] = fill(STATES_N, j) + ''.join(''.join(d) for d, _, _ in segs) + end
        pieces = [x for _, pc, _ in segs for x in pc]
        chunks = [pieces[i:i + per] for i in range(0, len(pieces), per)]
        for k, ch in enumerate(chunks):
            files[f'Trig{n}/R{j}_{k}.lean'] = fill(PIECES_N, j) + ''.join(ch) + end
        imports = [f'import ExpansionBounds.Trig{n}.R{j}_{k}' for k in range(len(chunks))]
        imports = imports or [f'import ExpansionBounds.Trig{n}.S{j}']
        files[f'Trig{n}/G{j}.lean'] = (
            fill(GROUP_N, j).replace('IMPORTS', '\n'.join(imports)) + ''.join(ch for _, _, ch in segs) + ok + grp
            + f'\nset_option maxHeartbeats 4000000 in\ntheorem tan{n}_ok{j} :\n'
            f'    trig{n}Tab.TanOk {nm.tan} {j} {Ks} {Kc} {last["s"]} {last["c"]} := by\n  decide +kernel\n'
            f'\ntheorem tan{n}_g{j} : trig{n}Tab.TanGroup {nm.tan} ({j}, {Ks}, {Kc}) :=\n'
            f'  ⟨_, _, trig{n}_s{j}, trig{n}_c{j}, tan{n}_ok{j}⟩\n' + end)
        rows.append((j, Ks, Kc, dS, dC, trig_c(dS, dC, rbar(j)), tan_c(j, dS, dC, psS, psC)))
        lasts[j] = (last['s'], last['c'])
    files[f'Trig{n}/All.lean'] = (
        ALL_N.replace('IMPORTS', '\n'.join(f'import ExpansionBounds.Trig{n}.G{j}' for j, _, _ in groups))
        .replace('%N', str(n)).replace('CASES', wrap(['rfl'] * len(groups), ' | ', 4))
        .replace('TEXACTS', '\n'.join(f'  · exact tan{n}_g{j}' for j, _, _ in groups))
        .replace('EXACTS', '\n'.join(f'  · exact trig{n}_g{j}' for j, _, _ in groups)))
    files[f'Trig{n}.lean'] = (TOP_N.replace('`Trig%N/Run0.lean` on', '`Trig%N/G0.lean` on').replace('%N', str(n))
                              .replace('%C', str(dec_up(c, 6))).replace('%Q', q)
                              .replace('%T', str(dec_up(ct, 6))).replace('%R', qt))
    return files, rows, controls_n(n, cm, ctm, rows, lasts)


def bounds_n(n):
    """(j, Ks, Kc, dS, dC, C, C^T) for each run of buckets at n, without the Lean text; N must be n"""
    return bounds(*tables_n(n))


def lean_modules(F, groups):
    end = '\nend ExpansionBounds\n'
    data = [DATA]
    for sine, name, what in ((True, 'trig8Fs', "SINR's"), (False, 'trig8Fc', "COSR's")):
        rows = ['  [' + ', '.join(pair(x) for x in row) + ']' for row in F[sine]]
        data.append(f'\n/-- the parts of {what} coefficients -/\ndef {name} : List (List (ℤ × ℕ)) := [\n'
                    + ',\n'.join(rows) + ']\n')
    data.append('\n/-- `(j, K_s, K_c)` for the first bucket `j` of each run of buckets with the same series lengths -/\n'
                'def trig8Groups : List (ℕ × ℕ × ℕ) :=\n  ['
                + wrap([f'({j}, {a}, {b})' for j, a, b in groups], ', ', 3) + ']\n')
    files = {'Trig8/Data.lean': ''.join(data) + end}
    # the modules, balanced by the number of Horner steps
    cost = lambda g: g[1] + g[2] + 4
    order = sorted(groups, key=cost, reverse=True)
    bins = [[] for _ in range(MODS)]
    for g in order:
        min(bins, key=lambda b: sum(cost(x) for x in b)).append(g)
    rows, states = [], {}
    for i, b in enumerate(bins):
        b.sort()
        body = [RUN.replace('FIRST', ', '.join(str(g[0]) for g in b)).replace('STEP', str(STEP))]
        for j, Ks, Kc in b:
            text, last, (dS, dC, psS, psC) = group_text(F, j, Ks, Kc)
            body.append(text)
            rows.append((j, Ks, Kc, dS, dC, trig_c(dS, dC, rbar(j)), tan_c(j, dS, dC, psS, psC)))
            states[j] = (last['s'], last['c'])
        files[f'Trig8/Run{i}.lean'] = ''.join(body) + end
    rows.sort()
    files['Trig8/All.lean'] = (
        ALL.replace('IMPORTS', '\n'.join(f'import ExpansionBounds.Trig8.Run{i}' for i in range(MODS)))
        .replace('CASES', wrap(['rfl'] * len(groups), ' | ', 4))
        .replace('EXACTS', '\n'.join(f'  · exact trig8_g{j}' for j, _, _ in groups)))
    # the tangent: one check a bucket, on the same states
    for i in range(TAN_MODS):
        b = groups[i::TAN_MODS]
        body = [TAN_RUN.replace('FIRST', ', '.join(str(g[0]) for g in b))]
        for j, Ks, Kc in b:
            body.append(f'\nset_option maxHeartbeats 4000000 in\ntheorem tan8_ok{j} : tan8Ok {j} {Ks} {Kc} {states[j][0]} '
                        f'{states[j][1]} := by\n  decide +kernel\n'
                        f'\ntheorem tan8_g{j} : Tan8Group ({j}, {Ks}, {Kc}) :=\n'
                        f'  ⟨_, _, trig8_s{j}, trig8_c{j}, tan8_ok{j}⟩\n')
        files[f'Tan8/Run{i}.lean'] = ''.join(body) + end
    files['Tan8/All.lean'] = (
        ALL.replace('IMPORTS', '\n'.join(f'import ExpansionBounds.Tan8.Run{i}' for i in range(TAN_MODS)))
        .replace('Theorem 35 at `n = 8` and `p = 53`: every bucket', 'Theorem 35 for the tangent at `n = 8` and `p = 53`: every bucket')
        .replace('`Trig8Group`', '`Tan8Group`').replace('trig8_all', 'tan8_all').replace('Trig8Group g', 'Tan8Group g')
        .replace('CASES', wrap(['rfl'] * len(groups), ' | ', 4))
        .replace('EXACTS', '\n'.join(f'  · exact tan8_g{j}' for j, _, _ in groups)))
    files['Trig8/Low.lean'] = low_text(groups, states, False)
    files['Tan8/Low.lean'] = low_text(groups, states, True)
    return files, rows


def bounds(F, groups):
    """(j, Ks, Kc, dS, dC, C) for each run of buckets, without the Lean text"""
    rows = []
    for j, Ks, Kc in groups:
        rb = rbar(j)
        dS, psS = tail(rb, True, Ks, horner_states(rb, True, F[True], Ks)[-1][1])
        dC, psC = tail(rb, False, Kc, horner_states(rb, False, F[False], Kc)[-1][1])
        rows.append((j, Ks, Kc, dS, dC, trig_c(dS, dC, rb), tan_c(j, dS, dC, psS, psC)))
    return rows


if __name__ == '__main__':
    F, groups = tables()
    if len(sys.argv) > 1:
        files, rows = lean_modules(F, groups)
    else:
        rows = bounds(F, groups)
    u8 = U ** N
    for j, Ks, Kc, dS, dC, C, CT in rows:
        print(f'bucket {j:3d}: K_s {Ks:2d}, K_c {Kc:2d}, delta_S {dec_up(dS / u8, 12)} u^8, delta_C {dec_up(dC / u8, 12)} u^8, '
              f'C {dec_up(C / u8, 12)} u^8, C^T ' + ('not on the ladder' if CT is None else f'{dec_up(CT / u8, 12)} u^8'))
    worst = max(r[5] for r in rows)
    tan_ok = all(r[6] is not None for r in rows)
    tan_worst = max(r[6] for r in rows) if tan_ok else None
    M = tc.Paper(N)
    ks, kc = tc.k_table(N, True), tc.k_table(N, False)
    kmax = max(max(ks), max(kc))
    ref = tc.bucket_bounds(M, N, 0, ks, kc, tc.coefs(N, kmax, True), tc.coefs(N, kmax, False))
    ref_c = max(ref['sin'], ref['cos'])
    print(f'the largest: {dec_up(worst / u8, 12)} u^8 <= {float(BOUND):.9f} u^8: {worst <= BOUND * u8}')
    tan_ok = tan_ok and tan_worst <= TAN_BOUND * u8
    print('the tangent, with the computed sine and cosine on H(theta) in every bucket: '
          + (f'{dec_up(tan_worst / u8, 12)} u^8 <= {float(TAN_BOUND):.9f} u^8: {tan_ok}' if tan_worst else 'False'))
    kd = [tc.div_consts(N, P, th)['K'] for th in TAN_TH]
    kd_ok = all(k <= b for k, b in zip(kd, TAN_KD))
    print(f'kappa_DIV at theta = {float(TAN_TH[0])} and {float(TAN_TH[1])}: {dec_up(kd[0], 2)} and {dec_up(kd[1], 2)}, '
          f'within {TAN_KD[0]} and {TAN_KD[1]}: {kd_ok}')
    ref_t = tc.bucket_bounds(M, N, 0, ks, kc, tc.coefs(N, kmax, True), tc.coefs(N, kmax, False))['tan']
    tan_agree = tan_ok and abs(rows[0][6] - ref_t) <= ref_t / 10 ** 9
    print(f'bucket 0 of the tangent agrees with trig_consts.py to 9 digits: {tan_agree}')
    agree = abs(rows[0][5] - ref_c) <= ref_c / 10 ** 50
    print(f'bucket 0 agrees with trig_consts.py to 50 digits: {agree}')
    DROP = True
    ctl = bounds(F, groups[:1])[0][5]
    DROP = False
    print(f'control, no truncation term, falls below trig_consts.py: {ctl < ref_c * (1 - Fr(1, 10 ** 6))}')
    TAN_TH = (Fr(1), Fr(3))
    ctl_t = bounds(F, groups[:1])[0][6]
    TAN_TH = (Fr(14143, 10000), Fr(3))
    print(f'control, the ladder H(1) in the top bucket, must not hold: {ctl_t is None}')
    low_ok = True
    for (j0, c, ct), what in zip(LOW, ('1/2', '2^-5')):
        mc, mt = max(r[5] for r in rows if r[0] >= j0), max(r[6] for r in rows if r[0] >= j0)
        low_ok = low_ok and mc <= c * u8 and mt <= ct * u8
        print(f'|r_0| < {what}: C {dec_up(mc / u8, 9)} u^8 <= {dec_up(c, 6)} u^8 and C^T {dec_up(mt / u8, 9)} u^8 <= '
              f'{dec_up(ct, 6)} u^8: {mc <= c * u8 and mt <= ct * u8}')
    low_ctl = (max(r[5] for r in rows if r[0] >= LOW[0][0]) <= LOW[1][1] * u8
               or max(r[6] for r in rows if r[0] >= LOW[0][0]) <= LOW[1][2] * u8)
    print(f'control, the bounds for |r_0| < 2^-5 hold from |r_0| < 1/2 on: {low_ctl}')
    ok = (worst <= BOUND * u8 and agree and ctl < ref_c * (1 - Fr(1, 10 ** 6)) and tan_ok and kd_ok and tan_agree
          and ctl_t is None and low_ok and not low_ctl)
    # the remark's bounds at other n, each with the control of one unit less in its last digit
    controls = [CONTROLS_N.replace('IMPORTS', '\n'.join(f'import ExpansionBounds.Trig{n}' for n, *_, m in OTHER if m))]
    for n, c, ct, mods in OTHER:
        kd_n = tuple(tc.div_consts(n, P, th)['K'] for th in TAN_TH)
        set_n(n, tuple(Fr(int(k) + 1) for k in kd_n))
        if len(sys.argv) > 1 and mods:
            more, rows_n, ctl_text = lean_modules_n(n, c, ct, mods)
            files.update(more)
            controls.append(ctl_text)
        elif len(sys.argv) > 2 and str(n) in sys.argv[2:] and n in SPLIT:
            more, rows_n, ctl_text = lean_modules_split(n, c, ct, SPLIT[n])
            files.update(more)
            files[f'../Controls/Trig{n}.lean'] = (
                CONTROLS_N.replace('IMPORTS', f'import ExpansionBounds.Trig{n}\nimport Controls.Axioms')
                .replace('the bounds at `n = 2` and `4`', f'the bounds at `n = {n}`')
                .replace('`Trig2.lean` and `Trig4.lean`', f'`Trig{n}.lean`')
                .replace('proves its negation. This file', 'proves its negation. The table is outside the default '
                         'build, so the audit of\n`Controls/Axioms.lean` is repeated here with its modules. This file')
                + ctl_text + '\nend ExpansionBounds\n' + AUDIT_N.replace('_N', f'_{n}').replace('Trig N', f'Trig{n}')
                .replace('n = N', f'n = {n}'))
        else:
            rows_n = bounds_n(n)
        un, c, ct = U ** n, Fr(c, 10 ** 6), Fr(ct, 10 ** 6)
        worst_n = max(r[5] for r in rows_n)
        on_ladder = all(r[6] is not None for r in rows_n)
        tan_n = max(r[6] for r in rows_n) if on_ladder else None
        held = worst_n <= c * un and on_ladder and tan_n <= ct * un
        ctl_n = worst_n <= (c - Fr(1, 10 ** 6)) * un or (on_ladder and tan_n <= (ct - Fr(1, 10 ** 6)) * un)
        print(f'n = {n}: {len(rows_n)} runs of buckets, kappa_DIV within {TAN_KD[0]} and {TAN_KD[1]}, the largest C '
              f'{dec_up(worst_n / un, 9)} u^{n} <= {dec_up(c, 6)} u^{n} and C^T '
              + (f'{dec_up(tan_n / un, 9)} u^{n} <= {dec_up(ct, 6)} u^{n}' if on_ladder else 'not on the ladder')
              + f': {held}; control, either bound one unit less in its last digit: {ctl_n}')
        ok = ok and held and not ctl_n
    set_n(8, (Fr(103232124), Fr(461400803)))
    if len(sys.argv) > 1:
        files['../Controls/TrigN.lean'] = ''.join(controls) + '\nend ExpansionBounds\n'
    if len(sys.argv) > 1 and ok:
        for folder in ['Trig8', 'Tan8', '../Controls'] + [f'Trig{n}' for n, *_ in OTHER]:
            os.makedirs(os.path.join(sys.argv[1], folder), exist_ok=True)
        for name, text in files.items():
            path = os.path.join(sys.argv[1], name)
            if os.path.exists(path) and open(path, encoding='utf-8').read() == text:
                continue  # an unchanged module keeps its build
            with open(path, 'w', encoding='utf-8') as f:
                f.write(text)
            print('wrote', path)
    sys.exit(0 if ok else 1)
