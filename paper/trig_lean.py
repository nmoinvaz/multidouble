"""Theorem 35 at n = 8 for Lean: the bounds of Lemma 34 by bucket, in exact rationals rounded up to 200 bits, written
from the Lean definitions (Eval.lean, SqrtEval.lean, TrigEval.lean of lean/ExpansionBounds), and the modules that hold
them: Trig8/Data.lean (the coefficients of the series and their lengths by bucket, multidouble's tables),
Trig8/Run0.lean to Run7.lean (Horner's run of every bucket with its own series lengths, in pieces of a few steps
checked by the kernel against the states stored there) and Trig8/All.lean (the buckets together).

The states must be the ones the Lean definitions compute, bit for bit, or the modules do not build. The bound of a
bucket is compared with trig_consts.py, which rounds at other places and agrees to more than 50 digits.

usage: trig_lean.py [lean/ExpansionBounds]
       prints the bound of each run of buckets and the largest; with an argument it writes the Lean modules there.
       The control drops the truncation term and must fall below trig_consts.py."""
import os
import sys
from fractions import Fraction as Fr

import trig_consts as tc

P, N, BITS, STEP, MODS = 53, 8, 200, 2, 8  # STEP Horner steps to a kernel check, MODS modules
U = Fr(1, 2 ** P)
US = U / (1 + U)
BOUND = Fr(3163167393, 10 ** 9)
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


def g_addf_err(al, b0, Zb):
    return g_err(addf_x(al, al[0] + b0), Zb, Fr(0))


AB = [(2 * U) ** i * ((1 - 2 * U) / (1 - 4 * U)) for i in range(N)]
_ez, _zeta = g_mul(AB, AB, Fr(1))
EZ = up(_ez)
ZETA = [up(x) for x in _zeta]


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
    """Lean's sinDeltaL or cosDeltaL"""
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
        ey, _ = g_add(AB, [zb * x for x in om], 1 + D)
        return U ** N + (D + ey - U ** N) / (1 - zb / 6)
    D = up(zb * Et + (0 if DROP else rb ** (2 * K) / tc.fact(2 * K)))
    ey = g_addf_err([zb * x for x in th], Fr(1), 1 + D)
    return U ** N + (D + ey - U ** N) / tc.cos_lo(rb)


def trig_c(dS, dC, rb):
    eps = 1 + 2 * U ** N
    return eps * max(dS + eps * U ** N, dC + eps * U ** N * (rb * tc.tan_hi(rb)))


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


def group_text(F, j, Ks, Kc):
    """the states, the kernel's checks and `Trig8Group` for bucket j"""
    rb = rbar(j)
    o, last = [], {}
    for sine, K, tag, C, Fq in ((True, Ks, 's', 'sinCQ', 'trig8FsQ'), (False, Kc, 'c', 'cosCQ', 'trig8FcQ')):
        sts = horner_states(rb, sine, F[sine], K)
        d = K - 1
        for a, st in sts[1:]:
            o.append(f'\ndef trig8_{tag}{j}_{a} : (ℤ × ℕ) × List (ℤ × ℕ) :=\n  ({pair(st[0])},\n    ['
                     + wrap([pair(x) for x in st[1]], ', ', 5) + '])\n')
        names = []
        for (a, _), (b, _) in zip(sts, sts[1:]):
            start = f'(trig8Init {C} {Fq} {d})' if a == 0 else f'(dySt trig8_{tag}{j}_{a})'
            names.append((f'trig8_{tag}{j}_{a}_{b}', b - a))
            o.append(f'\nset_option maxHeartbeats 4000000 in\ntheorem trig8_{tag}{j}_{a}_{b} :\n'
                     f'    trig8Run {C} {Fq} {j} {d} {a} {b - a} {start} = dySt trig8_{tag}{j}_{b} := by\n'
                     '  decide +kernel\n')
        if K == 2:
            last[tag] = f'(trig8Init {C} {Fq} {d})'
            o.append(f'\ntheorem trig8_{tag}{j} : trig8Run {C} {Fq} {j} {d} 0 0 (trig8Init {C} {Fq} {d}) =\n'
                     f'    trig8Init {C} {Fq} {d} := rfl\n')
        else:
            last[tag] = f'(dySt trig8_{tag}{j}_{K - 2})'
            term = names[-1][0]
            rest = names[-1][1]
            for nm, m in reversed(names[:-1]):
                term = f'trig8Run_cut {C} {Fq} {j} {d} _ {m} {rest} {nm}\n    ({term})'
                rest += m
            o.append(f'\ntheorem trig8_{tag}{j} : trig8Run {C} {Fq} {j} {d} 0 {K - 2} (trig8Init {C} {Fq} {d}) =\n'
                     f'    dySt trig8_{tag}{j}_{K - 2} :=\n  {term}\n')
        last[tag + 'v'] = tail(rb, sine, K, sts[-1][1])
    o.append(f'\nset_option maxHeartbeats 4000000 in\ntheorem trig8_ok{j} : trig8Ok {j} {Ks} {Kc} {last["s"]} {last["c"]} := by\n'
             '  decide +kernel\n')
    o.append(f'\ntheorem trig8_g{j} : Trig8Group ({j}, {Ks}, {Kc}) :=\n  ⟨_, _, trig8_s{j}, trig8_c{j}, trig8_ok{j}⟩\n')
    return ''.join(o), last['sv'], last['cv']


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
    rows = []
    for i, b in enumerate(bins):
        b.sort()
        body = [RUN.replace('FIRST', ', '.join(str(g[0]) for g in b)).replace('STEP', str(STEP))]
        for j, Ks, Kc in b:
            text, dS, dC = group_text(F, j, Ks, Kc)
            body.append(text)
            rows.append((j, Ks, Kc, dS, dC, trig_c(dS, dC, rbar(j))))
        files[f'Trig8/Run{i}.lean'] = ''.join(body) + end
    rows.sort()
    files['Trig8/All.lean'] = (
        ALL.replace('IMPORTS', '\n'.join(f'import ExpansionBounds.Trig8.Run{i}' for i in range(MODS)))
        .replace('CASES', wrap(['rfl'] * len(groups), ' | ', 4))
        .replace('EXACTS', '\n'.join(f'  · exact trig8_g{j}' for j, _, _ in groups)))
    return files, rows


def bounds(F, groups):
    """(j, Ks, Kc, dS, dC, C) for each run of buckets, without the Lean text"""
    rows = []
    for j, Ks, Kc in groups:
        rb = rbar(j)
        dS = tail(rb, True, Ks, horner_states(rb, True, F[True], Ks)[-1][1])
        dC = tail(rb, False, Kc, horner_states(rb, False, F[False], Kc)[-1][1])
        rows.append((j, Ks, Kc, dS, dC, trig_c(dS, dC, rb)))
    return rows


if __name__ == '__main__':
    F, groups = tables()
    if len(sys.argv) > 1:
        files, rows = lean_modules(F, groups)
    else:
        rows = bounds(F, groups)
    u8 = U ** N
    for j, Ks, Kc, dS, dC, C in rows:
        print(f'bucket {j:3d}: K_s {Ks:2d}, K_c {Kc:2d}, delta_S {float(dS / u8):.12f} u^8, delta_C {float(dC / u8):.12f} u^8, '
              f'C {float(C / u8):.12f} u^8')
    worst = max(r[5] for r in rows)
    M = tc.Paper(N)
    ks, kc = tc.k_table(N, True), tc.k_table(N, False)
    kmax = max(max(ks), max(kc))
    ref = tc.bucket_bounds(M, N, 0, ks, kc, tc.coefs(N, kmax, True), tc.coefs(N, kmax, False))
    ref_c = max(ref['sin'], ref['cos'])
    print(f'the largest: {float(worst / u8):.12f} u^8 <= {float(BOUND):.9f} u^8: {worst <= BOUND * u8}')
    agree = abs(rows[0][5] - ref_c) <= ref_c / 10 ** 50
    print(f'bucket 0 agrees with trig_consts.py to 50 digits: {agree}')
    DROP = True
    ctl = bounds(F, groups[:1])[0][5]
    DROP = False
    print(f'control, no truncation term, falls below trig_consts.py: {ctl < ref_c * (1 - Fr(1, 10 ** 6))}')
    ok = worst <= BOUND * u8 and agree and ctl < ref_c * (1 - Fr(1, 10 ** 6))
    if len(sys.argv) > 1 and ok:
        os.makedirs(os.path.join(sys.argv[1], 'Trig8'), exist_ok=True)
        for name, text in files.items():
            with open(os.path.join(sys.argv[1], name), 'w') as f:
                f.write(text)
            print('wrote', os.path.join(sys.argv[1], name))
    sys.exit(0 if ok else 1)
