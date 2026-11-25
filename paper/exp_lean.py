"""Theorem 40's bound of the octo-double exponential, as the Lean definitions of ExpEval.lean compute it.

The cases are those of explog_consts.py: k = 0 or not, a group of exponents e of step (2) with the same m and degree
d', a sign of r and an interval [a, b] of |r|. Horner's run and step (3)'s products and sum are evaluated once for a
group and a sign, at the group's largest b, whose bounds are above those of each of its intervals; the squarings and
the last ADDF are evaluated for each interval. Every value is an exact rational, rounded up to 200 bits where
ExpEval.lean rounds (upQ 200), so that the kernel can check each step against the stored states.

usage: exp_lean.py             prints the bounds (exp_lean.txt)
       exp_lean.py <dir>       also writes the Lean modules of <dir>/Exp8/
"""
import sys, os, math
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'scripts'))
import explog_constants as EC  # noqa: E402
import trig_lean as TL  # noqa: E402
from rounding import dec_down, dec_up  # noqa: E402

N, U = TL.N, TL.U
up, g_mul, g_add, g_err, addf_x, pair_x, g_parts = TL.up, TL.g_mul, TL.g_add, TL.g_err, TL.addf_x, TL.pair_x, TL.g_parts
S, DEG = 6, 43                       # the squaring threshold 2^-s and the largest degree
B = 53 * N + 12
ETA0 = Fr(1, 2 ** 1075)
XMAX = Fr(7452, 10)
BOUND = Fr(3661, 1000)
SUB = 8                              # intervals of |r| in a group where |r| exceeds 2^-12
fact = math.factorial

# -- Lemma 38 at n = 8, as ExpRed8.lean
CONST = EC.constants()
_lo, _hi = CONST['ln2']
LN2A = Fr((_lo.numerator << 600) // _lo.denominator - 1, 1 << 600)
LN2B = Fr(-((-_hi.numerator << 600) // _hi.denominator) + 1, 1 << 600)
CH = Fr(CONST['hi'])
CL = [Fr(x) for x in CONST['lo'][:N]]
CR = Fr(1.4426950408889634)
RED_XT = 2 * U / (1 - 2 * U) * XMAX
RED_DL = max(abs(CR - 1 / LN2B), abs(CR - 1 / LN2A))
RED_EPSK = XMAX * (RED_DL + U * CR)
RED_RMAX = (Fr(1, 2) + RED_EPSK) * LN2B + RED_XT
RED_A0 = RED_RMAX + RED_XT + 1075 * max(abs(CH - LN2A), abs(CH - LN2B))
RED_ETA = max(abs(CH + sum(CL) - LN2A), abs(CH + sum(CL) - LN2B))
_X, _R = pair_x([abs(c) * 1075 for c in CL])
RED_E1 = g_err(_X, 1075 * abs(sum(CL)), _R)
RED_MU = g_parts(_X, 1075 * abs(sum(CL)), _R)
RED_ALPHA = [RED_A0] + [(2 * U) ** i * XMAX for i in range(1, N)]


def red_delta_pi(rb):
    """Lean's (red8Delta rb, red8Pi rb)"""
    e2, pr = g_add(RED_ALPHA, RED_MU, rb + 1075 * RED_ETA + RED_E1)
    return RED_E1 + e2 + 1075 * RED_ETA, pr


RED_DELTA = red_delta_pi(RED_RMAX)[0]

# -- the coefficients F_j of 1/j!
FK = [[Fr(x) for x in EC.greedy(Fr(1, fact(j)), N)] for j in range(DEG + 1)]
# the crate's eight-part constants begin with these
assert all(FK[j] == [Fr(x) for x in CONST['fact'][j][:N]] for j in range(min(DEG, EC.JMAX) + 1)), 'F_j differ'
PHI = [abs(sum(FK[j]) - Fr(1, fact(j))) for j in range(DEG + 1)]


# -- the mirrors of ExpEval.lean
def core_v(bp, k):
    return Fr(1, fact(k)) / (1 - bp / (k + 1))


def etr(bp, d):
    return bp ** (d + 1) / (fact(d + 1) * (1 - bp / (d + 2)))


def exp_sum(z):
    return sum(z ** i / fact(i) for i in range(16))


def exp_rem(z):
    return abs(z) ** 16 / (fact(16) * (1 - abs(z) / 17))


def exp_up(z):
    return exp_sum(z) + exp_rem(z)


def exp_lo(z):
    return exp_sum(z) - exp_rem(z)


def horner_step(pq, bp, k, st):
    """hornerStepL with pi^z = pq, zb = bp, eps_z = eta = 0 and v = coreVQ bp"""
    e1, p1 = st
    Zm = bp * (core_v(bp, k + 1) + e1)
    em, mu = g_mul(pq, p1, Zm)
    D = bp * e1 + PHI[k] + em
    ea, pa = g_add([abs(x) for x in FK[k]], mu, core_v(bp, k) + D)
    return up(D + ea), [up(x) for x in pa]


def horner_states(pq, bp, d):
    """the states of Horner's run after 0, 1, ..., d - 2 steps"""
    st = (PHI[d], [abs(x) for x in FK[d]])
    out = [st]
    for j in range(d - 2):
        st = horner_step(pq, bp, d - (j + 1), st)
        out.append(st)
    return out


def exp_w(pq, bp, st):
    Zw = bp * (core_v(bp, 2) + st[0])
    e1, w1 = g_mul(pq, st[1], Zw)
    return ((up(Zw + e1), up(e1 + bp * st[0])), [up(x) for x in w1])


def exp_y(pq, bp, D, d, st):
    e2, w = g_mul(pq, st[1], bp * st[0][0])
    return (up(e2 + bp * st[0][1] + etr(bp, d) + D), [up(x) for x in w])


def exp_t(pq, T0, eta, st):
    e3, pa = g_add(pq, st[1], T0 + st[0])
    return (up(st[0] + e3 + N * eta), [up(x + eta) for x in pa])


def exp_sq(T, T2, g, st):
    E, ps = st
    em, nu = g_mul(ps, ps, (T + E) ** 2)
    ea, pa = g_add([2 * x for x in ps], nu, T2 + 2 * E * (1 + T) + E ** 2 + em)
    return (up(2 * g * E + E ** 2 + em + ea), [up(x) for x in pa])


DROP = False  # the control: no error of the last ADDF


def exp_eps(Zexp, v, dexp, st):
    E, ps = st
    es = Fr(0) if DROP else g_err(addf_x(ps, Zexp + E + sum(ps[1:])), Zexp + E, 0)
    return (E + es) / v + dexp


def core_t(pos, bp, j):
    return up(exp_up(2 ** j * bp) - 1) if pos else up(1 - exp_lo(-(2 ** j * bp)))


def core_g(pos, ap, bp, j):
    return up(exp_up(2 ** j * bp)) if pos else up(exp_up(-(2 ** j * ap)))


# -- the cases
def down(q):
    return -up(-q) if q else q


DELTA_S = up(RED_DELTA)                                   # delta*, of Lemma 38 at r_max
RMAX_S = up(RED_RMAX)
AB = TL.AB                                                # the part bounds of an expansion on H(2), in units of |r|
TOP = {True: up(1 / (2 * CR * (1 - 2 * U))), False: up(RMAX_S + DELTA_S)}
TAILS = {True: up(sum(AB[i] * TOP[True] for i in range(1, N))), False: up(sum(red_delta_pi(RED_RMAX)[1][1:]))}
DELTA = {True: Fr(0), False: DELTA_S}
UB = Fr(1, 2 ** 46)
STEP, MODS = 2, 12


def degree(e):
    return 1 if e < -1 - B else min(DEG, -(-B // (-e - 1)))


def group_pi(k0, hi):
    return [AB[i] * hi for i in range(N)] if k0 else red_delta_pi(hi + DELTA_S)[1]


def groups(k0):
    """(m, d, e_lo, e_hi, lo, hi): the exponents e_lo..e_hi share m and the degree d and select |r| in [lo, hi]; the
    last group, of degree 1, is every e up to its e_hi"""
    top, tail, out = TOP[k0], TAILS[k0], []
    lo_of = lambda e: down(max(Fr(0), Fr(2) ** e * (1 - UB) - 2 * tail))
    e = -2
    assert Fr(2) ** (e + 1) * (1 - UB) - 2 * tail > top, 'an exponent above -2 can be selected'
    while True:
        m = max(0, e + S + 1)
        d, e_lo = degree(e - m), e
        while m == 0 and e_lo - 1 >= -1 - B and degree(e_lo - 1) == d:
            e_lo -= 1
        if d == 1:
            out.append((0, 1, e, e, Fr(0), min(top, Fr(2) ** (e + 1))))
            return out
        out.append((m, d, e_lo, e, lo_of(e_lo), min(top, Fr(2) ** (e + 1))))
        e = e_lo - 1


def edges(lo, hi):
    """a partition of [lo, hi]: geometric, SUB pieces where hi > 2^-12, one piece below"""
    if hi <= Fr(1, 2 ** 12):
        return [(lo, hi)]
    lo_e = lo if lo > 0 else hi / 2 ** 16
    e = [lo_e] + [Fr(round(float(lo_e) * float(hi / lo_e) ** (i / SUB) * 2 ** 60), 2 ** 60) for i in range(1, SUB)]
    e += [hi]
    if lo == 0:
        e = [Fr(0)] + e
    return list(zip(e, e[1:]))


def group_case(k0, g):
    """the data of a group: its (pq, bp), Horner's states, the states of step (3) and (E_0, psi_0) for each sign, and
    for each interval (a, b, bpB, states by sign, eps by sign)"""
    m, d, e_lo, e_hi, lo, hi = g
    cap, sc = Fr(2) ** (e_hi + 1), Fr(1, 2 ** m)
    eta1 = ETA0 if m else Fr(0)
    pq = [up(sc * min(x, cap) + eta1) for x in group_pi(k0, hi)]
    bp = up(sc * min(hi, cap) + N * eta1)
    c = dict(k0=k0, g=g, pq=pq, bp=bp)
    if d == 1:
        c['hs'], c['st0'] = [], {s: (etr(bp, 1) + 2 * N * eta1, pq) for s in (True, False)}
    else:
        c['hs'] = horner_states(pq, bp, d)
        c['sw'] = exp_w(pq, bp, c['hs'][-1])
        c['sy'] = exp_y(pq, bp, 2 * N * eta1, d, c['sw'])
        c['st0'] = {s: exp_t(pq, core_t(s, bp, 0), ETA0, c['sy']) for s in (True, False)}
    c['bins'] = []
    for a, b in edges(lo, hi):
        bpb = up(sc * min(b, cap) + N * eta1)
        sts, eps = {}, {}
        for s in (True, False):
            st, l = c['st0'][s], []
            for j in range(m):
                st = exp_sq(core_t(s, bpb, j), core_t(s, bpb, j + 1), core_g(s, sc * a, bpb, j), st)
                l.append(st)
            Zexp = up(exp_up(b)) if s else up(exp_up(-a))
            v = exp_lo(a - DELTA[k0]) if s else exp_lo(-b - DELTA[k0])
            sts[s], eps[s] = l, exp_eps(Zexp, v, exp_up(DELTA[k0]) - 1, st)
        c['bins'].append((a, b, bpb, sts, eps))
    return c


def cases():
    return [group_case(k0, g) for k0 in (True, False) for g in groups(k0)]


# -- the Lean modules
pair, wrap = TL.pair, TL.wrap


def dy(q):
    return f'dyQ {pair(q)}'


def st_text(st, ind):
    return f'({pair(st[0])},\n{" " * ind}[' + wrap([pair(x) for x in st[1]], ', ', ind + 1) + '])'


def grp_text(g):
    m, d, e_lo, e_hi, lo, hi = g
    return f'({m}, {d}, {e_lo}, {e_hi}, {pair(lo)}, {pair(hi)})'


DATA = '''import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation

/-!
# Theorem 40 at `n = 8` and `p = 53`: multidouble's table and the cases

The eight parts of the coefficients `F_k` of `1/k!`, each the greedy rounding to eight binary64 numbers, as dyadic
pairs `(m, k)` for `m / 2 ^ k`; upper bounds of Lemma 38's `r̄_max` and `δ*` at `n = 8`, of `|r|` and of
`∑_{i ≥ 1} |r_i|` for `k = 0` and for `k ≠ 0`; and the groups of exponents `e` of step (2) for each, as
`(m, d', e_lo, e_hi, lo, hi)`: the exponents `e_lo ≤ e ≤ e_hi` share `m` and the degree `d'` and select `|r|` in
`[lo, hi]`, and the last group, of degree 1, is every `e` up to its `e_hi`. This file is written by `exp_lean.py`.
-/

namespace ExpansionBounds
'''

RUN = '''import ExpansionBounds.Exp8.Defs

/-!
# Theorem 40 at `n = 8` and `p = 53`: the groups FIRST

For each group the kernel checks Horner's run in pieces of at most STEP steps, from the state before a piece to the
state after it, step (3)'s two products and sum, and for each interval of `|r|` and each sign the squarings and the
bound `3.661u^8`. `z` names a group of `k = 0` and `n` one of `k ≠ 0`. This file is written by `exp_lean.py`.
-/

namespace ExpansionBounds
'''

ALL = '''IMPORTS

/-!
# Theorem 40 at `n = 8` and `p = 53`: every group

`Exp8Group` holds for each group of exponents, for `k = 0` and for `k ≠ 0`. This file is written by `exp_lean.py`.
-/

namespace ExpansionBounds
BODY
end ExpansionBounds
'''

DEC = 'set_option maxHeartbeats 4000000 in\n'


def group_text(c, tag):
    """the definitions and the kernel's checks of a group"""
    k0, g = c['k0'], c['g']
    m, d, e_lo, e_hi, lo, hi = g
    K = 'true' if k0 else 'false'
    o = [f'\ndef {tag}_pq : List ℚ :=\n  [' + wrap([dy(x) for x in c['pq']], ', ', 3) + ']\n',
         f'\ndef {tag}_bp : ℚ := {dy(c["bp"])}\n',
         f'\n{DEC}theorem {tag}_par : Exp8Par {K} {m} ({e_hi}) ({dy(hi)}) {tag}_pq {tag}_bp := by\n  decide +kernel\n']
    run = f'exp8Run {tag}_pq {tag}_bp {d}'
    pqf = f'(fun i => {tag}_pq.getD i 0)'
    if d == 1:
        st0 = {s: f'(eTrQ {tag}_bp 1 + 2 * ((8 : ℕ) : ℚ) * exp8Eta1 {m}, {tag}_pq)' for s in (True, False)}
        for s, sg in ((True, 'p'), (False, 'm')):
            o.append(f'\ntheorem {tag}_h{sg} : Exp8Head {"true" if s else "false"} {m} {d} {tag}_pq {tag}_bp\n'
                     f'    {st0[s]} :=\n  exp8Head_one _ _ _ _\n')
    else:
        hs = c['hs']
        cuts = [j for j in range(len(hs)) if j % STEP == 0 or j == len(hs) - 1]
        for j in cuts[1:]:
            o.append(f'\ndef {tag}_s{j} : (ℤ × ℕ) × List (ℤ × ℕ) :=\n  {st_text(hs[j], 4)}\n')
        names = []
        for a, b in zip(cuts, cuts[1:]):
            start = f'(hornerInitL 8 exp8F exp8Phi {d})' if a == 0 else f'(dySt {tag}_s{a})'
            names.append((f'{tag}_r{a}_{b}', b - a))
            o.append(f'\n{DEC}theorem {tag}_r{a}_{b} :\n    {run} {a} {b - a} {start} = dySt {tag}_s{b} := by\n'
                     '  decide +kernel\n')
        last = len(hs) - 1
        if last == 0:
            fin = f'(hornerInitL 8 exp8F exp8Phi {d})'
            o.append(f'\ntheorem {tag}_r : {run} 0 {d - 2} (hornerInitL 8 exp8F exp8Phi {d}) =\n    {fin} := rfl\n')
        else:
            fin = f'(dySt {tag}_s{last})'
            term, rest = names[-1]
            for nm, k in reversed(names[:-1]):
                term = f'exp8Run_cut {tag}_pq {tag}_bp {d} _ {k} {rest} {nm}\n    ({term})'
                rest += k
            o.append(f'\ntheorem {tag}_r : {run} 0 {d - 2} (hornerInitL 8 exp8F exp8Phi {d}) =\n    {fin} :=\n  {term}\n')
        sw, sy = c['sw'], c['sy']
        o.append(f'\ndef {tag}_w : ((ℤ × ℕ) × (ℤ × ℕ)) × List (ℤ × ℕ) :=\n  (({pair(sw[0][0])},\n     {pair(sw[0][1])}),\n    ['
                 + wrap([pair(x) for x in sw[1]], ', ', 5) + '])\n')
        o.append(f'\n{DEC}theorem {tag}_wt : expWL red8U 8 (upQ 200) {pqf} {tag}_bp {fin} =\n'
                 f'    dyStW {tag}_w := by\n  decide +kernel\n')
        o.append(f'\ndef {tag}_y : (ℤ × ℕ) × List (ℤ × ℕ) :=\n  {st_text(sy, 4)}\n')
        o.append(f'\n{DEC}theorem {tag}_yt : expYL red8U 8 (upQ 200) {pqf} {tag}_bp\n'
                 f'    (2 * ((8 : ℕ) : ℚ) * exp8Eta1 {m}) {d} (dyStW {tag}_w) = dySt {tag}_y := by\n  decide +kernel\n')
        st0 = {}
        for s, sg in ((True, 'p'), (False, 'm')):
            B_ = 'true' if s else 'false'
            o.append(f'\ndef {tag}_t{sg} : (ℤ × ℕ) × List (ℤ × ℕ) :=\n  {st_text(c["st0"][s], 4)}\n')
            o.append(f'\n{DEC}theorem {tag}_t{sg}t : expTL red8U 8 (upQ 200) {pqf} (coreTQ (upQ 200) {B_} {tag}_bp 0)\n'
                     f'    exp8Eta (dySt {tag}_y) = dySt {tag}_t{sg} := by\n  decide +kernel\n')
            st0[s] = f'(dySt {tag}_t{sg})'
            o.append(f'\ntheorem {tag}_h{sg} : Exp8Head {B_} {m} {d} {tag}_pq {tag}_bp {st0[s]} :=\n'
                     f'  exp8Head_of_ne (by decide) (exp8HeadH_mk {tag}_r {tag}_wt {tag}_yt {tag}_t{sg}t)\n')
    D = f'(exp8Delta {K})'
    for i, (a, b, bpb, sts, eps) in enumerate(c['bins']):
        ls = {s: '[' + (',\n     '.join('dySt ' + st_text(x, 7) for x in sts[s])) + ']' for s in (True, False)}
        o.append(f'\ndef {tag}_b{i} : (ℚ × ℚ) × ℚ × List (ℚ × List ℚ) × List (ℚ × List ℚ) :=\n'
                 f'  (({dy(a)}, {dy(b)}), {dy(bpb)},\n    {ls[True]},\n    {ls[False]})\n')
        for s, sg, prj in ((True, 'p', '2.2.1'), (False, 'm', '2.2.2')):
            o.append(f'\n{DEC}theorem {tag}_b{i}{sg} : Exp8Bin {"true" if s else "false"} {m} ({e_hi}) {D} {tag}_b{i}.1.1 '
                     f'{tag}_b{i}.1.2\n    {tag}_b{i}.2.1 {tag}_bp {st0[s]} {tag}_b{i}.{prj} := by\n  decide +kernel\n')
    nb = len(c['bins'])
    o.append(f'\ntheorem {tag} : Exp8Group {K} {grp_text(g)} :=\n'
             f'  ⟨{tag}_pq, {tag}_bp, {st0[True]}, {st0[False]},\n    ['
             + wrap([f'{tag}_b{i}' for i in range(nb)], ', ', 5) + f'],\n    {tag}_par, {tag}_hp, {tag}_hm, List.cons_ne_nil _ _, by decide +kernel, by\n'
             '    intro bn hb\n    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb\n'
             '    rcases hb with ' + wrap(['rfl'] * nb, ' | ', 6) + '\n'
             + '\n'.join(f'    · exact ⟨{tag}_b{i}p, {tag}_b{i}m⟩' for i in range(nb)) + '⟩\n')
    return ''.join(o)


def lean_modules(cs):
    end = '\nend ExpansionBounds\n'
    data = [DATA]
    rows = ['  [' + ', '.join(pair(x) for x in row) + ']' for row in FK]
    data.append('\n/-- the parts of the coefficients `F_k` -/\ndef exp8Fact : List (List (ℤ × ℕ)) := [\n'
                + ',\n'.join(rows) + ']\n')
    for name, what, v in (('exp8RMaxS', 'an upper bound of `r̄_max`', RMAX_S), ('exp8DeltaS', 'an upper bound of `δ*`', DELTA_S),
                          ('exp8Top0', 'an upper bound of `|r|` for `k = 0`', TOP[True]),
                          ('exp8Top1', 'an upper bound of `|r|` for `k ≠ 0`', TOP[False]),
                          ('exp8Tail0', 'an upper bound of `∑_{i ≥ 1} |r_i|` for `k = 0`', TAILS[True]),
                          ('exp8Tail1', 'an upper bound of `∑_{i ≥ 1} |r_i|` for `k ≠ 0`', TAILS[False])):
        data.append(f'\n/-- {what} -/\ndef {name} : ℤ × ℕ :=\n  {pair(v)}\n')
    names = {}
    for k0, nm in ((True, '0'), (False, '1')):
        gs = [c['g'] for c in cs if c['k0'] == k0]
        data.append(f'\n/-- the groups for `k {"=" if k0 else "≠"} 0`, but the last -/\n'
                    f'def exp8Grp{nm} : List (ℕ × ℕ × ℤ × ℤ × (ℤ × ℕ) × (ℤ × ℕ)) := [\n  '
                    + ',\n  '.join(grp_text(g) for g in gs[:-1]) + ']\n')
        data.append(f'\n/-- the last group for `k {"=" if k0 else "≠"} 0`: degree 1, every `e` up to its `e_hi` -/\n'
                    f'def exp8Last{nm} : ℕ × ℕ × ℤ × ℤ × (ℤ × ℕ) × (ℤ × ℕ) :=\n  {grp_text(gs[-1])}\n')
    files = {'Exp8/Data.lean': ''.join(data) + end}
    # the modules, balanced by the number of kernel checks
    tags = {}
    for k0 in (True, False):
        for i, c in enumerate([c for c in cs if c['k0'] == k0]):
            tags[id(c)] = f'exp8_{"z" if k0 else "n"}{i}'
    cost = lambda c: max(0, c['g'][1] - 2) + 3 + 2 * len(c['bins']) * (1 + c['g'][0])
    mods = [[] for _ in range(MODS)]
    for c in sorted(cs, key=cost, reverse=True):
        min(mods, key=lambda b: sum(cost(x) for x in b)).append(c)
    for i, b in enumerate(mods):
        b.sort(key=lambda c: (not c['k0'], int(tags[id(c)][6:])))
        body = [RUN.replace('FIRST', ', '.join(tags[id(c)][5:] for c in b)).replace('STEP', str(STEP))]
        body += [group_text(c, tags[id(c)]) for c in b]
        files[f'Exp8/Run{i}.lean'] = ''.join(body) + end
    body = []
    for k0, nm in ((True, '0'), (False, '1')):
        gs = [c for c in cs if c['k0'] == k0]
        K = 'true' if k0 else 'false'
        body.append(f'\ntheorem exp8_all{nm} : ∀ g ∈ exp8Grp{nm}, Exp8Group {K} g := by\n  intro g hg\n'
                    f'  simp only [exp8Grp{nm}, List.mem_cons, List.not_mem_nil, or_false] at hg\n  rcases hg with '
                    + wrap(['rfl'] * (len(gs) - 1), ' | ', 4) + '\n'
                    + '\n'.join(f'  · exact {tags[id(c)]}' for c in gs[:-1]) + '\n'
                    f'\ntheorem exp8_last{nm} : Exp8Group {K} exp8Last{nm} :=\n  {tags[id(gs[-1])]}\n')
    files['Exp8/All.lean'] = (ALL.replace('IMPORTS', '\n'.join(f'import ExpansionBounds.Exp8.Run{i}' for i in range(MODS)))
                              .replace('BODY', ''.join(body)))
    return files


if __name__ == '__main__':
    cs = cases()
    u8 = U ** N
    worst = max((eps[s], c['k0'], c['g'][:4], s, a, b) for c in cs for a, b, _, _, eps in c['bins']
                for s in (True, False))
    nb = 2 * sum(len(c['bins']) for c in cs)
    print(f'{len(cs)} groups, {nb} cases, {sum(max(0, c["g"][1] - 2) for c in cs)} steps of Horner\'s rule')
    print(f'the largest: {dec_up(worst[0] / u8, 9)} u^8 at k {"=" if worst[1] else "!="} 0, (m, d, e_lo, e_hi) = {worst[2]}, '
          f'r {">" if worst[3] else "<"} 0, |r| in [{dec_down(worst[4], 6)}, {dec_up(worst[5], 6)}]')
    ok = worst[0] <= BOUND * u8
    print(f'within {float(BOUND)} u^8: {ok}')
    tight = worst[0] > (BOUND - Fr(1, 1000)) * u8
    print(f'control, {float(BOUND - Fr(1, 1000))} u^8 must not hold: {tight}')
    sys.path.insert(0, HERE)
    import explog_consts as XC  # noqa: E402
    ref = XC.od_exp(N, S, DEG)[0]
    agree = abs(worst[0] - ref) <= ref / 10 ** 7
    print(f'agrees with explog_consts.py ({dec_up(ref / u8, 9)} u^8) to 7 digits: {agree}')
    wc = max(cs, key=lambda c: max(max(eps.values()) for _, _, _, _, eps in c['bins']))
    DROP = True
    ctl = max(max(eps.values()) for _, _, _, _, eps in group_case(wc['k0'], wc['g'])['bins'])
    DROP = False
    caught = ctl < ref * (1 - Fr(1, 10 ** 6))
    print(f'control, no error of the last ADDF, falls below explog_consts.py: {caught}')
    ok = ok and tight and agree and caught
    if len(sys.argv) > 1 and ok:
        os.makedirs(os.path.join(sys.argv[1], 'Exp8'), exist_ok=True)
        for name, text in lean_modules(cs).items():
            path = os.path.join(sys.argv[1], name)
            if os.path.exists(path) and open(path, encoding='utf-8').read() == text:
                continue  # an unchanged module keeps its build
            with open(path, 'w', encoding='utf-8') as f:
                f.write(text)
            print('wrote', path)
    sys.exit(0 if ok else 1)
