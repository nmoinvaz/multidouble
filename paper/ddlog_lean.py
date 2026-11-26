"""Proposition 44's bound of the double-double logarithm, as the Lean definitions of DDLogEval.lean compute it.

The cases are those of explog_consts.py for double words (dd_log, log_bound), in its convex mode: k = 0 or not, a
group of exponents e of step (2) with one degree d' (m = 0 in every group), a sign of r and, for k != 0, an interval
[a, b] of |r|. For a case the bound E(l) is convex in l = |ln x| (DDLogCvx.lean), so on an interval [l1, l2] with
l1 > 0 its ratio to l is largest at an end, and on [0, l2] it lies below the chord E(0) + l (E(l2) - E(0))/l2: the
report gives the largest ratio and the largest such slope apart, each at most the proposition's 15.351u^2, with E(0)
at most 2^-1071. Every value is an exact rational, with e^z from the upper end of the 16-term enclosure of
ExpEval.lean, and every printed bound is rounded up.

Where this departs from explog_consts.py, each time to a bound that is still valid:
  - k != 0: the ends of l are the least l with k != 0 and 745.2 only; the script also evaluates l = 1 and l = 4, which
    convexity makes unnecessary and which can only raise the largest ratio;
  - k != 0: the reduction of (-y0, 0) is evaluated with X = ybar(745.2) and a zero low part, where the script takes
    X = ybar / (1 - u) and a tail 2 u ybar, and with delta* at l = 745.2 for every l, as delta* grows with l;
  - k = 0: a is the least |r| that selects the group, 2^e (1 - 2^-46), where the script takes it times
    (1 - u) / (1 + u); the Lean proof has the first (prop44_exp's lower end);
  - the bound of |y0| for k = 0 is 1 / (2 c_r), without the script's factor (1 + 3u) / (1 - u), as y0 is one float;
  - the ends of an interval of l are rounded outward to 64-bit dyadic numbers.

usage: ddlog_lean.py             prints the count of cases and ends, the largest ratio and E(0)
       ddlog_lean.py <dir>       also writes the Lean modules of <dir>/DDLog2/ and <dir>/../Controls/DDLog2.lean
"""
import sys, os, math
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'scripts'))
import ddexp_lean as D  # noqa: E402
import explog_constants as EC  # noqa: E402
from rounding import dec_up  # noqa: E402

U, ETA0, E_A, E_F, E_P, B, XMAX = D.U, D.ETA0, D.E_A, D.E_F, D.E_P, D.B, D.XMAX
Q = 3
BOUND = Fr(15351, 1000)
EPS = BOUND * U ** 2
PHI = Fr(1, 2 ** 1071)
CG = Fr(1, 2 ** 40)                  # Lean's ddlCg, above every case's C
SUB = 4                              # intervals of |r| in a group of k != 0 where |r| exceeds 2^-12
PER_FILE = 2                         # groups of k != 0 with SUB intervals to a module of kernel checks
ETAB = Fr(5915, 1000) * U
D1 = U / (1 - U)
E1 = ETAB + U * (1 + ETAB)
E0 = ETAB * D1 + U * U + ETA0 + U * U / (2 * (1 - U)) + U * ((1 + ETAB) * D1 + U * (1 + U) + ETA0)
F3 = [Fr(x) for x in EC.greedy(Fr(1, 3), 8)[:2]]
FQ = {2: [Fr(-1, 2), Fr(0)], 3: F3}
PHIP = {i: abs(FQ[i][0] + FQ[i][1] - Fr((-1) ** (i + 1), i)) for i in FQ}
assert EC.greedy(Fr(-1, 2), 8)[0] == Fr(-1, 2)


def lin(l):
    """Lean's ddlE"""
    return E1 * l + E0


def small(l):
    """Lean's ddlEs"""
    return l * (U * (1 + l) + l)


def logv(C, q, i):
    return sum(C ** l / Fr(i + l) for l in range(q + 1 - i))


def up_dy(q, bits=64):
    """q > 0 rounded up to bits significant bits, a dyadic rational"""
    k = bits - (q.numerator.bit_length() - q.denominator.bit_length())
    return Fr(-((-q.numerator << k) // q.denominator), 1 << k)


def dn_dy(q, bits=64):
    """q > 0 rounded down to bits significant bits, a dyadic rational"""
    k = bits - (q.numerator.bit_length() - q.denominator.bit_length())
    return Fr((q.numerator << k) // q.denominator, 1 << k)


def bound(l, E, pos, a, b, delta, d):
    """Lean's ddlBQ and ddlCQ: the bound of the convex mode and its C, with eta = eta_c = ETA0,
    eta_x = eta_p = 2 ETA0, and e^z from the upper end of the 16-term enclosure"""
    Dx = 4 * ETA0
    Dp = 4 * ETA0
    Dc = 2 * ETA0
    assert 0 <= l and 0 <= E and 0 <= a <= 1 and 0 <= b and 0 <= delta and E + b + delta <= 1    # DDLogEnd
    tb = D.exp_up(b) - 1 if pos else b
    Em = D.core_e(tb, ETA0, b, d)
    xi = (D.exp_up(E + delta - a) if pos else D.exp_up(E + b + delta)) + Dx
    phib = max(xi - 1, E + b + delta + Dx)
    X1 = D.exp_up(b + delta) - 1 - (b + delta)
    X2 = D.exp_up(b + delta)
    X3 = D.exp_up(E + delta) - 1
    X4 = D.exp_up(E)
    X5 = D.exp_up(delta) - 1
    X6 = X4 - 1
    eft = E_P * (phib * (tb + Em)) + Dp + Fr(1, 2 ** (B + 12)) * max(phib, tb + Em)
    es = E_A * (2 * X1 + X2 * X3 + Em + Dx)
    Ed = X4 * X5 + Dx * (1 + tb + Em)
    ec = E_A * (X6 + xi * Em + Ed + eft + es)
    Ec = xi * Em + Ed + eft + es + ec
    C = X6 + Ec
    assert C < 1
    e2 = D.horner_b(C, Dc, PHIP, lambda k: logv(C, Q, k), Q, Q - 2)
    Zh = C * (logv(C, Q, 2) + e2)
    eh = E_P * Zh + Dc
    hb = Zh + eh
    eg = E_F * (1 + hb)
    er = E_P * (C * (1 + hb + eg)) + Dc
    P = er + C * (eg + eh + C * e2) + max(C ** (Q + 1) / (Q + 1), Fr(1, 2 ** (B + 13)) * C) / (1 - C) + Ec / (1 - C)
    return E_F * (l + P) + P, C


def floor_ok(pos, d, a, b):
    """Lean's DDLFloor and DDLSize"""
    tb = D.exp_up(b) - 1 if pos else b
    return (d == 1 or D.FLOOR * (1 + U) <= a / (1 + a) - D.core_e(tb, Fr(0), b, d)) and b <= Fr(1, 2) and \
        D.core_e(tb, ETA0, b, d) <= Fr(1, 4)


# -- the reduction of (-y0, 0): X = ybar(745.2) and a zero low part
YB = XMAX + lin(XMAX)
RMAX = (Fr(1, 2) + YB * (D.RED_DL + U * D.CR)) * D.LN2B
A0 = RMAX + 1075 * max(abs(D.CH - D.LN2A), abs(D.CH - D.LN2B))
DD_EQ0 = E_F * (1075 * D.DD_C + D.DD_E1)


def red_delta(rb):
    """Lean's ddlDelta"""
    return D.DD_E1 + DD_EQ0 + E_F * (rb + 1075 * D.DD_ETA + D.DD_E1 + DD_EQ0) + 1075 * D.DD_ETA


DSTAR = up_dy(red_delta(RMAX))
TOP1 = up_dy(RMAX + DSTAR)
TOP0 = up_dy(1 / (2 * D.CR))
LK = dn_dy((1 / (2 * D.CR * (1 + U)) - E0) / (1 + E1))
SPLIT = U * (1 - U) / 2
assert A0 < Fr(1, 2) and YB <= Fr(7453, 10) and max(TOP0, TOP1) < Fr(1, 2) * (1 - D.UB)
assert (1 + E1) * LK + E0 <= 1 / (2 * D.CR * (1 + U)) and LK <= XMAX


def groups(top):
    """(d', e_lo, e_hi, lo, hi), as ddexp_lean.groups, for a bound top of |r|"""
    out = []
    e = -2
    while True:
        d = D.degree(e)
        if d == 1:
            out.append((1, e, e, Fr(0), min(top, Fr(2) ** (e + 1))))
            return out
        e_lo = e
        while D.degree(e_lo - 1) == d:
            e_lo -= 1
        out.append((d, e_lo, e, Fr(2) ** e_lo * (1 - D.UB), min(top, Fr(2) ** (e + 1))))
        e = e_lo - 1


def edges(lo, hi):
    if hi <= Fr(1, 2 ** 12):
        return [(lo, hi)]
    e = [lo] + [Fr(round(float(lo) * float(hi / lo) ** (i / SUB) * 2 ** 60), 2 ** 60) for i in range(1, SUB)] + [hi]
    return list(zip(e, e[1:]))


def chord(pos, d, a, l1, E1v, b1, l2, E2v, b2, delta):
    """Lean's DDLChord; returns the largest ratio"""
    f1, _ = bound(l1, E1v, pos, a, b1, delta, d)
    f2, c2 = bound(l2, E2v, pos, a, b2, delta, d)
    assert f1 <= EPS * l1 and f2 <= EPS * l2 and c2 <= CG and floor_ok(pos, d, a, b2)
    return max(f1 / l1, f2 / l2)


def chord0(pos, d, a, l2, E2v, b2):
    """Lean's DDLChord0; returns E(0) and the slope"""
    f0, _ = bound(Fr(0), Fr(0), pos, a, Fr(0), Fr(0), d)
    f2, c2 = bound(l2, E2v, pos, a, b2, Fr(0), d)
    assert f0 <= PHI and f2 <= EPS * l2 + PHI and c2 <= CG and floor_ok(pos, d, a, b2)
    return f0, (f2 - f0) / l2


def cases():
    """the groups of k = 0 on the linear piece, those on the second piece, and the groups of k != 0"""
    k0lin, k0small, k1 = [], [], []
    for (d, e_lo, e_hi, a, hi) in groups(TOP0):
        l2 = up_dy((hi + E0) / (1 - E1))
        assert hi + E0 <= (1 - E1) * l2
        if a == 0 or (a - E0) / (1 + E1) < Fr(1, 2 ** 60):
            assert l2 < SPLIT
            res = [chord0(pos, d, a, l2, small(l2), l2 + small(l2)) for pos in (True, False)]
            k0small.append(dict(d=d, e_lo=e_lo, e_hi=e_hi, a=a, l2=l2, floor=max(r[0] for r in res),
                                worst=max(r[1] for r in res)))
        else:
            l1 = dn_dy((a - E0) / (1 + E1))
            assert 0 <= l1 and (1 + E1) * l1 + E0 <= a
            res = [chord(pos, d, a, l1, lin(l1), l1 + lin(l1), l2, lin(l2), l2 + lin(l2), Fr(0))
                   for pos in (True, False)]
            k0lin.append(dict(d=d, e_lo=e_lo, e_hi=e_hi, a=a, l1=l1, l2=l2, worst=max(res)))
    for (d, e_lo, e_hi, lo, hi) in groups(TOP1):
        bins, worst = [], (Fr(0), None)
        for (a, b) in edges(lo, hi):
            dl = red_delta(b + DSTAR)
            for pos in (True, False):
                r = chord(pos, d, a, LK, lin(LK), b, XMAX, lin(XMAX), b, dl)
                if r > worst[0]:
                    worst = (r, (pos, a, b))
            bins.append((a, b))
        k1.append(dict(d=d, e_lo=e_lo, e_hi=e_hi, bins=bins, worst=worst[0], at=worst[1]))
    return k0lin, k0small, k1


def dy(q):
    """an exact dyadic rational as Lean's pair (m, k)"""
    k = q.denominator.bit_length() - 1
    assert q.denominator == 1 << k
    return f'({q.numerator}, {k})'


HEAD = 'This file is written by `ddlog_lean.py`.'
T0 = 'ℕ × ℤ × ℤ × (ℤ × ℕ) × (ℤ × ℕ)'
T0S = 'ℕ × ℤ × ℤ × (ℤ × ℕ)'
T1 = 'ℕ × ℤ × ℤ × List ((ℤ × ℕ) × (ℤ × ℕ))'


def lean_modules(k0lin, k0small, k1):
    small_g, last0 = k0small
    grp1, last1 = k1[:-1], k1[-1]
    data = ['import Mathlib.Data.Int.Notation', 'import Mathlib.Data.Nat.Notation', '', '/-!',
            '# Proposition 44, `DD::ln` at `p = 53`: the cases', '',
            'The two parts of `F\'_3`, upper bounds of the reduction\'s `δ*` and of `|r|` for `k = 0` and for `k ≠ 0`,',
            'and a lower bound of the `ℓ` with `k ≠ 0`, as dyadic pairs `(m, k)` for `m / 2 ^ k`; the groups of',
            '`k = 0` on the start\'s linear piece, as `(d\', e_lo, e_hi, ℓ₁, ℓ₂)`, and on its second piece, as',
            '`(d\', e_lo, e_hi, ℓ₂)`; and the groups of `k ≠ 0`, as `(d\', e_lo, e_hi, bins)`, as for `DD::exp`.',
            HEAD, '-/', '', 'namespace ExpansionBounds', '',
            '/-- the first two parts of the greedy expansion of `1/3` -/',
            f'def ddlF3S : (ℤ × ℕ) × (ℤ × ℕ) := ({dy(F3[0])}, {dy(F3[1])})', '',
            '/-- an upper bound of `δ*` -/', f'def ddlDStarS : ℤ × ℕ := {dy(DSTAR)}', '',
            '/-- an upper bound of `|y_0|` for `k = 0` -/', f'def ddlTop0S : ℤ × ℕ := {dy(TOP0)}', '',
            '/-- an upper bound of `|r|` for `k ≠ 0` -/', f'def ddlTop1S : ℤ × ℕ := {dy(TOP1)}', '',
            '/-- a lower bound of the `ℓ` with `k ≠ 0` -/', f'def ddlLkS : ℤ × ℕ := {dy(LK)}', '']
    for i, c in enumerate(k0lin):
        data += [f'/-- `k = 0`, the group of degree {c["d"]} -/', f'def ddl0G{i} : {T0} :=',
                 f'  ({c["d"]}, {c["e_lo"]}, {c["e_hi"]}, {dy(c["l1"])}, {dy(c["l2"])})', '']
    h = len(k0lin) // 2
    data += ['/-- `k = 0`, the groups on the linear piece -/', f'def ddl0Lin : List ({T0}) :=',
             '  [' + ', '.join(f'ddl0G{i}' for i in range(h)) + ',',
             '    ' + ', '.join(f'ddl0G{i}' for i in range(h, len(k0lin))) + ']', '',
             f'/-- `k = 0`, the group of degree {small_g["d"]}, on the second piece -/', f'def ddl0S : {T0S} :=',
             f'  ({small_g["d"]}, {small_g["e_lo"]}, {small_g["e_hi"]}, {dy(small_g["l2"])})', '',
             '/-- `k = 0`, the last group, of degree 1 -/', f'def ddl0Last : {T0S} :=',
             f'  ({last0["d"]}, {last0["e_lo"]}, {last0["e_hi"]}, {dy(last0["l2"])})', '']

    def grp_text(c):
        bins = ', '.join(f'({dy(a)}, {dy(b)})' for a, b in c['bins'])
        return f'({c["d"]}, {c["e_lo"]}, {c["e_hi"]}, [{bins}])'

    for i, c in enumerate(grp1):
        data += [f'/-- `k ≠ 0`, the group of degree {c["d"]} -/', f'def ddl1G{i} : {T1} :=', f'  {grp_text(c)}', '']
    h = len(grp1) // 2
    data += ['/-- `k ≠ 0`, the groups but the last -/', f'def ddl1Grp : List ({T1}) :=',
             '  [' + ', '.join(f'ddl1G{i}' for i in range(h)) + ',',
             '    ' + ', '.join(f'ddl1G{i}' for i in range(h, len(grp1))) + ']', '',
             '/-- `k ≠ 0`, the last group, of degree 1 -/', f'def ddl1Last : {T1} :=', f'  {grp_text(last1)}', '',
             'end ExpansionBounds', '']
    mods = {'Data.lean': '\n'.join(data)}
    runs = []                                            # lists of theorem lines, a module each
    half = len(k0lin) // 2
    for part in (range(half), range(half, len(k0lin))):
        runs.append([(f'`k = 0`, the group of degree {k0lin[i]["d"]}', f'theorem ddl0_g{i} : DDL0Lin ddl0G{i}')
                     for i in part])
    runs[-1] += [(f'`k = 0`, the group of degree {small_g["d"]}', 'theorem ddl0_s : DDL0Small false ddl0S'),
                 ('`k = 0`, the last group', 'theorem ddl0_last : DDL0Small true ddl0Last')]
    big = [i for i, c in enumerate(grp1) if len(c['bins']) > 1]
    rest = [i for i, c in enumerate(grp1) if len(c['bins']) == 1]
    for j in range(0, len(big), PER_FILE):
        runs.append([(f'`k ≠ 0`, the group of degree {grp1[i]["d"]}',
                      f'theorem ddl1_g{i} : DDL1Group false ddl1G{i}') for i in big[j:j + PER_FILE]])
    runs.append([(f'`k ≠ 0`, the group of degree {grp1[i]["d"]}', f'theorem ddl1_g{i} : DDL1Group false ddl1G{i}')
                 for i in rest] + [('`k ≠ 0`, the last group', 'theorem ddl1_last : DDL1Group true ddl1Last')])
    for f, items in enumerate(runs):
        run = ['import ExpansionBounds.DDLog2.Defs', '', '/-!',
               f'# Proposition 44, `DD::ln` at `p = 53`: the kernel\'s checks, part {f}', '',
               'The chords of each group: for `k = 0`, `DDL0Lin` or `DDL0Small`; for `k ≠ 0`, `DDL1Group`.', HEAD,
               '-/', '', 'namespace ExpansionBounds', '']
        for doc, th in items:
            run += ['set_option maxHeartbeats 4000000 in', f'/-- {doc} -/', f'{th} := by decide +kernel', '']
        run += ['end ExpansionBounds', '']
        mods[f'Run{f}.lean'] = '\n'.join(run)
    al = [f'import ExpansionBounds.DDLog2.Run{f}' for f in range(len(runs))]
    al += ['', '/-!', '# Proposition 44, `DD::ln` at `p = 53`: every group', '',
           'The kernel\'s checks hold for each group of exponents, for `k = 0` and for `k ≠ 0`.', HEAD, '-/', '',
           'namespace ExpansionBounds', '', '/-- `k = 0`: every group on the linear piece -/',
           'theorem ddl0_all : ∀ g ∈ ddl0Lin, DDL0Lin g := by', '  intro g hg',
           '  simp only [ddl0Lin, List.mem_cons, List.not_mem_nil, or_false] at hg',
           '  rcases hg with ' + ' | '.join(['rfl'] * (len(k0lin) // 2)) + ' |',
           '    ' + ' | '.join(['rfl'] * (len(k0lin) - len(k0lin) // 2))]
    al += [f'  · exact ddl0_g{i}' for i in range(len(k0lin))]
    al += ['', '/-- `k ≠ 0`: every group but the last -/',
           'theorem ddl1_all : ∀ g ∈ ddl1Grp, DDL1Group false g := by',
           '  intro g hg', '  simp only [ddl1Grp, List.mem_cons, List.not_mem_nil, or_false] at hg',
           '  rcases hg with ' + ' | '.join(['rfl'] * (len(grp1) // 2)) + ' |',
           '    ' + ' | '.join(['rfl'] * (len(grp1) - len(grp1) // 2))]
    al += [f'  · exact ddl1_g{i}' for i in range(len(grp1))]
    al += ['', 'end ExpansionBounds', '']
    mods['All.lean'] = '\n'.join(al)
    # the controls
    wi = max(range(len(grp1)), key=lambda i: grp1[i]['worst'])
    wc = grp1[wi]
    ws, wa, wb = wc['at']
    assert wc['worst'] > Fr(15350, 1000) * U ** 2
    f0 = bound(Fr(0), Fr(0), True, small_g['a'], Fr(0), Fr(0), small_g['d'])[0]
    assert f0 > PHI / 2
    cw = bound(XMAX, lin(XMAX), ws, wa, wb, red_delta(wb + DSTAR), wc['d'])[1]
    assert cw > Fr(1, 2 ** 42)
    c3 = next(c for c in k0lin if c['d'] == 3)
    assert not c3['l2'] < SPLIT
    b0s = small_g['l2'] + small(small_g['l2'])
    assert small_g['d'] == 2 and not floor_ok(True, 2, Fr(1, 2 ** 968), b0s)
    assert not all(any(c['e_lo'] <= e <= c['e_hi'] for c in k0lin[1:]) for e in range(-59, -1))
    assert not all(any(c['e_lo'] <= e <= c['e_hi'] for c in grp1[1:]) for e in range(-118, -1))
    sgn = 'true' if ws else 'false'
    ctl = ['import ExpansionBounds.DDLog2', '', '/-!', '# Controls of Proposition 44\'s constants for `DD::ln`', '',
           'Each claim below is one of the kernel\'s checks of `DDLog2.lean` with a wrong number, a wrong degree or an',
           'interval or a group left out, and the kernel proves its negation.', HEAD, '-/', '',
           'namespace ExpansionBounds', '',
           'set_option maxHeartbeats 4000000 in', '/-- the worst case\'s ratio is not within `15.350u²` -/',
           f'example : ¬ ddlBQ {sgn} {wc["d"]} (dyQ {dy(wa)}) (dyQ ddlLkS) (ddlE (dyQ ddlLkS)) (dyQ {dy(wb)})',
           f'    (ddlDelta (dyQ {dy(wb)} + dyQ ddlDStarS)) ≤ 15350 / 1000 * red8U ^ 2 * dyQ ddlLkS := by',
           '  decide +kernel', '', 'set_option maxHeartbeats 4000000 in',
           '/-- `𝓔(0)` is not within `2^{-1072}` -/',
           f'example : ¬ ddlBQ true {small_g["d"]} ((2 : ℚ) ^ ({small_g["e_lo"]} : ℤ) * (1 - 1 / 2 ^ 46)) 0 0 0 0 ≤',
           '    1 / 2 ^ 1072 := by decide +kernel', '',
           'set_option maxHeartbeats 4000000 in', '/-- the worst case\'s `C` is not within `2^{-42}` -/',
           f'example : ¬ ddlCQ {sgn} {wc["d"]} (dyQ {dy(wa)}) (ddlE red8X) (dyQ {dy(wb)})',
           f'    (ddlDelta (dyQ {dy(wb)} + dyQ ddlDStarS)) ≤ 1 / 2 ^ 42 := by decide +kernel', '',
           'set_option maxHeartbeats 4000000 in', '/-- a group with the wrong degree is not accepted -/',
           f'example : ¬ DDL1Group false ({wc["d"] - 1}, {wc["e_lo"]}, {wc["e_hi"]}, ddl1G{wi}.2.2.2) := by',
           '  decide +kernel', '',
           'set_option maxHeartbeats 4000000 in', '/-- a group with an interval left out is not accepted -/',
           f'example : ¬ DDL1Group false ({wc["d"]}, {wc["e_lo"]}, {wc["e_hi"]}, ddl1G{wi}.2.2.2.drop 1) := by',
           '  decide +kernel', '',
           '/-- the groups of `k = 0` on the linear piece, the first left out, do not cover `-59 ≤ e ≤ -2` -/',
           'example : ¬ ∀ e : ℤ, -59 ≤ e → e ≤ -2 → ∃ g ∈ ddl0Lin.tail, g.2.1 ≤ e ∧ e ≤ g.2.2.1 := by decide +kernel',
           '', '/-- the groups of `k ≠ 0`, the first left out, do not cover `-118 ≤ e ≤ -2` -/',
           'example : ¬ ∀ e : ℤ, -118 ≤ e → e ≤ -2 → ∃ g ∈ ddl1Grp.tail, g.2.1 ≤ e ∧ e ≤ g.2.2.1 := by decide +kernel',
           '', f'/-- the floor of the scaling back is not met at degree {small_g["d"]} by an interval from '
           '`2^{-968}`, below it -/',
           f'example : ¬ DDLFloor true {small_g["d"]} (1 / 2 ^ 968) (dyQ ddl0S.2.2.2 + ddlEs (dyQ ddl0S.2.2.2)) := by',
           '  decide +kernel', '',
           '/-- the group of degree 3 is not on the start\'s second piece: its `ℓ₂` is above `u(1 - u)/2` -/',
           f'example : ¬ dyQ {dy(c3["l2"])} < red8U * (1 - red8U) / 2 := by decide +kernel', '',
           '/-- the least `ℓ` of a group of `k = 0`, one unit higher, is not below the `ℓ` that select it -/',
           f'example : ¬ (1 + ddlE1) * dyQ ({c3["l1"].numerator + 1}, {c3["l1"].denominator.bit_length() - 1}) +',
           '    ddlE0 ≤',
           f'    (2 : ℚ) ^ ({c3["e_lo"]} : ℤ) * (1 - 1 / 2 ^ 46) := by decide +kernel', '',
           'end ExpansionBounds', '']
    return mods, '\n'.join(ctl)


def sci(x, up):
    """x >= 0 at four significant digits as d.ddde+xx, rounded up or down: a printed interval holds the exact one"""
    x = Fr(x)
    if x == 0:
        return '0'
    e = len(str(x.numerator)) - len(str(x.denominator))
    while Fr(10) ** e > x:
        e -= 1
    while Fr(10) ** (e + 1) <= x:
        e += 1
    y = x / Fr(10) ** (e - 3)
    m = -(-y.numerator // y.denominator) if up else y.numerator // y.denominator
    if m == 10 ** 4:
        m, e = 1000, e + 1
    d = str(m)
    return f'{d[0]}.{d[1:]}e{e:+03d}'


def main():
    k0lin, k0small, k1 = cases()
    n0 = 4 * len(k0lin) + 4 * len(k0small)
    n1 = sum(4 * len(c['bins']) for c in k1)
    # the ratios E(l)/l of the pieces with l1 > 0, and the slopes of the chords from E(0) of those that start at 0
    ratio = max([c['worst'] for c in k0lin] + [c['worst'] for c in k1])
    slope = max(c['worst'] for c in k0small)
    worst = max(ratio, slope)
    floor = max(c['floor'] for c in k0small)
    for c in k0lin:
        print(f'k = 0   d = {c["d"]:2d}  l in [{sci(c["l1"], False)}, {sci(c["l2"], True)}]  '
              f'ratio <= {dec_up(c["worst"] / U ** 2)} u^2')
    for c in k0small:
        print(f'k = 0   d = {c["d"]:2d}  l in [0, {sci(c["l2"], True)}]  '
              f'E(0) <= {dec_up(c["floor"] / PHI, 4)} 2^-1071  slope <= {dec_up(c["worst"] / U ** 2)} u^2')
    for c in k1:
        print(f'k != 0  d = {c["d"]:2d}  {len(c["bins"])} intervals  ratio <= {dec_up(c["worst"] / U ** 2)} u^2')
    print(f'{n0} + {n1} = {n0 + n1} evaluations at the ends; largest ratio {dec_up(ratio / U ** 2)} u^2, largest '
          f'slope from E(0) {dec_up(slope / U ** 2)} u^2 (bound {float(BOUND):.3f}); '
          f'E(0) <= {dec_up(floor / PHI, 4)} 2^-1071')
    assert worst <= EPS and floor <= PHI
    assert not worst <= Fr(15350, 1000) * U ** 2, 'control: the ratio one unit lower must fail'
    print('control: the largest ratio is above 15.350 u^2, as it must be')
    if len(sys.argv) > 1:
        mods, ctl = lean_modules(k0lin, k0small, k1)
        d = os.path.join(os.path.realpath(sys.argv[1]), 'DDLog2')  # resolved, so `..` climbs the real tree
        os.makedirs(d, exist_ok=True)
        for name, text in list(mods.items()) + [(os.path.join('..', '..', 'Controls', 'DDLog2.lean'), ctl)]:
            path = os.path.normpath(os.path.join(d, name))
            if os.path.exists(path) and open(path, encoding='utf-8').read() == text:
                continue
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, 'w', encoding='utf-8') as f:
                f.write(text)
            print('wrote', path)


if __name__ == '__main__':
    main()
