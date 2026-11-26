"""Proposition 44's bound of the double-double exponential, as the Lean definitions of DDExpEval.lean compute it.

The cases are those of explog_consts.py for double words (dd_exp): a group of exponents e of step (2) with the same
degree d' (m = 0 in every group, as s = 1), a sign of r and an interval [a, b] of |r|. One family of cases serves
k = 0 and k != 0: each is evaluated with the reduction's delta* of k != 0, which is above the 0 of k = 0, and with the
larger of the two bounds of |r|. Every value is an exact rational, the mirror of the real bound, with e^z from the
16-term enclosure of ExpEval.lean (expUpQ, expLoQ); nothing is rounded but delta* and the bound of |r|, rounded up to
dyadic numbers, and the cuts between a group's intervals of |r|, which edges() places in binary64 arithmetic and rounds
to dyadic numbers. The cuts only decide where two intervals meet: every interval is then evaluated and checked in
exact rational arithmetic, so a regeneration on another platform must give the same cuts to give the same tables.

usage: ddexp_lean.py             prints the bounds
       ddexp_lean.py <dir>       also writes the Lean modules of <dir>/DDExp2/ and <dir>/../Controls/DDExp2.lean
"""
import sys, os, math
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'scripts'))
import explog_constants as EC  # noqa: E402
from rounding import dec_up  # noqa: E402

U = Fr(1, 2 ** 53)
S, DEG = 1, 27                       # the squaring threshold 2^-s and the largest degree
B = 53 * 2 + 12
ETA0 = Fr(1, 2 ** 1075)
FLOOR = Fr(1, 2 ** 967)              # the scaling back keeps a double word whose high part is at least this
XMAX = Fr(7452, 10)
BOUND = Fr(5465, 1000)
SUB = 8                              # intervals of |r| in a group where |r| exceeds 2^-12
UB = Fr(1, 2 ** 46)
PER_FILE = 6                         # groups to a module of kernel checks
fact = math.factorial

E_A = 3 * U * U / (1 - 4 * U)
E_F = 2 * U * U
E_M = 2 * U * U
E_P = 5 * U * U / (1 + U) ** 2

# -- Lemma 38's constants, as ExpRed8.lean
CONST = EC.constants()
_lo, _hi = CONST['ln2']
LN2A = Fr((_lo.numerator << 600) // _lo.denominator - 1, 1 << 600)
LN2B = Fr(-((-_hi.numerator << 600) // _hi.denominator) + 1, 1 << 600)
CH = Fr(CONST['hi'])
CL = [Fr(x) for x in CONST['lo'][:2]]
CR = Fr(1.4426950408889634)
RED_DL = max(abs(CR - 1 / LN2B), abs(CR - 1 / LN2A))
RED_EPSK = XMAX * (RED_DL + U * CR)
DD_XT = U * XMAX                                         # |x_l| <= u |x_h|
DD_RMAX = (Fr(1, 2) + RED_EPSK) * LN2B + DD_XT           # Lean's dd2RMax
DD_C = abs(CL[0] + CL[1])
DD_ETA = max(abs(CH + CL[0] + CL[1] - LN2A), abs(CH + CL[0] + CL[1] - LN2B))
DD_E1 = E_M * (1075 * DD_C)
DD_EQ = E_F * (1075 * DD_C + DD_E1 + DD_XT)


def red_delta(rb):
    """Lean's dd2Delta rb"""
    return DD_E1 + DD_EQ + E_F * (rb + 1075 * DD_ETA + DD_E1 + DD_EQ) + 1075 * DD_ETA


def up_dy(q, bits):
    """q rounded up to bits significant bits, as a dyadic pair (m, k) for m / 2^k"""
    k = bits - (q.numerator.bit_length() - q.denominator.bit_length())
    m = -((-q.numerator << k) // q.denominator)
    return (m, k)


def dyq(mk):
    return Fr(mk[0], 2 ** mk[1])


DELTA_S = up_dy(red_delta(DD_RMAX), 64)
DELTA = dyq(DELTA_S)
TOP_S = up_dy(max((1 + U) / (2 * CR), DD_RMAX + DELTA), 64)
TOP = dyq(TOP_S)

# -- the coefficients F_j of 1/j!, two parts
FK = [[Fr(x) for x in EC.greedy(Fr(1, fact(j)), 8)[:2]] for j in range(DEG + 1)]
PHI = [abs(FK[j][0] + FK[j][1] - Fr(1, fact(j))) for j in range(DEG + 1)]


def core_v(b, d, k):
    return sum(Fr(1, fact(k + l)) * b ** l for l in range(d + 1 - k))


def etr(b, d):
    return b ** (d + 1) / (fact(d + 1) * (1 - b / (d + 2)))


def exp_sum(z):
    return sum(z ** i / fact(i) for i in range(16))


def exp_rem(z):
    return abs(z) ** 16 / (fact(16) * (1 - abs(z) / 17))


def exp_up(z):
    return exp_sum(z) + exp_rem(z)


def exp_lo(z):
    return exp_sum(z) - exp_rem(z)


def horner_b(zb, D, phi, v, d, j):
    """Lean's ddHornerBQ"""
    e = phi[d]
    for i in range(1, j + 1):
        k = d - i
        Dk = zb * e + phi[k] + (E_P * (zb * (v(k + 1) + e)) + D)
        e = Dk + E_A * (v(k) + Dk)
    return e


def core_e(T0, eta, b, d):
    """Lean's ddCoreEQ"""
    if d == 1:
        return etr(b, 1)
    e2 = horner_b(b, 0, PHI, lambda k: core_v(b, d, k), d, d - 2)
    Zw = b * (core_v(b, d, 2) + e2)
    e1 = E_P * Zw
    Em = E_P * (b * (Zw + e1)) + b * (e1 + b * e2) + etr(b, d)
    return Em + E_A * (T0 + Em) + 2 * eta


def t0(pos, b):
    return exp_up(b) - 1 if pos else 1 - exp_lo(-b)


def exp_eps(eta, pos, a, b, delta, d):
    """Lean's ddExpEpsQ, with its numerator and divisor"""
    E = core_e(t0(pos, b), eta, b, d)
    num = E + E_F * ((exp_up(b) if pos else exp_up(-a)) + E)
    den = exp_lo(a - delta) if pos else exp_lo(-b - delta)
    return num / den + exp_up(delta) - 1, num, den


def degree(e):
    if e < -1 - B:
        return 1
    return min(DEG, -(-B // (-e - 1)))


def edges(lo, hi):
    """a partition of [lo, hi]: geometric, SUB pieces where hi > 2^-12, one piece below (explog_consts.edges)"""
    if hi <= Fr(1, 2 ** 12):
        return [(lo, hi)]
    e = [lo] + [Fr(round(float(lo) * float(hi / lo) ** (i / SUB) * 2 ** 60), 2 ** 60) for i in range(1, SUB)] + [hi]
    return list(zip(e, e[1:]))


def groups():
    """(d', e_lo, e_hi, lo, hi): the exponents e_lo <= e <= e_hi have degree d' and select |r| in [lo, hi]; the last
    group, of degree 1, is every e <= e_hi, with lo = 0"""
    out = []
    e = -S - 1
    assert Fr(2) ** (e + 1) * (1 - UB) > TOP                 # e = -1 selects no |r|: m = 0
    while True:
        d = degree(e)
        if d == 1:
            out.append((1, e, e, Fr(0), min(TOP, Fr(2) ** (e + 1))))
            return out
        e_lo = e
        while degree(e_lo - 1) == d:
            e_lo -= 1
        out.append((d, e_lo, e, Fr(2) ** e_lo * (1 - UB), min(TOP, Fr(2) ** (e + 1))))
        e = e_lo - 1


def cases():
    out = []
    for (d, e_lo, e_hi, lo, hi) in groups():
        bins = edges(lo, hi)
        worst = Fr(0)
        for (a, b) in bins:
            assert 0 <= a <= b and b + DELTA <= 1
            for pos in (True, False):
                eps, num, den = exp_eps(ETA0, pos, a, b, DELTA, d)
                assert den > 0 and num >= 0 and eps <= BOUND * U ** 2, (d, pos, float(a), float(b))
                if d != 1:
                    assert FLOOR * (1 + U) <= a / (1 + a) - core_e(t0(pos, b), Fr(0), b, d)
                worst = max(worst, eps)
        out.append(dict(d=d, e_lo=e_lo, e_hi=e_hi, lo=lo, hi=hi, bins=bins, worst=worst))
    return out


def dy(q):
    """an exact dyadic rational as Lean's pair (m, k)"""
    k = q.denominator.bit_length() - 1
    assert q.denominator == 1 << k
    return f'({q.numerator}, {k})'


HEAD = 'This file is written by `ddexp_lean.py`.'


def lean_modules(cs):
    grp = cs[:-1]
    last = cs[-1]
    data = ['import Mathlib.Data.Int.Notation', 'import Mathlib.Data.Nat.Notation', '', '/-!',
            '# Proposition 44, `DD::exp` at `p = 53`: the cases', '',
            'Upper bounds of the reduction\'s `δ*` and of `|r|`, as dyadic pairs `(m, k)` for `m / 2 ^ k`, and the',
            'groups of exponents `e` of step (2), as `(d\', e_lo, e_hi, bins)`: the exponents `e_lo ≤ e ≤ e_hi` have'
            ' the degree',
            '`d\'`, and `bins` are the intervals `[a, b]` of `|r|`, following each other from the least `|r|` that',
            'selects `e_lo` to the largest that selects `e_hi`. The last group, of degree 1, is every `e` up to its',
            f'`e_hi`. {HEAD}', '-/', '', 'namespace ExpansionBounds', '',
            '/-- an upper bound of `δ*` -/', f'def dd2DeltaS : ℤ × ℕ := ({DELTA_S[0]}, {DELTA_S[1]})', '',
            '/-- an upper bound of `|r|` -/', f'def dd2TopS : ℤ × ℕ := ({TOP_S[0]}, {TOP_S[1]})', '']

    def grp_text(c):
        bins = ', '.join(f'({dy(a)}, {dy(b)})' for a, b in c['bins'])
        return f'({c["d"]}, {c["e_lo"]}, {c["e_hi"]}, [{bins}])'

    for i, c in enumerate(grp):
        data += [f'/-- the group of degree {c["d"]} -/',
                 f'def dd2G{i} : ℕ × ℤ × ℤ × List ((ℤ × ℕ) × (ℤ × ℕ)) :=', f'  {grp_text(c)}', '']
    data += ['/-- the groups but the last -/', 'def dd2Grp : List (ℕ × ℤ × ℤ × List ((ℤ × ℕ) × (ℤ × ℕ))) :=',
             '  [' + ', '.join(f'dd2G{i}' for i in range(len(grp) // 2)) + ',',
             '    ' + ', '.join(f'dd2G{i}' for i in range(len(grp) // 2, len(grp))) + ']', '',
             '/-- the last group, of degree 1 -/', 'def dd2Last : ℕ × ℤ × ℤ × List ((ℤ × ℕ) × (ℤ × ℕ)) :=',
             f'  {grp_text(last)}', '', 'end ExpansionBounds', '']
    mods = {'Data.lean': '\n'.join(data)}
    nfiles = -(-len(grp) // PER_FILE)
    for f in range(nfiles):
        run = ['import ExpansionBounds.DDExp2.Defs', '', '/-!',
               f'# Proposition 44, `DD::exp` at `p = 53`: the kernel\'s checks, part {f}', '',
               '`DD2Group` for each group: its intervals follow each other, and each has `DD2Bin`.', HEAD, '-/', '',
               'namespace ExpansionBounds', '']
        for i in range(f * PER_FILE, min(len(grp), (f + 1) * PER_FILE)):
            run += ['set_option maxHeartbeats 4000000 in', f'/-- the group of degree {grp[i]["d"]} -/',
                    f'theorem dd2_g{i} : DD2Group false dd2G{i} := by decide +kernel', '']
        if f == nfiles - 1:
            run += ['set_option maxHeartbeats 4000000 in', '/-- the last group -/',
                    'theorem dd2_last : DD2Group true dd2Last := by decide +kernel', '']
        run += ['end ExpansionBounds', '']
        mods[f'Run{f}.lean'] = '\n'.join(run)
    al = [f'import ExpansionBounds.DDExp2.Run{f}' for f in range(nfiles)]
    al += ['', '/-!', '# Proposition 44, `DD::exp` at `p = 53`: every group', '',
           f'`DD2Group` holds for each group of exponents. {HEAD}', '-/', '', 'namespace ExpansionBounds', '',
           '/-- every group but the last -/', 'theorem dd2_all : ∀ g ∈ dd2Grp, DD2Group false g := by', '  intro g hg',
           '  simp only [dd2Grp, List.mem_cons, List.not_mem_nil, or_false] at hg',
           '  rcases hg with ' + ' | '.join(['rfl'] * len(grp))]
    al += [f'  · exact dd2_g{i}' for i in range(len(grp))]
    al += ['', 'end ExpansionBounds', '']
    mods['All.lean'] = '\n'.join(al)
    # the controls: the worst case one unit lower, and a wrong degree
    wi = max(range(len(grp)), key=lambda i: grp[i]['worst'])
    wc = grp[wi]
    wb = max(range(len(wc['bins'])), key=lambda j: max(exp_eps(ETA0, s, *wc['bins'][j], DELTA, wc['d'])[0]
                                                       for s in (True, False)))
    ws = max((True, False), key=lambda s: exp_eps(ETA0, s, *wc['bins'][wb], DELTA, wc['d'])[0])
    wa, wbb = wc['bins'][wb]
    weps = exp_eps(ETA0, ws, wa, wbb, DELTA, wc['d'])[0]
    assert weps > Fr(5464, 1000) * U ** 2
    g2 = next(c for c in grp if c['d'] == 2)
    a2, b2 = g2['bins'][0]
    assert not Fr(1, 2 ** 100) * (1 + U) <= a2 / (1 + a2) - core_e(t0(True, b2), Fr(0), b2, 2)
    assert not TOP < Fr(1, 4) * (1 - UB)
    assert not all(any(c['e_lo'] <= e <= c['e_hi'] for c in grp[1:]) for e in range(-118, -1))
    ctl = ['import ExpansionBounds.DDExp2', '', '/-!', '# Controls of Proposition 44\'s constant for `DD::exp`', '',
           'Each claim below is one of the kernel\'s checks of `DDExp2.lean` with a wrong number, a wrong degree, an',
           'interval or a group left out or a pair that is not a double word, and the kernel proves its negation.',
           HEAD,
           '-/', '', 'namespace ExpansionBounds', '',
           'set_option maxHeartbeats 4000000 in', '/-- the worst case\'s bound is not within `5.464u²` -/',
           f'example : ¬ ddExpEpsQ red8U dd2Eta {"true" if ws else "false"} (dyQ {dy(wa)}) (dyQ {dy(wbb)})',
           f'    (dyQ dd2DeltaS) dd2Phi {wc["d"]} ≤ 5464 / 1000 * red8U ^ 2 := by decide +kernel', '',
           'set_option maxHeartbeats 4000000 in', '/-- a group with the wrong degree is not accepted -/',
           f'example : ¬ DD2Group false ({wc["d"] - 1}, {wc["e_lo"]}, {wc["e_hi"]}, dd2G{wi}.2.2.2) := by',
           '  decide +kernel', '', 'set_option maxHeartbeats 4000000 in',
           '/-- a group with an interval left out is not accepted -/',
           f'example : ¬ DD2Group false ({wc["d"]}, {wc["e_lo"]}, {wc["e_hi"]}, dd2G{wi}.2.2.2.drop 1) := by',
           '  decide +kernel', '',
           '/-- the groups, the first left out, do not cover `-118 ≤ e ≤ -2` -/',
           'example : ¬ ∀ e : ℤ, -118 ≤ e → e ≤ -2 → ∃ g ∈ dd2Grp.tail, g.2.1 ≤ e ∧ e ≤ g.2.2.1 := by decide +kernel',
           '',
           '/-- the bound of `|r|`, which rules out the exponent `-1`, does not rule out `-2` -/',
           'example : ¬ dyQ dd2TopS < (2 : ℚ) ^ (-2 : ℤ) * (1 - 1 / 2 ^ 46) := by decide +kernel', '',
           '/-- the floor `2^{-100}` of the scaling back is not met at the least `|r|` of degree 2 -/',
           f'example : ¬ (1 / 2 ^ 100 : ℚ) * (1 + red8U) ≤ dyQ {dy(a2)} / (1 + dyQ {dy(a2)}) -',
           f'    ddCoreEQ red8U (ddT0Q true (dyQ {dy(b2)})) 0 (dyQ {dy(b2)}) dd2Phi 2 := by',
           '  decide +kernel', '',
           'set_option maxHeartbeats 4000000 in', '/-- the bound of `δ*` one unit lower is not one -/',
           'example : ¬ dd2Delta dd2RMax ≤ dyQ (dd2DeltaS.1 - 1, dd2DeltaS.2) := by decide +kernel', '',
           '/-- a pair whose low part is three quarters of an ulp of the high part is not a double word -/',
           'example : ¬ rnQ 53 (dyFn [(1, 0), (3, 54)] 0 + dyFn [(1, 0), (3, 54)] 1) = dyFn [(1, 0), (3, 54)] 0 := by',
           '  decide +kernel', '', 'end ExpansionBounds', '']
    return mods, '\n'.join(ctl)


def main():
    cs = cases()
    # the bounds rounded up; the last group, of degree 1, is every e up to its e_hi
    for i, c in enumerate(cs):
        es = f'e <= {c["e_hi"]}' if i == len(cs) - 1 else f'e in [{c["e_lo"]}, {c["e_hi"]}]'
        print(f'd = {c["d"]:2d}  {es}  {len(c["bins"])} intervals  eps <= {dec_up(c["worst"] / U ** 2)} u^2')
    print(f'delta* <= {dec_up(DELTA / U ** 2)} u^2, |r| <= {dec_up(TOP, 12)}, '
          f'{sum(2 * len(c["bins"]) for c in cs)} cases, largest {dec_up(max(c["worst"] for c in cs) / U ** 2)} u^2')
    if len(sys.argv) > 1:
        mods, ctl = lean_modules(cs)
        d = os.path.join(os.path.realpath(sys.argv[1]), 'DDExp2')  # resolved, so `..` climbs the real tree
        os.makedirs(d, exist_ok=True)
        for name, text in list(mods.items()) + [(os.path.join('..', '..', 'Controls', 'DDExp2.lean'), ctl)]:
            path = os.path.normpath(os.path.join(d, name))
            if os.path.exists(path) and open(path, encoding='utf-8').read() == text:
                continue
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, 'w', encoding='utf-8') as f:
                f.write(text)
            print('wrote', path)


if __name__ == '__main__':
    main()
