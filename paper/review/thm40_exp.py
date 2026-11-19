#!/usr/bin/env python3
"""Theorem 40's constant, recomputed in rational arithmetic rounded up.

Written from the text of the appendix "The exponential and the logarithm" at commit 187ce44 (Lemmas 33, 38 and 39,
Theorem 40 and its proof), without reading explog_consts.py, explog_bits.py, their outputs or the earlier
recomputation of this folder. It shares gop.py and explog_common.py with the other recomputations here and no code
with the paper's scripts.

The cases are those of the theorem: k = 0 or not, each exponent e of step (2) with m >= 1, the exponents of one
degree d' together for m = 0, both signs of r, and eight geometric intervals of |r| where |r| exceeds 2^-12.

    python3 thm40_exp.py           # prints the largest epsilon / u^8 and its case, then PASS (about 2 minutes)
    python3 thm40_exp.py control   # the squarings' factor g_j left out: must print FAIL (exit 0)
"""
import sys
from fractions import Fraction as Fr

import gop
from gop import abar, dec_up, g_addf, up
from explog_common import (Consts, U, degree, exp_down, exp_up, expm1_up, lemma38_setup, lemma38b, lemma39)

N, S, D, THETA = 8, 6, 43, 2
X = Fr(7452, 10)


def groups(c, rtop, pi_tail):
    """The cases' exponents: (e_low, e_high, m, d'), with the range of |r| that selects them."""
    out = []
    e = -1
    while Fr(2) ** e > rtop:
        e -= 1
    last = None
    while e >= -c.B - 2:
        m, dp = degree(c, e, S, D)
        if m == 0 and last is not None and last[2] == 0 and last[3] == dp:
            last[0] = e
        else:
            last = [e, e, m, dp]
            out.append(last)
        e -= 1
    res = []
    for e_lo, e_hi, m, dp in out:
        hi = min(Fr(2) ** (e_hi + 1), rtop)
        lo = max(Fr(0), Fr(2) ** e_lo * (1 - Fr(1, 2 ** 46)) - 2 * pi_tail(hi))
        if dp == 1:
            lo = Fr(0)
        res.append((e_lo, e_hi, m, dp, lo, hi))
    return res


def intervals(lo, hi):
    if hi <= Fr(1, 2 ** 12) or lo <= 0:
        return [(lo, hi)]
    ratio = float(hi / lo) ** 0.125
    pts = [lo] + [Fr(float(lo) * ratio ** i) for i in range(1, 8)] + [hi]
    return list(zip(pts[:-1], pts[1:]))


def main():
    control = 'control' in sys.argv[1:]
    gop.ROUND_BITS = 300
    n = N
    un = U ** n
    c = Consts(n)
    rho = THETA * U
    gamma = rho * X / (1 - rho)
    beta, rmax, alpha0 = lemma38_setup(c, X, gamma)
    alpha = [alpha0] + [rho ** i * X for i in range(1, n)]
    dstar, _ = lemma38b(c, alpha, rmax)
    rtop = rmax + dstar
    ab = abar(n, THETA, U)
    worst = (Fr(0), None)
    count = 0
    for knz in (0, 1):
        def pi_of(b):
            if knz:
                return lemma38b(c, alpha, b + dstar)
            return Fr(0), [x * b for x in ab]

        def tail(b):
            return sum(pi_of(b)[1][1:])

        for e_lo, e_hi, m, dp, lo, hi in groups(c, rtop, tail):
            cbar = Fr(2) ** (e_hi + 1)
            for a, b in intervals(lo, hi):
                delta, pi = pi_of(b)
                for sign in (1, -1):
                    E, psi, _ = lemma39(c, n, a, b, pi, m, dp, cbar, sign)
                    if control and m:
                        # without g_j the error of t would not double per squaring
                        E = E / 2 ** m
                    if sign > 0:
                        Z = exp_up(b) + E
                        v = exp_down(a - delta)
                    else:
                        Z = exp_up(-a) + E
                        v = exp_down(-(b + delta))
                    es, _ = g_addf(psi, Fr(1), Z, U, Z + sum(psi[1:]))
                    eps = up((E + es) / v + expm1_up(delta))
                    count += 1
                    if eps > worst[0]:
                        worst = (eps, (knz, e_lo, e_hi, m, dp, sign, float(a), float(b)))
    eps, case = worst
    got = float(eps / un)
    knz, e_lo, e_hi, m, dp, sign, a, b = case
    print(f'{count} cases; the largest epsilon / u^8 = {dec_up(eps / un, 9)} (rounded up)')
    print(f'  at k {"!=" if knz else "="} 0, e = {e_hi}, m = {m}, d\' = {dp}, r {"> 0" if sign > 0 else "< 0"}, '
          f'|r| in [{a:.6f}, {b:.6f}]')
    ok = got <= 3.661 and abs(got - 3.660061) <= 1.01e-6
    print(f'the paper has 3.661 (Theorem 40) and 3.660061 (explog_consts.txt): {"ok" if ok else "DIFFERS"}')
    ok &= (knz, m, sign) == (1, 5, -1)
    print('PASS' if ok else 'FAIL')
    return 0 if ok or control else 1


if __name__ == '__main__':
    sys.exit(main())
