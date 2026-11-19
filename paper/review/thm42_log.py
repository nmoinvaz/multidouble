#!/usr/bin/env python3
"""Theorem 42's constants eps_ln and Phi, recomputed in rational arithmetic rounded up.

Written from the text of the appendix "The exponential and the logarithm" at commit 187ce44 (Lemmas 33, 38 and 39,
Theorem 42 and its proof), without reading explog_consts.py, explog_bits.py, their outputs or the earlier
recomputation of this folder. It shares gop.py and explog_common.py with the other recomputations here and no code
with the paper's scripts. The double-word start's eps_DW = 15.351 u^2 and Phi_DW = 2^-1071 are taken from the
statement of Proposition 44.

The bound is evaluated in the convex forms of the proof (VecSum's second bound alone, no minima in Lemma 39,
tbar_j = 2^j b' for r <= 0, the linear lower bound in fbar), at the ends of the chords the proof names: for k = 0
each case on [l_e^-, l_e^+], or on [0, l_e^+] where l_e^- < 2^-60; for k != 0 each case at l_k^-, 1, 4 and X, with
four geometric intervals of |r| where |r| exceeds 2^-12.

    python3 thm42_log.py           # prints eps_ln / u^8 and log2 Phi with their cases, then PASS (about 6 minutes)
    python3 thm42_log.py control   # the start's error E(l) left out of c: must print FAIL (exit 0)
"""
import sys
from fractions import Fraction as Fr

import gop
from gop import abar, g_add, g_addf, g_mul, lg, up
from explog_common import (ETA0, KBAR, Consts, U, degree, exp_up, expm1_up, expm2_up, horner, lemma38_setup,
                           lemma38b, lemma39)

N, S, D, Q, THETA = 8, 6, 43, 4, 2
X = Fr(7452, 10)
EPS_DW = Fr(15351, 1000) * U ** 2
PHI_DW = Fr(1, 2 ** 1071)
CONTROL = False


class Log:
    def __init__(self, n):
        self.n = n
        self.c = Consts(n)
        rho = THETA * U
        g = (n - 2) * U / (1 - (n - 2) * U)
        w = g * rho / (1 - 2 * rho - g * rho)
        d0 = w / (1 - w)
        aA = 3 * U ** 2 / (1 - 4 * U)
        self.Es = EPS_DW + aA
        self.Ec = EPS_DW * d0 + d0 + PHI_DW + aA + self.c.eta_L + Fr(1, 2 ** 2000)
        self.ab2 = abar(n, THETA, U)
        self.aby = [(1 - U) / (1 - 2 * U), U * (1 - U) / (1 - 2 * U)] + [Fr(0)] * (n - 2)

    def E(self, ell):
        return self.Es * ell + self.Ec

    def reduction(self, ell):
        """Lemma 38 for -y_0 at this l: alpha, delta^* and rbar_max."""
        ybar = ell + self.E(ell)
        piy = [ybar * x for x in self.aby]
        _, rmax, alpha0 = lemma38_setup(self.c, ybar / (1 - U), 2 * U * ybar)
        alpha = [alpha0] + piy[1:]
        dstar, _ = lemma38b(self.c, alpha, rmax)
        return alpha, dstar, rmax

    def calE(self, ell, knz, sign, m, dp, a, b, cbar):
        """The bound of |y - ln x| at l in a case; b None stands for b = l + E(l)."""
        n, c = self.n, self.c
        E = self.E(ell)
        ybar = ell + E
        piy = [ybar * x for x in self.aby]
        if knz:
            alpha, dstar, _ = self.reduction(ell)
            delta, pi = lemma38b(c, alpha, b + dstar)
        else:
            delta, pi = Fr(0), piy
            if b is None:
                b = ybar
        Em, psi, tb = lemma39(c, n, a, b, pi, m, dp, cbar, sign, convex=True)
        lost = 2 * n * ETA0
        if sign >= 0:
            xi = exp_up(E + delta - a) + lost
            xim1 = (expm1_up(E + delta - a) if E + delta >= a else Fr(0)) + lost
        else:
            xi = exp_up(E + b + delta) + lost
            xim1 = expm1_up(E + b + delta) + lost
        fbar = max(xim1, E + b + delta + lost)
        pix = [x * xi + 2 * ETA0 for x in self.ab2]
        _, pif = g_addf(pix, Fr(1), fbar, U, fbar + sum(pix[1:]))
        eft, nu = g_mul(pif, psi, fbar * (tb + Em), U)
        eft += lost + Fr(1, 2 ** (c.B + 12)) * max(fbar, tb + Em)
        nu = [x + 2 * ETA0 for x in nu]
        bh = b + delta
        efpt, zeta = g_add(pif, psi, 2 * expm2_up(bh) + exp_up(bh) * expm1_up(E + delta) + Em + lost, U)
        cstar = Fr(0) if CONTROL else expm1_up(E)
        Edel = exp_up(E) * expm1_up(delta) + lost * (1 + tb + Em)
        ec, chi1 = g_add(zeta, nu, cstar + xi * Em + Edel + eft + efpt, U)
        Ecc = xi * Em + Edel + eft + efpt + ec
        C = up(cstar + Ecc)
        _, zeta1 = g_add(pif, psi, C, U)
        chi = [max(x, y) for x, y in zip(chi1, zeta1)]
        e2, pih, v2 = horner(c.Fp, Q, 2, C, chi, eta=ETA0, n=n)
        eh, omh = g_mul(chi, pih, C * (v2 + e2), U)
        eh += n * ETA0
        omh = [x + ETA0 for x in omh]
        hbar = C * (v2 + e2) + eh
        eg, omg = g_addf(omh, Fr(1), 1 + hbar, U, 1 + hbar + sum(omh[1:]))
        er, omr1 = g_mul(chi, omg, C * (1 + hbar + eg), U)
        er += n * ETA0
        omr = [max(x + ETA0, y) for x, y in zip(omr1, chi)]
        Pb = (er + C * (eg + eh + C * e2) + max(C ** (Q + 1) / (Q + 1), Fr(1, 2 ** (c.B + 13)) * C) / (1 - C)
              + Ecc / (1 - C))
        ey, _ = g_add(piy, omr, ell + Pb, U)
        return up(ey + Pb)


def egroups(c, etop):
    """(e_low, e_high, m, d') from the exponent etop down: one e for each m >= 1, one degree d' for m = 0."""
    out, last = [], None
    for e in range(etop, -c.B - 3, -1):
        m, dp = degree(c, e, S, D)
        if m == 0 and last is not None and last[2] == 0 and last[3] == dp:
            last[0] = e
        else:
            last = [e, e, m, dp]
            out.append(last)
    return out


def main():
    global CONTROL
    CONTROL = 'control' in sys.argv[1:]
    gop.ROUND_BITS = 300
    gop.VECSUM_MIN = False
    n = N
    un = U ** n
    L = Log(n)
    c = L.c
    # the split of l by k
    yh0 = 1 / (2 * c.Lam)
    y0max = yh0 * (1 + U)
    lk_plus = (y0max + L.Ec) / (1 - L.Es)
    lk_minus = (yh0 / (1 + U) * (1 - U) - L.Ec) / (1 + L.Es)
    E0 = L.E(Fr(0))
    eps = (Fr(0), None)
    phi = (Fr(0), None)
    count = 0

    def ratio(val, ell, tag):
        nonlocal eps
        if val / ell > eps[0]:
            eps = (val / ell, tag)

    # k = 0
    for e_lo, e_hi, m, dp in egroups(c, -2):
        cbar = Fr(2) ** (e_hi + 1)
        a = Fr(2) ** e_lo * (1 - Fr(1, 2 ** 46)) * (1 - U) / (1 + U)
        if dp == 1:
            a = Fr(0)
        top = min(cbar, y0max)
        l_minus = max(Fr(0), (a - L.Ec) / (1 + L.Es))
        l_plus = (top + L.Ec) / (1 - L.Es)
        for sign in (1, -1):
            tag = (0, e_lo, e_hi, m, dp, sign)
            if l_minus < Fr(1, 2 ** 60):
                b = top if top <= E0 else None
                at0 = L.calE(Fr(0), 0, sign, m, dp, a, b, cbar)
                at2 = L.calE(l_plus, 0, sign, m, dp, a, b, cbar)
                count += 2
                if at0 > phi[0]:
                    phi = (at0, tag)
                ratio(at2 - at0, l_plus, tag + ('slope',))
            else:
                for ell in (l_minus, l_plus):
                    ratio(L.calE(ell, 0, sign, m, dp, a, None, cbar), ell, tag + (float(ell),))
                    count += 1
    # k != 0: the ranges of |r| at l = X, which contain those of every l
    alphaX, dstarX, rmaxX = L.reduction(X)
    rtop = rmaxX + dstarX
    etop = -1
    while Fr(2) ** etop > rtop:
        etop -= 1
    for e_lo, e_hi, m, dp in egroups(c, etop):
        cbar = Fr(2) ** (e_hi + 1)
        hi = min(cbar, rtop)
        tail = sum(lemma38b(c, alphaX, hi + dstarX)[1][1:])
        lo = max(Fr(0), Fr(2) ** e_lo * (1 - Fr(1, 2 ** 46)) - 2 * tail)
        if dp == 1:
            lo = Fr(0)
        if hi <= Fr(1, 2 ** 12) or lo <= 0:
            ivs = [(lo, hi)]
        else:
            r4 = float(hi / lo) ** 0.25
            pts = [lo] + [Fr(float(lo) * r4 ** i) for i in range(1, 4)] + [hi]
            ivs = list(zip(pts[:-1], pts[1:]))
        for a, b in ivs:
            for sign in (1, -1):
                for ell in (lk_minus, Fr(1), Fr(4), X):
                    val = L.calE(ell, 1, sign, m, dp, a, b, cbar)
                    count += 1
                    ratio(val, ell, (1, e_lo, e_hi, m, dp, sign, float(ell), float(a), float(b)))
    got = float(eps[0] / un)
    print(f'{count} evaluations')
    print(f'eps_ln / u^8 = {got:.6f}, at (k != 0, e_low, e_high, m, d\', sign of r, l, a, b) = {eps[1]}')
    print(f'log2 Phi = {lg(phi[0]):.4f}, at (k != 0, e_low, e_high, m, d\', sign of r) = {phi[1]}')
    ok = got <= 9.926 and abs(got - 9.925819) <= 1.01e-6 and -509.09 <= lg(phi[0]) <= -509.07
    print(f'the paper has 9.926 and 2^-509 (Theorem 42), 9.925819 and 2^-509.08 (explog_consts.txt): '
          f'{"ok" if ok else "DIFFERS"}')
    print('PASS' if ok else 'FAIL')
    return 0 if ok or CONTROL else 1


if __name__ == '__main__':
    sys.exit(main())
