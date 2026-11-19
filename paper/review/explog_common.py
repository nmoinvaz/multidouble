#!/usr/bin/env python3
"""Lemmas 33, 38 and 39 of expansion-error-bounds.pdf, and the constants of EXP and LOG, as functions on rationals.

Written from the text of the appendix "The exponential and the logarithm" at commit 187ce44, without reading
explog_consts.py, explog_bits.py, their outputs or the earlier recomputation of this folder. Used by thm40_exp.py and
thm42_log.py; it shares gop.py with the other recomputations and no code with the paper's scripts.

Bounds are rationals rounded up to gop.ROUND_BITS bits (lower bounds down), exp and ln 2 by their series with the
remainder added.
"""
from fractions import Fraction as Fr
from math import factorial

import gop
from gop import down, g_add, g_mul, g_mulf, up

P = 53
U = Fr(1, 2 ** P)
ETA0 = Fr(1, 2 ** 1075)
KBAR = 1075


def rn(x):
    """x rounded to nearest, ties to even, at precision 53 with an unbounded exponent range."""
    if x == 0:
        return Fr(0)
    s = -1 if x < 0 else 1
    x = abs(x)
    e = x.numerator.bit_length() - x.denominator.bit_length()
    if Fr(2) ** e > x:
        e -= 1
    scale = Fr(2) ** (P - 1 - e)
    m = x * scale
    f = m.numerator // m.denominator
    rem = m - f
    if rem > Fr(1, 2) or (rem == Fr(1, 2) and f % 2):
        f += 1
    return s * f / scale


def greedy(x, n):
    """The greedy n-part rounding of x: its signed parts and the remainder x - their sum."""
    parts = []
    for _ in range(n):
        y = rn(x)
        parts.append(y)
        x -= y
    return parts, x


def exp_up(x):
    """A rational at least e^x."""
    if x < 0:
        return up(1 / exp_down(-x))
    x = up(x)
    if x >= 1:
        return up(exp_up(x / 2) ** 2)
    s, t, k = Fr(1), Fr(1), 0
    while t > Fr(1, 2 ** 400) * s or k < 4:
        k += 1
        t = t * x / k
        s += t
    return up(s + t * x / (k + 1) / (1 - x / (k + 2)))


def exp_down(x):
    """A positive rational at most e^x."""
    if x < 0:
        return down(1 / exp_up(-x))
    x = down(x)
    if x >= 1:
        return down(exp_down(x / 2) ** 2)
    s, t, k = Fr(1), Fr(1), 0
    while t > Fr(1, 2 ** 400) * s or k < 4:
        k += 1
        t = t * x / k
        s += t
    return down(s)


def expm1_up(x):
    """A rational at least e^x - 1, for x >= 0, with the rounding relative to the result."""
    x = up(x)
    if x >= 1:
        return up(exp_up(x) - 1)
    s, t, k = Fr(0), Fr(1), 0
    while k < 4 or t > Fr(1, 2 ** 400) * s:
        k += 1
        t = t * x / k
        s += t
    return up(s + t * x / (k + 1) / (1 - x / (k + 2)))


def one_minus_exp_up(y):
    """A rational at least 1 - e^(-y), for y >= 0, with the rounding relative to the result."""
    y = up(y)
    if y >= 1:
        return up(1 - exp_down(-y))
    s, t, k = Fr(0), Fr(1), 0
    while k < 5 or t > Fr(1, 2 ** 400) * s or k % 2 == 0:
        k += 1
        t = t * y / k
        s += t if k % 2 else -t
    return up(s)


def expm2_up(x):
    """A rational at least e^x - 1 - x, for 0 <= x < 1, with the rounding relative to the result."""
    x = up(x)
    s, t, k = Fr(0), x, 1
    while k < 5 or t > Fr(1, 2 ** 400) * s:
        k += 1
        t = t * x / k
        s += t
    return up(s + t * x / (k + 1) / (1 - x / (k + 2)))


def ln2_bounds(bits=1400):
    """Rationals below and above ln 2 = 2 artanh(1/3), closer than 2^-bits."""
    s, k = Fr(0), 0
    while True:
        s += Fr(2, (2 * k + 1) * 3 ** (2 * k + 1))
        k += 1
        rem = Fr(2, (2 * k + 1) * 3 ** (2 * k + 1)) * Fr(9, 8)
        if rem < Fr(1, 2 ** bits):
            return s, s + rem


class Consts:
    """c_h, c_l, eta_l, Lambda and the Taylor coefficients of EXP and LOG at n parts."""

    def __init__(self, n):
        self.n = n
        lo, hi = ln2_bounds()
        self.ln2_lo, self.ln2_hi = lo, hi
        ch = [Fr(round(v * 2 ** 42), 2 ** 42) for v in (lo, hi)]
        assert ch[0] == ch[1]
        self.ch = ch[0]
        g = [greedy(v - self.ch, n) for v in (lo, hi)]
        assert g[0][0] == g[1][0]
        self.cl = g[0][0]
        self.cl_abs = [abs(x) for x in self.cl]
        self.eta_l = max(abs(g[0][1]), abs(g[1][1]))
        self.dch = max(abs(lo - self.ch), abs(hi - self.ch))
        lam = [rn(1 / v) for v in (lo, hi)]
        assert lam[0] == lam[1]
        self.Lam = lam[0]
        self.dLam = max(abs(self.Lam - 1 / lo), abs(self.Lam - 1 / hi))
        cL = [greedy(v, 2) for v in (lo, hi)]
        assert cL[0][0] == cL[1][0]
        self.eta_L = max(abs(cL[0][1]), abs(cL[1][1]))
        self.B = P * n + 12
        self._F, self._Fp = {}, {}

    def F(self, j):
        """(1/j!, the magnitudes of its greedy parts, phi_j)."""
        if j not in self._F:
            v = Fr(1, factorial(j))
            parts, rem = greedy(v, self.n)
            self._F[j] = (v, [abs(x) for x in parts], abs(rem))
        return self._F[j]

    def Fp(self, i):
        """(1/i, the magnitudes of the greedy parts of (-1)^(i+1)/i, phi'_i)."""
        if i not in self._Fp:
            v = Fr(1, i)
            parts, rem = greedy(v, self.n)
            self._Fp[i] = (v, [abs(x) for x in parts], abs(rem))
        return self._Fp[i]


def lemma38_setup(c, X, gamma):
    """beta, rbar_max and alpha_0 of Lemma 38."""
    beta = X * (c.dLam + U * c.Lam)
    rmax = (Fr(1, 2) + beta) * c.ln2_hi + gamma
    alpha0 = rmax + gamma + KBAR * c.dch
    assert alpha0 < Fr(1, 2)
    return beta, up(rmax), up(alpha0)


def lemma38b(c, alpha, rbar):
    """Lemma 38(b): delta and the part bounds pi^r, for the part bounds alpha of x' and |r_e| <= rbar."""
    e1, mu = g_mulf(c.cl_abs, Fr(KBAR), KBAR * abs(sum(c.cl)), U)
    e2, pir = g_add(alpha, mu, rbar + KBAR * c.eta_l + e1, U)
    return up(e1 + e2 + KBAR * c.eta_l), pir


def horner(coef, d, k0, zbar, piz, eta=0, n=None):
    """Lemma 33 with eps_z = 0 for the coefficients coef(k) = (v, parts, phi), k0 <= k <= d, and the exact sums'
    bounds vb[k]: e_k0 and pi^(k0). eta is the loss per part of each product's scaling back."""
    vb = {d: coef(d)[0]}
    for k in range(d - 1, k0 - 1, -1):
        vb[k] = coef(k)[0] + zbar * vb[k + 1]
    _, parts, phi = coef(d)
    e, pi = phi, parts
    for k in range(d - 1, k0 - 1, -1):
        _, parts, phi = coef(k)
        ep, mu = g_mul(piz, pi, zbar * (vb[k + 1] + e), U)
        if eta:
            ep += n * eta
            mu = [x + eta for x in mu]
        D = zbar * e + phi + ep
        ea, pi = g_add(parts, mu, vb[k] + D, U)
        e = up(D + ea)
    return e, pi, vb[k0]


def lemma39(c, n, a, b, pi, m, dprime, cbar, sign, convex=False):
    """Lemma 39: E_m, psi_m and tbar_m. With convex, the forms of Theorem 42's proof: no minima with cbar, and
    tbar_j = 2^j b' for r <= 0."""
    sc = Fr(1, 2 ** m)
    lost = 1 if m > 0 else 0
    if convex:
        bp = sc * b + n * ETA0 * lost
        pip = [sc * x + ETA0 * lost for x in pi]
    else:
        bp = sc * min(b, cbar) + n * ETA0 * lost
        pip = [sc * min(x, cbar) + ETA0 * lost for x in pi]

    def tbar(j):
        if sign >= 0:
            return expm1_up(2 ** j * bp)
        if convex:
            return 2 ** j * bp
        return one_minus_exp_up(2 ** j * bp)

    def gfac(j):
        if sign >= 0:
            return 1 + tbar(j)
        return exp_up(-(2 ** j) * a * sc)

    if dprime == 1:
        E = up(bp ** 2 / (2 * (1 - bp / 3)))
        psi = pip
    else:
        e2, piq, v2 = horner(c.F, dprime, 2, bp, pip)
        e1, om1 = g_mul(pip, piq, bp * (v2 + e2), U)
        e11, om = g_mul(pip, om1, bp * (bp * (v2 + e2) + e1), U)
        etr = bp ** (dprime + 1) / (factorial(dprime + 1) * (1 - bp / (dprime + 2)))
        Eminus = e11 + bp * (e1 + bp * e2) + etr + 2 * n * ETA0 * lost
        e111, psim = g_add(pip, om, tbar(0) + Eminus, U)
        E = up(Eminus + e111 + n * ETA0)
        psi = [x + ETA0 for x in psim]
    for j in range(m):
        tj = tbar(j)
        em, nu = g_mul(psi, psi, (tj + E) ** 2, U)
        es, psi = g_add([2 * x for x in psi], nu, tbar(j + 1) + 2 * E * (1 + tj) + E * E + em, U)
        E = up(2 * gfac(j) * E + E * E + em + es)
    return E, psi, tbar(m)


def degree(c, e, s, d):
    """m and d' of steps (2) and (3) of EXP for the exponent e of U."""
    m = max(0, e + s + 1)
    ep = e - m
    if ep >= -1 - c.B:
        return m, min(d, -(-c.B // (-ep - 1)))
    return m, 1
