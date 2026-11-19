#!/usr/bin/env python3
"""Theorem 35's constants C and C^T, recomputed in rational arithmetic rounded up.

Written from the text of the appendix "Sine, cosine and tangent" at commit 187ce44 (Lemmas 32 to 34, the paragraph
before Theorem 35 and its statement), without reading trig_consts.py or its output. It shares gop.py with the other
recomputations of this folder and no code with the paper's scripts. Every bucket of the reduced argument is
evaluated, not one per pair of series lengths.

    python3 thm35_trig.py            # n = 8 and the double-word functions, compared with the paper's, then PASS
    python3 thm35_trig.py all        # also n = 2, 4 and 12 (Remark 36)
    python3 thm35_trig.py control    # the sine series one term short: must print FAIL (exit 0)
"""
import sys
from fractions import Fraction as Fr
from math import factorial

import gop
from gop import abar, g_add, g_addf, g_mul, kappa_div, up

P = 53
U = Fr(1, 2 ** P)
SHORT = 0  # control: terms dropped from the sine series


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
    """The greedy n-part rounding of x: its parts, and |x - their sum|."""
    parts = []
    for _ in range(n):
        y = rn(x)
        parts.append(abs(y))
        x -= y
    return parts, abs(x)


def cos_minus(x):
    return 1 - x ** 2 / 2 + x ** 4 / 24 - x ** 6 / 720


def sin_minus(x):
    return x - x ** 3 / 6 + x ** 5 / 120 - x ** 7 / 5040


def sin_plus(x):
    return x - x ** 3 / 6 + x ** 5 / 120


class Ops:
    """The operations' bounds: Lemma 13's for n parts, or the double-word ones."""

    def __init__(self, n, dw=False):
        self.n, self.dw = n, dw
        self.un = U ** n
        if dw:
            self.e_mul = (4 * U ** 2 + U ** 3 / 2) / (1 + U) ** 2
            self.e_add = 3 * U ** 2 / (1 - 4 * U)
            self.e_addf = 2 * U ** 2
            self.e_div = 15 * U ** 2 + 56 * U ** 3
            self.ab = [Fr(1), Fr(0)]
        else:
            self.e_add = self.e_addf = self.un
            self.ab = abar(n, 2, U)

    def scale(self, parts, c):
        return [c * x for x in parts]

    def mul(self, a, b, Z):
        if self.dw:
            return up(self.e_mul * Z), a
        return g_mul(a, b, Z, U)

    def add(self, a, b, Z):
        if self.dw:
            return up(self.e_add * Z), a
        return g_add(a, b, Z, U)

    def addf(self, a, f, Z):
        if self.dw:
            return up(self.e_addf * Z), a
        return g_addf(a, f, Z, U)


def series_length(rb, n, cosine):
    K = 2
    while True:
        if cosine:
            good = rb ** (2 * K) / factorial(2 * K) <= Fr(1, 2 ** 10) * U ** n * (1 - rb ** 2 / 2)
        else:
            good = rb ** (2 * K) / factorial(2 * K + 1) <= Fr(1, 2 ** 10) * U ** n * (1 - rb ** 2 / 6)
        if good:
            return K
        K += 1


def root_up(x, i):
    """A rational at least x^(1/i)."""
    s = 160
    t = x * Fr(2) ** (i * s)
    v = -((-t.numerator) // t.denominator)
    lo, hi = 0, 1 << (v.bit_length() // i + 2)
    while lo < hi:
        mid = (lo + hi) // 2
        if mid ** i >= v:
            hi = mid
        else:
            lo = mid + 1
    return Fr(lo, 2 ** s)


def horner(ops, coef, K, ez, zbar, piz):
    """Lemma 33 for the coefficients coef(k), 1 <= k <= K - 1: E_1 and pi^(1)."""
    val, parts, phi = coef(K - 1)
    e, pi = phi, parts
    for k in range(K - 2, 0, -1):
        v_next = abs(coef(k + 1)[0])
        val, parts, phi = coef(k)
        ep, mu = ops.mul(piz, pi, (1 + ez) * zbar * (v_next + e))
        D = (1 + ez) * zbar * e + ez * zbar * v_next + phi + ep
        ea, pi = ops.add(parts, mu, abs(val) + D)
        e = up(D + ea)
    return e, pi


def bucket(ops, rb, coefs, coefc, div_cache):
    """delta_S, delta_C, delta_D and the bucket's C_j and C^T_j for the bound rb of |r|."""
    n, un, ab = ops.n, ops.un, ops.ab
    ez, zeta = ops.mul(ab, ab, Fr(1))
    zbar = rb ** 2
    piz = ops.scale(zeta, zbar)
    # SINR
    K = series_length(rb, n, False) - SHORT
    s1 = abs(coefs(1)[0])
    E1, pi1 = horner(ops, coefs, K, ez, zbar, piz)
    et, vth = ops.mul(zeta, pi1, (1 + ez) * (s1 + E1))
    Et = (1 + ez) * E1 + ez * s1 + et
    ew, om = ops.mul(ab, vth, s1 + Et)
    D = zbar * (Et + ew) + rb ** (2 * K) / factorial(2 * K + 1)
    ey, psis = ops.add(ab, ops.scale(om, zbar), 1 + D)
    ES = D + ey - ops.e_add
    dS = up(ops.e_add + ES / (1 - zbar / 6))
    # COSR
    Kc = series_length(rb, n, True)
    c1 = abs(coefc(1)[0])
    E1, pi1 = horner(ops, coefc, Kc, ez, zbar, piz)
    et, vth = ops.mul(zeta, pi1, (1 + ez) * (c1 + E1))
    Et = (1 + ez) * E1 + ez * c1 + et
    Dc = zbar * Et + rb ** (2 * Kc) / factorial(2 * Kc)
    ey, psic = ops.addf(ops.scale(vth, zbar), Fr(1), 1 + Dc)
    EC = Dc + ey - ops.e_addf
    dC = up(ops.e_addf + EC / cos_minus(rb))
    # the quotient
    if ops.dw:
        dD = ops.e_div
    else:
        lam_s = (1 - zbar / 6) * (1 - dS) - sum(psis[1:])
        lam_c = cos_minus(rb) * (1 - dC) - sum(psic[1:])
        theta = Fr(1)
        for i in range(1, n):
            theta = max(theta, root_up(psis[i] / lam_s, i) / U, root_up(psic[i] / lam_c, i) / U)
        theta = up(theta)
        assert theta * U <= Fr(1, 4)
        if theta not in div_cache:
            div_cache[theta] = kappa_div(n, theta, U)
        dD = un + div_cache[theta] * U ** (n + 1)
    return dS, dC, dD, K, Kc


def consts(dS, dC, dD, rb, un):
    eps = 1 + 2 * un
    Cj = eps * max(dS + eps * un, dC + eps * un * rb * sin_plus(rb) / cos_minus(rb))
    CT = eps * (max((1 + dS) * (1 + dD) / (1 - dC), (1 + dC) * (1 + dD) / (1 - dS)) - 1
                + eps * un * 2 * rb / sin_minus(2 * rb))
    return Cj, CT


def theorem35(n, dw=False):
    """(C, C^T) in units of u^n, and the largest over the buckets j >= 1 and j >= 5."""
    ops = Ops(n, dw)
    un = ops.un
    cache_s, cache_c, div_cache = {}, {}, {}

    def coefs(k):
        if k not in cache_s:
            v = Fr((-1) ** k, factorial(2 * k + 1))
            cache_s[k] = (v,) + greedy(v, n)
        return cache_s[k]

    def coefc(k):
        if k not in cache_c:
            v = Fr((-1) ** k, factorial(2 * k))
            cache_c[k] = (v,) + greedy(v, n)
        return cache_c[k]

    rmin = U ** (n // 2) * (1 + Fr(1, 2 ** 50))
    # the bucket |r_0| < u^(n/2) and the early returns for |x_0| < u^(n/2)
    dS = rmin ** 2 / (6 - rmin ** 2)
    dC = rmin ** 2 / (2 * cos_minus(rmin))
    dD = ops.e_div if dw else un + kappa_div(n, 2, U) * U ** (n + 1)
    C, CT = consts(dS, dC, dD, rmin, un)
    C = max(C, rmin ** 2 / (2 * cos_minus(rmin)))
    CT = max(CT, sin_plus(rmin) / cos_minus(rmin) / rmin - 1)
    by_from = {1: (Fr(0), Fr(0)), 5: (Fr(0), Fr(0))}
    worst = None
    for j in range(P * n // 2 - 1, -1, -1):
        rb = Fr(78541, 100000) if j == 0 else Fr(1, 2 ** j) * (1 + Fr(1, 2 ** 50))
        dS, dC, dD, K, Kc = bucket(ops, rb, coefs, coefc, div_cache)
        Cj, CTj = consts(dS, dC, dD, rb, un)
        for lo in by_from:
            if j >= lo:
                by_from[lo] = (max(by_from[lo][0], Cj), max(by_from[lo][1], CTj))
        if Cj > C:
            worst = (j, K, Kc, dS, dC)
        C, CT = max(C, Cj), max(CT, CTj)
    return C / un, CT / un, {lo: (a / un, b / un) for lo, (a, b) in by_from.items()}, worst


def main():
    global SHORT
    args = sys.argv[1:]
    control = 'control' in args
    if control:
        SHORT = 1
    gop.ROUND_BITS = 300
    ok = True

    def check(name, got, want):
        nonlocal ok
        good = abs(want - float(got)) <= 1.01e-6
        ok &= good
        print(f'{name}: {float(got):.9f}, the paper has {want}: {"ok" if good else "DIFFERS"}')

    C, CT, part, worst = theorem35(8)
    check('n = 8: C / u^8', C, 3.163167)
    check('n = 8: C^T / u^8', CT, 6.418351)
    j, K, Kc, dS, dC = worst
    print(f'  the largest C_j is that of bucket {j}, K_s = {K}, K_c = {Kc}')
    check('n = 8, |r_0| < 1/2: C / u^8', part[1][0], 2.175822)
    check('n = 8, |r_0| < 1/2: C^T / u^8', part[1][1], 4.800526)
    check('n = 8, |r_0| < 2^-5: C / u^8', part[5][0], 2.000705)
    check('n = 8, |r_0| < 2^-5: C^T / u^8', part[5][1], 4.002771)
    C, CT, _, _ = theorem35(2, dw=True)
    check('double word: C / u^2', C, 7.841411)
    check('double word: C^T / u^2', CT, 28.414065)
    if 'all' in args:
        for n, wc, wt in ((2, 3.168700, 6.452138), (4, 3.164154, 6.426154), (12, 3582.787311, 4929.367335)):
            C, CT, _, _ = theorem35(n)
            check(f'n = {n}: C / u^{n}', C, wc)
            check(f'n = {n}: C^T / u^{n}', CT, wt)
    print('PASS' if ok else 'FAIL')
    return 0 if ok or control else 1


if __name__ == '__main__':
    sys.exit(main())
