#!/usr/bin/env python3
"""Lemma 43's constants eps_w and eta_b, recomputed in exact rationals.

Written from the statement and proof of Lemma 43 at commit 187ce44, without reading explog_consts.py or its output.
It shares no code with the paper's scripts. ln 2 and ln mu are enclosed by their artanh series with the remainder
added, and every other value is an exact rational.

    python3 lem43_lnb.py           # prints eps_w / u and eta_b / u, compared with the paper's, then PASS
    python3 lem43_lnb.py control   # the series cut at nine terms in the remainder: must print FAIL (exit 0)
"""
import sys
from fractions import Fraction as Fr
from math import isqrt

P = 53
U = Fr(1, 2 ** P)
US = U / (1 + U)


def rn(x):
    """x > 0 rounded to nearest, ties to even, at precision 53."""
    e = x.numerator.bit_length() - x.denominator.bit_length()
    if Fr(2) ** e > x:
        e -= 1
    scale = Fr(2) ** (P - 1 - e)
    m = x * scale
    f = m.numerator // m.denominator
    rem = m - f
    if rem > Fr(1, 2) or (rem == Fr(1, 2) and f % 2):
        f += 1
    return f / scale


def ln_bounds(m, bits=400):
    """Rationals below and above ln m = 2 artanh((m - 1)/(m + 1)), for m > 1."""
    s = (m - 1) / (m + 1)
    z = s * s
    total, t, k = Fr(0), s, 0
    while True:
        total += 2 * t / (2 * k + 1)
        k += 1
        t *= z
        rem = 2 * t / (2 * k + 1) / (1 - z)
        if rem < Fr(1, 2 ** bits):
            return total, total + rem


def main():
    control = 'control' in sys.argv[1:]
    # mu = RN(sqrt 2): the nearest 53-bit number, from the integer square root of 2^105
    f = isqrt(2 << 104)
    if (2 * f + 1) ** 2 < (2 << 106):
        f += 1
    mu = Fr(f, 2 ** 52)
    assert (2 * f - 1) ** 2 < (2 << 106) < (2 * f + 1) ** 2
    sbar = (mu - 1) / (mu + 1)
    assert (2 - mu) / (2 + mu) < sbar
    theta_z = (1 + 2 * U) ** 2 * (1 + US) - 1
    zbar = sbar ** 2 * (1 + theta_z)

    def V(j):
        return sum(zbar ** (i - j) / (2 * i + 1) for i in range(j, 10))

    vt = US
    for j in range(8, -1, -1):
        vt = (1 + (zbar * V(j + 1) * vt + (US / (2 * j + 1) if j > 0 else 0)) / V(j)) * (1 + US) - 1
    theta_V = theta_z * zbar / (2 * (1 - zbar))
    terms = 9 if control else 10
    theta_inf = zbar ** terms / ((2 * terms + 1) * (1 - zbar))
    eps_w = (1 + 2 * U) * (1 + vt) * (1 + theta_V) * (1 + US) / (1 - theta_inf) - 1
    ln2_lo, ln2_hi = ln_bounds(Fr(2))
    lnmu_lo, lnmu_hi = ln_bounds(mu)
    cL = rn(ln2_lo)
    assert cL == rn(ln2_hi)
    dcl = max(abs(cL - ln2_lo), abs(cL - ln2_hi))
    eta_b = US + (1 + US) * (dcl + eps_w * lnmu_hi) / (ln2_lo - lnmu_hi)
    ew, eb = float(eps_w / U), float(eta_b / U)
    def dec_up(x, k=6):
        q = -(-x.numerator * 10 ** k // x.denominator)
        return f'{q // 10 ** k}.{q % 10 ** k:0{k}d}'

    print(f'eps_w / u = {dec_up(eps_w / U)} (rounded up), the paper has 4.312')
    print(f'eta_b / u = {dec_up(eta_b / U)} (rounded up), the paper has 5.915')
    ok = 0 <= 4.312 - ew <= 1e-3 and 0 <= 5.915 - eb <= 1e-3
    print('PASS' if ok else 'FAIL')
    return 0 if ok or control else 1


if __name__ == '__main__':
    sys.exit(main())
