#!/usr/bin/env python3
"""Theorem 30's constants, recomputed in exact rationals.

Written from the text of the appendix "The sloppy multiply" at commit 187ce44, without reading sloppy_consts.py or
its output. It shares gop.py with the other recomputations of this folder and no code with the paper's scripts.

    python3 thm30_sloppy.py          # prints the constants and their comparison with the paper's, then PASS
    python3 thm30_sloppy.py control  # Q = n^2 - 1 in place of n^2: must print FAIL (exit 0)
"""
import sys
from fractions import Fraction as Fr

from gop import acc_bound, lg, theorem14


def sloppy(n, theta, u, q_off=0):
    """R_s, Delta_n u, and L_0..L_(n-1) of Theorem 30."""
    th = Fr(theta)
    rho = th * u
    alpha = [1 + u] + [(1 + u) * (m + 1) + m / th for m in range(1, n - 1)]
    T = [m * (m + 1) for m in range(n - 1)]
    Q = n * n - q_off
    d = alpha[0]
    L = []
    gamma = None
    for m in range(n - 1):
        L.append(th ** m * d / (1 - T[m] * u))
        gamma = T[m] * d / (th * (1 - T[m] * u))
        if m + 1 < n - 1:
            d = alpha[m + 1] + gamma
    d_last = n + (n - 1) / th + (n - 1) * rho + gamma
    L.append(th ** (n - 1) * d_last / (1 - Q * u))
    Delta = sum((2 * n - 1 - k) * th ** k * u ** (k - n - 1) for k in range(n + 1, 2 * n - 1))
    return Q * L[n - 1], Delta * u, L


def main():
    control = 'control' in sys.argv[1:]
    u = Fr(1, 2 ** 53)
    n = 8
    ok = True

    def check(name, got, want, tol):
        nonlocal ok
        good = 0 <= want - got <= tol
        ok &= good
        print(f'{name}: {got:.6f}, the paper has {want}: {"ok" if good else "DIFFERS"}')

    for theta, want, want_d in ((1, 30.4117, -50.41), (2, 31.9242, -41.41)):
        Rs, Du, L = sloppy(n, theta, u, 1 if control else 0)
        check(f'theta={theta}: log2(R_s + Delta_8 u)', lg(Rs + Du), want, 1.01e-4)
        check(f'theta={theta}: log2(Delta_8 u)', lg(Du), want_d, 1.01e-2)
        # the levels below n - 1 are MUL's (Theorem 14)
        Lmul = theorem14('mul', n, theta, u)[0]
        assert L[: n - 1] == Lmul[: n - 1]
    Rs, Du, L = sloppy(n, 2, u, 1 if control else 0)
    check('theta=2: log2 L_7', lg(L[7]), 25.93, 1.01e-2)
    rho = 2 * u
    tau = [max(L[l] * u ** l, rho ** l) for l in range(n)] + [Fr(0)]
    eprod = (Rs + Du) * u ** n
    for K in (1, 4, 16, 64):
        elev, phi = acc_bound(n, K, tau, eprod, u)
        second = ((1 + u ** n) * (elev + eprod) + phi) / u ** n
        check(f'theta=2, K={K}: log2 of the second term of (c) / u^8 W', lg(second), 31.9242, 1.01e-4)
        if K == 64:
            check('theta=2, K=64: log2 E_lev / u^8 W', lg(elev / u ** n), 2.6833, 1.01e-4)
    print('PASS' if ok else 'FAIL')
    return 0 if ok or control else 1


if __name__ == '__main__':
    sys.exit(main())
