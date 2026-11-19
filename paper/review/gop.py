#!/usr/bin/env python3
"""Lemmas 11 and 13 and Theorems 14, 19 and 27 of expansion-error-bounds.pdf as functions on rationals.

Written from the text of the appendix at commit 187ce44, without reading constants.py, div_consts.py,
sqrt_consts.py, acc_bound.py, sloppy_consts.py, trig_consts.py or explog_consts.py. It is the shared base of the
recomputations in this folder (thm30_sloppy.py, thm35_trig.py, thm40_exp.py, thm42_log.py); lem43_lnb.py stands alone.

Every value is a fractions.Fraction. Where ROUND_BITS is set, the quotients and each operation's results are
rounded up to that many significant bits, which keeps upper bounds: every formula is nondecreasing in them.

    python3 gop.py          # checks against Table IV, Theorem 19 and Theorem 21, prints PASS
    python3 gop.py control  # the same checks with Q of MUL lowered by one, must print FAIL (exit 0)
"""
import sys
from fractions import Fraction as Fr
from math import comb, log2

ROUND_BITS = None  # None: exact rationals
MUTATE_Q = 0       # control: subtracted from MUL's count of roundings
VECSUM_MIN = True  # False: V_j is VecSum's second bound alone (the convex form of Theorem 42's proof)


def up(x):
    """x rounded up to ROUND_BITS significant bits (x itself when exact, zero or negative)."""
    if ROUND_BITS is None or x <= 0:
        return x
    num, den = x.numerator, x.denominator
    shift = ROUND_BITS - (num.bit_length() - den.bit_length())
    if shift >= 0:
        return Fr(-((-num << shift) // den), 1 << shift)
    return Fr(-((-num) // (den << -shift)) << -shift)


def down(x):
    """x rounded down to ROUND_BITS significant bits."""
    if ROUND_BITS is None or x <= 0:
        return x
    num, den = x.numerator, x.denominator
    shift = ROUND_BITS - (num.bit_length() - den.bit_length())
    if shift >= 0:
        return Fr((num << shift) // den, 1 << shift)
    return Fr((num // (den << -shift)) << -shift)


def lg(x):
    """log2 of a positive rational, as a float."""
    num, den = x.numerator, x.denominator
    s = max(num.bit_length(), den.bit_length()) - 900
    if s > 0:
        num >>= s
        den >>= s
    return log2(num) - log2(den)


def lemma11(A, T, Q, u):
    """Lemma 11: the level bounds X_0..X_n and the rounding total R from the inputs A, the counts T and Q."""
    n = len(A) - 1
    X = []
    D = A[0]
    for m in range(n):
        X.append(up(D / (1 - T[m] * u)))
        C = up(T[m] * u * D / (1 - T[m] * u))
        D = A[m + 1] + C
    X.append(up(D / (1 - Q * u)))
    return X, Q * u * X[n]


def vecsum_bounds(X, u):
    """V_1..V_n of Lemma 13 from the level bounds X (Theorem 9(d)); returned with V[0] unused."""
    n = len(X) - 1
    us = u / (1 + u)
    sigma = [0] * (n + 2)
    for m in range(n, -1, -1):
        sigma[m] = sigma[m + 1] + X[m]
    V = [None]
    for j in range(1, n + 1):
        second = up(us * (1 + u) ** (n - j) * sigma[j - 1])
        V.append(min(X[j - 1], second) if VECSUM_MIN else second)
    return V, sigma


def finish13(X, R, Delta, Zbar, u):
    """Lemma 13 (a) and (b) from the level bounds: the error bound and the part bounds of the result."""
    n = len(X) - 1
    V, _ = vecsum_bounds(X, u)
    err = u ** n * Zbar + (1 + u ** n) * (R + Delta) + sum((u ** n + u ** (n + 1 - j)) * V[j] for j in range(1, n + 1))
    W = [sum(V[j] for j in range(k + 1, n + 1)) for k in range(n + 1)]
    parts = [(1 + u) * (Zbar + R + Delta + W[1])]
    for i in range(1, n):
        parts.append((1 + u) * (u * parts[i - 1] + W[i]))
    return up(err), [up(x) for x in parts]


def g_mul(alpha, beta, Zbar, u):
    """G_MUL(alpha, beta; Zbar) of Lemma 13."""
    n = len(alpha)
    P = [0] * (2 * n - 1)
    for i in range(n):
        for j in range(n):
            P[i + j] += alpha[i] * beta[j]
    A = [(1 + u) * P[m] + (u * P[m - 1] if m else 0) for m in range(n)]
    A.append(P[n] + u * P[n - 1] if n < len(P) else u * P[n - 1])
    T = [m * (m + 1) for m in range(n)]
    Q = n * n + n - 1 - MUTATE_Q
    Delta = sum(P[m] for m in range(n + 1, 2 * n - 1))
    X, R = lemma11(A, T, Q, u)
    return finish13(X, R, Delta, Zbar, u)


def _g_lambda(lam, Zbar, u):
    n = len(lam)
    A = [(1 + u) * lam[m] + (u * lam[m - 1] if m else 0) for m in range(n)]
    A.append(u * lam[n - 1])
    X, R = lemma11(A, list(range(n)), n - 1, u)
    return finish13(X, R, 0, Zbar, u)


def g_add(alpha, beta, Zbar, u, lam=None):
    """G_ADD(alpha, beta; Zbar[, lambda]) of Lemma 13, lambda_m = alpha_m + beta_m by default."""
    if lam is None:
        lam = [a + b for a, b in zip(alpha, beta)]
    return _g_lambda(lam, Zbar, u)


def g_mulf(alpha, beta0, Zbar, u):
    """G_MULF(alpha, beta_0; Zbar) of Lemma 13, lambda_m = alpha_m beta_0."""
    return _g_lambda([a * beta0 for a in alpha], Zbar, u)


def g_addf(alpha, beta0, Zbar, u, lam0=None):
    """G_ADDF(alpha, beta_0; Zbar[, lambda_0]) of Lemma 13, lambda_0 = alpha_0 + beta_0 by default."""
    n = len(alpha)
    if lam0 is None:
        lam0 = alpha[0] + beta0
    eps = [u * lam0]
    X = [(1 + u) * lam0]
    for m in range(1, n):
        X.append((1 + u) * (alpha[m] + eps[m - 1]))
        eps.append(u * (alpha[m] + eps[m - 1]))
    X.append(eps[n - 1])
    return finish13(X, 0, 0, Zbar, u)


def theorem14(op, n, theta, u):
    """Theorem 14: L_0..L_n, R and Delta (in units of u^(n+1) M), and Theorem 15's kappa."""
    th = Fr(theta)
    if op == 'addf':
        L = [(1 + u) * sum(th ** k for k in range(m + 1)) for m in range(n)]
        L.append(sum(th ** k for k in range(n)))
        R = Delta = Fr(0)
    else:
        if op == 'mul':
            alpha = [1 + u] + [(1 + u) * (m + 1) + m / th for m in range(1, n)] + [n - 1 + n / th]
            T = [m * (m + 1) for m in range(n)]
            Q = n * n + n - 1 - MUTATE_Q
            Delta = sum((2 * n - 1 - k) * th ** k * u ** (k - n - 1) for k in range(n + 1, 2 * n - 1))
        else:
            alpha = [1 + u] + [1 + u + 1 / th] * (n - 1) + [1 / th]
            T = list(range(n))
            Q = n - 1
            Delta = Fr(0)
        d = alpha[0]
        L = []
        for m in range(n):
            L.append(th ** m * d / (1 - T[m] * u))
            d = alpha[m + 1] + T[m] * d / (th * (1 - T[m] * u))
        L.append(th ** n * d / (1 - Q * u))
        R = Q * L[n]
    beta_n = (1 + u) ** (n - 1) / (1 - u)
    kappa = 2 * beta_n * sum(L) + (1 + u ** n) * (R + Delta)
    return L, R, Delta, kappa


def kappa_div(n, theta, u):
    """Theorem 19's kappa_DIV at H(theta)."""
    rho = theta * u
    us = u / (1 + u)
    P = [rho ** i for i in range(n)]
    qbar = [(1 + u) * P[0]]
    eps_sum = 0
    for _ in range(n):
        q = qbar[-1]
        G = [u * (P[0] + q)] + [P[i] + (1 + u) * rho ** i * q for i in range(1, n)]
        A = [(1 + u) * G[0]]
        A += [(1 + u) * G[m] + u * G[m - 1] + u * rho ** (m - 1) * q for m in range(1, n)]
        A.append(u * G[n - 1] + u * rho ** (n - 1) * q)
        X, R = lemma11(A, [2 * m for m in range(n)], 2 * n - 1, u)
        V, sigma = vecsum_bounds(X, u)
        V[0] = (1 + u) ** n * sigma[0]
        eps_sum += R + min(us ** (n - k) * V[k] + sum(us ** (n + 1 - j) * V[j] for j in range(k + 1, n + 1))
                           for k in range(n + 1))
        W = [sum(V[j] for j in range(i + 1, n + 1)) for i in range(n + 1)]
        P = [up((1 + u) * (sigma[0] + W[1]))]
        for i in range(1, n):
            P.append(up((1 + u) * (u * P[i - 1] + W[i])))
        qbar.append((1 + u) * P[0])
    Theta = sum(P[1:]) + u * P[0] + qbar[n] * rho / (1 - rho) + eps_sum
    Vq, _ = vecsum_bounds(qbar, u)
    Xi = sum((u ** n + u ** (n + 1 - j)) * Vq[j] for j in range(1, n + 1))
    return up(((1 + u ** n) * Theta * (1 - rho) / (1 - 2 * rho) + Xi) / ((1 - 2 * rho) * u ** (n + 1)))


def abar(n, theta, u):
    """The part bounds of (2), relative to the value, for an expansion on H(theta)."""
    rho = theta * u
    return [rho ** i * (1 - rho) / (1 - 2 * rho) for i in range(n)]


def acc_bound(n, K, tau, eprod, u):
    """Theorem 27: (E_lev, Phi) in units of W, from the tau_l and K; the second term is
    (1 + u^n)(E_lev + eprod) + Phi."""
    beta = 1 / (1 - (n + 1) * K * u)

    def rising(k, r):
        out = 1
        for i in range(r):
            out *= k + i
        return out

    S = [beta * sum(comb(m, l) * tau[l] * (beta * u) ** (m - l) * rising(K, m - l) for l in range(m + 1))
         for m in range(n + 1)]
    elev = sum(comb(n + 1, l) * tau[l] * (beta * u) ** (n + 1 - l) * rising(K, n + 1 - l) for l in range(n + 1))
    parts = [S[0]] + [Fr(0)] * (n - 1)
    phi = None
    for l in range(1, n + 1):
        Zbar = sum(S[: l + 1])
        if l == n:
            # the last ADDF: Phi is Lemma 13(a) without its first two terms
            lam0 = parts[0] + S[l]
            eps = [u * lam0]
            X = [(1 + u) * lam0]
            for m in range(1, n):
                X.append((1 + u) * (parts[m] + eps[m - 1]))
                eps.append(u * (parts[m] + eps[m - 1]))
            X.append(eps[n - 1])
            V, _ = vecsum_bounds(X, u)
            phi = sum((u ** n + u ** (n + 1 - j)) * V[j] for j in range(1, n + 1))
        _, parts = g_addf(parts, S[l], Zbar, u, parts[0] + S[l])
    return elev, phi


def sqrt_newton(n, J, theta, u):
    """Theorem 21's delta_J, used here only as a check of the G_OP against sqrt_consts.txt."""
    ab = abar(n, theta, u)
    hb = [a / 2 for a in ab]
    rho = theta * u
    E = max((1 + 2 * u) / (1 - rho) - 1, 1 - (1 - 2 * u) * (1 - 2 * rho) / (1 - rho))
    pi = [1 + E] + [Fr(0)] * (n - 1)
    half = Fr(1, 2)
    for _ in range(J):
        em, mu = g_mul(pi, pi, (1 + E) ** 2, u)
        eg, gam = g_mul(hb, mu, ((1 + E) ** 2 + em) / 2, u)
        zeta = half * (2 * E + E * E) + half * em + eg
        ec, chi = g_addf(gam, half, zeta, u, zeta + sum(gam[1:]))
        ed, dl = g_mul(chi, pi, (zeta + ec) * (1 + E), u)
        er, pi2 = g_add(pi, dl, (1 + E) + (zeta + ec) * (1 + E) + ed, u)
        E = up(Fr(3, 2) * E * E + half * E ** 3 + (1 + E) * (half * em + eg + ec) + ed + er)
        pi = pi2
    ez, _ = g_mul(pi, ab, 1 + E, u)
    return E + ez


def main():
    global ROUND_BITS, MUTATE_Q
    if 'control' in sys.argv[1:]:
        MUTATE_Q = 1
    u = Fr(1, 2 ** 53)
    ok = True

    def check(name, got, want, tol):
        nonlocal ok
        good = abs(got - want) <= tol
        ok &= good
        print(f'{name}: {got:.9f}, the paper has {want}: {"ok" if good else "DIFFERS"}')

    for op, want1, want2 in (('mul', 36.41, 37.92), ('add', 17.97, 19.99), ('mulf', 17.97, 19.99),
                             ('addf', 6.46, 10.56)):
        for theta, want in ((1, want1), (2, want2)):
            check(f'Table IV log2 kappa {op} theta={theta}', lg(theorem14(op, 8, theta, u)[3]), want, 0.0051)
    check('Theorem 19 log2 kappa_DIV theta=1', lg(kappa_div(8, 1, u)), 25.9, 0.051)
    check('Theorem 19 log2 kappa_DIV theta=2', lg(kappa_div(8, 2, u)), 27.47, 0.0051)
    ROUND_BITS = 300
    for theta, want in ((1, 3.0000198), (2, 3.0000319)):
        check(f'Theorem 21 delta_4/u^8 theta={theta}', float(sqrt_newton(8, 4, theta, u) / u ** 8), want, 1.01e-7)
    print('PASS' if ok else 'FAIL')
    return 0 if ok or MUTATE_Q else 1


if __name__ == '__main__':
    sys.exit(main())
