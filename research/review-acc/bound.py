"""Theorem thm:acc's bound in exact rationals, from the definitions of accumulator.tex and the appendix only.

second_term(n, p, theta, K, kind) = ((1 + u^n)(E_lev + E_prod) + Phi) / (u^n W), with W = 1, where kind is 'prod'
(all terms ADDPROD), 'addx' (all ADDX) or 'mixed'. Phi follows Lemma g along FINISH; the choices the theorem leaves
open (lambda_0, Zbar, whether the known zero parts of r^(l) are used) are parameters, see phi().
Run: python3 bound.py
"""
from fractions import Fraction as Fr
from math import comb, log2

import sys


def rising(k, r):
    v = 1
    for i in range(r):
        v *= k + i
    return v


def t2_mul(n, u, th):
    """Theorem t2 for MUL: L_0..L_n, R, Delta"""
    al = [1 + u] + [(1 + u) * (m + 1) + Fr(m) / th for m in range(1, n)] + [n - 1 + Fr(n) / th]
    T = [m * (m + 1) for m in range(n)]
    Q = n * n + n - 1
    d = [al[0]]
    ell = []
    for m in range(n):
        g = T[m] * d[m] / (th * (1 - T[m] * u))
        ell.append(d[m] / (1 - T[m] * u))
        d.append(al[m + 1] + g)
    ell.append(d[n] / (1 - Q * u))
    L = [th ** m * ell[m] for m in range(n + 1)]
    R = Q * th ** n * d[n] / (1 - Q * u)
    Dl = sum((2 * n - 1 - k) * th ** k * u ** (k - n - 1) for k in range(n + 1, 2 * n - 1))
    return L, R, Dl


def t2_addf(n, u, th):
    L = [(1 + u) * sum(th ** k for k in range(m + 1)) for m in range(n)] + [sum(th ** k for k in range(n))]
    return L, Fr(0), Fr(0)


def kappa(n, u, L, R, Dl):
    bn = (1 + u) ** (n - 1) / (1 - u)
    return 2 * bn * sum(L) + (1 + u ** n) * (R + Dl)


def taus(n, u, th, kind):
    rho = th * u
    if kind == 'addx':
        return [rho ** l for l in range(n)] + [Fr(0)], Fr(0), Fr(0)
    L, R, Dl = t2_mul(n, u, th)
    tau = [max(L[l] * u ** l, rho ** l) for l in range(n + 1)]
    return tau, R, Dl


def S_levels(n, u, K, tau, W=1):
    beta = 1 / (1 - (n + 1) * K * u)
    return [beta * W * sum(comb(m, l) * tau[l] * (beta * u) ** (m - l) * rising(K, m - l) for l in range(m + 1))
            for m in range(n + 1)], beta


def E_lev(n, u, K, tau, W=1):
    beta = 1 / (1 - (n + 1) * K * u)
    return W * sum(comb(n + 1, l) * tau[l] * (beta * u) ** (n + 1 - l) * rising(K, n + 1 - l) for l in range(n + 1))


def g_addf(n, u, alpha, b0, lam0, Zbar):
    """Lemma g for ADDF: (V_1..V_n, part bounds of the result)"""
    us = u / (1 + u)
    eps = [u * lam0]
    X = [(1 + u) * lam0]
    for m in range(1, n):
        X.append((1 + u) * (alpha[m] + eps[m - 1]))
        eps.append(u * (alpha[m] + eps[m - 1]))
    X.append(eps[n - 1])
    sig = [sum(X[l:]) for l in range(n + 1)]
    V = [None] + [min(X[j - 1], us * (1 + u) ** (n - j) * sig[j - 1]) for j in range(1, n + 1)]
    Wk = [sum(V[j] for j in range(k + 1, n + 1)) for k in range(n + 1)]
    x = [(1 + u) * (Zbar + Wk[1])]
    for i in range(1, n):
        x.append((1 + u) * (u * x[i - 1] + Wk[i]))
    return V, x


def phi(n, u, S, zero_parts=False, zbar='min'):
    """Phi of Theorem thm:acc. alpha starts at (S_0, 0, ...); ADDF l takes a = r^(l-1), b = s_l with |b| <= S_l,
    lambda_0 = alpha_0 + S_l, Zbar = sum_{m<=l} S_m ('sum'), sum alpha + S_l ('alpha') or the smaller ('min').
    zero_parts: use that r^(l) has nonzero parts only at 0..l (proved in the theorem's proof)."""
    alpha = [S[0]] + [Fr(0)] * (n - 1)
    V = None
    for l in range(1, n + 1):
        z1 = sum(S[:l + 1])
        z2 = sum(alpha) + S[l]
        Zb = {'sum': z1, 'alpha': z2, 'min': min(z1, z2)}[zbar]
        V, x = g_addf(n, u, alpha, S[l], alpha[0] + S[l], Zb)
        alpha = x
        if zero_parts:
            alpha = [alpha[i] if i <= l else Fr(0) for i in range(n)]
    return sum((u ** n + u ** (n + 1 - j)) * V[j] for j in range(1, n + 1))


def second_term(n, p, th, K, kind='prod', **kw):
    """((1 + u^n)(E_lev + E_prod) + Phi) / (u^n W), W = 1"""
    u = Fr(1, 2 ** p)
    th = Fr(th)
    tau, R, Dl = taus(n, u, th, kind)
    S, beta = S_levels(n, u, K, tau)
    El = E_lev(n, u, K, tau)
    Ep = (R + Dl) * u ** (n + 1)
    Ph = phi(n, u, S, **kw)
    return ((1 + u ** n) * (El + Ep) + Ph) / u ** n, dict(E_lev=El / u ** n, E_prod=Ep / u ** n, Phi=Ph / u ** n)


def full_bound(n, p, th, K, Zabs, W, kind='prod', **kw):
    """the theorem's bound u^n |Z| + second term, for given |Z| and W (Fractions)"""
    u = Fr(1, 2 ** p)
    c, _ = second_term(n, p, th, K, kind, **kw)
    return u ** n * Zabs + c * u ** n * W


def lg(x):
    return log2(float(x)) if x > 0 else float('-inf')


def crossover(n, p, th, kind, level, **kw):
    """largest K with second_term <= level (monotone in K)"""
    lo, hi = 1, 2
    while second_term(n, p, th, hi, kind, **kw)[0] <= level:
        lo, hi = hi, hi * 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if second_term(n, p, th, mid, kind, **kw)[0] <= level:
            lo = mid
        else:
            hi = mid
    return lo


if __name__ == '__main__':
    n, p = 8, 53
    u = Fr(1, 2 ** p)
    print('# cross-check of the appendix constants (Table tab:kappa), n = 8, p = 53')
    for th in (1, 2):
        L, R, Dl = t2_mul(n, u, Fr(th))
        print(f'MUL  theta={th}: kappa = 2^{lg(kappa(n, u, L, R, Dl)):.2f}  R = 2^{lg(R):.2f}  Delta = {float(Dl):.4g}'
              f'  L = ' + ' '.join(f'2^{lg(x):.2f}' for x in L))
        L, R, Dl = t2_addf(n, u, Fr(th))
        print(f'ADDF theta={th}: kappa = 2^{lg(kappa(n, u, L, R, Dl)):.2f}')
    print('\n# second term / (u^8 W), products, theta = 2, Phi variants')
    print(f"{'K':>6} {'min,nozero':>12} {'sum':>12} {'alpha':>12} {'min,zero':>12}   E_lev  E_prod  Phi (min,nozero)")
    for K in (1, 4, 16, 32, 50, 51, 64, 128, 1024, 2048):
        c, parts = second_term(n, p, 2, K)
        c2, _ = second_term(n, p, 2, K, zbar='sum')
        c3, _ = second_term(n, p, 2, K, zbar='alpha')
        c4, _ = second_term(n, p, 2, K, zero_parts=True)
        print(f'{K:>6} {lg(c):>12.4f} {lg(c2):>12.4f} {lg(c3):>12.4f} {lg(c4):>12.4f}   '
              f"2^{lg(parts['E_lev']):.2f} 2^{lg(parts['E_prod']):.2f} 2^{lg(parts['Phi']):.2f}")
    L, R, Dl = t2_mul(n, u, Fr(2))
    print(f'Theorem t3 MUL theta=2: kappa u = 2^{lg(kappa(n, u, L, R, Dl) * u):.4f}')
    print('\n# crossovers: largest K with second term <= 1/8 and <= 1')
    for kind, th in (('prod', 2), ('prod', 1), ('addx', 2), ('addx', 1)):
        print(f'{kind:5} theta={th}: 1/8 -> K = {crossover(n, p, th, kind, Fr(1, 8))}, 1 -> K = '
              f'{crossover(n, p, th, kind, Fr(1))}')
    print('\n# the leading term tau_0 beta^9 u K^(9) vs the full E_lev, addx theta=1, K = 2048')
    K = 2048
    tau, _, _ = taus(n, u, Fr(1), 'addx')
    beta = 1 / (1 - (n + 1) * K * u)
    lead = tau[0] * beta ** 9 * u * rising(K, 9)
    print(f'lead = 2^{lg(lead):.3f}  E_lev/(u^8 W) = 2^{lg(E_lev(n, u, K, tau) / u ** n):.3f}')
    c, _ = second_term(n, p, 1, K, 'addx')
    print(f'second term addx theta=1 K=2048: 2^{lg(c):.3f}')
