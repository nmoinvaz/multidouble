"""Theorem thm:acc (expansion-error-bounds-accumulator.tex): the error bound of the level accumulator (OdAcc generalized to n
parts) after K deposits, in exact rationals.

    |Z - finish| <= u^n |Z| + kappa_acc(K) u^(n+1) W

with W = sum of mu_k (|a_0| for add, |a_0 b_0| for add_prod) and
    kappa_acc u^(n+1) = (1 + u^n)(E_lev + E_prod) + Phi_fin,
    E_lev   = sum_{l=0}^{n} C(n+1, l) tau_l (Gamma u)^(n+1-l) K^(n+1-l rising) W,   Gamma = 1/(1 - (n+1) K u) (beta below),
    E_prod  = (R_n + Delta_n) u^(n+1) W for add_prod (Theorem thm:t2(b) of the appendix), 0 for add,
    Phi_fin = the second-order term of the last od + f64 of finish (Lemma lem:g(a) of the appendix, from the level bounds
              S_m(K) = Gamma sum_{l<=m} C(m, l) tau_l (Gamma u)^(m-l) K^(m-l rising) W).
tau_l bounds a deposit's level l in units of mu_k: (theta u)^l for add, L_l u^l (Theorem thm:t2(a)) for add_prod.

usage: acc_bound.py p n theta mode K...   (mode add or prod); prints kappa_acc u, E_lev / (u^n W) and the parts,
       each rounded up at the digits shown (rounding.py).
       acc_bound.py p n theta mode cross t...   prints the largest K whose second term is at most t u^n W.
"""
import os
import sys
from fractions import Fraction as Fr
from math import comb

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from constants import consts  # noqa: E402
from rounding import lg2_up  # noqa: E402
from sqrt_consts import op_bounds  # noqa: E402


def rising(k, r):
    out = 1
    for i in range(r):
        out *= k + i
    return out


def acc_bound(n, p, theta, K, mode, drop_power=0):
    """bound terms in units of W. drop_power = 1 is the control: each K^(r rising) replaced by K^(r-1 rising)."""
    u = Fr(1, 2 ** p)
    assert (n + 1) * K * u < 1, 'needs (n+1) K u < 1'
    beta = 1 / (1 - (n + 1) * K * u)
    if mode == 'add':
        tau = [(Fr(theta) * u) ** l for l in range(n)] + [Fr(0)]
        eprod = Fr(0)
    else:
        c = consts('mul', n, theta, u)
        tau = [c['L'][l] * u ** l for l in range(n + 1)]
        eprod = (c['R'] + c['drop']) * u ** (n + 1)
    rk = lambda r: rising(K, max(r - drop_power, 0))
    S = [beta * sum(comb(m, l) * tau[l] * (beta * u) ** (m - l) * rk(m - l) for l in range(m + 1))
         for m in range(n + 1)]
    elev = sum(comb(n + 1, l) * tau[l] * (beta * u) ** (n + 1 - l) * rk(n + 1 - l) for l in range(n + 1))
    al = [S[0]] + [Fr(0)] * (n - 1)
    phi = None
    for l in range(1, n + 1):
        zb = sum(S[:l + 1])
        eps, parts, _ = op_bounds('add_f', n, u, al, [S[l]], zb, lam=[al[0] + S[l]])
        al = parts
        phi = eps - u ** n * zb
    total = (1 + u ** n) * (elev + eprod) + phi
    return dict(u=u, S=S, elev=elev, eprod=eprod, phi=phi, total=total)


def crossover(n, p, theta, mode, t):
    """the largest K whose second term is at most t u^n W (the bound grows with K)"""
    K = 1
    while acc_bound(n, p, theta, K + 1, mode)['total'] <= t * Fr(1, 2 ** p) ** n:
        K += 1
    return K


if __name__ == '__main__':
    p, n, theta = map(int, sys.argv[1:4])
    mode = sys.argv[4]
    if sys.argv[5] == 'cross':
        ts = [Fr(t) for t in sys.argv[6:]]
        print(f'{mode} theta {theta} : largest K with second term <= t u^{n} W:',
              [(float(t), crossover(n, p, theta, mode, t)) for t in ts])
        sys.exit(0)
    for K in map(int, sys.argv[5:]):
        b = acc_bound(n, p, theta, K, mode)
        u = b['u']
        un = u ** n
        print(f'p={p} n={n} theta={theta} {mode} K={K}: second term / (u^n W) = 2^{lg2_up(b["total"] / un)}'
              f'  (E_lev 2^{lg2_up(b["elev"] / un)}, E_prod '
              + (f'2^{lg2_up(b["eprod"] / un)}' if b['eprod'] else '0')
              + f', Phi_fin 2^{lg2_up(b["phi"] / un)}); u^(n+1) K^(n+1 rising) / u^n = '
              f'2^{lg2_up(u * rising(K, n + 1))}')
