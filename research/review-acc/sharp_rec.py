"""A sharper valid form of Lemma lem:acc's level bounds: the self-referential carries handled deposit by deposit,
S_m(k) <= (tau_m W + G_{m-1}(k) + G_m(k-1)) / (1 - (m+1)u), G_m(k) = G_m(k-1) + (m+1) u S_m(k), the same counts
(m+1 two-sums or roundings per level and deposit) as the lemma's proof. E_lev <= G_n(K). W = 1.
python3 sharp_rec.py p n K [theta] [kind]
"""
from fractions import Fraction as Fr
from math import log2
import sys

import bound as B


def rec(n, p, K, th=1, kind='addx'):
    u = Fr(1, 2 ** p)
    tau, R, Dl = B.taus(n, u, Fr(th), kind)
    G = [Fr(0)] * (n + 1)
    for k in range(1, K + 1):
        Gm1 = Fr(0)
        for m in range(n + 1):
            S = (tau[m] + Gm1 + G[m]) / (1 - (m + 1) * u)
            G[m] = G[m] + (m + 1) * u * S
            Gm1 = G[m]
    return G[n]


if __name__ == '__main__':
    p, n, K = (int(v) for v in sys.argv[1:4])
    th = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    kind = sys.argv[5] if len(sys.argv) > 5 else 'addx'
    u = Fr(1, 2 ** p)
    tau, _, _ = B.taus(n, u, Fr(th), kind)
    el = B.E_lev(n, u, K, tau)
    sh = rec(n, p, K, th, kind)
    print(f'p={p} n={n} K={K} theta={th} {kind}: Lemma E_lev = {float(el / u ** n):.6g} u^n W, '
          f'deposit-wise recursion = {float(sh / u ** n):.6g} u^n W, ratio {float(sh / el):.4f}')
