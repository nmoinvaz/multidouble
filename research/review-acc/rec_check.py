"""Checks the counts behind Lemma lem:acc and sharp_rec.py's deposit-wise recursion on actual runs: per deposit k and
level m, the actual sum G_m(k) of |carries out| (m < n) or |rounding errors| (m = n), and the largest |s_m| so far,
against the recursion's G_m(k) and S_m(k) and the lemma's S_m(k).

python3 rec_check.py p n K [half]     terms: construct.py's greedy for (p, n, K), then 20 random positive sums
'half' halves the recursion's bounds: the check must then fire.
"""
from fractions import Fraction as Fr
import random
import sys

import bound as B
import construct as C
import reffp as F
from gen import operand


def run(terms, n, p, K, th, kind, half):
    u = Fr(1, 2 ** p)
    tau, _, _ = B.taus(n, u, Fr(th), kind)
    W = sum(abs(F.frac(a[0])) for a in terms)
    s = [F.ZERO] * (n + 1)
    G = [Fr(0)] * (n + 1)  # actual
    Smax = [Fr(0)] * (n + 1)
    Gr = [Fr(0)] * (n + 1)  # recursion
    worst = [0.0, 0.0, 0.0]  # G/Grec, Smax/Srec, Smax/Slemma
    sc = Fr(1, 2) if half else Fr(1)
    for k, a in enumerate(terms, 1):
        Gm1 = Fr(0)
        Sr = []
        for m in range(n + 1):
            S = (tau[m] * W + Gm1 + Gr[m]) / (1 - (m + 1) * u)
            Gr[m] = Gr[m] + (m + 1) * u * S
            Gm1 = Gr[m]
            Sr.append(S)
        for l in range(n):
            e = a[l]
            for m in range(l, n):
                s[m], e = F.two_sum(s[m], e)
                G[m] += abs(F.frac(e))
                Smax[m] = max(Smax[m], abs(F.frac(s[m])))
            ex = F.frac(s[n]) + F.frac(e)
            s[n] = F.add(s[n], e)
            G[n] += abs(ex - F.frac(s[n]))
            Smax[n] = max(Smax[n], abs(F.frac(s[n])))
        SL, _ = B.S_levels(n, u, k, tau, W) if k == len(terms) else (None, None)
        for m in range(n + 1):
            if Gr[m]:
                worst[0] = max(worst[0], float(G[m] / (sc * Gr[m])))
            worst[1] = max(worst[1], float(Smax[m] / (sc * Sr[m])))
            if SL:
                worst[2] = max(worst[2], float(Smax[m] / SL[m]))
    return worst


def main():
    p, n, K = (int(v) for v in sys.argv[1:4])
    half = len(sys.argv) > 4 and sys.argv[4] == 'half'
    F.setp(p)
    sets = [('construction', C.build(p, n, K, log=False))]
    rng = random.Random(p * 100 + n)
    for i in range(20):
        sets.append((f'random {i}', [operand(rng, n, 1, rng.randrange(-2, 2), style='edge', sign=1)
                                     for _ in range(K)]))
    tot = [0.0, 0.0, 0.0]
    for name, ts in sets:
        w = run(ts, n, p, K, 1, 'addx', half)
        tot = [max(x, y) for x, y in zip(tot, w)]
    print(f'p={p} n={n} K={K} half={half}: max G/G_rec = {tot[0]:.4g}, max |s|/S_rec = {tot[1]:.4g}, '
          f'max |s|/S_lemma(K) = {tot[2]:.4g}')
    fired = tot[0] > 1 or tot[1] > 1 or tot[2] > 1
    if half:
        print('control fired' if fired else 'CONTROL DID NOT FIRE')
    elif fired:
        print('RECURSION EXCEEDED')
        sys.exit(1)


if __name__ == '__main__':
    main()
