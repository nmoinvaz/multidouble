"""Greedy adversary for the level accumulator (acc.py): K positive n-part expansions on the ladder H(2), each chosen
among C random candidates to maximize a score after its deposit. Prints, for k = 1..K, the error of finish() in
units of u^n W (W = sum of the leading parts) and of u^n |Z|.

usage: acc_greedy.py p n K C seed score [front]
score: 'err' (|Z - levels|, the accumulated level-n roundings, then level sizes), 'grow' (the level sizes, in
units of u^m, then the error). front = 1 puts a leading part of size 1 first and the rest at size ~u."""
import math
import random
import sys
from fractions import Fraction as Q

import acc as A
F = A.F


def flt(m, e):
    return F.rnd(m, e) if m else F.PZ


def rand_exp(rng, p, e0, n, small):
    """a positive n-part expansion on H(2): a_0 = m 2^e0, |a_i| <= (2u)^i a_0"""
    top = rng.randrange(1 << (p - 1), 1 << p)
    a = [flt(top, e0)]
    a0 = A.val(a[0])
    for i in range(1, n):
        if rng.random() < 0.05:
            a.append(F.PZ)
            continue
        m = rng.randrange(1 << (p - 1), 1 << p) * rng.choice((1, -1))
        d = rng.choice((0, 1, 1, 2, 3)) if not small else rng.choice((0, 1))
        x = flt(m, e0 - i * (p - 1) - d)
        if abs(A.val(x)) > (Q(2) / 2 ** p) ** i * a0:
            x = flt(m, e0 - i * (p - 1) - d - 1)
        a.append(x)
    return a


def run(p, n, K, C, seed, score, front, log=True):
    F.set_p(p)
    rng = random.Random(seed)
    u = Q(1, 2 ** p)
    s = A.fresh(n)
    Z = Q(0)
    W = Q(0)
    worst = 0.0
    rows = []
    for k in range(1, K + 1):
        best = None
        for c in range(C):
            if front and k == 1:
                a = rand_exp(rng, p, 1 - p, n, True)
            elif front:
                a = rand_exp(rng, p, 1 - 2 * p + rng.choice((0, 0, -1)), n, True)
            else:
                a = rand_exp(rng, p, 1 - p + rng.choice((0, 0, -1)), n, True)
            t = list(s)
            A.acc_levels(t, a)
            Za = Z + sum(A.val(x) for x in a)
            lev = sum(A.val(x) for x in t)
            e = abs(Za - lev)
            size = sum(abs(A.val(t[m])) / u ** m for m in range(n + 1))
            key = (e, size) if score == 'err' else (size, e)
            if best is None or key > best[0]:
                best = (key, a, t, Za)
        _, a, s, Z = best
        W += abs(A.val(a[0]))
        x = A.finish(s)
        err = abs(Z - sum(A.val(y) for y in x))
        r1 = float(err / (u ** n * W))
        rows.append((k, r1, float(err / (u ** n * abs(Z))) if Z else float('inf')))
        worst = max(worst, r1)
        if log and (k & (k - 1) == 0 or k == K):
            lv = [float(abs(A.val(s[m])) / (u ** m * W)) for m in range(n + 1)]
            print(f'k={k:4d} err/(u^n W)={r1:9.4f} err/(u^n|Z|)={rows[-1][2]:9.4f} levels/(u^m W)='
                  + ' '.join(f'{v:.3g}' for v in lv), flush=True)
    return worst, rows


if __name__ == '__main__':
    p, n, K, C, seed = map(int, sys.argv[1:6])
    score = sys.argv[6]
    front = len(sys.argv) > 7 and sys.argv[7] == '1'
    w, _ = run(p, n, K, C, seed, score, front)
    # the largest measured error, rounded up at the digits shown
    print(f'p={p} n={n} K={K} C={C} seed={seed} score={score} front={front}: max err/(u^n W) = '
          f'{math.ceil(float(w) * 1e6) / 1e6:.6f}')
