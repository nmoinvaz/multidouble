"""Hill climbing for the largest relative error |Z - x| / |Z| of ADD (fpemu.od_add) on operands satisfying H(2), with
Z = a + b exact. Starts from b near -a and mutates one part at a time (a few units in its last place, or a new
exponent). usage: add_climb.py p n restarts steps seed"""
import random
import sys
from fractions import Fraction as Q

import acc as A
F = A.F


def ladder(x, p):
    u2 = Q(2, 2 ** p)
    a0 = abs(A.val(x[0]))
    return a0 > 0 and all(abs(A.val(x[i])) <= u2 ** i * a0 for i in range(1, len(x)))


def rel_err(a, b):
    Z = sum(A.val(t) for t in a) + sum(A.val(t) for t in b)
    if Z == 0:
        return Q(-1), Z
    x = F.od_add(a, b)
    return abs(Z - sum(A.val(t) for t in x)) / abs(Z), Z


def mutate(rng, v, i, p):
    m, e = v
    r = rng.random()
    if m == 0 or r < 0.2:
        mm = rng.randrange(1 << (p - 1), 1 << p) * rng.choice((1, -1))
        return F.rnd(mm, -i * (p - 1) - rng.randrange(0, 4))
    if r < 0.6:
        mm = m + rng.randrange(-8, 9)
        return F.rnd(mm, e) if mm and abs(mm) < 1 << p else v
    # rescale the significand to p bits and change its low bits
    sh = p - abs(m).bit_length()
    mm = (m << sh) + rng.randrange(-8, 9)
    return F.rnd(mm, e - sh) if mm and abs(mm) < 1 << p else v


def climb(p, n, restarts, steps, seed):
    F.set_p(p)
    rng = random.Random(seed)
    u = Q(1, 2 ** p)
    best = (Q(0), None)
    for _ in range(restarts):
        a = [(rng.randrange(1 << (p - 1), 1 << p), 0)]
        for i in range(1, n):
            a.append(F.rnd(rng.randrange(1 << (p - 1), 1 << p) * rng.choice((1, -1)), -i * (p - 1) - 1))
        b = [F.neg(t) for t in a]
        cur, _ = rel_err(a, b)
        for _ in range(steps):
            side = rng.randrange(2)
            i = rng.randrange(n)
            aa, bb = list(a), list(b)
            tgt = aa if side == 0 else bb
            tgt[i] = mutate(rng, tgt[i], i, p)
            if not (ladder(aa, p) and ladder(bb, p)):
                continue
            r, Z = rel_err(aa, bb)
            if r >= cur:
                a, b, cur = aa, bb, r
        if cur > best[0]:
            Z = sum(A.val(t) for t in a) + sum(A.val(t) for t in b)
            M = abs(A.val(a[0])) + abs(A.val(b[0]))
            best = (cur, (a, b, Z / M))
    rel, (a, b, zm) = best
    print(f'p={p} n={n}: largest |Z - x|/|Z| = {float(rel):.4g} = {float(rel / u ** n):.4g} u^n, |Z|/M = '
          f'{float(zm):.3g} = {float(zm / u ** (n + 1)):.3g} u^(n+1)')
    print('  a =', [str(A.val(t)) for t in a])
    print('  b =', [str(A.val(t)) for t in b])
    print('  x =', [str(A.val(t)) for t in F.od_add(a, b)])
    return best


if __name__ == '__main__':
    climb(*map(int, sys.argv[1:6]))
