"""ADD of two expansions on the ladder H(2) whose exact sum is zero: does it return zero? a is random; b = -a', where
a' is another n-part split of a's value on the ladder (parts moved between neighbors). Random search.
usage: add_cancel.py p n trials seed     prints the first inputs found with a nonzero result, and counts."""
import random
import sys
from fractions import Fraction as Q

import acc as A
F = A.F


def tofl(v, p):
    """v as a p-bit float if representable, else None"""
    if v == 0:
        return F.PZ
    num, den = v.numerator, v.denominator
    if den & (den - 1):
        return None
    e = -(den.bit_length() - 1)
    m = num
    while m % 2 == 0:
        m //= 2
        e += 1
    return (m, e) if abs(m) < (1 << p) else None


def ladder(x, p):
    u2 = Q(2, 2 ** p)
    a0 = abs(A.val(x[0]))
    return all(abs(A.val(x[i])) <= u2 ** i * a0 for i in range(1, len(x)))


PERTURB = False
best = [Q(0)]


def run(p, n, trials, seed):
    F.set_p(p)
    best[:] = [Q(0)]
    rng = random.Random(seed)
    found = 0
    tested = 0
    for _ in range(trials):
        top = rng.randrange(1 << (p - 1), 1 << p)
        a = [(top, 0)]
        for i in range(1, n):
            m = rng.randrange(1 << (p - 1), 1 << p) * rng.choice((1, -1))
            a.append(F.rnd(m, -i * (p - 1) - rng.choice((0, 1, 1, 2))))
        if not ladder(a, p):
            continue
        av = [A.val(x) for x in a]
        # a' = a with value d_i moved from part i+1 to part i
        ap = list(av)
        for i in range(n - 1):
            g = Q(2) ** (-(i + 1) * (p - 1) - rng.choice((0, 1, 2, 3, 4)))
            d = g * rng.randrange(-4, 5)
            ap[i] += d
            ap[i + 1] -= d
        bp = [tofl(-v, p) for v in ap]
        if any(x is None for x in bp) or not ladder(bp, p):
            continue
        # perturb the last part of b by a few units of its last place, so that a + b is small but not zero
        if PERTURB:
            m, e = bp[n - 1]
            if m == 0:
                continue
            m2 = m + rng.choice((-3, -2, -1, 1, 2, 3))
            if m2 == 0 or abs(m2) >= 1 << p:
                continue
            bp[n - 1] = F.rnd(m2, e)
        tested += 1
        x = F.od_add(a, bp)
        Z = sum(av) + sum(A.val(t) for t in bp)
        if PERTURB:
            rel = abs(Z - sum(A.val(t) for t in x)) / abs(Z)
            M = abs(av[0]) + abs(A.val(bp[0]))
            if rel > best[0]:
                best[:] = [rel, a, bp, x, Z / M]
            continue
        if any(t[0] != 0 for t in x):
            found += 1
            if found <= 3:
                print('a =', [str(v) for v in av])
                print('b =', [str(A.val(t)) for t in bp])
                print('ADD(a, b) =', [str(A.val(t)) for t in x], ' exact sum =', sum(av) + sum(A.val(t) for t in bp))
    if PERTURB and len(best) > 1:
        rel, a, bp, x, zm = best
        u = Q(1, 2 ** p)
        print(f'p={p} n={n}: {tested} pairs; largest |Z - x|/|Z| = {float(rel):.4g} = {float(rel / u ** n):.4g} u^n, '
              f'with |Z|/M = {float(zm):.3g} = {float(zm / u ** (n + 1)):.3g} u^(n+1)')
        print('  a =', [str(A.val(t)) for t in a], ' b =', [str(A.val(t)) for t in bp], ' x =', [str(A.val(t)) for t in x])
        return rel
    print(f'p={p} n={n}: {tested} pairs with a + b = 0 tested, {found} nonzero results')
    return found


if __name__ == '__main__':
    p, n, trials, seed = map(int, sys.argv[1:5])
    PERTURB = len(sys.argv) > 5 and sys.argv[5] == 'perturb'
    run(p, n, trials, seed)
