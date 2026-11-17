"""Relative error of ADD when both operands are fixed points of R_n (as the crate's results are): a = R_n(random
n-part value), b = R_n of a split of -(a + d) with d tiny, so that a + b = -d. Random search.
usage: add_canon.py p n trials seed"""
import random
import sys
from fractions import Fraction as Q

import acc as A
from add_zero import tofl
F = A.F


def run(p, n, trials, seed):
    F.set_p(p)
    rng = random.Random(seed)
    u = Q(1, 2 ** p)
    worst = (Q(0), None)
    tested = 0
    for _ in range(trials):
        # a random value near 1 with n p-bit parts, renormalized
        raw = [(rng.randrange(1 << (p - 1), 1 << p), 1 - p)]
        for i in range(1, n):
            raw.append(F.rnd(rng.randrange(1 << (p - 1), 1 << p) * rng.choice((1, -1)), 1 - p - i * p - rng.choice((0, 1, 2))))
        a = F.renorm(raw, n)
        av = sum(A.val(t) for t in a)
        # d tiny, of size about u^k, k = n - 1 .. n + 2, with two parts
        k = rng.randrange(n - 1, n + 3)
        d = Q(rng.randrange(1, 1 << p) * rng.choice((1, -1)), 2 ** p) * u ** k
        d += Q(rng.randrange(1, 1 << p) * rng.choice((1, -1)), 2 ** p) * u ** (k + 1) * Q(1, 2 ** rng.randrange(0, 4))
        bv = -(av + d)
        # b: the renormalization of a random n-term split of bv (n terms, so R_n is exact)
        terms = []
        r = bv
        for i in range(n - 1):
            num, den = r.numerator, r.denominator
            if num == 0:
                terms.append(F.PZ)
                continue
            x = F.rnd(num, -(den.bit_length() - 1))
            m, e = x
            x = F.rnd(m + rng.choice((-2, -1, 0, 0, 1, 2)), e) if m + 2 < (1 << p) and abs(m) > 2 else x
            terms.append(x)
            r -= A.val(x)
        num, den = r.numerator, r.denominator
        if r != 0 and (abs(num) >= (1 << p) or den & (den - 1)):
            continue
        terms.append(F.rnd(num, -(den.bit_length() - 1)) if r != 0 else F.PZ)
        b = F.renorm(terms, n)
        if sum(A.val(t) for t in b) != bv or F.renorm(a, n) != a or F.renorm(b, n) != b:
            continue
        tested += 1
        Z = av + bv
        x = F.od_add(a, b)
        rel = abs(Z - sum(A.val(t) for t in x)) / abs(Z)
        if rel > worst[0]:
            worst = (rel, (a, b, x, Z))
    rel, ex = worst
    print(f'p={p} n={n}: {tested} pairs of R_n fixed points; largest |Z - x|/|Z| = {float(rel):.4g} = '
          f'{float(rel / u ** n):.4g} u^n = {float(rel / u):.4g} u')
    if ex:
        a, b, x, Z = ex
        print('  a =', [str(A.val(t)) for t in a], ' b =', [str(A.val(t)) for t in b], ' x =',
              [str(A.val(t)) for t in x], ' Z =', Z)


if __name__ == '__main__':
    run(*map(int, sys.argv[1:5]))
