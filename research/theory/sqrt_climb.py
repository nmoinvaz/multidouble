"""Hill climbing for the largest error of SQRT_{n,J} (fpemu.od_sqrt) in units of u^n sqrt(x), on inputs on H(2)
whose parts are small odd multiples of powers of two near the top of each part's range (ties are likely there).
Exact arithmetic: the error is bracketed with an integer square root at 4 n p bits.
usage: sqrt_climb.py p n J restarts steps seed"""
import random
import sys
from fractions import Fraction as Q
from math import isqrt

import acc as A
F = A.F


def sqrt_err(x, p, n, J):
    """|sqrt(X) - sum(result)| / (u^n sqrt(X)), with X the exact value of x, to about 2^-40 relative"""
    X = sum(A.val(t) for t in x)
    r = F.od_sqrt(x, J=J)
    R = sum(A.val(t) for t in r)
    # sqrt(X) to 4np bits: floor(sqrt(X 2^(2k))) / 2^k
    k = 4 * n * p + 64
    num, den = X.numerator, X.denominator
    s = Q(isqrt(num * 2 ** (2 * k) // den), 2 ** k)
    u = Q(1, 2 ** p)
    return float(abs(s - R) / (u ** n * s))


def rand_part(rng, p, i):
    """a part of size about (2u)^i, a small odd multiple of a power of two, or zero"""
    if rng.random() < 0.15:
        return F.PZ
    m = rng.choice((1, 3, 5, 7, 2 ** p - 1, 2 ** p - 3, 2 ** (p - 1) + 1)) * rng.choice((1, -1))
    e = -i * p + rng.choice((-2, -1, 0, 0, 1)) - (m.bit_length() - 1 if abs(m) > 8 else 0)
    return F.rnd(m, e)


def ladder(x, p):
    u2 = Q(2, 2 ** p)
    a0 = abs(A.val(x[0]))
    return a0 > 0 and all(abs(A.val(x[i])) <= u2 ** i * a0 for i in range(1, len(x)))


def climb(p, n, J, restarts, steps, seed):
    F.set_p(p)
    rng = random.Random(seed)
    best = (0.0, None)
    for _ in range(restarts):
        x = [F.rnd(rng.choice((1, 3, 5, 2 ** p - 1, 2 ** p + 1 - 2)), rng.choice((0, 1, -p + 1, -p + 2)))]
        x += [rand_part(rng, p, i) for i in range(1, n)]
        if not ladder(x, p):
            continue
        cur = sqrt_err(x, p, n, J)
        for _ in range(steps):
            y = list(x)
            i = rng.randrange(1, n)
            y[i] = rand_part(rng, p, i)
            if not ladder(y, p):
                continue
            e = sqrt_err(y, p, n, J)
            if e >= cur:
                x, cur = y, e
        if cur > best[0]:
            best = (cur, x)
    print(f'p={p} n={n} J={J}: largest error = {best[0]:.6f} u^n sqrt(x) at x =', [str(A.val(t)) for t in best[1]])
    return best


if __name__ == '__main__':
    climb(*map(int, sys.argv[1:7]))
