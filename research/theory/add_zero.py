"""Relative accuracy of ADD (fpemu.od_add) after cancellation, n = 3: a random search over operands built so that the
leading parts cancel exactly, level 1 rounds (t_1 != 0) and level 2 nearly cancels the rest. Records the largest
|Z - x| / |Z|, and inputs with Z != 0 and x = 0.
usage: add_zero.py p trials seed"""
import random
import sys
from fractions import Fraction as Q

import acc as A
F = A.F


def tofl(v):
    if v == 0:
        return F.PZ
    num, den = v.numerator, v.denominator
    sh = 0
    while den > 1:
        den //= 2
        sh -= 1
    return F.rnd(num, sh)


def rnd_q(v, p):
    """RN of a dyadic rational v to p bits"""
    return tofl(v)


def ladder(x, p):
    u2 = Q(2, 2 ** p)
    a0 = abs(A.val(x[0]))
    return a0 > 0 and all(abs(A.val(x[i])) <= u2 ** i * a0 for i in range(1, len(x)))


def ulpno(v, p):
    """largest |v_(i+1)| / ulp(v_i)"""
    w = 0
    for i in range(len(v) - 1):
        if v[i][0] == 0:
            break
        t = abs(v[i][0]).bit_length() - 1 + v[i][1]
        w = max(w, abs(A.val(v[i + 1])) / Q(2) ** (t - p + 1))
    return float(w)

LIM = None
RENORM = False


def run(p, trials, seed, n=3, show=2):
    F.set_p(p)
    rng = random.Random(seed)
    u = Q(1, 2 ** p)
    best = (Q(-1), None)
    zeros = 0
    tested = 0
    for _ in range(trials):
        a = [F.ONE]
        b = [tofl(-(1 - u * rng.randrange(1, 5)))]
        R = A.val(a[0]) + A.val(b[0])
        for i in range(1, n):
            if i < n - 1:
                ai = tofl(-Q(rng.randrange(1 << (p - 1), 1 << p), 2 ** p) * u ** i * rng.choice((1, 2)) * (1 if R > 0 else -1))
                bi = tofl(-R - A.val(ai) + Q(rng.randrange(-64, 65), 64) * u ** (i + 1) * rng.choice((1, 2, 4)))
            else:
                ai = tofl(-R + Q(rng.randrange(-64, 65), 64) * u ** (i + 1) * rng.choice((1, 2, 4, 8)))
                bi = tofl(Q(rng.randrange(1 << (p - 1), 1 << p), 2 ** p) * rng.choice((1, -1)) * u ** (i + rng.choice((1, 2, 3)))
                          * rng.choice((1, 2, 4)))
            a.append(ai)
            b.append(bi)
            R += A.val(ai) + A.val(bi)
        if not (ladder(a, p) and ladder(b, p)):
            continue
        if RENORM:
            a, b = F.renorm(a, n), F.renorm(b, n)
            if a[0][0] == 0 or b[0][0] == 0 or not (ladder(a, p) and ladder(b, p)):
                continue
        if LIM is not None and (ulpno(a, p) > LIM or ulpno(b, p) > LIM):
            continue
        tested += 1
        Z = sum(A.val(t) for t in a + b)
        if Z == 0:
            continue
        x = F.od_add(a, b)
        xs = sum(A.val(t) for t in x)
        rel = abs(Z - xs) / abs(Z)
        if xs == 0:
            zeros += 1
            if zeros <= show:
                print('x = 0 for Z =', Z, '=', float(Z / u ** 4), 'u^4:')
                print('  a =', [str(A.val(t)) for t in a])
                print('  b =', [str(A.val(t)) for t in b])
        if rel > best[0]:
            best = (rel, (a, b, x, Z))
    rel, (a, b, x, Z) = best
    if DUMP and p == 53:
        with open(DUMP, 'w') as fh:
            for v in (a, b):
                fh.write(' '.join('%016x' % F.to_bits(t) for t in v) + '\n')
    print(f'  overlap max |v_(i+1)|/ulp(v_i): a {ulpno(a, p):.3g}, b {ulpno(b, p):.3g}')
    print(f'p={p} n={n}: {tested} inputs; largest |Z - x|/|Z| = {float(rel):.4g} = 2^{float(rel).hex()} '
          f'= {float(rel / u ** n):.4g} u^n; results 0 with Z != 0: {zeros}')
    print('  a =', [str(A.val(t)) for t in a], ' b =', [str(A.val(t)) for t in b], ' x =', [str(A.val(t)) for t in x],
          ' Z =', Z)
    return best, zeros


DUMP = None

if __name__ == '__main__':
    p, trials, seed = map(int, sys.argv[1:4])
    DUMP = sys.argv[5] if len(sys.argv) > 5 and sys.argv[5] != '-' else None
    LIM = float(sys.argv[6]) if len(sys.argv) > 6 and sys.argv[6] != '-' else None
    RENORM = len(sys.argv) > 7 and sys.argv[7] == 'renorm'
    n = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    run(p, trials, seed, n)
