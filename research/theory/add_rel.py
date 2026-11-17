"""Proposition C of research/theory/cancellation.tex: for n >= 3 and every p >= 5, ADD of the B-nonoverlapping
expansions
    n = 3:  a = (1, -u, -(2^p - 2) u^3),                       b = (-(1 - u), (2^p - 3) u^3, -(1 - 2u) u^4)
    n >= 4: a = (1, u, ..., u^(n-3), -u^(n-2), -(2^p - 2) u^n),
            b = (-1, -u, ..., -u^(n-4), -(1 - u) u^(n-3), (2^p - 3) u^n, -(1 - 2u) u^(n+1))
returns x = (-u^n, 0, ..., 0) while a + b = -u^n - (1 - 2u) u^(n+1): relative error (1 - 2u) u / (1 + u - 2u^2).
Checked exactly on fpemu.od_add; at p = 53 the operands are written as f64 bit patterns for the crate check.
Control: with ties away from zero (fpemu MUTATE 'ties_away') the result must differ.
usage: add_rel.py [dumpdir]     exits non-zero on a failure."""
import os
import sys
from fractions import Fraction as Q

import acc as A
F = A.F


def operands(p, n):
    u = Q(1, 2 ** p)
    two_p = 2 ** p
    if n == 3:
        a = [1, -u, -(two_p - 2) * u ** 3]
        b = [-(1 - u), (two_p - 3) * u ** 3, -(1 - 2 * u) * u ** 4]
    else:
        a = [u ** i for i in range(n - 2)] + [-u ** (n - 2), -(two_p - 2) * u ** n]
        b = [-u ** i for i in range(n - 3)] + [-(1 - u) * u ** (n - 3), (two_p - 3) * u ** n, -(1 - 2 * u) * u ** (n + 1)]
    return a, b


def tofl(v, p):
    num, den = v.numerator, v.denominator
    assert den & (den - 1) == 0
    e = -(den.bit_length() - 1)
    while num % 2 == 0:
        num //= 2
        e += 1
    assert abs(num) < 2 ** p, (v, p)
    return (num, e)


def b_nonoverlap(v, p):
    for i in range(len(v) - 1):
        t = abs(v[i][0]).bit_length() - 1 + v[i][1]
        if abs(A.val(v[i + 1])) > Q(2) ** (t - p):
            return False
    return True


ok = True
dump = sys.argv[1] if len(sys.argv) > 1 else None
for p in (5, 6, 7, 8, 10, 12, 24, 53):
    for n in range(3, 9):
        F.set_p(p)
        F.MUTATE = None
        u = Q(1, 2 ** p)
        av, bv = operands(p, n)
        a = [tofl(v, p) for v in av]
        b = [tofl(v, p) for v in bv]
        Z = sum(av) + sum(bv)
        x = F.od_add(a, b)
        xs = [A.val(t) for t in x]
        rel = abs(Z - sum(xs)) / abs(Z)
        want = (1 - 2 * u) * u / (1 + u - 2 * u * u)
        good = (xs == [-u ** n] + [0] * (n - 1) and Z == -u ** n - (1 - 2 * u) * u ** (n + 1) and rel == want
                and b_nonoverlap(a, p) and b_nonoverlap(b, p))
        F.MUTATE = 'ties_away'
        xc = F.od_add(a, b)
        F.MUTATE = None
        fired = [A.val(t) for t in xc] != xs
        ok &= good and fired
        if n in (3, 8) or not (good and fired):
            print(f'p={p:2d} n={n}: x = -u^n, rel. error = {float(rel):.6g} = {float(rel / u):.6f} u = 2^{float(rel).hex()}'
                  f' ({"PASS" if good else "FAIL"}; control ties-away changes x: {fired})')
        if dump and p == 53:
            with open(os.path.join(dump, f'add_rel_p53_n{n}.txt'), 'w') as fh:
                for v in (a, b):
                    fh.write(' '.join('%016x' % F.to_bits(t) for t in v) + '\n')
print('PASS' if ok else 'FAIL')
sys.exit(0 if ok else 1)
