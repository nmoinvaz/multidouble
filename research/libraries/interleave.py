"""Operands whose parts interleave in magnitude: b is a scaled by 2^-s (s near 0, 53 or 106) with one part of b drawn
close in magnitude to the part of a at the same scale. This is the pattern that makes QD's merge-based ieee_add emit a
word and then receive an input of comparable size.

usage: interleave.py OP N TRIALS SEED SECONDS     (OP: td_ieee_add | qd_ieee_add | qd_ieee_add_fixed | qd_ieee_add_fix2)
"""
import math
import random
import sys
import time
from fractions import Fraction

import attack as A
import ports as X
from ports import F, val, vsum


def rand_exp(rng, n, top=0):
    v = Fraction(0)
    parts = []
    sc = top
    for i in range(n):
        m = rng.getrandbits(53) | (1 << 52)
        p = rng.choice([-1, 1]) * Fraction(m, 1 << 52) * Fraction(2) ** sc
        if i == 0:
            p = abs(p)
        parts.append(p)
        sc -= rng.choice([53, 54, 55, 56])
    return parts


def main():
    op, n, trials, seed, secs = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), float(sys.argv[5])
    fn = getattr(X, op)
    F.set_p(53)
    rng = random.Random(seed)
    u = Fraction(1, 2 ** 53)
    bound = (4 * u ** 3) if n == 3 else (4 * u ** 4)
    best = (Fraction(0), None)
    over = cnt = 0
    t0 = time.time()
    while cnt < trials and time.time() - t0 < secs:
        pa = rand_exp(rng, n)
        lvl = rng.randrange(n)
        s = rng.choice([0, 1, 2, 3]) + 53 * rng.choice([0, 0, 1, 2])
        pb = rand_exp(rng, n, top=-s)
        # pull one part of b close to the part of a nearest its scale
        j = rng.randrange(n)
        target = min(range(n), key=lambda i: abs(math.log2(abs(pa[i])) - math.log2(abs(pb[j]))))
        sgn = 1 if pb[j] > 0 else -1
        pb[j] = sgn * abs(pa[target]) * (1 + Fraction(rng.randint(-(1 << 30), 1 << 30), 1 << 60))
        if rng.random() < 0.3:
            pb[j] *= Fraction(rng.choice([3, 5, 7]), 8)
        a = A.expand(sum(pa), n)
        b = A.expand(sum(pb), n)
        Z = vsum(a) + vsum(b)
        if Z == 0 or any(t[0] == 0 for t in a + b):
            continue
        cnt += 1
        r = abs(Z - vsum(fn(a, b))) / abs(Z)
        if r > bound:
            over += 1
        if r > best[0]:
            best = (r, (a, b))
    r, (a, b) = best
    print(f"{op}: {cnt} interleaved sums, over the bound ({'4u^3' if n == 3 else '4u^4'}) {over}, worst rel err "
          f"2^{math.log2(r):.2f}")
    print("  a =", [A.hexs(t) for t in a])
    print("  b =", [A.hexs(t) for t in b])


if __name__ == '__main__':
    main()
