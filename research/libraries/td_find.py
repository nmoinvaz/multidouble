"""Search for same-sign triple-double sums on which td_real::ieee_add (BL-highprecision/QD 92d99c8, td_inline.h:271-312)
errs by more than td_real::_eps = 2^-157 relative. Operands are greedy three-double roundings (QD normal form); the
middle parts of a and b are drawn close in magnitude so that the merge interleaves them.

usage: td_find.py TRIALS SEED SECONDS [OUT.json]
"""
import json
import math
import random
import sys
import time
from fractions import Fraction

import attack as A
import ports as X
from ports import F, vsum


def part(rng, top, near=None):
    if near is not None and rng.random() < 0.7:
        m = near + rng.randint(-(1 << 20), 1 << 20)
        m = min(max(m, 1 << 52), (1 << 53) - 1)
    else:
        m = rng.getrandbits(53) | (1 << 52)
    return Fraction(m, 1 << 52) * Fraction(2) ** top, m


def main():
    trials, seed, secs = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
    outp = sys.argv[4] if len(sys.argv) > 4 else None
    F.set_p(53)
    rng = random.Random(seed)
    eps = Fraction(1, 2 ** 157)
    best = (Fraction(0), None)
    over = n = 0
    t0 = time.time()
    while n < trials and time.time() - t0 < secs:
        a0, _ = part(rng, 0)
        b0, _ = part(rng, 0)
        e1 = -rng.choice([54, 55, 56])
        a1, m1 = part(rng, e1)
        b1, _ = part(rng, e1 + rng.choice([0, 0, -1, 1]), m1)
        s1 = rng.choice([-1, 1]); s2 = rng.choice([-1, 1])
        a2, _ = part(rng, e1 - rng.choice([54, 55, 56]))
        b2, _ = part(rng, e1 - rng.choice([54, 55, 56]))
        a = A.expand(a0 + s1 * a1 + rng.choice([-1, 1]) * a2, 3)
        b = A.expand(b0 + s2 * b1 + rng.choice([-1, 1]) * b2, 3)
        Z = vsum(a) + vsum(b)
        n += 1
        r = abs(Z - vsum(X.td_ieee_add(a, b))) / abs(Z)
        if r > eps:
            over += 1
        if r > best[0]:
            best = (r, (a, b))
    r, (a, b) = best
    Z = vsum(a) + vsum(b)
    rs = abs(Z - vsum(X.td_sloppy_add(a, b))) / abs(Z)
    print(f"td ieee_add: {n} same-sign sums, over 2^-157 relative: {over}; worst rel err 2^{math.log2(r):.2f} "
          f"(td_real::_eps = 2^-157); sloppy_add on that input: {'2^%.2f' % math.log2(rs) if rs else 'exact'}")
    print("  a =", [A.hexs(t) for t in a]); print("  b =", [A.hexs(t) for t in b])
    print("  ieee_add =", [A.hexs(t) for t in X.td_ieee_add(a, b)])
    print("  exact    =", [A.hexs(t) for t in A.expand(Z, 3)])
    if outp:
        json.dump(dict(a_hex=[A.hexs(t) for t in a], b_hex=[A.hexs(t) for t in b], rel_err_log2=math.log2(r),
                       over=over, trials=n), open(outp, 'w'), indent=1)


if __name__ == '__main__':
    main()
