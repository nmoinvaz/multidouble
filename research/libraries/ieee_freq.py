"""How often QD's ieee_add (2.3.24 and the upstream fix 92d99c8) exceeds 2 eps_qd = 2^-210 relative on random
same-sign operands, each the greedy four-double rounding of a random 260-bit number in [1, 2).

usage: ieee_freq.py TRIALS SEED SECONDS
"""
import random
import sys
import time
from fractions import Fraction

import attack as A
import ports as X
from ports import F, vsum


def main():
    trials, seed, secs = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
    F.set_p(53)
    rng = random.Random(seed)
    bound = Fraction(1, 2 ** 210)
    n = over_old = over_fix = over_sloppy = 0
    t0 = time.time()
    while n < trials and time.time() - t0 < secs:
        a = A.expand(Fraction((1 << 259) | rng.getrandbits(259), 1 << 259), 4)
        b = A.expand(Fraction((1 << 259) | rng.getrandbits(259), 1 << 259), 4)
        Z = vsum(a) + vsum(b)
        n += 1
        over_old += abs(Z - vsum(X.qd_ieee_add(a, b))) > bound * Z
        over_fix += abs(Z - vsum(X.qd_ieee_add_fixed(a, b))) > bound * Z
        over_sloppy += abs(Z - vsum(X.qd_sloppy_add(a, b))) > bound * Z
    print(f"random same-sign pairs {n}: over 2^-210 relative: ieee_add 2.3.24 {over_old}, ieee_add 92d99c8 {over_fix}, "
          f"sloppy_add {over_sloppy}")


if __name__ == '__main__':
    main()
