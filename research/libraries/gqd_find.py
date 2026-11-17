"""GQD's renorm (gqd_basic.cu:84) adds c4 into s2 with a plain addition when s3 == 0, where QD keeps the error as s3.
Search operands with fewer than four nonzero parts (which make s3 == 0 likely) for that loss.

usage: gqd_find.py OP TRIALS SEED [OUT.jsonl]
"""
import json
import random
import sys
from fractions import Fraction

import attack as A
from ports import F


def short_value(rng, k):
    """a value whose greedy expansion has k nonzero parts, the parts at the ulp scale or with small gaps"""
    v = Fraction(0)
    scale = 0
    for i in range(k):
        m = rng.getrandbits(53) | (1 << 52)
        v += rng.choice([-1, 1]) * Fraction(m) * Fraction(2) ** (scale - 52)
        scale -= rng.choice([53, 54, 55, 56, 60, 70])
    return v


def main():
    name, trials, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    outp = sys.argv[4] if len(sys.argv) > 4 else None
    F.set_p(53)
    spec = A.OPS[name]
    rng = random.Random(seed)
    best = (Fraction(0), None)
    over = 0
    for _ in range(trials):
        A_ = short_value(rng, rng.randint(1, 3))
        B_ = short_value(rng, rng.randint(1, 3)) * Fraction(2) ** (-rng.randint(0, 120))
        if spec['kind'] in ('add', 'addd') and rng.random() < 0.3:
            B_ = -A_ + B_ * Fraction(2) ** (-rng.randint(50, 110))
        if B_ == 0:
            continue
        a = A.expand(A_, 4)
        nb = 1 if spec['kind'] in ('addd', 'muld') else 4
        b = A.expand(B_, nb) + [F.PZ] * (4 - nb)
        r = A.run_case(spec, a, b, 53)[0]
        if r > 1:
            over += 1
        if r > best[0]:
            best = (r, (a, b))
    r, (a, b) = best
    ratio, out, err, Z = A.run_case(spec, a, b, 53)
    print(f"gqd_find {name} trials={trials} over_bound={over} worst_ratio={float(r):.4g} (log2 {A._l2(r)})")
    print("  a =", [A.hexs(x) for x in a])
    print("  b =", [A.hexs(x) for x in b])
    print("  out =", [A.hexs(x) for x in out], " err/|Z| =", float(err / abs(Z)))
    if outp:
        with open(outp, 'a') as f:
            f.write(json.dumps(dict(op=name, ratio=float(r), a_hex=[A.hexs(x) for x in a],
                                    b_hex=[A.hexs(x) for x in b], out_hex=[A.hexs(x) for x in out],
                                    rel_err=float(err / abs(Z)))) + '\n')


if __name__ == '__main__':
    main()
