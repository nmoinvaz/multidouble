"""Random counterparts of the K = 2048 construction: the term 1, then K - 1 positive terms with leading part in
[u/2, u) and random parts |a_{m+1}| <= ulp(a_m)/2 of random sign. Prints err / (u^8 W) per sample.
python3 random_same.py samples seed
"""
from fractions import Fraction as Fr
import random
import sys

import reffp as F
from gen import operand

F.setp(53)
u = Fr(1, 2 ** 53)
ns, seed = int(sys.argv[1]), int(sys.argv[2])
rng = random.Random(seed)
worst = 0
for i in range(ns):
    terms = [[(1, 0)] + [F.ZERO] * 7] + [operand(rng, 8, 1, -54, style='greedy', sign=1) for _ in range(2047)]
    acc = F.Acc(8)
    for a in terms:
        acc.addx(a)
    x = acc.finish()
    Z = sum(sum(F.frac(v) for v in a) for a in terms)
    W = sum(abs(F.frac(a[0])) for a in terms)
    r = abs(Z - sum(F.frac(v) for v in x)) / (u ** 8 * W)
    worst = max(worst, r)
    print(f'sample {i}: err = {float(r):.4g} u^8 W', flush=True)
print(f'max {float(worst):.4g} u^8 W over {ns} samples')
