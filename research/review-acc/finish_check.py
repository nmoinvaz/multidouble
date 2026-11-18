"""FINISH's structure (proof of Theorem thm:acc): for arbitrary levels s_0..s_n, in any order of magnitudes,
r^(l) = ADDF(r^(l-1), s_l) is exact for l <= n-1 and has nonzero parts only at positions 0..l; the last ADDF loses
at most min_k B_k of Theorem t1(b) (checked with k = 0 and the actual v_j).
python3 finish_check.py cases seed [control]     control 'vecsum' replaces VecSum's last two-sum by a plain sum
"""
from fractions import Fraction as Fr
import random
import sys

import reffp as F

cases, seed = int(sys.argv[1]), int(sys.argv[2])
control = len(sys.argv) > 3
rng = random.Random(seed)
if control:
    orig = F.vecsum

    def bad(c):
        v = orig(c)
        v[0] = F.add(v[0], v[1])
        v[1] = F.ZERO
        return v
    F.vecsum = bad
bad_exact = bad_prefix = bad_t1 = 0
worst = 0.0
for i in range(cases):
    p, n = rng.choice([(8, 2), (8, 3), (10, 4), (12, 5), (53, 8)])
    F.setp(p)
    u = Fr(1, 2 ** p)
    us = u / (1 + u)
    s = []
    for m in range(n + 1):
        if rng.random() < 0.15:
            s.append(F.ZERO)
            continue
        e = rng.randrange(-3 * p, 3) if rng.random() < 0.5 else -m * p + rng.randrange(-3, 3)
        x = F.rn(rng.randrange(1 << (p - 1), 1 << p), e - p + 1)
        s.append(x if rng.random() < 0.5 else F.neg(x))
    r = [s[0]] + [F.ZERO] * (n - 1)
    for l in range(1, n + 1):
        prev = r
        lev = [F.ZERO] * (n + 1)
        e = s[l]
        for j in range(n):
            lev[j], e = F.two_sum(prev[j], e)
        lev[n] = e
        v = F.vecsum(lev)
        r = F.renorm(lev, n)
        tot = sum(F.frac(x) for x in s[:l + 1])
        got = sum(F.frac(x) for x in r)
        if l <= n - 1:
            bad_exact += got != tot
            nz = [j for j in range(n) if r[j][0] != 0]
            bad_prefix += bool(nz) and max(nz) > l
        else:
            E = abs(tot - got)
            B0 = us ** n * abs(F.frac(v[0])) + sum(us ** (n + 1 - j) * abs(F.frac(v[j])) for j in range(1, n + 1))
            bad_t1 += E > B0
            if B0:
                worst = max(worst, float(E / B0))
print(f'{cases} cases{" (control)" if control else ""}: inexact intermediate ADDF {bad_exact}, '
      f'parts beyond l {bad_prefix}, last ADDF above B_0 {bad_t1}; max E/B_0 = {worst:.4g}')
fails = bad_exact + bad_prefix + bad_t1
if control:
    print('control fired' if fails else 'CONTROL DID NOT FIRE')
elif fails:
    sys.exit(1)
