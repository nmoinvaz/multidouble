"""Gap-free operands whose partial products cancel inside a level, so that a level is smaller than the next one.

a = (a0, a1, a2, a3) and b = (b0, b1, b2, b3) in QD's normal form (|x_{i+1}| <= ulp(x_i)/2, no zero parts). b1 is
chosen near -a1 b0 / a0, so level 1 (a0 b1 + a1 b0) cancels to a few ulps of a1 while level 2 keeps its size. Then
the first pass of QD's renorm, quick_two_sum(c1, s0) with |c1| < |s0|, can be inexact.

usage: mul_cancel.py OP P TRIALS SEED [OUT.jsonl]
"""
import json
import random
import sys
from fractions import Fraction

import attack as A
from ports import F, val, vsum


def rnd(x):
    """RN-even of a nonzero rational to P bits (exact, via an integer quotient and a sticky bit)"""
    if x == 0:
        return F.PZ
    neg = x < 0
    n, d = abs(x.numerator), x.denominator
    k = F.P + 3 + d.bit_length() - n.bit_length()
    q, r = divmod(n << k, d) if k >= 0 else divmod(n, d << -k)
    return F.rnd_sticky(q, -k, r != 0, neg)


def part_below(rng, prev, full=True):
    """a nonzero part with |x| <= ulp(prev)/2, near the top of that range"""
    m, e = prev
    half_ulp = Fraction(2) ** (abs(m).bit_length() - 1 + e - F.P)
    mm = rng.getrandbits(F.P) | (1 << (F.P - 1))
    scale = Fraction(mm, 1 << F.P) * (1 if full else Fraction(1, 1 << rng.randint(1, 4)))
    v = rng.choice([-1, 1]) * half_ulp * scale
    return rnd(v)


def valid(x):
    for i in range(len(x) - 1):
        if x[i][0] == 0:
            return False
        m, e = x[i]
        if abs(val(x[i + 1])) > Fraction(2) ** (abs(m).bit_length() - 1 + e - F.P):
            return False
    return x[-1][0] != 0


def gen(rng):
    a0 = rnd(Fraction(rng.getrandbits(F.P) | (1 << (F.P - 1)), 1 << (F.P - 1)))
    b0 = rnd(Fraction(rng.getrandbits(F.P) | (1 << (F.P - 1)), 1 << (F.P - 1)))
    if rng.random() < 0.5:
        b0 = F.rnd(1, 0)
    a1 = part_below(rng, a0)
    lev = rng.choice([1, 1, 2])
    if lev == 1:
        t = -val(a1) * val(b0) / val(a0)
        b1 = rnd(t)
        k = rng.randint(-3, 3)
        m, e = b1
        b1 = rnd(val(b1) + k * Fraction(2) ** (abs(m).bit_length() - 1 + e - F.P + 1 - rng.randint(0, 1)))
        a2, a3 = part_below(rng, a1), None
        b2 = part_below(rng, b1) if b1[0] != 0 else F.PZ
        a3 = part_below(rng, a2)
        b3 = part_below(rng, b2) if b2[0] != 0 else F.PZ
    else:
        b1 = part_below(rng, b0)
        a2 = part_below(rng, a1)
        # level 2: a0 b2 + a1 b1 + a2 b0 ~ 0
        t = -(val(a1) * val(b1) + val(a2) * val(b0)) / val(a0)
        b2 = rnd(t)
        k = rng.randint(-3, 3)
        if b2[0] != 0:
            m, e = b2
            b2 = rnd(val(b2) + k * Fraction(2) ** (abs(m).bit_length() - 1 + e - F.P + 1))
        a3 = part_below(rng, a2)
        b3 = part_below(rng, b2) if b2[0] != 0 else F.PZ
    a = [a0, a1, a2, a3]
    b = [b0, b1, b2, b3]
    return a, b


def main():
    name, p, trials, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    outp = sys.argv[5] if len(sys.argv) > 5 else None
    F.set_p(p)
    spec = A.OPS[name]
    rng = random.Random(seed)
    worst = (Fraction(0), None)
    over = 0
    n = 0
    for _ in range(trials):
        a, b = gen(rng)
        if not (valid(a) and valid(b)):
            continue
        n += 1
        r, out, err, Z = A.run_case(spec, a, b, p)
        if r > 1:
            over += 1
        if r > worst[0]:
            worst = (r, (a, b, out))
    r, (a, b, out) = worst
    print(f"mul_cancel {name} p={p} seed={seed} valid_trials={n} over_bound={over} worst_ratio={float(r):.4g} "
          f"(log2 {A._l2(r)})")
    if outp and r > 0:
        row = dict(op=name, p=p, seed=seed, ratio=float(r), a=[list(x) for x in a], b=[list(x) for x in b],
                   out=[list(x) for x in out])
        if p == 53:
            row['a_hex'] = [A.hexs(x) for x in a]
            row['b_hex'] = [A.hexs(x) for x in b]
            row['out_hex'] = [A.hexs(x) for x in out]
        with open(outp, 'a') as f:
            f.write(json.dumps(row) + '\n')


if __name__ == '__main__':
    main()
