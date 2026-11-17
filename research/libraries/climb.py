"""Hill climbing on the ratio error / documented bound, over valid inputs (greedy RN expansions).

usage: climb.py OP SEED P SECONDS [OUT.jsonl] [RESTART_STEPS]
"""
import json
import random
import sys
import time
from fractions import Fraction

import attack as A
from ports import F, val, vsum


def ulp_of(x):
    m, e = x
    return Fraction(2) ** (abs(m).bit_length() - 1 + e - F.P + 1)


def mutate(rng, a, b, kind, n):
    a = list(a)
    b = list(b)
    nb = 1 if kind in ('addd', 'muld') else n
    which = rng.random() < 0.5 and nb > 0
    x = b if which else a
    m = nb if which else n
    r = rng.random()
    vals = [val(t) for t in x[:m]]
    i = rng.randrange(m)
    if r < 0.35 and vals[i] != 0:
        k = rng.choice([1, 1, 2, 3, 4, rng.randint(1, 1 << min(F.P - 1, 20))])
        vals[i] += rng.choice([-1, 1]) * k * ulp_of(x[i]) * Fraction(2) ** (-rng.randint(0, 3))
    elif r < 0.55 and i > 0 and vals[i - 1] != 0:
        h = ulp_of(x[i - 1]) / 2  # the largest part QD's normal form allows
        mm = rng.getrandbits(F.P) | (1 << (F.P - 1))
        vals[i] = rng.choice([-1, 1]) * h * Fraction(mm, 1 << F.P) * rng.choice([1, 1, 2])
    elif r < 0.7 and i > 0:
        vals[i] *= Fraction(2) ** (-rng.randint(1, 2 * F.P))  # open a gap
    elif r < 0.8 and i > 0:
        for j in range(i, m):
            vals[j] = Fraction(0)
    elif r < 0.92 and kind in ('add',) and not which:
        k = rng.randint(1, n)
        for j in range(k):
            b[j] = F.neg(a[j])
        vals = [val(t) for t in x[:m]]
        vb = [val(t) for t in b]
        V = sum(vb)
        if V == 0:
            V = val(a[0]) * Fraction(1, 1 << (3 * F.P))
            V = Fraction(V.numerator, V.denominator)
        b = A.expand(V, n)
        return a, b
    else:
        mm = rng.getrandbits(F.P) | (1 << (F.P - 1))
        vals[i] = rng.choice([-1, 1]) * Fraction(mm, 1 << (F.P - 1)) * (ulp_of(x[i]) * (1 << (F.P - 1)) if
                                                                          vals[i] != 0 else 1)
    V = sum(vals)
    if V == 0:
        return a, b
    newx = A.expand(V, m) + [F.PZ] * (n - m)
    if which:
        b = newx
    else:
        a = newx
    return a, b


def main():
    name, seed, p, secs = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
    outp = sys.argv[5] if len(sys.argv) > 5 else None
    restart = int(sys.argv[6]) if len(sys.argv) > 6 else 3000
    F.set_p(p)
    spec = A.OPS[name]
    n = spec['n']
    rng = random.Random(seed)
    t0 = time.time()
    best_all = (Fraction(-1), None)
    steps = 0
    restarts = 0
    while time.time() - t0 < secs:
        a, b = A.rand_pair(rng, p, n, spec['kind'])
        try:
            cur = A.run_case(spec, a, b, p)[0]
        except ZeroDivisionError:
            continue
        restarts += 1
        for _ in range(restart):
            if time.time() - t0 >= secs:
                break
            a2, b2 = mutate(rng, a, b, spec['kind'], n)
            try:
                r2 = A.run_case(spec, a2, b2, p)[0]
            except ZeroDivisionError:
                continue
            steps += 1
            if r2 >= cur:
                a, b, cur = a2, b2, r2
                if cur > best_all[0]:
                    best_all = (cur, (a, b))
    r, (a, b) = best_all
    ratio, out, err, Zx = A.run_case(spec, a, b, p)
    print(f"climb {name} p={p} seed={seed} steps={steps} restarts={restarts} best_ratio={float(r):.6g} "
          f"(log2 {A._l2(r)}) time={time.time() - t0:.0f}s")
    if outp:
        row = dict(op=name, p=p, seed=seed, ratio=float(r), a=[list(x) for x in a], b=[list(x) for x in b],
                   out=[list(x) for x in out], err=str(err), Z=str(Zx))
        if p == 53:
            row['a_hex'] = [A.hexs(x) for x in a]
            row['b_hex'] = [A.hexs(x) for x in b]
            row['out_hex'] = [A.hexs(x) for x in out]
        with open(outp, 'a') as f:
            f.write(json.dumps(row) + '\n')


if __name__ == '__main__':
    main()
