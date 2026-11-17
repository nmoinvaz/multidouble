"""Largest relative error, in units of u^2, of shipped double-word operations, by random search and hill climbing.

usage: dd_climb.py OP SEED P SECONDS [OUT.jsonl]
OP: boost_add boost_mul boost_div boost_sqrt df_add df_mul df_div jmp_div_dw2
"""
import json
import random
import sys
import time
from fractions import Fraction

import attack as A
import dd_ports as D
from ports import F, val, vsum

OPS = {
    'boost_add': (D.boost_add, 'add'), 'boost_mul': (D.boost_mul, 'mul'), 'boost_div': (D.boost_div, 'div'),
    'boost_sqrt': (D.boost_sqrt, 'sqrt'), 'df_add': (D.df_add, 'add'), 'df_mul': (D.df_mul, 'mul'),
    'df_div': (D.df_div, 'div'), 'jmp_div_dw2': (D.jmp_div_dw2, 'div'),
}


def rel_err_u2(fn, kind, x, y):
    X, Y = vsum(x), vsum(y)
    if kind == 'add':
        Z = X + Y
    elif kind == 'mul':
        Z = X * Y
    elif kind == 'div':
        Z = X / Y
    else:
        Z = None
    out = fn(x) if kind == 'sqrt' else fn(x, y)
    R = vsum(out)
    if kind == 'sqrt':
        # |R - sqrt(X)| / sqrt(X) = |R^2 - X| / (sqrt(X) (R + sqrt(X))), bracketed exactly by rationals
        if X <= 0:
            return Fraction(0)
        d = abs(R * R - X)
        # sqrt(X) lies between X/R' and R' for R' > 0; use the bracket [lo, hi] of sqrt(X)
        lo, hi = sorted([R, X / R])
        rel_hi = d / (lo * (R + lo))  # an upper bound on the relative error
        return rel_hi * (2 ** (2 * F.P))
    if Z == 0:
        return Fraction(0)
    return abs(R - Z) / abs(Z) * (2 ** (2 * F.P))


def rand_dw(rng, p):
    """a random normalized double-word (xh, xl) with xh in [1, 2) and |xl| <= ulp(xh)/2"""
    m = rng.getrandbits(p) | (1 << (p - 1))
    xh = Fraction(m, 1 << (p - 1))
    half_ulp = Fraction(1, 1 << p)
    lo = Fraction(rng.getrandbits(p + 1) - (1 << p), 1 << p) * half_ulp
    lo *= Fraction(1, 1 << rng.choice([0, 0, 0, 1, 2, rng.randint(0, p)]))
    s = rng.choice([-1, 1])
    return A.expand(s * (xh + lo), 2)


def mutate(rng, x):
    v = [val(t) for t in x]
    i = rng.randrange(2)
    if x[i][0] == 0:
        i = 0
    m, e = x[i]
    ulp = Fraction(2) ** (abs(m).bit_length() - 1 + e - F.P + 1)
    k = rng.choice([1, 1, 2, 3, rng.randint(1, 1 << min(F.P - 2, 16))])
    v[i] += rng.choice([-1, 1]) * k * ulp
    if rng.random() < 0.2:
        h = ulp / 2 if i == 0 else Fraction(2) ** (abs(x[0][0]).bit_length() - 1 + x[0][1] - F.P)
        v[1] = rng.choice([-1, 1]) * h * Fraction(rng.getrandbits(F.P) | (1 << (F.P - 1)), 1 << F.P)
    V = sum(v)
    if V == 0:
        return x
    return A.expand(V, 2)


def main():
    name, seed, p, secs = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
    outp = sys.argv[5] if len(sys.argv) > 5 else None
    F.set_p(p)
    fn, kind = OPS[name]
    rng = random.Random(seed)
    t0 = time.time()
    best = (Fraction(-1), None)
    steps = 0
    while time.time() - t0 < secs:
        x, y = rand_dw(rng, p), rand_dw(rng, p)
        if kind == 'sqrt':
            x = [F.fabs(x[0]), x[1] if x[0][0] > 0 else F.neg(x[1])]
        cur = rel_err_u2(fn, kind, x, y)
        for _ in range(2000):
            if time.time() - t0 >= secs:
                break
            if rng.random() < 0.5:
                x2, y2 = mutate(rng, x), y
            else:
                x2, y2 = x, mutate(rng, y)
            if kind == 'sqrt' and (x2[0][0] <= 0):
                continue
            r = rel_err_u2(fn, kind, x2, y2)
            steps += 1
            if r >= cur:
                x, y, cur = x2, y2, r
                if cur > best[0]:
                    best = (cur, (x, y))
    r, (x, y) = best
    print(f"dd {name} p={p} seed={seed} steps={steps} max_rel_err={float(r):.5f} u^2  time={time.time() - t0:.0f}s")
    if outp:
        row = dict(op=name, p=p, seed=seed, rel_err_u2=float(r), x=[list(t) for t in x], y=[list(t) for t in y])
        if p == 53:
            row['x_hex'] = [A.hexs(t) for t in x]
            row['y_hex'] = [A.hexs(t) for t in y]
        with open(outp, 'a') as f:
            f.write(json.dumps(row) + '\n')


if __name__ == '__main__':
    main()
