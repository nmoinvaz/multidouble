"""Checks Theorem thm:acc (acc_bound.py) on the level accumulator in exact arithmetic, with controls that must fail.

1. The constructed adversary (acc_construct.py) at small p and at p = 53, n = 8: at every logged k,
   |Z - x| <= u^n |Z| + kappa_acc(k) u^(n+1) W  (ratio <= 1 required).
2. Random positive and mixed-sign expansions (greedy and plain) at p = 8..12: the same bound after every deposit.
Controls (each must fire):
   C1. the bound with every rising power K^(r) lowered to K^(r-1) fails on the construction (so the growth order
       n + 1 in K is needed);
   C2. the crate's mutation ACC_L3 (level 3's carry dropped) breaks the bound (n >= 4);
   C3. a bound linear in K, (n + K) u^n W (the form of the crate's test threshold), fails on the construction.
usage: acc_check.py [quick]      exits non-zero if a check fails or a control does not fire."""
import random
import math
import sys
from fractions import Fraction as Q

import acc as A
import acc_construct as C
import acc_greedy as G
from acc_bound import acc_bound

F = A.F
quick = len(sys.argv) > 1 and sys.argv[1] == 'quick'
ok = True


def bound(p, n, k, Z, W, drop_power=0):
    b = acc_bound(n, p, 1, k, 'add', drop_power)
    return b['u'] ** n * abs(Z) + b['total'] * W


# 1. the construction
cases = [(8, 2, 64), (10, 3, 128), (12, 3, 512), (12, 4, 256), (14, 5, 512)] + ([] if quick else [(53, 8, 2048)])
c1_fired = c3_fired = False
for p, n, K in cases:
    rows = C.run(p, n, K, log=True) if False else None
    import io, contextlib
    with contextlib.redirect_stdout(io.StringIO()):
        rows = C.run(p, n, K)
    worst = 0.0
    for (k, r1, r2, r3, err, Z, W) in rows:
        rat = err / bound(p, n, k, Z, W)
        worst = max(worst, float(rat))
        if err > bound(p, n, k, Z, W, drop_power=1):
            c1_fired = True
        if err > (n + k) * Q(1, 2 ** p) ** n * W:
            c3_fired = True
    last = rows[-1]
    print(f'construction p={p:2d} n={n} K={K:5d}: err/(u^n W) = {last[1]:.4g}, max over k <= K of err/bound = {worst:.3g}',
          'PASS' if worst <= 1 else 'FAIL', flush=True)
    kk, err, Z, W = last[0], last[4], last[5], last[6]
    lead = Q(kk, 2 ** p) ** (n + 1) * W / math.factorial(n + 1)
    print(f'    at k = {kk}: err / ((k u)^(n+1) W / (n+1)!) = {float(err / lead):.3g}, err/bound = '
          f'{float(err / bound(p, n, kk, Z, W)):.3g}', flush=True)
    ok &= worst <= 1
print('C1 (bound with rising powers lowered by one) fires:', c1_fired)
print('C3 (bound linear in K) fires:', c3_fired)
ok &= c1_fired and c3_fired

# C2: the mutation, on random positive expansions of size about 1
fired = []
for p, n, K in ((12, 5, 8), (53, 8, 8)):
    F.set_p(p)
    A.MUT = 'acc_l3'
    rng = random.Random(5)
    s = A.fresh(n)
    Z = Q(0)
    W = Q(0)
    hit = False
    for k in range(1, K + 1):
        a = G.rand_exp(rng, p, 1 - p, n, True)
        A.acc_levels(s, a)
        Z += sum(A.val(y) for y in a)
        W += abs(A.val(a[0]))
        x = A.finish(s)
        hit |= abs(Z - sum(A.val(y) for y in x)) > bound(p, n, k, Z, W)
    A.MUT = None
    fired.append(hit)
print('C2 (mutation ACC_L3 at p=12 n=5 and p=53 n=8, K=8) breaks the bound:', fired)
ok &= all(fired)

# 2. random inputs, the bound after every deposit
for p, n, K, trials in [(8, 2, 64, 6), (10, 3, 96, 4), (12, 4, 64, 3)]:
    worst = 0.0
    for seed in range(trials if not quick else 1):
        for front, sgn in ((True, 1), (False, 1), (False, -1)):
            F.set_p(p)
            rng = random.Random(1000 * seed + 7 * front + (sgn < 0))
            u = Q(1, 2 ** p)
            s = A.fresh(n)
            Z = Q(0)
            W = Q(0)
            for k in range(1, K + 1):
                e0 = (1 - p) if (k == 1 or not front) else (1 - 2 * p)
                a = G.rand_exp(rng, p, e0 + rng.choice((0, 0, -1, -3)), n, False)
                if sgn < 0 and rng.random() < 0.5:
                    a = F.od_neg(a)
                A.acc_levels(s, a)
                Z += sum(A.val(y) for y in a)
                W += abs(A.val(a[0]))
                x = A.finish(s)
                err = abs(Z - sum(A.val(y) for y in x))
                worst = max(worst, float(err / bound(p, n, k, Z, W)))
    print(f'random p={p:2d} n={n} K={K}: max err/bound = {worst:.3g}', 'PASS' if worst <= 1 else 'FAIL', flush=True)
    ok &= worst <= 1

# 3. products (add_prod: expand, then deposit), the bound of mode prod with theta = 2, after every deposit
for p, n, K in [(10, 3, 48), (12, 4, 32)]:
    worst = 0.0
    for seed in range(1 if quick else 3):
        F.set_p(p)
        rng = random.Random(77 + seed)
        u = Q(1, 2 ** p)
        s = A.fresh(n)
        Z = Q(0)
        W = Q(0)
        for k in range(1, K + 1):
            a = G.rand_exp(rng, p, 1 - p + rng.choice((0, -1)), n, False)
            b = G.rand_exp(rng, p, 1 - p + rng.choice((0, -1)), n, False)
            if rng.random() < 0.5:
                b = F.od_neg(b)
            A.acc_levels(s, F.od_expand(a, b))
            Z += sum(A.val(y) for y in a) * sum(A.val(y) for y in b)
            W += abs(A.val(a[0]) * A.val(b[0]))
            x = A.finish(s)
            err = abs(Z - sum(A.val(y) for y in x))
            bd = acc_bound(n, p, 2, k, 'prod')
            worst = max(worst, float(err / (bd['u'] ** n * abs(Z) + bd['total'] * W)))
    print(f'products p={p:2d} n={n} K={K}: max err/bound = {worst:.3g}', 'PASS' if worst <= 1 else 'FAIL', flush=True)
    ok &= worst <= 1

print('PASS' if ok else 'FAIL')
sys.exit(0 if ok else 1)
