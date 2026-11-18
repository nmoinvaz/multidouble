"""Hill climbing on err / bound (Theorem thm:acc) at small p, over inputs satisfying H(theta).

python3 climb.py p n K kind theta seconds seed [start] [control]
kind: addx | prod | mixed. start: 'cons' (construct.py's greedy, addx only) or 'rand'. control 'half' halves the
bound: the climb must then report err > bound. Also reports err against the deposit-wise recursion of sharp_rec.py
(a sharper valid bound), which must never be exceeded either.
"""
from fractions import Fraction as Fr
import random
import sys
import time

import bound as B
import construct as C
import reffp as F
import sharp_rec as SR
from gen import operand, check_H


def simulate(terms, n):
    acc = F.Acc(n)
    Z = Fr(0)
    W = Fr(0)
    for t in terms:
        if t[0] == 'P':
            acc.addprod(t[1], t[2])
            Z += sum(F.frac(x) for x in t[1]) * sum(F.frac(x) for x in t[2])
            W += abs(F.frac(t[1][0]) * F.frac(t[2][0]))
        else:
            acc.addx(t[1])
            Z += sum(F.frac(x) for x in t[1])
            W += abs(F.frac(t[1][0]))
    x = acc.finish()
    return abs(Z - sum(F.frac(v) for v in x)), Z, W


def mutate(rng, t, n, th):
    """a copy of term t with one part changed, still satisfying H(th)"""
    which = rng.randrange(1, len(t))
    a = list(t[which])
    l = rng.randrange(n)
    u = Fr(1, 2 ** F.P)
    r = rng.random()
    if l == 0:
        if r < 0.5:
            a[0] = F.add(a[0], (rng.choice((1, -1)) * rng.randrange(1, 4), F.ulp(a[0])[1]))
        else:
            a[0] = operand(rng, n, th, F.expo(a[0]) + rng.choice((-1, 0, 0, 1)), sign=1 if a[0][0] > 0 else -1)[0]
    else:
        if r < 0.4 and a[l][0] != 0:
            a[l] = F.add(a[l], (rng.choice((1, -1)) * rng.randrange(1, 8), F.ulp(a[l])[1]))
        else:
            b = operand(rng, n, th, F.expo(a[0]), style=rng.choice(('edge', 'greedy', 'deep')))
            # rescale b's part l to a's a_0
            a[l] = b[l] if b[l][0] == 0 else (b[l][0], b[l][1] + F.expo(a[0]) - F.expo(b[0]))
    if a[0][0] == 0 or not check_H(a, th):
        return None
    out = list(t)
    out[which] = a
    return tuple(out)


def main():
    p, n, K = (int(v) for v in sys.argv[1:4])
    kind, th, secs, seed = sys.argv[4], int(sys.argv[5]), float(sys.argv[6]), int(sys.argv[7])
    start = sys.argv[8] if len(sys.argv) > 8 else 'rand'
    control = sys.argv[9] if len(sys.argv) > 9 else None
    F.setp(p)
    rng = random.Random(seed)
    u = Fr(1, 2 ** p)
    c, _ = B.second_term(n, p, th, K, kind)
    # the deposit-wise recursion, with the same E_prod and Phi as the theorem
    tau, R, Dl = B.taus(n, u, Fr(th), kind)
    S, _ = B.S_levels(n, u, K, tau)
    c_rec = ((1 + u ** n) * (SR.rec(n, p, K, th, kind) + (R + Dl) * u ** (n + 1)) + B.phi(n, u, S)) / u ** n
    scale = Fr(1, 2) if control == 'half' else Fr(1)
    if start == 'cons':
        terms = [('X', a) for a in C.build(p, n, K, log=False)]
    else:
        terms = []
        for _ in range(K):
            if kind == 'prod' or (kind == 'mixed' and rng.random() < 0.5):
                terms.append(('P', operand(rng, n, th, 0, sign=1), operand(rng, n, th, 0, sign=1)))
            else:
                terms.append(('X', operand(rng, n, th, 0, sign=1)))

    def score(ts):
        err, Z, W = simulate(ts, n)
        bd = u ** n * abs(Z) + c * u ** n * W
        return err / bd, err, Z, W

    best = score(terms)
    t0 = time.time()
    it = acc = 0
    while time.time() - t0 < secs:
        it += 1
        cand = list(terms)
        for _ in range(rng.choice((1, 1, 1, 2, 4))):
            i = rng.randrange(K)
            m = mutate(rng, cand[i], n, th)
            if m is not None:
                cand[i] = m
        sc = score(cand)
        if sc[0] >= best[0]:
            acc += sc[0] > best[0]
            terms, best = cand, sc
    ratio, err, Z, W = best
    bd = u ** n * abs(Z) + c * u ** n * W
    bd_rec = u ** n * abs(Z) + c_rec * u ** n * W
    print(f'p={p} n={n} K={K} {kind} theta={th} start={start} seed={seed}: {it} evaluations, {acc} improvements; '
          f'err/bound = {float(err / bd):.4g}, err/(recursion bound) = {float(err / bd_rec):.4g}, '
          f'err = {float(err / (u ** n * W)):.4g} u^n W, recursion/theorem = {float(bd_rec / bd):.4g}')
    fired = err > scale * bd or err > scale * bd_rec
    if control:
        print('control fired' if fired else 'CONTROL DID NOT FIRE')
    elif fired:
        print('BOUND EXCEEDED')
        sys.exit(1)


if __name__ == '__main__':
    main()
