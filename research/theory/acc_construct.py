"""A constructed adversary for the level accumulator (acc.py, OdAcc generalized to n parts): the sum of 1 and K - 1
positive n-part expansions of size about u, each B-nonoverlapping (|a_{m+1}| <= ulp(a_m)/2, so each is a valid
result of the crate's renormalization). Each part is chosen, given the accumulator's state, among significands whose
residue modulo the ulp of a lower level puts the sum just below a midpoint, so that the two-sum there carries about
half an ulp down. The choice maximizes the carries weighted by an estimate of their effect on the final error.

usage: acc_construct.py p n K [mut [dump.json|- [joint]]]     prints err/(u^n W) and err/(u^n |Z|) at k = 2^j and K; exact arithmetic.
mut = 'acc_l3' runs the crate's mutation ACC_L3 (a control), 'none' the algorithm."""
import math
import sys
from fractions import Fraction as Q

import acc as A
F = A.F


def top(x):
    """t with 2^t <= |x| < 2^(t+1)"""
    m, e = x
    return abs(m).bit_length() - 1 + e


def fl(q, e):
    return F.rnd(q, e) if q else F.PZ


def candidates(s, m, e_g, p, n):
    """significands q (a part q 2^e_g, 2^(p-1) <= q < 2^p) aimed at a midpoint of each lower level's ulp"""
    lo, hi = 1 << (p - 1), 1 << p
    out = {lo, hi - 1, (lo + hi) // 2}
    for j in range(m, n + 1):
        if s[j][0] == 0:
            continue
        uj = top(s[j]) - p + 1  # ulp(s_j) = 2^uj
        k = uj - e_g  # U / g = 2^k
        if k < 2:
            continue
        U = 1 << k
        for d in (1, 2, 3):
            r = (U // 2 - d) % U
            first = lo + ((r - lo) % U)
            if first >= hi:
                continue
            last = first + ((hi - 1 - first) // U) * U
            step = max((last - first) // U // 7, 1) * U
            out.update(range(first, last + 1, step))
            out.add(last)
    if JOINT:
        # residues aimed at midpoints of two or three consecutive levels at once: the carry out of level j keeps the
        # part's bits below ulp(s_j), and those decide the rounding at level j + 1
        us = [(top(s[j]) - p + 1 - e_g) if s[j][0] else None for j in range(n + 1)]
        for j in range(m, n + 1):
            for depth in (2, 3):
                ks = us[j:j + depth]
                if len(ks) < depth or any(k is None or k < 2 for k in ks) or any(ks[i] <= ks[i + 1] for i in range(depth - 1)):
                    continue
                U = 1 << ks[0]
                for d in (1, 2, 3):
                    r = (U // 2 - sum(1 << (k - 1) for k in ks[1:]) - d) % U
                    first = lo + ((r - lo) % U)
                    if first >= hi:
                        continue
                    last = first + ((hi - 1 - first) // U) * U
                    step = max((last - first) // U // 7, 1) * U
                    out.update(range(first, last + 1, step))
                    out.add(last)
    return sorted(out)


JOINT = False


def run(p, n, K, mut=None, log=True, dump=None):
    F.set_p(p)
    A.MUT = mut
    u = Q(1, 2 ** p)
    s = A.fresh(n)
    one = [(1, 0)] + [F.PZ] * (n - 1)
    A.acc_levels(s, one)
    Z = Q(1)
    W = Q(1)
    rows = []
    terms = [one]
    for k in range(2, K + 1):
        rem = max(K - k, 1)
        # weight of a unit at level j on the final error, about (u rem)^(n+1-j)/(n+1-j)!; the loss itself weighs 1
        w = [float(u * rem) ** (n + 1 - j) / math.factorial(n + 1 - j) for j in range(n + 1)] + [1.0]
        a = []
        for m in range(n):
            if m == 0:
                e_g = -p - 1 - (p - 1)  # a_0 in [u/2, u): 2^(p-1) g = 2^(-p-1)
            else:
                e_g = top(a[m - 1]) - p - 1 - (p - 1) if a[m - 1][0] else None  # |a_m| in [ulp/4, ulp/2) of a_{m-1}
            if e_g is None:
                a.append(F.PZ)
                continue
            best = None
            for q in candidates(s, m, e_g, p, n):
                x = fl(q, e_g)
                t = list(s)
                before = sum(A.val(y) for y in t) + A.val(x)
                F.dep(t, m, x) if m < n else None
                loss = float(before - sum(A.val(y) for y in t))
                sc = loss + sum(float(A.val(t[j]) - A.val(s[j])) * w[j] for j in range(n + 1))
                if best is None or sc > best[0]:
                    best = (sc, x, t)
            _, x, s = best
            a.append(x)
        Z += sum(A.val(y) for y in a)
        W += A.val(a[0])
        terms.append(a)
        if log and ((k & (k - 1)) == 0 or k == K):
            xr = A.finish(s)
            err = abs(Z - sum(A.val(y) for y in xr))
            lv = sum(A.val(y) for y in s)
            r1 = err / (u ** n * W)
            rows.append((k, float(r1), float(err / (u ** n * abs(Z))), float(abs(Z - lv) / (u ** n * W)), err, Z, W))
            print(f'k={k:6d} err/(u^n W)={float(r1):.6g} err/(u^n|Z|)={rows[-1][2]:.6g} '
                  f'level loss/(u^n W)={rows[-1][3]:.6g} levels/(u^m W)='
                  + ' '.join(f'{float(abs(A.val(s[j])) / (u ** j * W)):.3g}' for j in range(n + 1)), flush=True)
    if dump:
        import json
        xr = A.finish(s)
        json.dump({'p': p, 'n': n, 'K': K, 'terms': [[F.to_bits(y) for y in t] for t in terms],
                   'result': [F.to_bits(y) for y in xr], 'Z': [Z.numerator, Z.denominator]}, open(dump, 'w'))
    return rows


if __name__ == '__main__':
    p, n, K = map(int, sys.argv[1:4])
    mut = sys.argv[4] if len(sys.argv) > 4 and sys.argv[4] != 'none' else None
    JOINT = len(sys.argv) > 6 and sys.argv[6] == 'joint'
    run(p, n, K, mut, dump=sys.argv[5] if len(sys.argv) > 5 and sys.argv[5] != '-' else None)
