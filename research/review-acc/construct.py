"""The referee's own version of the construction of Proposition prop:acc-low, from the section's description only:
K ADDX terms, the first (1, 0, ..., 0) and the others positive with leading part about u and |a_{m+1}| <= ulp(a_m)/2;
each part is chosen, in order, to aim the carry it starts at the midpoint of the ulp of a lower level.

The choice is greedy on a potential V = E + sum_m c_m s_m, where E is the signed sum of the rounding errors at level n
so far and c_m = (u (K - k))^(n+1-m) / (n+1-m)! the yield of a unit at level m over the remaining deposits, if each
level passes about u times its value down per deposit. Candidates for part l: for each level j >= l, the largest
|a| <= cap with s_j + a at a midpoint of ulp(s_j) (both tie directions, both signs), the cap itself, and at small p
every float of the top binades below the cap.

python3 construct.py p n K [out.txt]     prints the error in units of u^n |Z| and of the theorem's bound
"""
from fractions import Fraction as Fr
from math import factorial, log2
import sys

import bound as B
import reffp as F


def frac(x):
    return F.frac(x)


def aim_candidates(s, l, cap):
    """parts a with |a| <= cap aiming s_j + carry at a midpoint of ulp(s_j), j >= l"""
    out = set()
    capf = frac(cap)
    n = len(s) - 1
    for j in range(l, n + 1):
        if s[j][0] == 0:
            continue
        U = frac(F.ulp(s[j]))
        sj = frac(s[j])
        # representable odd multiples of U/2 need |a| < 2^P U/2
        lim = min(capf, (2 ** F.P - 1) * U / 2)
        for sgn in (1, -1):
            for r0 in (U / 2, 3 * U / 2):
                # a = sgn * |a|, s_j + a = r0 (mod 2U)
                # largest |a| <= lim with sgn*|a| = r0 - sj (mod 2U)
                t = (r0 - sj) % (2 * U)
                if sgn > 0:
                    m = lim - ((lim - t) % (2 * U))
                else:
                    t2 = (-t) % (2 * U)
                    m = lim - ((lim - t2) % (2 * U))
                if m <= 0:
                    continue
                a = m * sgn
                num, den = a.numerator, a.denominator
                x = F.rn(num * 2 ** 0, 0) if den == 1 else F.rn(num, -(den.bit_length() - 1))
                if frac(x) == a:
                    out.add(x)
    return out


def binade_candidates(cap, binades=3):
    out = set()
    e = F.expo(cap)
    for b in range(binades):
        for m in range(1 << (F.P - 1), 1 << F.P):
            x = F.rn(m, e - b - F.P + 1)
            if frac(x) <= frac(cap):
                out.add(x)
                out.add(F.neg(x))
    return out


class State:
    def __init__(self, n):
        self.s = [F.ZERO] * (n + 1)
        self.E = Fr(0)

    def copy(self):
        c = State.__new__(State)
        c.s = list(self.s)
        c.E = self.E
        return c

    def dep(self, l, t):
        n = len(self.s) - 1
        e = t
        for m in range(l, n):
            self.s[m], e = F.two_sum(self.s[m], e)
        ex = frac(self.s[n]) + frac(e)
        self.s[n] = F.add(self.s[n], e)
        self.E += ex - frac(self.s[n])


def build(p, n, K, exhaustive=None, log=True, absval=False):
    F.setp(p)
    u = Fr(1, 2 ** p)
    if exhaustive is None:
        exhaustive = p <= 12
    st = State(n)
    terms = [[(1, 0)] + [F.ZERO] * (n - 1)]
    st.dep(0, terms[0][0])
    for k in range(2, K + 1):
        c = [(u * (K - k + 1)) ** (n + 1 - m) / factorial(n + 1 - m) for m in range(n + 1)]

        def V(x):
            if absval:
                return abs(x.E) + sum(cm * abs(frac(sm)) for cm, sm in zip(c, x.s))
            return x.E + sum(cm * frac(sm) for cm, sm in zip(c, x.s))

        parts = []
        for l in range(n):
            if l == 0:
                cap = (1, -p)  # a_0 <= u, positive
            else:
                prev = parts[-1]
                if prev[0] == 0:
                    parts.append(F.ZERO)
                    continue
                cap = F.ulp(prev)
                cap = (cap[0], cap[1] - 1)  # ulp/2
            cands = aim_candidates(st.s, l, cap) | {cap}
            if l > 0:
                cands.add(F.neg(cap))
            if exhaustive:
                cands |= binade_candidates(cap)
            if l == 0:
                cands = {x for x in cands if x[0] > 0 and frac(x) >= u / 4}
            best = None
            for a in cands:
                t = st.copy()
                t.dep(l, a)
                v = V(t)
                if best is None or v > best[0]:
                    best = (v, a, t)
            parts.append(best[1])
            st = best[2]
        terms.append(parts)
        if log and k & (k - 1) == 0:
            print(f'  k={k}: E/u^n = {float(st.E / u ** n):.4g}', flush=True)
    return terms


def evaluate(terms, n, p, th=1):
    F.setp(p)
    u = Fr(1, 2 ** p)
    acc = F.Acc(n)
    for a in terms:
        assert all(abs(frac(a[i + 1])) <= frac(F.ulp(a[i])) / 2 if a[i][0] else a[i + 1][0] == 0
                   for i in range(n - 1)), a
        acc.addx(a)
    x = acc.finish()
    Z = sum(sum(frac(v) for v in a) for a in terms)
    W = sum(abs(frac(a[0])) for a in terms)
    err = abs(Z - sum(frac(v) for v in x))
    bd = B.full_bound(n, p, th, len(terms), abs(Z), W, 'addx')
    return dict(err=err, Z=Z, W=W, x=x, units=err / (u ** n * abs(Z)), ratio=err / bd, levels=acc.s)


def save(terms, path):
    with open(path, 'w') as f:
        for a in terms:
            f.write(' '.join(f'{m}:{e}' for m, e in a) + '\n')


def load(path):
    out = []
    for line in open(path):
        out.append([tuple(int(v) for v in w.split(':')) for w in line.split()])
    return out


if __name__ == '__main__':
    p, n, K = (int(v) for v in sys.argv[1:4])
    absval = 'abs' in sys.argv[4:]
    terms = build(p, n, K, absval=absval)
    r = evaluate(terms, n, p)
    print(f'p={p} n={n} K={K}: err = {float(r["units"]):.6g} u^n |Z| = 2^{log2(r["units"]):.3f} u^n |Z|; '
          f'err/bound = {float(r["ratio"]):.4g}; W/|Z| - 1 = {float(r["W"] / abs(r["Z"]) - 1):.3g}')
    outs = [a for a in sys.argv[4:] if a != 'abs']
    if outs:
        save(terms, outs[0])
