"""Theorem thm:acc and Lemma lem:acc against exact arithmetic, on random inputs satisfying the hypotheses.

For each case: the error |Z - sum x| against the theorem's full bound; the levels |s_m| after every two-sum or
rounding against S_m(k) (Lemma (a), k the current deposit); the signed sum of the rounding errors at level n against
Lemma (b)'s bound; and |Z - S| against E_lev + E_prod. 'excess' is (err - u^n |Z|) / (second term), which is
at most 1 exactly when err <= bound.

python3 bound_test.py SECONDS [seed] [control]
control: 'half' (every bound halved), 'drop' (level-3 carry dropped), 'sign' (two-sum's error with a wrong sign); each
must report failures.
"""
from fractions import Fraction as Fr
import math
import random
import sys
import time

import bound as B
import reffp as F
from gen import operand

CFG = [(8, 2), (8, 3), (8, 4), (10, 2), (10, 3), (10, 4), (12, 2), (12, 3), (12, 4), (16, 3), (53, 8)]

_cache = {}


def consts(n, p, th, K, kind):
    key = (n, p, th, K, kind)
    if key not in _cache:
        u = Fr(1, 2 ** p)
        tau, R, Dl = B.taus(n, u, Fr(th), kind)
        S, beta = B.S_levels(n, u, K, tau)
        El = B.E_lev(n, u, K, tau)
        c, _ = B.second_term(n, p, th, K, kind)
        _cache[key] = (S, El, (R + Dl) * u ** (n + 1), c)
    return _cache[key]


class Inst:
    """the accumulator with the checks of Lemma lem:acc at every level change"""

    def __init__(self, n, S, W):
        self.n, self.S, self.W = n, S, W
        self.s = [F.ZERO] * (n + 1)
        self.k = 0
        self.Elev = Fr(0)
        self.lev_ratio = 0.0

    def _chk(self, m):
        v = abs(F.frac(self.s[m]))
        if v:
            r = v / (self.S[m] * self.W)
            self.lev_ratio = max(self.lev_ratio, float(r))

    def _round_n(self, e):
        n = self.n
        exact = F.frac(self.s[n]) + F.frac(e)
        self.s[n] = F.add(self.s[n], e)
        self.Elev += exact - F.frac(self.s[n])
        self._chk(n)

    def dep(self, l, t):
        n = self.n
        e = t
        for m in range(l, n):
            self.s[m], e = F.two_sum(self.s[m], e)
            if 'dep_drop_l3' in F.MUT and m == 3:
                e = F.ZERO
            self._chk(m)
        self._round_n(e)

    def deposit(self, t):
        self.k += 1
        for l in range(self.n):
            self.dep(l, t[l])
        if len(t) == self.n + 1:
            self._round_n(t[self.n])

    def finish(self):
        n = self.n
        r = [self.s[0]] + [F.ZERO] * (n - 1)
        for l in range(1, n + 1):
            r = F.addf(r, self.s[l])
        return r


def run_case(terms, n, p, th, kind):
    """terms: list of ('P', a, b) or ('X', a). Returns dict of ratios."""
    K = len(terms)
    S, El, Ep1, c = consts(n, p, th, K, kind)
    u = Fr(1, 2 ** p)
    W = sum(abs(F.frac(t[1][0]) * F.frac(t[2][0])) if t[0] == 'P' else abs(F.frac(t[1][0])) for t in terms)
    Z = Fr(0)
    T = Fr(0)
    acc = Inst(n, S, W)
    for t in terms:
        if t[0] == 'P':
            va = sum(F.frac(x) for x in t[1])
            vb = sum(F.frac(x) for x in t[2])
            Z += va * vb
            lev = F.mul_levels(t[1], t[2])
        else:
            Z += sum(F.frac(x) for x in t[1])
            lev = t[1]
        T += sum(F.frac(x) for x in lev)
        acc.deposit(lev)
    x = acc.finish()
    Ssum = sum(F.frac(v) for v in acc.s)
    ident = Ssum == T - acc.Elev  # Lemma (b)'s identity, exactly
    err = abs(Z - sum(F.frac(v) for v in x))
    bound = u ** n * abs(Z) + c * u ** n * W
    return dict(K=K, W=W, Z=Z, err=err, bound=bound, ratio=err / bound, lev=acc.lev_ratio,
                elev=abs(acc.Elev) / (El * W), zs=abs(Z - Ssum) / ((El + Ep1) * W),
                xs=(err - u ** n * abs(Z)) / (c * u ** n * W), ident=ident)


def make_terms(rng, n, p, K, th, kind, signs):
    terms = []
    for i in range(K):
        e0 = rng.randrange(-3, 3) if rng.random() < 0.8 else rng.randrange(-2 * p, 2)
        sg = 1 if signs == 'pos' else None
        if kind == 'prod' or (kind == 'mixed' and rng.random() < 0.6):
            terms.append(('P', operand(rng, n, th, e0, sign=sg), operand(rng, n, th, rng.randrange(-2, 2), sign=1)))
        else:
            terms.append(('X', operand(rng, n, th, e0, sign=sg)))
    if kind == 'mixed' and all(t[0] == 'P' for t in terms):
        pass
    return terms


def sharp_terms(n, p):
    """ADDX (1, u, ..., u^(n-1)) then ADDX (u^n, 0, ...): FINISH's last ADDF errs by u^n (Prop. sharp(b))"""
    a = [(1, -p * i) for i in range(n)]
    b = [(1, -p * n)] + [F.ZERO] * (n - 1)
    return [('X', a), ('X', b)]


def main():
    secs = float(sys.argv[1]) if len(sys.argv) > 1 else 60
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    control = sys.argv[3] if len(sys.argv) > 3 else None
    if control == 'drop':
        F.MUT.add('dep_drop_l3')
    if control == 'sign':
        F.MUT.add('two_sum_sign')
    scale = Fr(1, 2) if control == 'half' else Fr(1)
    rng = random.Random(seed)
    stats = {}
    t0 = time.time()
    it = 0
    while time.time() - t0 < secs:
        p, n = CFG[it % len(CFG)]
        it += 1
        F.setp(p)
        u = Fr(1, 2 ** p)
        kmax = int(Fr(9, 10) / ((n + 1) * u))
        kmax = min(kmax, 300 if p > 12 else 2000)
        if p == 53:
            kmax = 64
        K = max(1, int(math.exp(rng.uniform(0, math.log(kmax)))))
        kind = rng.choice(('prod', 'addx', 'mixed'))
        th = rng.choice((1, 2))
        signs = rng.choice(('pos', 'rand'))
        cat = 'rand'
        if rng.random() < 0.05:
            terms, kind, th, cat = sharp_terms(n, p), 'addx', 1, 'sharp'
        else:
            terms = make_terms(rng, n, p, K, th, kind, signs)
        r = run_case(terms, n, p, th, kind)
        st = stats.setdefault((p, n, cat), dict(cases=0, terms=0, fail=0, ratio=0.0, lev=0.0, elev=0.0, zs=0.0,
                                                xs=-1e9, Kmax=0))
        st['cases'] += 1
        st['terms'] += r['K']
        st['Kmax'] = max(st['Kmax'], r['K'])
        if r['err'] > scale * r['bound']:
            st['fail'] += 1
        for key in ('ratio', 'lev', 'elev', 'zs', 'xs'):
            st[key] = max(st[key], float(r[key]))
        if r['lev'] > scale or r['elev'] > scale or r['zs'] > scale or not r['ident']:
            st['fail'] += 1
        st['bndfail'] = st.get('bndfail', 0) + (r['err'] > scale * r['bound'])
    tot_fail = 0
    print(f'seed {seed}, control {control}, {secs:.0f} s')
    print(f"{'p':>3} {'n':>2} {'cat':>5} {'cases':>6} {'terms':>7} {'Kmax':>5} {'fail':>5} {'err/bound':>10} "
          f"{'excess':>8} {'|s|/S':>8} {'Elev/bd':>8} {'|Z-S|/bd':>8} {'err>bd':>6}")
    for (p, n, cat), st in sorted(stats.items()):
        tot_fail += st['fail']
        print(f"{p:>3} {n:>2} {cat:>5} {st['cases']:>6} {st['terms']:>7} {st['Kmax']:>5} {st['fail']:>5} "
              f"{st['ratio']:>10.3g} {st['xs']:>8.3g} {st['lev']:>8.3g} {st['elev']:>8.3g} {st['zs']:>8.3g} "
              f"{st['bndfail']:>6}")
    print('failures', tot_fail)
    if control and tot_fail == 0:
        print('CONTROL DID NOT FIRE')
        sys.exit(1)
    if not control and tot_fail:
        sys.exit(1)


if __name__ == '__main__':
    main()
