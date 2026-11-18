"""The sloppy multiply (`OD::sloppy_mul`) on the exact emulator `fpemu.py`, written from its description in
`src/od.rs`'s module doc, at any precision p and number of parts n, against the bound of `sloppy_consts.py`.

usage: sloppy_emu.py [mode]   from this folder
  bound    hill climbs at p = 6..16 and n = 3..8 and at p = 53, n = 8: every error within the bound at its p and n
  bits     the worst pair of the crate's hill climb (`od_tests::od_sloppy_worst_case`): the emulator gives the crate's
           eight parts bit for bit and the same error, 581.97 u^8 |a_0 b_0|
  control  the control of `bound`: with the carries out of level n-2 dropped (the crate's `mutate::SLOPPY_C6`), more
           than half of 60 random pairs at the top of the ladder (p = 53, n = 8) exceed the bound
Each prints PASS or FAIL and exits 1 on FAIL. Errors are |ab - x| / (u^n |a_0 b_0|).
"""
import random
import sys
from fractions import Fraction as Fr

import fpemu as F
from sloppy_consts import sloppy_consts

DROP_CARRY = False


def dep(s, l, t):
    """fpemu's dep on the sloppy levels; with DROP_CARRY the carry out of level n-2 is dropped"""
    if DROP_CARRY and l <= len(s) - 2:
        e = t
        for m in range(l, len(s) - 1):
            s[m], e = F.two_sum(s[m], e)
        return
    F.dep(s, l, t)


def expand_sloppy(a, b):
    """n levels: 0..n-2 with two-sum carries, n-1 plain; the products of orders n and n-1 by one FMA chain (smallest
    first), then the errors of a_0 b_j, then rows 1..n-2"""
    n = len(a)
    s = [F.PZ] * n
    e = [F.PZ] * (n - 1)
    for j in range(n - 1):
        s[j], e[j] = F.two_prod(a[0], b[j])
    acc = F.mul(a[1], b[n - 1])
    for i in range(2, n):
        acc = F.fma(a[i], b[n - i], acc)
    for i in range(0, n):
        acc = F.fma(a[i], b[n - 1 - i], acc)
    s[n - 1] = acc
    for j in range(n - 1):
        dep(s, j + 1, e[j])
    for i in range(1, n - 1):
        for j in range(0, n - 1 - i):
            p, pe = F.two_prod(a[i], b[j])
            dep(s, i + j, p)
            dep(s, i + j + 1, pe)
    return s


def sloppy_mul(a, b):
    return F.renorm(expand_sloppy(a, b), len(a))


def val(x):
    m, e = x
    return Fr(0) if m == 0 else Fr(m) * Fr(2) ** e


def ulp(x):
    m, e = x
    return Fr(2) ** (abs(m).bit_length() + e - F.P)


def flt(q):
    """the dyadic q (exactly representable by construction) as a p-bit float"""
    if q == 0:
        return F.PZ
    d = q.denominator
    assert d & (d - 1) == 0
    return F.rnd(q.numerator, -(d.bit_length() - 1))


def top_part(r, prev):
    m = Fr(1) if r.randrange(8) == 0 else Fr(r.randrange(1 << (F.P - 1), 1 << F.P), 1 << F.P)
    return flt((-1 if r.randrange(2) else 1) * m * ulp(prev))


def topped(r, n):
    """x_0 in [1, 2), x_i = s m ulp(x_(i-1)) with m in [1/2, 1] (as od_tests' `topped`)"""
    xs = [flt(Fr(r.randrange(1 << (F.P - 1), 1 << F.P), 1 << (F.P - 1)))]
    for _ in range(1, n):
        xs.append(top_part(r, xs[-1]))
    return xs


def on_ladder(a):
    a0 = abs(val(a[0]))
    return all(abs(val(a[i])) <= Fr(2, 1 << F.P) ** i * a0 for i in range(1, len(a)))


def err(a, b):
    n = len(a)
    z = sum(val(x) for x in a) * sum(val(y) for y in b)
    x = sloppy_mul(a, b)
    return abs(z - sum(val(t) for t in x)) / (Fr(1, 1 << F.P) ** n * abs(val(a[0]) * val(b[0])))


def climb(r, n, starts, steps):
    """hill climb on err from topped pairs: one part changed at a time (sign, zero, or a new top part)"""
    best = Fr(0)
    for _ in range(starts):
        a, b = topped(r, n), topped(r, n)
        e = err(a, b)
        for _ in range(steps):
            a2, b2 = list(a), list(b)
            w = a2 if r.randrange(2) else b2
            i = r.randrange(1, n)
            k = r.randrange(6)
            if k == 0:
                w[i] = F.neg(w[i])
            elif k == 1:
                w[i] = F.PZ
            elif w[i - 1][0] != 0:
                w[i] = top_part(r, w[i - 1])
            if not (on_ladder(a2) and on_ladder(b2)):
                continue
            e2 = err(a2, b2)
            if e2 > e:
                a, b, e = a2, b2, e2
        best = max(best, e)
    return best


def bound(p, n):
    s = sloppy_consts(n, 2, Fr(1, 1 << p))
    return s['R'] + s['drop'] * Fr(1, 1 << p)


def main(mode):
    global DROP_CARRY
    r = random.Random(7)
    if mode == 'bound':
        ok = True
        for p, n, starts, steps in [(6, 3, 6, 300), (8, 3, 6, 300), (6, 4, 6, 300), (8, 4, 6, 300), (10, 4, 6, 300),
                                    (8, 5, 6, 300), (12, 5, 6, 300), (10, 6, 6, 400), (12, 7, 4, 400),
                                    (16, 8, 4, 400), (53, 8, 4, 400)]:
            F.set_p(p)
            e, bd = climb(r, n, starts, steps), bound(p, n)
            print(f'p {p:2d} n {n}: worst found {float(e):9.3f}, bound {float(bd):.4e}, ratio {float(e / bd):.2e}')
            ok &= e <= bd
        return ok
    if mode == 'bits':
        F.set_p(53)
        a = [13880425436936531171, 13643404232887038185, 4182921161570140560, 3944219206860732546,
             12926963581260454180, 3465845960584700914, 0, 12240662596661725798]
        b = [13784591529929041515, 4320060963810580716, 4083962236838454907, 3843288925856740887,
             3607133674073714068, 3378501570112196583, 12366683244327917580, 12124319821763928267]
        want = [4611353654102344903, 13591716506493445106, 13340987550089454146, 13097440973751722636,
                3623390517086358246, 12604289439650886032, 3136861571265889385, 12115119624030257152]
        A, B = [F.from_bits(x) for x in a], [F.from_bits(x) for x in b]
        got = [F.to_bits(x) for x in sloppy_mul(A, B)]
        e = err(A, B)
        print(f'bits equal to the crate\'s: {got == want}; error {float(e):.4f}')
        return got == want and abs(e - Fr(58197, 100)) < 1
    if mode == 'control':
        F.set_p(53)
        bd = bound(53, 8)
        DROP_CARRY = True
        past = sum(err(topped(r, 8), topped(r, 8)) > bd for _ in range(60))
        print(f'carries out of level 6 dropped: {past} of 60 past the bound')
        return past > 30
    raise SystemExit(__doc__)


if __name__ == '__main__':
    ok = main(sys.argv[1] if len(sys.argv) > 1 else 'bound')
    print('PASS' if ok else 'FAIL')
    sys.exit(0 if ok else 1)
