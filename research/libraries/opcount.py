"""Operation counts of four-part multiplications and additions, and their error on the paper's attaining inputs.

Counts are calls of the emulated hardware operations (add or sub, mul, fma, div, magnitude compare) on one generic
input; branches that skip work on zero parts are not taken on it. Errors are in units of u^4 |Z| at p = 53.
"""
import math
from fractions import Fraction

import ports as X
from ports import F, vsum

COUNT = {}


def wrap(mod, name, key):
    f = getattr(mod, name)

    def g(*args):
        COUNT[key] = COUNT.get(key, 0) + 1
        return f(*args)
    setattr(mod, name, g)


for mod in (F, X):
    for name, key in (('add', 'add'), ('mul', 'mul'), ('fma', 'fma'), ('div', 'div')):  # sub calls add
        if hasattr(mod, name):
            wrap(mod, name, key)
wrap(F, 'abs_ge', 'cmp')
X.fabs_gt = (lambda f: (lambda a, b: (COUNT.__setitem__('cmp', COUNT.get('cmp', 0) + 1), f(a, b))[1]))(X.fabs_gt)


def count(fn, a, b):
    COUNT.clear()
    fn(a, b)
    return dict(COUNT)


def main():
    F.set_p(53)
    u = Fraction(1, 2 ** 53)
    # a generic input: every part nonzero, full mantissas
    a = [F.rnd((1 << 52) | 0x5a5a5a5a5a5a5, -52), F.rnd(-((1 << 52) | 0x3c3c3c3c3c3c3), -52 - 54),
         F.rnd((1 << 52) | 0x1234567891234, -52 - 108), F.rnd((1 << 52) | 0x4321987654321, -52 - 162)]
    b = [F.rnd((1 << 52) | 0x2b2b2b2b2b2b2, -52), F.rnd((1 << 52) | 0x7171717171717, -52 - 55),
         F.rnd(-((1 << 52) | 0x0f0f0f0f0f0f0), -52 - 109), F.rnd((1 << 52) | 0x1111122222333, -52 - 163)]
    one = F.rnd(1, 0)
    U = [F.rnd(1, -53 * k) for k in range(5)]  # 1, u, u^2, u^3, u^4
    # the paper's attaining inputs (Proposition sharp): (1, u, u^2, 0) x (1, 0, 0, u^3) and (1, u, u^2, u^3) + (u^4)
    ma, mb = [one, U[1], U[2], F.PZ], [one, F.PZ, F.PZ, U[3]]
    aa, ab = [one, U[1], U[2], U[3]], [U[4], F.PZ, F.PZ, F.PZ]
    muls = [('paper MUL (multidouble od, TwoSum renorm)', lambda x, y: F.od_mul(x, y, 'two')),
            ('paper MUL, branch + Fast2Sum (multidouble 4.8.2)', lambda x, y: F.od_mul(x, y, 'branch')),
            ('QD 2.3.24 accurate_mul', X.qd_accurate_mul),
            ('QD 2.3.24 sloppy_mul (default)', X.qd_sloppy_mul),
            ('libQD3 bf_mul (Kouya Alg. 14, QD_BF)', X.l3_bf_mul),
            ('CAMPARY baileyMul_renorm', lambda x, y: X.cp_bailey_mul_renorm(x, y, 4))]
    adds = [('paper ADD (multidouble od, TwoSum renorm)', lambda x, y: F.od_add(x, y, 'two')),
            ('QD 2.3.24 sloppy_add (default)', X.qd_sloppy_add),
            ('QD 2.3.24 ieee_add', X.qd_ieee_add),
            ('libQD3 bf_add (Kouya Alg. 13, QD_BF)', X.l3_bf_add),
            ('CAMPARY certifiedAdd', lambda x, y: X.cp_certified_add(x, y, 4)),
            ('CAMPARY baileyAdd_renorm', lambda x, y: X.cp_bailey_add_renorm(x, y, 4))]
    print("| multiplication | add/sub | mul | fma | cmp | error on (1,u,u^2,0)x(1,0,0,u^3), units of u^4|Z| |")
    print("|---|---|---|---|---|---|")
    for name, fn in muls:
        c = count(fn, a, b)
        Z = vsum(ma) * vsum(mb)
        e = abs(Z - vsum(fn(ma, mb))) / (u ** 4 * abs(Z))
        print(f"| {name} | {c.get('add', 0)} | {c.get('mul', 0)} | {c.get('fma', 0)} | {c.get('cmp', 0)} | {float(e):.4f} |")
    print()
    print("| addition | add/sub | cmp | error on (1,u,u^2,u^3)+(u^4,0,0,0), units of u^4|Z| |")
    print("|---|---|---|---|")
    for name, fn in adds:
        c = count(fn, a, b)
        Z = vsum(aa) + vsum(ab)
        e = abs(Z - vsum(fn(aa, ab))) / (u ** 4 * abs(Z))
        print(f"| {name} | {c.get('add', 0)} | {c.get('cmp', 0)} | {float(e):.4f} |")


if __name__ == '__main__':
    main()
