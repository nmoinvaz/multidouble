"""The level accumulator of multidouble's OdAcc (src/od.rs), generalized to n parts, on the exact emulator fpemu.py.

State: n + 1 levels. add_prod(a, b) forms the n + 1 levels t of the product (alg::expand, fpemu.od_expand) and
deposits them (alg::acc_levels): dep(s, l, t_l) for l < n, then s_n <- RN(s_n + t_n). add(a) deposits the n parts
of a. finish() adds the levels in turn with od + f64, starting from (s_0, 0, ..., 0).
"""
import os
import sys
from fractions import Fraction as Q

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'paper'))
import fpemu as F  # noqa: E402

MUT = None  # control: 'acc_l3' drops the carry of level 3 on its first deposit (the crate's ACC_L3)


def val(x):
    m, e = x
    return Q(0) if m == 0 else Q(m) * Q(2) ** e


def acc_levels(s, t):
    n = len(s) - 1
    for l in range(min(len(t), n)):
        if l == 3 and MUT == 'acc_l3':
            s[3], _ = F.two_sum(s[3], t[3])
            continue
        F.dep(s, l, t[l])
    if len(t) > n:
        s[n] = F.add(s[n], t[n])


def finish(s):
    n = len(s) - 1
    r = [s[0]] + [F.PZ] * (n - 1)
    for l in range(1, n + 1):
        r = F.od_add_f(r, s[l])
    return r


def fresh(n):
    return [F.PZ] * (n + 1)
