"""Controls for the bound checks: each check must fire on a known-bad algorithm and stay quiet on a known-good one.

usage: controls.py [P] [TRIALS]    exits non-zero when a control misbehaves
"""
import random
import sys
from fractions import Fraction

import attack as A
import ports as X
from ports import F, vsum


def greedy4(a, b, kind):
    """known-good: the exact result rounded greedily to four parts (error <= u^4 |Z| (1 + O(u)))"""
    Z = A.exact(kind, a, b)
    return A.expand(Z, 4) if Z != 0 else [F.PZ] * 4


def broken_add(a, b):
    """known-bad: QD sloppy add with the error of a2 + b2 dropped (t2 = 0)"""
    s0, t0 = X.qd_two_sum(a[0], b[0])
    s1, t1 = X.qd_two_sum(a[1], b[1])
    s2, t2 = X.qd_two_sum(a[2], b[2])
    s3, t3 = X.qd_two_sum(a[3], b[3])
    t2 = F.PZ
    s1, t0 = X.qd_two_sum(s1, t0)
    s2, t0, t1 = X.qd_three_sum(s2, t0, t1)
    s3, t0, t2 = X.qd_three_sum2(s3, t0, t2)
    t0 = F.add(F.add(t0, t1), t3)
    return X.qd_renorm5(s0, s1, s2, s3, t0)


def broken_mul(a, b):
    """known-bad: QD's accurate mul with the a3 b0 product removed"""
    a2 = list(a)
    out = X.qd_accurate_mul(a2, b)
    # remove a3*b0 exactly by subtracting it from the result's last part (rounded), a gross change
    return out[:3] + [F.sub(out[3], F.mul(a[3], b[0]))]


def run(p, trials):
    F.set_p(p)
    rng = random.Random(11)
    fails = []
    cases = [
        ('qd_sloppy_add', 'add', broken_add, True),
        ('qd_sloppy_add', 'add', lambda a, b: greedy4(a, b, 'add'), False),
        ('qd_accurate_mul', 'mul', broken_mul, True),
        ('qd_accurate_mul', 'mul', lambda a, b: greedy4(a, b, 'mul'), False),
        ('cp_bailey_add_renorm', 'add', lambda a, b: greedy4(a, b, 'add'), False),
        ('cp_bailey_add_renorm', 'add', X.cp_certified_add.__call__ if False else
         (lambda a, b: X.cp_certified_add(a, b, 4)), False),
    ]
    for name, kind, fn, must_fire in cases:
        spec = dict(A.OPS[name])
        spec['fn'] = fn
        worst = Fraction(0)
        for _ in range(trials):
            a, b = A.rand_pair(rng, p, 4, kind)
            if any(x[0] == 0 for x in a) and kind == 'mul':
                pass
            r = A.run_case(spec, a, b, p)[0]
            worst = max(worst, r)
        fired = worst > 1
        ok = fired == must_fire
        print(f"control {name} with {'bad' if must_fire else 'good'} algorithm {fn.__doc__.split(':')[0] if fn.__doc__ else 'certifiedAdd'}"
              f": worst ratio {float(worst):.3g}, fired={fired}, {'OK' if ok else 'CONTROL FAILED'}")
        if not ok:
            fails.append(name)
    return fails


if __name__ == '__main__':
    p = int(sys.argv[1]) if len(sys.argv) > 1 else 53
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
    fails = run(p, trials)
    sys.exit(1 if fails else 0)
