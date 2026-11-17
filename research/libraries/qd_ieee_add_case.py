"""QD 2.3.24's IEEE-style quad-double addition (qd_real::ieee_add, include/qd/qd_inline.h:286-336) against the bound
its authors state for it, |delta| <= 2 eps_qd "or so" with eps_qd = 2^-211 (Hida, Li and Bailey 2001, Sec. 3.2).

The default build uses sloppy_add; ieee_add is selected by --enable-ieee-add (QD_IEEE_ADD), and MPLAPACK builds its
QD (libQD3 1.6.0) with QD_ENABLE_IEEE_ADD=ON.

Checks, each of which must hold (exit status 1 otherwise):
  1. on the input below, ieee_add's relative error exceeds 4u^4 = 2^-210 (the bound fires);
  2. control, quiet: the exact sum rounded greedily to four doubles meets the bound on the same input;
  3. control, quiet: ieee_add with the dropped accumulator word v passed to a five-term renorm meets it;
  4. control, quiet: ieee_add meets the bound on 2000 random non-cancelling inputs whose parts do not interleave;
  5. on A2 (A with its last part one ulp larger), the upstream fix of the k == 3 case (BL-highprecision/QD 92d99c8)
     still exceeds the bound, because the loop now ends with k == 4 and drops the accumulator (u, v);
  6. control, quiet: our repair ports.qd_ieee_add_fix2 meets the bound on A and A2.
"""
import random
import struct
import sys
from fractions import Fraction

import attack as A
import ports as X
from ports import F, val, vsum


def h(s):
    return F.from_bits(struct.unpack('<Q', struct.pack('<d', float.fromhex(s)))[0])


A_HEX = ['-0x1.10b3152f6f89ap+0', '-0x1.fffffffffffffp-56', '0x1.dbf40e3873925p-110', '0x1.bd32b707ee75cp-166']
A2_HEX = A_HEX[:3] + ['0x1.bd32b707ee75dp-166']
B_HEX = ['-0x1.061d2017c3fddp+0', '0x1.f2c626c6a92efp-54', '0x1.db856994e5f1ep-110', '0x1.8fb8e95ff5794p-164']


def ieee_add_keep_v(a, b):
    """qd_inline.h:286-336 with one change: the accumulator's second word is renormalized instead of dropped"""
    i = j = k = 0
    x = [F.PZ] * 4
    fg = X.fabs_gt
    if fg(a[i], b[j]):
        u = a[i]; i += 1
    else:
        u = b[j]; j += 1
    if fg(a[i], b[j]):
        v = a[i]; i += 1
    else:
        v = b[j]; j += 1
    u, v = X.qd_quick_two_sum(u, v)
    extra = F.PZ
    while k < 4:
        if i >= 4 and j >= 4:
            x[k] = u
            if k < 3:
                k += 1
                x[k] = v
            else:
                extra = v
            break
        if i >= 4:
            t = b[j]; j += 1
        elif j >= 4:
            t = a[i]; i += 1
        elif fg(a[i], b[j]):
            t = a[i]; i += 1
        else:
            t = b[j]; j += 1
        s, u, v = X.qd_quick_three_accum(u, v, t)
        if s[0] != 0:
            x[k] = s
            k += 1
    for kk in range(i, 4):
        x[3] = F.add(x[3], a[kk])
    for kk in range(j, 4):
        x[3] = F.add(x[3], b[kk])
    return X.qd_renorm5(*x, extra)


def rel(out, Z):
    return abs(Z - vsum(out)) / abs(Z)


def main():
    F.set_p(53)
    a = [h(s) for s in A_HEX]
    b = [h(s) for s in B_HEX]
    Z = vsum(a) + vsum(b)
    bound = Fraction(4, 2 ** 212)  # 2 eps_qd = 2^-210
    out = X.qd_ieee_add(a, b)
    r = rel(out, Z)
    ok = True
    print("a =", A_HEX)
    print("b =", B_HEX)
    print("ieee_add =", [A.hexs(t) for t in out])
    print("exact Z  =", [A.hexs(t) for t in A.expand(Z, 4)], "(greedy four-double rounding)")
    print("rel err = %.4e = 2^%.2f, bound 2^-210, ratio 2^%.2f" % (float(r), _l2(r), _l2(r / bound)))
    if not r > bound:
        print("FAIL 1: the bound did not fire"); ok = False
    rg = rel(A.expand(Z, 4), Z)
    print("control greedy rounding: rel err 2^%.2f" % _l2(rg) if rg else "control greedy rounding: exact")
    if rg > bound:
        print("FAIL 2"); ok = False
    rk = rel(ieee_add_keep_v(a, b), Z)
    print("control ieee_add keeping v: rel err", "2^%.2f" % _l2(rk) if rk else "0 (exact)")
    if rk > bound:
        print("FAIL 3"); ok = False
    rng = random.Random(1)
    worst = Fraction(0)
    for _ in range(2000):
        x = A.expand(A.rand_value(rng, 53, 4), 4)
        y = A.expand(abs(A.rand_value(rng, 53, 4)) * Fraction(1, 1 << rng.randint(60, 400)), 4)
        if x[0][0] == 0 or y[0][0] == 0:
            continue
        if x[0][0] < 0:
            y = [F.neg(t) for t in y]  # same sign, and y lies entirely below x's parts' range or far below
        Zr = vsum(x) + vsum(y)
        worst = max(worst, rel(X.qd_ieee_add(x, y), Zr))
    print("control random separated inputs: worst rel err 2^%.2f" % _l2(worst) if worst else "control random: exact")
    if worst > bound:
        print("FAIL 4"); ok = False
    a2 = [h(s) for s in A2_HEX]
    Z2 = vsum(a2) + vsum(b)
    rf = rel(X.qd_ieee_add_fixed(a2, b), Z2)
    print("A2 =", A2_HEX)
    print("upstream fix 92d99c8 on A2: rel err 2^%.2f, ratio 2^%.2f" % (_l2(rf), _l2(rf / bound)))
    if not rf > bound:
        print("FAIL 5"); ok = False
    for name, x in (("A", a), ("A2", a2)):
        Zx = vsum(x) + vsum(b)
        r2 = rel(X.qd_ieee_add_fix2(x, b), Zx)
        print("control fix2 on %s: rel err %s" % (name, "2^%.2f" % _l2(r2) if r2 else "0"))
        if r2 > bound:
            print("FAIL 6"); ok = False
    print("PASS" if ok else "CHECK FAILED")
    return 0 if ok else 1


def _l2(r):
    import math
    return math.log2(r.numerator) - math.log2(r.denominator)


if __name__ == '__main__':
    sys.exit(main())
