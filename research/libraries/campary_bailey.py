"""CAMPARY's QD-like addition (baileyAdd_renorm, addition.h:91-118) against its stated bound
"relative error < 24 * 2^{-(prec-1)R}", on a hand-made binary64 input with R = 4.

x = (1, 2^-60, 2^-120, 2^-180 + 2^-232), y = (-1, -2^-60, 2^-174 + 2^-226, 2^-300): both ulp-nonoverlapping.
The exact sum 2^-120 + 2^-174 + 2^-180 + 2^-226 + 2^-232 + 2^-300 fits in four doubles, but the level builder rounds
f[4] = RN(2^-300 + 2^-232) and loses 2^-300. Controls: certifiedAdd (merge + renorm2L) on the same input must return
the exact sum, and a halved bound must still pass on a non-cancelling input. Exits non-zero if a check misbehaves.
"""
import sys
from fractions import Fraction

import ports as X
from ports import F, val, vsum


def d(m, e):
    return F.rnd(m, e)


def main():
    F.set_p(53)
    x = [d(1, 0), d(1, -60), d(1, -120), d((1 << 52) + 1, -232)]
    y = [d(-1, 0), d(-1, -60), d((1 << 52) + 1, -226), d(1, -300)]
    for v in (x, y):  # ulp-nonoverlapping: |v_{i+1}| <= ulp(v_i)
        for i in range(3):
            m, e = v[i]
            ulp = Fraction(2) ** (abs(m).bit_length() - 1 + e - 52)
            assert abs(val(v[i + 1])) <= ulp, (v, i)
    Z = vsum(x) + vsum(y)
    R = 4
    bound = 24 * Fraction(1, 2 ** (52 * R)) * abs(Z)
    out = X.cp_bailey_add_renorm(x, y, R)
    err = abs(Z - vsum(out))
    ratio = err / bound
    cert = X.cp_certified_add(x, y, R)
    cerr = abs(Z - vsum(cert))
    print("baileyAdd_renorm out:", [float(val(t)) for t in out])
    print("exact sum Z =", float(Z), " err =", float(err), " = 2^%d" % (err.numerator.bit_length() - err.denominator.bit_length()))
    print("bound 24*2^-208*|Z| =", float(bound), " ratio err/bound = %.4g (2^%.1f)" % (float(ratio), _log2(ratio)))
    print("certifiedAdd err =", float(cerr))
    ok = True
    if not ratio > 1:
        print("FAIL: the stated bound was not exceeded"); ok = False
    if cerr != 0:
        print("FAIL: control certifiedAdd did not return the exact sum"); ok = False
    # control: the Cray-style reading, 24 * 2^-208 * max(|x|, |y|), holds on this input
    cray = 24 * Fraction(1, 2 ** (52 * R)) * max(abs(vsum(x)), abs(vsum(y)))
    print("Cray-style reading: err / (24*2^-208*max(|x|,|y|)) = %.3g" % float(err / cray))
    if err > cray:
        print("FAIL: Cray-style reading exceeded too"); ok = False
    # control: a non-cancelling input must stay within a halved bound
    x2 = [d(1, 0), d(1, -60), d(1, -120), d(1, -180)]
    y2 = [d(3, -1), d(1, -61), d(1, -121), d(1, -181)]
    Z2 = vsum(x2) + vsum(y2)
    e2 = abs(Z2 - vsum(X.cp_bailey_add_renorm(x2, y2, R)))
    print("non-cancelling control err =", float(e2))
    if e2 > 12 * Fraction(1, 2 ** (52 * R)) * abs(Z2):
        print("FAIL: non-cancelling control exceeded half the bound"); ok = False
    print("PASS" if ok else "CHECK FAILED")
    return 0 if ok else 1


def _log2(r):
    import math
    return math.log2(r.numerator) - math.log2(r.denominator)


if __name__ == '__main__':
    sys.exit(main())
