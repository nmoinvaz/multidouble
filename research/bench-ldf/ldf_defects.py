#!/usr/bin/env python3
"""Exact errors of the results ldf_defects prints (fractions; units of u^n with u = 2^-53).

  ldf_defects.py < output of ldf_defects and ldf_defects_ieee
"""
import sys
from fractions import Fraction as F

U = F(1, 1 << 53)


def val(parts):
    return sum((F(float.fromhex(p)) for p in parts), F(0))


QX = ["-0x1.2069d768735c3p-8", "-0x1.e6fe6600c0040p-63", "-0x1.48b21f064d551p-117", "0x1.9a6511e87ea76p-171"]
QY = ["0x1.20f8a227c3e64p-8", "0x1.a4becffadf20ap-65", "-0x1.faa58966080b5p-119", "0x1.fec036f4d4027p-173"]
IU = ["-0x1.e7c3a633d8879p+0", "-0x1.90080fd14ebd0p-54", "-0x1.f4a4906597005p-113", "0x1.89cf65a8383b5p-167"]
IV = ["-0x1.ed387f10e504bp+2", "0x1.55fae5265b70ep-52", "0x1.4f62e25e56f0ap-106", "-0x1.f5b32cc80ae9bp-163"]
EXACT = {
    "dd_add": (F(1) + F(2) ** -54 + F(2) ** -106) + (F(-1) + 3 * F(2) ** -108),
    "qd_add_accurate": val(QX) + val(QY),
    "ieee_mode_add": val(IU) + val(IV),
}
for line in sys.stdin:
    w = line.split()
    if w and w[0] in EXACT:
        e = EXACT[w[0]]
        n = 2 if w[0].startswith("dd") else 4
        err = abs(val(w[1:]) - e) / abs(e)
        print("%-16s relative error %.3g = %.3g u^%d" % (w[0], float(err), float(err / U ** n), n))
    else:
        print(line.rstrip())
