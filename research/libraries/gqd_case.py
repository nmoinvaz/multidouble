"""GQD (gqd_basic.cu:84) and QD up to 2.3.20 renormalize with `s2 += c4` where QD 2.3.21 and later keep the error,
s2 = quick_two_sum(s2, c4, s3). On the input below GQD's addition returns three parts and loses 2^-161 relative,
where QD 2.3.24's sloppy_add (the same code apart from the renorm) is exact.

Checks (exit status 1 if one misbehaves): 1. GQD's relative error exceeds 2^-210 on this input; 2. control, quiet:
QD 2.3.24's sloppy_add meets 2^-210 on it; 3. control: both stay within QD's documented Cray-style bound
2 eps_qd max(|a|, |b|) = 2^-210 max(|a|, |b|), which the loss does not breach because the sum cancels.
"""
import math
import struct
import sys
from fractions import Fraction

import attack as A
import ports as X
from ports import F, vsum


def h(s):
    return F.from_bits(struct.unpack('<Q', struct.pack('<d', float.fromhex(s)))[0])


A_HEX = ['0x1.0000000000000p+0', '0x1.2193c232f8aa6p-54', '0x1.308f0b7a1fd6bp-108', '0x1.2a646bd3a48d3p-162']
B_HEX = ['-0x1.ffffffffffffcp-1', '0x1.cf45b08369fbep-55', '-0x1.6b1ee54533d02p-109', '0x1.6d245fc56b872p-163']


def main():
    F.set_p(53)
    a = [h(s) for s in A_HEX]
    b = [h(s) for s in B_HEX]
    assert A.expand(vsum(a), 4) == a and A.expand(vsum(b), 4) == b, "operands not in QD normal form"
    Z = vsum(a) + vsum(b)
    M = max(abs(vsum(a)), abs(vsum(b)))
    g = X.gqd_add(a, b)
    q = X.qd_sloppy_add(a, b)
    rg = abs(Z - vsum(g)) / abs(Z)
    rq = abs(Z - vsum(q)) / abs(Z)
    print("a   =", A_HEX)
    print("b   =", B_HEX)
    print("gqd =", [A.hexs(t) for t in g])
    print("qd  =", [A.hexs(t) for t in q])
    print("GQD rel err 2^%.2f; QD 2.3.24 sloppy_add rel err %s" % (math.log2(rg), "2^%.2f" % math.log2(rq) if rq else "0"))
    cray_g = abs(Z - vsum(g)) / (Fraction(1, 2 ** 210) * M)
    print("GQD error / (2^-210 max(|a|,|b|)) = %.3g" % float(cray_g))
    ok = rg > Fraction(1, 2 ** 210) and rq <= Fraction(1, 2 ** 210) and cray_g <= 1
    print("PASS" if ok else "CHECK FAILED")
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
