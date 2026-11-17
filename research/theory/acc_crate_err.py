"""Independent of fpemu: the exact error of a result (eight f64 bit patterns, e.g. multidouble's OdAcc output from
acc_check/) against the exact sum of the terms of a file (one term per line, eight bit patterns in hex).
usage: acc_crate_err.py terms.txt "result hex parts"     prints |Z - x| / (u^8 |Z|), |Z - x| / (u^8 W), W / |Z| - 1"""
import math
import struct
import sys
from fractions import Fraction as Q


def f(h):
    return Q(*struct.unpack('<d', struct.pack('<Q', int(h, 16)))[0].as_integer_ratio())


Z = Q(0)
W = Q(0)
for line in open(sys.argv[1]):
    t = [f(h) for h in line.split()]
    Z += sum(t)
    W += abs(t[0])
x = sum(f(h) for h in sys.argv[2].split())
u8 = Q(1, 2 ** 424)
err = abs(Z - x)
print(f'|Z - x| / (u^8 |Z|) = {float(err / (u8 * abs(Z))):.6g} = 2^{math.log2(err / (u8 * abs(Z))):.3f}; '
      f'|Z - x| / (u^8 W) = {float(err / (u8 * W)):.6g}; W/|Z| - 1 = 2^{math.log2(abs(W / abs(Z) - 1)):.1f}')
