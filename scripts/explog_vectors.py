"""Planted truth for the reference of tests/explog.rs: e^x to 700 significant digits from Python's decimal module
(libmpdec, correctly rounded), for exact sums x of f64 parts. A line is the parts' bits in hex, a space, and the
digits of e^x as d.ddd...e+NNN. usage: python3 scripts/explog_vectors.py > tests/data/explog_vectors.txt"""
import struct
from decimal import Context, Decimal
from fractions import Fraction as Fr

EXACT = Context(prec=3000, Emin=-999999, Emax=999999)  # the parts' sum is exact at this precision
OUT = Context(prec=710, Emin=-999999, Emax=999999)


def bits(x):
    return '%016x' % struct.unpack('<Q', struct.pack('<d', x))[0]


def greedy(v, n):
    out = []
    for _ in range(n):
        c = v.numerator / v.denominator if v else 0.0
        out.append(c)
        v -= Fr(c)
    return out


CASES = [
    [1.0], [-1.0], [0.5], [2.0 ** -30], [-(2.0 ** -600)], [1e-22], [100.0], [-700.0], [709.5], [-744.4],
    [0.6931471805599453, 2.3190468138462996e-17], [-0.34657359027997264, 0.0, 2.0 ** -120],
    greedy(Fr(31415926535897932384626433832795, 10 ** 31), 8),     # pi to 31 digits, as eight parts
    greedy(Fr(-271828182845904523536, 10 ** 20) * 100, 8),        # -271.83, eight parts
    greedy(Fr(1, 3) * 1000, 4), greedy(Fr(-7, 11), 2),
]

if __name__ == '__main__':
    for parts in CASES:
        x = Decimal(0)
        for p in parts:
            x = EXACT.add(x, Decimal(p))                   # each f64 is exact in decimal, and so is the sum
        assert Fr(x) == sum(Fr(p) for p in parts)
        e = OUT.exp(x)
        s = '{:.699e}'.format(e)
        print(','.join(bits(p) for p in parts), s)
