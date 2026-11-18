"""Referee's own exact model of p-bit binary floating point and of the level accumulator (accumulator.tex).

Written from the paper's definitions (appendix: TwoSum, dep, VecSum, R_n, ADDF, MUL) and from src/od.rs, sharing no
code with paper/fpemu.py or the author's scripts. A float is a pair (m, e) worth m 2^e, canonical (m odd, or (0, 0)).
Rounding is to nearest, ties to even, with an unbounded exponent (Assumption A1-A2). Signed zeros are not modeled; no
branch of the algorithms depends on the sign of a zero.
"""
from fractions import Fraction

P = 53
MUT = set()  # controls: 'two_sum_sign', 'dep_drop_l3' (level-3 carry of a deposit dropped), 'finish_skip_last'


def setp(p):
    global P
    P = p


ZERO = (0, 0)


def rn(m, e):
    """m 2^e rounded to P bits, ties to even, canonical"""
    if m == 0:
        return ZERO
    neg = m < 0
    a = -m if neg else m
    sh = a.bit_length() - P
    if sh > 0:
        q = a >> sh
        r = a - (q << sh)
        h = 1 << (sh - 1)
        if r > h or (r == h and q & 1):
            q += 1
        a = q
        e += sh
    tz = (a & -a).bit_length() - 1
    if tz:
        a >>= tz
        e += tz
    return (-a if neg else a, e)


def xadd(x, y):
    """exact sum, not canonical"""
    m1, e1 = x
    m2, e2 = y
    if m1 == 0:
        return y
    if m2 == 0:
        return x
    if e1 >= e2:
        return ((m1 << (e1 - e2)) + m2, e2)
    return (m1 + (m2 << (e2 - e1)), e1)


def neg(x):
    return (-x[0], x[1])


def add(x, y):
    return rn(*xadd(x, y))


def sub(x, y):
    return rn(*xadd(x, neg(y)))


def mul(x, y):
    return rn(x[0] * y[0], x[1] + y[1])


def fma(a, b, c):
    return rn(*xadd((a[0] * b[0], a[1] + b[1]), c))


def two_sum(a, b):
    """Knuth's two-sum, operation by operation as src/od.rs two_sum"""
    s = add(a, b)
    bb = sub(s, a)
    x = sub(a, sub(s, bb))
    y = sub(b, bb)
    if 'two_sum_sign' in MUT:
        return s, sub(x, y)
    return s, add(x, y)


def two_prod(a, b):
    p = mul(a, b)
    return p, fma(a, b, neg(p))


def frac(x):
    m, e = x
    return Fraction(m) * (Fraction(2) ** e)


def absf(x):
    return (abs(x[0]), x[1])


def cmpabs_ge(x, y):
    return frac(absf(x)) >= frac(absf(y))


# ---------------------------------------------------------------------------------------------------------------
# the appendix's algorithms, n parts
# ---------------------------------------------------------------------------------------------------------------

def dep(s, l, t, drop_level=None):
    """dep(s, l, t): two-sums at levels l..n-1, each error carried down, RN at level n"""
    n = len(s) - 1
    e = t
    for m in range(l, n):
        s[m], e = two_sum(s[m], e)
        if drop_level is not None and m == drop_level:
            e = ZERO
    s[n] = add(s[n], e)


def vecsum(c):
    N = len(c)
    v = list(c)
    s = c[N - 1]
    for i in range(N - 2, -1, -1):
        s, v[i + 1] = two_sum(c[i], s)
    v[0] = s
    return v


def renorm(c, n):
    """R_n of the appendix (TwoSum in the second pass throughout)"""
    v = vecsum(c)
    x = [ZERO] * n
    k = 0
    acc = v[0]
    for j in range(1, len(c)):
        t, e = two_sum(acc, v[j])
        if k < n - 1 and e[0] != 0:
            x[k] = t
            k += 1
            acc = e
        else:
            acc = t
    x[k] = acc
    return x


def addf(a, b):
    n = len(a)
    s = [ZERO] * (n + 1)
    e = b
    for i in range(n):
        s[i], e = two_sum(a[i], e)
    s[n] = e
    return renorm(s, n)


def mul_levels(a, b):
    """MUL steps (1)-(4): the n+1 levels before renormalization (src/od.rs alg::expand)"""
    n = len(a)
    s = [ZERO] * (n + 1)
    e0 = [ZERO] * n
    for j in range(n):
        s[j], e0[j] = two_prod(a[0], b[j])
    f = mul(a[1], b[n - 1])
    for i in range(2, n):
        f = fma(a[i], b[n - i], f)
    s[n] = f
    for l in range(1, n + 1):
        dep(s, l, e0[l - 1])
    for i in range(1, n):
        for j in range(0, n - i):
            p, e = two_prod(a[i], b[j])
            dep(s, i + j, p)
            dep(s, i + j + 1, e)
    return s


def mulx(a, b):
    return renorm(mul_levels(a, b), len(a))


# ---------------------------------------------------------------------------------------------------------------
# the accumulator: ADDPROD, ADDX, FINISH
# ---------------------------------------------------------------------------------------------------------------

class Acc:
    """levels s_0..s_n; records the signed rounding errors at level n (E_lev) as a check of Lemma acc(b)"""

    def __init__(self, n):
        self.n = n
        self.s = [ZERO] * (n + 1)

    def deposit(self, t):
        n = self.n
        drop = 3 if 'dep_drop_l3' in MUT else None
        for l in range(n):
            dep(self.s, l, t[l], drop)
        if len(t) == n + 1:
            self.s[n] = add(self.s[n], t[n])

    def addx(self, a):
        self.deposit(a)

    def addprod(self, a, b):
        self.deposit(mul_levels(a, b))

    def finish(self):
        n = self.n
        r = [self.s[0]] + [ZERO] * (n - 1)
        last = n - 1 if 'finish_skip_last' in MUT else n
        for l in range(1, last + 1):
            r = addf(r, self.s[l])
        return r


# ---------------------------------------------------------------------------------------------------------------
# helpers: ulp, f64 conversion
# ---------------------------------------------------------------------------------------------------------------

def expo(x):
    """floor(log2 |x|) of a nonzero float"""
    m, e = x
    return abs(m).bit_length() - 1 + e


def ulp(x):
    """ulp of a nonzero float: 2^(expo - P + 1)"""
    return (1, expo(x) - P + 1)


def to_f64_hex(x):
    import struct
    import math
    if x[0] == 0:
        return '0000000000000000'
    f = math.ldexp(x[0], x[1])
    assert Fraction(f) == frac(x), 'not representable in f64'
    return struct.pack('>d', f).hex()


def from_f64_hex(h):
    import struct
    f = struct.unpack('>d', bytes.fromhex(h))[0]
    if f == 0:
        return ZERO
    num, den = f.as_integer_ratio()
    return rn(num, -(den.bit_length() - 1))


def is_float(x):
    return rn(*x) == x and (x[0] == 0 or abs(x[0]) < (1 << P))
