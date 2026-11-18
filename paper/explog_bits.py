"""The exponential and the logarithm of Appendix L on fpemu.py, written from the appendix's steps: EXP and LOG at n = 8
(`OD::exp`, `OD::ln`) and their double-word forms (`DD::exp`, `DD::ln`, Proposition 38), checked bit for bit against
multidouble (accumulator/acc_check, modes exp8, ln8, expdd and lndd) and against the bounds, and scanned for
underflow.

usage: explog_bits.py bits [N [seed [control]]]   N inputs per function and category (default 200): prints the inputs,
                                                  the mismatches and the largest error as a share of the bound, against
                                                  Python's correctly rounded exp and ln at 1300 digits; exits 1 on a
                                                  mismatch or an error beyond the bound. control: the emulator's
                                                  Taylor degree halved ('exp_half', the crate's TAYLOR_HALF) or its
                                                  start off by 2^-20 ('ln_start', LN_START), and the run exits 1 unless
                                                  both functions so changed mismatch and break their bounds.
       explog_bits.py scan [K]                    K greedy inputs per binade (default 2), and as many with parts at the
                                                  top of the ladder at n = 8, of every binade from the largest argument
                                                  down to the smallest, and for ln of x - 1: counts the products, fused
                                                  multiply-adds and quotients whose binary64 result would differ from
                                                  the unbounded-exponent one (underflow), and the power-of-two
                                                  scalings that would leave the normal range; exits 1 on any of the
                                                  former but x_0 Lambda and the factors of the U's, which decide
                                                  only k, m, the degree or a branch of LOG. control 'full_degree':
                                                  the Taylor polynomial at full degree for every r, which must
                                                  underflow (the run exits 1 unless it does)."""
import math
import os
from decimal import Decimal as D, localcontext
import random
import struct
import subprocess
import sys
import tempfile
from fractions import Fraction as Q

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'scripts'))
import fpemu as F  # noqa: E402
import explog_constants as EC  # noqa: E402

CONTROL = None
SCAN = None  # a dict of counters while scanning


def bits(t):
    return struct.unpack('<Q', struct.pack('<d', t))[0]


def fl(t):
    return F.from_bits(bits(t))


def val(x):
    m, e = x
    return Q(m) * Q(2) ** e if m else Q(0)


def to_bits(x):
    """the binary64 bits of an emulated value, subnormals included"""
    m, e = x
    if m == 0:
        return e << 63
    v = abs(val(x))
    f = float(v)
    assert Q(f) == v, 'not a binary64 value'
    return bits(-f if m < 0 else f)


CONST = EC.constants()
LN2_HI = fl(CONST['hi'])
LN2_LO = [fl(t) for t in CONST['lo']]
FACT = [[fl(t) for t in v] for v in CONST['fact']]
THIRD = [fl(t) for t in CONST['third']]
LOG2_E = fl(1.4426950408889634)
LN_2 = fl(0.6931471805599453)
SQRT_2 = fl(1.4142135623730951)
LN_SERIES = [fl(1.0 / (2 * j + 1)) for j in range(10)]
ONE, PZ = fl(1.0), F.PZ
MIN_NORMAL = Q(2) ** -1022


def expo(x):
    """floor(log2 |x|) for a normal x, -1023 for zero or a subnormal (the crate's biased exponent less 1023)"""
    if x[0] == 0 or abs(val(x)) < MIN_NORMAL:
        return -1023
    return abs(x[0]).bit_length() - 1 + x[1]


def p2(x, k):
    """x 2^k as binary64 gives it: exact unless the result falls below 2^-1022, where it rounds to the nearest
    multiple of 2^-1074, ties to even (gradual underflow); while scanning, counts such a result"""
    m, e = x
    if m == 0:
        return x
    y = (m, e + k)
    v = val(y)
    if abs(v) < MIN_NORMAL:
        if SCAN is not None:
            SCAN['scale'] += 1
        q = v * Q(2) ** 1074
        n = math.floor(q)
        rem = q - n
        if rem > Q(1, 2) or (rem == Q(1, 2) and n % 2 == 1):
            n += 1
        if n == 0:
            return (0, 1 if m < 0 else 0)
        y = F.rnd(n, -1074)
    return y


# -- the underflow hook: a product, an FMA or a quotient whose exact result is below 2^-1022 and not a multiple of
#    2^-1074 would round differently in binary64
def _hook(kind, exact, r):
    if SCAN is not None and r[0] != 0 and abs(val(r)) < MIN_NORMAL:
        if val(r) != exact or (val(r) * Q(2) ** 1074).denominator != 1:
            SCAN[kind] += 1
    return r


_mul, _fma, _div = F.mul, F.fma, F.div


def mul(x, y):
    return _hook('mul', val(x) * val(y), _mul(x, y))


def fma(x, y, z):
    return _hook('fma', val(x) * val(y) + val(z), _fma(x, y, z))


def div(x, y):
    return _hook('div', val(x) / val(y), _div(x, y))


F.mul, F.fma, F.div = mul, fma, div  # the od_* functions of fpemu call these through the module


def rnd_away(q):
    """the nearest integer to the rational q, half away from zero (f64::round)"""
    s = -1 if q < 0 else 1
    return s * math.floor(abs(q) + Q(1, 2))


# ---------------------------------------------------------------------------------------------------------------
# the double-word operations (Proposition 37) and the expansion ones (fpemu)
# ---------------------------------------------------------------------------------------------------------------

def dw_add(a, b):
    """AccurateDWPlusDW (DD's +)"""
    s, e = F.two_sum(a[0], b[0])
    t, f = F.two_sum(a[1], b[1])
    e = F.add(e, t)
    s, e = F.quick_two_sum(s, e)
    e = F.add(e, f)
    return list(F.quick_two_sum(s, e))


def dw_plus_fp(a, b):
    """DWPlusFP"""
    sh, sl = F.two_sum(a[0], b)
    v = F.add(a[1], sl)
    return list(F.quick_two_sum(sh, v))


def dw_times_dw(a, b):
    """DWTimesDW2"""
    ch, cl1 = F.two_prod(a[0], b[0])
    tl = F.mul(a[0], b[1])
    cl2 = F.fma(a[1], b[0], tl)
    return list(F.quick_two_sum(ch, F.add(cl1, cl2)))


def dw_times_fp(a, b):
    """DWTimesFP3 (DD::mul_f)"""
    p, e = F.two_prod(a[0], b)
    e = F.fma(a[1], b, e)
    return list(F.quick_two_sum(p, e))


def flog2(x):
    """floor(log2 x) for a rational x > 0, exactly"""
    k = x.numerator.bit_length() - x.denominator.bit_length()
    return k if x >= Q(2) ** k else k - 1


def margin(a, b):
    """how far the products a MUL forms from its operands' parts clear the underflow threshold, in binades: for a
    two-product (i + j <= n - 1) e_ai + e_bj against -970, the classical condition for its error to be exact, and for a
    rounded product (i + j = n) floor(log2 |a_i b_j|) against -1022 (min over nonzero parts; inf if none)"""
    n = len(a)
    va, vb = [val(t) for t in a], [val(t) for t in b]
    m = math.inf
    for i in range(n):
        for j in range(n - i + 1):
            if j < n and va[i] != 0 and vb[j] != 0:
                if i + j <= n - 1:
                    m = min(m, flog2(abs(va[i])) + flog2(abs(vb[j])) + 970)
                else:
                    m = min(m, flog2(abs(va[i] * vb[j])) + 1022)
    return m


def measured(mul):
    """a MUL that, while scanning, records the least margin of the products it forms"""
    def m(a, b):
        if SCAN is not None:
            SCAN['margin'] = min(SCAN['margin'], margin(a, b))
        return mul(a, b)
    return m


class DW:
    n, S, DEG, Q, B = 2, 1, 27, 3, 118

    @staticmethod
    def const(c):
        return list(c[:2])

    plus, times = staticmethod(dw_add), staticmethod(measured(dw_times_dw))

    @staticmethod
    def plus_one(a):
        return dw_plus_fp(a, ONE)

    @staticmethod
    def neg(a):
        return [F.neg(a[0]), F.add(F.neg(a[1]), PZ)]

    @staticmethod
    def reduce(x, k):
        a = F.sub(x[0], F.mul(k, LN2_HI))
        p = dw_times_fp(LN2_LO[:2], F.neg(k))
        return dw_plus_fp(dw_plus_fp(p, x[1]), a)

    @staticmethod
    def sub_one(x):
        return list(F.two_sum(F.sub(x[0], ONE), x[1]))

    @staticmethod
    def ln_start(x):
        return [F.add(ln_f64(x[0]), F.div(x[1], x[0])), PZ]

    @staticmethod
    def ln_finish(y0, corr):
        return dw_plus_fp(corr, y0[0])

    @staticmethod
    def from_f(v):
        return [v, PZ]


class OD:
    n, S, DEG, Q, B = 8, 6, 43, 4, 436

    @staticmethod
    def const(c):
        return list(c[:8])

    plus, times = staticmethod(F.od_add), staticmethod(measured(F.od_mul))

    @staticmethod
    def plus_one(a):
        return F.od_add_f(a, ONE)

    @staticmethod
    def neg(a):
        return F.od_neg(a)

    @staticmethod
    def reduce(x, k):
        xp = [F.sub(x[0], F.mul(k, LN2_HI))] + list(x[1:])
        return F.od_add(xp, F.od_mul_f(LN2_LO, F.neg(k)))

    @staticmethod
    def sub_one(x):
        return F.od_add_f(x, F.neg(ONE))

    @staticmethod
    def ln_start(x):
        top = val(x[0]) >= Q(2) ** 1023
        if top:                           # the double-double of x could round past f64::MAX: start from x/2, add ln 2
            x = [p2(v, -1) for v in x]
        t = x[7]
        for i in range(6, 0, -1):
            t = F.add(x[i], t)
        y = ln_of(DW, list(F.quick_two_sum(x[0], t)))
        if top:
            y = dw_add(y, [fl(v) for v in EC.constants()['dd']])
        return y + [PZ] * 6

    @staticmethod
    def ln_finish(y0, corr):
        return F.od_add(corr, y0)

    @staticmethod
    def from_f(v):
        return [v] + [PZ] * 7


def ln_f64(h):
    """the start's binary64 logarithm (Lemma 37)"""
    e0 = 0
    if abs(val(h)) < MIN_NORMAL:
        h, e0 = p2(h, 54), -54
    e = expo(h) + e0
    m = p2(h, -expo(h))                                       # the significand in [1, 2), exact
    if F.abs_ge(m, SQRT_2) and val(m) != val(SQRT_2):
        m, e = p2(m, -1), e + 1
    s = F.div(F.sub(m, ONE), F.add(m, ONE))
    z = F.mul(s, s)
    v = LN_SERIES[9]
    for c in reversed(LN_SERIES[:9]):
        v = F.fma(z, v, c)
    y = F.fma(fl(float(e)), LN_2, F.mul(F.add(s, s), v))
    return F.mul(y, fl(1 + 2.0 ** -20)) if CONTROL == 'ln_start' else y


# ---------------------------------------------------------------------------------------------------------------
# EXP and LOG (Appendix L), over the operations of P
# ---------------------------------------------------------------------------------------------------------------

def degree(P, er):
    if er < -1 - P.B:
        return 1
    return min(P.DEG, -(-P.B // (-er - 1)))


def scaled_times(P, a, e, b):
    return [p2(t, e) for t in P.times([p2(t, -e) for t in a], b)]


def expm1_red(P, x):
    before = None if SCAN is None else SCAN['mul']
    kq = F.mul(x[0], LOG2_E)
    if SCAN is not None and SCAN['mul'] > before:
        SCAN['k'] += 1                    # x_0 Lambda below 2^-1022: k = 0 whatever its rounding
        assert abs(val(kq)) < Q(1, 2)
    k = rnd_away(val(kq))
    r = x if k == 0 else P.reduce(x, fl(float(k)))
    e = bound_expo(r)
    m = max(0, e + P.S + 1)
    if m > 0:
        r = [p2(t, -m) for t in r]
    er = e - m
    d = degree(P, er)
    if CONTROL == 'exp_half':
        d = max(1, d // 2)
    if CONTROL == 'full_degree':
        d = P.DEG                         # the scan's control: every term formed, however small r
    if d == 1:
        t = r
    else:
        q = P.const(FACT[d])
        for j in range(d - 1, 1, -1):
            q = P.plus(P.const(FACT[j]), P.times(r, q))
        w = P.times(r, q)
        rs = [p2(t, -er) for t in r]
        t = [p2(v, er) for v in P.plus(rs, P.times(rs, w))]
    for _ in range(m):
        t = P.plus([p2(v, 1) for v in t], P.times(t, t))
    return k, t


def scale2(P, x, k):
    k1 = int(k / 2)
    return [p2(p2(t, k1), k - k1) for t in x]


def exp_of(P, x):
    k, t = expm1_red(P, x)
    return scale2(P, P.plus_one(t), k)


def series(P, i):
    if i == 2:
        return P.from_f(fl(-0.5))
    if i == 3:
        return P.const(THIRD)
    return P.from_f(fl(-0.25))


def bound_expo(v):
    """the crate's bound_expo: the exponent of U = RN(RN(sum |v_i|) (1 + 2^-48)), summed from the leading part down"""
    acc = PZ
    for t in v:
        acc = F.add(acc, F.fabs(t))
    before = None if SCAN is None else SCAN['mul']
    uq = F.mul(acc, fl(1 + 2.0 ** -48))
    if SCAN is not None and SCAN['mul'] > before:
        SCAN['k'] += 1                    # U below 2^-1022: e = -1023 or -1022, a choice as with an unbounded exponent
        assert val(acc) < Q(2) ** -1022
    return expo(uq)


def ln_of(P, x):
    y0 = P.ln_start(x)
    k, t = expm1_red(P, P.neg(y0))
    f = P.sub_one(scale2(P, x, k))
    ef, et = bound_expo(f), bound_expo(t)
    if min(ef, et) < -P.B - 13:
        c = P.plus(f, t)
    else:
        p = P.times([p2(v, -ef) for v in f], [p2(v, -et) for v in t])
        c = P.plus(P.plus(f, t), [p2(p2(v, ef), et) for v in p])
    ec = bound_expo(c)
    if ec < -P.B - 13:
        corr = c
    else:
        h = series(P, P.Q)
        for i in range(P.Q - 1, 1, -1):
            h = P.plus(series(P, i), scaled_times(P, c, ec, h))
        corr = scaled_times(P, c, ec, P.plus_one(scaled_times(P, c, ec, h)))
    return P.ln_finish(y0, corr)


# ---------------------------------------------------------------------------------------------------------------
# inputs
# ---------------------------------------------------------------------------------------------------------------

def greedy(z, n):
    out = []
    for _ in range(n):
        x = float(z)
        out.append(x)
        z -= Q(x)
    return out


def ladder_top(r, x0, n):
    """parts at the top of the ladder H(2), |x_i| in ((2u)^i / 2, (2u)^i] |x_0|, random signs"""
    return [x0] + [r.choice((-1.0, 1.0)) * (0.5 + 0.5 * r.random()) * abs(x0) * 2.0 ** (-52 * i) for i in range(1, n)]


def rand_val(r, e):
    return Q(r.getrandbits(400) | (1 << 399), 1 << 399) * Q(2) ** e


def inputs(fn, n, N, seed):
    """N inputs of each category for fn ('exp' or 'ln') with n parts"""
    r = random.Random(seed)
    xs = []
    for i in range(N):
        if fn == 'exp':
            cats = [rand_val(r, r.randint(-60, 9)) * r.choice((-1, 1)),            # random magnitude
                    rand_val(r, r.randint(-1000, -60)) * r.choice((-1, 1)),         # near 0
                    Q(r.randint(-1074, 1023)) * Q(EC.constants()['ln2'][0]) / 2 + rand_val(r, -60)]  # near (k/2) ln 2
            for z in cats:
                if abs(z) < 700:
                    xs.append(greedy(z, n))
            x0 = (r.random() * 1400 - 700)
            if n > 2:
                xs.append(ladder_top(r, x0, n))
        else:
            cats = [rand_val(r, r.randint(-1000, 1000)),                           # random magnitude
                    1 + rand_val(r, r.randint(-1000, -1)) * r.choice((-1, 1)),      # near 1
                    rand_val(r, 0) * Q(2) ** r.randint(-1074, -1023)]               # subnormal
            for z in cats:
                xs.append(greedy(z, n) if z >= Q(2) ** -1022 else [float(z)] + [0.0] * (n - 1))
            if n > 2:
                xs.append(ladder_top(r, (1 + r.random()) * 2.0 ** r.randint(-900, 900), n))
                xs.append(ladder_top(r, 1.0 + r.choice((-1, 1)) * 2.0 ** -r.randint(1, 52), n))
                # the top of the range, where the start takes x/2: x_0 within 3 ulps of f64::MAX, a tail near half an
                # ulp
                x0 = struct.unpack('<d', struct.pack('<Q', 0x7fefffffffffffff - r.randint(0, 3)))[0]
                xs.append([x0, math.ulp(x0) / 2, r.choice((-1.0, 1.0)) * 2.0 ** (915 - r.randint(0, 40))] + [0.0] * (n - 3))
    return xs


def run_crate(mode, xs):
    manifest = os.path.join(HERE, 'accumulator', 'acc_check', 'Cargo.toml')
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, 'xs.txt')
        with open(path, 'w') as fh:
            for x in xs:
                fh.write(' '.join(f'{bits(t):016x}' for t in x) + '\n')
        out = subprocess.run(['cargo', 'run', '-q', '--release', '--manifest-path', manifest, '--', mode, path],
                             capture_output=True, text=True, check=True).stdout.split('\n')
    return [line.strip() for line in out if line.strip()]


# the proven bounds (explog_consts.txt) as quoted: relative coefficient in units of u^n, and the absolute term
BOUNDS = {('exp', 8): (3.661, Q(8, 2 ** 1074)), ('ln', 8): (9.926, Q(1, 2 ** 509)),
          ('exp', 2): (5.465, Q(2, 2 ** 1074)), ('ln', 2): (15.351, Q(1, 2 ** 1071))}


def dec(q):
    """an exact dyadic rational as a Decimal, exact at the context's 1300 digits"""
    return D(q.numerator) / D(q.denominator)


def error(fn, n, x, y):
    """|y - f(x)| / (C u^n |f(x)| + A), the bound's share used, against Python's correctly rounded exp and ln at 1300
    digits (no code shared with the crate's reference)"""
    C, A = BOUNDS[(fn, n)]
    with localcontext() as c:
        c.prec = 1300
        xv, yv = dec(sum(val(t) for t in x)), dec(sum(val(t) for t in y))
        ref = xv.exp() if fn == 'exp' else xv.ln()
        lim = D(C) * dec(Q(1, 2 ** (53 * n))) * abs(ref) + dec(A)
        return float(abs(yv - ref) / lim)


def bits_main(N, seed, control):
    global CONTROL
    CONTROL = control
    bad_total, changed = 0, []
    for fn, P, mode in (('exp', OD, 'exp8'), ('ln', OD, 'ln8'), ('exp', DW, 'expdd'), ('ln', DW, 'lndd')):
        xs = inputs(fn, P.n, N, seed)
        got = run_crate(mode, xs)
        assert len(got) == len(xs)
        bad, over, worst = 0, 0, 0.0
        for x, line in zip(xs, got):
            ex = [fl(t) for t in x]
            y = exp_of(P, ex) if fn == 'exp' else ln_of(P, ex)
            bad += ' '.join(f'{to_bits(t):016x}' for t in y) != line
            e = error(fn, P.n, ex, y)
            worst = max(worst, e)
            over += e > 1
        print(f'{mode}: {len(xs)} inputs, {bad} mismatches; error at most {worst:.4f} of the bound, {over} beyond it'
              + (f' ({control})' if control else ''))
        bad_total += bad + over
        if control == 'ln_start' and fn == 'ln' or control == 'exp_half' and fn == 'exp':
            changed.append(bad > 0 and over > 0)
    if control:
        sys.exit(0 if changed and all(changed) else 1)
    sys.exit(1 if bad_total else 0)


def scan_main(K, control=None):
    global SCAN, CONTROL
    CONTROL = control
    r = random.Random(7)
    worst = 0
    for fn, P in (('exp', OD), ('ln', OD), ('exp', DW), ('ln', DW)):
        SCAN = dict(mul=0, fma=0, div=0, scale=0, k=0, margin=math.inf)
        count, where = 0, []
        if fn == 'exp':
            es = range(10, -1076, -1)
        else:
            es = list(range(1023, -1075, -1)) + [-j for j in range(1, 1075)]  # magnitudes, then 1 + 2^-j
        for idx, e in enumerate(es):
            for _ in range(K):
                if fn == 'exp':
                    if e < -1074:
                        continue
                    z = rand_val(r, e) * r.choice((-1, 1))
                    if not -745 < z < 709.7:
                        continue
                elif idx < 2098:
                    z = rand_val(r, e)
                else:
                    z = 1 + rand_val(r, e) * r.choice((-1, 1))
                x = greedy(z, P.n) if abs(z) >= Q(2) ** -1022 else [float(z)] + [0.0] * (P.n - 1)
                if x[0] == 0:
                    continue
                xs = [x]
                if P.n > 2 and abs(x[0]) >= 2.0 ** -1022 * 2.0 ** (52 * (P.n - 1)):
                    xs.append(ladder_top(r, x[0], P.n))   # parts at the top of the ladder, all normal
                for x in xs:
                    ex = [fl(t) for t in x]
                    before = SCAN['mul'] + SCAN['fma'] + SCAN['div']
                    k0 = SCAN['k']
                    exp_of(P, ex) if fn == 'exp' else ln_of(P, ex)
                    count += 1
                    if SCAN['mul'] + SCAN['fma'] + SCAN['div'] - (SCAN['k'] - k0) > before:
                        where.append(('1+' if idx >= 2098 and fn == 'ln' else '') + str(e))
        hits = SCAN['mul'] + SCAN['fma'] + SCAN['div'] - SCAN['k']
        worst = max(worst, hits)
        print(f'{"OD" if P is OD else "DD"} {fn}: {count} inputs over every binade{" (half at the top of the ladder)" if P.n > 2 else ""}; underflowing products {SCAN["mul"]}, '
              f'FMAs {SCAN["fma"]}, quotients {SCAN["div"]}, of which {SCAN["k"]} are x_0 Lambda or a U, deciding only k, m, d or a branch; scalings '
              f'leaving the normal range {SCAN["scale"]}; the MULs\' products clear the threshold by {SCAN["margin"]} binades at least' + (f'; other underflows at binades {where}' if where else ''))
    SCAN = None
    if control:
        sys.exit(0 if worst else 1)
    sys.exit(1 if worst else 0)


if __name__ == '__main__':
    what = sys.argv[1] if len(sys.argv) > 1 else 'bits'
    if what == 'bits':
        bits_main(int(sys.argv[2]) if len(sys.argv) > 2 else 200, int(sys.argv[3]) if len(sys.argv) > 3 else 1,
                  sys.argv[4] if len(sys.argv) > 4 else None)
    else:
        scan_main(int(sys.argv[2]) if len(sys.argv) > 2 else 2, sys.argv[3] if len(sys.argv) > 3 else None)
