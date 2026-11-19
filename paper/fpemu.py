"""Exact emulator of p-bit binary floating point (RN, ties to even, unbounded exponents, signed zeros) and of
multidouble's octo-double algorithms (src/od.rs) generalized to n parts.

A value is a tuple (m, e) worth m 2^e with |m| < 2^p and m odd (canonical), or a zero (0, s) with s = 1 for -0.
Every operation rounds the exact result once, with IEEE 754's signed-zero rules (an exact zero sum of nonzero
operands is +0). Written from src/od.rs, operation by operation; campaign.py compares it with the crate bit for bit.
"""
from math import isqrt

P = 53
MUTATE = None  # controls: 'ties_away' (rounding), 'two_sum_sign' (two-sum's error x - y), 'fma_plain'
LEVEL_HOOK = None  # called with the levels after every change by dep and after each level builder's setup
DROP = None  # controls of the operation checks: 'add_t1' drops the error of a1 + b1 (as the crate's ADD_T1),
#              'mul_e23' the error of a2 b3 (MUL_E23), 'mulf_e3' the error of a3 b (MUL_F_E3), 'div_rem' the remainder
#              update before the sixth quotient term (DIV_REM), 'sqrt_iter' the second Newton step skipped (SQRT_ITER),
#              'sqrt_two_sum' the square root's two-sum of a_0, a_1 skipped
RANGE_CHECK = False  # p = 53 only: count results outside f64's normal range (they would be subnormal or overflow)
range_hits = 0
PZ = (0, 0)
NZ = (0, 1)


def set_p(p, range_check=False):
    global P, RANGE_CHECK, range_hits
    P = p
    RANGE_CHECK = range_check
    range_hits = 0


def _fin(a, e, neg):
    # a > 0 with at most P + 1 bits (a carry may give 2^P); canonical odd mantissa
    tz = (a & -a).bit_length() - 1
    if tz:
        a >>= tz
        e += tz
    if RANGE_CHECK:
        global range_hits
        top = a.bit_length() - 1 + e
        if top < -1022 or top > 1023:
            range_hits += 1
    return (-a, e) if neg else (a, e)


def rnd(m, e):
    """RN-even of the nonzero exact value m 2^e to P bits"""
    neg = m < 0
    a = -m if neg else m
    sh = a.bit_length() - P
    if sh > 0:
        q = a >> sh
        r = a - (q << sh)
        h = 1 << (sh - 1)
        if r > h or (r == h and ((q & 1) or MUTATE == 'ties_away')):
            q += 1
        a = q
        e += sh
    return _fin(a, e, neg)


def rnd_sticky(a, e, sticky, neg):
    """RN-even of (a + s) 2^e, 0 < s < 1 when sticky; a has at least P + 2 bits"""
    sh = a.bit_length() - P
    q = a >> sh
    r = a - (q << sh)
    h = 1 << (sh - 1)
    if r > h or (r == h and (sticky or (q & 1))):
        q += 1
    return _fin(q, e + sh, neg)


def sgn(x):
    m, e = x
    return (1 if m < 0 else 0) if m else e


def is_zero(x):
    return x[0] == 0


def neg(x):
    m, e = x
    return (-m, e) if m else (0, 1 - e)


def fabs(x):
    m, e = x
    return (-m, e) if m < 0 else (m, 0 if m == 0 else e)


def add(x, y):
    mx, ex = x
    my, ey = y
    if mx == 0:
        if my == 0:
            return (0, ex & ey)
        return y
    if my == 0:
        return x
    if ex <= ey:
        m = mx + (my << (ey - ex))
        e = ex
    else:
        m = my + (mx << (ex - ey))
        e = ey
    if m == 0:
        return PZ
    return rnd(m, e)


def sub(x, y):
    return add(x, neg(y))


def mul(x, y):
    mx, ex = x
    my, ey = y
    if mx == 0 or my == 0:
        return (0, sgn(x) ^ sgn(y))
    return rnd(mx * my, ex + ey)


def fma(x, y, z):
    """x y + z with one rounding"""
    mx, ex = x
    my, ey = y
    mz, ez = z
    if mx == 0 or my == 0:
        ps = sgn(x) ^ sgn(y)
        if mz == 0:
            return (0, ps & ez)
        return z
    mp = mx * my
    ep = ex + ey
    if mz == 0:
        return rnd(mp, ep)
    if ep <= ez:
        m = mp + (mz << (ez - ep))
        e = ep
    else:
        m = mz + (mp << (ep - ez))
        e = ez
    if m == 0:
        return PZ
    return rnd(m, e)


def div(x, y):
    mx, ex = x
    my, ey = y
    if my == 0:
        raise ZeroDivisionError("emulator: division by zero")
    if mx == 0:
        return (0, sgn(x) ^ sgn(y))
    neg_ = (mx < 0) != (my < 0)
    a = abs(mx)
    b = abs(my)
    k = max(0, P + 3 + b.bit_length() - a.bit_length())
    q, r = divmod(a << k, b)
    return rnd_sticky(q, ex - ey - k, r != 0, neg_)


def fsqrt(x):
    m, e = x
    if m == 0:
        return x
    if m < 0:
        raise ValueError("emulator: sqrt of a negative")
    if e & 1:
        m <<= 1
        e -= 1
    k = max(0, (2 * (P + 3) - m.bit_length() + 2) // 2)
    M = m << (2 * k)
    s = isqrt(M)
    return rnd_sticky(s, (e - 2 * k) // 2, s * s != M, False)


def pow2_floor(x):
    """2^floor(log2 |x|), positive (the f64 exponent bits alone)"""
    m, e = x
    if m == 0:
        return PZ
    return (1, abs(m).bit_length() - 1 + e)


def abs_ge(x, y):
    """|x| >= |y|"""
    mx, ex = x
    my, ey = y
    if my == 0:
        return True
    if mx == 0:
        return False
    ax = abs(mx)
    ay = abs(my)
    tx = ax.bit_length() + ex
    ty = ay.bit_length() + ey
    if tx != ty:
        return tx > ty
    if ex <= ey:
        return ax >= (ay << (ey - ex))
    return (ax << (ex - ey)) >= ay


# ---------------------------------------------------------------------------------------------------------------
# error-free transformations, as written in od.rs
# ---------------------------------------------------------------------------------------------------------------

def two_sum(a, b):
    s = add(a, b)
    bb = sub(s, a)
    x = sub(a, sub(s, bb))
    y = sub(b, bb)
    if MUTATE == 'two_sum_sign':
        return s, sub(x, y)
    return s, add(x, y)


def quick_two_sum(a, b):
    s = add(a, b)
    return s, sub(b, sub(s, a))


def two_prod(a, b):
    p = mul(a, b)
    if MUTATE == 'fma_plain':
        return p, sub(mul(a, b), p)  # control: the FMA as a plain product and a subtraction (the crate's OV_FMA_PLAIN)
    return p, fma(a, b, neg(p))  # fms(a, b, p) = a.mul_add(b, -p)


def dep(s, l, t):
    K = len(s)
    e = t
    for m in range(l, K - 1):
        s[m], e = two_sum(s[m], e)
        if LEVEL_HOOK:
            LEVEL_HOOK(s)
    s[K - 1] = add(s[K - 1], e)
    if LEVEL_HOOK:
        LEVEL_HOOK(s)


def vecsum(c):
    c = list(c)
    N = len(c)
    s = c[N - 1]
    for i in range(N - 2, -1, -1):
        t, e = two_sum(c[i], s)
        s = t
        c[i + 1] = e
    c[0] = s
    return c


# second-pass variants: 'fast' = quick-two-sum throughout (4.8.0, mutate RENORM_FAST), 'two' = two-sum throughout
# (4.8.1), 'branch' = quick-two-sum where |acc| >= |c_i|, two-sum elsewhere (4.8.2)
MODE = 'branch'


def second_pass(c, n, mode=None):
    """returns (out, k): out the n parts, k the number of parts emitted before the last"""
    mode = mode or MODE
    out = [PZ] * n
    k = 0
    acc = c[0]
    for ci in c[1:]:
        if mode == 'fast' or (mode == 'branch' and abs_ge(acc, ci)):
            t, e = quick_two_sum(acc, ci)
        else:
            t, e = two_sum(acc, ci)
        if k < n - 1 and e[0] != 0:
            out[k] = t
            k += 1
            acc = e
        else:
            acc = t
    out[k] = acc
    return out, k


def renorm(c, n, mode=None):
    return second_pass(vecsum(c), n, mode)[0]


# ---------------------------------------------------------------------------------------------------------------
# alg:: of od.rs with n parts (n = 8 is the crate)
# ---------------------------------------------------------------------------------------------------------------

def od_add_levels(a, b):
    n = len(a)
    s = [PZ] * (n + 1)
    t = [PZ] * n
    for i in range(n):
        s[i], t[i] = two_sum(a[i], b[i])
    if DROP == 'add_t1':
        t[1] = PZ
    s[n] = t[n - 1]
    if LEVEL_HOOK:
        LEVEL_HOOK(s)
    for i in range(n - 1):
        dep(s, i + 1, t[i])
    return s


def od_add(a, b, mode=None):
    return renorm(od_add_levels(a, b), len(a), mode)


def od_add_f_levels(a, b):
    n = len(a)
    s = [PZ] * (n + 1)
    e = b
    for i in range(n):
        s[i], e = two_sum(a[i], e)
    s[n] = e
    if LEVEL_HOOK:
        LEVEL_HOOK(s)
    return s


def od_add_f(a, b, mode=None):
    return renorm(od_add_f_levels(a, b), len(a), mode)


def od_mul_f_levels(a, b):
    n = len(a)
    s = [PZ] * (n + 1)
    e = [PZ] * n
    for i in range(n):
        s[i], e[i] = two_prod(a[i], b)
    if DROP == 'mulf_e3':
        e[3] = PZ
    s[n] = e[n - 1]
    if LEVEL_HOOK:
        LEVEL_HOOK(s)
    for i in range(n - 1):
        dep(s, i + 1, e[i])
    return s


def od_mul_f(a, b, mode=None):
    return renorm(od_mul_f_levels(a, b), len(a), mode)


def od_expand(a, b):
    n = len(a)
    s = [PZ] * (n + 1)
    e = [PZ] * n
    for j in range(n):
        s[j], e[j] = two_prod(a[0], b[j])
    acc = mul(a[1], b[n - 1])
    for i in range(2, n):
        acc = fma(a[i], b[n - i], acc)
    s[n] = acc
    if LEVEL_HOOK:
        LEVEL_HOOK(s)
    for j in range(n):
        dep(s, j + 1, e[j])
    for i in range(1, n):
        for j in range(0, n - i):
            p, pe = two_prod(a[i], b[j])
            if DROP == 'mul_e23' and (i, j) == (2, 3):
                pe = PZ
            dep(s, i + j, p)
            dep(s, i + j + 1, pe)
    return s


def od_mul(a, b, mode=None):
    return renorm(od_expand(a, b), len(a), mode)


def od_sub_mul_f(r, b, q, mode=None):
    n = len(r)
    s = [PZ] * (n + 1)
    t = [PZ] * n
    e = [PZ] * n
    for i in range(n):
        p, pe = two_prod(b[i], q)
        s[i], t[i] = two_sum(r[i], neg(p))
        e[i] = neg(pe)
    s[n] = add(t[n - 1], e[n - 1])
    for l in range(n - 1):
        dep(s, l + 1, t[l])
        dep(s, l + 1, e[l])
    return renorm(s, n, mode)


def od_div(a, b, mode=None):
    n = len(a)
    qs = [PZ] * (n + 1)
    r = list(a)
    qs[0] = div(r[0], b[0])
    for k in range(1, n + 1):
        if not (k == 5 and DROP == 'div_rem'):
            r = od_sub_mul_f(r, b, qs[k - 1], mode)
        qs[k] = div(r[0], b[0])
    return renorm(qs, n, mode)


def od_neg(a):
    return [neg(a[0])] + [add(neg(x), PZ) for x in a[1:]]


ONE = (1, 0)
HALF = (1, -1)


def od_sqrt_newton(x, mode=None, J=4):
    """SQRT_{n,J}: J Newton steps on 1/sqrt(a) from RN(1/RN(sqrt(a_0)))"""
    n = len(x)
    if x[0][0] == 0:
        return [PZ] * n
    s = pow2_floor(fsqrt(x[0]))
    inv = div(ONE, s)
    a = [mul(mul(xk, inv), inv) for xk in x]
    r = [PZ] * n
    r[0] = div(ONE, fsqrt(a[0]))
    h = [mul(ak, HALF) for ak in a]
    for _ in range(J):
        hr2 = od_mul(h, od_mul(r, r, mode), mode)
        c = od_add_f(od_neg(hr2), HALF, mode)
        r = od_add(r, od_mul(c, r, mode), mode)
    r = od_mul(r, a, mode)
    return [mul(rk, s) for rk in r]


def od_sqrt(x, mode=None):
    """The crate's square root: r_0 = 1/y for y the double-double square root of a_0 + a_1 (a quick two-sum, then
    Algorithm 8 of Lefevre et al.) and 1/y by DWDivDW2; one step with the second-order term, r + (c + 3/2 c^2) r, and
    one Newton step, r + c r, c = 1/2 - h r^2 (DROP 'sqrt_iter' skips the second, as the mutation SQRT_ITER)"""
    n = len(x)
    if x[0][0] == 0:
        return [PZ] * n  # the crate selects +0 in every part for a zero leading part
    s = pow2_floor(fsqrt(x[0]))
    inv = div(ONE, s)
    a = [mul(mul(xk, inv), inv) for xk in x]
    # DROP 'sqrt_two_sum' takes a_0, a_1 as they are (a control: only a_1 above ulp(a_0)/2 tells them apart)
    a0, a1 = (a[0], a[1]) if DROP == 'sqrt_two_sum' else quick_two_sum(a[0], a[1])
    sh = fsqrt(a0)
    yh, yl = quick_two_sum(sh, div(add(a1, fma(neg(sh), sh, a0)), add(sh, sh)))
    th = div(ONE, yh)
    ch, cl1 = two_prod(yh, th)
    g, tl1 = quick_two_sum(ch, mul(yl, th))
    rh, rl = quick_two_sum(g, add(tl1, cl1))
    r0, r1 = quick_two_sum(th, div(sub(sub(ONE, rh), rl), yh))
    r = [r0, r1] + [PZ] * (n - 2)
    h = [mul(ak, HALF) for ak in a]
    c = od_add_f(od_neg(od_mul(h, od_mul(r, r, mode), mode)), HALF, mode)
    c2 = od_mul(c, c, mode)
    w = od_add(c, od_add(c2, [mul(t, HALF) for t in c2], mode), mode)
    r = od_add(r, od_mul(w, r, mode), mode)
    if DROP != 'sqrt_iter':
        c = od_add_f(od_neg(od_mul(h, od_mul(r, r, mode), mode)), HALF, mode)
        r = od_add(r, od_mul(c, r, mode), mode)
    r = od_mul(r, a, mode)
    return [mul(rk, s) for rk in r]


# ---------------------------------------------------------------------------------------------------------------
# f64 bit patterns (p = 53)
# ---------------------------------------------------------------------------------------------------------------

def from_bits(b):
    sign = b >> 63
    ex = (b >> 52) & 0x7FF
    fr = b & ((1 << 52) - 1)
    if ex == 0x7FF:
        raise ValueError("inf or nan")
    if ex == 0:
        if fr == 0:
            return (0, sign)
        m, e = fr, -1074
    else:
        m, e = fr | (1 << 52), ex - 1075
    tz = (m & -m).bit_length() - 1
    m >>= tz
    e += tz
    return (-m, e) if sign else (m, e)


def to_bits(x):
    m, e = x
    if m == 0:
        return e << 63
    sign = 1 if m < 0 else 0
    a = abs(m)
    L = a.bit_length()
    if L > 53:
        raise ValueError("not a double")
    mm = a << (53 - L)
    be = e - (53 - L) + 1075
    if be <= 0 or be >= 2047:
        raise ValueError("outside the normal range")
    return (sign << 63) | (be << 52) | (mm & ((1 << 52) - 1))


def exact_sum(xs):
    """exact sum of values as (m, e) with m possibly wider than P (not rounded); zero gives (0, 0)"""
    nz = [x for x in xs if x[0] != 0]
    if not nz:
        return (0, 0)
    e0 = min(x[1] for x in nz)
    return (sum(x[0] << (x[1] - e0) for x in nz), e0)
