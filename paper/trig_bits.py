"""The emulator's sine, cosine and tangent, the algorithms of the appendix on the trigonometric functions (RED, SINR,
COSR, SIN_n, COS_n, TAN_n) on fpemu.py, against multidouble's OD::sin, cos and tan (n = 8, the paper's MUL, ADD, ADDF,
DIV) and DD::sin, cos and tan (n = 2, with DWTimesDW3, AccurateDWPlusDW, DWPlusFP and DWDivDW2 written here from Joldes,
Muller and Popescu's algorithms), bit for bit. pi/2 to 1216 fraction bits comes from Machin's formula computed here.
Inputs: random greedy values with |x| from 2^-8 to 2^20, small ones down to the early return, the greedy roundings of
k pi/2 (results down to about 2^-440 at n = 8), k pi/2 +- 0.7854 (the reduction's correction of k), values up to 2^52,
and for |x| < 0.78 values at the top of the ladder H(2) (each part in (1/2, 1] ulp of the one above), which RED does
not round. Runs the crate on them (accumulator/acc_check, modes trig8 and trig2) and compares.

usage: trig_bits.py [N [seed [manifest [control]]]]   prints the inputs and mismatches per type; exits 1 on a
mismatch. control: the sine series cut to half its terms, so at least the inputs whose series has six terms or more
must mismatch (exit 0 only if they do). control2: RED without its correction of k, so some inputs beyond 2^31 must
mismatch."""
import math
import os
import random
import struct
import subprocess
import sys
import tempfile
from fractions import Fraction as Q

import fpemu as F
from trig_consts import k_table

HERE = os.path.dirname(os.path.abspath(__file__))
FB = 1216
CONTROL = None


def bits(t):
    return struct.unpack('<Q', struct.pack('<d', t))[0]


def fp(t):
    return F.from_bits(bits(t))


def val(x):
    m, e = x
    return Q(m) * Q(2) ** e if m else Q(0)


def arctan_inv(m, g):
    s, k = 0, 0
    while True:
        t = (1 << g) // ((2 * k + 1) * m ** (2 * k + 1))
        if t == 0:
            return s
        s += -t if k % 2 else t
        k += 1


# pi 2^1400 from Machin's formula, within 2^-1300 of it; P = round(pi/2 2^1216), c = RN(2/pi)
G = 1400
PI_G = 16 * arctan_inv(5, G) - 4 * arctan_inv(239, G)
P = (PI_G + (1 << (G - FB))) >> (G - FB + 1)
C = fp(Q(2 << G, PI_G).numerator / Q(2 << G, PI_G).denominator)
TAU = fp(0.7854)
ONE = (1, 0)


def round_away(q):
    """the integer nearest to q, halves away from zero"""
    a = abs(q)
    n = int(a + Q(1, 2))
    return n if q >= 0 else -n


def rn_fixed(N):
    """RN(N 2^-F)"""
    return F.rnd(N, -FB) if N else F.PZ


def greedy(x, n):
    out = []
    for _ in range(n):
        f = float(x)
        out.append(f)
        x -= Q(f)
    return out


def red(x, n):
    """RED: (k mod 4, r)"""
    k = round_away(val(F.mul(x[0], C)))
    if k == 0:
        return 0, list(x)
    N = int(sum(val(t) for t in x) * 2 ** FB) - k * P
    r0 = rn_fixed(N)
    if CONTROL != 'control2' and abs(val(r0)) > val(TAU):
        k2 = round_away(val(F.mul(r0, C)))
        N -= k2 * P
        k += k2
    r = []
    for _ in range(n):
        t = rn_fixed(N)
        r.append(t)
        N -= int(val(t) * 2 ** FB)
    return k % 4, r


# the double-word algorithms (Joldes, Muller and Popescu 2017) on fpemu
def dw_mul3(x, y):
    """DWTimesDW3 (their Algorithm 12)"""
    ch, cl1 = F.two_prod(x[0], y[0])
    tl0 = F.mul(x[1], y[1])
    tl1 = F.fma(x[0], y[1], tl0)
    cl2 = F.fma(x[1], y[0], tl1)
    cl3 = F.add(cl1, cl2)
    return list(F.quick_two_sum(ch, cl3))


def dw_add(x, y):
    """AccurateDWPlusDW (their Algorithm 6)"""
    sh, sl = F.two_sum(x[0], y[0])
    th, tl = F.two_sum(x[1], y[1])
    c = F.add(sl, th)
    vh, vl = F.quick_two_sum(sh, c)
    w = F.add(tl, vl)
    return list(F.quick_two_sum(vh, w))


def dw_plus_fp(x, y):
    """DWPlusFP (their Algorithm 4)"""
    sh, sl = F.two_sum(x[0], y)
    v = F.add(x[1], sl)
    return list(F.quick_two_sum(sh, v))


def dw_div2(x, y):
    """DWDivDW2 (their Algorithm 17, with their Algorithm 7 for (y_h + y_l) t_h), as DD::fast_div"""
    th = F.div(x[0], y[0])
    ch, cl1 = F.two_prod(y[0], th)
    h, tl1 = F.quick_two_sum(ch, F.mul(y[1], th))
    rh, rl = F.quick_two_sum(h, F.add(tl1, cl1))
    d = F.add(F.sub(x[0], rh), F.sub(x[1], rl))
    h, l = F.quick_two_sum(th, F.div(d, y[0]))
    return [h, F.add(l, F.PZ)]


def dw_neg(x):
    return [F.neg(x[0]), F.add(F.neg(x[1]), F.PZ)]


OPS = {
    8: dict(mul=F.od_mul, add=F.od_add, one_plus=lambda t: F.od_add_f(t, ONE), div=F.od_div, neg=F.od_neg),
    2: dict(mul=dw_mul3, add=dw_add, one_plus=lambda t: dw_plus_fp(t, ONE), div=dw_div2, neg=dw_neg),
}


def setup(n):
    ks, kc = k_table(n, True), k_table(n, False)
    kmax = max(max(ks), max(kc))
    fact = [1]
    for i in range(1, 2 * kmax + 2):
        fact.append(fact[-1] * i)
    cs = [[fp(t) for t in greedy(Q((-1) ** k, fact[2 * k + 1]), n)] for k in range(kmax)]
    cc = [[fp(t) for t in greedy(Q((-1) ** k, fact[2 * k]), n)] for k in range(kmax)]
    return ks, kc, cs, cc


def bucket(x):
    m, e = x
    return -(abs(m).bit_length() - 1 + e) - 1


def tiny(x, n):
    return val(x) == 0 or abs(val(x)) < Q(1, 2 ** (53 * n // 2))


def horner(o, z, c, K):
    p = c[K - 1]
    for k in range(K - 2, 0, -1):
        p = o['add'](o['mul'](z, p), c[k])
    return p


def trig(x, n, tabs):
    """(sin, cos, tan) by SIN_n, COS_n, TAN_n"""
    ks, kc, cs, cc = tabs
    o = OPS[n]
    one = [ONE] + [F.PZ] * (n - 1)
    if tiny(x[0], n):
        return x, one, x
    q, r = red(x, n)
    z = o['mul'](r, r)
    if tiny(r[0], n):
        s, c = r, one
    else:
        j = bucket(r[0])
        K = max(2, ks[j] // 2) if CONTROL == 'control' else ks[j]
        s = o['add'](r, o['mul'](r, o['mul'](z, horner(o, z, cs, K))))
        c = o['one_plus'](o['mul'](z, horner(o, z, cc, kc[j])))
    ng = o['neg']
    sx = [s, c, ng(s), ng(c)][q]
    cx = [c, ng(s), ng(c), s][q]
    tx = o['div'](s, c) if q % 2 == 0 else ng(o['div'](c, s))
    return sx, cx, tx


def inputs(N, seed, n):
    rnd = random.Random(seed * 10 + n)
    half_pi = Q(P, 2 ** FB)
    xs = []
    for i in range(N):
        cat = i % 6
        sign = rnd.choice((-1, 1))
        if cat == 0:
            v = Q(rnd.getrandbits(500) | (1 << 499), 1 << 499) * Q(2) ** rnd.randint(-8, 19)
        elif cat == 1:
            v = Q(rnd.getrandbits(500) | (1 << 499), 1 << 499) * Q(2) ** rnd.randint(-(53 * n // 2) - 3, -9)
        elif cat == 2:
            v = (2 ** rnd.randint(0, 19) + rnd.randint(0, 1023)) * half_pi
        elif cat == 3:
            v = rnd.randint(1, 2 ** rnd.randint(1, 50)) * half_pi + Q(0.7854) * rnd.choice((-1, 1)) * (
                1 + Q(rnd.randint(-2 ** 20, 2 ** 20), 2 ** 50))
        elif cat == 4:
            v = Q(rnd.getrandbits(500) | (1 << 499), 1 << 499) * Q(2) ** rnd.randint(40, 51)
        else:
            v = None
        if v is None:
            # the top of the ladder H(2) below 0.78
            x = [rnd.uniform(0.1, 0.78)]
            for k in range(1, n):
                x.append(rnd.choice((-1.0, 1.0)) * (0.5 + 0.5 * rnd.random()) * math.ulp(x[k - 1]))
            x = [sign * t for t in x]
        else:
            x = greedy(sign * v, n)
        xs.append(x)
    return xs


def main():
    global CONTROL
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 600
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    manifest = sys.argv[3] if len(sys.argv) > 3 else os.path.join(HERE, 'accumulator', 'acc_check', 'Cargo.toml')
    CONTROL = sys.argv[4] if len(sys.argv) > 4 else None
    status = 0
    for n, mode in ((8, 'trig8'), (2, 'trig2')):
        tabs = setup(n)
        xs = inputs(N, seed, n)
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, 'xs.txt')
            with open(path, 'w') as fh:
                for x in xs:
                    fh.write(' '.join(f'{bits(t):016x}' for t in x) + '\n')
            out = subprocess.run(['cargo', 'run', '-q', '--release', '--manifest-path', manifest, '--', mode, path],
                                 capture_output=True, text=True, check=True).stdout.split('\n')
        bad = 0
        runs = 0
        for x, line in zip(xs, out):
            ex = [fp(t) for t in x]
            got = trig(ex, n, tabs)
            want = ' '.join(f'{F.to_bits(y):016x}' for f in got for y in f)
            bad += want != line.strip()
            # inputs whose sine series has six terms or more (the control halves them)
            if not tiny(ex[0], n):
                r0 = red(ex, n)[1][0]
                runs += not tiny(r0, n) and tabs[0][bucket(r0)] >= 6
        note = f' (control; {runs} with six terms or more)' if CONTROL == 'control' else ''
        print(f'n = {n}: {N} inputs, {bad} mismatches' + (f' ({CONTROL})' if CONTROL == 'control2' else note))
        if CONTROL == 'control':
            status |= bad < runs
        elif CONTROL == 'control2':
            status |= bad == 0
        else:
            status |= bad != 0
    sys.exit(status)


if __name__ == '__main__':
    main()
