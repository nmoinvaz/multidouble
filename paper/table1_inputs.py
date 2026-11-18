"""The inputs of Table 1 for the octo-double square root, sine, cosine, tangent, exponential and logarithm, checked from
scratch in exact arithmetic: each input's result by the emulator (fpemu.py's square root, trig_bits.py's SIN_8, COS_8
and TAN_8, explog_bits.py's EXP and LOG), the function's exact value at the input, enclosed by code that shares nothing
with the algorithms (an integer square root, Taylor series of the sine and cosine in fixed point with a bound on their
error, and Python's correctly rounded decimal exp and ln at 1300 digits), and the ratio |Z - z| / (u^8 |Z|) of the
error to u^8 times the exact result Z, as an enclosure. The crate's OD gives the same bits on every input
(accumulator/acc_check, modes sqrt8, trig8, exp8 and ln8).

usage: table1_inputs.py [control]

Prints one row per input: its parts, the result's parts in units of the powers of u (they are 2^E (1, u, ..., u^7)),
and the ratio. Exits 1 unless every result matches the crate and every ratio is at least its row's floor. control
'ties_away': the emulator rounds ties away from zero, which breaks the chains of ties that these results end in; the
run exits 0 only if every ratio then falls below its floor. control 'perturb': each input's leading part moved up by
one ulp; the run exits 0 only if every ratio then falls below its floor."""
import os
import struct
import subprocess
import sys
import tempfile
from decimal import Decimal as D, localcontext
from fractions import Fraction as Q
from math import isqrt

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import fpemu as F  # noqa: E402
import trig_bits as TB  # noqa: E402
import explog_bits as EB  # noqa: E402

U = Q(1, 2 ** 53)
U8 = U ** 8

# (function, the input's parts as binary64 bits, the ratio as Table 1 quotes it, which is a lower bound of the ratio
# and the floor that the check holds it to)
INPUTS = [
    ('sqrt', '3ff0000000000001 3967fdf3b645a1cb 38b0624dd2f1af00 35f0000000000004 32b0000000000003 2c3bff7ced916873 '
     '2b60624dd2f1be00 28b0000000000009', '1 - 5u', 1 - 5 * U),
    ('sin', '3ee000000000aaab 3b75555eeef6eef2 381729d2975900e8 348a195a54a29eb4 3128cc3a41f5cda2 ad6de6f5c4da02df '
     '29dad523df82f39d 261efb1a1688e432', '0.999999995', Q(999999995, 10 ** 9)),
    ('cos', '3ff941fb6999a8d4 3c98b0c392810f09 b93572503683ff67 b58f05686f022788 b1ca742cfa0db1ed 2e6693f13d61b2d3 '
     'ab0bccc00c1d973a a7a798c3c05b350e', '1.00069', Q(100069, 10 ** 5)),
    ('tan', '3e0000000000000e 3aaffaaaaaaaaaac b748f55222222223 b3eb04e88ad1ad57 307dc840ac82561c 2d0b1f36bfab0d59 '
     '299bd6c73c83ad94 a5fdb97f61d2dd6c', '1.00138', Q(100138, 10 ** 5)),
    ('exp', '3cd1fffffffffffe b97dffffffffffe3 3617fffffffffe78 3290000000005734 af399999999ea6ee abd1111110c3fec7 '
     '286c09c092a9409b 25442702796c90a9', '1 - 8.2u', 1 - Q(82, 10) * U),
    ('ln', '3fef80feabfeefa4 3c7804fa722c50e6 b90d33e543ae606f b5a9c51096bddb1f b220568c7ee0a0ac aeb561138ac7c121 '
     '2b51118a13c0f359 27f77c36d87db0bc', '0.99998', Q(99998, 10 ** 5)),
]


def on_ladder(x):
    """H(2), |x_i| <= (2u)^i |x_0|, with every part normal (or zero below a nonzero one)"""
    v = [val(t) for t in x]
    normal = all(t == 0 or abs(t) >= Q(2) ** -1022 for t in v)
    return normal and v[0] != 0 and all(abs(v[i]) <= (2 * U) ** i * abs(v[0]) for i in range(8))


def from_hex(h):
    return [F.from_bits(int(t, 16)) for t in h.split()]


def bits(t):
    return struct.unpack('<Q', struct.pack('<d', t))[0]


def val(x):
    m, e = x
    return Q(m) * Q(2) ** e if m else Q(0)


def total(xs):
    return sum((val(t) for t in xs), Q(0))


# -- the exact values, enclosed ---------------------------------------------------------------------------------

FB = 2400  # fraction bits of the fixed point


def fixed(q):
    """floor(q 2^FB), exact for the inputs' dyadic values"""
    v = q * 2 ** FB
    assert v.denominator == 1, 'below the fixed point'
    return v.numerator


def sin_cos_fixed(x):
    """(sin x, cos x) for |x| < 2 as enclosures (lo, hi): the Taylor terms in fixed point, each truncated toward zero
    from the last, so within one unit per term below the true term; the series stops at a zero term, whose tail is
    below one unit; the bound (terms + 2) units covers both"""
    X = fixed(abs(x))
    one = 1 << FB
    out = []
    for start, k0 in ((X, 1), (one, 0)):
        s, t, k, n = start, start, k0, 1
        while True:
            t = t * X // one * X // one // ((k + 1) * (k + 2))
            if t == 0:
                break
            s = s - t if n % 2 else s + t
            k += 2
            n += 1
        err = n + 4
        out.append((Q(s - err, one), Q(s + err, one)))
    (slo, shi), (clo, chi) = out
    if x < 0:
        slo, shi = -shi, -slo
    return (slo, shi), (clo, chi)


def dec_q(d):
    """a Decimal as an exact rational"""
    n, e = d.as_integer_ratio()
    return Q(n, e)


def exact(fn, X):
    """an enclosure (lo, hi) of f(X)"""
    if fn == 'sqrt':
        K = 1600
        S = isqrt(X.numerator * (1 << (2 * K)) // X.denominator)
        return Q(S, 1 << K), Q(S + 1, 1 << K)
    if fn in ('sin', 'cos', 'tan'):
        (slo, shi), (clo, chi) = sin_cos_fixed(X)
        if fn == 'sin':
            return slo, shi
        if fn == 'cos':
            return clo, chi
        # c > 0 here; s / c over the box
        ends = [a / b for a in (slo, shi) for b in (clo, chi)]
        return min(ends), max(ends)
    with localcontext() as c:
        c.prec = 1300
        xd = D(X.numerator) / D(X.denominator)
        y = dec_q(xd.exp() if fn == 'exp' else xd.ln())
    # xd is X to 1300 digits and the function correctly rounded: both within 10^-1290 relative, far inside 2^-4000 of
    # the enclosure's width below
    w = abs(y) * Q(1, 10 ** 1280)
    return y - w, y + w


def ratio(fn, x, z):
    """an enclosure of |Z - z| / (u^8 |Z|)"""
    lo, hi = exact(fn, total(x))
    zv = total(z)
    ends = [abs(Z - zv) / (U8 * abs(Z)) for Z in (lo, hi)]
    assert (lo - zv) * (hi - zv) > 0, 'the enclosure contains the result'
    return min(ends), max(ends)


# -- the emulator and the crate ---------------------------------------------------------------------------------

TABS = TB.setup(8)


def emulate(fn, x):
    if fn == 'sqrt':
        return F.od_sqrt(x)
    if fn in ('sin', 'cos', 'tan'):
        s, c, t = TB.trig(x, 8, TABS)
        return {'sin': s, 'cos': c, 'tan': t}[fn]
    return (EB.exp_of if fn == 'exp' else EB.ln_of)(EB.OD, x)


def crate(fn, x):
    mode = {'sqrt': 'sqrt8', 'sin': 'trig8', 'cos': 'trig8', 'tan': 'trig8', 'exp': 'exp8', 'ln': 'ln8'}[fn]
    manifest = os.path.join(HERE, 'accumulator', 'acc_check', 'Cargo.toml')
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, 'x.txt')
        with open(path, 'w') as fh:
            fh.write(' '.join(f'{F.to_bits(t):016x}' for t in x) + '\n')
        out = subprocess.run(['cargo', 'run', '-q', '--release', '--manifest-path', manifest, '--', mode, path],
                             capture_output=True, text=True, check=True).stdout.split()
    if mode == 'trig8':
        k = {'sin': 0, 'cos': 1, 'tan': 2}[fn]
        out = out[8 * k:8 * k + 8]
    return ' '.join(out)


def shape(z):
    """the result as +-2^E (1 + c u, u, ..., u^7) when it has that form, E that of the leading part, else its parts over
    the powers 2^E u^k"""
    E = abs(z[0][0]).bit_length() - 1 + z[0][1]
    r = [val(t) / (Q(2) ** E * U ** k) for k, t in enumerate(z)]
    sg = 1 if r[0] > 0 else -1
    c = (abs(r[0]) - 1) / U
    if all(v == sg for v in r[1:]) and c.denominator == 1:
        lead = '1' if c == 0 else f'1 + {c.numerator}u'
        return f'{"-" if sg < 0 else ""}2^{E} ({lead}, u, ..., u^7)'
    return 'parts / 2^E u^k: ' + ' '.join(f'{float(v):.17g}' for v in r)


def main():
    control = sys.argv[1] if len(sys.argv) > 1 else None
    if control == 'ties_away':
        F.MUTATE = 'ties_away'
    elif control not in (None, 'perturb'):
        sys.exit(f'unknown control {control}')
    bad, fell = 0, 0
    for fn, h, quoted, floor in INPUTS:
        x = from_hex(h)
        if control == 'perturb':
            x[0] = F.from_bits(int(h.split()[0], 16) + 1)
        z = emulate(fn, x)
        rlo, rhi = ratio(fn, x, z)
        same = True
        if control is None:
            same = crate(fn, x) == ' '.join(f'{F.to_bits(t):016x}' for t in z)
        hyp = on_ladder(x)
        ok = rlo >= floor
        print(f'{fn}: x = {h}{"" if hyp else " (OFF THE LADDER)"}\n  result {shape(z)}\n'
              f'  |Z - z| / (u^8 |Z|) in [{float(rlo):.15f}, {float(rhi):.15f}], (ratio - 1) / u in '
              f'[{float((rlo - 1) / U):.6f}, {float((rhi - 1) / U):.6f}]; at least {quoted}: '
              f'{"yes" if ok else "NO"}' + ('' if control else f'; crate {"same bits" if same else "MISMATCH"}'))
        bad += not (ok and same and hyp)
        fell += not ok
    if control:
        print(f'{control}: {fell} of {len(INPUTS)} below their quoted ratios')
        sys.exit(0 if fell == len(INPUTS) else 1)
    print('PASS' if bad == 0 else f'FAIL: {bad} rows')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
