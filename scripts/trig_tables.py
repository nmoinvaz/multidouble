"""The constants of src/trig.rs, from first principles in exact integer and rational arithmetic, written to
src/trig/tables.rs.

* pi from Machin's formula, pi/4 = 4 arctan(1/5) - arctan(1/239), each arctan series summed term by term with exact
  floors at 2^-G and its tail bounded by its first omitted term, so that pi lies in an interval of width below 2^-1300.
  Checked against Gauss's formula, pi/4 = 12 arctan(1/18) + 8 arctan(1/57) - 5 arctan(1/239), whose interval must
  overlap it and give the same rounded constants, and against the parts of QD::PI in src/qd.rs, which must be the
  greedy four-part rounding of the same interval.
* P = round(pi/2 2^F), F = 1216, as 20 little-endian u64 limbs: the reduction's pi/2; the interval must not contain a
  rounding boundary, so P is the correct rounding.
* TWO_OVER_PI = RN(2/pi) in binary64.
* SIN[k] = (-1)^k / (2k+1)! and COS[k] = (-1)^k / (2k)!, rounded greedily to eight binary64 parts (x_0 = RN(c),
  x_1 = RN(c - x_0), ...). The first two and four parts are the greedy double-double and quad-double roundings.
* KS{n}[j] and KC{n}[j]: for n = 2, 4, 8 parts and |r_0| in bucket j (2^-(j+1) <= |r_0| < 2^-j, j = 0 up to
  |r_0| <= 0.7854), the least number of Taylor terms K >= 2 with truncation error at most 2^-10 u^n relative to
  sin r or cos r on |r| <= R_j, where R_0 = 0.78541 and R_j = 2^-j (1 + 2^-50).

usage: python3 scripts/trig_tables.py [out.rs]   (default src/trig/tables.rs; prints a summary)"""
import os
import re
import sys
from fractions import Fraction as Fr

F = 1216            # fraction bits of the reduction's fixed-point accumulator
LIMBS = 20          # u64 limbs, 1280 bits
G = 1400            # bits of the pi computation
TERM_EXP = 10       # Taylor truncation at most 2^-TERM_EXP u^n relative
R_TOP = Fr(78541, 100000)


def arctan_inv(m, g):
    """floor-summed 2^g arctan(1/m): (value, error bound), |2^g arctan(1/m) - value| <= error"""
    s = 0
    k = 0
    while True:
        d = (2 * k + 1) * m ** (2 * k + 1)
        t = (1 << g) // d                   # floor: error in [0, 1)
        if t == 0:
            break
        s += t if k % 2 == 0 else -t
        k += 1
    # k terms summed, each floor off by less than 1; the alternating tail is below its first term, below 2^-g
    return s, k + 1


def pi_interval(formula, g):
    """pi 2^g in [lo, hi] from sum c_i arctan(1/m_i) = pi/4"""
    v = 0
    e = 0
    for c, m in formula:
        a, err = arctan_inv(m, g)
        v += 4 * c * a
        e += 4 * abs(c) * err
    return v - e, v + e


MACHIN = [(4, 5), (-1, 239)]
GAUSS = [(12, 18), (8, 57), (-5, 239)]


def check(ok, what):
    """a failed check stops the generator before it writes, also under python -O (which drops asserts)"""
    if not ok:
        sys.exit(f'trig_tables.py: {what}')


def round_int(lo, hi, sh):
    """the integer nearest to x / 2^sh for every x in [lo, hi] (integers), or an error if the interval straddles a
    rounding boundary"""
    a = (lo + (1 << (sh - 1))) >> sh
    b = (hi + (1 << (sh - 1))) >> sh
    check(a == b, 'interval straddles a rounding boundary')
    return a


def rn(x):
    """binary64 nearest to the rational x (Python's int / int true division is correctly rounded)"""
    return x.numerator / x.denominator if x != 0 else 0.0


def greedy(x, n):
    out = []
    for _ in range(n):
        f = rn(x)
        out.append(f)
        x -= Fr(f)
    return out


def f64_bits(f):
    import struct
    return struct.unpack('<Q', struct.pack('<d', f))[0]


def two_over_pi(lo, hi, g):
    """RN(2/pi) for pi 2^g in [lo, hi]: the same for both ends"""
    a = rn(Fr(2 << g, hi))
    b = rn(Fr(2 << g, lo))
    check(a == b, '2/pi rounding not determined')
    return a


def fact(n):
    r = 1
    for i in range(2, n + 1):
        r *= i
    return r


def k_table(n, sine):
    """least K >= 2 per bucket with truncation <= 2^-TERM_EXP u^n relative"""
    u_n = Fr(1, 2 ** (53 * n))
    nb = 53 * n // 2
    ks = []
    for j in range(nb):
        R = R_TOP if j == 0 else Fr(1, 2 ** j) * (1 + Fr(1, 2 ** 50))
        low = 1 - R * R / 6 if sine else 1 - R * R / 2   # sin r / r >= 1 - r^2/6, cos r >= 1 - r^2/2
        K = 2
        while True:
            # the alternating series' remainder after K terms is below the first omitted term
            rem = R ** (2 * K) / fact(2 * K + 1) if sine else R ** (2 * K) / fact(2 * K)
            if rem <= Fr(1, 2 ** TERM_EXP) * u_n * low:
                break
            K += 1
        ks.append(K)
    return ks


def qd_pi_parts(root):
    src = open(os.path.join(root, 'src', 'qd.rs')).read()
    m = re.search(r'pub const PI: QD = QD \{\s*x: \[(.*?)\]', src, re.S)
    return [int(h, 16) for h in re.findall(r'0x([0-9a-f]+)', m.group(1))]


def main():
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(root, 'src', 'trig', 'tables.rs')

    lo, hi = pi_interval(MACHIN, G)
    glo, ghi = pi_interval(GAUSS, G)
    check(hi - lo < 2 ** (G - 1300) and ghi - glo < 2 ** (G - 1300), 'pi intervals too wide')
    check(max(lo, glo) <= min(hi, ghi), 'Machin and Gauss disagree')
    # P = round(pi/2 2^F) from pi 2^G: pi/2 2^F = pi 2^G / 2^(G - F + 1)
    P = round_int(lo, hi, G - F + 1)
    check(P == round_int(glo, ghi, G - F + 1), 'P differs between Machin and Gauss')
    check(P.bit_length() <= F + 1, 'P too long')
    limbs = [(P >> (64 * i)) & (2 ** 64 - 1) for i in range(LIMBS)]
    t2p = two_over_pi(lo, hi, G)
    check(t2p == two_over_pi(glo, ghi, G), 'RN(2/pi) differs between Machin and Gauss')
    # QD::PI's parts are the greedy four-part rounding of pi
    want = qd_pi_parts(root)
    for a, b in ((lo, hi), (glo, ghi)):
        for end in (a, b):
            check([f64_bits(f) for f in greedy(Fr(end, 2 ** G), 4)] == want, 'QD::PI differs')

    ks = {n: k_table(n, True) for n in (2, 4, 8)}
    kc = {n: k_table(n, False) for n in (2, 4, 8)}
    kmax = max(max(ks[8]), max(kc[8]))
    sin_c = [greedy(Fr((-1) ** k, fact(2 * k + 1)), 8) for k in range(kmax)]
    cos_c = [greedy(Fr((-1) ** k, fact(2 * k)), 8) for k in range(kmax)]

    def arr(v):
        return '[' + ', '.join(f'f64::from_bits(0x{f64_bits(f):016x})' for f in v) + ']'

    L = []
    w = L.append
    w('// Generated by scripts/trig_tables.py; do not edit. The derivations are in its docstring.')
    w('')
    w(f'/// fraction bits of the reduction\'s fixed-point accumulator')
    w(f'pub(crate) const F: u32 = {F};')
    w(f'/// round(pi/2 2^{F}), little-endian u64 limbs')
    w(f'pub(crate) const P: [u64; {LIMBS}] = [')
    for i in range(0, LIMBS, 4):
        w('    ' + ' '.join(f'0x{x:016x},' for x in limbs[i:i + 4]))
    w('];')
    w('/// RN(2/pi)')
    w(f'pub(crate) const TWO_OVER_PI: f64 = f64::from_bits(0x{f64_bits(t2p):016x});')
    w(f'/// (-1)^k / (2k+1)!, eight greedy parts, k = 0..{kmax - 1}')
    w(f'pub(crate) const SIN: [[f64; 8]; {kmax}] = [')
    for c in sin_c:
        w(f'    {arr(c)},')
    w('];')
    w(f'/// (-1)^k / (2k)!, eight greedy parts, k = 0..{kmax - 1}')
    w(f'pub(crate) const COS: [[f64; 8]; {kmax}] = [')
    for c in cos_c:
        w(f'    {arr(c)},')
    w('];')
    for n in (2, 4, 8):
        for name, t in (('KS', ks[n]), ('KC', kc[n])):
            what = 'sin' if name == 'KS' else 'cos'
            w(f'/// terms of the {what} series for {n} parts, by bucket j of |r_0| (2^-(j+1) <= |r_0| < 2^-j)')
            w(f'pub(crate) const {name}{n}: [u8; {len(t)}] = [')
            for i in range(0, len(t), 24):
                w('    ' + ' '.join(f'{x},' for x in t[i:i + 24]))
            w('];')
    open(out, 'w').write('\n'.join(L) + '\n')
    print(f'pi from Machin and Gauss agree to 2^-{G - (max(hi, ghi) - min(lo, glo)).bit_length()}; '
          f'P = round(pi/2 2^{F}) has {P.bit_length()} bits; RN(2/pi) = {t2p!r}')
    for n in (2, 4, 8):
        print(f'n = {n}: sin terms {ks[n][0]} (top bucket) .. {ks[n][-1]}, cos terms {kc[n][0]} .. {kc[n][-1]}')
    print(f'wrote {out}')


if __name__ == '__main__':
    main()
