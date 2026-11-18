"""The sine, cosine and tangent of expansion-error-bounds.pdf (the appendix on the trigonometric functions): the bounds
of the evaluation of sin r and cos r by Taylor series in r^2, step by step in exact rationals, from part bounds carried
through every operation by Lemma 20 (the paper's algorithms at n parts, multidouble's octo-double at n = 8), or from
the double-word algorithms' published relative bounds (multidouble's double-double), then the reduction's and the
quotient's errors. Every formula is nondecreasing in the quantities rounded up by `up`, so the values are upper
bounds.

The algorithm, per bucket j of |r_0| (2^-(j+1) <= |r_0| < 2^-j, j = 0 for [1/2, 0.7854]), with z = r r, K terms:
  sin r = ADD(r, MUL(r, MUL(z, p_1))),  p_(K-1) = s_(K-1),  p_k = ADD(MUL(z, p_(k+1)), s_k),  s_k = (-1)^k/(2k+1)!
  cos r = ADDF(MUL(z, q_1), 1),        q_(K-1) = c_(K-1),  q_k = ADD(MUL(z, q_(k+1)), c_k),  c_k = (-1)^k/(2k)!
the constants rounded greedily to n parts, and r either x itself (k = 0, x on the ladder |x_i| <= (2u)^i |x_0|) or
the greedy n-part rounding of the exact x - k pi/2 (its parts within the same ladder). Units: r, w and sin r in |r|,
z and t in r^2, the Horner sums absolute; |r| <= rbar_j (R below).

usage: trig_consts.py [check]     (check: the tables of src/trig/tables.rs, and the controls, must pass)"""
import math
import os
import re
import sys
from fractions import Fraction as Fr

from div_consts import div_consts
from sqrt_consts import op_bounds, up

P = 53
U = Fr(1, 2 ** P)
US = U / (1 + U)
TERM_EXP = 10
R_TOP = Fr(78541, 100000)
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def fact(n):
    r = 1
    for i in range(2, n + 1):
        r *= i
    return r


# ---------------------------------------------------------------------------------------------------------------
# rational bounds of the elementary functions at R (alternating Taylor sums, 0 < R < 1.6)
# ---------------------------------------------------------------------------------------------------------------

def sin_lo(x):
    return x - x ** 3 / 6 + x ** 5 / 120 - x ** 7 / 5040


def sin_hi(x):
    return x - x ** 3 / 6 + x ** 5 / 120


def cos_lo(x):
    return 1 - x ** 2 / 2 + x ** 4 / 24 - x ** 6 / 720


def sinc_lo(x):
    """sin x / x >= 1 - x^2/6"""
    return 1 - x * x / 6


def tan_hi(x):
    return sin_hi(x) / cos_lo(x)


# ---------------------------------------------------------------------------------------------------------------
# the operations' error models
# ---------------------------------------------------------------------------------------------------------------

class Paper:
    """the paper's algorithms at n parts: Lemma 20 (op_bounds), errors and part bounds"""
    def __init__(self, n):
        self.n = n
        self.name = f'paper n={n}'

    def lead(self, kind):
        return U ** self.n

    def op(self, kind, al, be, zb, lam=None):
        """(error bound for |Z| <= zb, the part of it not proportional to |Z|, the result's part bounds)"""
        eps, parts, _ = op_bounds(kind, self.n, U, al, be, zb, lam)
        return eps, eps - U ** self.n * zb, parts

    def div(self, theta):
        return U ** self.n + div_consts(self.n, P, theta)['K'] * U ** (self.n + 1)


class DoubleWord:
    """multidouble's double-double: DWTimesDW3 (Joldes, Muller, Popescu 2017, Alg. 12; Muller and Rideau 2022,
    Thm. 2.8), AccurateDWPlusDW (JMP17 Alg. 6, Thm. 3.1), DWPlusFP (JMP17 Alg. 4, Thm. 2.2), DWDivDW2 (JMP17 Alg. 17,
    Thm. 7.1): relative error bounds"""
    n = 2
    name = 'double-word'
    EPS = {'mul': (4 * U ** 2 + U ** 3 / 2) / (1 + U) ** 2, 'add': 3 * U ** 2 / (1 - 4 * U), 'add_f': 2 * U ** 2}

    def lead(self, kind):
        return self.EPS[kind]

    def op(self, kind, al, be, zb, lam=None):
        return self.EPS[kind] * zb, Fr(0), None

    def div(self, theta):
        return 15 * U ** 2 + 56 * U ** 3


# ---------------------------------------------------------------------------------------------------------------
# the constants and the series lengths
# ---------------------------------------------------------------------------------------------------------------

def rn(x):
    return x.numerator / x.denominator if x != 0 else 0.0


def greedy(x, n):
    out = []
    for _ in range(n):
        f = rn(x)
        out.append(f)
        x -= Fr(f)
    return out


def coefs(n, kmax, sine, kept=None):
    """(exact value, part bounds of the n-part constant, |constant - value|) for k < kmax; with `kept`, only that many
    parts of the greedy rounding are kept (a control)"""
    out = []
    for k in range(kmax):
        v = Fr((-1) ** k, fact(2 * k + 1) if sine else fact(2 * k))
        g = greedy(v, kept or n) + [0.0] * (n - (kept or n))
        out.append((v, [abs(Fr(t)) for t in g], abs(sum(Fr(t) for t in g) - v)))
    return out


def bucket_r(n, j):
    """rbar_j >= |r| in bucket j; j = nb is the tiny bucket, |r_0| < u^(n/2) = 2^-(53n/2)"""
    if j == 0:
        return R_TOP
    return Fr(1, 2 ** j) * (1 + Fr(1, 2 ** 50))


def k_table(n, sine):
    """the least K >= 2 per bucket with the first omitted term at most 2^-10 u^n of sin r or cos r"""
    ks = []
    for j in range(53 * n // 2):
        R = bucket_r(n, j)
        low = sinc_lo(R) if sine else 1 - R * R / 2
        K = 2
        while (R ** (2 * K) / fact(2 * K + 1) if sine else R ** (2 * K) / fact(2 * K)) > Fr(1, 2 ** TERM_EXP) * U ** n * low:
            K += 1
        ks.append(K)
    return ks


def rust_tables():
    src = open(os.path.join(ROOT, 'src', 'trig', 'tables.rs')).read()
    out = {}
    for name in ('KS2', 'KC2', 'KS4', 'KC4', 'KS8', 'KC8'):
        m = re.search(rf'const {name}: \[u8; \d+\] = \[(.*?)\];', src, re.S)
        out[name] = [int(v) for v in re.findall(r'\d+', m.group(1))]
    for name in ('SIN', 'COS'):
        m = re.search(rf'const {name}: \[\[f64; 8\]; \d+\] = \[(.*?)\n\];', src, re.S)
        rows = re.findall(r'\[(f64::from_bits.*?)\]', m.group(1))
        out[name] = [[int(h, 16) for h in re.findall(r'0x([0-9a-f]+)', r)] for r in rows]
    return out


# ---------------------------------------------------------------------------------------------------------------
# the evaluation
# ---------------------------------------------------------------------------------------------------------------

def ladder(n, theta):
    """part bounds of r in units of |r|, for r on |r_i| <= (theta u)^i |r_0|: |r_0| <= |r| (1-t)/(1-2t), t = theta u"""
    t = theta * U
    return [up((theta * U) ** i * (1 - t) / (1 - 2 * t)) for i in range(n)]


def horner(M, zabs, zmax, ez, R2, cs, K):
    """p_1 by Horner's scheme from p_(K-1) = c_(K-1): (E_1 with |p_1 - p_1^e(r^2)| <= E_1, part bounds of p_1)"""
    v, parts, d = cs[K - 1]
    E, pb = d, parts
    for k in range(K - 2, 0, -1):
        nxt = abs(cs[k + 1][0])
        em, _, mu = M.op('mul', zabs, pb, zmax * (nxt + E))
        vk, ck, dk = cs[k]
        drift = zmax * E + ez * R2 * nxt + dk + em
        ea, _, pb = M.op('add', mu, ck, up(abs(vk) + drift))
        E = up(drift + ea)
    return E, pb


def eval_sin(M, n, R, K, alpha, cs):
    """(lead, E_S, part bounds): |sin_r(r) - sin r| <= lead |sin r| + E_S |r|"""
    R2 = R * R
    ez, _, zeta = M.op('mul', alpha, alpha, Fr(1))
    zabs = [up(t * R2) for t in zeta] if zeta else None
    zmax = (1 + ez) * R2
    E, pb = horner(M, zabs, zmax, ez, R2, cs, K)
    s1 = abs(cs[1][0])
    et, _, tau = M.op('mul', zeta, pb, up((1 + ez) * (s1 + E)))
    Et = up((1 + ez) * E + ez * s1 + et)
    ew, _, om = M.op('mul', alpha, tau, up(s1 + Et))
    D = up(R2 * (Et + ew) + R ** (2 * K) / fact(2 * K + 1))
    _, rest, ypart = M.op('add', alpha, [up(t * R2) for t in om] if om else None, 1 + D)
    lead = M.lead('add')
    return lead, up((1 + lead) * D + rest), ypart


def eval_cos(M, n, R, K, cs):
    """(lead, E_C, part bounds): |cos_r(r) - cos r| <= lead |cos r| + E_C"""
    R2 = R * R
    alpha = ladder(n, 2)
    ez, _, zeta = M.op('mul', alpha, alpha, Fr(1))
    zabs = [up(t * R2) for t in zeta] if zeta else None
    zmax = (1 + ez) * R2
    E, pb = horner(M, zabs, zmax, ez, R2, cs, K)
    c1 = abs(cs[1][0])
    et, _, tau = M.op('mul', zeta, pb, up((1 + ez) * (c1 + E)))
    Et = up((1 + ez) * E + ez * c1 + et)
    D = up(R2 * Et + R ** (2 * K) / fact(2 * K))
    _, rest, ypart = M.op('add_f', [up(t * R2) for t in tau] if tau else None, [Fr(1)], 1 + D)
    lead = M.lead('add_f')
    return lead, up((1 + lead) * D + rest), ypart


def theta_of(parts, lo):
    """the least theta >= 1 (up to rounding up) with parts[i] <= (theta u)^i lo for i >= 1, lo <= |x_0|"""
    th = Fr(1)
    for i in range(1, len(parts)):
        if parts[i] == 0:
            continue
        r = parts[i] / lo
        t = Fr(math.exp(math.log(float(r)) / i) / float(U) * (1 + 1e-9)).limit_denominator(2 ** 40)
        while (t * U) ** i < r:
            t *= 1 + Fr(1, 2 ** 30)
        th = max(th, t)
    return th


def bucket_bounds(M, n, j, ks, kc, cs_s, cs_c):
    """the relative bounds of sin_r and cos_r (evaluation only), of the reductions, and of tan, for bucket j"""
    nb = 53 * n // 2
    un = U ** n
    alpha = ladder(n, 2)
    if j == nb:
        # |r| < 2^-(53n/2): sin r = r, cos r = 1
        R = Fr(1, 2 ** (53 * n // 2)) * (1 + Fr(1, 2 ** 50))
        dS = R * R / 6 / sinc_lo(R)
        dC = R * R / 2 / cos_lo(R)
        sp = cp = None
        Ks = Kc = 0
    else:
        R = bucket_r(n, j)
        Ks, Kc = ks[j], kc[j]
        lS, ES, sp = eval_sin(M, n, R, Ks, alpha, cs_s)
        lC, EC, cp = eval_cos(M, n, R, Kc, cs_c)
        dS = up(lS + ES / sinc_lo(R))
        dC = up(lC + EC / cos_lo(R))
    # the reduction: |r - r_exact| <= u^n |r| (1 + 2u^n), the rest absolute (|k| 2^-1217, in the statement)
    red = un * (1 + 2 * un)
    rS = red
    rC = red * R * tan_hi(R)
    rT = red * 2 * R / sin_lo(2 * R)
    # the quotient: the ladders of the computed sin r and cos r
    if j == nb:
        # r on the ladder |r_i| <= (2u)^i |r_0| over the constant 1
        th = Fr(2)
    elif sp is not None:
        s_lo = sinc_lo(R) * (1 - dS)
        c_lo = cos_lo(R) * (1 - dC)
        th = max(theta_of(sp, s_lo - sum(sp[1:])), theta_of(cp, c_lo - sum(cp[1:])))
    else:
        th = None
    # Theorem 18 is stated for a ladder H(theta) with theta u <= 1/4 (Definition 7)
    require(th is None or th * U <= Fr(1, 4), f'theta_j u > 1/4 in bucket {j}')
    dD = M.div(th)
    dT = max((1 + dS) * (1 + dD) / (1 - dC), (1 + dC) * (1 + dD) / (1 - dS)) - 1
    f = 1 + 2 * un
    return dict(j=j, R=R, Ks=Ks, Kc=Kc, sin=up((dS + rS) * f), cos=up((dC + rC) * f), tan=up((dT + rT) * f),
                dS=dS, dC=dC, dD=dD, theta=th)


def run(M, n, ks, kc, coef_n=None):
    """the bounds of every bucket for M at n parts: (rows, max sin/cos, max tan)"""
    kmax = max(max(ks), max(kc))
    cs_s = coefs(n, kmax, True, coef_n)
    cs_c = coefs(n, kmax, False, coef_n)
    rows = []
    done = {}
    nb = 53 * n // 2
    for j in range(nb + 1):
        key = (ks[j], kc[j]) if j < nb else 'tiny'
        # buckets with the same series lengths: the first (largest R) bounds the rest, every bound being
        # nondecreasing in R and the relative denominators sin R / R, cos R nonincreasing
        if key in done:
            continue
        b = bucket_bounds(M, n, j, ks, kc, cs_s, cs_c)
        done[key] = b
        rows.append(b)
    # the early return of |x_0| < 2^-(53n/2): x, 1, x within (1/6, 1/2, 1/3 + ...) u^n
    T = Fr(1, 2 ** (53 * n // 2)) * (1 + Fr(1, 2 ** 50))
    early = dict(sin=T * T / 6 / sinc_lo(T), cos=T * T / 2 / cos_lo(T), tan=(tan_hi(T) / T - 1))
    sc = max(max(b['sin'], b['cos']) for b in rows + [early])
    tn = max(max(b['tan'] for b in rows), early['tan'])
    return rows, sc, tn


def require(ok, what):
    """a failed check exits nonzero, also under python -O (which drops asserts)"""
    if not ok:
        sys.exit(f'trig_consts.py: {what}')


def fmt(x, n):
    return f'{float(x / U ** n):.6f}'


def main():
    check = len(sys.argv) > 1 and sys.argv[1] == 'check'
    tabs = rust_tables()
    ks = {n: k_table(n, True) for n in (2, 4, 8, 12)}
    kc = {n: k_table(n, False) for n in (2, 4, 8, 12)}
    for n in (2, 4, 8):
        require(ks[n] == tabs[f'KS{n}'] and kc[n] == tabs[f'KC{n}'], f'src/trig/tables.rs differs at n = {n}')
    for name, sine in (('SIN', True), ('COS', False)):
        for k, row in enumerate(tabs[name]):
            v = Fr((-1) ** k, fact(2 * k + 1) if sine else fact(2 * k))
            import struct
            g = [struct.unpack('<Q', struct.pack('<d', t))[0] for t in greedy(v, 8)]
            require(g == row, f'{name}[{k}] differs from the greedy rounding')
    print('src/trig/tables.rs: series lengths and constants as derived here')
    out = {}
    for M in (DoubleWord(), Paper(2), Paper(4), Paper(8), Paper(12)):
        n = M.n
        rows, sc, tn = run(M, n, ks[n], kc[n])
        out[M.name] = (rows, sc, tn)
        top = rows[0]
        print(f'{M.name}: sin, cos <= {fmt(sc, n)} u^{n}, tan <= {fmt(tn, n)} u^{n}; top bucket '
              f'(K = {top["Ks"]}, {top["Kc"]}): sin r {fmt(top["dS"], n)}, cos r {fmt(top["dC"], n)}, '
              f'quotient {fmt(top["dD"], n)}' + (f' (theta = {float(top["theta"]):.6f})' if top['theta'] else '') + f' u^{n}')
    rows = out['paper n=8'][0]
    print('paper n=8 by bucket (sin x, cos x, tan x in u^8): ' + ', '.join(
        f'j={b["j"]}: {fmt(b["sin"], 8)}/{fmt(b["cos"], 8)}/{fmt(b["tan"], 8)}' for b in rows[:6]) + ', ...')
    top = rows[0]
    R = top['R']
    print(f'paper n=8, cos in bucket 0 (u^8): reduction {fmt(U ** 8 * R * tan_hi(R), 8)}, last ADDF 1, '
          f'the rest {fmt(top["dC"] - U ** 8, 8)}')
    for jmin in (1, 5):
        sc = max(max(b['sin'], b['cos']) for b in rows if b['j'] >= jmin)
        tn = max(b['tan'] for b in rows if b['j'] >= jmin)
        print(f'paper n=8, |r_0| < 2^-{jmin}: sin, cos <= {fmt(sc, 8)} u^8, tan <= {fmt(tn, 8)} u^8')
    if check:
        # controls: a sine series two terms short, or a constant rounded to n - 1 parts, must raise the bound
        n = 8
        M = Paper(8)
        _, sc, tn = out['paper n=8']
        short = [max(2, k - 2) for k in ks[8]]
        _, sc2, _ = run(M, 8, short, kc[8])
        require(sc2 > 4 * sc, 'control: a short series did not raise the bound')
        _, sc3, _ = run(M, 8, ks[8], kc[8], coef_n=7)
        require(sc3 > 4 * sc, 'control: seven-part constants did not raise the bound')
        print('check: PASS (the controls raise the bound to', fmt(sc2, 8), 'and', fmt(sc3, 8), 'u^8)')


if __name__ == '__main__':
    main()
