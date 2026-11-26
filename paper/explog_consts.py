"""Theorems 40 and 42, Lemma 43 and Proposition 44 of expansion-error-bounds.pdf: the error bounds of exp and ln
(src/explog.rs) in exact rationals. For the octo-double algorithms at any number of parts n, Lemma 13 bounds every
operation's error and its result's parts from its operands' part bounds, and the bounds are carried through every step;
for the double-double ones, the published relative bounds of the double-word operations. A scaling by a power of two
that leaves the normal range, and the start's quotient, add at most ETA0 = 2^-1075 per part; the products obey (A2) but
for those that only choose k, m and the degree. The start of the logarithm is the crate's own binary64 logarithm, whose
error is bounded here too. Every bound is computed in rationals rounded up to 200-bit dyadic numbers (sqrt_consts.up);
every formula is nondecreasing in the quantities so rounded, and nonincreasing in the lower bounds of |r| (a), which are
not rounded.

Every printed bound is rounded up: its decimals by up_dec, its base-2 exponents by lg2_up.

usage: explog_consts.py           the bound of the start ln_f64, the bounds of the crate's DD and OD exp and ln, and
                                  of the n-part algorithms at n = 4 and 12 (about 7 minutes)
       explog_consts.py check     the octo-double log's bounds sampled for monotonicity and convexity in |ln x|, the
                                  property its chords use, at nine points of every k = 0 case and 22 of four k != 0
                                  cases; a concave function is the control, and must be caught"""
import sys, os, math
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'scripts'))
from sqrt_consts import up, lemma_L  # noqa: E402
import explog_constants as EC  # noqa: E402

CONST = EC.constants()
LN2_A, LN2_B = CONST['ln2']          # ln 2 lies in [LN2_A, LN2_B]
LN2_HI = Fr(CONST['hi'])             # 42 bits
L2E = Fr(1.4426950408889634)         # f64 LOG2_E = RN(1 / ln 2)
XMAX = Fr(7452, 10)                  # |x_0| <= 745.2 for exp; |ln x| <= 745.2 for log
KMAX = 1075                          # |k| <= 1075
ETA0 = Fr(1, 2 ** 1075)              # half the least subnormal: a scaling or quotient that underflows errs by this
UB = Fr(1, 2 ** 46)                  # U = RN(RN(sum |r_i|)(1 + 2^-48)) in [2^e, 2^(e+1)): sum |r_i| >= 2^e (1 - UB)


# ---------------------------------------------------------------------------------------------------------------
# exact helpers
# ---------------------------------------------------------------------------------------------------------------

def expm1_up(z, N=60):
    """an upper bound of e^z - 1 for rational 0 <= z <= 2"""
    assert 0 <= z <= 2
    s, t = Fr(0), Fr(1)
    for i in range(1, N):
        t = up(t * z / i)
        s += t
    t = up(t * z / N)
    return up(s + t / (1 - z / (N + 1)))


def exp_up(z):
    return 1 + expm1_up(z)


def exp_lo(z, N=40):
    """a lower bound of e^z for rational z >= 0: a partial sum, rounded down"""
    s, t = Fr(1), Fr(1)
    for i in range(1, N):
        t = t * z / i
        if t.denominator.bit_length() > 300:
            t = 1 / up(1 / t)
        s += t
    return 1 / up(1 / s)


def mexpm1_up(z):
    """an upper bound of 1 - e^-z = e^-z (e^z - 1) for rational z >= 0"""
    return up(expm1_up(z) / exp_lo(z))


def vecb(X, u, n, convex):
    """VecSum output bounds from level bounds (Theorem 9(d)); convex: the second of its two bounds alone"""
    us = u / (1 + u)
    sig = [sum(X[l:]) for l in range(n + 1)]
    V = [(1 + u) ** n * sig[0]]
    for j in range(1, n + 1):
        b2 = us * (1 + u) ** (n - j) * sig[j - 1]
        V.append(b2 if convex else min(X[j - 1], b2))
    return V


def lemma13(name, n, u, al, be, Zb, lam=None, convex=False):
    """Lemma 13: the error bound and the result's part bounds of MUL, ADD, MULF and ADDF from the operands' part
    bounds al, be (be = [|b|] for MULF and ADDF), Zb >= |Z| and, optionally, lam (lambda_m >= |a_m + b_m| for ADD,
    lambda_0 >= |a_0 + b| for ADDF). sqrt_consts.op_bounds, with convex as in vecb."""
    Rr = Fr(0); Dl = Fr(0)
    if name == 'mul':
        Pm = lambda m: sum(al[i] * be[m - i] for i in range(n) if 0 <= m - i < n)
        A = [(1 + u) * Pm(0)] + [(1 + u) * Pm(m) + u * Pm(m - 1) for m in range(1, n)]
        A.append(sum(al[i] * be[n - i] for i in range(1, n)) + u * Pm(n - 1))
        T = [m * (m + 1) for m in range(n)]; Q = n * n + n - 1
        X, Rr = lemma_L(A, T, Q, u)
        Dl = sum(al[i] * be[j] for i in range(n) for j in range(n) if i + j >= n + 1)
    elif name in ('add', 'mul_f'):
        lm = (lam if lam is not None else [al[m] + be[m] for m in range(n)]) if name == 'add' else \
            [al[m] * be[0] for m in range(n)]
        A = [(1 + u) * lm[0]] + [(1 + u) * lm[m] + u * lm[m - 1] for m in range(1, n)] + [u * lm[n - 1]]
        X, Rr = lemma_L(A, list(range(n)), n - 1, u)
    elif name == 'add_f':
        l0 = lam[0] if lam is not None else al[0] + be[0]
        e_ = [u * l0]
        X = [(1 + u) * l0]
        for m in range(1, n):
            X.append((1 + u) * (al[m] + e_[m - 1]))
            e_.append(u * (al[m] + e_[m - 1]))
        X.append(e_[n - 1])
    else:
        raise ValueError(name)
    V = vecb(X, u, n, convex)
    Psi = sum((u ** n + u ** (n + 1 - j)) * V[j] for j in range(1, n + 1))
    eps = u ** n * Zb + (1 + u ** n) * (Rr + Dl) + Psi
    W = [sum(V[j] for j in range(k + 1, n + 1)) for k in range(n + 1)]
    parts = [(1 + u) * (Zb + Rr + Dl + W[1])]
    for i in range(1, n):
        parts.append((1 + u) * (u * parts[i - 1] + W[i]))
    return up(eps), [up(t) for t in parts]


# ---------------------------------------------------------------------------------------------------------------
# operation models: an operand is a list of part bounds (expansions) or None (double-words)
# ---------------------------------------------------------------------------------------------------------------

class Expansion:
    """the n-part algorithms of the paper (OD at n = 8): Lemma 13 at every operation"""

    def __init__(self, n, p, convex=False):
        self.n, self.u, self.convex = n, Fr(1, 2 ** p), convex
        self.name = f'n={n}'

    def const(self, parts):
        v = [abs(Fr(x)) for x in parts[:self.n]]
        return v + [Fr(0)] * (self.n - len(v))

    def mul(self, a, b, Zb):
        return lemma13('mul', self.n, self.u, a, b, Zb, convex=self.convex)

    def add(self, a, b, Zb, lam=None):
        return lemma13('add', self.n, self.u, a, b, Zb, lam=lam, convex=self.convex)

    def add_f(self, a, f, Zb, lam0=None):
        return lemma13('add_f', self.n, self.u, a, [abs(Fr(f))], Zb, lam=None if lam0 is None else [lam0],
                       convex=self.convex)

    def mul_f(self, a, f, Zb):
        return lemma13('mul_f', self.n, self.u, a, [abs(Fr(f))], Zb, convex=self.convex)

    def scale(self, a, s):
        return [up(x * s) for x in a]

    def ladder(self, top, theta, nparts=None):
        """part bounds of a value with |x| <= top whose parts satisfy H(theta) (only the first nparts nonzero)"""
        rho = Fr(theta) * self.u
        k = self.n if nparts is None else nparts
        x0 = up(top * (1 - rho) / (1 - 2 * rho))
        return [up(rho ** i * x0) if i < k else Fr(0) for i in range(self.n)]

    def tail(self, a):
        return sum(a[1:])


class DoubleWord:
    """the double-double algorithms: each operation's relative error bound, from the published theorems"""
    name = 'DD'

    def __init__(self, p=53, convex=False):
        u = self.u = Fr(1, 2 ** p)
        self.convex = convex
        self.n = 2
        self.a_add = 3 * u * u / (1 - 4 * u)        # AccurateDWPlusDW, Joldes-Muller-Popescu Thm 3.1, p >= 3
        self.a_addf = 2 * u * u                     # DWPlusFP, Joldes-Muller-Popescu Algorithm 4, p >= 3
        self.a_mul = 5 * u * u / (1 + u) ** 2       # DWTimesDW2, Muller-Rideau 2022, p >= 5
        self.a_mulf = 2 * u * u                     # DWTimesFP3, Joldes-Muller-Popescu Algorithm 9

    def const(self, parts):
        return None

    def mul(self, a, b, Zb):
        return up(self.a_mul * Zb), None

    def add(self, a, b, Zb, lam=None):
        return up(self.a_add * Zb), None

    def add_f(self, a, f, Zb, lam0=None):
        return up(self.a_addf * Zb), None

    def mul_f(self, a, f, Zb):
        return up(self.a_mulf * Zb), None

    def scale(self, a, s):
        return None

    def ladder(self, top, theta, nparts=None):
        return None

    def tail(self, a):
        return Fr(0)


# ---------------------------------------------------------------------------------------------------------------
# the start of the logarithm: the crate's binary64 logarithm (ln_f64), Lemma 43
# ---------------------------------------------------------------------------------------------------------------

def start_eta(p=53, J=9):
    """a bound of |ln_f64(h) - ln h| / |ln h| for every positive finite h != 1 (ln_f64(1) = 0): h = 2^e m exactly,
    m in [mu/2, mu] (mu = RN(sqrt 2)), s = RN((m - 1) / RN(m + 1)), z = RN(s^2), v by J fused multiply-adds from
    RN(1/(2J+1)), w = RN(2 s v), y = RN(e LN2 + w), LN2 = RN(ln 2). The relative errors are taken at |s| = sbar,
    z = sbar^2 (1 + theta_z), where each is largest; for e != 0, |e ln 2 + ln m| >= |e| ln 2 - ln mu, least at
    |e| = 1."""
    u = Fr(1, 2 ** p)
    us = u / (1 + u)
    mu = Fr(1.4142135623730951)
    sbar = (mu - 1) / (mu + 1)
    th_s = 2 * u                                        # s = s_t (1 + d2) / (1 + d1)
    th_z = (1 + th_s) ** 2 * (1 + us) - 1               # z = s_t^2 (1 + th_z)
    zmax = up(sbar ** 2 * (1 + th_z))
    # Horner with positive terms: v_j = RN(z v_(j+1) + c_j), c_j = RN(1/(2j+1)) (c_0 = 1 exact); the relative error
    # of v_j against V_j(z) = sum_(i >= j) z^(i-j) / (2i+1) is at most rel_j
    V = [Fr(0)] * (J + 2)
    rel = [Fr(0)] * (J + 2)
    V[J] = Fr(1, 2 * J + 1)
    rel[J] = us
    for j in range(J - 1, -1, -1):
        cj = Fr(1, 2 * j + 1)
        V[j] = cj + zmax * V[j + 1]
        cerr = Fr(0) if j == 0 else us
        rel[j] = up(((zmax * V[j + 1] * rel[j + 1] + cj * cerr) / V[j] + 1) * (1 + us) - 1)
    # V_J(z) against V_J(s_t^2): V' <= 1 / (2 (1 - z)), as i / (2i + 1) <= 1/2, and V >= 1
    th_V = up(th_z * zmax / (2 * (1 - zmax)))
    trunc = up(zmax ** (J + 1) / ((2 * J + 3) * (1 - zmax)))   # V_infinity - V_J, relative to V_infinity >= 1
    # w = 2 s v (1 + d4) against ln m = 2 s_t V_infinity(s_t^2)
    ew = up((1 + th_s) * (1 + rel[0]) * (1 + th_V) * (1 + us) / (1 - trunc) - 1)
    # e != 0: |y - y_t| <= us |y_t| + (1 + us) (|e| |LN2 - ln 2| + ew |ln m|), relative to |y_t| >= |e| ln 2 - ln mu,
    # largest at |e| = 1
    lnmu = up(Fr(1, 2) * LN2_B + (mu - SQRT2_LO) / SQRT2_LO)   # ln mu <= ln sqrt 2 + (mu - sqrt 2) / sqrt 2
    yl = LN2_A - lnmu
    dln2 = max(abs(Fr(0.6931471805599453) - LN2_A), abs(Fr(0.6931471805599453) - LN2_B))
    e_ne0 = up(us + (1 + us) * (dln2 + ew * lnmu) / yl)
    return up(max(ew, e_ne0)), dict(ew=ew, rel0=rel[0], trunc=trunc, e_ne0=e_ne0)


SQRT2_LO = Fr(14142135623730950488, 10 ** 19)   # below sqrt 2


# ---------------------------------------------------------------------------------------------------------------
# exp
# ---------------------------------------------------------------------------------------------------------------

class Exp:
    """exp at the model's precision: squaring threshold 2^-s (tau below), Taylor degree at most d, input ladder H(theta);
    the degree is d(e) = min(d, ceil(B / (-e - 1))) for |r'| < 2^(e+1), B = 53 n + 12"""

    def __init__(self, M, s, d, theta=2):
        self.M, self.s, self.d, self.theta = M, s, d, theta
        n, u = M.n, M.u
        self.u = u
        self.B = 53 * n + 12
        self.tau = Fr(1, 2 ** s)
        self.D = [Fr(x) for x in EC.greedy_interval(LN2_A - LN2_HI, LN2_B - LN2_HI, n)]
        self.Dsum = sum(self.D)
        self.De = max(abs(LN2_A - LN2_HI), abs(LN2_B - LN2_HI))                       # |ln 2 - LN2_HI|
        self.etaD = max(abs(LN2_A - LN2_HI - self.Dsum), abs(LN2_B - LN2_HI - self.Dsum))
        self.F = [[Fr(x) for x in EC.greedy(Fr(1, math.factorial(j)), n)] for j in range(d + 1)]
        # the crate's eight-part constants begin with these (a greedy expansion's first n parts are its n-part one)
        if n <= 8:
            assert all([Fr(x) for x in CONST['fact'][j][:n]] == self.F[j] for j in range(min(d, EC.JMAX) + 1))
            assert [Fr(x) for x in CONST['lo'][:n]] == self.D
        self.Ferr = [abs(sum(self.F[j]) - Fr(1, math.factorial(j))) for j in range(d + 1)]
        self.dl2e = max(abs(L2E - 1 / LN2_A), abs(L2E - 1 / LN2_B))

    def degree(self, e):
        """the crate's degree for |r'| < 2^(e+1)"""
        if e < -1 - self.B:
            return 1
        return min(self.d, -(-self.B // (-e - 1)))

    # -- the reduction: k = round(RN(x_0 L2E)), x' = (x_0 - k LN2_HI, x_1, ...), r = x' + MULF(LN2_LO, -k)
    def rho_e(self, X, xtail):
        """|x - k ln 2| for |x_0| <= X with |x - x_0| <= xtail"""
        beta = up(X * (self.dl2e + self.u * L2E))                # |RN(x_0 L2E) - x_0 / ln 2|
        return up(LN2_B * (Fr(1, 2) + beta) + xtail)

    def reduce(self, xparts, X, xtail, Zr=None):
        """k != 0, |x_0| <= X, |x - x_0| <= xtail, x's parts xparts (None for double-words). Returns the error
        delta of r against x - k ln 2, r's part bounds, and the full-range bound of |r|, for |x - k ln 2| <= Zr."""
        M, K = self.M, KMAX
        re = self.rho_e(X, xtail)
        Zr = re if Zr is None else Zr
        if xparts is not None:
            xp = [up(re + xtail + K * self.De)] + xparts[1:]      # x_0 - k LN2_HI is exact
        else:
            xp = None
        e1, P = M.mul_f(M.const(self.D), K, up(K * abs(self.Dsum)))
        if xparts is not None:
            e2, rp = M.add(xp, P, up(Zr + K * self.etaD + e1))
            dr = up(e1 + e2 + K * self.etaD)
        else:
            # double-words: Q = DWPlusFP(P, x_l), r = DWPlusFP(Q, x_h - k LN2_HI)
            eq, _ = M.add_f(None, 0, up(K * abs(self.Dsum) + e1 + xtail))
            e2, rp = M.add_f(None, 0, up(Zr + K * self.etaD + e1 + eq))
            e2 = up(e2 + eq)
            dr = up(e1 + e2 + K * self.etaD)
        return dict(dr=dr, parts=rp, re=re, e1=e1, e2=e2)

    def tj(self, j, bp, sigma, convex):
        """a bound of |e^(2^j r') - 1| for |r'| <= bp of sign sigma"""
        z = up(bp * 2 ** j)
        if sigma > 0:
            return expm1_up(z)
        return z if convex else mexpm1_up(z)

    def core(self, rp, b, m, d, sigma, a=Fr(0), cap=None):
        """t ~ e^r - 1 for r with part bounds rp, a <= |r| <= b, sign sigma, m squarings and degree d, the sum of
        r's parts' magnitudes below cap 2^m: |t - (e^r - 1)| <= E"""
        M, n = self.M, self.M.n
        convex = M.convex
        sc = Fr(1, 2 ** m)
        # sum |r_i| < cap selects the case, so |r| and each |r_i| are below it (in convex mode, without the minima)
        bc = b if (convex or cap is None) else min(b, cap)
        # the scaling of r by 2^-m may move each part by ETA0, so |r'| by n ETA0
        bp = up(bc * sc + (n * ETA0 if m > 0 else 0))
        if rp is not None:
            rp = [up((x if (convex or cap is None) else min(x, cap)) * sc) for x in rp]
        # r' = 2^-m r may lose ETA0 per part to the subnormals: t then approximates e^(r' + lam) - 1, |lam| <= n ETA0,
        # within e^(b') n ETA0 <= 2 n ETA0 of e^r' - 1
        shift = 2 * n * ETA0 if m > 0 else Fr(0)
        if m > 0:
            rp = addeta(rp, 1)
        trunc = up(bp ** (d + 1) / math.factorial(d + 1) / (1 - bp / (d + 2)) + shift)
        if d == 1:
            E = trunc                                       # t = r', exactly
            tp = rp
        else:
            # Horner: q_d = 1/d!, q_j = 1/j! + r' q_(j+1) down to j = 2, q_2 ~ sum_(i=2)^d r'^(i-2) / i!
            qv, qe, qp = Fr(1, math.factorial(d)), self.Ferr[d], M.const(self.F[d])
            for j in range(d - 1, 1, -1):
                ep, pp = M.mul(rp, qp, up(bp * (qv + qe)))
                cj = Fr(1, math.factorial(j))
                ea, qp = M.add(M.const(self.F[j]), pp, up(cj + self.Ferr[j] + bp * (qv + qe) + ep))
                qe = up(self.Ferr[j] + bp * qe + ep + ea)
                qv = up(cj + bp * qv)
            # t_0 = r' + r' (r' q_2), the outer product and sum in r' 2^-er (exact scalings, Lemma 13's bounds scale
            # with them); scaling back loses at most ETA0 per part below 2^-1022
            e1, w1p = M.mul(rp, qp, up(bp * (qv + qe)))
            e2, wp = M.mul(rp, w1p, up(bp * (bp * (qv + qe) + e1)))
            E = up(e2 + bp * (e1 + bp * qe) + trunc)
            e3, tp = M.add(rp, wp, up(self.tj(0, bp, sigma, convex) + E))
            E = up(E + e3 + n * ETA0)
            tp = addeta(tp, 1)
        steps = [dict(E=E)]
        # m squarings t <- 2 t + t^2
        for j in range(m):
            Tj = self.tj(j, bp, sigma, convex)
            # |2 + 2 t*_j| <= 2 (1 + Tj) for r > 0, and 2 (1 - |t*_j|) <= 2 e^(-2^j |r'|) for r < 0
            g = 1 + Tj if sigma > 0 else (Fr(1) if a == 0 else 1 / exp_lo(a * sc * 2 ** j))
            em, mp = M.mul(tp, tp, up((Tj + E) ** 2))
            Z = up(self.tj(j + 1, bp, sigma, convex) + 2 * E + 2 * Tj * E + E * E + em)
            ea, tp = M.add(None if tp is None else M.scale(tp, 2), mp, Z)
            E = up(2 * E * g + E * E + em + ea)
            steps.append(dict(E=E, mul=em, add=ea))
        return dict(E=E, parts=tp, T=self.tj(m, bp, sigma, convex), bp=bp, steps=steps)

    def groups(self, tail, top):
        """the cases of step (2): (m, d, lo, hi, cap) with lo <= |r| <= hi and sum |r_i| < cap for the U of exponent
        e = m - s - 1 (m >= 1) or every e of one degree d (m = 0); |r| >= 2^e (1 - UB) - 2 tail"""
        out = []
        m = 1
        while True:
            e = m - self.s - 1
            lo = max(Fr(0), Fr(2) ** e * (1 - UB) - 2 * tail)
            if lo > top:
                break
            cap = Fr(2) ** (e + 1)
            out.append((m, self.degree(-self.s - 1), lo, min(top, cap), cap))
            m += 1
        e = -self.s - 1
        while e >= -1 - self.B - 1:
            d = self.degree(e)
            e_lo = e
            while e_lo - 1 >= -1 - self.B and self.degree(e_lo - 1) == d:
                e_lo -= 1
            if d == 1:
                e_lo = None                                  # every smaller sum, zero and subnormal included
            lo = Fr(0) if e_lo is None else max(Fr(0), Fr(2) ** e_lo * (1 - UB) - 2 * tail)
            cap = Fr(2) ** (e + 1)
            if lo <= top:
                out.append((0, d, lo, min(top, cap), cap))
            if e_lo is None:
                break
            e = e_lo - 1
        return out

    def input_parts(self, X):
        """part bounds of an input with |x_0| <= X on H(theta), and a bound of |x - x_0|"""
        M, rho = self.M, Fr(self.theta) * self.u
        if M.ladder(X, self.theta) is None:
            return None, up(self.u * X)          # a double-word: |x_l| <= u |x_h|
        return [X] + [up(rho ** i * X) for i in range(1, M.n)], up(rho * X / (1 - rho))

    def exp_bin(self, k0, a, b, sigma, m, d, cap, red):
        """relative error bound of exp for computed |r| in [a, b], sign sigma, m squarings, degree d"""
        M = self.M
        if k0:
            rp = M.ladder(b, self.theta)
            dr = Fr(0)
        else:
            xp, xt = self.input_parts(XMAX)
            rr = self.reduce(xp, XMAX, xt, Zr=up(b + red['dr']))
            rp, dr = rr['parts'], red['dr']
        c = self.core(rp, b, m, d, sigma, a, cap)
        # s = ADDF(t, 1); |1 + t| <= e^r + E
        Zb = up((exp_up(b) if sigma > 0 else 1 / exp_lo(a)) + c['E'])
        es, _ = M.add_f(c['parts'], 1, Zb, None if c['parts'] is None else up(Zb + M.tail(c['parts'])))
        vmin = (exp_lo(a) if sigma > 0 else 1 / exp_up(b)) / exp_up(dr)
        return up((c['E'] + es) / vmin + expm1_up(dr)), dict(core=c, es=es, dr=dr)

    def bound(self, sub=8):
        """the largest relative error over k = 0 and k != 0, every case of step (2), both signs, and sub-intervals of
        |r| where e^r varies (|r| above 2^-12)"""
        M, u = self.M, self.u
        xp, xt = self.input_parts(XMAX)
        red = self.reduce(xp, XMAX, xt)
        worst, rows = (Fr(0), None), []
        for k0 in (True, False):
            if k0:
                # k = 0: |RN(x_0 L2E)| < 1/2, so |x_0| <= 1 / (2 L2E (1 - u)), |x| <= that (1 + 3 theta u)
                top = up(1 / (2 * L2E * (1 - u)) * (1 + 3 * Fr(self.theta) * u))
                lad = M.ladder(top, self.theta)
                tail = M.tail(lad) if lad is not None else Fr(0)
            else:
                top = up(red['re'] + red['dr'])
                tail = M.tail(red['parts']) if red['parts'] is not None else Fr(0)
            for (m, d, lo, hi, cap) in self.groups(tail, top):
                for sigma in (1, -1):
                    for a, b in edges(lo, hi, sub):
                        rel, info = self.exp_bin(k0, a, b, sigma, m, d, cap, red)
                        rows.append((k0, m, d, sigma, a, b, rel))
                        if rel > worst[0]:
                            worst = (rel, dict(k0=k0, m=m, d=d, sigma=sigma, a=a, b=b, **info))
        return worst[0], worst[1], rows, red


def addeta(parts, k):
    """part bounds after k scalings back that may each lose ETA0 per part (None for double-words)"""
    return None if parts is None else [x + k * ETA0 for x in parts]


def edges(lo, hi, sub):
    """a partition of [lo, hi]: geometric, sub pieces where hi > 2^-12, one piece below"""
    if hi <= Fr(1, 2 ** 12):
        return [(lo, hi)]
    lo_e = lo if lo > 0 else hi / 2 ** 16
    e = [lo_e] + [Fr(round(float(lo_e) * float(hi / lo_e) ** (i / sub) * 2 ** 60), 2 ** 60)
                  for i in range(1, sub)] + [hi]
    if lo == 0:
        e = [Fr(0)] + e
    return list(zip(e, e[1:]))


# ---------------------------------------------------------------------------------------------------------------
# log
# ---------------------------------------------------------------------------------------------------------------

class Log:
    """log by one Newton step on exp, y = y0 + log(1 + c), c = (f + t) + f t with (k, t) the reduction and core of
    exp(-y0) and f = x 2^k - 1, log(1 + c) = c (1 + c H(c)) to order q. start(l) bounds |y0 - ln x| for |ln x| <= l;
    nstart the parts of y0."""

    def __init__(self, exp, q, start, nstart, theta=2):
        self.E, self.q, self.start, self.nstart, self.theta = exp, q, start, nstart, theta
        self.M, self.u = exp.M, exp.u
        n = self.M.n
        # the series coefficients (-1)^(i+1) / i in n greedy parts (exact for i = 2, 4)
        self.A = {}
        for i in range(2, q + 1):
            a = Fr((-1) ** (i + 1), i)
            g = [Fr(x) for x in EC.greedy(a, n)]
            self.A[i] = (g, abs(sum(g) - a))

    def series(self, cp, Cb):
        """corr = c (1 + c h), h = A_2 + c (A_3 + c A_4 ...), each product with c formed at c 2^-ec (exact scalings,
        and a loss of at most ETA0 per part scaled back below 2^-1022): its error against S_q(c) = c (1 + c H(c)),
        |corr| bound and parts. Below 2^-(B + 13), corr = c, whose truncation is bounded in bin(); so it is for q = 1,
        where S_1(c) = c."""
        M, q, n = self.M, self.q, self.M.n
        if q == 1:
            return Fr(0), Cb, cp
        lossp = n * ETA0
        hp, he = M.const(self.A[q][0]), self.A[q][1]
        hv = Fr(1, q)
        for i in range(q - 1, 1, -1):
            ep, pp = M.mul(cp, hp, up(Cb * (hv + he)))
            ep, pp = up(ep + lossp), addeta(pp, 1)
            ai, aerr = self.A[i]
            ea, hp = M.add(M.const(ai), pp, up(Fr(1, i) + aerr + Cb * (hv + he) + ep))
            he = up(aerr + Cb * he + ep + ea)
            hv = up(Fr(1, i) + Cb * hv)
        ech, chp = M.mul(cp, hp, up(Cb * (hv + he)))           # c h
        ech, chp = up(ech + lossp), addeta(chp, 1)
        chv = up(Cb * (hv + he) + ech)
        eg, gp = M.add_f(chp, 1, up(1 + chv), None if chp is None else up(1 + chv + M.tail(chp)))
        gv = up(1 + chv + eg)
        ecorr, corrp = M.mul(cp, gp, up(Cb * gv))
        ecorr, corrp = up(ecorr + lossp), addeta(corrp, 1)
        # corr - S_q(c) = (corr - c g) + c (g - (1 + c h)) + c (c h - c H)
        serr = up(ecorr + Cb * (eg + ech + Cb * he))
        Sb = up(Cb * (1 + Cb * hv))
        return serr, up(Sb + serr), corrp

    def bin(self, l, k0, m, d, sigma, a, b, cap=None, start=None):
        """|y - ln x| bound for |ln x| <= l: k0 (k = 0, r = -y0, |r| in [a, b]) or k != 0 (|r| in [a, b], sign
        sigma); m squarings, degree d."""
        E, M, u, n = self.E, self.M, self.u, self.M.n
        E0 = self.start(l) if start is None else start
        Z = up(l + E0)                                     # |y0|
        zp = M.ladder(Z, 1, self.nstart)                  # y0's parts, H(1)
        if k0:
            rp, dr = zp, Fr(0)
        else:
            X = up(Z / (1 - u))                            # |y_h| <= |y0| / (1 - u)
            ztail = up(u * Z * 2)
            rr = E.reduce(zp, X, ztail, Zr=up(b + E.reduce(zp, X, ztail)['dr']))
            rp, dr = rr['parts'], rr['dr']
        c = E.core(rp, b, m, d, sigma, a, cap)
        # x' = x 2^k = e^(-e0 - r_e), r_e = -y0 - k ln 2 of sign sigma, |r_e| in [a - dr, b + dr]; scaling x by 2^k in
        # two steps loses at most 2 ETA0 per part to parts below 2^-1022
        if sigma > 0:
            xmax = up(exp_up(up(E0 + dr)) / exp_lo(a))
        else:
            xmax = up(exp_up(up(b + dr + E0)))
        xmax = xmax + 2 * n * ETA0                                     # exact: up() would round 1 + ETA0 to 1 + 2^-199
        zlo = up(b + dr + E0)
        F = up(max(xmax - 1, (zlo if M.convex else mexpm1_up(zlo)) + 2 * n * ETA0))    # |x' - 1|
        xp = addeta(M.ladder(xmax, self.theta), 2)
        # f = ADDF(x', -1), exact (Sterbenz); its parts
        if xp is not None:
            _, fp = M.add_f(xp, 1, F, up(F + M.tail(xp)))
        else:
            fp = None
        # c = ADD(ADD(f, t), f t), the value of x' (1 + t) - 1 = f + t + f t; f t from f 2^-ef and t 2^-et (exact
        # scalings, a loss of 2 n ETA0 in the two steps back), or dropped when |f| or |t| < 2^-(B+12), at most 2^-(B+12)
        # max(|f|, |t|)
        tb = up(c['T'] + c['E'])
        eft, ftp = M.mul(fp, c['parts'], up(F * tb))
        ftp = addeta(ftp, 2)
        eft = up(eft + 2 * n * ETA0 + Fr(1, 2 ** (E.B + 12)) * max(F, tb))
        # |f + t| <= |e^-r + e^r - 2| + |x' - e^-r| + E, x' = e^-r e^(-e0 + r - r_e)
        bb = up(b + dr)
        # 2 (cosh r - 1) <= 2 (e^b - 1 - b)
        sb = up(2 * (expm1_up(bb) - bb) + exp_up(bb) * expm1_up(up(E0 + dr)) + c['E'] + 2 * n * ETA0)
        es, sp = M.add(fp, c['parts'], sb)
        cstar = expm1_up(E0)                                           # |c*| = |e^(-e0) - 1|
        drift = up(exp_up(E0) * expm1_up(dr) + 2 * n * ETA0 * (1 + tb))    # |x' (e^r - e^r_e)|, and x' scaled lossily
        ec, cp = M.add(sp, ftp, up(cstar + xmax * c['E'] + drift + eft + es))
        eg = up(eft + es)
        Ec = up(xmax * c['E'] + drift + eg + ec)                       # |c - c*|
        Cb = up(cstar + Ec)
        # where p is dropped, c = ADD(f, t) itself, whose exact value f + t is c's less ft, within Cb: c's part
        # bounds cover the parts of that ADD too
        if cp is not None:
            cp = [max(x, y) for x, y in zip(cp, M.add(fp, c['parts'], Cb)[1])]
        serr, Sb, corrp = self.series(cp, Cb)
        # where step (5) returns c itself, the last ADD's operand has c's part bounds: cover both
        if corrp is not None:
            corrp = [max(x, y) for x, y in zip(cp, corrp)]
        # the series to order q, or c alone when |c| < 2^-(B + 12): c^2 / (2 (1 - |c|)) <= 2^-(B + 13) |c| / (1 - |c|)
        trunc = up(max(Cb ** (self.q + 1) / (self.q + 1), Fr(1, 2 ** (E.B + 13)) * Cb) / (1 - Cb))
        lip = up(Ec / (1 - Cb))                                        # |ln(1 + c) - ln(1 + c*)|
        pre = up(serr + trunc + lip)
        if self.nstart == 1:
            ey, _ = M.add_f(corrp, 0, up(l + pre))                     # DWPlusFP(corr, y0)
        else:
            ey, _ = M.add(zp, corrp, up(l + pre))
        return up(ey + pre), dict(c=c, Ec=Ec, Cb=Cb, serr=serr, trunc=trunc, lip=lip, ey=ey, E0=E0, dr=dr)


LTINY = Fr(1, 2 ** 60)    # a k = 0 case whose l start below this is bounded by its chord from l = 0


def k0_fn(Lg, e1, e0, m, d, sigma, a, hi, cap, llo):
    """the bound E(l) of a k = 0 case, with |r| = |y0| <= l + E0(l), or, for a case whose chord starts at l = 0 (llo =
    0) and whose hi >= sum |r_i| > |r| is at most E0(0) = e0, the constant hi: there e0 exceeds the case's |r| by far.
    Either b is convex in l, where their minimum would not be."""
    if llo == 0 and hi <= e0:
        return lambda l: Lg.bin(l, True, m, d, sigma, a, hi, cap)[0]
    return lambda l: Lg.bin(l, True, m, d, sigma, a, up(l + e1 * l + e0), cap)[0]


def chord(Ef, lo, hi):
    """for E convex on [lo, hi]: max of E(l)/l there is at an end; for lo = 0, E(l) <= E(0) + l slope. Each E passed
    here is a case's bound as Log.bin evaluates it in convex mode (VecSum's second bound alone, no minima, tbar_j = 2^j
    b' for r <= 0), which the paper's appendix, proof of the log theorem, "Convexity", shows nondecreasing and
    convex in l; its rounding up at the two ends keeps the chord above E. check() samples that property, and proves
    nothing."""
    if lo == 0:
        e0, e1 = Ef(Fr(0)), Ef(hi)
        return dict(floor=e0, rel=up((e1 - e0) / hi))
    return dict(floor=Fr(0), rel=up(max(Ef(lo) / lo, Ef(hi) / hi)))


def log_bound(Lg, e1, e0, pieces=(Fr(1), Fr(4)), sub=4, verbose=False, dd_split=None):
    """the relative bound of log: |y - ln x| <= rel |ln x| + floor, the start's error E0(l) = e1 l + e0. k = 0: each
    case of step (2) on r = -y0, both signs, a chord over the l that select it; k != 0: every (sign, case, |r| bin)
    at the ends of the l pieces. dd_split: below this l, x_h = 1 and E0(l) = l (u (1 + l) + l)."""
    E, M, u = Lg.E, Lg.M, Lg.u
    zk = up(1 / (2 * L2E * (1 - u)))
    out = []
    # k = 0: r = -y0, two parts on H(1): sum |r_i| <= |y0| (1 + u) / (1 - u), |y0| >= sum |r_i| (1 - u) / (1 + u)
    ytop = up(zk * (1 + 3 * u))                            # |y_h| < 1 / (2 L2E), so |y0| <= that (1 + u)
    for (m, d, lo, hi, cap) in E.groups(Fr(0), ytop):
        ylo = lo * (1 - u) / (1 + u)
        a = ylo
        llo = Fr(0) if lo == 0 else max(Fr(0), (ylo - e0) / (1 + e1))
        lhi = up((hi + e0) / (1 - e1))
        tiny = llo < LTINY
        for sigma in (1, -1):
            if dd_split is not None and tiny:
                ea = lambda l: up(l * (u * (1 + l) + l))
                Ef = lambda l: Lg.bin(l, True, m, d, sigma, a, up(l + ea(l)), cap, start=ea(l))[0]
                c1 = chord(Ef, Fr(0), min(dd_split, lhi))
                if lhi > dd_split:
                    c2 = chord(k0_fn(Lg, e1, e0, m, d, sigma, a, hi, cap, dd_split), dd_split, lhi)
                    rel = max(c1['rel'], c2['rel'])
                else:
                    rel = c1['rel']
                out.append(('k=0', m, d, sigma, Fr(0), lhi, rel, c1['floor']))
            else:
                lo_c = Fr(0) if tiny else llo
                c = chord(k0_fn(Lg, e1, e0, m, d, sigma, a, hi, cap, lo_c), lo_c, lhi)
                out.append(('k=0', m, d, sigma, lo_c, lhi, c['rel'], c['floor']))
            if verbose:
                print(out[-1][:4], float(out[-1][6] / u ** M.n), float(out[-1][7] / u ** M.n))
    # k != 0: |RN(z_0 L2E)| >= 1/2, so |z_0| >= 1 / (2 L2E (1 + u)) and |y0| >= |z_0| (1 - u)
    lk = ((1 - u) / (2 * L2E * (1 + u)) - e0) / (1 + e1)
    Z = up(XMAX + e1 * XMAX + e0)
    zp = M.ladder(Z, 1, Lg.nstart)
    red = E.reduce(zp, up(Z / (1 - u)), up(2 * u * Z))
    top = up(red['re'] + red['dr'])
    tail = M.tail(red['parts']) if red['parts'] is not None else Fr(0)
    # E(l)/l at the ends of [lk, 1], [1, 4] and [4, XMAX] bounds it inside each: for a fixed case (sign, m, d, |r| in
    # [ra, rb]), E is nondecreasing and convex in l, since l enters only through y-bar = l + E0(l), linear, and the
    # reduction's X, x-bar_t and alpha, linear in y-bar (the appendix, proof of the log theorem, "Convexity"; chord())
    ends = [lk] + list(pieces) + [XMAX]
    worst = (Fr(0), None)
    for (m, d, rlo, rhi, cap) in E.groups(tail, top):
        for sigma in (1, -1):
            for ra, rb in edges(rlo, rhi, sub):
                rel = max(Lg.bin(l, False, m, d, sigma, ra, rb, cap)[0] / l for l in ends)
                if rel > worst[0]:
                    worst = (rel, (m, d, sigma, ra, rb))
    out.append(('k!=0', worst[1], None, None, lk, XMAX, up(worst[0]), Fr(0)))
    if verbose:
        print(out[-1][:2], float(worst[0] / u ** M.n))
    return out


def up_dec(x, k=6):
    """a rational x >= 0 rounded up to k decimals, as printed: every printed bound is an upper bound"""
    q = -(-x.numerator * 10 ** k // x.denominator)
    return f'{q // 10 ** k}.{q % 10 ** k:0{k}d}' if k else str(q)


def lg2_up(x, k=2):
    """the least c, a multiple of 10^-k, with x <= 2^c for a rational x > 0, printed with k decimals; exact, from
    x^(10^k) against 2^(c 10^k), as a float's log2 loses bits below 2^-1022"""
    s = 10 ** k
    b = x.numerator.bit_length() - x.denominator.bit_length()
    a = math.ceil((b + math.log2(float(x / Fr(2) ** b))) * s)
    le = lambda a: x ** s <= Fr(2) ** a
    while not le(a):
        a += 1
    while le(a - 1):
        a -= 1
    return f'{a / s:.{k}f}' if k else str(a)


def fmt(x, u, n):
    return up_dec(x / u ** n)


def ceil3(x):
    """x rounded up to three decimals, as quoted"""
    return up_dec(x, 3)


# the crate's parameters: (s, d, q) per precision
DD_PARAMS = (1, 27, 3)
QD_PARAMS = (6, 24, 2)
OD_PARAMS = (6, 43, 4)


def dd_exp(s=DD_PARAMS[0], d=DD_PARAMS[1]):
    E = Exp(DoubleWord(), s, d)
    w, info, rows, red = E.bound(sub=8)
    return w, info, red


def dd_start(eta):
    """the start's error E0(l) = e1 l + e0 of the double-double logarithm: y0 = RN(h + RN(x_l / x_h)), h =
    ln_f64(x_h) within eta |ln x_h|; with v = x_l / x_h, |v| <= u, |ln(1 + v)| <= delta = u / (1 - u), the quotient's
    rounding at most u |v| + ETA0, and |y0 - ln x| <= eta |ln x_h| + u |v| + ETA0 + v^2 / (2 (1 - u)) + u |h + RN(v)|,
    |ln x_h| <= l + delta"""
    u = Fr(1, 2 ** 53)
    delta = up(u / (1 - u))
    e1 = up(eta + u * (1 + eta))
    e0 = up(eta * delta + u * u + ETA0 + u * u / (2 * (1 - u)) + u * ((1 + eta) * delta + u * (1 + u) + ETA0))
    return e1, e0


def dd_log(s=DD_PARAMS[0], d=DD_PARAMS[1], q=DD_PARAMS[2], verbose=False):
    """the double-double log from its own start (start_eta, dd_start)"""
    M = DoubleWord(convex=True)
    u = M.u
    E = Exp(M, s, d)
    eta, _ = start_eta()
    e1, e0 = dd_start(eta)
    Lg = Log(E, q, lambda l: up(e1 * l + e0), 1)
    rows = log_bound(Lg, e1, e0, verbose=verbose, dd_split=up(u / 2 * (1 - u)))
    rel = max(r[6] for r in rows)
    floor = max(r[7] for r in rows)
    return rel, floor, rows


def od_exp(n, s, d, theta=2):
    E = Exp(Expansion(n, 53), s, d, theta)
    w, info, rows, red = E.bound(sub=8)
    return w, info, red


def od_start(n, eps_dd, fl_dd, theta=2):
    """E0(l) = e1 l + e0 for the expansion log's start: the double-double log of to_dd(x), within eps_dd |ln to_dd(x)|
    + fl_dd of ln(to_dd(x)); to_dd's sum of the n - 1 lower parts errs by g sum |x_i|, g = (n-2)u/(1-(n-2)u), so |ln x - ln
    to_dd(x)| <= delta. For x_0 >= 2^1023 the start is that of x/2 (the halving moves each part by at most ETA0,
    relative to x below 2^-2090) plus LN2_DD, within eta_l of ln 2, by AccurateDWPlusDW, within e_A (l + 1) of
    the sum: E0 covers both."""
    u = Fr(1, 2 ** 53)
    rho = Fr(theta) * u
    g = (n - 2) * u / (1 - (n - 2) * u)
    w = up(g * rho / (1 - 2 * rho - g * rho))
    delta = up(w / (1 - w))
    alpha_a = 3 * u * u / (1 - 4 * u)
    dd = [Fr(x) for x in CONST['dd']]
    eta_l = max(abs(LN2_A - sum(dd)), abs(LN2_B - sum(dd)))
    return up(eps_dd + alpha_a), up(delta * (1 + eps_dd) + fl_dd + alpha_a + eta_l + Fr(1, 2 ** 2000)), delta


def dd_quoted():
    """the double-word logarithm's bounds as Proposition 44 quotes them, eps_DW = 15.351 u^2 and Phi_DW = 2^-1071:
    the E(l) of the expansion's logarithm is defined with these, not with dd_log's unrounded values"""
    u = Fr(1, 2 ** 53)
    rdd, fdd, _ = dd_log()
    return Fr(ceil3(rdd / u ** 2)) * u ** 2, Fr(2) ** int(lg2_up(fdd, 0))


def od_log(n, s, d, q, eps_dd, fl_dd, theta=2, verbose=False):
    M = Expansion(n, 53, convex=True)
    E = Exp(M, s, d, theta)
    e1, e0, delta = od_start(n, eps_dd, fl_dd, theta)
    Lg = Log(E, q, lambda l: up(e1 * l + e0), 2, theta)
    rows = log_bound(Lg, e1, e0, verbose=verbose)
    rel = max(r[6] for r in rows)
    floor = max(r[7] for r in rows)
    return rel, floor, rows, (e1, e0, delta)


def degree(n, s, p=53):
    """the least d with 2^(-s d) / (d + 1)! <= 2^-12 u^n"""
    d = 1
    while s * d + math.log2(math.factorial(d + 1)) < p * n + 12:
        d += 1
    return d


def order(n, eps_dd, p=53):
    """the least q with (eps_dd 745.2 + 2^-100)^(q + 1) / ((q + 1) 0.34) <= 2^-12 u^n"""
    c = float(eps_dd) * 745.2 + 2 ** -100
    q = 1
    while (q + 1) * -math.log2(c) + math.log2((q + 1) * 0.34) < p * n + 12:
        q += 1
    return q


def convexity_check(f, pts, tol=Fr(1, 2 ** 180)):
    """f nondecreasing and convex at the sample points (each interior point at most the chord of its neighbours), up to
    tol relative, far above the evaluation's 200-bit rounding and far below any bound's digits"""
    v = [f(x) for x in pts]
    mono = all(a <= b * (1 + tol) for a, b in zip(v, v[1:]))
    conv = all(v[i] * (pts[i + 1] - pts[i - 1]) <= (v[i - 1] * (pts[i + 1] - pts[i]) + v[i + 1] * (pts[i] - pts[i - 1]))
               * (1 + tol) for i in range(1, len(pts) - 1))
    return mono and conv


def check():
    """the log's chords take each case's bound E(l) as nondecreasing and convex in l (an argument in the appendix):
    sample od_log's own setting, every k = 0 case at nine points and four k != 0 cases at 22, and fire on a concave
    function (the control)"""
    u = Fr(1, 2 ** 53)
    rdd, fdd = dd_quoted()
    n, (s, d, q) = 8, OD_PARAMS
    M = Expansion(n, 53, convex=True)
    E = Exp(M, s, d)
    e1, e0, _ = od_start(n, rdd, fdd)
    Lg = Log(E, q, lambda l: up(e1 * l + e0), 2)
    ok, count = True, 0
    zk = up(1 / (2 * L2E * (1 - u)))
    for (m, dd, lo, hi, cap) in E.groups(Fr(0), up(zk * (1 + 3 * u))):
        ylo = lo * (1 - u) / (1 + u)
        llo = Fr(0) if lo == 0 else max(Fr(0), (ylo - e0) / (1 + e1))
        llo = Fr(0) if llo < LTINY else llo
        lhi = up((hi + e0) / (1 - e1))
        pts = [llo + (lhi - llo) * Fr(i, 8) for i in range(9)]
        for sig in (1, -1):
            r = convexity_check(k0_fn(Lg, e1, e0, m, dd, sig, ylo, hi, cap, llo), pts)
            ok &= r
            count += 1
    lk = ((1 - u) / (2 * L2E * (1 + u)) - e0) / (1 + e1)
    pts = [lk + (XMAX - lk) * Fr(i, 21) ** 3 for i in range(22)]
    for (m, dd, sig, ra, rb) in ((5, 43, -1, Fr(3194, 10000), Fr(3466, 10000)), (5, 43, 1, Fr(3194, 10000),
                                 Fr(3466, 10000)), (0, 43, -1, Fr(0), Fr(1, 128)), (3, 43, 1, Fr(1, 32), Fr(1, 16))):
        f = lambda l: Lg.bin(l, False, m, dd, sig, ra, rb, None)[0]
        r = convexity_check(f, pts)
        ok &= r
        count += 1
    # the controls: a concave function fails convexity alone, a decreasing affine one monotonicity alone
    concave = convexity_check(lambda l: l * (2 - l), [Fr(0), Fr(1, 2), Fr(1)])
    decreasing = convexity_check(lambda l: 2 - l, [Fr(0), Fr(1, 2), Fr(1)])
    print(f'{count} cases sampled: nondecreasing and convex: {ok}; controls, l (2 - l): {concave}, 2 - l: '
          f'{decreasing}')
    print('PASS' if ok and not concave and not decreasing else 'FAIL')
    return ok and not concave and not decreasing


if __name__ == '__main__':
    u = Fr(1, 2 ** 53)
    if len(sys.argv) > 1 and sys.argv[1] == 'check':
        sys.exit(0 if check() else 1)
    print('the crate (u = 2^-53; exp relative; log relative to |ln x|, plus an absolute term)')
    eta, se = start_eta()
    print(f'the start ln_f64 (Lemma 43): within {up_dec(eta / u)} u relative (2^{lg2_up(eta)}); for e = 0, '
          f'{up_dec(se["ew"] / u)} u')
    w, info, red = dd_exp()
    rdd, fdd, _ = dd_log()
    print(f'DD s,d,q = {DD_PARAMS}: exp <= {fmt(w, u, 2)} u^2 e^x + 2 2^-1074 (quoted {ceil3(w / u ** 2)}), '
          f'worst at {"k = 0" if info["k0"] else "k != 0"}, d {info["d"]}, sign {info["sigma"]}, '
          f'|r| in [{float(info["a"]):.4f}, '
          f'{float(info["b"]):.4f}]; log <= {fmt(rdd, u, 2)} u^2 |ln x| + 2^{lg2_up(fdd)} (quoted '
          f'{ceil3(rdd / u ** 2)} u^2 and 2^{lg2_up(fdd, 0)})')
    wdd = w
    s, d, q = OD_PARAMS
    w, info, red = od_exp(8, s, d)
    print(f'OD s,d,q = {OD_PARAMS}: exp <= {fmt(w, u, 8)} u^8 e^x + 8 2^-1074 (quoted {ceil3(w / u ** 8)}), '
          f'worst at {"k = 0" if info["k0"] else "k != 0"}, m {info["m"]}, d {info["d"]}, sign {info["sigma"]}, '
          f'|r| in '
          f'[{float(info["a"]):.4f}, {float(info["b"]):.4f}]; reduction {fmt(red["dr"], u, 8)} u^8')
    qdd, qfl = dd_quoted()
    rel, floor, rows, (e1, e0, delta) = od_log(8, s, d, q, qdd, qfl)
    print(f'OD log <= {fmt(rel, u, 8)} u^8 |ln x| + 2^{lg2_up(floor)} (quoted {ceil3(rel / u ** 8)} u^8 and '
          f'2^{lg2_up(floor, 0)}); start within {fmt(e1, u, 2)} u^2 |ln x| + 2^{lg2_up(e0)} of ln x on either branch '
          f'(the DD log of to_dd(x), |ln x - ln to_dd(x)| <= 2^{lg2_up(delta)}, or for x_0 >= 2^1023 that of x/2 '
          f'plus LN2_DD)')
    # where each quoted bound's absolute term exceeds its relative one: e^x below n 2^-1074 / (C u^n), |ln x| below
    # 2^a / (C u^n), as quoted (C and 2^a rounded up); the printed limits are rounded up too
    A_od, A_dd = Fr(2) ** int(lg2_up(floor, 0)), Fr(2) ** int(lg2_up(fdd, 0))
    C = {k: Fr(ceil3(v)) for k, v in dict(de=wdd / u ** 2, dl=rdd / u ** 2, oe=w / u ** 8, ol=rel / u ** 8).items()}
    lim = [lg2_up(16 * ETA0 / (C['oe'] * u ** 8), 0), lg2_up(4 * ETA0 / (C['de'] * u ** 2), 0),
           lg2_up(A_od / (C['ol'] * u ** 8), 0), lg2_up(A_dd / (C['dl'] * u ** 2), 0)]
    print(f'the absolute terms, as quoted, exceed the relative ones only where e^x < 2^{lim[0]} (OD) or '
          f'2^{lim[1]} (DD), and |ln x| < 2^{lim[2]} (OD) or 2^{lim[3]} (DD)')
    for r in rows[:-1]:
        print(f'   k=0 m={r[1]} d={r[2]:<2d} sign={r[3]:+d} {fmt(r[6], u, 8)} u^8' +
              (f' + 2^{lg2_up(r[7])}' if r[7] else ''))
    w = rows[-1][1]
    print(f'   k!=0 {fmt(rows[-1][6], u, 8)} u^8, at m {w[0]}, d {w[1]}, sign {w[2]:+d}, |r| in [{float(w[3]):.4f}, '
          f'{float(w[4]):.4f}]')
    print('the theorems at other n (theta = 2, s = 6, d and q the least that serve)')
    for n in (4, 12):
        s = 6
        d, q = degree(n, s), order(n, qdd)
        w, _, _ = od_exp(n, s, d)
        rel, floor, _, _ = od_log(n, s, d, q, qdd, qfl)
        print(f'n={n:2d} d={d} q={q}: exp <= {fmt(w, u, n)} u^n e^x + {n} 2^-1074, log <= {fmt(rel, u, n)} u^n '
              f'|ln x| + 2^{lg2_up(floor)}')
