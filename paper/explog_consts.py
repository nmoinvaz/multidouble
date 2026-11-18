"""The error bounds of exp and ln (src/explog.rs) in exact rationals. For the octo-double algorithms at any number of
parts n, Lemma 20 of expansion-error-bounds.pdf bounds every operation's error and its result's parts from its
operands' part bounds, and the bounds are carried through every step; for the double-double ones, the published
relative bounds of the double-word operations. Every bound is computed in rationals rounded up to 200-bit dyadic
numbers (sqrt_consts.up); every formula is nondecreasing in the quantities so rounded.

usage: explog_consts.py           the bounds of the crate's DD and OD exp and ln, and of the n-part algorithms at
                                  n = 4 and 12 (about 5 minutes)
       explog_consts.py check     the log's bounds sampled for monotonicity and convexity in |ln x|, the property its
                                  chords use; a concave function is the control, and must be caught"""
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
    """an upper bound of 1 - e^-z for rational z >= 0: e^-z >= 1 - z + z^2/2 - z^3/6"""
    return up(z - z * z / 2 + z ** 3 / 6)


def vecb(X, u, n, convex):
    """VecSum output bounds from level bounds (Theorem 9(d)); convex: the second of its two bounds alone"""
    us = u / (1 + u)
    sig = [sum(X[l:]) for l in range(n + 1)]
    V = [(1 + u) ** n * sig[0]]
    for j in range(1, n + 1):
        b2 = us * (1 + u) ** (n - j) * sig[j - 1]
        V.append(b2 if convex else min(X[j - 1], b2))
    return V


def lemma20(name, n, u, al, be, Zb, lam=None, convex=False):
    """Lemma 20: the error bound and the result's part bounds of MUL, ADD, MULF and ADDF from the operands' part
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
    """the n-part algorithms of the paper (OD at n = 8): Lemma 20 at every operation"""

    def __init__(self, n, p, convex=False):
        self.n, self.u, self.convex = n, Fr(1, 2 ** p), convex
        self.name = f'n={n}'

    def const(self, parts):
        v = [abs(Fr(x)) for x in parts[:self.n]]
        return v + [Fr(0)] * (self.n - len(v))

    def mul(self, a, b, Zb):
        return lemma20('mul', self.n, self.u, a, b, Zb, convex=self.convex)

    def add(self, a, b, Zb, lam=None):
        return lemma20('add', self.n, self.u, a, b, Zb, lam=lam, convex=self.convex)

    def add_f(self, a, f, Zb, lam0=None):
        return lemma20('add_f', self.n, self.u, a, [abs(Fr(f))], Zb, lam=None if lam0 is None else [lam0],
                       convex=self.convex)

    def mul_f(self, a, f, Zb):
        return lemma20('mul_f', self.n, self.u, a, [abs(Fr(f))], Zb, convex=self.convex)

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
        self.a_addf = 2 * u * u / (1 - 2 * u)       # DWPlusFP, Joldes-Muller-Popescu Algorithm 4, p >= 4
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
# exp
# ---------------------------------------------------------------------------------------------------------------

class Exp:
    """exp at the model's precision: squaring threshold tau = 2^-s, Taylor degree d, input ladder H(theta)"""

    def __init__(self, M, s, d, theta=2):
        self.M, self.s, self.d, self.theta = M, s, d, theta
        n, u = M.n, M.u
        self.u = u
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

    def core(self, rp, b, m, sigma, a=Fr(0)):
        """t ~ e^r - 1 for r with part bounds rp, a <= |r| <= b, sign sigma, m squarings: |t - (e^r - 1)| <= E"""
        M, d = self.M, self.d
        convex = M.convex
        sc = Fr(1, 2 ** m)
        tail = M.tail(rp) if rp is not None else Fr(0)
        # |r'| <= 2^-s + tail 2^-m by the choice of m (dropped in convex mode, where |r'| <= b 2^-m serves)
        bp = up((b if convex else min(b, Fr(2) ** m * self.tau + tail)) * sc)
        if rp is not None:
            rp = [up((rp[0] if convex else min(rp[0], Fr(2) ** m * self.tau)) * sc)] + [up(x * sc) for x in rp[1:]]
        # Horner: q_d = 1/d!, q_j = 1/j! + r' q_(j+1) down to j = 2, q_2 ~ sum_(i=2)^d r'^(i-2) / i!
        qv, qe, qp = Fr(1, math.factorial(d)), self.Ferr[d], M.const(self.F[d])
        for j in range(d - 1, 1, -1):
            ep, pp = M.mul(rp, qp, up(bp * (qv + qe)))
            cj = Fr(1, math.factorial(j))
            ea, qp = M.add(M.const(self.F[j]), pp, up(cj + self.Ferr[j] + bp * (qv + qe) + ep))
            qe = up(self.Ferr[j] + bp * qe + ep + ea)
            qv = up(cj + bp * qv)
        # t_0 = r' + r' (r' q_2)
        e1, w1p = M.mul(rp, qp, up(bp * (qv + qe)))
        e2, wp = M.mul(rp, w1p, up(bp * (bp * (qv + qe) + e1)))
        trunc = up(bp ** (d + 1) / math.factorial(d + 1) / (1 - bp / (d + 2)))
        E = up(e2 + bp * (e1 + bp * qe) + trunc)
        e3, tp = M.add(rp, wp, up(self.tj(0, bp, sigma, convex) + E))
        E = up(E + e3)
        steps = [dict(E=E, taylor=E - e3, add=e3)]
        # m squarings t <- 2 t + t^2
        for j in range(m):
            Tj = self.tj(j, bp, sigma, convex)
            # |2 + 2 T_j| <= 2 (1 + Tj) for r > 0, and 2 (1 - |T_j|) <= 2 e^(-2^j |r'|) for r < 0
            g = 1 + Tj if sigma > 0 else (Fr(1) if a == 0 else 1 / exp_lo(up(a * sc * 2 ** j)))
            em, mp = M.mul(tp, tp, up((Tj + E) ** 2))
            Z = up(self.tj(j + 1, bp, sigma, convex) + 2 * E + 2 * Tj * E + E * E + em)
            ea, tp = M.add(None if tp is None else M.scale(tp, 2), mp, Z)
            E = up(2 * E * g + E * E + em + ea)
            steps.append(dict(E=E, mul=em, add=ea))
        return dict(E=E, parts=tp, T=self.tj(m, bp, sigma, convex), bp=bp, steps=steps)

    def m_bins(self, tail, top):
        """(m, lo, hi): the squaring counts and the |r| that can select each, |r| <= top, |r - r_0| <= tail"""
        out, m = [], 0
        while True:
            lo = Fr(0) if m == 0 else max(Fr(0), Fr(2) ** (m - self.s - 1) - tail)
            if lo > top:
                return out
            out.append((m, lo, min(top, Fr(2) ** (m - self.s) + tail)))
            m += 1

    def input_parts(self, X):
        """part bounds of an input with |x_0| <= X on H(theta), and a bound of |x - x_0|"""
        M, rho = self.M, Fr(self.theta) * self.u
        if M.ladder(X, self.theta) is None:
            return None, up(self.u * X)          # a double-word: |x_l| <= u |x_h|
        return [X] + [up(rho ** i * X) for i in range(1, M.n)], up(rho * X / (1 - rho))

    def exp_bin(self, k0, a, b, sigma, m, red):
        """relative error bound of exp for computed |r| in [a, b], sign sigma, m squarings (k = 0 or not)"""
        M = self.M
        if k0:
            rp = M.ladder(b, self.theta)
            dr = Fr(0)
        else:
            xp, xt = self.input_parts(XMAX)
            rr = self.reduce(xp, XMAX, xt, Zr=up(b + red['dr']))
            rp, dr = rr['parts'], red['dr']
        c = self.core(rp, b, m, sigma, a)
        # s = ADDF(t, 1); |1 + t| <= e^r + E
        Zb = up((exp_up(b) if sigma > 0 else 1 / exp_lo(a)) + c['E'])
        es, _ = M.add_f(c['parts'], 1, Zb, None if c['parts'] is None else up(Zb + M.tail(c['parts'])))
        vmin = (exp_lo(a) if sigma > 0 else 1 / exp_up(b)) / exp_up(dr)
        return up((c['E'] + es) / vmin + expm1_up(dr)), dict(core=c, es=es, dr=dr)

    def bound(self, sub=8):
        """the largest relative error over k = 0 and k != 0, every m, both signs, sub sub-bins per m"""
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
            for (m, lo, hi) in self.m_bins(tail, top):
                lo_e = lo if lo > 0 else hi / 2 ** 16
                edges = [lo_e] + [Fr(round(float(lo_e) * float(hi / lo_e) ** (i / sub) * 2 ** 60), 2 ** 60)
                                  for i in range(1, sub)] + [hi]
                if lo == 0:
                    edges = [Fr(0)] + edges
                for sigma in (1, -1):
                    for a, b in zip(edges, edges[1:]):
                        rel, info = self.exp_bin(k0, a, b, sigma, m, red)
                        rows.append((k0, m, sigma, a, b, rel))
                        if rel > worst[0]:
                            worst = (rel, dict(k0=k0, m=m, sigma=sigma, a=a, b=b, **info))
        return worst[0], worst[1], rows, red


# ---------------------------------------------------------------------------------------------------------------
# log
# ---------------------------------------------------------------------------------------------------------------

class Log:
    """log by one Newton step on exp, y = y0 + S_q(c), c = x 2^k (1 + t) - 1 with (k, t) the reduction and core of
    exp(-y0), S_q the log1p series to order q. start(l) bounds |y0 - ln x| for |ln x| <= l; nstart the parts of y0."""

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
        """corr = c + c^2 h, h = A_2 + c (A_3 + c A_4 ...): error against S_q(c), |corr| bound, parts"""
        M, q = self.M, self.q
        hp, he = M.const(self.A[q][0]), self.A[q][1]
        hv = Fr(1, q)
        for i in range(q - 1, 1, -1):
            ep, pp = M.mul(cp, hp, up(Cb * (hv + he)))
            ai, aerr = self.A[i]
            ea, hp = M.add(M.const(ai), pp, up(Fr(1, i) + aerr + Cb * (hv + he) + ep))
            he = up(aerr + Cb * he + ep + ea)
            hv = up(Fr(1, i) + Cb * hv)
        e0, c2p = M.mul(cp, cp, up(Cb * Cb))
        ew, wp = M.mul(c2p, hp, up((Cb * Cb + e0) * (hv + he)))
        werr = up(ew + e0 * (hv + he) + Cb * Cb * he)            # |w - c^2 H(c)|
        Sb = up(Cb + Cb * Cb * hv)                                  # |S_q(c)|
        ec, corrp = M.add(cp, wp, up(Sb + werr))
        return up(ec + werr), up(Sb + werr + ec), corrp

    def bin(self, l, k0, m, sigma, a, b, start=None):
        """|y - ln x| bound for |ln x| <= l: k0 (k = 0, r = -y0, |r| in [a, b]) or k != 0 (|r| in [a, b], sign
        sigma); m squarings. Also returns the bound of |c|."""
        E, M, u, n = self.E, self.M, self.u, self.M.n
        E0 = self.start(l) if start is None else start
        Z = up(l + E0)                                     # |y0|
        zp = M.ladder(Z, 1, self.nstart)                  # y0's parts, H(1)
        if k0:
            rp, dr, b = zp, Fr(0), min(b, Z)
            re_lo, re_hi = (a, b)
        else:
            ztail = up(u * Z * 2)
            rr = E.reduce(zp, Z, ztail, Zr=up(b + E.reduce(zp, Z, ztail)['dr']))
            rp, dr = rr['parts'], rr['dr']
        c = E.core(rp, b, m, sigma, a)
        # x' = x 2^k = e^(-e0 - r_e), r_e = -y0 - k ln 2 of sign sigma, |r_e| in [a - dr, b + dr]
        if sigma > 0:
            xmax = up(exp_up(up(E0 + dr)) / exp_lo(a) if a > dr else exp_up(up(E0 + dr)))
        else:
            xmax = up(exp_up(up(b + dr + E0)))
        zlo = up(b + dr + E0)
        F = up(max(xmax - 1, zlo if M.convex else mexpm1_up(zlo)))    # |x' - 1|
        xp = M.ladder(xmax, self.theta)
        # f = ADDF(x', -1), exact (Sterbenz); its parts
        if xp is not None:
            _, fp = M.add_f(xp, 1, F, up(F + M.tail(xp)))
        else:
            fp = None
        # c = ADD(ADD(f, t), MUL(f, t)), the value of x' (1 + t) - 1 = f + t + f t
        tb = up(c['T'] + c['E'])
        eft, ftp = M.mul(fp, c['parts'], up(F * tb))
        # |f + t| <= |e^-r + e^r - 2| + |x' - e^-r| + E, x' = e^-r e^(-e0 + r - r_e)
        bb = up(b + dr)
        # 2 (cosh r - 1) <= 2 (e^b - 1 - b)
        sb = up(2 * (expm1_up(bb) - bb) + exp_up(bb) * expm1_up(up(E0 + dr)) + c['E'])
        es, sp = M.add(fp, c['parts'], sb)
        cstar = expm1_up(E0)                                           # |c*| = |e^(-e0) - 1|
        drift = up(exp_up(E0) * expm1_up(dr))                         # |x' (e^r - e^r_e)|
        ec, cp = M.add(sp, ftp, up(cstar + xmax * c['E'] + drift + eft + es))
        eg = up(eft + es)
        Ec = up(xmax * c['E'] + drift + eg + ec)                       # |c - c*|
        Cb = up(cstar + Ec)
        serr, Sb, corrp = self.series(cp, Cb)
        trunc = up(Cb ** (self.q + 1) / (self.q + 1) / (1 - Cb))
        lip = up(Ec / (1 - Cb))                                        # |ln(1 + c) - ln(1 + c*)|
        pre = up(serr + trunc + lip)
        if self.nstart == 1:
            ey, _ = M.add_f(corrp, 0, up(l + pre))                     # DWPlusFP(corr, y0)
        else:
            ey, _ = M.add(zp, corrp, up(l + pre))
        return up(ey + pre), dict(c=c, Ec=Ec, Cb=Cb, serr=serr, trunc=trunc, lip=lip, ey=ey, E0=E0, dr=dr)


def chord(Ef, lo, hi):
    """for E convex on [lo, hi]: max of E(l)/l there is at an end; for lo = 0, E(l) <= E(0) + l slope"""
    if lo == 0:
        e0, e1 = Ef(Fr(0)), Ef(hi)
        return dict(floor=e0, rel=up((e1 - e0) / hi))
    return dict(floor=Fr(0), rel=up(max(Ef(lo) / lo, Ef(hi) / hi)))


def log_bound(Lg, e1, e0, pieces=(Fr(1), Fr(4)), sub=4, verbose=False, dd_split=None):
    """the relative bound of log: |y - ln x| <= rel |ln x| + floor, the start's error E0(l) = e1 l + e0. k = 0: each
    m, both signs, a chord over the l that select m; k != 0: every (sign, m, |r| bin) at the ends of the l pieces.
    dd_split: below this l the start is exact (x_h = 1, y0 = 0) and E0(l) = l."""
    E, M, u = Lg.E, Lg.M, Lg.u
    zk = up(1 / (2 * L2E * (1 - u)))
    out = []
    # k = 0: r = -y0
    m = 0
    while True:
        a = Fr(0) if m == 0 else Fr(2) ** (m - E.s - 1) * (1 - 2 * u)
        cap = min(Fr(2) ** (m - E.s) * (1 + 2 * u), zk * (1 + 2 * u))
        lo = Fr(0) if m == 0 else max(Fr(0), (a - e0) / (1 + e1))
        hi = up((cap + e0) / (1 - e1))
        if lo > hi or (m > 0 and a > zk * (1 + 2 * u)):
            break
        for sigma in (1, -1):
            if dd_split is not None and m == 0:
                # x_h = 1: y0 = RN(x_l), |y0 - ln x| <= u |x_l| + x_l^2 / (2 (1 - |x_l|)) <= l (u (1 + l) + l)
                ea = lambda l: up(l * (u * (1 + l) + l))
                Ef = lambda l: Lg.bin(l, True, m, sigma, a, up(l + ea(l)), start=ea(l))[0]
                c1 = chord(Ef, Fr(0), dd_split)
                Ef2 = lambda l: Lg.bin(l, True, m, sigma, a, up(l + e1 * l + e0))[0]
                c2 = chord(Ef2, dd_split, hi)
                out.append(('k=0', m, sigma, Fr(0), hi, max(c1['rel'], c2['rel']), c1['floor']))
            else:
                Ef = lambda l: Lg.bin(l, True, m, sigma, a, up(l + e1 * l + e0))[0]
                c = chord(Ef, lo, hi)
                out.append(('k=0', m, sigma, lo, hi, c['rel'], c['floor']))
            if verbose:
                print(out[-1][:3], float(out[-1][5] / u ** M.n), float(out[-1][6] / u ** M.n))
        m += 1
    # k != 0: l >= lk
    # k != 0: |RN(z_0 L2E)| >= 1/2, so |z_0| >= 1 / (2 L2E (1 + u)) and |y0| >= |z_0| (1 - u)
    lk = ((1 - u) / (2 * L2E * (1 + u)) - e0) / (1 + e1)
    Z = up(XMAX + e1 * XMAX + e0)
    zp = M.ladder(Z, 1, Lg.nstart)
    red = E.reduce(zp, Z, up(2 * u * Z))
    top = up(red['re'] + red['dr'])
    tail = M.tail(red['parts']) if red['parts'] is not None else Fr(0)
    ends = [lk] + list(pieces) + [XMAX]
    worst = (Fr(0), None)
    for (m, rlo, rhi) in E.m_bins(tail, top):
        rlo_e = rlo if rlo > 0 else rhi / 2 ** 16
        edges = [rlo_e] + [Fr(round(float(rlo_e) * float(rhi / rlo_e) ** (i / sub) * 2 ** 60), 2 ** 60)
                           for i in range(1, sub)] + [rhi]
        if rlo == 0:
            edges = [Fr(0)] + edges
        for sigma in (1, -1):
            for ra, rb in zip(edges, edges[1:]):
                rel = max(Lg.bin(l, False, m, sigma, ra, rb)[0] / l for l in ends)
                if rel > worst[0]:
                    worst = (rel, (m, sigma, ra, rb))
    out.append(('k!=0', worst[1], None, lk, XMAX, up(worst[0]), Fr(0)))
    if verbose:
        print(out[-1][:2], float(worst[0] / u ** M.n))
    return out


def fmt(x, u, n):
    return f'{float(x / u ** n):.6f}'


def ceil3(x):
    """x rounded up to three decimals, as quoted"""
    return math.ceil(float(x) * 1000 - 1e-9) / 1000


ETA_LIBM = Fr(1, 2 ** 40)  # the hypothesis on f64::ln: |ln_f64(h) - ln h| <= ETA_LIBM |ln h|

# the crate's parameters: (s, d, q) per precision
DD_PARAMS = (1, 27, 3)
QD_PARAMS = (6, 24, 2)
OD_PARAMS = (6, 43, 4)


def dd_exp(s=DD_PARAMS[0], d=DD_PARAMS[1]):
    E = Exp(DoubleWord(), s, d)
    w, info, rows, red = E.bound(sub=8)
    return w, info, red


def dd_log(s=DD_PARAMS[0], d=DD_PARAMS[1], q=DD_PARAMS[2], verbose=False):
    """the double-double log: start y0 = RN(h + RN(x_l / x_h)), h = f64::ln(x_h). With v = x_l / x_h, |v| <= u and
    |ln(1 + v)| <= delta = u / (1 - u); for x_h != 1, |ln x| >= u/2 (1 - u), and
    |y0 - ln x| <= eta |ln x_h| + u |v| + v^2 / (2 (1 - u)) + u |h + RN(v)|, |ln x_h| <= l + delta"""
    M = DoubleWord(convex=True)
    u = M.u
    E = Exp(M, s, d)
    eta = ETA_LIBM
    delta = up(u / (1 - u))
    e1 = up(eta + u * (1 + eta))
    e0 = up(eta * delta + u * u + u * u / (2 * (1 - u)) + u * ((1 + eta) * delta + u * (1 + u)))
    Lg = Log(E, q, lambda l: up(e1 * l + e0), 1)
    rows = log_bound(Lg, e1, e0, verbose=verbose, dd_split=up(u / 2 * (1 - u)))
    rel = max(r[5] for r in rows)
    assert all(r[6] == 0 for r in rows)
    return rel, rows


def od_exp(n, s, d, theta=2):
    E = Exp(Expansion(n, 53), s, d, theta)
    w, info, rows, red = E.bound(sub=8)
    return w, info, red


def od_log(n, s, d, q, eps_dd, theta=2, verbose=False):
    """the expansion log: start the double-double log of to_dd(x), within eps_dd relative of ln(to_dd(x)); to_dd's
    sum of the n - 1 lower parts errs by gamma_(n-2) sum |x_i|, so |ln x - ln to_dd(x)| <= delta"""
    M = Expansion(n, 53, convex=True)
    u = M.u
    rho = Fr(theta) * u
    g = (n - 2) * u / (1 - (n - 2) * u)
    w = up(g * rho / (1 - 2 * rho - g * rho))
    delta = up(w / (1 - w))
    E = Exp(M, s, d, theta)
    e1, e0 = eps_dd, up(delta * (1 + eps_dd))
    Lg = Log(E, q, lambda l: up(e1 * l + e0), 2, theta)
    rows = log_bound(Lg, e1, e0, verbose=verbose)
    rel = max(r[5] for r in rows)
    floor = max(r[6] for r in rows)
    return rel, floor, rows, delta


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


def convexity_check(f, pts):
    """f nondecreasing and convex at the sample points (each interior point at most the chord of its neighbours)"""
    v = [f(x) for x in pts]
    mono = all(a <= b for a, b in zip(v, v[1:]))
    conv = all(v[i] * (pts[i + 1] - pts[i - 1]) <= v[i - 1] * (pts[i + 1] - pts[i]) + v[i + 1] * (pts[i] - pts[i - 1])
               for i in range(1, len(pts) - 1))
    return mono and conv


if __name__ == '__main__':
    u = Fr(1, 2 ** 53)
    if len(sys.argv) > 1 and sys.argv[1] == 'check':
        # the log's chords take each regime's bound E(l) as nondecreasing and convex in l (an argument in the
        # appendix); sample it, and fire on a concave function (the control)
        rdd, _ = dd_log()
        n, (s, d, q) = 8, OD_PARAMS
        M = Expansion(n, 53, convex=True)
        E = Exp(M, s, d)
        e1, e0 = rdd, Fr(1, 2 ** 100)
        Lg = Log(E, q, lambda l: up(e1 * l + e0), 2)
        ok = True
        for (k0, m, sig, a, b, pts) in [(True, 0, 1, Fr(0), None, [Fr(0), Fr(1, 2 ** 40), Fr(1, 2 ** 20), Fr(1, 2 ** 8)]),
                                        (True, 3, -1, Fr(1, 2 ** 4), None, [Fr(1, 16), Fr(3, 32), Fr(1, 8)]),
                                        (False, 5, -1, Fr(1, 4), Fr(3466, 10000), [Fr(1, 3), Fr(1), Fr(20), XMAX])]:
            f = (lambda l: Lg.bin(l, k0, m, sig, a, up(l + e1 * l + e0))[0]) if b is None else \
                (lambda l: Lg.bin(l, k0, m, sig, a, b)[0])
            r = convexity_check(f, pts)
            print(f'k0={k0} m={m} sigma={sig}: nondecreasing and convex at {len(pts)} points: {r}')
            ok &= r
        concave = convexity_check(lambda l: l * (2 - l), [Fr(0), Fr(1, 2), Fr(1)])
        print('control, l (2 - l):', concave)
        print('PASS' if ok and not concave else 'FAIL')
        sys.exit(0 if ok and not concave else 1)
    print('the crate (u = 2^-53; exp relative; log relative to |ln x|, plus an absolute term)')
    w, info, red = dd_exp()
    rdd, _ = dd_log()
    print(f'DD s,d,q = {DD_PARAMS}: exp <= {fmt(w, u, 2)} u^2 (quoted {ceil3(w / u ** 2)}), log <= {fmt(rdd, u, 2)} '
          f'u^2 (quoted {ceil3(rdd / u ** 2)}), given f64 ln within 2^-40')
    s, d, q = OD_PARAMS
    w, info, red = od_exp(8, s, d)
    print(f'OD s,d,q = {OD_PARAMS}: exp <= {fmt(w, u, 8)} u^8 (quoted {ceil3(w / u ** 8)}), worst at {"k = 0" if info["k0"] else "k != 0"}, '
          f'm {info["m"]}, sign {info["sigma"]}, |r| in [{float(info["a"]):.4f}, {float(info["b"]):.4f}]; '
          f'reduction {fmt(red["dr"], u, 8)} u^8')
    rel, floor, rows, delta = od_log(8, s, d, q, rdd)
    print(f'OD log <= {fmt(rel, u, 8)} u^8 |ln x| + 2^{math.log2(floor):.2f} (quoted {ceil3(rel / u ** 8)} u^8 and '
          f'2^{math.ceil(math.log2(floor))}); start within {fmt(rdd, u, 2)} u^2 of ln to_dd(x), '
          f'|ln x - ln to_dd(x)| <= 2^{math.log2(delta):.2f}')
    for r in rows:
        tag = r[0] if r[0] == 'k!=0' else f'k=0 m={r[1]} sign={r[2]:+d}'
        print(f'   {tag:<18} {fmt(r[5], u, 8)} u^8' + (f' + 2^{math.log2(r[6]):.2f}' if r[6] else ''))
    print('the theorems at other n (theta = 2, s = 6, d and q the least that serve)')
    for n in (4, 12):
        s = 6
        d, q = degree(n, s), order(n, rdd)
        w, _, _ = od_exp(n, s, d)
        rel, floor, _, _ = od_log(n, s, d, q, rdd)
        print(f'n={n:2d} d={d} q={q}: exp <= {fmt(w, u, n)} u^n, log <= {fmt(rel, u, n)} u^n |ln x| + '
              f'2^{math.log2(floor):.2f}')
