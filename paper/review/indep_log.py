"""Reviewer scratch: Theorem 41 recomputed from the appendix's text with separate code (see indep_exp.py). The
'Convexity' paragraph's modifications are applied: VecSum's second bound alone, b' and pi'_0 without their minima,
tau_j = 2^j b' for sigma = -1, and f-bar's second branch as E + b + delta."""
import math, sys
from fractions import Fraction as Fr
import indep_exp as I
from indep_exp import rd, u, n, us, fexp, fexpm1, greedy, levels, absv, LN2, Lam, ch, cl, eta, F, phi, s, d

def finish(X, R, Dl, Zb):
    sig = [sum(X[l:]) for l in range(n + 1)]
    V = [None] + [us * (1 + u) ** (n - j) * sig[j - 1] for j in range(1, n + 1)]
    eps = u ** n * Zb + (1 + u ** n) * (R + Dl) + sum((u ** n + u ** (n + 1 - j)) * V[j] for j in range(1, n + 1))
    W = lambda k: sum(V[j] for j in range(k + 1, n + 1))
    parts = [(1 + u) * (Zb + R + Dl + W(1))]
    for i in range(1, n):
        parts.append((1 + u) * (u * parts[-1] + W(i)))
    return rd(eps), [rd(x) for x in parts]
I.finish = finish            # G_mul, G_add, G_mulf, G_addf now use the second bound alone
G_mul, G_add, G_mulf, G_addf = I.G_mul, I.G_add, I.G_mulf, I.G_addf

def lemma33c(pi, a, b, m, sigma):
    bp = b / 2 ** m
    pp = [x / 2 ** m for x in pi]
    tau = lambda j: (fexp(2 ** j * bp) - 1) if sigma > 0 else 2 ** j * bp
    g = lambda j: (1 + tau(j)) if sigma > 0 else 1 / fexp(2 ** j * a / 2 ** m)
    v, e, kap = Fr(1, math.factorial(d)), phi[d], absv(F[d])
    for j in range(d - 1, 1, -1):
        ep, mu = G_mul(pp, kap, bp * (v + e))
        ea, kap = G_add(absv(F[j]), mu, Fr(1, math.factorial(j)) + phi[j] + bp * (v + e) + ep)
        e = rd(phi[j] + bp * e + ep + ea)
        v = rd(Fr(1, math.factorial(j)) + bp * v)
    e1, om1 = G_mul(pp, kap, bp * (v + e))
    e2, om = G_mul(pp, om1, bp * (bp * (v + e) + e1))
    Em = e2 + bp * (e1 + bp * e) + bp ** (d + 1) / math.factorial(d + 1) / (1 - bp / (d + 2))
    e3, psi = G_add(pp, om, tau(0) + Em)
    E = rd(Em + e3)
    for j in range(m):
        em, nu = G_mul(psi, psi, (tau(j) + E) ** 2)
        es, psi = G_add([2 * x for x in psi], nu, tau(j + 1) + 2 * E * (1 + tau(j)) + E * E + em)
        E = rd(2 * g(j) * E + E * E + em + es)
    return E, psi, tau(m)

q = 4
theta = 2; rho = theta * u
A = {i: greedy(Fr((-1) ** (i + 1), i), n) for i in range(2, q + 1)}
phip = {i: abs(sum(A[i]) - Fr((-1) ** (i + 1), i)) for i in A}
eps_dw = Fr(15351, 1000) * u * u          # the quoted double-word bound
gg = (n - 2) * u / (1 - (n - 2) * u)
w = gg * rho / (1 - 2 * rho - gg * rho)
d0 = w / (1 - w)
Estart = lambda l: eps_dw * (l + d0) + d0
XMAX = Fr(7452, 10)

def piy(yb):
    t = yb * (1 - u) / (1 - 2 * u)
    return [t, u * t] + [Fr(0)] * (n - 2)

def red36(yb):
    """Lemma 37 for -y0: X = y-bar, gamma = 2 u y-bar, alpha = pi^y"""
    K = 1075
    beta = yb * (abs(Lam - 1 / LN2) + u * Lam)
    gamma = 2 * u * yb
    rho_e = (Fr(1, 2) + beta) * LN2 + gamma
    a0 = rho_e + gamma + K * abs(LN2 - ch)
    e1, mu = G_mulf(absv(cl), K, K * abs(sum(cl)))
    def b(rb):
        e2, pr = G_add([a0] + piy(yb)[1:], mu, rb + K * eta + e1)
        return e1 + e2 + K * eta, pr
    dstar, _ = b(rho_e)
    return rho_e, dstar, b

def calE(l, k0, m, sigma, a, b):
    E0 = Estart(l); yb = l + E0
    if k0:
        pi, dl = piy(yb), Fr(0)
    else:
        _, dstar, red = red36(yb)
        dl, pi = red(b + dstar)
    Em, psi, taum = lemma33c(pi, a, b, m, sigma)
    xi = fexp(E0 + dl - a) if sigma > 0 else fexp(E0 + b + dl)
    fbar = max(xi - 1, E0 + b + dl)
    t = xi * (1 - rho) / (1 - 2 * rho)
    chi1 = [rho ** i * t for i in range(n)]
    _, pif = G_addf(chi1, fbar + sum(chi1[1:]), fbar)
    eft, nu = G_mul(pif, psi, fbar * (taum + Em))
    bh = b + dl
    efpt, zeta = G_add(pif, psi, 2 * (fexpm1(bh) - bh) + fexp(bh) * fexpm1(E0 + dl) + Em)
    cst = fexpm1(E0); Dl = fexp(E0) * fexpm1(dl)
    ec, chi = G_add(zeta, nu, cst + xi * Em + Dl + eft + efpt)
    Ec = xi * Em + Dl + eft + efpt + ec
    C = cst + Ec
    v, e, kap = Fr(1, q), phip[q], absv(A[q])
    for i in range(q - 1, 1, -1):
        ep, mu = G_mul(chi, kap, C * (v + e))
        ea, kap = G_add(absv(A[i]), mu, Fr(1, i) + phip[i] + C * (v + e) + ep)
        e = phip[i] + C * e + ep + ea
        v = Fr(1, i) + C * v
    e00, om0 = G_mul(chi, chi, C * C)
    ew, om = G_mul(om0, kap, (C * C + e00) * (v + e))
    W = ew + e00 * (v + e) + C * C * e
    er, omr = G_add(chi, om, C + C * C * v + W)
    P = er + W + C ** (q + 1) / ((q + 1) * (1 - C)) + Ec / (1 - C)
    ey, _ = G_add(piy(yb), omr, l + P)
    return rd(ey + P)

if __name__ == '__main__':
    e1 = eps_dw; e0 = d0 * (1 + eps_dw)
    lg = lambda x: (x.numerator.bit_length() - x.denominator.bit_length())
    zk = 1 / (2 * Lam * (1 - u))
    # k = 0
    for m in range(0, 6):
        a = Fr(0) if m == 0 else Fr(2) ** (m - s - 1) * (1 - 2 * u)
        cap = min(Fr(2) ** (m - s) * (1 + 2 * u), zk * (1 + 2 * u))
        lo = Fr(0) if m == 0 else (a - e0) / (1 + e1)
        hi = (cap + e0) / (1 - e1)
        for sigma in (1, -1):
            f = lambda l: calE(l, True, m, sigma, a, l + Estart(l))
            if lo == 0:
                f0, f1 = f(Fr(0)), f(hi)
                print(f'k=0 m={m} sign={sigma:+d}: {float((f1 - f0) / hi / u ** 8):.6f} u^8 + 2^{math.log2(float(f0 * 2 ** 600)) - 600:.2f}', flush=True)
            else:
                print(f'k=0 m={m} sign={sigma:+d}: {float(max(f(lo) / lo, f(hi) / hi) / u ** 8):.6f} u^8', flush=True)
    # k != 0
    lk = ((1 - u) / (2 * Lam * (1 + u)) - e0) / (1 + e1)
    yb = XMAX + Estart(XMAX)
    rho_e, dstar, red = red36(yb)
    _, pir = red(rho_e + dstar)
    tail, top = sum(pir[1:]), rho_e + dstar
    worst = (0, None)
    for m in range(0, 7):
        rlo = Fr(0) if m == 0 else Fr(2) ** (m - s - 1) - tail
        if rlo > top:
            break
        rhi = min(top, Fr(2) ** (m - s) + tail)
        lo_e = rlo if rlo > 0 else rhi / 2 ** 16
        edges = [lo_e] + [Fr(lo_e) * Fr(float(rhi / lo_e) ** (i / 4)) for i in range(1, 4)] + [rhi]
        if rlo == 0:
            edges = [Fr(0)] + edges
        for sigma in (1, -1):
            for ra, rb in zip(edges, edges[1:]):
                for l in (lk, Fr(1), Fr(4), XMAX):
                    r = calE(l, False, m, sigma, ra, rb) / l
                    if r > worst[0]:
                        worst = (r, (m, sigma, float(ra), float(rb), float(l)))
    print(f'k!=0: {float(worst[0] / u ** 8):.6f} u^8 at (m, sign, |r| interval, l) = {worst[1]}')
