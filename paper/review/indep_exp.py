"""Reviewer scratch: Theorem 34 (and Theorem 36 at one point) recomputed from the appendix's text with separate code.
Fractions rounded to nearest at 420 bits (not directed: a cross-check of the digits, not a proof). No import of the
PR's scripts."""
import math, sys
from fractions import Fraction as Fr
from decimal import Decimal, getcontext

BITS = 420
def rd(x):
    if x == 0:
        return Fr(0)
    e = x.numerator.bit_length() - x.denominator.bit_length() - BITS
    return Fr(round(x / Fr(2) ** e)) * Fr(2) ** e

p, n = 53, 8
u = Fr(1, 2 ** p)
us = u / (1 + u)
getcontext().prec = 400
LN2 = Fr(Decimal(2).ln())
E_ = Fr(Decimal(1).exp())

def fexp(z, terms=120):
    """e^z for rational z, |z| <= 2, to ~1e-120"""
    s, t = Fr(1), Fr(1)
    for i in range(1, terms):
        t = rd(t * z / i)
        s += t
    return rd(s)

def fexpm1(z, terms=120):
    """e^z - 1 without cancellation, for small rational z >= 0"""
    s, t = Fr(0), Fr(1)
    for i in range(1, terms):
        t = t * z / i
        if t.denominator.bit_length() > 4000:
            t = rd(t)
        s += t
    return s

def greedy(v, k):
    out = []
    for _ in range(k):
        c = v.numerator / v.denominator if v else 0.0
        out.append(Fr(c)); v -= Fr(c)
    return out

def levels(A, T, Q):
    N = len(A) - 1
    D = [A[0]]; X = []
    for m in range(N):
        C = T[m] * u * D[m] / (1 - T[m] * u)
        X.append(D[m] / (1 - T[m] * u))
        D.append(A[m + 1] + C)
    X.append(D[N] / (1 - Q * u))
    return X, Q * u * D[N] / (1 - Q * u)

def finish(X, R, Dl, Zb):
    sig = [sum(X[l:]) for l in range(n + 1)]
    V = [None] + [min(X[j - 1], us * (1 + u) ** (n - j) * sig[j - 1]) for j in range(1, n + 1)]
    eps = u ** n * Zb + (1 + u ** n) * (R + Dl) + sum((u ** n + u ** (n + 1 - j)) * V[j] for j in range(1, n + 1))
    W = lambda k: sum(V[j] for j in range(k + 1, n + 1))
    parts = [(1 + u) * (Zb + R + Dl + W(1))]
    for i in range(1, n):
        parts.append((1 + u) * (u * parts[-1] + W(i)))
    return rd(eps), [rd(x) for x in parts]

def G_mul(al, be, Zb):
    P = lambda m: sum(al[i] * be[m - i] for i in range(n) if 0 <= m - i < n)
    A = [(1 + u) * P(0)] + [(1 + u) * P(m) + u * P(m - 1) for m in range(1, n)]
    A.append(sum(al[i] * be[n - i] for i in range(1, n)) + u * P(n - 1))
    X, R = levels(A, [m * (m + 1) for m in range(n)], n * n + n - 1)
    Dl = sum(al[i] * be[j] for i in range(n) for j in range(n) if i + j >= n + 1)
    return finish(X, R, Dl, Zb)

def G_lin(lam, Zb):
    A = [(1 + u) * lam[0]] + [(1 + u) * lam[m] + u * lam[m - 1] for m in range(1, n)] + [u * lam[n - 1]]
    X, R = levels(A, list(range(n)), n - 1)
    return finish(X, R, Fr(0), Zb)

def G_add(al, be, Zb):
    return G_lin([al[m] + be[m] for m in range(n)], Zb)

def G_mulf(al, f, Zb):
    return G_lin([al[m] * f for m in range(n)], Zb)

def G_addf(al, lam0, Zb):
    e = [u * lam0]; X = [(1 + u) * lam0]
    for m in range(1, n):
        X.append((1 + u) * (al[m] + e[-1])); e.append(u * (al[m] + e[-1]))
    X.append(e[-1])
    return finish(X, Fr(0), Fr(0), Zb)

# constants
def rn_bits(x, bits):
    e = math.floor(math.log2(float(x)))
    q = x / Fr(2) ** (e - bits + 1)
    return Fr(round(q)) * Fr(2) ** (e - bits + 1)
ch = rn_bits(LN2, 42)
cl = greedy(LN2 - ch, n)
eta = abs(LN2 - ch - sum(cl))
Lam = Fr(float(1 / LN2))
s, d = 6, 43
F = [greedy(Fr(1, math.factorial(j)), n) for j in range(d + 1)]
phi = [abs(sum(F[j]) - Fr(1, math.factorial(j))) for j in range(d + 1)]
absv = lambda v: [abs(x) for x in v]

def lemma32(X, gamma, alpha_low, rbar):
    K = 1075
    beta = X * (abs(Lam - 1 / LN2) + u * Lam)
    rho_e = (Fr(1, 2) + beta) * LN2 + gamma
    a0 = rho_e + gamma + K * abs(LN2 - ch)
    assert a0 < Fr(1, 2)
    e1, mu = G_mulf(absv(cl), K, K * abs(sum(cl)))
    def b(rb):
        e2, pr = G_add([a0] + alpha_low, mu, rb + K * eta + e1)
        return e1 + e2 + K * eta, pr
    dstar, _ = b(rho_e)
    return rho_e, dstar, b

def lemma33(pi, a, b, m, sigma):
    tailp = sum(pi[1:])
    bp = min(b, Fr(2) ** (m - s) + tailp) / 2 ** m
    pp = [min(pi[0], Fr(2) ** (m - s)) / 2 ** m] + [x / 2 ** m for x in pi[1:]]
    tau = lambda j: (fexp(2 ** j * bp) - 1) if sigma > 0 else (1 - 1 / fexp(2 ** j * bp))
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

def thm34_case(pi, delta, a, b, m, sigma):
    E, psi, _ = lemma33(pi, a, b, m, sigma)
    Z = (fexp(b) if sigma > 0 else 1 / fexp(a)) + E
    es, _ = G_addf(psi, Z + sum(psi[1:]), Z)
    v = fexp(a - delta) if sigma > 0 else 1 / fexp(b + delta)
    return (E + es) / v + fexpm1(delta)

if __name__ == '__main__':
    theta = 2; rho = theta * u; X = Fr(7452, 10)
    alpha_low = [rho ** i * X for i in range(1, n)]
    rho_e, dstar, red = lemma32(X, rho * X / (1 - rho), alpha_low, None)
    print('rho_e', float(rho_e), 'delta*/u^8', float(dstar / u ** 8))
    _, pir = red(rho_e + dstar)
    tail = sum(pir[1:]); top = rho_e + dstar
    worst = (0, None)
    for m in range(0, 7):
        lo = Fr(0) if m == 0 else Fr(2) ** (m - s - 1) - tail
        if lo > top:
            break
        hi = min(top, Fr(2) ** (m - s) + tail)
        lo_e = lo if lo > 0 else hi / 2 ** 16
        # my own partition: 12 geometric sub-intervals (the PR uses 8), so the maximum differs slightly from theirs
        NS = int(sys.argv[1]) if len(sys.argv) > 1 else 8
        edges = [lo_e] + [Fr(lo_e) * Fr(float(hi / lo_e) ** (i / NS)) for i in range(1, NS)] + [hi]
        if lo == 0:
            edges = [Fr(0)] + edges
        for sigma in (1, -1):
            for a, b in zip(edges, edges[1:]):
                dl, pi = red(b + dstar)
                r = thm34_case(pi, dl, a, b, m, sigma)
                if r > worst[0]:
                    worst = (r, ('k!=0', m, sigma, float(a), float(b)))
    # k = 0
    top0 = 1 / (2 * Lam * (1 - u)) * (1 + 3 * rho)
    lad = lambda t: [rho ** i * t * (1 - rho) / (1 - 2 * rho) for i in range(n)]
    tail0 = sum(lad(top0)[1:])
    for m in range(0, 7):
        lo = Fr(0) if m == 0 else Fr(2) ** (m - s - 1) - tail0
        if lo > top0:
            break
        hi = min(top0, Fr(2) ** (m - s) + tail0)
        lo_e = lo if lo > 0 else hi / 2 ** 16
        edges = [lo_e] + [Fr(lo_e) * Fr(float(hi / lo_e) ** (i / NS)) for i in range(1, NS)] + [hi]
        if lo == 0:
            edges = [Fr(0)] + edges
        for sigma in (1, -1):
            for a, b in zip(edges, edges[1:]):
                r = thm34_case(lad(b), Fr(0), a, b, m, sigma)
                if r > worst[0]:
                    worst = (r, ('k=0', m, sigma, float(a), float(b)))
    print('Theorem 34, n = 8, s = 6, d = 43, theta = 2: max over cases =', float(worst[0] / u ** 8), 'u^8 at', worst[1])
