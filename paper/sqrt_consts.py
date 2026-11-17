"""Lemma 19 of expansion-error-bounds.pdf (an operation's error and its result's part bounds from part bounds of its
operands) and Theorem 20 (the square root), in exact rationals. Units: r in y = A^(-1/2), a and h in A, m in y^2, g
and c dimensionless (A y^2 = 1), d in y, z in sqrt(A). usage: sqrt_consts.py [p]"""
import sys, math
from fractions import Fraction as Fr
from div_consts import vec_bounds


def up(x, bits=200):
    """x rounded up to a dyadic rational with `bits` significant bits (x >= 0). Every formula below is nondecreasing in
    the quantities it is applied to, so rounding them up keeps every bound an upper bound."""
    if x == 0:
        return Fr(0)
    n_, d_ = x.numerator, x.denominator
    e = n_.bit_length() - d_.bit_length() - bits
    if e >= 0:
        q = -(-n_ // (d_ << e))
        return Fr(q << e)
    q = -(-(n_ << -e) // d_)
    return Fr(q, 1 << -e)


def lemma_L(A, T, Q, u):
    n = len(A) - 1
    D = [A[0]]; X = []
    for m in range(n):
        Cm = T[m] * u * D[m] / (1 - T[m] * u)
        X.append(D[m] / (1 - T[m] * u))
        D.append(A[m + 1] + Cm)
    X.append(D[n] / (1 - Q * u))
    return X, Q * u * D[n] / (1 - Q * u)


def op_bounds(op, n, u, al, be, Zb, lam=None):
    """Lemma 19. al, be: part bounds of the operands (be = [|b|] for ADDF and MULF); Zb >= |Z|; lam: bounds
    lambda_m >= |a_m + b_m| (ADD) or lambda_0 >= |a_0 + b| (ADDF), if better than the triangle inequality.
    Returns (eps, parts, X): |Z - x| <= eps, |x_i| <= parts[i], level bounds X."""
    Rr = Fr(0); Dl = Fr(0)
    if op == 'mul':
        P = lambda m: sum(al[i] * be[m - i] for i in range(n) if 0 <= m - i < n)
        A = [(1 + u) * P(0)] + [(1 + u) * P(m) + u * P(m - 1) for m in range(1, n)]
        A.append(sum(al[i] * be[n - i] for i in range(1, n)) + u * P(n - 1))
        T = [m * (m + 1) for m in range(n)]; Q = n * n + n - 1
        X, Rr = lemma_L(A, T, Q, u)
        Dl = sum(al[i] * be[j] for i in range(n) for j in range(n) if i + j >= n + 1)
    elif op in ('add', 'mul_f'):
        if op == 'add':
            lm = lam if lam is not None else [al[m] + be[m] for m in range(n)]
        else:
            lm = [al[m] * be[0] for m in range(n)]
        A = [(1 + u) * lm[0]] + [(1 + u) * lm[m] + u * lm[m - 1] for m in range(1, n)] + [u * lm[n - 1]]
        T = [m for m in range(n)]; Q = n - 1
        X, Rr = lemma_L(A, T, Q, u)
    elif op == 'add_f':
        l0 = lam[0] if lam is not None else al[0] + be[0]
        eps_ = [u * l0]
        X = [(1 + u) * l0]
        for m in range(1, n):
            X.append((1 + u) * (al[m] + eps_[m - 1]))
            eps_.append(u * (al[m] + eps_[m - 1]))
        X.append(eps_[n - 1])
    else:
        raise ValueError(op)
    V, sig = vec_bounds(X, u, n)
    Psi = sum((u ** n + u ** (n + 1 - j)) * V[j] for j in range(1, n + 1))
    eps = u ** n * Zb + (1 + u ** n) * (Rr + Dl) + Psi
    W = [sum(V[j] for j in range(k + 1, n + 1)) for k in range(n + 1)]
    parts = [(1 + u) * (Zb + Rr + Dl + W[1])]
    for i in range(1, n):
        parts.append((1 + u) * (u * parts[i - 1] + W[i]))
    return up(eps), [up(t) for t in parts], [up(t) for t in X]


def sqrt_consts(n, p, theta, J=4):
    """Theorem 20: the bounds E_k on |r_k / y - 1| and the final relative error bound of the square root"""
    u = Fr(1, 2 ** p); rho = Fr(theta) * u
    upa = (1 - rho) / (1 - 2 * rho)                  # a_0 <= upa A, and |a_i| <= rho^i a_0
    apart = [rho ** i * upa for i in range(n)]        # a, units A
    hpart = [t / 2 for t in apart]                   # h = a/2, units A
    E = up(max((1 + 2 * u) / (1 - rho) - 1, 1 - (1 - 2 * u) * (1 - 2 * rho) / (1 - rho)))
    pi = [1 + E] + [Fr(0)] * (n - 1)                 # parts of r_0, units y
    steps = []
    for k in range(J):
        em, mpart, _ = op_bounds('mul', n, u, pi, pi, (1 + E) ** 2)
        mval = (1 + E) ** 2 + em
        eg, gpart, _ = op_bounds('mul', n, u, hpart, mpart, mval / 2)
        zc = up((2 * E + E * E) / 2 + em / 2 + eg)   # |1/2 - g| (exact value of the ADDF)
        lam0 = up(zc + sum(gpart[1:]))                # |1/2 - g_0|
        ec, cpart, _ = op_bounds('add_f', n, u, gpart, [Fr(1, 2)], zc, lam=[lam0])
        cval = zc + ec
        ed, dpart, _ = op_bounds('mul', n, u, cpart, pi, cval * (1 + E))
        dval = cval * (1 + E) + ed
        rd = (1 + E) + dval                           # |r + d|
        er, rpart, _ = op_bounds('add', n, u, pi, dpart, rd)
        En = up(Fr(3, 2) * E * E + E ** 3 / 2 + (1 + E) * (em / 2 + eg + ec) + ed + er)
        steps.append(dict(E=E, em=em, eg=eg, ec=ec, ed=ed, er=er, zc=zc, pi=pi, mpart=mpart, gpart=gpart,
                          cpart=cpart, dpart=dpart))
        E, pi = En, rpart
    ez, zpart, _ = op_bounds('mul', n, u, pi, apart, 1 + E)
    rel = E + ez
    return dict(u=u, steps=steps, EJ=E, ez=ez, rel=rel, pi=pi)


if __name__ == '__main__':
    p = int(sys.argv[1]) if len(sys.argv) > 1 else 53
    for theta in (1, 2):
        for n, J in ((4, 3), (8, 4), (12, 5)):
            r = sqrt_consts(n, p, theta, J)
            u = r['u']
            print(f'theta={theta} n={n} J={J}: |sqrt(x) - result| <= {float(r["rel"] / u ** n):.10g} u^n sqrt(x); '
                  f'E_k/u^n: {[float(s["E"] / u ** n) for s in r["steps"]] + [float(r["EJ"] / u ** n)]}')
    r = sqrt_consts(8, p, 2, 4); u = r['u']
    print('n=8 theta=2 last step (units u^n): em %.6g eg %.6g ec %.6g ed %.6g er %.6g ez %.6g' % tuple(
        float(t / u ** 8) for t in (r['steps'][-1]['em'], r['steps'][-1]['eg'], r['steps'][-1]['ec'],
                                    r['steps'][-1]['ed'], r['steps'][-1]['er'], r['ez'])))
    print('rel - 3 u^8 = 2^%.2f u^8' % math.log2(r['rel'] / u ** 8 - 3) if r['rel'] > 3 * u ** 8 else 'rel <= 3 u^8')
