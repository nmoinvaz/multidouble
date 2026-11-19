"""Theorem 19 of expansion-error-bounds.pdf (division): its recursion, in exact rationals. All magnitudes are in
units of |a_0|, and quotient terms are multiplied by |b_0|. Returns per step k the part bounds P^(k), the quotient
bounds qbar_k (Q_k below), the level bounds X^(k) of each remainder update, the update errors eps_k, and the final
kappa_DIV (K below) with |a/b - x| <= (u^n + kappa_DIV u^(n+1)) |a/b| for a, b satisfying H(theta).
usage: div_consts.py [p]. Every printed value is an upper bound, rounded up at the digits shown (rounding.py)."""
import sys
from fractions import Fraction as Fr

from rounding import dec_up, lg2_up


def vec_bounds(X, u, n):
    """VecSum output bounds V_0..V_n from level bounds X_0..X_n (Theorem 9(d))"""
    us = u / (1 + u)
    sig = [sum(X[l:]) for l in range(n + 1)]
    V = [(1 + u) ** n * sig[0]] + [min(X[j - 1], us * (1 + u) ** (n - j) * sig[j - 1]) for j in range(1, n + 1)]
    return V, sig


def renorm_err(V, u, n):
    """Theorem 9(b): min_k B_k"""
    us = u / (1 + u)
    return min(us ** (n - k) * V[k] + sum(us ** (n + 1 - j) * V[j] for j in range(k + 1, n + 1)) for k in range(n + 1))


def smf_step(P, Qk, n, theta, u):
    """one remainder update r - q b: level bounds (Lemma 11), its error bound, and the part bounds of its result"""
    rho = Fr(theta) * u
    G = [u * (P[0] + Qk)] + [P[i] + (1 + u) * rho ** i * Qk for i in range(1, n)]
    A = [(1 + u) * G[0]] + [(1 + u) * G[m] + u * G[m - 1] + u * rho ** (m - 1) * Qk for m in range(1, n)]
    A.append(u * G[n - 1] + u * rho ** (n - 1) * Qk)
    T = [0] + [2 * m for m in range(1, n)]
    Q = 2 * n - 1
    D = [A[0]]; X = []
    for m in range(n):
        Cm = T[m] * u * D[m] / (1 - T[m] * u)
        X.append(D[m] / (1 - T[m] * u))
        D.append(A[m + 1] + Cm)
    X.append(D[n] / (1 - Q * u))
    Rr = Q * u * D[n] / (1 - Q * u)
    V, sig = vec_bounds(X, u, n)
    eps = Rr + renorm_err(V, u, n)
    W = [sum(V[j] for j in range(k + 1, n + 1)) for k in range(n + 1)]
    Pn = [(1 + u) * (sig[0] + W[1])]
    for i in range(1, n):
        Pn.append((1 + u) * (u * Pn[i - 1] + W[i]))
    return dict(X=X, eps=eps, P=Pn, Rr=Rr)


def div_consts(n, p, theta):
    u = Fr(1, 2 ** p)
    rho = Fr(theta) * u
    P = [rho ** i for i in range(n)]
    steps = []
    Qs = []
    for k in range(n + 1):
        Qk = (1 + u) * P[0]
        Qs.append(Qk)
        if k == n:
            break
        st = smf_step(P, Qk, n, theta, u)
        st['Pin'] = P; st['Qk'] = Qk
        steps.append(st)
        P = st['P']
    tau = sum(P[1:]) + u * P[0] + Qs[n] * rho / (1 - rho)
    Theta = tau + sum(st['eps'] for st in steps)
    # final renormalization of the n + 1 quotient terms (units |a_0| / |b_0|)
    Vq, _ = vec_bounds(Qs, u, n)
    tail = u ** n * sum(Vq[1:]) + sum(u ** (n + 1 - j) * Vq[j] for j in range(1, n + 1))
    lo = 1 - 2 * rho                               # |a/b| >= lo |a_0| / |b_0|
    qerr = Theta * (1 - rho) / (1 - 2 * rho)       # |a/b - sum q| <= qerr |a_0| / |b_0|
    K = ((1 + u ** n) * qerr + tail) / lo / u ** (n + 1)
    return dict(u=u, steps=steps, Qs=Qs, tau=tau, Theta=Theta, qerr=qerr, K=K, P_last=P)


if __name__ == '__main__':
    p = int(sys.argv[1]) if len(sys.argv) > 1 else 53
    for theta in (1, 2):
        row = []
        for n in range(2, 15):
            r = div_consts(n, p, theta)
            row.append(f'{n}:{lg2_up(r["K"], 1):>6s}/{lg2_up(r["K"] * r["u"], 1):>6s}')
        print(f'div theta={theta}  log2 kappa_DIV / log2 kappa_DIV u:  ' + '  '.join(row))
    r = div_consts(8, p, 2)
    u = r['u']
    print('n=8 theta=2: P_0^(k)/u^k: [' + ', '.join(dec_up(st['Pin'][0] / u ** k, 2) for k, st in enumerate(r['steps'])) + ']')
    print('             eps_k/u^(n+k): [' + ', '.join(lg2_up(st['eps'] / u ** (8 + k + 1), 2) for k, st in enumerate(r['steps']))
          + '] (log2, units u^(n+k+1))')
    print(f'             Theta_0/u^9 = 2^{lg2_up(r["tau"] / u ** 9, 2)}, Theta/u^9 = 2^{lg2_up(r["Theta"] / u ** 9, 2)}, '
          f'kappa_DIV = 2^{lg2_up(r["K"], 2)}')
