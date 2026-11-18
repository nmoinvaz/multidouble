"""The constants of Theorems 14 and 15 of expansion-error-bounds.pdf, computed exactly in rationals from their
recursions.
usage: constants.py [p]   (default p = 53); prints, per operation, n and theta, the level constants and kappa, and
the values of Table IV."""
import sys
from fractions import Fraction as Fr
import math

def level_consts(op, n, theta, u):
    """(alpha, T, Q, Delta_coef): alpha_m (m = 0..n), TwoSums per level T_m (m < n), roundings at level n Q,
    and the dropped-products coefficient (Delta <= coef u^(n+1) M)."""
    th = Fr(theta)
    if op == 'mul':
        alpha = [1 + u] + [(1 + u) * (m + 1) + Fr(m) / th for m in range(1, n)] + [(n - 1) + Fr(n) / th]
        T = [m * (m + 1) for m in range(n)]
        Q = n * n + n - 1
        rho = th * u
        drop = sum((2 * n - 1 - k) * th ** k * u ** (k - n - 1) for k in range(n + 1, 2 * n - 1))
    elif op in ('add', 'mul_f'):
        alpha = [1 + u] + [(1 + u) + 1 / th for m in range(1, n)] + [1 / th]
        T = [m for m in range(n)]
        Q = n - 1
        drop = Fr(0)
    else:
        raise ValueError(op)
    return alpha, T, Q, drop

def consts(op, n, theta, u):
    """L_m (|c_m| <= L_m u^m M), R (formation roundings <= R u^(n+1) M), Delta, Lambda, beta, kappa"""
    th = Fr(theta)
    if op == 'add_f':
        L = [(1 + u) * sum(th ** k for k in range(m + 1)) for m in range(n)] + [sum(th ** k for k in range(n))]
        R = Fr(0); drop = Fr(0)
    else:
        alpha, T, Q, drop = level_consts(op, n, theta, u)
        d = [None] * (n + 1); c = [None] * n; ell = [None] * (n + 1)
        prev_c = Fr(0)
        for m in range(n):
            d[m] = alpha[m] + prev_c
            assert T[m] * u < 1
            c[m] = T[m] * d[m] / (th * (1 - T[m] * u))
            ell[m] = d[m] / (1 - T[m] * u)
            prev_c = c[m]
        d[n] = alpha[n] + prev_c
        assert Q * u < 1
        ell[n] = d[n] / (1 - Q * u)
        L = [th ** m * ell[m] for m in range(n + 1)]
        R = Q * th ** n * d[n] / (1 - Q * u)
    Lam = sum(L)
    beta = (1 + u) ** (n - 1) / (1 - u)
    kappa = 2 * beta * Lam + (1 + u ** n) * (R + drop)
    return dict(L=L, R=R, drop=drop, Lam=Lam, beta=beta, kappa=kappa)

if __name__ == '__main__':
    p = int(sys.argv[1]) if len(sys.argv) > 1 else 53
    u = Fr(1, 2 ** p)
    print(f'p = {p}: |error| <= u^n |exact| + kappa u^(n+1) M; log2(kappa) and log2(kappa u)')
    for op in ('add', 'add_f', 'mul_f', 'mul'):
        for theta in (1, 2):
            row = []
            for n in range(2, 13):
                try:
                    k = consts(op, n, theta, u)['kappa']
                    row.append(f'{n}:{math.log2(k):6.1f}/{math.log2(k * u):6.1f}')
                except AssertionError:
                    row.append(f'{n}: n/a')
            print(f'{op:6s} theta={theta}  ' + '  '.join(row))
    for theta in (1, 2):
        k = consts('mul', 8, theta, u)
        print(f'mul n=8 theta={theta}: L_m (log2) =', [round(math.log2(x), 2) for x in k['L']],
              ' R/u^(n+1)M = 2^%.2f' % math.log2(k['R']), ' Delta coef = 2^%.2f' % math.log2(k['drop']),
              ' kappa = 2^%.2f' % math.log2(k['kappa']))
    print('Table IV, n = 8: kappa for theta = 1 and 2, and the second term kappa u^(n+1) M for theta = 2 (log2)')
    for op in ('mul', 'add', 'mul_f', 'add_f'):
        k1, k2 = (consts(op, 8, theta, u)['kappa'] for theta in (1, 2))
        print(f'{op:6s} kappa = 2^{math.log2(k1):.2f}, 2^{math.log2(k2):.2f};  kappa u^9 = 2^{math.log2(k2 * u ** 9):.2f}')


def theta_out(op, n, theta, u):
    """Theorem 17: the theta' with which the result of MUL or MULF satisfies H(theta'), or None if xi <= 0.
    theta'^i = (1+u)^i + i u (1+u)^(n+i-1) Lambda / xi, xi = (zeta - (R + Delta) u^(n+1) - u^2 (1+u)^(n-1) Lambda)/(1+u)"""
    C = consts(op, n, theta, u)
    rho = Fr(theta) * u
    zeta = ((1 - 2 * rho) / (1 - rho)) ** (2 if op == 'mul' else 1)  # adds: leading parts of one sign
    xi = (zeta - (C['R'] + C['drop']) * u ** (n + 1) - u ** 2 * (1 + u) ** (n - 1) * C['Lam']) / (1 + u)
    if xi <= 0:
        return None
    best = 0.0
    for i in range(1, n):
        t = (1 + u) ** i + i * u * (1 + u) ** (n + i - 1) * C['Lam'] / xi
        best = max(best, float(t) ** (1.0 / i))
    return best


if __name__ == '__main__':
    p = int(sys.argv[1]) if len(sys.argv) > 1 else 53
    u = Fr(1, 2 ** p)
    print("Theorem 17: theta' of the result (H(theta) inputs; for ADD and ADDF leading parts of one sign)")
    for op in ('mul', 'mul_f', 'add', 'add_f'):
        for theta in (1, 2):
            row = []
            for n in range(2, 13):
                t = theta_out(op, n, theta, u)
                row.append(f'{n}:{"none" if t is None else "1+2^%.1f" % math.log2(t - 1) if t > 1 else "1"}')
            print(f'{op:6s} theta={theta}  ' + '  '.join(row))
