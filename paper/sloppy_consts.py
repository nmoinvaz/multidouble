"""The error bound of the sloppy multiply (`OD::sloppy_mul`, `OV::sloppy_mul`) and of sums of its products
(`OdAcc::add_prod_sloppy`, `ODotAcc::add_prod_sloppy`), in exact rationals: Theorem 30 of expansion-error-bounds.pdf.

The sloppy multiply of n-part expansions (SLOPPY-MUL there) keeps levels 0..n-2 error-free (every deposit carried down
with two-sums to level n-2) and sums level n-1 in plain arithmetic: the products of orders n-1 and n by a chain of fused
multiply-adds, the errors of the products of order n-2, and the carries out of level n-2. The products of order n+1
and above are dropped. Its n levels go to the renormalization R_n, which is exact for n terms (Theorem 9(a)). So its
error is the roundings at level n-1 and the dropped products. Lemma 11 with level n-1 as the plain level gives
(Theorem 30(a) and (b))

    |ab - x| <= (R_s + Delta u) u^n M,    M = |a_0 b_0|,
    R_s = Q theta^(n-1) d_(n-1) / (1 - Q u),

with T_m = m (m + 1) two-sums at level m <= n-2 (as for MUL), Q = n^2 roundings at level n-1 (2n - 1 in the chain,
one per dep: (n-1)^2), alpha_m as for MUL for m <= n-2, and alpha_(n-1) = n + (n-1)/theta + (n-1) rho (the n
products of order n-1 and the n-1 of order n, exact, and the n-1 errors of order n-2). `counts` walks the algorithm's
deposits and checks T_m and Q.

A sum of K sloppy products deposits each product's n levels into the accumulator's n+1 levels, as `OdAcc::add`
deposits a value (Lemma 26, with N = n-1 and tau_n = 0). With tau_l the sloppy levels' bounds and E_prod = (R_s +
Delta u) u^n W, its bound is that of Theorem 27 (Theorem 30(c); `dot_bound`, which with MUL's levels in place of the
sloppy ones, tau_n = L_n u^n included, gives accumulator/acc_bound.py's values exactly):

    |Z - x| <= u^n |Z| + (1 + u^n)(E_lev + E_prod) + Phi.

usage: sloppy_consts.py [p] [n]   (default 53 8); prints the deposit counts, the level bounds, R_s and Delta u, and the
                                  dot bound for K = 1..64.
       sloppy_consts.py check     the control: the multiply's bound with the plain level one level higher (level
                                  n-2 plain) must exceed u^(n-1) M, which the n-level bound must not.
"""
import math
import sys
from fractions import Fraction as Fr
from math import comb

from constants import consts
from sqrt_consts import op_bounds


def counts(n):
    """SLOPPY-MUL's operations walked in the order of `expand_sloppy`: the two-sums at each level m <= n-2, and the
    roundings at level n-1 by source (carries out of level n-2, deps started at level n-1, the FMA chain)"""
    T = [0] * (n - 1)
    q = dict(carry=0, direct=0, chain=0)

    def dep(l):
        for m in range(l, n - 1):
            T[m] += 1
        q['carry' if l <= n - 2 else 'direct'] += 1

    # step (2): a_1 b_(n-1) by a product, a_i b_(n-i) for i = 2..n-1 and a_i b_(n-1-i) for i = 0..n-1 by FMAs
    q['chain'] = 1 + len(range(2, n)) + len(range(n))
    for l in range(1, n):  # step (3): the error of a_0 b_(l-1)
        dep(l)
    for i in range(1, n - 1):  # step (4): a_i b_j of order i + j <= n-2, its error one level lower
        for j in range(n - 1 - i):
            dep(i + j)
            dep(i + j + 1)
    return T, q


def sloppy_consts(n, theta, u):
    """level bounds L_m (|s_m| <= L_m u^m M, m = 0..n-1), R_s and the dropped products' coefficient (in u^(n+1) M)"""
    th = Fr(theta)
    rho = th * u
    alpha = [1 + u] + [(1 + u) * (m + 1) + Fr(m) / th for m in range(1, n - 1)]
    alpha.append(n + Fr(n - 1) / th + (n - 1) * rho)
    T = [m * (m + 1) for m in range(n - 1)]
    Q = n * n
    walked, q = counts(n)
    assert walked == T and sum(q.values()) == Q
    d = [alpha[0]]
    ell = []
    for m in range(n - 1):
        assert T[m] * u < 1
        ell.append(d[m] / (1 - T[m] * u))
        gamma = T[m] * d[m] / (th * (1 - T[m] * u))
        d.append(alpha[m + 1] + gamma)
    assert Q * u < 1
    ell.append(d[n - 1] / (1 - Q * u))
    L = [th ** m * ell[m] for m in range(n)]
    R = Q * th ** (n - 1) * d[n - 1] / (1 - Q * u)
    drop = sum((2 * n - 1 - k) * th ** k * u ** (k - n - 1) for k in range(n + 1, 2 * n - 1))
    return dict(L=L, R=R, drop=drop, Q=Q, T=T)


def rising(k, r):
    out = 1
    for i in range(r):
        out *= k + i
    return out


def dot_bound(n, theta, u, K):
    """second term of the sloppy dot's bound in units of u^n W: (1 + u^n)(E_lev + E_prod) + Phi"""
    assert (n + 1) * K * u < 1
    beta = 1 / (1 - (n + 1) * K * u)
    c = consts('mul', n, theta, u)
    s = sloppy_consts(n, theta, u)
    # a deposit's level l: the sloppy levels (L_l u^l, l < n), nothing at level n
    tau = [max(s['L'][l] * u ** l, (Fr(theta) * u) ** l) for l in range(n)] + [Fr(0)]
    eprod = (s['R'] + s['drop'] * u) * u ** n
    S = [beta * sum(comb(m, l) * tau[l] * (beta * u) ** (m - l) * rising(K, m - l) for l in range(m + 1))
         for m in range(n + 1)]
    elev = sum(comb(n + 1, l) * tau[l] * (beta * u) ** (n + 1 - l) * rising(K, n + 1 - l) for l in range(n + 1))
    al = [S[0]] + [Fr(0)] * (n - 1)
    phi = None
    for l in range(1, n + 1):
        zb = sum(S[:l + 1])
        eps, parts, _ = op_bounds('add_f', n, u, al, [S[l]], zb, lam=[al[0] + S[l]])
        al = parts
        phi = eps - u ** n * zb
    total = (1 + u ** n) * (elev + eprod) + phi
    assert c['kappa'] > 0
    return total / u ** n, eprod / u ** n, elev / u ** n


def lg(x):
    return math.log2(x) if x > 0 else float('-inf')


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'check':
        p, n = 53, 8
        u = Fr(1, 2 ** p)
        ok = True
        for theta in (1, 2):
            s = sloppy_consts(n, theta, u)
            # the multiply as the control's: n - 1 levels, the plain level at n - 2, so its bound is in u^(n-1) M
            w = sloppy_consts(n - 1, theta, u)
            good = (s['R'] + s['drop'] * u) * u ** n
            wrong = (w['R'] + w['drop'] * u) * u ** (n - 1)
            print(f'theta {theta}: n-level bound 2^{lg(good):.2f} M, one level higher 2^{lg(wrong):.2f} M, '
                  f'u^(n-1) = 2^{lg(u ** (n - 1)):.0f}')
            ok &= good < u ** (n - 1) / 2 ** 20 and wrong > u ** (n - 1)
        print('PASS' if ok else 'FAIL')
        sys.exit(0 if ok else 1)
    p = int(sys.argv[1]) if len(sys.argv) > 1 else 53
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    u = Fr(1, 2 ** p)
    print(f'p = {p}, n = {n}: sloppy multiply |ab - x| <= (R_s + Delta u) u^n |a_0 b_0|')
    T, q = counts(n)
    print(f'T_m (m <= {n - 2}) = {T}, {sum(T)} two-sums (MUL: {sum(m * (m + 1) for m in range(n))}); '
          f'Q = {sum(q.values())} roundings at level {n - 1}: {q["carry"]} carries out of level {n - 2}, '
          f'{q["direct"]} deps started at level {n - 1}, {q["chain"]} in the chain')
    for theta in (1, 2):
        s = sloppy_consts(n, theta, u)
        c = s['R'] + s['drop'] * u
        print(f'theta {theta}: L_m (log2) = {[round(lg(x), 2) for x in s["L"]]}, Q = {s["Q"]}')
        print(f'  R_s + Delta u = 2^{lg(c):.4f} = {float(c):.6e}, in units of 2^-418 (u^n/64): 2^{lg(c / 64):.4f}')
        print(f'  R_s = 2^{lg(s["R"]):.4f}, Delta u = 2^{lg(s["drop"] * u):.2f}')
        mul = consts('mul', n, theta, u)
        print(f'  default multiply: u^n |ab| + 2^{lg(mul["kappa"] * u):.2f} u^n |a_0 b_0|')
    print('sloppy dot of K products, theta 2: |Z - x| <= u^n |Z| + c_K u^n W; c_K (log2), of which E_prod, E_lev')
    for K in (1, 4, 16, 64):
        t, ep, el = dot_bound(n, 2, u, K)
        print(f'  K {K:3d}: c_K = {float(t):.6e} = 2^{lg(t):.4f}  (E_prod 2^{lg(ep):.4f}, E_lev 2^{lg(el):.4f})')
