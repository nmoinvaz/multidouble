"""Tests of the Python bindings against exact rational arithmetic (fractions.Fraction, no shared code), with controls
that feed the same checks a wrong result and must fail. u^2 = 2^-106 is the double-double unit."""
from fractions import Fraction

import numpy as np
import pytest

import multidouble as md

U2 = Fraction(1, 2**106)
N = 1003  # not a multiple of 8: the last 3 elements take the scalar path


def rand_dd(rng, n, emax=20):
    """normalized double-doubles with random signs, exponents in [-emax, emax] and full-width low parts"""
    hi = (1 + rng.random(n)) * np.exp2(rng.integers(-emax, emax + 1, n)) * rng.choice([-1.0, 1.0], n)
    lo = rng.uniform(-1, 1, n) * np.abs(hi) * 2.0**-53
    h = hi + lo
    return h, lo - (h - hi)


def exact(h, l):
    return [Fraction(a) + Fraction(b) for a, b in zip(h, l)]


def worst_rel(got_h, got_l, want):
    """max |got - want| / |want| in units of u^2"""
    return max(abs(g - w) / abs(w) for g, w in zip(exact(got_h, got_l), want) if w != 0) / U2


@pytest.fixture
def ab():
    rng = np.random.default_rng(1)
    return rand_dd(rng, N) + rand_dd(rng, N)


def test_elementwise_within_bounds(ab):
    ah, al, bh, bl = ab
    a, b = exact(ah, al), exact(bh, bl)
    assert worst_rel(*md.add(ah, al, bh, bl), [x + y for x, y in zip(a, b)]) <= 3
    assert worst_rel(*md.sub(ah, al, bh, bl), [x - y for x, y in zip(a, b)]) <= 3
    assert worst_rel(*md.mul(ah, al, bh, bl), [x * y for x, y in zip(a, b)]) <= 5
    # division: the residual of the quotient, q b - a, relative to a
    qh, ql = md.div(ah, al, bh, bl)
    assert max(abs(q * y - x) / abs(x) for q, x, y in zip(exact(qh, ql), a, b)) / U2 <= 8


def test_control_dropped_low_part_is_caught(ab):
    ah, al, bh, bl = ab
    a, b = exact(ah, al), exact(bh, bl)
    h, _ = md.add(ah, al, bh, bl)
    assert worst_rel(h, np.zeros_like(h), [x + y for x, y in zip(a, b)]) > 3


def test_dd_op_codes_match_the_named_functions(ab):
    ah, al, bh, bl = ab
    for op, f in ((0, md.add), (1, md.mul), (2, md.div), (3, md.sub)):
        h1, l1 = md.dd_op(op, ah, al, bh, bl)
        h2, l2 = f(ah, al, bh, bl)
        assert np.array_equal(h1, h2) and np.array_equal(l1, l2)


def test_lanes_and_tail_agree_bitwise(ab):
    """the same values give the same bits in the 8-lane part and in the scalar tail"""
    ah, al, bh, bl = (x[:8] for x in ab)
    # 11 elements: the first 8 in one vector, then elements 0..2 again in the scalar tail
    rep = lambda x: np.concatenate([x, x[:3]])  # noqa: E731
    for f in (md.add, md.sub, md.mul, md.div):
        h, l = f(rep(ah), rep(al), rep(bh), rep(bl))
        assert np.array_equal(h[8:], h[:3]) and np.array_equal(l[8:], l[:3])


def test_rust_add_is_the_numpy_dd_add_bitwise(ab):
    h1, l1 = md.add(*ab)
    h2, l2 = md.dd_add(*ab)
    assert np.array_equal(h1, h2) and np.array_equal(l1, l2)


def test_numpy_helpers_exact_and_within_bounds(ab):
    ah, al, bh, bl = ab
    s, e = md.two_sum(ah, bh)
    assert all(Fraction(x) + Fraction(y) == Fraction(p) + Fraction(q) for x, y, p, q in zip(ah, bh, s, e))
    p, e = md.two_prod(ah, bh)
    assert all(Fraction(x) * Fraction(y) == Fraction(u) + Fraction(v) for x, y, u, v in zip(ah, bh, p, e))
    a = 0.1234567891011
    want = [Fraction(a) * x for x in exact(ah, al)]
    assert worst_rel(*md.dd_scale(ah, al, a), want) <= 4
    want = [y + Fraction(a) * x for x, y in zip(exact(ah, al), exact(bh, bl))]
    # an axpy can cancel; bound it relative to |y| + |a x|
    h, l = md.dd_axpy(a, ah, al, bh, bl)
    scale = [abs(y) + abs(Fraction(a) * x) for x, y in zip(exact(ah, al), exact(bh, bl))]
    assert max(abs(g - w) / s for g, w, s in zip(exact(h, l), want, scale)) / U2 <= 8
    assert md.dd_norm(ah, al) == float(np.max(np.abs(ah + al))) and md.dd_norm(ah[:0], al[:0]) == 0.0


def residual(Ah, Al, bh, bl, xh, xl):
    """max |b - A x| / (|A| |x| + |b|), exactly"""
    n = len(bh)
    A = [[Fraction(Ah[i, j]) + Fraction(Al[i, j]) for j in range(n)] for i in range(n)]
    b, x = exact(bh, bl), exact(xh, xl)
    worst = Fraction(0)
    for i in range(n):
        r = b[i] - sum(A[i][j] * x[j] for j in range(n))
        s = sum(abs(A[i][j] * x[j]) for j in range(n)) + abs(b[i])
        worst = max(worst, abs(r) / s)
    return worst / U2


def test_dd_solve_backward_error():
    rng = np.random.default_rng(2)
    n = 24
    Ah, Al = rand_dd(rng, n * n, emax=2)
    Ah, Al = Ah.reshape(n, n), Al.reshape(n, n)
    Ah += np.diag(np.full(n, 8.0))  # well conditioned
    bh, bl = rand_dd(rng, n, emax=2)
    xh, xl = md.dd_solve(Ah, Al, bh, bl)
    assert residual(Ah, Al, bh, bl, xh, xl) <= 64 * n
    # control: x off by 1e-24 relative must fail the same check
    assert residual(Ah, Al, bh, bl, xh, xl + 1e-24 * xh) > 64 * n


def test_errors():
    z = np.zeros(4)
    with pytest.raises(ValueError):
        md.dd_op(4, z, z, z, z)
    with pytest.raises(ValueError):
        md.add(z, z, np.zeros(5), np.zeros(5))
    with pytest.raises(ValueError):
        md.dd_solve(np.zeros((3, 3)), np.zeros((3, 3)), np.ones(3), np.zeros(3))  # singular
    with pytest.raises(ValueError):
        md.qd_add_dd(z, z, z, z, z, np.zeros(5))
    assert md.isa() in ("avx512", "avx2", "sse2", "neon", "portable")


def test_two_prod_large_operands():
    """operands above 2^996, where Dekker's _SPLIT * a overflows: the scaled split keeps the product exact, and below
    2^996 the split is bitwise the plain one"""
    a, b = np.array([2e300, -1.7e308, 3.0]), np.array([1e-300, 1e-308, 1e300])
    p, e = md.two_prod(a, b)
    assert np.all(np.isfinite(p)) and np.all(np.isfinite(e))
    assert all(Fraction(x) * Fraction(y) == Fraction(u) + Fraction(v) for x, y, u, v in zip(a, b, p, e))

    def plain_split(x):
        t = md._SPLIT * x
        hi = t - (t - x)
        return hi, x - hi

    # control: the plain split fails on the same operands
    with np.errstate(all="ignore"):
        assert np.isnan(plain_split(a[:2])[0]).all()
    rng = np.random.default_rng(3)
    x = rand_dd(rng, 2000, emax=900)[0]
    assert all(np.array_equal(u, v) for u, v in zip(md._split(x), plain_split(x)))


def rand_qd(rng, n):
    """quad-doubles as four float64 arrays: random signs and exponents, each part below the previous one's last bit"""
    z0 = (1 + rng.random(n)) * np.exp2(rng.integers(-20, 21, n)) * rng.choice([-1.0, 1.0], n)
    return [z0] + [rng.uniform(-1, 1, n) * np.abs(z0) * 2.0 ** (-53 * k) for k in (1, 2, 3)]


def test_qd_add_dd_exact_to_quad_double():
    """(z0 + z1 + z2 + z3) + (dh + dl) against exact arithmetic, within 2^-205 of the larger operand (a few quad-double
    units), its lanes bitwise its scalar tail (each element alone); control: z3 dropped must miss the bound"""
    rng = np.random.default_rng(5)
    z = rand_qd(rng, N)
    dh, dl = rand_dd(rng, N)
    scale = np.exp2(rng.integers(-60, 1, N))    # steps from the operand's size down to far below it (exact scaling)
    dh, dl = dh * scale, dl * scale

    def worst(parts):
        """largest error of qd_add_dd(parts, d) against the exact sum of z (the true parts) and d"""
        r = md.qd_add_dd(*parts, dh, dl)
        out = 0
        for i in range(N):
            zi = sum(Fraction(p[i]) for p in z)
            want = zi + Fraction(dh[i]) + Fraction(dl[i])
            got = sum(Fraction(p[i]) for p in r)
            out = max(out, abs(got - want) / max(abs(zi), abs(Fraction(dh[i]) + Fraction(dl[i]))))
        return out, r

    w, r = worst(z)
    assert w <= Fraction(1, 2**205), float(w)
    for i in (0, 7, 8, 500, N - 1):
        one = md.qd_add_dd(*[np.array([p[i]]) for p in z], np.array([dh[i]]), np.array([dl[i]]))
        assert all(np.array_equal(a, b[i:i + 1]) for a, b in zip(one, r)), i
    wc, _ = worst(z[:3] + [np.zeros(N)])        # control: a wrong input, graded against the true sum
    assert wc > Fraction(1, 2**205), float(wc)


def test_gcr_refines_an_f64_solve_to_double_double():
    """A x = b with A of order 40 (float64 entries, a diagonal shift) and x a random double-double vector, b = A x and
    every product A u exact (mpmath at 60 digits, rounded to double-double), the preconditioner the f64 solve: gcr gives
    x back to 1e-29 relative and reports convergence, also with an inexact preconditioner. Controls: its first iterate,
    the plain preconditioned solve, is only f64-accurate; with every product off by 1e-20 relative the error stays
    above 1e-27; with f64 coefficients (coef="f64") above 1e-20."""
    import mpmath as mp

    mp.mp.dps = 60
    rng = np.random.default_rng(9)
    n = 40
    A = rng.standard_normal((n, n)) + 8 * np.eye(n)
    Am = [[mp.mpf(v) for v in row] for row in A]
    xh, xl = rand_dd(rng, n, emax=2)

    def mat(v, eps=0):
        return [mp.fsum(Am[i][j] * v[j] for j in range(n)) * (1 + eps) for i in range(n)]

    def to_mp(h, l):
        return [mp.mpf(a) + mp.mpf(b) for a, b in zip(h, l)]

    bh, bl = md.dd_from_mp(mat(to_mp(xh, xl)))

    def precond(rh, rl):
        return np.linalg.solve(A, rh + rl), np.zeros(n)

    _, _, info = md.gcr(lambda uh, ul: md.dd_from_mp(mat(to_mp(uh, ul))), precond, bh, bl, ref=(xh, xl))
    err = info["errors"][-1]
    assert info["converged"] and err <= 1e-29, (err, info["products"])
    assert info["errors"][0] > 1e-20, info["errors"][0]
    # an inexact preconditioner (A perturbed by 1e-3): more products, the same accuracy
    Ap = A + 1e-3 * rng.standard_normal((n, n))
    _, _, slow = md.gcr(lambda uh, ul: md.dd_from_mp(mat(to_mp(uh, ul))),
                        lambda rh, rl: (np.linalg.solve(Ap, rh + rl), np.zeros(n)), bh, bl, ref=(xh, xl))
    assert slow["converged"] and slow["products"] > info["products"] and slow["errors"][-1] <= 1e-29, \
        (slow["errors"][-1], slow["products"])
    _, _, bad = md.gcr(lambda uh, ul: md.dd_from_mp(mat(to_mp(uh, ul), eps=mp.mpf("1e-20"))), precond, bh, bl,
                       ref=(xh, xl))
    assert bad["errors"][-1] > 1e-27, bad["errors"][-1]
    # f64 coefficients (the original form) stall near f64 accuracy relative to b
    _, _, f64c = md.gcr(lambda uh, ul: md.dd_from_mp(mat(to_mp(uh, ul))), precond, bh, bl, ref=(xh, xl), coef="f64",
                        max_products=10)
    assert f64c["errors"][-1] > 1e-20, f64c["errors"][-1]


def _dd_of(xs):
    """the double-double parts of exact rationals"""
    hi = np.array([float(x) for x in xs])
    return hi, np.array([float(x - Fraction(h)) for x, h in zip(xs, hi)])


def _dense_gcr(A, b, M=None, nu=0.9, coef="dd"):
    """gcr on the f64 matrix A with b, preconditioned by the f64 matrix M (the identity by default), every product
    exact (fractions) and rounded to double-double: (x as exact rationals, info)"""
    n = len(b)
    M = np.eye(n) if M is None else np.asarray(M, dtype=float)

    def mul(Q):
        def f(uh, ul):
            u = [Fraction(a) + Fraction(c) for a, c in zip(uh, ul)]
            return _dd_of([sum(Fraction(q) * v for q, v in zip(row, u)) for row in np.asarray(Q, dtype=float)])
        return f

    bh, bl = _dd_of([Fraction(v) for v in b])
    xh, xl, info = md.gcr(mul(A), mul(M), bh, bl, nu=nu, coef=coef)
    return [Fraction(a) + Fraction(c) for a, c in zip(xh, xl)], info


def _shift(n, sign):
    """the cyclic shift of size n, A e_j = e_(j+1) and A e_(n-1) = sign e_0"""
    A = np.zeros((n, n))
    for j in range(n - 1):
        A[j + 1, j] = 1.0
    A[0, n - 1] = sign
    return A


@pytest.mark.parametrize("coef", ["dd", "f64"])
def test_gcr_does_not_break_down_where_gmres_stagnates(coef):
    """On the rotation [[0, -1], [1, 0]] with b = e_0, where GMRES stagnates at its first step, and on the cyclic shift
    of size 6 with b = e_0, where it stagnates for five, gcr returns the solution sign e_(n-1) exactly, converged,
    after n products. Control: with nu = inf (the residual directions only) the second direction's image vanishes on
    both, and gcr returns x = 0, not converged."""
    for n, sign in ((2, -1.0), (6, 1.0)):
        b = np.eye(n)[0]
        want = [Fraction(sign) if i == n - 1 else Fraction(0) for i in range(n)]
        x, info = _dense_gcr(_shift(n, sign), b, coef=coef)
        assert x == want and info["converged"] and info["products"] == n, (n, x, info)
        x, info = _dense_gcr(_shift(n, sign), b, nu=float("inf"), coef=coef)
        assert x != want and not info["converged"], (n, x, info)


def test_gcr_converges_on_an_exact_residual():
    """With A = I and b = e_0 gcr returns x = e_0, converged, after one product, and with b = 0 it returns x = 0,
    converged, after none. Control: with the singular A = diag(1, 0) and b = e_1 the first direction's image vanishes
    while r is nonzero, and gcr reports no convergence."""
    x, info = _dense_gcr(np.eye(2), [1.0, 0.0])
    assert x == [1, 0] and info["converged"] and info["products"] == 1, (x, info)
    x, info = _dense_gcr(np.eye(2), [0.0, 0.0])
    assert x == [0, 0] and info["converged"] and info["products"] == 0, (x, info)
    _, info = _dense_gcr(np.diag([1.0, 0.0]), [0.0, 1.0])
    assert not info["converged"], info


@pytest.mark.parametrize("coef", ["dd", "f64"])
def test_gcr_does_not_stop_on_a_zero_step_below_the_floor(coef):
    """With d = 2^-110, A = [[1, 0, 0], [0, 0, -d], [0, d, 0]], M^-1 = [[1, 0, 0], [-d, 1, 0], [0, 0, 1]] and
    b = (1, d, 0), the first iteration leaves r = (0, d, 0), far below the rounding floor, with x = (1, 0, 0) off by 1
    along the weak direction, and the second takes a zero step. gcr goes on and returns the solution (1, 0, -1)
    exactly, converged, after three products. Control: with nu = inf (every iteration counts) the zero step ends the
    loop with x = (1, 0, 0)."""
    d = 2.0 ** -110
    A = [[1.0, 0.0, 0.0], [0.0, 0.0, -d], [0.0, d, 0.0]]
    M = [[1.0, 0.0, 0.0], [-d, 1.0, 0.0], [0.0, 0.0, 1.0]]
    want = [1, 0, -1]
    x, info = _dense_gcr(A, [1.0, d, 0.0], M=M, coef=coef)
    assert x == want and info["converged"] and info["products"] == 3, (x, info)
    x, info = _dense_gcr(A, [1.0, d, 0.0], M=M, nu=float("inf"), coef=coef)
    assert x != want, (x, info)


def test_dd_dot_against_exact():
    """dd_dot within 2^-100 of sum |x_i y_i| of the exact sum (fractions); control: the f64 dot product misses that"""
    rng = np.random.default_rng(11)
    xh, xl = rand_dd(rng, N)
    yh, yl = rand_dd(rng, N)
    s, e = md.dd_dot(xh, xl, yh, yl)
    xs, ys = exact(xh, xl), exact(yh, yl)
    want = sum(a * b for a, b in zip(xs, ys))
    size = sum(abs(a * b) for a, b in zip(xs, ys))
    assert abs(Fraction(s) + Fraction(e) - want) / size <= Fraction(1, 2**100)
    f = float((xh + xl) @ (yh + yl))
    assert abs(Fraction(f) - want) / size > Fraction(1, 2**100)


def test_dd_dot_lengths_and_cancellation():
    """dd_dot within its documented (n / 8 + 12) u^2 of sum |x_i y_i| for every length 0..40 (the last block padded)
    and for a sum whose second half cancels the first to about 2^-30 per pair; lists are accepted and mismatched
    lengths are an error. Control: the products of the high parts alone miss the bound."""
    rng = np.random.default_rng(12)
    for n in list(range(41)) + [517]:
        xh, xl = rand_dd(rng, n)
        yh, yl = rand_dd(rng, n)
        if n >= 4 and n % 2 == 0:
            # x_{k + n/2} y_{k + n/2} = -x_k y_k (1 + d), |d| ~ 2^-30, with y repeated
            h = n // 2
            d = 1 + rng.uniform(-1, 1, h) * 2.0**-30
            xh[h:], xl[h:] = -xh[:h] * d, -xl[:h] * d
            yh[h:], yl[h:] = yh[:h], yl[:h]
        xs, ys = exact(xh, xl), exact(yh, yl)
        want = sum((a * b for a, b in zip(xs, ys)), Fraction(0))
        size = sum((abs(a * b) for a, b in zip(xs, ys)), Fraction(0))
        bound = (Fraction(n, 8) + 12) * U2
        s, e = md.dd_dot(list(xh), xl, yh, yl)
        assert s + e == s
        if size == 0:
            assert (s, e) == (0.0, 0.0)
            continue
        err = abs(Fraction(s) + Fraction(e) - want) / size
        assert err <= bound, (n, float(err / U2))
        if n >= 2:
            c, _ = md.dd_dot(xh, np.zeros(n), yh, np.zeros(n))
            assert abs(Fraction(c) - want) / size > bound, n
    with pytest.raises(ValueError):
        md.dd_dot(np.ones(3), np.ones(3), np.ones(4), np.ones(4))


def test_qd_axpy_exact_to_quad_double():
    """y + a x against exact arithmetic, within 2^-205 of the larger of |y| and |a x| (a few quad-double units), its
    lanes bitwise its scalar tail (each element alone); controls: x's second part dropped must miss the bound, and
    unequal lengths raise"""
    rng = np.random.default_rng(6)
    x, y = rand_qd(rng, N), rand_qd(rng, N)
    a = -0.37

    def worst(xp):
        r = md.qd_axpy(a, *xp, *y)
        out = 0
        for i in range(N):
            xi = sum(Fraction(p[i]) for p in x)
            yi = sum(Fraction(p[i]) for p in y)
            want = yi + Fraction(a) * xi
            got = sum(Fraction(p[i]) for p in r)
            out = max(out, abs(got - want) / max(abs(yi), abs(Fraction(a) * xi)))
        return out, r

    w, r = worst(x)
    assert w <= Fraction(1, 2**205), float(w)
    for i in (0, 7, 8, 500, N - 1):
        one = md.qd_axpy(a, *[np.array([p[i]]) for p in x], *[np.array([p[i]]) for p in y])
        assert all(np.array_equal(u, v[i:i + 1]) for u, v in zip(one, r)), i
    wc, _ = worst([x[0], np.zeros(N), x[2], x[3]])
    assert wc > Fraction(1, 2**205), float(wc)
    with pytest.raises(ValueError):
        md.qd_axpy(a, *x, y[0][:-1], y[1], y[2], y[3])


def test_dd_matvec_within_bound():
    """A v (A 37 x 1003, so every row has a scalar tail) against exact arithmetic: each row within (m / 8 + 12) u^2 of
    sum |a_ij v_j|; row i is bitwise dd_dot of that row; controls: one term dropped must miss the bound, and a wrong
    shape raises"""
    rng = np.random.default_rng(7)
    n, m = 37, N
    ah, al = rand_dd(rng, n * m)
    ah, al = ah.reshape(n, m), al.reshape(n, m)
    vh, vl = rand_dd(rng, m)
    yh, yl = md.dd_matvec(ah, al, vh, vl)
    v = exact(vh, vl)
    bound = U2 * (m // 8 + 12)
    for i in range(n):
        row = exact(ah[i], al[i])
        want = sum(r * x for r, x in zip(row, v))
        scale = sum(abs(r * x) for r, x in zip(row, v))
        assert abs(Fraction(yh[i]) + Fraction(yl[i]) - want) <= bound * scale, i
        dh, dl = md.dd_dot(np.ascontiguousarray(ah[i]), np.ascontiguousarray(al[i]), vh, vl)
        assert (dh, dl) == (yh[i], yl[i]), i
    i, j = 3, 500
    wrong = ah.copy()
    wrong[i, j] = 0.0
    wh, wl = md.dd_matvec(wrong, al, vh, vl)
    row = exact(ah[i], al[i])
    want = sum(r * x for r, x in zip(row, v))
    scale = sum(abs(r * x) for r, x in zip(row, v))
    assert abs(Fraction(wh[i]) + Fraction(wl[i]) - want) > bound * scale
    with pytest.raises(ValueError):
        md.dd_matvec(ah, al, vh[:-1], vl[:-1])


def series_at(zh, zl, Zh, Zl, a):
    """the loop dd_horner replaces (choptuik-large-d, hp/anm_run.py): z0 + sum_k z_k a^k by Horner's rule with the
    numpy dd_add and dd_scale, z0 = (zh, zl) and Zh[0], Zl[0] unused"""
    ph, pl = np.array(Zh[-1]), np.array(Zl[-1])
    for k in range(len(Zh) - 2, 0, -1):
        ph, pl = md.dd_add(Zh[k], Zl[k], *md.dd_scale(ph, pl, a))
    return md.dd_add(zh, zl, *md.dd_scale(ph, pl, a))


def rand_series(rng, terms, n):
    """terms coefficient arrays of n double-doubles: (list of hi arrays, list of lo arrays)"""
    c = [rand_dd(rng, n, emax=4) for _ in range(terms)]
    return [h for h, _ in c], [l for _, l in c]


def test_dd_horner_is_the_numpy_horner_loop_bitwise():
    """dd_horner is the numpy Horner loop it replaces (series_at, with dd_add and dd_scale) bit for bit, for 2 to 25
    coefficients of N values (the last 3 in the scalar tail), at points that are not powers of two, a power of two and
    a negative one, from lists of arrays and from (N + 1, n) arrays alike. Control: the same loop with the Rust
    double-double product (md.mul by (a, 0), whose low part is a fused multiply-add) differs in the low bits."""
    rng = np.random.default_rng(21)
    fused_differs = False
    for terms in (2, 3, 8, 25):
        Zh, Zl = rand_series(rng, terms, N)
        for a in (0.4341, -1.37, 0.5, 2.0**-7 * 3):
            got = md.dd_horner(Zh, Zl, a)
            assert same_bits(got, series_at(Zh[0], Zl[0], Zh, Zl, a)), (terms, a)
            assert same_bits(got, md.dd_horner(np.array(Zh), np.array(Zl), a)), (terms, a)
            ph, pl = Zh[-1], Zl[-1]
            for k in range(terms - 2, -1, -1):
                ph, pl = md.add(Zh[k], Zl[k], *md.mul(ph, pl, np.full(N, a), np.zeros(N)))
            fused_differs |= not same_bits(got, (ph, pl))
    assert fused_differs, "control: the fused product gives the same bits"


def test_dd_horner_against_mpmath():
    """dd_horner against the sum in mpmath at 80 digits, for 25 coefficients at a = 0.4341 (not a power of two, so its
    float64 powers are inexact) and a = -0.75: within (N + 2) 2^-104 of sum |c_k a^k|. Control: at 0.4341 the sum
    with float64 powers a**k (each term c_k a**k in double-double, summed in double-double) misses that bound. Seen:
    dd_horner 0.2 and 0.3 units of 2^-104, the float64 powers 2e14 units at 0.4341."""
    import mpmath as mp

    mp.mp.dps = 80
    rng = np.random.default_rng(22)
    terms, n = 25, 40
    bound = (terms + 1) * mp.mpf(2) ** -104

    def worst(h, l, Zh, Zl, a):
        am, out = mp.mpf(a), mp.mpf(0)
        for i in range(n):
            t = [(mp.mpf(Zh[k][i]) + mp.mpf(Zl[k][i])) * am**k for k in range(terms)]
            err = abs(mp.mpf(h[i]) + mp.mpf(l[i]) - mp.fsum(t)) / mp.fsum(abs(x) for x in t)
            out = max(out, err)
        return out

    for a in (0.4341, -0.75):
        Zh, Zl = rand_series(rng, terms, n)
        w = worst(*md.dd_horner(Zh, Zl, a), Zh, Zl, a)
        assert w <= bound, (a, float(w / 2.0**-104))
        if a == 0.4341:
            ph, pl = Zh[0], Zl[0]
            for k in range(1, terms):
                ph, pl = md.dd_add(ph, pl, *md.dd_scale(Zh[k], Zl[k], a**k))
            wc = worst(ph, pl, Zh, Zl, a)
            assert wc > bound, float(wc / 2.0**-104)


def test_dd_horner_edge_cases():
    """one coefficient gives c_0 back, a = 0 gives c_0 (as the loop does), empty coefficient arrays give empty sums,
    and the lanes agree with the scalar tail (each value alone); no coefficients, coefficient arrays of different
    lengths, ch and cl of different shapes and a 1-D ch raise ValueError"""
    rng = np.random.default_rng(23)
    Zh, Zl = rand_series(rng, 6, N)
    assert same_bits(md.dd_horner(Zh[:1], Zl[:1], 0.3), (Zh[0], Zl[0]))
    got = md.dd_horner(Zh, Zl, 0.0)
    assert same_bits(got, (Zh[0], Zl[0])) and same_bits(got, series_at(Zh[0], Zl[0], Zh, Zl, 0.0))
    assert same_bits(md.dd_horner(np.zeros((3, 0)), np.zeros((3, 0)), 0.3), (np.zeros(0), np.zeros(0)))
    full = md.dd_horner(Zh, Zl, 0.4341)
    for i in (0, 7, 8, 500, N - 1):
        one = md.dd_horner([h[i:i + 1] for h in Zh], [l[i:i + 1] for l in Zl], 0.4341)
        assert same_bits(one, (full[0][i:i + 1], full[1][i:i + 1])), i
    for ch, cl in ((np.zeros((0, 4)), np.zeros((0, 4))),
                   ([np.ones(4), np.ones(5)], [np.zeros(4), np.zeros(5)]),
                   (np.ones((3, 4)), np.zeros((3, 5))),
                   (np.ones(4), np.zeros(4))):
        with pytest.raises(ValueError):
            md.dd_horner(ch, cl, 0.5)


UQ = 2.0**-209  # QD::EPS, the quad-double unit
MP_DPS = 150  # the reference arithmetic: a quad-double is exact in about 80 digits, a product of two in 160


def qd_mp(parts):
    """the exact values of a quad-double array (four part arrays of one shape), as an mpmath matrix (2-D) or list"""
    import mpmath as mp

    with mp.workdps(MP_DPS):
        p = [np.asarray(x, dtype=np.float64) for x in parts]
        if p[0].ndim == 2:
            return mp.matrix([[mp.fsum(mp.mpf(float(x[i, j])) for x in p) for j in range(p[0].shape[1])]
                              for i in range(p[0].shape[0])])
        return [mp.fsum(mp.mpf(float(x[i])) for x in p) for i in range(len(p[0]))]


def mp_parts(vals):
    """mpmath numbers rounded to quad-double greedily (each part the nearest float64 to what is left): four arrays"""
    import mpmath as mp

    out = [np.zeros(len(vals)) for _ in range(4)]
    with mp.workdps(MP_DPS):
        for i, v in enumerate(vals):
            r = v
            for q in range(4):
                out[q][i] = float(r)
                r = r - mp.mpf(out[q][i])
    return out


def ill_conditioned(n, cond, seed):
    """A = H1 D H2 rounded to quad-double, H1, H2 Householder reflectors and D = diag(cond^(-k / (n - 1))), so that the
    2-norm condition number is cond (to the rounding of A): four (n, n) part arrays"""
    import mpmath as mp

    rng = np.random.default_rng(seed)
    with mp.workdps(MP_DPS):
        def refl():
            v = [mp.mpf(float(x)) for x in rng.standard_normal(n)]
            vv = mp.fsum(x * x for x in v)
            return mp.matrix([[(1 if i == j else 0) - 2 * v[i] * v[j] / vv for j in range(n)] for i in range(n)])
        d = [mp.mpf(cond) ** (-mp.mpf(k) / (n - 1)) for k in range(n)]
        A = refl() * mp.diag(d) * refl()
        flat = mp_parts([A[i, j] for i in range(n) for j in range(n)])
    return [x.reshape(n, n) for x in flat]


def planted_rhs(parts, rng, k=None):
    """b = A x rounded to quad-double for a planted x of unit size (k columns, or a vector when k is None), formed in
    mpmath from A's exact entries: four part arrays"""
    import mpmath as mp

    A, n = qd_mp(parts), parts[0].shape[0]
    cols = []
    with mp.workdps(MP_DPS):
        for _ in range(1 if k is None else k):
            x = [mp.mpf(float(v)) for v in rng.standard_normal(n)]
            cols.append(mp_parts([mp.fsum(A[i, j] * x[j] for j in range(n)) for i in range(n)]))
    if k is None:
        return cols[0]
    return [np.stack([c[q] for c in cols], axis=1) for q in range(4)]


def qd_errors(parts, bparts, xparts, transpose=False):
    """(forward, backward) error of x against A x = b (A^T x = b when transpose), in mpmath at MP_DPS digits, b of
    shape (n,) or (n, k): forward max |x - x*| / max |x*| over each column (x* = mpmath's solve of the system as given,
    to about cond 10^-MP_DPS), backward the componentwise max |b - A x| / (|A| |x| + |b|)"""
    import mpmath as mp

    A = qd_mp(parts)
    if transpose:
        A = A.T
    n = A.rows
    b2 = [np.asarray(p, dtype=np.float64).reshape(n, -1) for p in bparts]
    x2 = [np.asarray(p, dtype=np.float64).reshape(n, -1) for p in xparts]
    fwd = bwd = 0
    with mp.workdps(MP_DPS):
        for c in range(b2[0].shape[1]):
            b = qd_mp([p[:, c] for p in b2])
            x = qd_mp([p[:, c] for p in x2])
            ref = mp.lu_solve(A, mp.matrix(b))
            fwd = max(fwd, max(abs(x[i] - ref[i]) for i in range(n)) / max(abs(ref[i]) for i in range(n)))
            for i in range(n):
                r = b[i] - mp.fsum(A[i, j] * x[j] for j in range(n))
                s = mp.fsum(abs(A[i, j] * x[j]) for j in range(n)) + abs(b[i])
                bwd = max(bwd, abs(r) / s)
    return float(fwd), float(bwd)


@pytest.mark.parametrize("n", [24, 37])
@pytest.mark.parametrize("cond", [1.0, 1e10, 1e20])
def test_qd_solve_error_scales_with_the_condition(n, cond):
    """x of qd_solve for A of condition 1, 1e10 and 1e20 (n = 24, and 37 with a partial last row block) and a planted
    x of unit size: the backward error within n 2^-209 and the forward error within n cond 2^-209 (partial pivoting
    is backward stable; the error is about cond(A) 2^-209), against mpmath at 150 digits. Control: the last part of
    one entry of A dropped (2^-159 of it), x graded against the true system, misses the forward bound."""
    parts = ill_conditioned(n, cond, seed=n + int(np.log10(cond)))
    b = planted_rhs(parts, np.random.default_rng(n))
    x = md.qd_solve(*parts, *b)
    fwd, bwd = qd_errors(parts, b, x)
    print(f"n {n} cond {cond:.0e}: forward {fwd:.2e} ({fwd / (cond * UQ):.2e} cond u), backward {bwd / UQ:.3f} u")
    assert bwd <= n * UQ, bwd / UQ
    assert fwd <= n * cond * UQ, fwd / (cond * UQ)
    i, j = 3, n - 2
    assert parts[3][i, j] != 0
    wrong = [p.copy() for p in parts]
    wrong[3][i, j] = 0.0
    fc, _ = qd_errors(parts, b, md.qd_solve(*wrong, *b))
    assert fc > n * cond * UQ, fc / (cond * UQ)


def test_qd_solve_residual_control():
    """control for the backward error check: a solution off by 2^-190 of its size in one entry misses n 2^-209"""
    n = 24
    parts = ill_conditioned(n, 1e5, seed=3)
    b = planted_rhs(parts, np.random.default_rng(4))
    x = [p.copy() for p in md.qd_solve(*parts, *b)]
    assert qd_errors(parts, b, x)[1] <= n * UQ
    x[3][7] += 2.0**-190 * x[0][7]
    assert qd_errors(parts, b, x)[1] > n * UQ


def test_qd_lu_solves_many_right_hand_sides_and_the_transpose():
    """QDLu factored once: solve gives qd_solve's bits for one right-hand side and for k = 3 at once (each column the
    bits of its own solve), and A x = b and A^T x = b at cond 1e20 to the bounds of the single solve. Controls: a solve
    of a b with one bit changed gives other bits, and the transposed solve graded as A x = b misses the bound."""
    n, cond = 37, 1e20
    parts = ill_conditioned(n, cond, seed=11)
    rng = np.random.default_rng(12)
    B = planted_rhs(parts, rng, k=3)
    lu = md.QDLu(*parts)
    assert lu.n == n
    X = lu.solve(*B)
    assert [p.shape for p in X] == [(n, 3)] * 4
    assert same_bits(X, md.qd_solve(*parts, *B))
    for c in range(3):
        col = [np.ascontiguousarray(p[:, c]) for p in B]
        assert same_bits(lu.solve(*col), [p[:, c] for p in X]), c
        assert same_bits(md.qd_solve(*parts, *col), [p[:, c] for p in X]), c
    fwd, bwd = qd_errors(parts, B, X)
    assert bwd <= n * UQ and fwd <= n * cond * UQ, (bwd / UQ, fwd / (cond * UQ))
    T = lu.solve(*B, transpose=True)
    fwd, bwd = qd_errors(parts, B, T, transpose=True)
    print(f"transpose: forward {fwd / (cond * UQ):.2e} cond u, backward {bwd / UQ:.3f} u")
    assert bwd <= n * UQ and fwd <= n * cond * UQ, (bwd / UQ, fwd / (cond * UQ))
    assert qd_errors(parts, B, T)[1] > n * UQ
    flip = [p.copy() for p in B]
    flip[1][5, 1] = np.nextafter(flip[1][5, 1], np.inf)
    assert not same_bits(lu.solve(*flip), X)


def pinned_part(i, j, q):
    """part q of entry (i, j) of the pinned system's matrix, or of entry i of b when j is None: `pinned_part` of the
    Rust test qd_lu_pinned_bits (tests/linalg.rs), small integers over powers of two, exact in float64"""
    scale = (2.0**-7, 2.0**-58, 2.0**-113, 2.0**-168)[q]
    if j is None:
        t = (i * 29 + q * 71) % 199 - 99
    else:
        t = (i * 37 + j * 101 + q * 53 + i * j * 7) % 211 - 105 + (64 if q == 0 and i == j else 0)
    return t * scale


def pinned_system(n=37):
    """the four part arrays of the pinned A ((n, n), entry (i, j) at [i, j]) and of b (n)"""
    A = [np.array([[pinned_part(i, j, q) for j in range(n)] for i in range(n)]) for q in range(4)]
    b = [np.array([pinned_part(i, None, q) for i in range(n)]) for q in range(4)]
    return A, b


def parts_hash(x):
    """FNV-1a over the bits of the four parts, all of part 0 first, as parts_hash of tests/linalg.rs"""
    h = 0xCBF29CE484222325
    for p in x:
        for w in np.ascontiguousarray(p, dtype=np.float64).ravel().view(np.uint64):
            h = ((h ^ int(w)) * 0x100000001B3) & 0xFFFFFFFFFFFFFFFF
    return h


PINNED = (0x90714C6EBACC4705, 0xE34A230E39E22035)  # tests/linalg.rs, qd_lu_pinned_bits: A x = b and A^T x = b


def test_qd_solve_is_the_rust_lu_bitwise():
    """qd_solve and QDLu.solve (and its transpose) of the pinned system give the bits of the Rust QDLu called directly
    (tests/linalg.rs pins the same hashes), with the parts renormalized as QD::new does. Control: b with one bit
    changed in a second part gives another hash."""
    A, b = pinned_system()
    x = md.qd_solve(*A, *b)
    assert parts_hash(x) == PINNED[0], hex(parts_hash(x))
    lu = md.QDLu(*A)
    assert parts_hash(lu.solve(*b)) == PINNED[0]
    assert parts_hash(lu.solve(*b, transpose=True)) == PINNED[1]
    c = [p.copy() for p in b]
    c[1][5] = np.nextafter(c[1][5], np.inf)
    assert parts_hash(md.qd_solve(*A, *c)) != PINNED[0]


def test_qd_solve_renormalizes_its_inputs():
    """parts that are not normalized are renormalized first: A and b given as (0, x0, x1, x2), the same values with a
    zero leading part, which the pivot search and the zero-skips read, solve to the bounds (unnormalized, every
    leading part would read as zero and the factorization would raise as singular), for A x = b and A^T x = b by
    QDLu and for qd_solve. Control: each of those solutions off by 2^-190 of its size in one entry misses the backward
    bound."""
    n = 13
    A, b = pinned_system(n)
    A[3][:], b[3][:] = 0.0, 0.0  # three parts, so that the shift keeps the values exactly
    shift = lambda p: [np.zeros_like(p[0]), p[0], p[1], p[2]]  # noqa: E731
    cond = np.linalg.cond(A[0])  # in float64, enough for a bound
    for t in (False, True):
        x = md.QDLu(*shift(A)).solve(*shift(b), transpose=t)
        fwd, bwd = qd_errors(A, b, x, transpose=t)
        assert bwd <= n * UQ and fwd <= n * cond * UQ, (bwd / UQ, fwd / (cond * UQ))
        wrong = [p.copy() for p in x]
        wrong[3][5] += 2.0**-190 * wrong[0][5]
        assert qd_errors(A, b, wrong, transpose=t)[1] > n * UQ
    x = [p.copy() for p in md.qd_solve(*shift(A), *shift(b))]
    assert qd_errors(A, b, x)[1] <= n * UQ
    x[3][5] += 2.0**-190 * x[0][5]
    assert qd_errors(A, b, x)[1] > n * UQ


def test_qd_inputs_in_any_order():
    """qd_solve, QDLu and qd_add_dd take each entry as the exact sum of its four parts in any order (QD::from_sum).
    The 1 x 1 matrix (1, 1e16, -1, -1e16), whose sum is zero, raises as singular; summed in QD::new's order it read
    as 1. The pinned system with every entry's parts permuted, and its double-double rounding written as (B, x0, -B,
    x1) with B 2^60 above x0, solve to the backward and forward bounds of the true values, for A x = b and A^T x = b by
    QDLu and for qd_solve; a permutation changes the representation, so the bits may differ. qd_add_dd of permuted
    parts is within 2^-205 of the exact sum on its lanes and its scalar tail. Controls: a solution off by 2^-190 of its
    size in one entry misses the backward bound, and qd_add_dd with z3 dropped misses its bound."""
    one = lambda v: np.array([[v]])  # noqa: E731
    with pytest.raises(ValueError, match="singular"):
        md.qd_solve(one(1.0), one(1e16), one(-1.0), one(-1e16), *[np.ones(1)] * 4)
    n = 13
    A, b = pinned_system(n)
    perm = (2, 0, 3, 1)
    shuffled = lambda p: [p[q] for q in perm]  # noqa: E731
    A2 = [A[0], A[1], np.zeros_like(A[0]), np.zeros_like(A[0])]
    big = np.exp2(np.floor(np.log2(np.abs(A[0]) + 1e-300)) + 60)
    cases = [(A, shuffled(A), shuffled(b)), (A2, [big, A[0], -big, A[1]], b)]
    for true_A, given_A, given_b in cases:
        cond = np.linalg.cond(true_A[0])  # in float64, enough for a bound
        for t in (False, True):
            x = md.QDLu(*given_A).solve(*given_b, transpose=t)
            fwd, bwd = qd_errors(true_A, b, x, transpose=t)
            assert bwd <= n * UQ and fwd <= n * cond * UQ, (bwd / UQ, fwd / (cond * UQ))
        x = [p.copy() for p in md.qd_solve(*given_A, *given_b)]
        assert qd_errors(true_A, b, x)[1] <= n * UQ
        x[3][5] += 2.0**-190 * x[0][5]
        assert qd_errors(true_A, b, x)[1] > n * UQ
    rng = np.random.default_rng(13)
    m = 11  # 8 lanes and a scalar tail of 3
    z = rand_qd(rng, m)
    dh, dl = rand_dd(rng, m)

    def worst(parts):
        """largest error of qd_add_dd(parts, d) against the exact sum of z (the true parts) and d"""
        r = md.qd_add_dd(*parts, dh, dl)
        out = 0
        for i in range(m):
            zi = sum(Fraction(p[i]) for p in z)
            want = zi + Fraction(dh[i]) + Fraction(dl[i])
            got = sum(Fraction(p[i]) for p in r)
            out = max(out, abs(got - want) / max(abs(zi), abs(Fraction(dh[i]) + Fraction(dl[i]))))
        return out

    assert worst(shuffled(z)) <= Fraction(1, 2**205)
    assert worst(shuffled(z[:3] + [np.zeros(m)])) > Fraction(1, 2**205)


def test_qd_solve_errors():
    """singular A (an exactly zero pivot), entries that are not finite in any part of A or b, and mismatched shapes
    raise ValueError, as dd_solve does for a singular A; QDLu raises the same"""
    n = 5
    A, b = pinned_system(n)
    z = [np.zeros((n, n))] * 4
    with pytest.raises(ValueError, match="singular"):
        md.qd_solve(*z, *b)
    with pytest.raises(ValueError, match="singular"):
        md.dd_solve(z[0], z[1], b[0], b[1])
    twin = [p.copy() for p in A]
    for p in twin:
        p[3] = p[1]  # two equal rows
    with pytest.raises(ValueError, match="singular"):
        md.qd_solve(*twin, *b)
    with pytest.raises(ValueError, match="singular"):
        md.QDLu(*twin)
    for q in range(4):
        for bad in (np.nan, np.inf, -np.inf):
            a = [p.copy() for p in A]
            a[q][2, 3] = bad
            with pytest.raises(ValueError, match=r"A has a non-finite entry at \(2, 3\)"):
                md.qd_solve(*a, *b)
            with pytest.raises(ValueError, match="non-finite"):
                md.QDLu(*a)
            c = [p.copy() for p in b]
            c[q][4] = bad
            with pytest.raises(ValueError, match="b has a non-finite entry at 4"):
                md.qd_solve(*A, *c)
            with pytest.raises(ValueError, match="non-finite"):
                md.QDLu(*A).solve(*c)
    big = [np.full((n, n), 1e308), np.full((n, n), 1e308), z[0], z[0]]  # finite parts whose sum overflows
    with pytest.raises(ValueError, match="non-finite"):
        md.qd_solve(*big, *b)
    with pytest.raises(ValueError):
        md.qd_solve(A[0][:, :4], A[1][:, :4], A[2][:, :4], A[3][:, :4], *b)  # not square
    with pytest.raises(ValueError):
        md.qd_solve(A[0], A[1], A[2], A[3][:4, :4], *b)  # the parts of A differ in shape
    with pytest.raises(ValueError):
        md.qd_solve(*A, b[0][:4], b[1][:4], b[2][:4], b[3][:4])  # b too short
    with pytest.raises(ValueError):
        md.qd_solve(*A, b[0], b[1], b[2], b[3][:4])  # the parts of b differ in shape
    with pytest.raises(ValueError):
        md.QDLu(*A).solve(*[p.reshape(n, 1, 1) for p in b])  # three-dimensional
    with pytest.raises(TypeError):
        md.qd_solve(A[0][0], A[1][0], A[2][0], A[3][0], *b)  # A one-dimensional
    e = [np.zeros((0, 0))] * 4
    assert [p.shape for p in md.qd_solve(*e, *[np.zeros(0)] * 4)] == [(0,)] * 4
    assert [p.shape for p in md.QDLu(*A).solve(*[np.zeros((n, 0))] * 4)] == [(n, 0)] * 4


def test_qd_lu_inputs_are_converted():
    """QDLu's matrix and right-hand sides (k = 2, so b is 2-D too) as strided or reversed views, in Fortran order, as
    integers, float32 or lists give the bits of the call with np.ascontiguousarray(x, dtype=np.float64). Control: the
    Rust class itself raises on each of these inputs, Fortran order included."""
    rng = np.random.default_rng(41)
    n = 6
    A = conversion_cases()["qd_solve"][:4]
    B = [np.stack([p, p[::-1]], axis=1) for p in rand_qd(rng, n)]
    want_lu = md.QDLu(*A)
    for i in range(4):
        for kind, v in variants(A[i]).items():
            a = list(A)
            a[i] = v
            w = list(A)
            w[i] = np.ascontiguousarray(v, dtype=np.float64)
            assert same_bits(md.QDLu(*a).solve(*B), md.QDLu(*w).solve(*B)), (i, kind)
            with pytest.raises((TypeError, ValueError)):
                md._md.QDLu(*a)
        for kind, v in variants(B[i]).items():
            c = list(B)
            c[i] = v
            w = list(B)
            w[i] = np.ascontiguousarray(v, dtype=np.float64)
            assert same_bits(want_lu.solve(*c), want_lu.solve(*w)), (i, kind)
            assert same_bits(want_lu.solve(*c, transpose=True), want_lu.solve(*w, transpose=True)), (i, kind)
            with pytest.raises((TypeError, ValueError)):
                want_lu._lu.solve(*c)


def conversion_cases():
    """every array function of the package with valid arguments, all arrays C-contiguous float64: name -> arguments"""
    rng = np.random.default_rng(31)
    n = 21
    ah, al = rand_dd(rng, n)
    bh, bl = rand_dd(rng, n)
    Ah, Al = (x.reshape(3, 7) for x in rand_dd(rng, 21))
    Sh, Sl = (x.reshape(6, 6) for x in rand_dd(rng, 36, emax=2))
    Sh = Sh + 16 * np.eye(6)
    z, y = rand_qd(rng, n), rand_qd(rng, n)
    # octo-double arrays: the quad-double parts and four zero parts, each its own array
    oz, oy = (*z, *(np.zeros(n) for _ in range(4))), (*y, *(np.zeros(n) for _ in range(4)))
    Ch, Cl = (np.array(c) for c in rand_series(rng, 5, n))
    Q = [Sh, Sl, Sl * 2.0**-53 * rng.uniform(-1, 1, (6, 6)), Sl * 2.0**-106 * rng.uniform(-1, 1, (6, 6))]
    two = (ah, al, bh, bl)
    return {
        "add": two, "sub": two, "mul": two, "div": two, "dd_op": (1,) + two, "dd_dot": two,
        "dd_matvec": (Ah, Al, bh[:7], bl[:7]), "dd_solve": (Sh, Sl, bh[:6], bl[:6]),
        "qd_add_dd": (*z, bh, bl), "qd_axpy": (0.37, *z, *y), "dd_horner": (Ch, Cl, 0.4341),
        "od_add_dd": (*oz, bh, bl), "od_axpy": (0.37, *oz, *oy),
        "qd_solve": (*Q, *[p[:6] for p in z]),
    }


def same_bits(x, y):
    """two results (tuples of arrays or of floats) with the same bits, NaNs included"""
    bx = [np.asarray(o, dtype=np.float64).view(np.uint64) for o in x]
    by = [np.asarray(o, dtype=np.float64).view(np.uint64) for o in y]
    return len(bx) == len(by) and all(a.shape == b.shape and np.array_equal(a, b) for a, b in zip(bx, by))


def variants(x):
    """inputs with x's values (or values derived from them) that are not C-contiguous float64 arrays: a strided view,
    a view in reverse order, Fortran order (2-D), integers, float32 and a nested list"""
    s = np.zeros(x.shape[:-1] + (2 * x.shape[-1],))
    s[..., ::2] = x
    out = {"strided": s[..., ::2], "reversed": x[::-1].copy()[::-1], "int64": np.rint(x * 1024).astype(np.int64),
           "float32": x.astype(np.float32), "list": x.tolist()}
    if x.ndim == 2:
        out["fortran"] = np.asfortranarray(x)
    return out


NAMES = list(conversion_cases())


@pytest.mark.parametrize("name", NAMES)
def test_array_inputs_are_converted(name):
    """each array argument of each function given as a strided or reversed view, in Fortran order, as integers, as
    float32 or as a list gives the bits of the same call with np.ascontiguousarray(x, dtype=np.float64). Control: the
    Rust binding itself raises on each of these inputs, a Fortran-ordered matrix included, so the conversion is what
    makes them pass."""
    args = conversion_cases()[name]
    f, raw = getattr(md, name), getattr(md._md, name)
    for i, x in enumerate(args):
        if not isinstance(x, np.ndarray):
            continue
        for kind, v in variants(x).items():
            a = list(args)
            a[i] = v
            want = list(args)
            want[i] = np.ascontiguousarray(v, dtype=np.float64)
            assert same_bits(f(*a), f(*want)), (name, i, kind)
            with pytest.raises((TypeError, ValueError)):
                raw(*a)


@pytest.mark.parametrize("name", NAMES)
def test_contiguous_float64_inputs_pass_through(name, monkeypatch):
    """a C-contiguous float64 array reaches the Rust binding as the same object, not a copy, and the result is the
    binding's own bit for bit"""
    args = conversion_cases()[name]
    raw = getattr(md._md, name)
    seen = []

    def spy(*a):
        seen.extend(a)
        return raw(*a)

    monkeypatch.setattr(md._md, name, spy)
    got = getattr(md, name)(*args)
    assert len(seen) == len(args)
    assert all(s is x for s, x in zip(seen, args) if isinstance(x, np.ndarray))
    assert same_bits(got, raw(*args))


def test_control_unconverted_inputs_fail(monkeypatch):
    """control: with the conversion replaced by the identity, every function raises on a strided view"""
    monkeypatch.setattr(md, "_f64", lambda v, name: v)
    for name, args in conversion_cases().items():
        a = list(args)
        i = next(i for i, x in enumerate(a) if isinstance(x, np.ndarray))
        a[i] = variants(a[i])["strided"]
        with pytest.raises((TypeError, ValueError)):
            getattr(md, name)(*a)


@pytest.mark.parametrize("bad", [None, ["1.5", "2"], np.array(["1.5", "2"], dtype=object), [1.0, None],
                                 np.array([1 + 2j, 3j]), [object(), object()]],
                         ids=["None", "strings", "object strings", "a None", "complex", "objects"])
def test_non_numeric_inputs_raise(bad):
    """None, strings (also in an object array), complex numbers and other objects in an array argument raise TypeError
    naming it, where numpy's float64 conversion would give nan, parse the strings or drop the imaginary parts"""
    for name, args in conversion_cases().items():
        a = list(args)
        i = next(i for i, x in enumerate(a) if isinstance(x, np.ndarray))
        a[i] = bad
        with pytest.raises(TypeError, match="must be real numbers"):
            getattr(md, name)(*a)


def test_masked_values_raise():
    """a masked array with a masked value raises TypeError, where np.asarray would pass the hidden value on, and so
    does a list holding one (a 2-D argument as a list of rows, one of them masked, or a 1-D one with np.ma.masked as
    an element) and an object array holding np.ma.masked; a masked array with nothing masked gives the bits of its
    data"""
    for name, args in conversion_cases().items():
        f, a = getattr(md, name), list(args)
        i = next(i for i, x in enumerate(a) if isinstance(x, np.ndarray))
        m = np.zeros(args[i].shape, dtype=bool)
        m.flat[1] = True
        a[i] = np.ma.masked_array(args[i], mask=m)
        with pytest.raises(TypeError, match="must not have masked values"):
            f(*a)
        x = args[i]
        if x.ndim == 2:
            a[i] = [np.ma.masked_array(r, mask=k) for r, k in zip(x, m)]
        else:
            a[i] = [x[0], np.ma.masked, *x[2:]]
        with pytest.raises(TypeError, match="must not have masked values"):
            f(*a)
        if x.ndim == 1:
            a[i] = np.array([x[0], np.ma.masked, *x[2:]], dtype=object)
            with pytest.raises(TypeError, match="must not have masked values"):
                f(*a)
        a[i] = np.ma.masked_array(args[i])
        assert same_bits(f(*a), f(*args)), name
