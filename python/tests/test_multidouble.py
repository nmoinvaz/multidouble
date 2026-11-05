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
    Ch, Cl = (np.array(c) for c in rand_series(rng, 5, n))
    two = (ah, al, bh, bl)
    return {
        "add": two, "sub": two, "mul": two, "div": two, "dd_op": (1,) + two, "dd_dot": two,
        "dd_matvec": (Ah, Al, bh[:7], bl[:7]), "dd_solve": (Sh, Sl, bh[:6], bl[:6]),
        "qd_add_dd": (*z, bh, bl), "qd_axpy": (0.37, *z, *y), "dd_horner": (Ch, Cl, 0.4341),
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


@pytest.mark.parametrize("bad", [None, ["1.5", "2"], np.array([1 + 2j, 3j]), [object(), object()]],
                         ids=["None", "strings", "complex", "objects"])
def test_non_numeric_inputs_raise(bad):
    """None, strings, complex numbers and other objects in an array argument raise TypeError naming it, where numpy's
    float64 conversion would give nan, parse the strings or drop the imaginary parts"""
    for name, args in conversion_cases().items():
        a = list(args)
        i = next(i for i, x in enumerate(a) if isinstance(x, np.ndarray))
        a[i] = bad
        with pytest.raises(TypeError, match="must be real numbers"):
            getattr(md, name)(*a)
