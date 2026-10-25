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
