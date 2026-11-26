"""Tests of DDLu, the double-double LU kept for several solves, against mpmath at 60 digits (about 200 bits, more than
the 106 of two parts) and against dd_solve bit for bit, with controls that feed the same checks a wrong result."""
import numpy as np
import pytest

import multidouble as md

mp = pytest.importorskip("mpmath")
EPS = 2.0**-104


def split2(v):
    """the two parts of an mpmath number: hi the nearest float64, lo the nearest float64 to the rest"""
    h = float(v)
    return h, float(v - h)


def to_parts(M):
    """an mpmath matrix (or vector, as a list) as hi and lo float64 arrays"""
    if isinstance(M, list):
        p = [split2(v) for v in M]
        return [np.array([e[q] for e in p]) for q in range(2)]
    n, m = M.rows, M.cols
    p = [[split2(M[i, j]) for j in range(m)] for i in range(n)]
    return [np.array([[p[i][j][q] for j in range(m)] for i in range(n)]) for q in range(2)]


def from_parts(x):
    """hi and lo arrays of shape (n,) as a list of mpmath numbers (their exact sums)"""
    return [mp.mpf(float(x[0][i])) + mp.mpf(float(x[1][i])) for i in range(len(x[0]))]


def reflector(rng, n):
    """a Householder reflector I - 2 v v^T / v^T v of order n in mpmath, v from rng"""
    v = mp.matrix([mp.mpf(float(t)) for t in rng.uniform(-1, 1, n)])
    vv = sum(t * t for t in v)
    return mp.eye(n) - (v * v.T) * (2 / vv)


def system(rng, n, p):
    """A = H1 D H2 with D = diag(10^(-p i / (n - 1))), condition 10^p, rounded to two parts entrywise, a planted x of
    two parts and b = A x rounded to two parts, all in mpmath"""
    d = mp.diag([mp.mpf(10) ** (-mp.mpf(p) * k / (n - 1)) for k in range(n)])
    A = reflector(rng, n) * d * reflector(rng, n)
    Ap = to_parts(A)
    A = mp.matrix([[mp.mpf(float(Ap[0][i, j])) + mp.mpf(float(Ap[1][i, j])) for j in range(n)] for i in range(n)])
    xp = [np.array(rng.uniform(-1, 1, n)), np.array(rng.uniform(-1, 1, n)) * 2.0**-53]
    xp = to_parts(from_parts(xp))
    x = from_parts(xp)
    b = [sum(A[i, j] * x[j] for j in range(n)) for i in range(n)]
    return A, Ap, x, to_parts(b)


def errors(A, x, b, y):
    """max |y - x| / max |x| (forward) and max_i |b_i - (A y)_i| / sum_j |A_ij y_j| (backward), in mpmath"""
    n = len(x)
    yv, bv = from_parts(y), from_parts(b)
    fwd = max(abs(yv[i] - x[i]) for i in range(n)) / max(abs(t) for t in x)
    bwd = max(abs(bv[i] - sum(A[i, j] * yv[j] for j in range(n))) / sum(abs(A[i, j] * yv[j]) for j in range(n))
              for i in range(n))
    return float(fwd), float(bwd)


def bits(*v):
    """the uint64 bit patterns of the arrays v, concatenated"""
    return np.concatenate([np.ascontiguousarray(a, dtype=np.float64).ravel().view(np.uint64) for a in v])


def same(u, v):
    return np.array_equal(bits(*u), bits(*v))


def flip(a, i):
    """a copy of a with the last bit of element i flipped"""
    a = a.copy()
    a.flat[i] = np.frombuffer((np.array([a.flat[i]]).view(np.uint64) ^ 1).tobytes(), dtype=np.float64)[0]
    return a


def test_dd_lu_error_follows_the_condition():
    """DDLu(A).solve of A = H1 D H2 (n = 24, condition 10^p for p = 0, 3, 6, 9), A x = b and A^T x = b: the forward
    error is within cond 2^-100 + 1e-60 of the planted x (b itself carries a rounding of 2^-106 relative, and each
    update one of about 2^-104) and the backward error within n 2^-104. Control: x rounded to its hi parts misses the
    forward bound by more than 1e4."""
    mp.mp.dps = 60
    n = 24
    for p in (0, 3, 6, 9):
        rng = np.random.default_rng(200 + p)
        cond = 10.0**p
        A, Ap, x, b = system(rng, n, p)
        lu = md.DDLu(*Ap)
        assert lu.n == n
        At = A.T
        bt = to_parts([sum(At[i, j] * x[j] for j in range(n)) for i in range(n)])
        bound = 16 * cond * EPS + 1e-60
        for M, rhs, t in ((A, b, False), (At, bt, True)):
            y = lu.solve(*rhs, transpose=t)
            fwd, bwd = errors(M, x, rhs, y)
            assert fwd <= bound, (p, t, fwd, bound)
            assert bwd <= n * EPS, (p, t, bwd)
            fh, _ = errors(M, x, rhs, (y[0], np.zeros(n)))
            assert fh > 1e4 * bound, (p, t, fh)


def test_dd_lu_is_dd_solve_and_solves_many_right_hand_sides():
    """DDLu factored once, unblocked (n = 37) and blocked (n = 100, at least BLOCKED_MIN): solve gives dd_solve's
    bits, and k = 11 right-hand sides at once (two lane groups, the second partial; zeros and negative zeros among the
    entries) give each column the bits of its own solve, for A x = b and A^T x = b, with par and without. Controls:
    b with one bit changed gives other bits, and the transposed solve's residual taken with A instead of A^T misses
    the bound."""
    mp.mp.dps = 60
    rng = np.random.default_rng(11)
    for n in (37, 100):
        A = rng.uniform(-1, 1, (n, n)) + 4 * np.eye(n)
        Ah, Al = md.two_sum(A, rng.uniform(-1, 1, (n, n)) * 2.0**-55)
        bh, bl = md.two_sum(rng.uniform(-1, 1, n), rng.uniform(-1, 1, n) * 2.0**-55)
        lu = md.DDLu(Ah, Al)
        X = md.dd_solve(Ah, Al, bh, bl)
        assert same(lu.solve(bh, bl), X)
        assert same(md.DDLu(Ah, Al, par=True).solve(bh, bl), X)
        assert not same(lu.solve(flip(bh, 3), bl), X)
        k = 11
        Bh, Bl = md.two_sum(rng.uniform(-1, 1, (n, k)), rng.uniform(-1, 1, (n, k)) * 2.0**-55)
        Bh[::7, 2], Bl[::7, 2] = 0.0, 0.0
        Bh[1::5, 9], Bl[1::5, 9] = -0.0, 0.0
        for t in (False, True):
            XB = lu.solve(Bh, Bl, transpose=t)
            assert XB[0].shape == (n, k)
            assert same(lu.solve(Bh, Bl, transpose=t, par=True), XB)
            for c in range(k):
                one = lu.solve(np.ascontiguousarray(Bh[:, c]), np.ascontiguousarray(Bl[:, c]), transpose=t)
                assert same(one, (XB[0][:, c], XB[1][:, c])), (n, t, c)
            assert not same(lu.solve(flip(Bh, 5 * k + 4), Bl, transpose=t), XB)
    n = 17
    A, Ap, x, _ = system(rng, n, 5)
    At = A.T
    bt = to_parts([sum(At[i, j] * x[j] for j in range(n)) for i in range(n)])
    yt = md.DDLu(*Ap).solve(*bt, transpose=True)
    fwd, bwd = errors(At, x, bt, yt)
    assert fwd <= 1e5 * EPS + 1e-60 and bwd <= n * EPS, (fwd, bwd)
    _, bw = errors(A, x, bt, yt)
    assert bw > 1e-10, bw


def test_dd_lu_f64_factors():
    """DDLu.factor_f64 of a float64 A (n = 24 unblocked and 120 blocked, condition 10^4): its solves of A x = b and
    A^T x = b, b in double-double, have a backward error within n 2^-52 and are not the double-double LU's (their
    forward error exceeds 1e6 times its bound). Control: the factors of A with one entry changed by 1e-9 relative miss
    the backward bound."""
    mp.mp.dps = 60
    for n, seed in ((24, 5), (120, 6)):
        rng = np.random.default_rng(seed)
        A, Ap, x, b = system(rng, n, 4)
        a = Ap[0]
        A64 = mp.matrix([[mp.mpf(float(a[i, j])) for j in range(n)] for i in range(n)])
        b = to_parts([sum(A64[i, j] * x[j] for j in range(n)) for i in range(n)])
        lu = md.DDLu.factor_f64(a)
        assert lu.n == n
        bound = n * 2.0**-52
        for t, M in ((False, A64), (True, A64.T)):
            rhs = b if not t else to_parts([sum(M[i, j] * x[j] for j in range(n)) for i in range(n)])
            y = lu.solve(*rhs, transpose=t)
            fwd, bwd = errors(M, x, rhs, y)
            assert bwd <= bound, (n, t, bwd)
            assert fwd > 1e6 * (1e4 * EPS), (n, t, fwd)
            assert same(md.DDLu.factor_f64(a, par=True).solve(*rhs, transpose=t), y)
        bad = a.copy()
        bad[2, 3] *= 1 + 1e-9
        _, bw = errors(A64, x, b, md.DDLu.factor_f64(bad).solve(*b))
        assert bw > 10 * bound, (n, bw)


def test_dd_lu_errors():
    """singular A, non-finite entries and mismatched shapes raise ValueError naming the problem"""
    rng = np.random.default_rng(3)
    n = 9
    A = rng.uniform(-1, 1, (n, n)) + 4 * np.eye(n)
    z = np.zeros((n, n))
    b = rng.uniform(-1, 1, n)
    S = A.copy()
    S[:, 4] = 0.0
    with pytest.raises(ValueError, match="pivot at column 4"):
        md.DDLu(S, z)
    with pytest.raises(ValueError, match="pivot at column 4"):
        md.DDLu.factor_f64(S)
    N = A.copy()
    N[1, 3] = np.nan
    with pytest.raises(ValueError, match=r"non-finite entry at \(1, 3\)"):
        md.DDLu(A, np.where(N != N, np.inf, 0.0))
    with pytest.raises(ValueError, match=r"non-finite entry at \(1, 3\)"):
        md.DDLu.factor_f64(N)
    lu = md.DDLu(A, z)
    c = b.copy()
    c[2] = np.inf
    with pytest.raises(ValueError, match="non-finite entry at 2"):
        lu.solve(c, np.zeros(n))
    C = np.zeros((n, 3))
    C[4, 1] = np.nan
    with pytest.raises(ValueError, match=r"non-finite entry at \(4, 1\)"):
        lu.solve(np.zeros((n, 3)), C)
    with pytest.raises(ValueError, match=r"\(n,\) or \(n, k\)"):
        lu.solve(b[:-1], np.zeros(n - 1))
    with pytest.raises(ValueError, match="same shape"):
        lu.solve(b, np.zeros((n, 1)))
    with pytest.raises(ValueError, match=r"\(n, n\)"):
        md.DDLu(A, z[:-1])
    with pytest.raises(ValueError, match=r"\(n, n\)"):
        md.DDLu.factor_f64(A[:-1])
    with pytest.raises(TypeError):
        md.DDLu(A.astype(complex), z)
    # parts whose exact sum is zero: DD::new's two-sum keeps the value, so the 1 x 1 matrix is singular
    with pytest.raises(ValueError, match="pivot at column 0"):
        md.DDLu(np.array([[1.0]]), np.array([[-1.0]]))
