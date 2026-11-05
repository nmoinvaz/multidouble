"""Tests of od_solve and ODLu, the octo-double LU, against mpmath at 150 digits (about 500 bits, more than the 424 of
eight parts), and against the Rust LU bit for bit, with controls that feed the same checks a wrong result."""
import numpy as np
import pytest

import multidouble as md

mp = pytest.importorskip("mpmath")
EPS = 2.0**-418


def split8(v):
    """the eight parts of an mpmath number by greedy round-to-nearest (each part the float nearest the rest)"""
    parts = []
    for _ in range(8):
        p = float(v)
        parts.append(p)
        v -= p
    return parts


def to_parts(M):
    """an mpmath matrix (or vector, as a list) as eight float64 part arrays"""
    if isinstance(M, list):
        p = [split8(v) for v in M]
        return [np.array([e[q] for e in p]) for q in range(8)]
    n, m = M.rows, M.cols
    p = [[split8(M[i, j]) for j in range(m)] for i in range(n)]
    return [np.array([[p[i][j][q] for j in range(m)] for i in range(n)]) for q in range(8)]


def from_parts(x):
    """eight part arrays of shape (n,) as a list of mpmath numbers (their exact sums)"""
    return [sum((mp.mpf(float(x[q][i])) for q in range(8)), mp.mpf(0)) for i in range(len(x[0]))]


def reflector(rng, n):
    v = mp.matrix([mp.mpf(float(t)) for t in rng.uniform(-1, 1, n)])
    vv = sum(t * t for t in v)
    return mp.eye(n) - (v * v.T) * (2 / vv)


def system(rng, n, p):
    """A = H1 D H2 with D = diag(10^(-p i / (n - 1))), condition 10^p, rounded to eight parts entrywise, a planted x
    of eight parts and b = A x rounded to eight parts, all in mpmath"""
    d = mp.diag([mp.mpf(10) ** (-mp.mpf(p) * k / (n - 1)) for k in range(n)])
    A = reflector(rng, n) * d * reflector(rng, n)
    Ap = to_parts(A)
    A = mp.matrix([[sum((mp.mpf(float(Ap[q][i, j])) for q in range(8)), mp.mpf(0)) for j in range(n)] for i in range(n)])
    x = [sum(mp.mpf(float(t)) * mp.mpf(2) ** (-53 * k) for k, t in enumerate(rng.uniform(-1, 1, 8))) for _ in range(n)]
    xp = to_parts(x)
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


def test_od_solve_error_follows_the_condition():
    """od_solve of A = H1 D H2 (n = 24, condition 10^p for p = 0, 10, 20, 30): the forward error is within
    cond 2^-418 + 1e-120 of the planted x and the backward error within n 2^-418. The error follows the condition: at
    cond 10^p it is at least 10^(p - 5) times the error at cond 1 (as tests/odlu.rs checks the Rust LU). Control: x
    rounded to its first four parts (quad-double) misses the forward bound by more than 1e20."""
    mp.mp.dps = 150
    n, f0 = 24, None
    for p in (0, 10, 20, 30):
        rng = np.random.default_rng(100 + p)
        cond = 10.0**p
        A, Ap, x, b = system(rng, n, p)
        y = md.od_solve(*Ap, *b)
        fwd, bwd = errors(A, x, b, y)
        bound = cond * EPS + 1e-120
        assert fwd <= bound, (p, fwd, bound)
        assert bwd <= n * EPS, (p, bwd)
        if p == 0:
            f0 = fwd
        else:
            assert fwd >= f0 * 10.0 ** (p - 5), (p, fwd, f0)
        yq = [np.array(t) for t in y[:4]] + [np.zeros(n)] * 4
        fq, _ = errors(A, x, b, yq)
        assert fq > 1e20 * bound, (p, fq)


def test_od_lu_solves_many_right_hand_sides_and_the_transpose():
    """ODLu factored once: solve gives od_solve's bits for one right-hand side and for k = 3 at once (each column the
    bits of its own solve), and A^T x = b is solved to the same bounds. Controls: b with one bit changed gives other
    bits, and the transposed solve's residual taken with A instead of A^T misses the bound."""
    mp.mp.dps = 150
    rng = np.random.default_rng(7)
    n = 17
    A, Ap, x, b = system(rng, n, 5)
    lu = md.ODLu(*Ap)
    assert lu.n == n
    same = lambda u, v: all(np.array_equal(np.asarray(s).view(np.uint64), np.asarray(t).view(np.uint64))
                            for s, t in zip(u, v))
    X = md.od_solve(*Ap, *b)
    assert same(lu.solve(*b), X)
    B = [np.stack([q, 2 * q, -q], axis=1) for q in b]
    XB = lu.solve(*B)
    for c, f in enumerate((1.0, 2.0, -1.0)):
        col = [q[:, c] for q in XB]
        assert same(col, md.od_solve(*Ap, *[f * q for q in b]))
    At = A.T
    bt = to_parts([sum(At[i, j] * x[j] for j in range(n)) for i in range(n)])
    yt = lu.solve(*bt, transpose=True)
    fwd, bwd = errors(At, x, bt, yt)
    assert fwd <= 1e5 * EPS + 1e-120 and bwd <= n * EPS, (fwd, bwd)
    _, bw = errors(A, x, bt, yt)
    assert bw > 1e-10, bw
    flip = [q.copy() for q in b]
    flip[1][3] = np.frombuffer((np.array([flip[1][3]]).view(np.uint64) ^ 1).tobytes(), dtype=np.float64)[0]
    assert not same(lu.solve(*flip), X)


def pinned_part(i, j, q):
    """part q of entry (i, j) of the pinned system's matrix, or of entry i of b when j is None: `pinned_part` of the
    Rust test od_lu_pinned_bits (tests/odlu.rs), small integers over powers of two, exact in float64"""
    scale = 2.0 ** (-7 - 53 * q)
    if j is None:
        t = (i * 29 + q * 71) % 199 - 99
    else:
        t = (i * 37 + j * 101 + q * 53 + i * j * 7) % 211 - 105 + (64 if q == 0 and i == j else 0)
    return t * scale


def pinned_system(n=37):
    A = [np.array([[pinned_part(i, j, q) for j in range(n)] for i in range(n)]) for q in range(8)]
    b = [np.array([pinned_part(i, None, q) for i in range(n)]) for q in range(8)]
    return A, b


def parts_hash(x):
    """FNV-1a over the bits of the eight parts, all of part 0 first, as parts_hash of tests/odlu.rs"""
    h = 0xCBF29CE484222325
    for q in range(8):
        for v in np.asarray(x[q]).view(np.uint64):
            h ^= int(v)
            h = (h * 0x100000001B3) % 2**64
    return h


PINNED = (0x06CED95B3A263818, 0x8CF2F5804D098C89)  # tests/odlu.rs, od_lu_pinned_bits: A x = b and A^T x = b


def test_od_solve_is_the_rust_lu_bitwise():
    """od_solve and ODLu.solve (and its transpose) of the pinned system give the bits of the Rust ODLu called directly
    (tests/odlu.rs pins the same hashes), with the parts renormalized as OD::new does. Control: b with one bit changed
    in a second part gives another hash."""
    A, b = pinned_system()
    x = md.od_solve(*A, *b)
    assert parts_hash(x) == PINNED[0], hex(parts_hash(x))
    lu = md.ODLu(*A)
    assert parts_hash(lu.solve(*b)) == PINNED[0]
    assert parts_hash(lu.solve(*b, transpose=True)) == PINNED[1]
    c = [q.copy() for q in b]
    c[1][5] = np.frombuffer((np.array([c[1][5]]).view(np.uint64) ^ 1).tobytes(), dtype=np.float64)[0]
    assert parts_hash(md.od_solve(*A, *c)) != PINNED[0]


def test_od_solve_errors():
    """singular A, non-finite entries and mismatched shapes raise ValueError naming the problem"""
    A, b = pinned_system(9)
    Z = [q.copy() for q in A]
    for q in Z:
        q[:, 4] = 0.0
    with pytest.raises(ValueError, match="pivot at column 4"):
        md.od_solve(*Z, *b)
    with pytest.raises(ValueError, match="pivot"):
        md.ODLu(*Z)
    N = [q.copy() for q in A]
    N[2][1, 3] = np.nan
    with pytest.raises(ValueError, match=r"non-finite entry at \(1, 3\)"):
        md.od_solve(*N, *b)
    c = [q.copy() for q in b]
    c[0][2] = np.inf
    with pytest.raises(ValueError, match="non-finite entry at 2"):
        md.od_solve(*A, *c)
    with pytest.raises(ValueError, match=r"\(n,\) or \(n, k\)"):
        md.od_solve(*A, *[q[:-1] for q in b])
    with pytest.raises(ValueError, match="same shape"):
        md.od_solve(*A, *b[:7], b[7][:, None])
    with pytest.raises(ValueError, match=r"\(n, n\)"):
        md.od_solve(*A[:7], A[7][:-1], *b)
    with pytest.raises(TypeError):
        md.od_solve(*A[:7], A[7].astype(complex), *b)
