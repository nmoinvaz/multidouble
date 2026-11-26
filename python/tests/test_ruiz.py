"""Tests of ruiz_pow2 and scale_pow2, the power-of-two equilibration of a matrix and its exact application to every
part, on planted badly scaled matrices, with mpmath's log-determinant of the exact entries as the reference, and
controls that feed the same checks a wrong result."""
import numpy as np
import pytest

import multidouble as md

mp = pytest.importorskip("mpmath")


def planted(rng, n, spread=300):
    """A = diag(2^s) A0 diag(2^t), A0 = I + a random matrix of norm about 1/2 (well conditioned), s and t random
    integers within +-spread, as double-double parts (hi, lo), the lo parts full width"""
    a0 = np.eye(n) + 0.5 * rng.uniform(-1, 1, (n, n)) / np.sqrt(n)
    h, lo = md.two_sum(a0, a0 * rng.uniform(-1, 1, (n, n)) * 2.0**-54)
    s, t = rng.integers(-spread, spread, n), rng.integers(-spread, spread, n)
    e = s[:, None] + t[None, :]
    return np.ldexp(h, e), np.ldexp(lo, e)


def norms_in_range(S):
    """every nonzero row's and column's max |S| in [1/2, 2)"""
    m = np.concatenate([np.abs(S).max(axis=1), np.abs(S).max(axis=0)])
    m = m[m > 0]
    return bool(np.all((m >= 0.5) & (m < 2.0)))


def mp_logdet(h, lo):
    """(sign, ln|det|) of the exact matrix h + lo by mpmath's LU at 400 digits"""
    with mp.workdps(400):
        A = mp.matrix([[mp.mpf(float(h[i, j])) + mp.mpf(float(lo[i, j])) for j in range(h.shape[1])]
                       for i in range(h.shape[0])])
        d = mp.det(A)
        return (1.0 if d > 0 else -1.0), float(mp.log(abs(d)))


@pytest.mark.parametrize("n", [1, 7, 40])
def test_ruiz_pow2_equilibrates_and_keeps_the_determinant(n):
    """On planted matrices with rows and columns scaled by 2^+-300: every row's and column's max norm after
    scale_pow2 is in [1/2, 2), the scaled parts are the planted ones times exact powers of two (their unscaled
    round trip is bitwise), a second ruiz_pow2 gives zero scalings, and dd_logdet of the scaled matrix with
    ln|det A| = ln|det S| - (sum r + sum c) ln 2 gives mpmath's sign and ln|det A| to 1e-12 relative. Control: one
    sweep (iters=1) leaves some row or column out of range."""
    rng = np.random.default_rng(20 + n)
    h, lo = planted(rng, n)
    r, c = md.ruiz_pow2(h)
    assert r.dtype == np.int64 and c.dtype == np.int64
    sh, sl = md.scale_pow2(r, c, h, lo)
    assert norms_in_range(sh), (n, np.abs(sh).max(axis=1), np.abs(sh).max(axis=0))
    back = md.scale_pow2(-r, -c, sh, sl)
    assert all(np.array_equal(x.view(np.uint64), y.view(np.uint64)) for x, y in zip(back, (h, lo)))
    r2, c2 = md.ruiz_pow2(sh)
    assert not (r2.any() or c2.any())
    sg, la, _, _ = md.dd_logdet(sh, sl)
    la -= float(r.sum() + c.sum()) * np.log(2.0)
    ref = mp_logdet(h, lo)
    print(f"n {n}: ln|det A| {la:.15g}, mpmath {ref[1]:.15g}; scalings over 2^{r.min()}..2^{r.max()}")
    assert sg == ref[0] and abs(la - ref[1]) <= 1e-12 * max(1.0, abs(ref[1])), (n, sg, la, ref)
    if n > 1:
        r1, c1 = md.ruiz_pow2(h, iters=1)
        assert not norms_in_range(md.scale_pow2(r1, c1, h)[0]), "control: one sweep equilibrated the planted matrix"


def test_ruiz_pow2_edges():
    """zero rows and columns are left alone, an empty matrix gives empty scalings, a vector raises ValueError, and
    scale_pow2 raises ValueError for a shift that would lose bits below 2^-1022 or overflow, and for a part of
    another shape"""
    A = np.array([[0.0, 0.0, 0.0], [0.0, 8.0, 0.0], [0.0, 0.0, 0.25]])
    r, c = md.ruiz_pow2(A)
    assert r[0] == 0 and c[0] == 0 and norms_in_range(md.scale_pow2(r, c, A)[0])
    assert [len(x) for x in md.ruiz_pow2(np.zeros((0, 0)))] == [0, 0]
    with pytest.raises(ValueError, match="matrix"):
        md.ruiz_pow2(np.ones(3))
    one = np.array([[1.0 + 2.0**-52]])
    with pytest.raises(ValueError, match="not scaled exactly"):
        md.scale_pow2([-1060], [0], one)
    with pytest.raises(ValueError, match="not scaled exactly"):
        md.scale_pow2([1100], [0], one)
    with pytest.raises(ValueError, match="shape"):
        md.scale_pow2([0, 0], [0], one)


def test_scale_pow2_exponent_sums_do_not_wrap():
    """r + c past int64 raises ValueError for a finite nonzero entry instead of wrapping (2^63 - 1 twice wraps to -2,
    which would scale 1.0 by 1/4), naming the exact exponent, on either side; 2^62 and 2^62 - 1, a sum just inside
    int64, raises too. Controls: a zero entry under the same exponents stays zero, and sums that cancel, 1000 and
    -1000, scale exactly, so the check does not reject every large exponent."""
    big = 2**63 - 1
    with pytest.raises(ValueError, match=f"2\\^{2 * big}"):
        md.scale_pow2([big], [big], np.array([[1.0]]))
    with pytest.raises(ValueError, match="not scaled exactly"):
        md.scale_pow2([-big], [-big], np.array([[1.0]]))
    assert md.scale_pow2([big], [big], np.zeros((1, 1)))[0][0, 0] == 0.0
    assert md.scale_pow2([1000], [-1000], np.array([[1.5]]))[0][0, 0] == 1.5
    with pytest.raises(ValueError, match="not scaled exactly"):
        md.scale_pow2([2**62], [2**62 - 1], np.array([[1.0]]))
