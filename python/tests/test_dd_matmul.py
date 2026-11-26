"""Tests of dd_matmul, the double-double matrix product, against exact rational arithmetic (fractions.Fraction) and
against dd_matvec bit for bit, with controls that feed the same checks a wrong result."""
from fractions import Fraction

import numpy as np
import pytest

import multidouble as md

U2 = Fraction(1, 2**106)


def dd(rng, shape, spread=20):
    """hi and lo arrays of random double-doubles of the shape, exponents within 2^+-spread, the lo parts full width"""
    h = rng.uniform(-1, 1, shape) * np.exp2(rng.integers(-spread, spread, shape))
    return md.two_sum(h, h * rng.uniform(-1, 1, shape) * 2.0**-54)


def bits(*v):
    return np.concatenate([np.ascontiguousarray(a, dtype=np.float64).ravel().view(np.uint64) for a in v])


def test_dd_matmul_is_dd_matvec_and_accurate():
    """A (13 x 37) times B (37 x 11): column j is bitwise dd_matvec(A, B[:, j]), and every entry is within
    (m / 8 + 12) 2^-106 of sum_l |a_il b_lj| of the exact product. Controls: the result's lo parts dropped miss the
    bound, and B with one bit flipped changes that column."""
    rng = np.random.default_rng(4)
    n, m, k = 13, 37, 11
    Ah, Al = dd(rng, (n, m))
    Bh, Bl = dd(rng, (m, k))
    Ch, Cl = md.dd_matmul(Ah, Al, Bh, Bl)
    assert Ch.shape == Cl.shape == (n, k)
    for j in range(k):
        vh, vl = md.dd_matvec(Ah, Al, np.ascontiguousarray(Bh[:, j]), np.ascontiguousarray(Bl[:, j]))
        assert np.array_equal(bits(Ch[:, j], Cl[:, j]), bits(vh, vl)), j
    bound = Fraction(m, 8) + 12
    worst, misses = Fraction(0), 0
    for i in range(n):
        for j in range(k):
            terms = [(Fraction(Ah[i, l]) + Fraction(Al[i, l])) * (Fraction(Bh[l, j]) + Fraction(Bl[l, j]))
                     for l in range(m)]
            s, scale = sum(terms), sum(abs(t) for t in terms)
            e = abs(Fraction(Ch[i, j]) + Fraction(Cl[i, j]) - s) / scale
            worst = max(worst, e)
            misses += abs(Fraction(Ch[i, j]) - s) / scale > bound * U2
    print(f"worst error {float(worst / U2):.3g} 2^-106 of sum |a b| (bound {float(bound):.3g})")
    assert worst <= bound * U2
    assert misses == n * k, "control: the hi parts alone met the bound"
    Bf = Bh.copy()
    Bf[5, 3] = np.frombuffer((np.array([Bf[5, 3]]).view(np.uint64) ^ 1).tobytes(), dtype=np.float64)[0]
    Fh, Fl = md.dd_matmul(Ah, Al, Bf, Bl)
    assert not np.array_equal(bits(Fh[:, 3], Fl[:, 3]), bits(Ch[:, 3], Cl[:, 3]))
    rest = lambda h, l: bits(np.delete(h, 3, 1), np.delete(l, 3, 1))
    assert np.array_equal(rest(Fh, Fl), rest(Ch, Cl))


def test_dd_matmul_shapes():
    """empty dimensions give empty or zero products; mismatched shapes raise ValueError, and a vector for B a
    TypeError (the binding takes matrices)"""
    z = lambda *s: np.zeros(s)
    h, l = md.dd_matmul(z(3, 0), z(3, 0), z(0, 2), z(0, 2))
    assert h.shape == (3, 2) and not h.any() and not l.any()
    assert md.dd_matmul(z(0, 4), z(0, 4), z(4, 2), z(4, 2))[0].shape == (0, 2)
    assert md.dd_matmul(z(3, 4), z(3, 4), z(4, 0), z(4, 0))[0].shape == (3, 0)
    with pytest.raises(ValueError, match=r"\(m, k\)"):
        md.dd_matmul(z(3, 4), z(3, 4), z(5, 2), z(5, 2))
    with pytest.raises(ValueError, match=r"\(m, k\)"):
        md.dd_matmul(z(3, 4), z(3, 3), z(4, 2), z(4, 2))
    with pytest.raises(TypeError):
        md.dd_matmul(z(3, 4), z(3, 4), z(4), z(4))
