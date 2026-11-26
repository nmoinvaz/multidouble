"""Tests of parts_from_mp (and dd_from_mp, qd_from_mp, od_from_mp) and mp_from_parts, the conversions between mpmath
numbers and 2-, 4- and 8-part float64 arrays, against exact rational arithmetic (fractions.Fraction) and against the
Rust renormalization of the octo-double arrays, with controls that feed the same checks a wrong result."""
from fractions import Fraction

import numpy as np
import pytest

import multidouble as md

mp = pytest.importorskip("mpmath")


def values(prec=1200, count=40, seed=5):
    """mpmath numbers of prec bits: random mantissas over exponents from 2^-500 to 2^500 (so that eight parts stay above
    2^-1022), both signs, and 1/3, -2/7, a power of two, an exact double, zero and 1 + 2^-53 + 2^-160, just past a
    tie"""
    rng = np.random.default_rng(seed)
    with mp.workprec(prec):
        out = []
        for _ in range(count):
            m = mp.mpf(int(rng.integers(1, 2**62))) / 2**62 + mp.mpf(int(rng.integers(0, 2**62))) / 2**124
            m += mp.mpf(1) / int(rng.integers(3, 10**6))
            e = int(rng.integers(-500, 500))
            out.append((1 if rng.random() < 0.5 else -1) * mp.ldexp(m, e))
        out += [mp.mpf(1) / 3, mp.mpf(-2) / 7, mp.ldexp(mp.mpf(1), -300), mp.mpf(0.1), mp.mpf(0),
                mp.mpf(1) + mp.ldexp(mp.mpf(1), -53) + mp.ldexp(mp.mpf(1), -160)]
    return out


def frac(x):
    """an mpmath number as an exact Fraction"""
    sign, m, e, _ = x._mpf_
    return (-1) ** sign * Fraction(m) * Fraction(2) ** e


def nearest(r):
    """the float64 nearest a Fraction r (ties to even), by Python's exact Fraction -> float conversion"""
    return float(r)


@pytest.mark.parametrize("n", [2, 4, 8])
def test_parts_are_the_greedy_expansion(n):
    """For values of 1200 bits, with the working precision at 53, 200 and 2000 bits: every part is the float64
    nearest to the exact remainder the parts before it leave (Fraction arithmetic, no mpmath), the parts are the same
    at every working precision, and mp_from_parts gives their exact sum. Control: the parts formed by the plain
    mpmath subtraction at a working precision of 30 bits (the former dd_from_mp's remainder) miss the greedy check for
    some values."""
    vals = values()
    got = {}
    for prec in (53, 200, 2000):
        with mp.workprec(prec):
            got[prec] = md.parts_from_mp(vals, n)
            sums = md.mp_from_parts(*got[prec])
        for i, x in enumerate(vals):
            r = frac(x)
            for q in range(n):
                p = got[prec][q][i]
                assert p == nearest(r), (n, prec, i, q)
                r -= Fraction(p)
            assert frac(sums[i]) == sum(Fraction(got[prec][q][i]) for q in range(n)), (n, prec, i)
    for prec in (200, 2000):
        assert all(np.array_equal(a.view(np.uint64), b.view(np.uint64)) for a, b in zip(got[prec], got[53]))
    misses = 0
    with mp.workprec(30):
        for x in vals:
            r, ok = x, True
            exact = frac(x)
            for _ in range(n):
                p = float(r)
                ok &= p == nearest(exact)
                exact -= Fraction(p)
                r = r - mp.mpf(p)
            misses += not ok
    assert misses > 0, "control: the rounded remainders gave the greedy parts everywhere"


def test_named_conversions_and_the_rust_renormalization():
    """dd_from_mp, qd_from_mp and od_from_mp are parts_from_mp with 2, 4 and 8 parts, bit for bit, and the octo-double
    parts are a fixed point of the Rust renormalization (od_add_dd of zero, OD::new), the normalized form, except at
    the planted tie 1 + 2^-53 + 2^-160, whose greedy parts 1 + 2^-52 and -2^-53 the renormalization moves to 1 and
    2^-53, the same sum. Control: the parts with two adjacent ones swapped are renormalized to other bits."""
    vals = values(count=20, seed=9)
    same = lambda u, v: all(np.array_equal(np.asarray(a).view(np.uint64), np.asarray(b).view(np.uint64))
                            for a, b in zip(u, v))
    assert same(md.dd_from_mp(vals), md.parts_from_mp(vals, 2))
    assert same(md.qd_from_mp(vals), md.parts_from_mp(vals, 4))
    od = md.od_from_mp(vals)
    assert same(od, md.parts_from_mp(vals, 8))
    z = np.zeros(len(vals))
    r = md.od_add_dd(*od, z, z)
    tie = len(vals) - 1
    assert same([q[:tie] for q in r], [q[:tie] for q in od])
    assert (od[0][tie], od[1][tie], r[0][tie], r[1][tie]) == (1 + 2.0**-52, -(2.0**-53), 1.0, 2.0**-53)
    assert md.mp_from_parts(*[q[tie:] for q in r]) == md.mp_from_parts(*[q[tie:] for q in od])
    swapped = list(od)
    swapped[1], swapped[2] = swapped[2], swapped[1]
    assert not same(md.od_add_dd(*swapped, z, z), swapped)


def test_dd_from_mp_at_a_low_working_precision():
    """At a working precision of 30 bits, dd_from_mp of 1/3 and 2/7 formed at 200 bits gives hi + lo within 2^-106 of
    the value (the exact remainder). Control: the former remainder, x - hi at the working precision, keeps 30 bits of
    lo and misses the bound by more than 2^20."""
    with mp.workprec(200):
        vals = [mp.mpf(1) / 3, mp.mpf(2) / 7]
    with mp.workprec(30):
        hi, lo = md.dd_from_mp(vals)
        old = [float(x - mp.mpf(float(x))) for x in vals]
    for i, x in enumerate(vals):
        err = abs(frac(x) - Fraction(hi[i]) - Fraction(lo[i])) / abs(frac(x))
        bad = abs(frac(x) - Fraction(hi[i]) - Fraction(old[i])) / abs(frac(x))
        assert err <= Fraction(1, 2**106), (i, float(err))
        assert bad > 2**20 * Fraction(1, 2**106), (i, float(bad))


def test_edges():
    """zeros, an empty sequence, strings and floats (converted at the working precision), values past the float64
    range (an infinite first part, the rest zero) and unequal part arrays (ValueError)"""
    assert [len(p) for p in md.parts_from_mp([], 4)] == [0] * 4
    p = md.parts_from_mp([0, "0.5", 0.25], 3)
    assert [list(q) for q in p] == [[0.0, 0.5, 0.25], [0.0] * 3, [0.0] * 3]
    with mp.workprec(100):
        big = mp.ldexp(mp.mpf(1), 1100)
    p = md.parts_from_mp([big, -big], 2)
    assert list(p[0]) == [np.inf, -np.inf] and list(p[1]) == [0.0, 0.0]
    assert md.mp_from_parts() == []
    with pytest.raises(ValueError, match="same length"):
        md.mp_from_parts(np.ones(2), np.ones(3))
