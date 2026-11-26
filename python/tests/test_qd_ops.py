"""Tests of qd_op and qd_add, qd_sub, qd_mul, qd_div, the elementwise quad-double operations, against exact rational
arithmetic (fractions.Fraction), and bitwise between the SIMD lanes and the scalar remainder and between parts in
any order, with controls that feed the same checks a wrong result."""
from fractions import Fraction

import numpy as np
import pytest

import multidouble as md

U4 = Fraction(1, 2**212)
# the quad-double bounds of the README's accuracy table, in u^4: add and subtract relative to |a| + |b|, multiply to
# |a b|, divide to |a / b|
BOUND = {0: 8, 3: 8, 1: 16, 2: 32}


def qd_parts(rng, n, spread=40):
    """four normalized part arrays of n random quad-doubles, exponents within 2^+-spread, both signs: each part the
    float64 nearest to what the parts before leave of an exact random rational"""
    out = [np.zeros(n) for _ in range(4)]
    for i in range(n):
        r = Fraction(int(rng.integers(1, 2**62)), 2**62) + Fraction(int(rng.integers(1, 2**62)), 2**130)
        r += Fraction(int(rng.integers(1, 2**62)), 2**200) + Fraction(1, int(rng.integers(3, 10**9)))
        r *= Fraction(2) ** int(rng.integers(-spread, spread))
        r *= 1 if rng.random() < 0.5 else -1
        for q in range(4):
            p = float(r)
            out[q][i] = p
            r -= Fraction(p)
    return out


def exact(parts, i):
    return sum(Fraction(float(p[i])) for p in parts)


def ref(op, x, y):
    return {0: x + y, 3: x - y, 1: x * y, 2: x / y}[op]


def scale(op, x, y):
    return {0: abs(x) + abs(y), 3: abs(x) + abs(y), 1: abs(x * y), 2: abs(x / y)}[op]


def bits(parts):
    return np.concatenate([np.asarray(p, dtype=np.float64).view(np.uint64) for p in parts])


@pytest.mark.parametrize("op", [0, 1, 2, 3])
def test_qd_op_against_exact(op):
    """On 203 elements (25 lane blocks and a remainder of 3): each result is within its bound of the exact
    operation, and qd_add, qd_mul, qd_div, qd_sub give qd_op's bits. Control: the results rounded to three parts miss
    the bound for some element."""
    rng = np.random.default_rng(10 + op)
    n = 203
    a, b = qd_parts(rng, n), qd_parts(rng, n)
    got = md.qd_op(op, *a, *b)
    named = {0: md.qd_add, 1: md.qd_mul, 2: md.qd_div, 3: md.qd_sub}[op]
    assert np.array_equal(bits(named(*a, *b)), bits(got))
    worst, misses = Fraction(0), 0
    for i in range(n):
        x, y = exact(a, i), exact(b, i)
        r, s = ref(op, x, y), scale(op, x, y)
        e = abs(exact(got, i) - r) / s
        worst = max(worst, e)
        e3 = abs(sum(Fraction(float(p[i])) for p in got[:3]) - r) / s
        misses += e3 > BOUND[op] * U4
    print(f"op {op}: worst error {float(worst / U4):.3g} u^4 (bound {BOUND[op]})")
    assert worst <= BOUND[op] * U4, float(worst / U4)
    assert misses > 0, "control: the results rounded to three parts met the bound everywhere"


def test_qd_op_lanes_are_the_scalar_and_parts_in_any_order():
    """Each element's bits do not depend on its place (an array of 19 rolled by 0..18 puts every element both in a
    lane block and in the scalar remainder) nor on the order of its parts (reversed and shuffled parts, which are
    renormalized first). Control: one ulp of one part of one input element changes that element's result."""
    rng = np.random.default_rng(3)
    n = 19
    a, b = qd_parts(rng, n), qd_parts(rng, n)
    for op in range(4):
        base = md.qd_op(op, *a, *b)
        for k in range(n):
            rolled = md.qd_op(op, *[np.roll(p, k) for p in a], *[np.roll(p, k) for p in b])
            assert np.array_equal(bits([np.roll(p, -k) for p in rolled]), bits(base)), (op, k)
        assert np.array_equal(bits(md.qd_op(op, *a[::-1], *[b[2], b[0], b[3], b[1]])), bits(base)), op
        c = [p.copy() for p in a]
        c[1][7] = np.nextafter(c[1][7], np.inf)
        moved = md.qd_op(op, *c, *b)
        assert any(moved[q][7] != base[q][7] for q in range(4)), op


def test_qd_op_errors():
    """an unknown op and unequal lengths raise ValueError"""
    z = [np.zeros(3)] * 4
    with pytest.raises(ValueError, match="op must be"):
        md.qd_op(4, *z, *z)
    with pytest.raises(ValueError, match="same length"):
        md.qd_op(0, *z, *z[:3], np.zeros(2))
