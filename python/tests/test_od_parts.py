"""Tests of od_axpy and od_add_dd, octo-double arrays as eight float64 part arrays: against mpmath at 150 digits (about
500 bits, more than the 424 of eight parts), the SIMD lanes against the scalar tail bit for bit, and with controls that
feed the same checks a wrong input."""
import numpy as np
import pytest

import multidouble as md

mp = pytest.importorskip("mpmath")
EPS = 2.0**-418
N = 21  # not a multiple of 8: two blocks of lanes and a scalar tail of five


def split8(v):
    """the eight parts of an mpmath number by greedy round-to-nearest (each part the float nearest the rest)"""
    parts = []
    for _ in range(8):
        p = float(v)
        parts.append(p)
        v -= p
    return parts


def to_parts(vals):
    """mpmath numbers as eight float64 part arrays"""
    p = [split8(v) for v in vals]
    return [np.array([e[q] for e in p]) for q in range(8)]


def from_parts(x):
    """eight part arrays as a list of mpmath numbers (their exact sums)"""
    return [sum((mp.mpf(float(x[q][i])) for q in range(8)), mp.mpf(0)) for i in range(len(x[0]))]


def values(rng, n, scale=1.0):
    """n mpmath numbers of magnitudes up to scale with about 530 random bits, so that all eight parts are in use"""
    return [mp.mpf(float(scale * rng.uniform(-1, 1)))
            * (1 + sum(mp.mpf(float(rng.uniform(-1, 1))) * mp.mpf(2) ** (-53 * k) for k in range(1, 10)))
            for _ in range(n)]


def same_bits(a, b):
    """eight part arrays equal bit for bit"""
    return all(np.array_equal(np.asarray(p).view(np.uint64), np.asarray(q).view(np.uint64)) for p, q in zip(a, b))


def test_od_axpy_matches_mpmath_and_the_scalar_tail():
    """y + a x elementwise within 4 2^-418 (|y| + |a x|) of the exact value (two roundings to eight parts, one of the
    product, one of the sum), on 21 elements, so lanes and the scalar tail; every element computed alone (the scalar
    path) gives the bits of the full call. Control: x's second part dropped misses the bound."""
    mp.mp.dps = 150
    rng = np.random.default_rng(7)
    a = -0.37
    xv, yv = values(rng, N), values(rng, N, 3.0)
    x, y = to_parts(xv), to_parts(yv)
    out = md.od_axpy(a, *x, *y)
    assert len(out) == 8 and all(p.shape == (N,) for p in out)
    got = from_parts(out)
    xe, ye = from_parts(x), from_parts(y)
    worst = max(abs(got[i] - (ye[i] + a * xe[i])) / (abs(ye[i]) + abs(a * xe[i])) for i in range(N))
    assert worst <= 4 * EPS, float(worst / EPS)
    for i in (0, 7, 8, 15, 16, 20):
        one = md.od_axpy(a, *[p[i:i + 1] for p in x], *[p[i:i + 1] for p in y])
        assert same_bits(one, [p[i:i + 1] for p in out]), i
    xw = [p.copy() for p in x]
    xw[1][:] = 0.0
    bad = from_parts(md.od_axpy(a, *xw, *y))
    wrong = max(abs(bad[i] - (ye[i] + a * xe[i])) / (abs(ye[i]) + abs(a * xe[i])) for i in range(N))
    assert wrong > 1e10 * EPS, "control: x without its second part passes"


def test_od_add_dd_matches_mpmath_and_the_scalar_tail():
    """z + d elementwise for an octo-double z and a double-double d within 2 2^-418 (|z| + |d|) of the exact value,
    on 21 elements; every element alone gives the bits of the full call; z given with overlapping parts (each about
    a quarter of the one before, renormalized first) gives its exact sum plus d to the same bound. Control: d's low
    part dropped misses the bound."""
    mp.mp.dps = 150
    rng = np.random.default_rng(8)
    zv = values(rng, N, 2.0)
    z = to_parts(zv)
    dh = rng.uniform(-1, 1, N) * 1e-3
    dl = dh * rng.uniform(-1, 1, N) * 2.0**-53
    ze = from_parts(z)
    want = [ze[i] + mp.mpf(float(dh[i])) + mp.mpf(float(dl[i])) for i in range(N)]
    mag = [abs(ze[i]) + abs(mp.mpf(float(dh[i])) + mp.mpf(float(dl[i]))) for i in range(N)]
    out = md.od_add_dd(*z, dh, dl)
    got = from_parts(out)
    worst = max(abs(got[i] - want[i]) / mag[i] for i in range(N))
    assert worst <= 2 * EPS, float(worst / EPS)
    for i in (0, 7, 8, 16, 20):
        one = md.od_add_dd(*[p[i:i + 1] for p in z], dh[i:i + 1], dl[i:i + 1])
        assert same_bits(one, [p[i:i + 1] for p in out]), i
    # overlapping parts: each three quarters of what is left, so each about a quarter of the one before
    ov = []
    for v in zv:
        parts, r = [], v
        for _ in range(7):
            p = float(r) * 0.75
            parts.append(p)
            r -= mp.mpf(p)
        parts.append(float(r))
        ov.append(parts)
    zo = [np.array([e[q] for e in ov]) for q in range(8)]
    zoe = from_parts(zo)
    got = from_parts(md.od_add_dd(*zo, dh, dl))
    wo = max(abs(got[i] - (zoe[i] + mp.mpf(float(dh[i])) + mp.mpf(float(dl[i])))) / mag[i] for i in range(N))
    assert wo <= 2 * EPS, float(wo / EPS)
    bad = from_parts(md.od_add_dd(*z, dh, np.zeros(N)))
    wrong = max(abs(bad[i] - want[i]) / mag[i] for i in range(N))
    assert wrong > 1e10 * EPS, "control: d without its low part passes"


def test_od_parts_errors():
    """unequal lengths raise ValueError naming the arguments, and complex input raises TypeError"""
    x = [np.zeros(4) for _ in range(8)]
    with pytest.raises(ValueError, match="same length"):
        md.od_axpy(1.0, *x[:7], np.zeros(3), *x)
    with pytest.raises(ValueError, match="same length"):
        md.od_add_dd(*x, np.zeros(4), np.zeros(5))
    with pytest.raises(TypeError):
        md.od_add_dd(*x[:7], x[7].astype(complex), np.zeros(4), np.zeros(4))
