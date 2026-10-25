"""Double-double arithmetic on numpy arrays.

A double-double array is a pair of float64 arrays (hi, lo) with value hi + lo elementwise (about 32 significant digits).

Backed by the Rust crate multidouble, on the best SIMD backend the CPU has (``isa()``):

- ``add``, ``sub``, ``mul``, ``div``: elementwise operations; ``dd_op(op, ...)`` with op 0 add, 1 mul, 2 div, 3 sub;
- ``dd_solve``: x with A x = b by LU with partial pivoting, A and b in double-double;
- ``qd_add_dd``: a quad-double array (four float64 arrays) plus a double-double one, elementwise in quad-double.

In numpy, for code that composes them with other numpy operations (these are plain numpy expressions, so the same
inputs give the same bits on every machine with IEEE float64 arithmetic):

- ``two_sum``, ``two_prod``: the error-free transformations (``two_prod`` by Dekker's splitting, no FMA needed);
- ``dd_add`` (the accurate double-double sum), ``dd_scale`` (times an f64 scalar), ``dd_axpy`` (y + a x);
- ``dd_norm`` (max |hi + lo|) and ``dd_from_mp`` (from mpmath numbers; needs mpmath).
"""
import numpy as np

from ._multidouble import add, dd_op, dd_solve, div, isa, mul, qd_add_dd, sub

__all__ = ["add", "sub", "mul", "div", "dd_op", "dd_solve", "qd_add_dd", "isa", "two_sum", "two_prod", "dd_add",
           "dd_scale", "dd_axpy", "dd_norm", "dd_from_mp"]


def two_sum(a, b):
    """a + b = s + e exactly (Knuth), elementwise"""
    s = a + b
    bb = s - a
    return s, (a - (s - bb)) + (b - bb)


_SPLIT = 134217729.0  # 2^27 + 1
_BIG = 2.0**996  # above it _SPLIT * a overflows


def _split(a):
    """a = hi + lo exactly, hi with at most 26 significant bits (Dekker), elementwise. Operands above 2^996 are split
    at 2^-28 times their value and scaled back (exact), so that _SPLIT * a cannot overflow; below it the result is
    bitwise that of the plain split."""
    a = np.asarray(a, dtype=np.float64)
    big = np.abs(a) > _BIG
    s = np.where(big, a * 2.0**-28, a)
    t = _SPLIT * s
    hi = t - (t - s)
    lo = s - hi
    if big.any():
        hi = np.where(big, hi * 2.0**28, hi)
        lo = np.where(big, lo * 2.0**28, lo)
    return hi, lo


def two_prod(a, b):
    """a b = p + e exactly (Dekker), elementwise, wherever p and the partial products are finite"""
    p = a * b
    ah, al = _split(a)
    bh, bl = _split(b)
    return p, ((ah * bh - p) + ah * bl + al * bh) + al * bl


def dd_add(ah, al, bh, bl):
    """(ah + al) + (bh + bl) in double-double (the accurate sum: both parts' errors kept), elementwise"""
    s, e = two_sum(ah, bh)
    t, f = two_sum(al, bl)
    e = e + t
    h = s + e
    e = e - (h - s)
    e = e + f
    h2 = h + e
    return h2, e - (h2 - h)


def dd_scale(xh, xl, a):
    """a (xh + xl) in double-double, a an f64 scalar"""
    p, e = two_prod(np.full_like(xh, a), xh)
    e = e + a * xl
    h = p + e
    return h, e - (h - p)


def dd_axpy(a, xh, xl, yh, yl):
    """y + a x in double-double, a an f64 scalar"""
    ph, pl = dd_scale(xh, xl, a)
    return dd_add(yh, yl, ph, pl)


def dd_norm(h, l):
    """max |h + l| (0 for empty arrays)"""
    return float(np.max(np.abs(h + l))) if len(h) else 0.0


def dd_from_mp(v):
    """(hi, lo) arrays from a sequence of mpmath numbers: hi the nearest f64, lo the nearest f64 to the rest"""
    import mpmath as mp

    v = list(v)
    hi = np.array([float(x) for x in v])
    lo = np.array([float(x - mp.mpf(h)) for x, h in zip(v, hi)])
    return hi, lo
