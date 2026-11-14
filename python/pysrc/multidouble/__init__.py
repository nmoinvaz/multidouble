"""Double-double arithmetic on numpy arrays.

A double-double array is a pair of float64 arrays (hi, lo) with value hi + lo elementwise (about 32 significant digits).

Backed by the Rust crate multidouble, on the best SIMD backend the CPU has (``isa()``):

- ``add``, ``sub``, ``mul``, ``div``: elementwise operations; ``dd_op(op, ...)`` with op 0 add, 1 mul, 2 div, 3 sub;
- ``dd_dot``: a dot product in double-double (8 lanes at a time, then the lane sums), to about (n / 8 + 12) 2^-106 of
  sum |x_i y_i|;
- ``dd_matvec``: A v in double-double, each row a ``dd_dot``;
- ``dd_horner``: sum_k c_k a^k by Horner's rule in double-double at a float a, each step ``dd_add(c_k, dd_scale(p,
  a))`` bit for bit;
- ``dd_solve``: x with A x = b by LU with partial pivoting, A and b in double-double;
- ``qd_solve``: x with A x = b by LU with partial pivoting in quad-double, A and b as four float64 part arrays each,
  to about cond(A) 2^-209; ``QDLu`` factors A once for several solves (and solves with A^T);
- ``qd_add_dd``: a quad-double array (four float64 arrays) plus a double-double one, elementwise in quad-double;
- ``qd_axpy``: y + a x for quad-double arrays x, y and a float a, elementwise in quad-double;
- ``od_solve``: x with A x = b by LU with partial pivoting in octo-double, A and b as eight float64 part arrays each,
  to about cond(A) 2^-418; ``ODLu`` factors A once for several solves (and solves with A^T);
- ``od_add_dd``: an octo-double array (eight float64 arrays) plus a double-double one, elementwise in octo-double;
- ``od_axpy``: y + a x for octo-double arrays x, y and a float a, elementwise in octo-double.

Their array arguments may be any arrays or sequences of real numbers, strided, in Fortran order or of another numeric
dtype. Each is converted to a C-contiguous float64 array, and one that is already so is passed on without a copy.

In numpy, for code that composes them with other numpy operations (these are plain numpy expressions, so the same
inputs give the same bits on every machine with IEEE float64 arithmetic):

- ``two_sum``, ``two_prod``: the error-free transformations (``two_prod`` by Dekker's splitting, no FMA needed);
- ``dd_add`` (the accurate double-double sum), ``dd_scale`` (times an f64 scalar), ``dd_axpy`` (y + a x);
- ``dd_norm`` (max |hi + lo|) and ``dd_from_mp`` (from mpmath numbers; needs mpmath);
- ``gcr``: x with A x = b in double-double by preconditioned GMRES (its GCR form), given the products A u in
  double-double and a preconditioner, typically an f64 LU of A: the refinement of a mixed-precision solve.
"""
import time

import numpy as np

from . import _multidouble as _md
from ._multidouble import isa

__all__ = ["add", "sub", "mul", "div", "dd_op", "dd_matvec", "dd_horner", "dd_solve", "qd_solve", "QDLu", "qd_add_dd",
           "qd_axpy", "isa", "two_sum", "two_prod", "dd_add", "dd_scale", "dd_axpy", "dd_norm", "dd_from_mp", "dd_dot",
           "gcr"]


def _masked(v):
    """v, or an array or element of a sequence or object array v (nested ones included), has a masked value"""
    if np.ma.isMaskedArray(v):
        return bool(np.ma.getmaskarray(v).any())
    if isinstance(v, np.ndarray) and v.dtype == object:
        return any(_masked(x) for x in v.flat)
    if isinstance(v, (list, tuple)):
        return any(_masked(x) for x in v)
    return False


def _f64(v, name):
    """v as a C-contiguous float64 array for the Rust functions: v itself if it is one (no copy), else a converted
    copy (np.ascontiguousarray). Any array or sequence of real numbers converts (float, integer, unsigned and bool
    dtypes, and objects that float() converts). Complex, string and other dtypes, None and masked values raise
    TypeError naming the argument, where numpy's conversion would drop an imaginary part or a mask, parse a string or
    give nan."""
    # np.asarray drops the masks, also of masked arrays in a list, and passes the hidden values on
    if _masked(v):
        raise TypeError(f"{name} must not have masked values")
    a = np.asarray(v)
    if a.dtype.kind == "O":
        # astype would turn None into nan and parse strings
        if any(x is None or isinstance(x, (str, bytes)) for x in a.flat):
            raise TypeError(f"{name} must be real numbers, not None or strings")
        try:
            a = a.astype(np.float64)
        except (TypeError, ValueError) as e:
            raise TypeError(f"{name} must be real numbers ({e})") from e
    elif a.dtype.kind not in "biuf":
        raise TypeError(f"{name} must be real numbers, not {a.dtype}")
    return np.ascontiguousarray(a, dtype=np.float64)


def dd_op(op, ah, al, bh, bl):
    """(ah + al) op (bh + bl) elementwise in double-double, any length: op 0 add, 1 mul, 2 div, 3 sub. Returns the
    (hi, lo) arrays of the result."""
    return _md.dd_op(op, _f64(ah, "ah"), _f64(al, "al"), _f64(bh, "bh"), _f64(bl, "bl"))


def add(ah, al, bh, bl):
    """a + b in double-double, elementwise: (hi, lo)"""
    return _md.add(_f64(ah, "ah"), _f64(al, "al"), _f64(bh, "bh"), _f64(bl, "bl"))


def sub(ah, al, bh, bl):
    """a - b in double-double, elementwise: (hi, lo)"""
    return _md.sub(_f64(ah, "ah"), _f64(al, "al"), _f64(bh, "bh"), _f64(bl, "bl"))


def mul(ah, al, bh, bl):
    """a b in double-double, elementwise: (hi, lo)"""
    return _md.mul(_f64(ah, "ah"), _f64(al, "al"), _f64(bh, "bh"), _f64(bl, "bl"))


def div(ah, al, bh, bl):
    """a / b in double-double, elementwise: (hi, lo)"""
    return _md.div(_f64(ah, "ah"), _f64(al, "al"), _f64(bh, "bh"), _f64(bl, "bl"))


def dd_matvec(ah, al, vh, vl):
    """A v in double-double: A as (n, m) hi and lo arrays, v as hi and lo arrays of length m, each row of the result
    the dot product of dd_dot. Returns the (hi, lo) arrays of A v."""
    return _md.dd_matvec(_f64(ah, "ah"), _f64(al, "al"), _f64(vh, "vh"), _f64(vl, "vl"))


def dd_horner(ch, cl, a):
    """sum_k (ch + cl)_k a^k by Horner's rule in double-double at a float a. ch and cl hold the hi and lo parts of the
    coefficients c_0, ..., c_N, each a sequence of N + 1 arrays of one length n or an (N + 1, n) array, the form in
    which a Taylor series' coefficients are collected order by order. From p = c_N each step p = c_k + a p is
    dd_add(c_k, dd_scale(p, a)) bit for bit, in Rust, 8 values at a time on the best SIMD backend. A sum with
    float64 powers a**k would carry an error of about 2^-53 of each term unless a is a power of two. Returns the
    (hi, lo) arrays of the n sums."""
    h, l = _f64(ch, "ch"), _f64(cl, "cl")
    if h.ndim != 2 or l.ndim != 2:
        raise ValueError("ch and cl must be sequences of N + 1 arrays of one length, or (N + 1, n) arrays")
    return _md.dd_horner(h, l, float(a))


def dd_solve(ah, al, bh, bl):
    """x with A x = b in double-double, by LU with partial pivoting: A as (n, n) hi and lo arrays, b as hi and lo
    arrays of length n. Returns the (hi, lo) arrays of x. Raises ValueError if A is singular."""
    return _md.dd_solve(_f64(ah, "ah"), _f64(al, "al"), _f64(bh, "bh"), _f64(bl, "bl"))


def _parts(names, *v):
    """each of the arrays v converted by _f64 under its name, e.g. the four parts a0, a1, a2, a3 of a quad-double
    array"""
    return [_f64(x, n) for x, n in zip(v, names)]


def qd_solve(a0, a1, a2, a3, b0, b1, b2, b3):
    """x with A x = b in quad-double, by LU with partial pivoting (the Rust crate's QDLu, getf2 order, its updates 8
    rows at a time on the best SIMD backend, bitwise the same on every backend): A as four (n, n) part arrays (A = a0 +
    a1 + a2 + a3 entrywise), b as four part arrays of shape (n,), or (n, k) for k right-hand sides, the columns of b.
    Each entry is the exact sum of its four parts in any order, so any four parts summing to the value will do, and
    normalized parts give the bits of their renormalization as before. The error is about cond(A) 2^-209 relative
    (partial pivoting is backward stable). Returns the four parts of x, of b's shape. Raises ValueError if A is singular
    (an exactly zero pivot), if A or b has an entry that is not finite, or for mismatched shapes. QDLu(a0, a1, a2,
    a3).solve(b0, b1, b2, b3) gives the same bits and keeps the factors."""
    a = _parts(("a0", "a1", "a2", "a3"), a0, a1, a2, a3)
    b = _parts(("b0", "b1", "b2", "b3"), b0, b1, b2, b3)
    return _md.qd_solve(*a, *b)


class QDLu:
    """The quad-double LU of A with partial pivoting, factored once for several solves, e.g. the same Jacobian over
    several Newton steps: QDLu(a0, a1, a2, a3) with A as four (n, n) part arrays, each entry the exact sum of its parts
    in any order. The factorization costs about n^3 / 3 quad-double multiply-adds and each solve about n^2. Raises
    ValueError if A is singular or has an entry that is not finite."""

    def __init__(self, a0, a1, a2, a3):
        self._lu = _md.QDLu(*_parts(("a0", "a1", "a2", "a3"), a0, a1, a2, a3))

    @property
    def n(self):
        """the order of A"""
        return self._lu.n

    def solve(self, b0, b1, b2, b3, transpose=False):
        """x with A x = b in quad-double, or A^T x = b when transpose: b as four part arrays of shape (n,) or (n, k),
        each entry the exact sum of its parts in any order. Returns the four parts of x, of b's shape. A x = b gives the
        bits of qd_solve (8 rows at a time on the SIMD lanes); A^T x = b runs in scalar quad-double. Raises ValueError
        if b has an entry that is not finite or the wrong shape."""
        return self._lu.solve(*_parts(("b0", "b1", "b2", "b3"), b0, b1, b2, b3), bool(transpose))


def qd_add_dd(z0, z1, z2, z3, dh, dl):
    """(z0 + z1 + z2 + z3) + (dh + dl) elementwise in quad-double: a quad-double array (four float64 arrays, each
    element the exact sum of its parts in any order) plus a double-double one. Returns the four parts of the result,
    renormalized."""
    z = [_f64(v, n) for v, n in ((z0, "z0"), (z1, "z1"), (z2, "z2"), (z3, "z3"))]
    return _md.qd_add_dd(*z, _f64(dh, "dh"), _f64(dl, "dl"))


def qd_axpy(a, x0, x1, x2, x3, y0, y1, y2, y3):
    """y + a x elementwise in quad-double for quad-double arrays x and y (four float64 arrays each, the parts
    normalized) and a float a. Returns the four parts of the result."""
    x = [_f64(v, n) for v, n in ((x0, "x0"), (x1, "x1"), (x2, "x2"), (x3, "x3"))]
    y = [_f64(v, n) for v, n in ((y0, "y0"), (y1, "y1"), (y2, "y2"), (y3, "y3"))]
    return _md.qd_axpy(a, *x, *y)


def od_solve(a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3, b4, b5, b6, b7):
    """x with A x = b in octo-double, by LU with partial pivoting (the Rust crate's ODLu, getf2 order, its updates
    8 rows at a time on the best SIMD backend, bitwise the same on every backend): A as eight (n, n) part arrays (A =
    a0 + ... + a7 entrywise), b as eight part arrays of shape (n,), or (n, k) for k right-hand sides, the columns of
    b. Each entry is renormalized first, so any eight parts summing to the value will do. The error is about cond(A)
    2^-418 relative (partial pivoting is backward stable). Returns the eight parts of x, of b's shape. Raises
    ValueError if A is singular (an exactly zero pivot), if A or b has an entry that is not finite, or for mismatched
    shapes. ODLu(a0, ..., a7).solve(b0, ..., b7) gives the same bits and keeps the factors."""
    a = [_f64(v, f"a{q}") for q, v in enumerate((a0, a1, a2, a3, a4, a5, a6, a7))]
    b = [_f64(v, f"b{q}") for q, v in enumerate((b0, b1, b2, b3, b4, b5, b6, b7))]
    return _md.od_solve(*a, *b)


class ODLu:
    """The octo-double LU of A with partial pivoting, factored once for several solves: ODLu(a0, ..., a7) with A as
    eight (n, n) part arrays, each entry renormalized first. The factorization costs about n^3 / 3 octo-double
    multiply-adds and each solve about n^2. Raises ValueError if A is singular or has an entry that is not finite."""

    def __init__(self, a0, a1, a2, a3, a4, a5, a6, a7):
        """factor A = a0 + ... + a7 (eight (n, n) part arrays)"""
        self._lu = _md.ODLu(*[_f64(v, f"a{q}") for q, v in enumerate((a0, a1, a2, a3, a4, a5, a6, a7))])

    @property
    def n(self):
        """the order of A"""
        return self._lu.n

    def solve(self, b0, b1, b2, b3, b4, b5, b6, b7, transpose=False):
        """x with A x = b in octo-double, or A^T x = b when transpose: b as eight part arrays of shape (n,) or (n, k),
        each entry renormalized first. Returns the eight parts of x, of b's shape. A x = b gives the bits of od_solve
        (8 rows at a time on the SIMD lanes); A^T x = b runs in scalar octo-double. Raises ValueError if b has an
        entry that is not finite or the wrong shape."""
        b = [_f64(v, f"b{q}") for q, v in enumerate((b0, b1, b2, b3, b4, b5, b6, b7))]
        return self._lu.solve(*b, bool(transpose))


def od_add_dd(z0, z1, z2, z3, z4, z5, z6, z7, dh, dl):
    """(z0 + ... + z7) + (dh + dl) elementwise in octo-double: an octo-double array (eight float64 arrays, each element
    renormalized first, as od_solve takes its entries) plus a double-double one, e.g. a Newton step applied to a state
    kept in octo-double. 8 elements at a time on the best SIMD backend and the rest in scalar octo-double, bitwise the
    same per element. Returns the eight parts of the result, renormalized."""
    z = [_f64(v, f"z{q}") for q, v in enumerate((z0, z1, z2, z3, z4, z5, z6, z7))]
    return _md.od_add_dd(*z, _f64(dh, "dh"), _f64(dl, "dl"))


def od_axpy(a, x0, x1, x2, x3, x4, x5, x6, x7, y0, y1, y2, y3, y4, y5, y6, y7):
    """y + a x elementwise in octo-double for octo-double arrays x and y (eight float64 arrays each, the parts
    normalized, e.g. the output of od_add_dd) and a float a: each element times a, then the sum, 8 at a time on the best
    SIMD backend, bitwise the same on every backend. Returns the eight parts of the result."""
    x = [_f64(v, f"x{q}") for q, v in enumerate((x0, x1, x2, x3, x4, x5, x6, x7))]
    y = [_f64(v, f"y{q}") for q, v in enumerate((y0, y1, y2, y3, y4, y5, y6, y7))]
    return _md.od_axpy(a, *x, *y)


__all__ += ["od_solve", "ODLu", "od_add_dd", "od_axpy"]


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


def dd_dot(xh, xl, yh, yl):
    """sum_i (xh + xl)_i (yh + yl)_i in double-double, as (hi, lo) floats: the Rust dot product (8 lanes at a time on
    the best SIMD backend, bitwise the same on every backend), to about (n / 8 + 12) 2^-106 of sum |x_i y_i|. Any
    sequences of numbers of one length."""
    return _md.dd_dot(_f64(xh, "xh"), _f64(xl, "xl"), _f64(yh, "yh"), _f64(yl, "yl"))


def _dd_div(a, b):
    """a / b for double-double scalars a = (hi, lo), b = (hi, lo): the f64 quotient q, then (a - q b) / b, to about
    2^-104 relative"""
    q = a[0] / b[0]
    p, e = two_prod(np.float64(q), np.float64(b[0]))
    r = (((a[0] - p) - e) + a[1]) - q * b[1]
    q2 = r / b[0]
    h = q + q2
    return float(h), float(q2 - (h - q))


def gcr(apply, precond, bh, bl, max_products=30, step_tol=1e-28, confirm=1, ref=None, verbose=False, coef="dd",
        nu=0.9):
    """x with A x = b, b = bh + bl in double-double: GMRES on A M^-1 (right preconditioning; Saad and Schultz, SIAM J.
    Sci. Stat. Comput. 7 (1986) 856, doi:10.1137/0907058) in its GCR form (Eisenstat, Elman and Schultz, SIAM J.
    Numer. Anal. 20 (1983) 345, doi:10.1137/0720023). apply(uh, ul) returns A u in double-double as (hi, lo) (the
    products must be exact to double-double for the result to be); precond(rh, rl) returns M^-1 r as (hi, lo), M an
    approximation of A such as its f64 LU. Each iteration takes a direction u, forms w = A u (one product),
    orthogonalizes w against the earlier w's (twice), applying the same coefficients to u, and updates x += c u,
    r -= c w with c = w.r. The u, w, x and r are double-double and updated with the same coefficients, so r stays the
    residual b - A x to double-double rounding without recomputing it.
    The direction is the preconditioned residual u = M^-1 r while the last iteration reduced |r| by the factor nu, and
    otherwise u = M^-1 w for the last w, the next Krylov vector of A M^-1 (the adaptive choice of Jiranek and
    Rozloznik, Numer. Algorithms 53 (2010) 93, doi:10.1007/s11075-009-9311-2). The residual alone breaks down where
    GMRES stagnates: there c = 0, r does not change, and its next direction's image lies in the span of the earlier w's.
    The Krylov vector extends the span there, so in exact arithmetic the iterates are GMRES's. nu = inf gives the
    residual directions only.
    coef: the coefficients c and the orthogonalization's in double-double ("dd", the default: c = (w.r) / (w.w) and
    beta = (W.w) / (W.W), the dot products by dd_dot and the quotients in double-double, each coefficient applied as two
    f64 updates), or in f64 from the vectors rounded to f64 with |w| = 1 assumed ("f64", fewer operations). w is scaled
    by the f64 1 / |w|, so w.w = 1 only to about 2^-53, and with f64 coefficients each update leaves a component of
    about 2^-53 |r| along its direction in r, which the later directions, orthogonal to it, never remove: x then stalls
    near f64 accuracy relative to b, which a Newton step tolerates and a double-double solve does not.
    Stopping is on the change of x, not on the residual (an error along a weak direction of A barely shows in the
    residual): the loop ends after `confirm` iterations in a row with |c u| <= step_tol |x|, each of which reduced |r|
    by the factor nu, or left it at most max(step_tol, n u) |b| with a nonzero step, u the unit roundoff of the
    coefficients (2^-104 with "dd", 2^-52 with "f64"). An iteration in which GMRES stagnates leaves x unchanged without
    having converged, while r at its rounding floor stops falling once x has; an exactly zero step is stagnation even
    below the floor. The loop also ends, converged, when r is exactly zero, and, not converged, after max_products
    products or when a direction's image vanishes. The first iteration's u is M^-1 b, the plain preconditioned solve.
    The default step_tol asks for x to double-double accuracy; inside a Newton iteration, whose steps need far less, a
    step_tol of 1e-10 saves products.
    ref (optional, a double-double vector): the exact solution, for checks: info["errors"] gets |x - ref| / |ref|
    after each iteration.
    Returns (xh, xl, info): info = dict(products, changes, converged, t_prod, t_solve, errors)."""
    if coef not in ("dd", "f64"):
        raise ValueError(f"coef must be 'dd' or 'f64', not {coef!r}")

    def dot(ah, al, bh_, bl_, a64, aa):
        """(a.b) / aa in double-double, aa = a.a (dd), or a64.b in f64"""
        if coef == "dd":
            return _dd_div(dd_dot(ah, al, bh_, bl_), aa)
        return float(a64 @ (bh_ + bl_)), 0.0

    def axpy(c, xh_, xl_, yh_, yl_):
        yh_, yl_ = dd_axpy(c[0], xh_, xl_, yh_, yl_)
        return dd_axpy(c[1], xh_, xl_, yh_, yl_) if c[1] != 0.0 else (yh_, yl_)

    n = len(bh)
    xh, xl = np.zeros(n), np.zeros(n)
    rh, rl = np.asarray(bh, dtype=float).copy(), np.asarray(bl, dtype=float).copy()
    U, W, W64, WW = [], [], [], []
    info = {"products": 0, "changes": [], "converged": False, "t_prod": 0.0, "t_solve": 0.0}
    if ref is not None:
        info["errors"] = []
        refv = np.asarray(ref[0]) + np.asarray(ref[1])
    # the residual reached with step_tol, or at most the coefficients' rounding floor, n times their unit roundoff
    rn = float(np.linalg.norm(rh + rl))
    floor = rn * max(step_tol, n * (2.0 ** -104 if coef == "dd" else 2.0 ** -52))
    # whether the last iteration reduced |r| by the factor nu; the first takes the residual
    fell = True
    run = 0
    while True:
        if rn == 0.0:
            info["converged"] = True
            break
        if rn != rn or info["products"] >= max_products:
            break
        sh, sl = (rh, rl) if fell or not W else W[-1]
        t = time.time()
        uh, ul = (np.asarray(a) for a in precond(np.ascontiguousarray(sh), np.ascontiguousarray(sl)))
        info["t_solve"] += time.time() - t
        t = time.time()
        wh, wl = (np.asarray(a) for a in apply(uh, ul))
        info["t_prod"] += time.time() - t
        info["products"] += 1
        for _ in range(2):
            for (Uh, Ul), (Wh, Wl), w64, ww in zip(U, W, W64, WW):
                beta = dot(Wh, Wl, wh, wl, w64, ww)
                nb = (-beta[0], -beta[1])
                wh, wl = axpy(nb, Wh, Wl, wh, wl)
                uh, ul = axpy(nb, Uh, Ul, uh, ul)
        nw = float(np.linalg.norm(wh + wl))
        # a vanished image with r nonzero: not converged
        if not nw > 0:
            break
        wh, wl = dd_scale(wh, wl, 1.0 / nw)
        uh, ul = dd_scale(uh, ul, 1.0 / nw)
        w64 = wh + wl
        ww = dd_dot(wh, wl, wh, wl) if coef == "dd" else None
        c = dot(wh, wl, rh, rl, w64, ww)
        xh, xl = axpy(c, uh, ul, xh, xl)
        rh, rl = axpy((-c[0], -c[1]), wh, wl, rh, rl)
        rn1 = float(np.linalg.norm(rh + rl))
        fell = rn1 <= nu * rn
        # at its rounding floor r stops falling without stagnating, but its steps still move x; a zero step is
        # stagnation at any residual, since an error along a weak direction of A barely shows in r
        counts = fell or (rn1 <= floor and c[0] != 0.0)
        rn = rn1
        U.append((uh, ul))
        W.append((wh, wl))
        W64.append(w64)
        WW.append(ww)
        ch = abs(c[0]) * float(np.linalg.norm(uh + ul)) / max(float(np.linalg.norm(xh + xl)), 1e-300)
        info["changes"].append(ch)
        if ref is not None:
            info["errors"].append(float(np.linalg.norm((xh - ref[0]) + (xl - ref[1])) / np.linalg.norm(refv)))
        if verbose:
            err = f", error {info['errors'][-1]:.1e}" if ref is not None else ""
            print(f"    gcr {len(U)}: change {ch:.1e}{err}", flush=True)
        run = run + 1 if (len(U) > 1 and counts and ch <= step_tol) else 0
        if run >= confirm:
            info["converged"] = True
            break
    return xh, xl, info
