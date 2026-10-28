"""Double-double arithmetic on numpy arrays.

A double-double array is a pair of float64 arrays (hi, lo) with value hi + lo elementwise (about 32 significant digits).

Backed by the Rust crate multidouble, on the best SIMD backend the CPU has (``isa()``):

- ``add``, ``sub``, ``mul``, ``div``: elementwise operations; ``dd_op(op, ...)`` with op 0 add, 1 mul, 2 div, 3 sub;
- ``dd_dot``: a dot product in double-double (8 lanes at a time, then the lane sums), to about (n / 8 + 12) 2^-106 of
  sum |x_i y_i|;
- ``dd_matvec``: A v in double-double, each row a ``dd_dot``;
- ``dd_solve``: x with A x = b by LU with partial pivoting, A and b in double-double;
- ``qd_add_dd``: a quad-double array (four float64 arrays) plus a double-double one, elementwise in quad-double;
- ``qd_axpy``: y + a x for quad-double arrays x, y and a float a, elementwise in quad-double.

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

from ._multidouble import add, dd_matvec, dd_op, dd_solve, div, isa, mul, qd_add_dd, qd_axpy, sub
from ._multidouble import dd_dot as _dd_dot

__all__ = ["add", "sub", "mul", "div", "dd_op", "dd_matvec", "dd_solve", "qd_add_dd", "qd_axpy", "isa", "two_sum",
           "two_prod", "dd_add", "dd_scale", "dd_axpy", "dd_norm", "dd_from_mp", "dd_dot", "gcr"]


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
    a = [np.ascontiguousarray(v, dtype=np.float64) for v in (xh, xl, yh, yl)]
    return _dd_dot(*a)


def _dd_div(a, b):
    """a / b for double-double scalars a = (hi, lo), b = (hi, lo): the f64 quotient q, then (a - q b) / b, to about
    2^-104 relative"""
    q = a[0] / b[0]
    p, e = two_prod(np.float64(q), np.float64(b[0]))
    r = (((a[0] - p) - e) + a[1]) - q * b[1]
    q2 = r / b[0]
    h = q + q2
    return float(h), float(q2 - (h - q))


def gcr(apply, precond, bh, bl, max_products=30, step_tol=1e-28, confirm=1, ref=None, verbose=False, coef="dd"):
    """x with A x = b, b = bh + bl in double-double: GMRES on A M^-1 (right preconditioning; Saad and Schultz, SIAM J.
    Sci. Stat. Comput. 7 (1986) 856, doi:10.1137/0907058) in its GCR form (Eisenstat, Elman and Schultz, SIAM J.
    Numer. Anal. 20 (1983) 345, doi:10.1137/0720023). apply(uh, ul) returns A u in double-double as (hi, lo) (the
    products must be exact to double-double for the result to be); precond(rh, rl) returns M^-1 r as (hi, lo), M an
    approximation of A such as its f64 LU. Each iteration takes the preconditioned residual u = M^-1 r as the new
    direction, w = A u (one product), orthogonalizes w against the earlier w's (twice), applying the same coefficients
    to u, and updates x += c u, r -= c w with c = w.r. The u, w, x and r are double-double and updated with the same
    coefficients, so r stays the residual b - A x to double-double rounding without recomputing it. In exact
    arithmetic the iterates are GMRES's.
    coef: the coefficients c and the orthogonalization's in double-double ("dd", the default: c = (w.r) / (w.w) and
    beta = (W.w) / (W.W), the dot products by dd_dot and the quotients in double-double, each coefficient applied as two
    f64 updates), or in f64 from the vectors rounded to f64 with |w| = 1 assumed ("f64", fewer operations). w is scaled
    by the f64 1 / |w|, so w.w = 1 only to about 2^-53, and with f64 coefficients each update leaves a component of
    about 2^-53 |r| along its direction in r, which the later directions, orthogonal to it, never remove: x then stalls
    near f64 accuracy relative to b, which a Newton step tolerates and a double-double solve does not.
    Stopping is on the change of x, not on the residual (an error along a weak direction of A barely shows in the
    residual): the loop ends after `confirm` iterations in a row with |c u| <= step_tol |x|, or after max_products
    products. The first iteration's u is M^-1 b, the plain preconditioned solve. The default step_tol asks for x to
    double-double accuracy; inside a Newton iteration, whose steps need far less, a step_tol of 1e-10 saves products.
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
    run = 0
    while info["products"] < max_products:
        t = time.time()
        uh, ul = (np.asarray(a) for a in precond(np.ascontiguousarray(rh), np.ascontiguousarray(rl)))
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
        if not nw > 0:
            break
        wh, wl = dd_scale(wh, wl, 1.0 / nw)
        uh, ul = dd_scale(uh, ul, 1.0 / nw)
        w64 = wh + wl
        ww = dd_dot(wh, wl, wh, wl) if coef == "dd" else None
        c = dot(wh, wl, rh, rl, w64, ww)
        xh, xl = axpy(c, uh, ul, xh, xl)
        rh, rl = axpy((-c[0], -c[1]), wh, wl, rh, rl)
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
        run = run + 1 if (len(U) > 1 and ch <= step_tol) else 0
        if run >= confirm:
            info["converged"] = True
            break
    return xh, xl, info
