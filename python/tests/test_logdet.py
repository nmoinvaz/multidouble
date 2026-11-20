"""Tests of dd_logdet and qd_logdet, the sign and ln|det A| of a real matrix by the double-double and the quad-double
LU, against mpmath at 200 digits on the exact entries (about 660 bits, more than the 212 of four parts). The controls
break the LU through the binding's control argument (no pivoting, the sign without its flips for the row interchanges,
the quad-double updates rounded to double-double) and feed numpy's float64 slogdet to the same checks."""
import numpy as np
import pytest

import multidouble as md

mp = pytest.importorskip("mpmath")
DPS = 200


def mp_matrix(parts):
    """the exact entries of A, given as part arrays whose entrywise sums they are, as an mpmath matrix"""
    n = parts[0].shape[0]
    with mp.workdps(DPS):
        return mp.matrix([[mp.fsum(mp.mpf(float(p[i, j])) for p in parts) for j in range(n)] for i in range(n)])


def mp_logdet(parts):
    """(sign, ln|det A|) of A's exact entries, by mpmath's determinant at 200 digits"""
    with mp.workdps(DPS):
        d = mp.det(mp_matrix(parts))
        return (1.0 if d > 0 else -1.0), float(mp.log(abs(d)))


def mp_pivot_range(parts):
    """min and max |u_kk| of LU with partial pivoting (getf2) of A's exact entries at 200 digits"""
    with mp.workdps(DPS):
        a, n = mp_matrix(parts), parts[0].shape[0]
        piv = []
        for k in range(n):
            p = max(range(k, n), key=lambda i: abs(a[i, k]))
            for j in range(n):
                a[k, j], a[p, j] = a[p, j], a[k, j]
            piv.append(abs(a[k, k]))
            for i in range(k + 1, n):
                m = a[i, k] / a[k, k]
                for j in range(k + 1, n):
                    a[i, j] -= m * a[k, j]
        return float(min(piv)), float(max(piv))


def ln_tol(n, res):
    """the float64 rounding that ln|det A| may carry, n 2^-52 (1 + n max_k |ln|u_kk||), from the result's pivot range:
    twice the n 2^-53 (1 + sum_k |ln|u_kk||) of the docstrings"""
    return n * 2.0**-52 * (1 + n * max(abs(np.log(res[2])), abs(np.log(res[3]))))


def agrees(res, ref, tol):
    """the result's sign is the reference's and its ln|det A| is within tol of the reference's"""
    return res[0] == ref[0] and abs(res[1] - ref[1]) <= tol


def zeros_like(a, k):
    return [np.zeros_like(a) for _ in range(k)]


def rand_parts(rng, n, k):
    """a random (n, n) matrix as k normalized part arrays (standard normal leading parts, each next part a random
    fraction of half an ulp of the one before), with a diagonal shift for good conditioning"""
    parts = [rng.standard_normal((n, n)) + np.sqrt(n) * np.eye(n)]
    for _ in range(k - 1):
        prev = parts[-1]
        parts.append(rng.uniform(-1, 1, (n, n)) * np.abs(prev) * 2.0**-54)
    return parts


def test_logdet_of_random_matrices_against_mpmath():
    """dd_logdet of random float64 matrices (a, 0) and of double-double ones, and qd_logdet of quad-double ones, of
    orders 1, 2, 7, 8, 37 and 100 (which takes the blocked double-double LU): the sign is mpmath's and ln|det A| is
    within ln_tol of its, for n up to 37 min and max |u_kk| are those of mpmath's partial-pivoting LU to 1e-14, and
    par=True gives the same bits. Control: with the sign's flips for the row interchanges dropped ("no_swap_sign"),
    the check fails on the matrices with an odd number of interchanges, of which there are some."""
    misses = 0
    for n in (1, 2, 7, 8, 37, 100):
        rng = np.random.default_rng(100 + n)
        cases = [("dd", [rng.standard_normal((n, n)), np.zeros((n, n))]), ("dd", rand_parts(rng, n, 2)),
                 ("qd", rand_parts(rng, n, 4))]
        for kind, parts in cases:
            f, raw = getattr(md, f"{kind}_logdet"), getattr(md._md, f"{kind}_logdet")
            res, ref = f(*parts), mp_logdet(parts)
            print(f"n {n} {kind}: {res[:2]}, ln error {abs(res[1] - ref[1]):.1e} of {ln_tol(n, res):.1e}")
            assert agrees(res, ref, ln_tol(n, res)), (n, kind, res, ref)
            if n <= 37:
                want = mp_pivot_range(parts)
                assert abs(res[2] - want[0]) <= 1e-14 * want[0] and abs(res[3] - want[1]) <= 1e-14 * want[1], (n, kind)
            assert f(*parts, par=True) == res, (n, kind)
            blind = raw(*parts, False, "no_swap_sign")
            misses += not agrees(blind, ref, ln_tol(n, blind))
    print(f"control: the sign without the interchanges' flips misses {misses} of 18")
    assert misses > 0


def test_logdet_parallel_is_serial():
    """at n = 300 the double-double LU's trailing updates run on rayon's threads (they do not below about 150) and so do
    the quad-double ones: par=True gives the serial result bit for bit"""
    rng = np.random.default_rng(7)
    A = rng.standard_normal((300, 300))
    z = np.zeros_like(A)
    assert md.dd_logdet(A, z, par=True) == md.dd_logdet(A, z)
    assert md.qd_logdet(A, z, z, z, par=True) == md.qd_logdet(A, z, z, z)


def near_singular(n, tau, seed):
    """a float64 matrix A = [[B, b], [c^T, d]] (B of order n - 1) whose Schur complement s = d - c^T B^-1 b is tau to
    about 2^-50 relative, so that det A = s det B with |s| far below the float64 rounding of A's entries: B, b and c
    random, then the last three entries of c chosen in turn to cancel t = c^T y, y = B^-1 b in mpmath (each the float64
    nearest -t / y_k, so that |t| falls by about 2^-53 each time, and the entries with it), and d = fl(t + tau). Returns
    A and s, exactly."""
    rng = np.random.default_rng(seed)
    m = n - 1
    B, b, c = rng.standard_normal((m, m)), rng.standard_normal(m), rng.standard_normal(m)
    c[m - 3:] = 0.0
    with mp.workdps(DPS):
        y = mp.lu_solve(mp.matrix(B.tolist()), mp.matrix(b.tolist()))
        t = mp.fsum(mp.mpf(c[k]) * y[k] for k in range(m))
        for k in range(m - 3, m):
            c[k] = float(-t / y[k])
            t += mp.mpf(c[k]) * y[k]
        d = float(t + tau)
        s = mp.mpf(d) - t
    return np.block([[B, b[:, None]], [c[None, :], np.array([[d]])]]), s


def planted(n, tau, seed, wrong):
    """near_singular's matrix of Schur complement +tau or -tau, whichever gives det A the sign opposite to wrong(A), the
    sign a lower precision's LU finds (set by its rounding, so that it does not follow the 2 tau change of d). Returns
    A and its exact (sign, ln|det A|), the planted s checked against it."""
    for t in (tau, -tau):
        A, s = near_singular(n, t, seed)
        ref = mp_logdet([A])
        with mp.workdps(DPS):
            assert ref[0] == (1.0 if s * mp.det(mp.matrix(A[:-1, :-1].tolist())) > 0 else -1.0)
        if wrong(A) != ref[0]:
            return A, ref
    raise AssertionError(f"the lower precision's sign follows tau at n {n}, seed {seed}")


def np_sign(A):
    with np.errstate(all="ignore"):
        return np.linalg.slogdet(A)[0]


def dd_sign(A):
    return md.dd_logdet(A, np.zeros_like(A))[0]


@pytest.mark.parametrize("n,seed", [(12, 1), (40, 2), (100, 3)])
def test_dd_logdet_resolves_what_float64_cannot(n, seed):
    """A float64 matrix with |det A| about 1e-20 det B (one singular value near 1e-20, far below the 2^-53 rounding
    of its entries), planted so that numpy's slogdet, the float64 LU of the same stored entries, gets the sign wrong:
    dd_logdet gets the sign right and ln|det A| within 1e-6, its factorization error being about n 2^-106 / 1e-20 (and
    qd_logdet agrees). Control: numpy's result fails the same check."""
    A, ref = planted(n, 1e-20, seed, np_sign)
    z = np.zeros_like(A)
    res, q = md.dd_logdet(A, z), md.qd_logdet(A, z, z, z)
    with np.errstate(all="ignore"):
        npr = np.linalg.slogdet(A)
    print(f"n {n}: mpmath {ref}, dd {res[:2]}, qd {q[:2]}, numpy {tuple(map(float, npr))}")
    assert agrees(res, ref, 1e-6) and agrees(q, ref, 1e-6)
    assert not agrees((float(npr[0]), float(npr[1])), ref, 1e-6)


def test_dd_logdet_of_a_two_by_two_matrix_float64_rounds_to_singular():
    """A = [[3, 1], [1, fl(1/3)]] has det A = 3 fl(1/3) - 1 = -2^-54 exactly; float64 elimination gives u_22 =
    fl(1/3) - fl(1/3) 1 = 0, so numpy's slogdet reports a singular matrix (sign 0), while dd_logdet and qd_logdet give
    the sign -1 and ln|det A| = -54 ln 2 to 1e-15. Control: numpy's result fails the same check."""
    A = np.array([[3.0, 1.0], [1.0, 1.0 / 3.0]])
    ref = mp_logdet([A])
    assert ref[0] == -1.0 and abs(ref[1] + 54 * np.log(2)) < 1e-14
    z = np.zeros_like(A)
    for res in (md.dd_logdet(A, z), md.qd_logdet(A, z, z, z)):
        assert agrees(res, ref, 1e-15), res
    with np.errstate(all="ignore"):
        npr = np.linalg.slogdet(A)
    assert not agrees((float(npr[0]), float(npr[1])), ref, 1e-15), npr


@pytest.mark.parametrize("n,seed", [(12, 4), (40, 5)])
def test_qd_logdet_resolves_what_dd_cannot(n, seed):
    """A float64 matrix with |det A| about 1e-45 det B, planted so that dd_logdet gets the sign wrong (its
    factorization error, about n 2^-106, exceeds 1e-45): qd_logdet gets the sign right and ln|det A| within 1e-6.
    Control: qd_logdet with every trailing update rounded to double-double ("update_dd") misses the same check."""
    A, ref = planted(n, 1e-45, seed, dd_sign)
    z = np.zeros_like(A)
    res, d = md.qd_logdet(A, z, z, z), md.dd_logdet(A, z)
    bad = md._md.qd_logdet(A, z, z, z, False, "update_dd")
    print(f"n {n}: mpmath {ref}, qd {res[:2]}, dd {d[:2]}, qd with dd updates {bad[:2]}")
    assert agrees(res, ref, 1e-6)
    assert not agrees(d, ref, 1e-6)
    assert not agrees(bad, ref, 1e-6)


@pytest.mark.parametrize("n", [12, 100])
def test_logdet_needs_pivoting(n):
    """A random float64 matrix with its entry (0, 0) replaced by 1.37 2^-300: dd_logdet and qd_logdet agree with
    mpmath (n = 100 takes the blocked double-double LU). Control: without pivoting ("no_pivot") the multipliers reach
    2^300, and each either stops at an exactly zero pivot (ValueError) or misses the check."""
    rng = np.random.default_rng(200 + n)
    A = rng.standard_normal((n, n))
    A[0, 0] = 1.37 * 2.0**-300
    ref = mp_logdet([A])
    for kind, parts in (("dd", [A, np.zeros_like(A)]), ("qd", [A] + zeros_like(A, 3))):
        res = getattr(md, f"{kind}_logdet")(*parts)
        assert agrees(res, ref, ln_tol(n, res)), (kind, res, ref)
        try:
            bad = getattr(md._md, f"{kind}_logdet")(*parts, False, "no_pivot")
        except ValueError as e:
            print(f"n {n} {kind} without pivoting: {e}")
            continue
        print(f"n {n} {kind} without pivoting: {bad[:2]}, mpmath {ref}")
        assert not agrees(bad, ref, ln_tol(n, bad)), kind


def test_logdet_of_a_permutation_matrix():
    """[[0, 1], [1, 0]] has det -1 and needs a row interchange: both give (-1, 0, 1, 1). Control: without pivoting
    the zero pivot raises ValueError."""
    A, z = np.array([[0.0, 1.0], [1.0, 0.0]]), np.zeros((2, 2))
    assert md.dd_logdet(A, z) == (-1.0, 0.0, 1.0, 1.0)
    assert md.qd_logdet(A, z, z, z) == (-1.0, 0.0, 1.0, 1.0)
    with pytest.raises(ValueError, match="singular"):
        md._md.dd_logdet(A, z, False, "no_pivot")
    with pytest.raises(ValueError, match="singular"):
        md._md.qd_logdet(A, z, z, z, False, "no_pivot")


def parity(p):
    """the sign of the permutation p, from its cycles"""
    seen, s = [False] * len(p), 1.0
    for i in range(len(p)):
        j, length = i, 0
        while not seen[j]:
            seen[j], j, length = True, p[j], length + 1
        if length and length % 2 == 0:
            s = -s
    return s


@pytest.mark.parametrize("n", [12, 100])
def test_logdet_sign_follows_row_permutations(n):
    """Row permutations P of a random float64 matrix, odd and even (a transposition, a 3-cycle, a cyclic shift and
    random ones): partial pivoting picks the same pivots in another order, so ln|det PA| and the pivot range are those
    of A bit for bit, and the sign of det PA is parity(P) times that of det A, in both precisions (n = 100 takes the
    blocked double-double LU). The sign of A itself is mpmath's. Control: with the sign's flips for the interchanges
    dropped ("no_swap_sign") the check fails for every odd P."""
    rng = np.random.default_rng(300 + n)
    A = rng.standard_normal((n, n))
    ref = mp_logdet([A])
    t, c3 = list(range(n)), list(range(n))
    t[1], t[n - 2] = t[n - 2], t[1]
    c3[0], c3[1], c3[2] = 1, 2, 0
    perms = [t, c3, [(i + 1) % n for i in range(n)]] + [list(rng.permutation(n)) for _ in range(4)]
    assert {parity(p) for p in perms} == {1.0, -1.0}
    for kind, k in (("dd", 2), ("qd", 4)):
        f, raw = getattr(md, f"{kind}_logdet"), getattr(md._md, f"{kind}_logdet")
        base = f(A, *zeros_like(A, k - 1))
        assert agrees(base, ref, ln_tol(n, base))
        blind = raw(A, *zeros_like(A, k - 1), False, "no_swap_sign")
        for p in perms:
            PA = A[p, :]
            res = f(PA, *zeros_like(A, k - 1))
            assert res == (parity(p) * base[0], *base[1:]), (kind, p)
            b = raw(PA, *zeros_like(A, k - 1), False, "no_swap_sign")
            assert (b == (parity(p) * blind[0], *blind[1:])) == (parity(p) > 0), (kind, p)


def test_logdet_errors():
    """non-square and mismatched shapes, non-finite entries, an exactly singular matrix and an unknown control raise
    ValueError; an empty matrix gives (1, 0, inf, 0)"""
    z3 = np.zeros((3, 3))
    for args in ((np.ones((2, 3)), np.zeros((2, 3))), (np.eye(3), np.zeros((2, 2))),
                 (np.array([[1.0, np.nan], [0.0, 1.0]]), np.zeros((2, 2))),
                 (np.eye(2), np.array([[0.0, np.inf], [0.0, 0.0]])), (z3, z3)):
        with pytest.raises(ValueError):
            md.dd_logdet(*args)
        with pytest.raises(ValueError):
            md.qd_logdet(args[0], args[1], np.zeros_like(args[1]), np.zeros_like(args[1]))
    with pytest.raises(ValueError, match="unknown control"):
        md._md.dd_logdet(np.eye(2), np.zeros((2, 2)), False, "update_dd")
    with pytest.raises(ValueError, match="unknown control"):
        md._md.qd_logdet(*([np.eye(2)] + zeros_like(np.eye(2), 3)), False, "nonsense")
    e = np.zeros((0, 0))
    assert md.dd_logdet(e, e) == (1.0, 0.0, np.inf, 0.0)
    assert md.qd_logdet(e, e, e, e) == (1.0, 0.0, np.inf, 0.0)
