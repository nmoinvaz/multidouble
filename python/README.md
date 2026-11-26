# multidouble for Python

Double-double arithmetic on numpy arrays, backed by the Rust crate [multidouble](https://github.com/nmoinvaz/multidouble).
A double-double array is a pair of float64 arrays `(hi, lo)` whose elementwise sum `hi + lo` carries about 32
significant digits.

```python
import numpy as np
import multidouble as md

ah, al = np.array([1.0, 2.0]), np.zeros(2)
bh, bl = np.array([3.0, 3.0]), np.zeros(2)
qh, ql = md.div(ah, al, bh, bl)          # 1/3 and 2/3 to about 32 digits
xh, xl = md.dd_solve(np.eye(2) * 2, np.zeros((2, 2)), qh, ql)
print(md.isa())                           # the SIMD backend in use, detected at run time
```

- `add`, `sub`, `mul`, `div(ah, al, bh, bl)`: elementwise, any length, 8 lanes at a time on the best SIMD backend the
  CPU has (AVX-512, AVX2, SSE2, NEON or plain), bitwise the same results on every backend; `dd_op(op, ...)` with op 0
  add, 1 mul, 2 div, 3 sub.
- `dd_dot(xh, xl, yh, yl)`: a dot product in double-double, 8 lanes at a time and then the lane sums, to about
  (n / 8 + 12) 2^-106 of sum |x_i y_i|; returns (hi, lo) as floats.
- `dd_matvec(Ah, Al, vh, vl)`: A v in double-double, A as (n, m) row-major hi and lo arrays, each row of the result
  a `dd_dot`.
- `dd_matmul(Ah, Al, Bh, Bl)`: A B in double-double, A as (n, m) and B as (m, k) hi and lo arrays, each entry a
  `dd_dot` of a row of A and a column of B, so column j is bitwise `dd_matvec(A, B[:, j])`.
- `dd_horner(ch, cl, a)`: sum_k c_k a^k by Horner's rule in double-double at a float a, the coefficients c_0, ..., c_N
  as sequences of N + 1 hi and lo arrays of one length n or as (N + 1, n) arrays, each step `dd_add(c_k, dd_scale(p,
  a))` bit for bit, 8 values at a time; returns the (hi, lo) arrays of the n sums. Float64 powers a**k would carry
  about 2^-53 of each term unless a is a power of two.
- `dd_solve(Ah, Al, bh, bl)`: x with A x = b by LU with partial pivoting, A as (n, n) row-major hi and lo arrays.
  `DDLu(Ah, Al, par=False)` factors A once (each entry the exact sum of its two parts), and `DDLu.factor_f64(a)` factors
  a float64 matrix in f64 (lo = 0), the preconditioner of a mixed-precision solve. Their `solve(bh, bl,
  transpose=False, par=False)` solves A x = b (or A^T x = b) in double-double for b of shape (n,) or (n, k), k
  right-hand sides eight to a lane vector, each column bitwise its own solve. With the factors of `DDLu(Ah, Al)`,
  normalized parts and `transpose=False` it gives the bits of `dd_solve`. Both raise `ValueError` for a singular A and
  for entries that are not finite.
- `qd_solve(a0, a1, a2, a3, b0, b1, b2, b3)`: x with A x = b by LU with partial pivoting in quad-double, A as four
  (n, n) part arrays and b as four part arrays of shape (n,) or (n, k) (k right-hand sides), each entry the exact sum of
  its parts in any order; returns the four parts of x, of b's shape, to about cond(A) 2^-209. `QDLu(a0, a1, a2, a3)`
  factors A once, and its `solve(b0, b1, b2, b3, transpose=False)` gives the bits of `qd_solve` (or solves A^T x = b)
  without factoring again. Both raise `ValueError` for a singular A and for entries that are not finite.
- `dd_logdet(Ah, Al, par=False, control="none")`, `qd_logdet(a0, a1, a2, a3, par=False, control="none")`: the sign and ln|det A| of a real square
  matrix by the LU of `dd_solve` or `qd_solve`, returned with the smallest and largest pivot magnitude as four floats
  `(sign, logabsdet, min_pivot, max_pivot)`. A float64 matrix `a` is `(a, zeros)` or `(a, zeros, zeros, zeros)`. The
  factors are those of a matrix within about n 2^-106 |L| |U| of A (n 2^-209 in quad-double), so the sign is that of
  det A unless A is that close to a singular matrix, against n 2^-53 |L| |U| for numpy's float64 `slogdet`. ln|det A|
  is a float64 sum of the ln|u_kk|. `par=True` updates the trailing columns on rayon's threads (`RAYON_NUM_THREADS`
  sets how many), with the same bits. `control` breaks the LU for tests' controls: `"no_pivot"` (no row interchanges),
  `"no_swap_sign"` (the sign without its flip per interchange) and, for `qd_logdet`, `"update_dd"` (every trailing
  update rounded to double-double). Both raise `ValueError` for a singular A (an exactly zero pivot), for entries that
  are not finite and for an unknown control.
- `ruiz_pow2(a, iters=40)`: integer row and column scalings r, c by Ruiz's iteration in the max norm, powers of two
  chosen without libm (np.frexp), so that diag(2^r) A diag(2^c) has max norm in [1/2, 2) in every nonzero row and
  column; `scale_pow2(r, c, *parts)` applies them to every part of a matrix exactly (raising `ValueError` where an
  entry would overflow or lose bits). Before `dd_logdet` or `qd_logdet` of the scaled matrix S,
  ln|det A| = ln|det S| - (sum r + sum c) ln 2.
- `qd_add_dd(z0, z1, z2, z3, dh, dl)`: a quad-double array (four float64 arrays, each element the exact sum of its
  parts in any order) plus a double-double one, elementwise in quad-double; returns the four parts of the sum.
- `qd_axpy(a, x0, x1, x2, x3, y0, y1, y2, y3)`: y + a x for quad-double arrays x and y (normalized parts) and a
  float a, elementwise in quad-double; returns the four parts.
- `qd_add`, `qd_sub`, `qd_mul`, `qd_div(a0, a1, a2, a3, b0, b1, b2, b3)`: elementwise quad-double operations, each
  element's four parts in any order (renormalized first), 8 elements at a time on the best SIMD backend and bitwise
  the same per element on every backend; `qd_op(op, ...)` with op 0 add, 1 mul, 2 div, 3 sub. Each returns the four
  normalized parts.
- `od_solve(a0, ..., a7, b0, ..., b7)`: x with A x = b by LU with partial pivoting in octo-double (eight parts,
  about 126 digits), A as eight (n, n) part arrays and b as eight of shape (n,) or (n, k), each entry the exact sum of
  its parts in any order; returns the eight parts of x, to about cond(A) 2^-418. `ODLu(a0, ..., a7)` keeps the factors for several solves, `solve(b0, ..., b7,
  transpose=False)`.
- `od_add_dd(z0, ..., z7, dh, dl)`: an octo-double array (eight float64 arrays, each element the exact sum of its
  parts in any order) plus a double-double one, elementwise in octo-double; returns the eight parts of the sum.
- `od_axpy(a, x0, ..., x7, y0, ..., y7)`: y + a x for octo-double arrays x and y (normalized parts) and a float a,
  elementwise in octo-double; returns the eight parts.
- The array arguments of the functions above may be any arrays or sequences of real numbers, strided, in Fortran order
  or of another numeric dtype. Each is converted to a C-contiguous float64 array (`np.ascontiguousarray`), and one that
  is already so is passed on without a copy. Complex, string, `None` and masked inputs raise `TypeError`.
- In numpy (plain float64 expressions): `two_sum`, `two_prod` (Dekker), `dd_add`, `dd_scale` (times an f64),
  `dd_axpy` (y + a x), `dd_norm` (max |hi + lo|).
- From and to mpmath numbers (needs mpmath): `parts_from_mp(v, n)`, the n part arrays of the greedy expansion, each
  part the float64 nearest to what the parts before leave, the remainders formed exactly whatever the working
  precision; `dd_from_mp`, `qd_from_mp` and `od_from_mp` with 2, 4 and 8 parts; `mp_from_parts(*parts)`, their exact
  sums.
- `gcr(apply, precond, bh, bl)`: x with A x = b in double-double by right-preconditioned GMRES in its GCR form, given
  `apply(uh, ul)`, the product A u in double-double, and `precond(rh, rl)`, an approximate solve such as an f64 LU of
  A: the refinement of a mixed-precision solve to double-double accuracy (`coef="f64"` keeps the coefficients in
  float64, which is cheaper and stalls near float64 accuracy, enough inside a Newton iteration).

## Build and test

Needs a Rust toolchain (1.89 or later).

```sh
pip install ./python                    # from the repository root, builds with maturin
pip install pytest mpmath && pytest python/tests
```

The tests compare every operation with exact rational arithmetic (`fractions.Fraction`) or with mpmath at more digits
than the result holds, and contain controls that feed the same checks a wrong result.
