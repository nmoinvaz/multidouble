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
- `dd_solve(Ah, Al, bh, bl)`: x with A x = b by LU with partial pivoting, A as (n, n) row-major hi and lo arrays.
- `qd_add_dd(z0, z1, z2, z3, dh, dl)`: a quad-double array (four float64 arrays, renormalized first) plus a
  double-double one, elementwise in quad-double; returns the four parts of the sum.
- In numpy (plain float64 expressions): `two_sum`, `two_prod` (Dekker), `dd_add`, `dd_scale` (times an f64),
  `dd_axpy` (y + a x), `dd_norm` (max |hi + lo|), `dd_from_mp` (from mpmath numbers; needs mpmath), `dd_dot` (a dot
  product in double-double).
- `gcr(apply, precond, bh, bl)`: x with A x = b in double-double by right-preconditioned GMRES in its GCR form, given
  `apply(uh, ul)`, the product A u in double-double, and `precond(rh, rl)`, an approximate solve such as an f64 LU of
  A: the refinement of a mixed-precision solve to double-double accuracy (`coef="f64"` keeps the coefficients in
  float64, which is cheaper and stalls near float64 accuracy, enough inside a Newton iteration).

## Build and test

Needs a Rust toolchain (1.89 or later).

```sh
pip install ./python                    # from the repository root, builds with maturin
pip install pytest && pytest python/tests
```

The tests compare every operation with exact rational arithmetic (`fractions.Fraction`) and contain controls that feed
the same checks a wrong result.
