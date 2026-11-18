import json
body = """Four findings, none in the arithmetic.

## Checked

- `DD::sloppy_div` step by step against DWDivDW2 and DWTimesFP1 (Algorithms 17 and 7) as I know them. HAL refused the fetch of the paper from here, so this is not a reading against the source.
- `DV::sloppy_div` against the scalar, operation by operation. The order and the roundings are the same.
- 400,000 quotients against exact arithmetic, both operands just above or below a power of two with low parts near half an ulp. The worst is 7.708 u², inside 15 u² + 56 u³. `/` has 2.186 u² on the same inputs.
- 144 pairs of special values (zeros, infinities, NaN, subnormals, near overflow). The lanes match the scalar bit for bit on all. The class of the result is that of `/` on all but a zero quotient's sign (finding 4).

## Ran

| build | passed | failed |
|---|---|---|
| `cargo test --release` | 238 | 0 |
| `--features portable` | 238 | 0 |
| `--features mutate` | 252 | 0 |

Benchmarks on an Apple M-series laptop under load, ns per quotient at 1,024 quotients per pass. The quoted changes reproduce.

| | `/` | `sloppy_div` | change | PR body |
|---|---|---|---|---|
| scalar, dependent chain | 51.5 | 17.8 | −66% | −62% |
| scalar, independent | 12.1 | 2.12 | −83% | −84% |
| `DV` on NEON, independent | 4.69 | 1.24 | −74% | −73% |

The scripts are on the branch `wip/fable-review`, folder `fable-review/pr74`."""
comments = [
 dict(path="tests/dd.rs", line=138, side="RIGHT", body="""1. **gap**: The low part of the divisors near a power of two has the wrong scale, so this half of the test is weaker than its comment says.

`r.dd(20).lo` carries its own exponent in ±20, and `r.dd(20).lo * p2(k)` is then not within half an ulp of `p2(k) (1 ± 2^-j)`. Of the 10,000 such divisors, `DD::new` moves `hi` off 2^k (1 ± 2^-j) on 4,822, and 4,109 have |lo| ≥ ulp(hi)/8.

| low part | worst of the 20,000 quotients |
|---|---|
| `r.dd(20).lo * p2(k)` (this PR) | 4.872 u² |
| `r.dd(0).lo * p2(k)`, same seed | 6.856 u² |
| both operands near a power of two, low parts near half an ulp, 400,000 quotients | 7.708 u² |

All are inside the bound.

```diff
-            DD::new(p2(k) * (1.0 + s * p2(-j)), r.dd(20).lo * p2(k))
+            DD::new(p2(k) * (1.0 + s * p2(-j)), r.dd(0).lo * p2(k))
```"""),
 dict(path="tests/dd.rs", line=155, side="RIGHT", body="""2. **nit**: The control's quotient is wrong by about u, 2^53 u². It shows the check can fail, but it would also fire with the bound set to 10^15 u², so it does not tie the threshold to 15 u². A second control at the scale of the bound would: the quotient with its low part moved by 32 u² of the quotient has an error of at least 17 u², by the theorem, and must fail."""),
 dict(path="src/dd.rs", line=120, side="RIGHT", body="""3. **nit**: The name reads differently here than in `QD`. `QD::sloppy_div` is QD's default `/` (`qd.rs`: "`/` the sloppy divide"), with `accurate_div` the other. `DD::sloppy_div` is not DD's `/`, and it is the less accurate of the two (7.7 u² against 2.2 u² measured). A reader who knows the quad-double names will take `DD::sloppy_div` for `/`. A name of its own, such as `div2` or `fast_div`, avoids that."""),
 dict(path="src/dd.rs", line=128, side="RIGHT", body="""4. **nit**: A zero quotient of a negative divisor has `lo = -0.0`: `DD::ZERO.sloppy_div(DD::new(-3.0, 1e-17))` is `DD { hi: -0.0, lo: -0.0 }`, and so is 5e-324 over it. `Neg` documents the canonical form as a low part that never carries a negative zero, and `/` returns `DD { hi: 0.0, lo: 0.0 }` there. The values compare equal, the bits do not. Either add `+ 0.0` to the low part in both `DD` and `DV`, or say in the doc comment that a zero quotient's low part takes the sign of the quotient."""),
]
json.dump(dict(commit_id="479ee4fb22b38c31d55ce605464a6e6eab9cb0f2", event="COMMENT", body=body, comments=comments), open("pr74.json", "w"), indent=1)
