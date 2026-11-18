import json
body = """Two findings, in the comments and the documented error. The arithmetic and the lanes hold on everything I ran.

## Checked

- `QV::sqrt` against `QD::sqrt` operation by operation, the inlined `DD::sqrt` among them. The lanes skip `DD::sqrt`'s branches for zero, negative, infinite and small `hi`, which is sound: a0 is in [1, 4) after the scaling, and the other lanes are NaN or selected to zero.
- 1.6 million lane square roots with exponents from 2^-1060 to 2^1040 and zero lanes mixed in: bit for bit with the scalar, on NEON and on the portable backend.
- Zero, negative zero, negatives, infinities, NaN, subnormals, `f64::MAX` with a full tail: the same results as main's square root (NaN in every part for negative, infinite and NaN inputs, as before), and the lanes match the scalar.
- Accuracy against exact arithmetic on 1.2 million inputs chosen where the double-double start is worst (a0 just above 1, above 2 and below 4, a1 near half an ulp), against main's three Newton steps on the same inputs:

| a0 | worst, this PR | worst, main | worst start |
|---|---|---|---|
| anywhere in [1, 4) | 3.17 u⁴ | 4.09 u⁴ | 2.95 u² |
| just above 1 | 4.93 u⁴ | 4.08 u⁴ | 3.37 u² |
| just above 2 | 2.77 u⁴ | 4.84 u⁴ | 2.58 u² |
| just below 4 | 1.79 u⁴ | 3.19 u⁴ | 1.61 u² |

The test's threshold is 32 u⁴. Each number is the worst of 300,000 inputs, not a bound.

- Leading parts that are not a double-word pair, which `DD::sqrt`'s theorem needs and #79 restores with a quick two-sum: with |a1| up to a whole ulp of a0 the worst is 3.5 u⁴ (main 5.8 u⁴), so no two-sum is needed here for the parts a sum's renormalization leaves. Far outside QD's contract the new root loses more than the old one (|a1| up to 1,024 ulp: 7·10⁵ u⁴ against 7·10³ u⁴).

## Ran

| build | passed | failed |
|---|---|---|
| `cargo test --release` | 236 | 0 |
| `--features portable` | 236 | 0 |
| `--features mutate` | 250 | 0 |

The diff touches only the two `sqrt` bodies, so the re-pinned digests can hide no change of another operation. I did not rerun the benchmarks.

The scripts are on the branch `wip/fable-review`, folder `fable-review/pr78`."""
comments = [
 dict(path="src/qd.rs", line=737, side="RIGHT", body="""1. **gap**: "The error left is cubic in y's" holds for the truncation only, about 2^-310. It is not the result's error, and the doc comment above and the PR body repeat it.

The correction t is formed in double-double, so the result keeps |e| times t's relative error, with e the start's error:

- |e| ≤ 25/8 u² + 1/2 u² (the two parts a2 + a3 that the start does not see);
- t's relative error is at most u² from `to_dd` plus that of the double-double `/`.

| double-double `/` | bound on the result |
|---|---|
| 2.2 u², the worst I measured on 400,000 quotients | 11.6 u⁴ |
| 8 u², the threshold `tests/dd.rs` checks | 32.6 u⁴ |

The second is past the 32 u⁴ this square root is tested against, so the threshold now leans on the measured accuracy of a divide that has no proven bound. Main's steps were formed in quad-double throughout. Measured, the two are alike (4.93 u⁴ against 4.84 u⁴, review body), so this is a statement to correct and a margin to know, not a wrong result.

```diff
-        // one Newton step with its second-order term: sqrt(y^2 + r) = y + t - t^2 / (2 y) + O(t^3 / y^2) with
-        // t = r / (2 y), so the error left is cubic in y's
+        // one Newton step with its second-order term: sqrt(y^2 + r) = y + t - t^2 / (2 y) + O(t^3 / y^2) with
+        // t = r / (2 y). The truncation is cubic in y's error e. The result's error is the rounding of t, formed
+        // in double-double: |e| times t's relative error, a few u^4.
```"""),
 dict(path="src/qd.rs", line=10, side="RIGHT", body="""2. **nit**: This line is 134 characters, and `src/qd_tests.rs:1156` is 155, past the 120 of `rustfmt.toml`, which does not wrap comments. Both need a manual rewrap."""),
]
json.dump(dict(commit_id="2734d44adf3211cee81a8034a0c7cf9a23203ed3", event="COMMENT", body=body, comments=comments), open("pr78.json", "w"), indent=1)
