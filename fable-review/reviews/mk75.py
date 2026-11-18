import json
body = """One nit. The rewrite gives `QD::ieee_add`'s bits on everything I ran.

## Checked

- The loop against `QD::ieee_add` branch by branch: the two first reads, the read order with one input exhausted, the stop after eight reads and after four emissions, the placement of u and v by k after the loop, and the fifth term's order of additions (a's unread parts first, in order, then b's).
- The check skipped before the fourth step: four emissions take four steps and eight reads take six, so no lane is done before then.
- A differential test of every lane against `QD::ieee_add`, bit for bit, on 3.2 million sums per backend (NEON and portable) with gaps, zero parts, overlapping and equal parts, cancellation to every depth, infinities, NaN and subnormals, and the exits mixed across the lanes of one call. No mismatch.

| exit of the merge | sums |
|---|---|
| all parts read, k = 0 emitted | 821,031 |
| all parts read, k = 1 | 522,273 |
| all parts read, k = 2 | 919,447 |
| all parts read, k = 3 (v as fifth term) | 602,716 |
| four emitted, 0 parts unread | 180,696 |
| four emitted, 1 unread | 137,158 |
| four emitted, 2 unread | 16,679 |

Four emissions take six reads, so two unread parts is the most there can be.

## Ran

| build | passed | failed |
|---|---|---|
| `cargo test --release` | 236 | 0 |
| `--features portable` | 236 | 0 |
| `--features mutate` | 250 | 0 |

`lanes neon/qv ieee_add` on an Apple M-series laptop under load, two interleaved runs per version, µs per pass:

| | main | this PR | change |
|---|---|---|---|
| NEON | 48.7, 51.0 | 38.8, 40.6 | −20% |
| portable | 136.5, 131.4 | 115.7, 106.7 | −17% |

That is a cut, smaller here than the 28% quoted.

The test is `fable-review/pr75/fable_ieee.rs` on the branch `wip/fable-review`, if it is worth keeping."""
comments = [
 dict(path="src/qv.rs", line=386, side="RIGHT", body="""1. **nit**: The comment explains the queue by `pick(&a, i)`, which this PR removes, so it describes what the code did before.

```diff
-                // a's and b's parts not yet read, as queues: qa[0] is the next part of a (pick(&a, i)); a
-                // read shifts the queue and fills it with zeros
+                // a's and b's parts not yet read, as queues: qa[0] is a[i], the next part of a, and qb[0] is b[j]. A
+                // read shifts its queue and fills it with zeros.
```"""),
]
json.dump(dict(commit_id="6126cf087cb7e024288cdefccd5d360620b0795b", event="COMMENT", body=body, comments=comments), open("pr75.json", "w"), indent=1)
