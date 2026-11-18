import json
body = r"""This merged while I was reading it, before #79, so the fixes below need a follow-up. Seven findings: one false constant in the theorem, the merge order, two holes in `sqrt_bits.py`, and three nits. The proof's structure and the script's arithmetic hold.

## Checked

- Theorem 22 line by line. The start: the two-sum's exactness, the double-word pair, d₁ and d₂, the tail ratio τ = ρ²/(1−ρ)², both branches of E₀, and π⁽⁰⁾. The step: c's exact value, the identity (1 + e)(1 + c + 3/2 c²) = 1 + 5/2 e³ + 15/8 e⁴ + 3/8 e⁵ by hand and in exact rationals, γ′, c̄, the five G calls and their Z̄, and every term of E₁. The rest is Theorem 21's step and end.
- `sqrt_dd_consts` and `newton_step` against the statement, term by term: τ, η₁, η₂, E₀, π⁽⁰⁾, the operand order and Z̄ of each `op_bounds` call, `werr`, E₁, and the Newton branch against Theorem 21's formula. They compute what the theorem states. `python3 sqrt_consts.py` reproduces `sqrt_consts.txt`, and the other two scripts their files.
- In exact rationals: E₁ = 2^-303.28 at θ = 2 and 2^-303.91 at θ = 1, and δ^DD = 3.0000318152 u⁸ and 3.0000197071 u⁸, the values of SQRT₈,₄ less 2.4·10⁻²² u⁸.
- `fpemu.od_sqrt` against `alg::sqrt` of #79, operation by operation: the same order.
- `sqrt_bits.py` with a driver built from #79: 2,000 inputs, 0 mismatches. At seed 7: 500 inputs, 0 mismatches. The control: 300 of 300.
- The rebuilt PDF has the committed one's size, and its numbers are those the scripts and `paper/README.md` now cite (Theorems 12, 13, 16, 18, 21, 22, 27, Lemma 20), except finding 7.
- The statements of Theorem 3.5 of Lefèvre et al. and Theorem 7.1 of Joldes et al. are as I know them. HAL refused the fetch from here, so I did not read them against the sources.

The scripts are on the branch `wip/fable-review`, folders `fable-review/pr79` and `fable-review/pr80`."""
comments = [
 dict(path="paper/expansion-error-bounds-appendix.tex", line=604, side="RIGHT", body=r"""1. **bug**: "E₀ ≤ 22.125 u²" is false as stated, and it names no θ. In exact rationals, at p = 53:

| θ | E₀ |
|---|---|
| 1 | 19.125 u² + 58 u³, less a term below 10⁻¹³ u³ |
| 2 | 22.125 u² + 72 u³, less a term below 10⁻¹³ u³ |

The u³ term is 56 from η₂ plus 2θ³ from τ, and the larger branch is the lower one, 1 − (1−τ)(1−η₂)/(1+η₁). The final bounds are computed from the exact E₀, so they stand. `sqrt_consts.py` prints E₀ with `%.6g`, which is why `sqrt_consts.txt` shows 22.125 and 19.125. The PR body quotes the same 22.125 u².

```diff
-\mathrm{SQRT}^{\rm DD}_n(x)_k| \le \delta^{\rm DD}\sqrt x$. At $n = 8$, $p = 53$: $E_0 \le 22.125\,u^2$, $E_1 \le 2^{-303}$, and
+\mathrm{SQRT}^{\rm DD}_n(x)_k| \le \delta^{\rm DD}\sqrt x$. At $n = 8$, $p = 53$: $E_0 \le 22.125\,u^2 + 72\,u^3$ for
+$\theta = 2$ and $19.125\,u^2 + 58\,u^3$ for $\theta = 1$, $E_1 \le 2^{-303}$, and
```"""),
 dict(path="paper/README.md", line=25, side="RIGHT", body=r"""2. **bug**: This command fails on main. The PR merged before #79, so `accumulator/acc_check` builds against main's `OD::sqrt`, which is still SQRT₈,₄:

```
$ python3 sqrt_bits.py 2000
2000 inputs, 547 mismatches        (exit 1)
```

Until #79 merges, three statements are false on main: this line, the appendix's "At n = 8 this is multidouble's square root (identical bits on 2000 inputs, `sqrt_bits.py`)", and the main text's "The emulator's square root matches multidouble's bit for bit on 2000 inputs". Against #79's code they hold (0 of 2,000). The control on the next line passes on main too, 300 of 300, which there means nothing. No workflow runs the paper's scripts, so CI did not see it."""),
 dict(path="paper/sqrt_bits.py", line=45, side="RIGHT", body=r"""3. **gap**: No input reaches the quick two-sum of (a₀, a₁), the one step Theorem 22 adds for θ = 2. Greedy parts, parts scaled down and zero parts all have |a₁| ≤ ulp(a₀)/2, so the two-sum returns its operands.

| inputs | two-sum moves a₀ | emulator mismatches | emulator without the two-sum |
|---|---|---|---|
| this script's 2,000 | 0 | 0 | 0 |
| 2,000 with each part in (1/2, 1] ulp of the one above | 2,000 | 0 | 141 |

So the check passes with that line deleted from the emulator, and equally from the crate. The second row is against #79's code, and it is also the first evidence that the two agree on H(2) inputs.

```diff
+import math
 import os
```
```diff
-        if k % 3 == 1:
+        if k % 4 == 1:
             g = r.randint(1, 6)  # a gap after part g: the parts below it scaled down
             x = x[:g] + [t * 2.0 ** -r.randint(1, 40) for t in x[g:]]
-        elif k % 3 == 2:
+        elif k % 4 == 2:
             x[r.randint(2, 6)] = 0.0  # a zero part between nonzero ones
+        elif k % 4 == 3:
+            for i in range(1, 8):  # the top of the ladder H(2): each part in (1/2, 1] ulp of the one above
+                x[i] = r.choice((-1.0, 1.0)) * (0.5 + 0.5 * r.random()) * math.ulp(x[i - 1])
```

A second control, the emulator without the two-sum, should then mismatch on some inputs (7% of the ladder ones here)."""),
 dict(path="paper/sqrt_bits.py", line=66, side="RIGHT", body=r"""4. **gap**: `zip` stops at the shorter list, so a driver that prints fewer lines than inputs and exits 0 counts the missing lines as matches, and the script still prints "N inputs".

```diff
+    assert len(out) >= N, f'{len(out)} lines for {N} inputs'
     for x, line in zip(xs, out):
```"""),
 dict(path="paper/expansion-error-bounds-appendix.tex", line=613, side="RIGHT", body=r"""5. **nit**: "1 − t ≤ (1+t)^½" is false for t < 0, the case the lower branch of E₀ needs: t = −τ gives 1 + τ ≤ √(1−τ). The bound used is the right one, 1 − τ ≤ (1+t)^½ ≤ 1 + τ/2 for |t| ≤ τ ≤ 1. The comment in `sqrt_consts.py` line 153 has the same slip ("for 0 <= t <= 1").

```diff
-$|a_0 + a_1| \ge (1-\rho)a_0$, $r/y_A = (1+t)^{1/2}(1+d_2)/(1+d_1)$ for $y_A = A^{-1/2}$, and $1 - t \le (1+t)^{1/2}
-\le 1 + t/2$ give $|r/y_A - 1| \le E_0$. The output of $\FastTwoSum$ has $|r_1| \le u|r_0|$, so $|r_0| \le |r|/(1-u)$,
+$|a_0 + a_1| \ge (1-\rho)a_0$, $r/y_A = (1+t)^{1/2}(1+d_2)/(1+d_1)$ for $y_A = A^{-1/2}$, and $1 - \tau \le
+(1+t)^{1/2} \le 1 + \tau/2$ give $|r/y_A - 1| \le E_0$. The output of $\FastTwoSum$ has $|r_1| \le u|r_0|$, so $|r_0|
+\le |r|/(1-u)$,
```"""),
 dict(path="paper/expansion-error-bounds-appendix.tex", line=609, side="RIGHT", body=r"""6. **nit**: Two letters each name two things in this proof. y is the double-word square root in the algorithm and in *Start* ("r y = 1 + d₂"), and it is Theorem 21's unit A^(−1/2) in the statement ("with its units") and in the step ("With r = y(1+e)"), where *Start* had to call it y_A. t is the tail's ratio in *Start* and ADD(q, q/2) in the step. Another letter for the double-word root, say v, and for the ratio, say ϑ, removes both."""),
 dict(path="paper/div_consts.py", line=1, side="RIGHT", body=r"""7. **nit**: The commit that corrects the cited numbers fixed this line and left three in the same file one low: line 11 "Theorem 8(d)" and line 19 "Theorem 8(b)" are Theorem 9 in the PDF, and line 25 "Lemma 10" is Lemma 11."""),
]
json.dump(dict(commit_id="e3850793bc67ea7bc930721b504c1798b228b4c1", event="COMMENT", body=body, comments=comments), open("pr80.json", "w"), indent=1)
