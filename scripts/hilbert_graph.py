"""The error of Hilbert solves in f64, double-double, quad-double and octo-double against n, animated as n grows, for
the README. Standard library only, with the shared drawing primitives data_graphs.py and this repository's
graph_extras.py beside it. Reads the JSON lines of examples/hilbert.rs, writes docs/hilbert.svg and prints the chart's
numbers.

usage: cargo run --release --example hilbert > docs/hilbert.jsonl
       python3 scripts/hilbert_graph.py
"""
import json
import math
import os

from data_graphs import (INK, INK_SOFT, SERIES, Svg, axes, better_hint, callout, caption, footnote, host_specs,
                         legend, marker)
from graph_extras import cursor, decade, end, group, polyline, reveal_clip, sup

DOCS = os.path.join(os.path.dirname(os.path.abspath(__file__)), os.pardir, "docs")
REPO = "https://github.com/nmoinvaz/multidouble"
# the animation: the lines drawn as n grows over T_END seconds of a DUR-second cycle, then the callouts
DUR, T_END = 10.0, 7.0

lines = [json.loads(line) for line in open(os.path.join(DOCS, "hilbert.jsonl"))]
meta, rows = lines[0], lines[1:]
# f64 in the neutral last slot: the baseline
types = [("dd", "double-double", 2, SERIES[0]), ("qd", "quad-double", 4, SERIES[1]),
         ("od", "octo-double", 8, SERIES[2]), ("f64", "f64", 1, SERIES[-1])]
# the first n without a correct digit, by an error of 1 or more or a failed factorization (None if every solve kept one)
out = {key: next((r["n"] for r in rows if r[key] is None or r[key] >= 1), None) for key, *_ in types}


def first_out(key):
    """the error at the first n without a correct digit, None where there is none or the factorization failed"""
    return next((r[key] for r in rows if r["n"] == out[key]), None)


# table on stdout
print(f"{'n':>4}" + "".join(f"{name:>16}" for _, name, _, _ in types))
for r in rows:
    if r["n"] % 6 == 2 or r["n"] in out.values():
        print(f"{r['n']:>4}" + "".join(f"{r[k]:>16.2e}" if r[k] is not None else f"{'failed':>16}"
                                     for k, *_ in types))
print("no correct digit from n = " + ", ".join(f"{name} {out[k]}" for k, name, *_ in types))

# layout
W = 890
left, top = 92, 100
pw, ph = 620, 330
YLO, YHI = -135, 5
svg = Svg(W)
caption(svg, 16, 24, "Ill-conditioned systems: Hilbert solves in each precision as n grows",
        "H x = b with H(i, j) = 1/(i + j + 1) and b its row sums, so that x is all ones, by LU with partial pivoting; "
        "cond(H) grows like e^(3.5 n); lower is better")
legend(svg, left + pw, 62, [(name, color) for _, name, _, color in types])
xmap, ymap = axes(svg, left, top, pw, ph, (0, 100), (YLO, YHI), "matrix size n",
                  "largest error max |xᵢ − 1| (log scale)", xfmt=lambda v: f"{v:g}", yfmt=lambda v: decade(int(v)))

# each type's own rounding, uⁿ = 2⁻⁵³ⁿ, and an error of 1: no correct digit left
for key, name, n, color in types:
    y = ymap(-53 * n * math.log10(2))
    polyline(svg, [(left, y), (left + pw, y)], color, width=1, dash="2 4")
    svg.text(left + pw - 6, y - 5, f"u{sup(n) if n > 1 else ''} of {name}", size=10, fill=color, anchor="end")
y1 = ymap(0)
polyline(svg, [(left, y1), (left + pw, y1)], INK_SOFT, width=1.5, dash="6 4")
# below the line where only the octo-double line runs, far under it until n = 82
svg.text(xmap(61), y1 + 14, "error 1: no correct digit", size=10, fill=INK_SOFT)

# the lines, revealed as n grows, with each type's first n without a correct digit marked
reveal_clip(svg, "hilbert-reveal", left, top - 6, pw + 8, ph + 12, DUR, T_END)
group(svg, clip="hilbert-reveal")
pts = {}
for key, name, n, color in types:
    pts[key] = [(xmap(r["n"]), ymap(math.log10(r[key]))) for r in rows if r[key] is not None]
    polyline(svg, pts[key], color, width=2.2, title=f"{name} LU")
for key, name, n, color in types:
    e = first_out(key)
    if e is None:
        continue
    x, y = xmap(out[key]), ymap(math.log10(e))
    marker(svg, "circle", x, y, color, f"{name}: no correct digit from n = {out[key]}, error {e:.2g}")
    if key in ("dd", "qd"):
        svg.text(x + 8, y + 18, f"n = {out[key]}", size=11, fill=color, weight="bold")
end(svg)
cursor(svg, left, top, ph, pw, DUR, T_END, INK_SOFT)

# points of interest, after the lines: where f64 and octo-double run out
group(svg, fade=(T_END, T_END + 0.6), dur=DUR)
for key, label, dx, dy in (("f64", "f64: none left at n = {}", 26, 40), ("od", "octo-double: n = {}", -30, 56)):
    e = first_out(key)
    if e is not None:
        callout(svg, xmap(out[key]), ymap(math.log10(e)), label.format(out[key]), dx=dx, dy=dy)
end(svg)

better_hint(svg, left, top, pw, ph, where="right", label="better", reverse=True)

body_bottom = top + ph + 44
height = footnote(svg, [f"multidouble {meta['version']}", "examples/hilbert.rs: H and b formed in octo-double, "
                        "rounded to each type"], host_specs(), [], body_bottom, repo_url=REPO)
with open(os.path.join(DOCS, "hilbert.svg"), "w") as f:
    f.write(svg.finish(height))
