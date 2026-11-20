"""Time per value of add, multiply and divide against the precision's significant digits, on the scalar types and on
their 8-lane twins, for the README. Standard library only, with the shared drawing primitives data_graphs.py beside it.
Reads the JSON lines of examples/precision_costs.rs, writes docs/precision-costs.svg and prints the chart's numbers.

usage: cargo run --release --example precision_costs > docs/precision-costs.jsonl
       python3 scripts/cost_graph.py [--warn TEXT]

--warn adds a warning line to the footnote, for conditions that make the timings suspect (load, throttling).
"""
import argparse
import json
import math
import os

from data_graphs import (INK, INK_SOFT, SERIES, SHAPES, Svg, axes, better_hint, callout, caption, dodge_markers,
                         fmt_pct, footnote, legend, marker, text_width)
from graph_extras import polyline

DOCS = os.path.join(os.path.dirname(os.path.abspath(__file__)), os.pardir, "docs")
REPO = "https://github.com/nmoinvaz/multidouble"

ap = argparse.ArgumentParser()
ap.add_argument("--warn", action="append", default=[])
args = ap.parse_args()
lines = [json.loads(line) for line in open(os.path.join(DOCS, "precision-costs.jsonl"))]
meta, rows = lines[0], lines[1:]
ISA = {"neon": "NEON", "avx512": "AVX-512", "avx2": "AVX2", "sse2": "SSE2", "portable": "the portable backend"}
isa = ISA.get(meta["isa"], meta["isa"])
source = f"multidouble main of {meta.get('date', '?')} (Cargo.toml {meta.get('version', '?')})"
types = [("f64", 1), ("double-double", 2), ("quad-double", 4), ("octo-double", 8)]
short = {"f64": "f64", "double-double": "DD / DV", "quad-double": "QD / QV", "octo-double": "OD / OV"}
ops = [("add", "add"), ("mul", "multiply"), ("div", "divide")]
modes = [("scalar_ns", "scalar"), ("lanes_ns", "8 lanes")]
data = {(r["type"], r["op"]): r for r in rows}
digits = {t: 53 * n * math.log10(2) for t, n in types}


def change(t, op):
    """the lanes' change in time per value against the scalar type's, in percent"""
    r = data[(t, op)]
    return (r["lanes_ns"] - r["scalar_ns"]) / r["scalar_ns"] * 100


# table on stdout
print(f"{'type':<16}{'digits':>7}" + "".join(f"{label:>34}" for _, label in ops))
for t, _ in types:
    cells = [f"{data[(t, op)]['scalar_ns']:>9.2f} {data[(t, op)]['lanes_ns']:>8.2f} {fmt_pct(change(t, op)):>8}"
             for op, _ in ops]
    print(f"{t:<16}{digits[t]:>7.1f}" + "".join(f"{c:>34}" for c in cells))

# layout
W = 890
left, top = 84, 96
pw, ph = 500, 340
svg = Svg(W)
caption(svg, 16, 24, "The cost of precision: time per value of add, multiply and divide",
        f"scalar types against their 8-lane twins on {isa}, the same inputs for both; fastest of {meta['runs']} "
        f"alternating passes over {meta['values']} values; lower is faster")
legend(svg, left + pw, 62, [(label, SERIES[i]) for i, (_, label) in enumerate(ops)])
# the line styles: scalar solid with circles, lanes dashed with squares
lx = 16
for (key, label), shape, dash in zip(modes, (SHAPES[0], SHAPES[1]), (None, "6 4")):
    polyline(svg, [(lx, 58), (lx + 26, 58)], INK_SOFT, dash=dash)
    marker(svg, shape, lx + 13, 58, INK_SOFT, label)
    svg.text(lx + 34, 62, label, size=11, fill=INK)
    lx += text_width(label, 11) + 64

xmap, ymap = axes(svg, left, top, pw, ph, (10, 200, "log"), (0.5, 2000, "log"), "significant decimal digits",
                  "time per value (ns, log scale)", xfmt=lambda v: f"{v:g}", yfmt=lambda v: f"{v:g}")
for t, _ in types:
    svg.text(xmap(digits[t]), top + 14, short[t], size=10, fill=INK_SOFT, anchor="middle", weight="bold")

# markers, dodged where series meet at a precision
series = [(op, key) for op, _ in ops for key, _ in modes]
pts = {s: {t: (xmap(digits[t]), ymap(data[(t, op)][key])) for t, _ in types} for s, (op, key) in enumerate(series)}
dodged = dodge_markers(pts, step=7.0, tol=8.0)
for s, (op, key) in enumerate(series):
    i = [o for o, _ in ops].index(op)
    polyline(svg, [pts[s][t] for t, _ in types], SERIES[i], dash=None if key == "scalar_ns" else "6 4")
for s, (op, key) in enumerate(series):
    i = [o for o, _ in ops].index(op)
    mode = dict(modes)[key]
    for t, _ in types:
        x, y = dodged[s][t]
        marker(svg, SHAPES[0] if key == "scalar_ns" else SHAPES[1], x, y, SERIES[i],
               f"{t} {dict(ops)[op]}, {mode}: {data[(t, op)][key]:.2f} ns per value")

# direct labels right of the plot at the octo-double values, spread so that none overlap
labels = sorted(((pts[s]["octo-double"][1], s) for s in range(len(series))), reverse=True)
placed = []
for y, s in labels:
    placed.append(min(y, placed[-1] - 14) if placed else y)
for (y, s), ly in zip(labels, placed):
    op, key = series[s]
    i = [o for o, _ in ops].index(op)
    svg.text(left + pw + 40, ly + 4, f"{dict(ops)[op]}, {dict(modes)[key]}: {data[('octo-double', op)][key]:.0f} ns",
             size=11, fill=SERIES[i], tabular=True)

better_hint(svg, left, top, pw, ph, where="right", label="faster", reverse=True)

# points of interest: the double-double and quad-double divides on lanes
for t, op, dx, dy in (("double-double", "div", 40, 72), ("quad-double", "div", -50, -56)):
    s = series.index((op, "lanes_ns"))
    x, y = dodged[s][t]
    callout(svg, x, y, f"{dict(ops)[op]} on 8 lanes: {fmt_pct(change(t, op)).replace('-', '−')}", dx=dx, dy=dy)

body_bottom = top + ph + 44
# the machine the timings ran on, as the example recorded it, not the one drawing the graph
height = footnote(svg, [source, "examples/precision_costs.rs"], meta.get("machine", ""), args.warn, body_bottom,
                  repo_url=REPO)
with open(os.path.join(DOCS, "precision-costs.svg"), "w") as f:
    f.write(svg.finish(height))
