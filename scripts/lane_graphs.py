"""Time per value of the elementary functions on the 8-lane types against the scalar ones, per type family, for the
README. Standard library only, with the shared drawing primitives data_graphs.py beside it. Reads the JSON lines of
examples/lane_speedups.rs, writes docs/lane-speedups.svg and prints the chart's numbers.

usage: cargo run --release --example lane_speedups > docs/lane-speedups.jsonl
       python3 scripts/lane_graphs.py [--warn TEXT]

--warn adds a warning line to the footnote, for conditions that make the timings suspect (load, throttling).
"""
import argparse
import json
import os
import subprocess

from data_graphs import (GRID, INK, INK_SOFT, SERIES, SHAPES, Svg, axes, better_hint, callout, caption,
                         dodge_markers, fmt_pct, footnote, host_specs, marker, text_width)

DOCS = os.path.join(os.path.dirname(os.path.abspath(__file__)), os.pardir, "docs")
REPO = "https://github.com/nmoinvaz/multidouble"

ap = argparse.ArgumentParser()
ap.add_argument("--warn", action="append", default=[])
args = ap.parse_args()
lines = [json.loads(line) for line in open(os.path.join(DOCS, "lane-speedups.jsonl"))]
meta, rows_in = lines[0], lines[1:]
ISA = {"neon": "NEON", "avx512": "AVX-512", "avx2": "AVX2", "sse2": "SSE2", "portable": "the portable backend"}
isa = ISA.get(meta["isa"], meta["isa"])
commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"], capture_output=True, text=True,
                        cwd=DOCS).stdout.strip()
families = ["double-double", "quad-double", "octo-double"]
short = {"double-double": "DD → DV", "quad-double": "QD → QV", "octo-double": "OD → OV"}
groups = [("", ["exp", "ln"]), ("1/4 <= |x| < 1", ["sin", "cos", "tan", "sin_cos"]),
          ("1 <= |x| < 1024", ["sin", "cos", "tan", "sin_cos"])]
group_title = {"": "", "1/4 <= |x| < 1": "¼ ≤ |x| < 1", "1 <= |x| < 1024": "1 ≤ |x| < 1024"}
data = {(r["type"], r["func"], r["range"]): r for r in rows_in}
change = {k: (r["lanes_ns"] - r["scalar_ns"]) / r["scalar_ns"] * 100 for k, r in data.items()}

# table on stdout
print(f"{'function':<10}{'range':<18}" + "".join(f"{f:>28}" for f in families))
for rng, funcs in groups:
    for fn in funcs:
        cells = []
        for fam in families:
            r = data[(fam, fn, rng)]
            cells.append(f"{r['scalar_ns']:>9.1f} {r['lanes_ns']:>8.1f} {fmt_pct(change[(fam, fn, rng)]):>8}")
        print(f"{fn:<10}{rng:<18}" + "".join(f"{c:>28}" for c in cells))

# layout
W = 890
left, top = 132, 92
pw, row_h, gap = 400, 26, 18
nrows = sum(len(f) for _, f in groups)
ph = nrows * row_h + gap * (len(groups) - 1)
svg = Svg(W)
caption(svg, 16, 24, "SIMD lanes against the scalar types: change in time per value",
        f"8 lanes on {isa}, the same inputs for both; fastest of {meta['runs']} alternating passes over "
        f"{meta['values']} values; lower is faster")
n0 = len(svg.parts)
xmap, _ = axes(svg, left, top, pw, ph, (-90, 0), (0, 1), "change in time per value, lanes against scalar (%)",
               "function", xfmt=lambda v: f"{v:+.0f}%".replace("+0%", "0%").replace("-", "−"), yfmt=lambda v: "")
# The y axis is categorical: drop axes()'s y gridlines, empty y tick labels and rotated y title, and name the
# column above the function names instead.
y_grid = f'x1="{left:.1f}"'
svg.parts[n0:] = [q for q in svg.parts[n0:]
                  if not (q.startswith("<line") and y_grid in q and f'x2="{left + pw:.1f}"' in q and GRID in q)
                  and not (q.startswith("<text") and q.endswith("></text>"))
                  and "rotate(-90" not in q]
svg.text(left - 10, top - 10, "function", size=10, fill=INK_SOFT, anchor="end", weight="bold")
ys, y = {}, top + row_h / 2
for gi, (rng, funcs) in enumerate(groups):
    if gi:
        y += gap
    if group_title[rng]:
        svg.text(16, y - row_h / 2 - 2, group_title[rng], size=10, fill=INK_SOFT)
    for fn in funcs:
        ys[(fn, rng)] = y
        svg.text(left - 10, y + 4, fn, size=12, fill=INK, anchor="end")
        svg.line(left, y, left + pw, y, GRID)
        y += row_h

# markers, dodged where two families land on the same value in a row (dodge spreads along its first coordinate)
pts = {i: {key: (ys[key], xmap(change[(fam,) + key])) for key in ys} for i, fam in enumerate(families)}
dodged = dodge_markers(pts, step=11.0, tol=9.0)
for i, fam in enumerate(families):
    for key, (yy, xx) in dodged[i].items():
        r = data[(fam,) + key]
        marker(svg, SHAPES[i], xx, yy, SERIES[i],
               f"{fam} {key[0]} {key[1]}: scalar {r['scalar_ns']:.1f} ns, lanes {r['lanes_ns']:.1f} ns per value, "
               f"{fmt_pct(change[(fam,) + key])}")

# numbers beside the plot, one column per family
cx0 = left + pw + 140
for i, fam in enumerate(families):
    cx = cx0 + i * 86
    svg.text(cx, top - 10, short[fam], size=10, fill=SERIES[i], anchor="end", weight="bold")
    # the column header carries the family's marker, so it doubles as the legend
    marker(svg, SHAPES[i], cx - text_width(short[fam], 10) - 12, top - 14, SERIES[i], fam)
    for key, yy in ys.items():
        svg.text(cx, yy + 4, fmt_pct(change[(fam,) + key]).replace("-", "−"), size=11, fill=INK, anchor="end",
                 tabular=True)

better_hint(svg, left, top, pw, ph, where="axis", label="faster", reverse=True)

# points of interest
k = ("double-double", "ln", "")
callout(svg, xmap(change[k]), ys[("ln", "")], "largest gain", dx=36, dy=22)
k = ("double-double", "sin", "1 <= |x| < 1024")
callout(svg, xmap(change[k]), ys[("sin", "1 <= |x| < 1024")], "the π/2 reduction stays scalar", dx=40, dy=-14)

body_bottom = top + ph + 44
height = footnote(svg, [f"multidouble {commit}", "examples/lane_speedups.rs"], host_specs(), args.warn,
                  body_bottom, repo_url=REPO)
with open(os.path.join(DOCS, "lane-speedups.svg"), "w") as f:
    f.write(svg.finish(height))
