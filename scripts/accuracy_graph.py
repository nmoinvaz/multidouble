"""Each operation's error bound against the largest error the tests measured, per precision, for the README. Standard
library only, with the shared drawing primitives data_graphs.py beside it. The numbers are the README's two Accuracy
tables, in units of uⁿ = 2⁻⁵³ⁿ; writes docs/accuracy.svg and prints the chart's numbers.

usage: python3 scripts/accuracy_graph.py
"""
import math
import os

from data_graphs import (GRID, INK, INK_SOFT, SERIES, SHAPES, Svg, axes, better_hint, callout, caption, footnote,
                         marker, text_width)
from graph_extras import sup

DOCS = os.path.join(os.path.dirname(os.path.abspath(__file__)), os.pardir, "docs")
REPO = "https://github.com/nmoinvaz/multidouble"
VERSION = "5.1.0"

# (precision, n parts): bound, whether it is proven (otherwise the tests' threshold), and the largest measured error,
# None where the README gives none and a pair ("<", v) where it gives only an upper limit
TYPES = [("double-double", 2), ("quad-double", 4), ("octo-double", 8)]
SHORT = ["DD", "QD", "OD"]
ROWS = [
    ("add, subtract", [(3, True, 1.66), (8, False, None), (1, True, ("<", 0.01))]),
    ("multiply", [(5, False, 3.12), (16, False, None), (1, True, ("<", 0.01))]),
    ("divide", [(8, False, 1.54), (32, False, None), (1, True, ("<", 0.01))]),
    ("square root", [(25 / 8, True, None), (32, False, None), (3, True, None)]),
    ("exp", [(5.465, True, 1.04), (64, False, 0.55), (3.661, True, 0.25)]),
    ("ln", [(15.351, True, 1.27), (64, False, 0.58), (9.926, True, 0.0070)]),
    ("sin, cos", [(7.85, True, 1.82), (32, False, 1.24), (3.17, True, 0.48)]),
    ("tan", [(28.5, True, 4.07), (64, False, 7.18), (6.42, True, 0.32)]),
]


def num(v):
    return f"{v:g}" if v >= 0.01 else f"{v:.4f}".rstrip("0")


def unit(n):
    return f"u{sup(n)}"


def measured_text(m, n):
    if m is None:
        return "—"
    if isinstance(m, tuple):
        return f"below {num(m[1])} {unit(n)}"
    return f"{num(m)} {unit(n)}"


# table on stdout
print(f"{'operation':<15}" + "".join(f"{t:>44}" for t, _ in TYPES))
for op, cells in ROWS:
    out = []
    for (t, n), (b, proven, m) in zip(TYPES, cells):
        out.append(f"{num(b)} {unit(n)} ({math.log2(b):.1f} bits{', proven' if proven else ''}) / "
                   f"{measured_text(m, n)}")
    print(f"{op:<15}" + "".join(f"{c:>44}" for c in out))

# layout
W = 890
left, top = 150, 118
pw, row_h, gap = 400, 17, 11
nrows = len(ROWS) * len(TYPES)
ph = nrows * row_h + gap * (len(ROWS) - 1) + 8
svg = Svg(W)
caption(svg, 16, 24, "Error bounds and the largest measured errors, per operation and precision",
        "in units of uⁿ = 2⁻⁵³ⁿ, the rounding of the 53n bits of n parts: proven bounds, the tests' thresholds, and "
        "the tests' largest errors; lower is better")

# legend: the precisions by color, what a marker is by its shape
lx = 16
for i, (t, n) in enumerate(TYPES):
    marker(svg, "circle", lx + 5, 66, SERIES[i], t)
    svg.text(lx + 16, 70, f"{t}, n = {n}", size=11, fill=INK)
    lx += text_width(f"{t}, n = {n}", 11) + 34
lx += 10
for shape, label in ((SHAPES[0], "proven bound"), (SHAPES[1], "tested bound"), (SHAPES[2], "largest measured")):
    marker(svg, shape, lx + 5, 66, INK_SOFT, label)
    svg.text(lx + 16, 70, label, size=11, fill=INK)
    lx += text_width(label, 11) + 34

n0 = len(svg.parts)
xmap, _ = axes(svg, left, top, pw, ph, (0.005, 100, "log"), (0, 1), f"relative error (units of uⁿ, u = 2⁻⁵³)",
               "operation", xfmt=lambda v: num(v), yfmt=lambda v: "")
# The y axis is categorical: drop axes()'s y gridlines, y tick labels and y title. On x, keep the 1-2-5 gridlines but
# label only the decades.
decades = {num(10.0 ** e) for e in range(-2, 3)}
kept = []
for q in svg.parts[n0:]:
    if q.startswith("<line") and f'x1="{left:.1f}"' in q and f'x2="{left + pw:.1f}"' in q and GRID in q:
        continue
    if q.startswith("<text") and (q.endswith("></text>") or "rotate(-90" in q):
        continue
    if q.startswith("<text") and 'text-anchor="middle"' in q and f'y="{top + ph + 15:.1f}"' in q:
        label = q[q.rindex('">') + 2:-7]
        if label not in decades:
            continue
    kept.append(q)
svg.parts[n0:] = kept
# 1 uⁿ, the rounding error of the type's own bits
x1 = xmap(1)
svg.line(x1, top, x1, top + ph, INK_SOFT)
svg.text(x1, top - 6, "1 uⁿ: the rounding of 53n bits", size=10, fill=INK_SOFT, anchor="middle")

# rows
svg.text(left + pw + 120, top - 6, "bound", size=10, fill=INK_SOFT, anchor="end", weight="bold")
svg.text(left + pw + 240, top - 6, "measured", size=10, fill=INK_SOFT, anchor="end", weight="bold")
pos, y = {}, top + 4 + row_h / 2
for gi, (op, cells) in enumerate(ROWS):
    if gi:
        y += gap
    svg.text(16, y + 4, op, size=12, fill=INK)
    for i, ((t, n), (b, proven, m)) in enumerate(zip(TYPES, cells)):
        svg.text(left - 10, y + 4, SHORT[i], size=10, fill=SERIES[i], anchor="end", weight="bold")
        xb = xmap(b)
        if m is not None:
            mv = m[1] if isinstance(m, tuple) else m
            xm = xmap(mv)
            svg.line(xm, y, xb, y, SERIES[i], 2)
            if isinstance(m, tuple):
                svg.text(xm - 9, y + 4, "<", size=11, fill=SERIES[i], anchor="end", weight="bold")
            marker(svg, SHAPES[2], xm, y, SERIES[i], f"{op}, {t}: largest measured {measured_text(m, n)}")
        marker(svg, SHAPES[0] if proven else SHAPES[1], xb, y, SERIES[i],
               f"{op}, {t}: {'proven' if proven else 'tested'} bound {num(b)} {unit(n)}, "
               f"{math.log2(b):.1f} of {53 * n} bits given up")
        svg.text(left + pw + 120, y + 4, f"{num(b)} {unit(n)}", size=11, fill=INK, anchor="end", tabular=True)
        svg.text(left + pw + 240, y + 4, measured_text(m, n).replace("below ", "< "), size=11, fill=INK,
                 anchor="end", tabular=True)
        pos[(op, i)] = (xb, y)
        y += row_h

better_hint(svg, left, top, pw, ph, where="axis", label="better", reverse=True)

# points of interest: the octo-double add's proven u⁸, and the loosest proven bound
xa, ya = pos[("add, subtract", 2)]
callout(svg, xa, ya, "proven: no bits lost", dx=46, dy=-14)
xt, yt = pos[("tan", 0)]
callout(svg, xt, yt, "loosest proven: 4.8 bits", dx=-60, dy=-14)

body_bottom = top + ph + 44
height = footnote(svg, [f"multidouble {VERSION}, README Accuracy tables: bounds proved or checked by the tests, "
                        "largest errors of the tests"], "", [],
                  body_bottom, repo_url=REPO)
with open(os.path.join(DOCS, "accuracy.svg"), "w") as f:
    f.write(svg.finish(height))
