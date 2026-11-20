"""The error of central differences against the step h, and of the dual numbers, in each precision, animated as h
shrinks, for the README. Standard library only, with the shared drawing primitives data_graphs.py and this repository's
graph_extras.py beside it. Reads the JSON lines of examples/derivatives.rs, measures each estimate against the exact
derivative in rational arithmetic, writes docs/derivatives.svg and prints the chart's numbers.

usage: cargo run --release --example derivatives > docs/derivatives.jsonl
       python3 scripts/derivative_graph.py
"""
import json
import math
import os
from fractions import Fraction

from data_graphs import (INK, INK_SOFT, SERIES, Svg, axes, better_hint, callout, caption, footnote, host_specs,
                         legend, marker, text_width)
from graph_extras import cursor, decade, end, group, polyline, reveal_clip

DOCS = os.path.join(os.path.dirname(os.path.abspath(__file__)), os.pardir, "docs")
REPO = "https://github.com/nmoinvaz/multidouble"
# the animation: the differences drawn as h shrinks over T_END seconds of a DUR-second cycle, then the duals, then
# the callouts
DUR, T_END = 12.0, 7.0
T_DUAL, T_CALL = (7.4, 8.2), (8.4, 9.0)
L2 = math.log10(2)

lines = [json.loads(line) for line in open(os.path.join(DOCS, "derivatives.jsonl"))]
meta = lines[0]
steps = [r for r in lines[1:] if "k" in r]
duals = next(r for r in lines[1:] if r.get("dual"))
# f64 in the neutral last slot: the baseline
types = [("dd", "double-double", "Du", SERIES[0]), ("qd", "quad-double", "Qu", SERIES[1]),
         ("od", "octo-double", "Ou", SERIES[2]), ("f64", "f64", "Fu", SERIES[-1])]

# the exact derivative of (x⁵ - 3x + 1) / (x² + 2) at the f64 x, a dyadic rational
x = Fraction(meta["x"])
p, dp, q, dq = x ** 5 - 3 * x + 1, 5 * x ** 4 - 3, x * x + 2, 2 * x
exact = (dp * q - p * dq) / (q * q)


def log_err(parts):
    """log10 of the relative error of the sum of parts, exactly, None for an exact estimate"""
    e = abs(sum(map(Fraction, parts)) - exact) / abs(exact)
    return None if e == 0 else math.log10(e.numerator) - math.log10(e.denominator)


fd = {key: [(r["k"] * L2, log_err(r[key])) for r in steps] for key, *_ in types}
du = {key: log_err(duals[key]) for key, *_ in types}
best = {key: min((v for v in fd[key] if v[1] is not None), key=lambda v: v[1]) for key, *_ in types}

# table on stdout
print(f"{'precision':<15}{'best step h':>14}{'differences':>14}{'dual numbers':>14}")
for key, name, _, _ in types:
    print(f"{name:<15}{'1e-' + format(best[key][0], '.1f'):>14}{'1e' + format(best[key][1], '.1f'):>14}"
          f"{'1e' + format(du[key], '.1f'):>14}")

# layout
W = 890
left, top = 92, 100
pw, ph = 620, 330
YLO, YHI = -135, 5
svg = Svg(W)
caption(svg, 16, 24, "Derivatives: central differences against dual numbers, in each precision",
        "f′(0.7) of f(x) = (x⁵ − 3x + 1) / (x² + 2) by (f(x + h) − f(x − h)) / 2h with h = 1/2ᵏ, and by the dual "
        "numbers, against the exact derivative; lower is better")
legend(svg, left + pw, 62, [(name, color) for _, name, _, color in types])
lx = 16
for label, dash in (("central differences", None), ("dual numbers", "6 4")):
    polyline(svg, [(lx, 58), (lx + 26, 58)], INK_SOFT, dash=dash)
    svg.text(lx + 34, 62, label, size=11, fill=INK)
    lx += text_width(label, 11) + 64
xmap, ymap = axes(svg, left, top, pw, ph, (0, 85), (YLO, YHI), "step h (log scale)", "relative error (log scale)",
                  xfmt=lambda v: decade(-int(v)), yfmt=lambda v: decade(int(v)))

# the differences, revealed as h shrinks, each type's best step marked
reveal_clip(svg, "deriv-reveal", left, top - 6, pw + 8, ph + 12, DUR, T_END)
group(svg, clip="deriv-reveal")
for key, name, _, color in types:
    pts = [(xmap(v), ymap(min(e, YHI + 4))) for v, e in fd[key] if e is not None]
    polyline(svg, pts, color, width=2.2, title=f"{name} central differences")
for key, name, _, color in types:
    v, e = best[key]
    marker(svg, "circle", xmap(v), ymap(e), color, f"{name} differences: best step 10^-{v:.1f}, error 10^{e:.1f}")
end(svg)
cursor(svg, left, top, ph, pw, DUR, T_END, INK_SOFT)

# the dual numbers, one error whatever the step
group(svg, fade=T_DUAL, dur=DUR)
for key, name, dual, color in types:
    y = ymap(du[key])
    polyline(svg, [(left, y), (left + pw, y)], color, width=2, dash="6 4", title=f"{name} dual numbers ({dual})")
    svg.text(left + pw - 6, y - 6, f"{dual}: {decade(round(du[key]))}", size=11, fill=color, anchor="end",
             weight="bold")
end(svg)

# points of interest: the f64 differences' best, and the octo-double ones' against its duals
group(svg, fade=T_CALL, dur=DUR)
v, e = best["f64"]
# the label below the octo-double line, between the Qu line and the 10⁻¹⁰⁰ gridline
callout(svg, xmap(v), ymap(e), f"f64 differences at best: {decade(round(e))}", dx=20, dy=150)
v, e = best["od"]
callout(svg, xmap(v), ymap(e), f"octo-double: {decade(round(e))} at best, {decade(round(du['od']))} by duals",
        dx=34, dy=40)
end(svg)

better_hint(svg, left, top, pw, ph, where="right", label="better", reverse=True)

body_bottom = top + ph + 44
height = footnote(svg, [f"multidouble {meta['version']}", "examples/derivatives.rs, errors in exact rational "
                        "arithmetic"], host_specs(), [], body_bottom, repo_url=REPO)
with open(os.path.join(DOCS, "derivatives.svg"), "w") as f:
    f.write(svg.finish(height))
