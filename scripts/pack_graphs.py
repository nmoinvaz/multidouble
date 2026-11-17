"""Diagrams of the packed storage (pack::Packed<N>) for docs/pack.md, and a chart of its size against general
compressors. Standard library only, with the shared drawing primitives data_graphs.py beside it. Writes
docs/pack-*.svg and prints the chart's numbers.

usage: python3 scripts/pack_graphs.py"""
import os

from data_graphs import (GRID, INK, INK_SOFT, SERIES, SURFACE, Svg, bar_path, better_hint, callout, caption,
                         esc, footnote, host_specs, legend, text_width)

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), os.pardir, "docs")
SIGN, EXP, CODE, FRAC = SERIES[3], SERIES[1], SERIES[2], SERIES[0]
# labels on colored fills take a fixed ink, not a themed one
ON_FILL, ON_LIGHT_FILL = "#ffffff", "#1a1a1a"
REPO = "https://github.com/nmoinvaz/multidouble"


def box(svg, x, y, w, h, fill, tip, label=None, ink=ON_FILL, size=10):
    svg.add(f'<rect x="{x:.1f}" y="{y:.1f}" width="{max(w, 0.8):.1f}" height="{h:.1f}" fill="{fill}">'
            f'<title>{esc(tip)}</title></rect>')
    if label and w > text_width(label, size) + 4:
        svg.text(x + w / 2, y + h / 2 + size * 0.35, label, size=size, fill=ink, anchor="middle")


def outline(svg, x, y, w, h, stroke=INK_SOFT):
    svg.add(f'<rect x="{x:.1f}" y="{y:.1f}" width="{w:.1f}" height="{h:.1f}" fill="none" '
            f'stroke="{stroke}" stroke-width="1"/>')


def hatch(svg, x, y, w, h, tip):
    """an empty span, drawn as diagonal lines in the grid color"""
    svg.add(f'<rect x="{x:.1f}" y="{y:.1f}" width="{w:.1f}" height="{h:.1f}" fill="{GRID}">'
            f'<title>{esc(tip)}</title></rect>')
    k = x - h
    while k < x + w:
        x1, y1, x2, y2 = k, y + h, k + h, y
        if x1 < x:
            y1 -= x - x1
            x1 = x
        if x2 > x + w:
            y2 += x2 - (x + w)
            x2 = x + w
        svg.line(x1, y1, x2, y2, INK_SOFT, 0.6)
        k += 7


def part(svg, x, y, s, h, kind, name):
    """one part at s px per bit: a raw f64 (sign, exponent, fraction) or a packed field (sign, code, fraction)"""
    if kind == "raw":
        box(svg, x, y, s, h, SIGN, f"{name}: sign, 1 bit")
        box(svg, x + s, y, 11 * s, h, EXP, f"{name}: exponent, 11 bits", "exp" if 11 * s > 24 else None)
        box(svg, x + 12 * s, y, 52 * s, h, FRAC, f"{name}: fraction, 52 bits", name)
        width = 64 * s
    else:
        box(svg, x, y, s, h, SIGN, f"{name}: sign, 1 bit")
        box(svg, x + s, y, 4 * s, h, CODE, f"{name}: exponent code, 4 bits")
        box(svg, x + 5 * s, y, 52 * s, h, FRAC, f"{name}: fraction, 52 bits", name)
        width = 57 * s
    outline(svg, x, y, width, h)
    return width


def layout():
    """an octo-double raw and packed, at one scale"""
    s, x0, h = 1.75, 70, 30
    svg = Svg(int(x0 + 512 * s + 30))
    y = caption(svg, 16, 22, "An octo-double, raw and packed",
                "Eight f64 parts take 512 bits. Packed, the leading part stays raw and each lower part drops 7 "
                "exponent bits: 463 bits.")
    svg.text(x0 - 8, y + h / 2 + 4, "raw", size=11, fill=INK, anchor="end")
    x = x0
    for k in range(8):
        x += part(svg, x, y, s, h, "raw", f"x{k}")
    svg.text(x0 + 512 * s, y - 6, "512 bits", size=10, anchor="end", tabular=True)
    y2 = y + h + 34
    svg.text(x0 - 8, y2 + h / 2 + 4, "packed", size=11, fill=INK, anchor="end")
    x = x0 + part(svg, x0, y2, s, h, "raw", "x0")
    for k in range(1, 8):
        x += part(svg, x, y2, s, h, "packed", f"x{k}")
    hatch(svg, x, y2, 512 * s - (x - x0), h, "saved: 49 bits")
    svg.text(x - 4, y2 + h + 14, "463 bits", size=10, anchor="end", tabular=True)
    svg.text(x + (512 * s - (x - x0)) / 2, y2 + h + 14, "49 saved", size=10, anchor="middle")
    ly = y2 + h + 42
    legend(svg, x0 + 512 * s, ly, [("sign", SIGN), ("exponent", EXP), ("4-bit exponent code", CODE),
                                    ("fraction", FRAC)])
    return svg.finish(ly + 18)


def field():
    """one lower part, raw and packed, bit by bit"""
    s, x0, h = 11, 90, 34
    svg = Svg(x0 + 66 * s + 40)
    y = caption(svg, 16, 22, "One lower part",
                "The 11-bit exponent becomes a 4-bit code: how far the part lies below the last nonzero part "
                "above it.")
    svg.text(x0 - 10, y + h / 2 + 4, "raw f64", size=11, fill=INK, anchor="end")
    box(svg, x0, y, s, h, SIGN, "sign", "s", ink=ON_LIGHT_FILL)
    box(svg, x0 + s, y, 11 * s, h, EXP, "biased exponent e, 11 bits", "exponent e (11)")
    box(svg, x0 + 12 * s, y, 52 * s, h, FRAC, "fraction, 52 bits", "fraction (52)")
    outline(svg, x0, y, 64 * s, h)
    y2 = y + h + 56
    svg.text(x0 - 10, y2 + h / 2 + 4, "packed", size=11, fill=INK, anchor="end")
    box(svg, x0, y2, s, h, SIGN, "sign: one bit of the group's sign byte", "s", ink=ON_LIGHT_FILL)
    outline(svg, x0, y2, s, h)
    xf = x0 + s + 6
    box(svg, xf, y2, 4 * s, h, CODE, "code, 4 bits", "code")
    box(svg, xf + 4 * s, y2, 52 * s, h, FRAC, "fraction, 52 bits", "fraction (52)")
    outline(svg, xf, y2, 56 * s, h)
    hatch(svg, xf + 56 * s, y2, 7 * s, h, "saved: 7 bits")
    svg.text(xf + 59.5 * s, y2 + h + 14, "7 saved", size=10, anchor="middle")
    svg.text(x0 + s / 2, y2 + h + 14, "sign byte", size=10, anchor="start")
    svg.text(xf + 30 * s, y2 + h + 14, "7-byte field: fraction | code << 52", size=10, anchor="middle")
    # the exponent maps to the code, the fraction is copied
    a1, b1 = x0 + 6.5 * s, xf + 2 * s
    svg.line(a1, y + h + 2, b1, y2 - 2, INK_SOFT, 1.2)
    svg.add(f'<polygon points="{b1:.1f},{y2 - 1:.1f} {b1 - 4:.1f},{y2 - 9:.1f} {b1 + 4:.1f},{y2 - 9:.1f}" '
            f'fill="{INK_SOFT}"/>')
    svg.text(x0 + 8 * s, y + h + 32, "code = 64 − drop, the drop being (e of the last nonzero part above) − e, "
             "53 to 64", size=11, fill=INK)
    mid = xf + 50 * s
    svg.line(mid, y + h + 2, mid, y2 - 2, INK_SOFT, 1.2)
    svg.add(f'<polygon points="{mid:.1f},{y2 - 1:.1f} {mid - 4:.1f},{y2 - 9:.1f} {mid + 4:.1f},{y2 - 9:.1f}" '
            f'fill="{INK_SOFT}"/>')
    y3 = y2 + h + 40
    rows = [("0 … 11", "a normal part whose exponent lies 64 − code below the last nonzero part above it"),
            ("12", "a zero part, its sign in the sign byte"),
            ("15", "this value is in the side table; the fraction bits hold its row")]
    svg.text(x0, y3, "code", size=11, fill=INK, weight="bold")
    svg.text(x0 + 70, y3, "meaning", size=11, fill=INK, weight="bold")
    for i, (c, m) in enumerate(rows):
        yy = y3 + 20 * (i + 1)
        svg.text(x0, yy, c, size=11, fill=INK, tabular=True)
        svg.text(x0 + 70, yy, m, size=11, fill=INK_SOFT)
    svg.text(x0, y3 + 20 * (len(rows) + 1), "Decoding is one add: the field under a constant top byte 0xfc, plus "
             "the exponent above shifted by 52.", size=11, fill=INK_SOFT)
    return svg.finish(y3 + 20 * (len(rows) + 1) + 18)


def stream():
    """one block of 8 octo-doubles, to scale in bytes"""
    s, x0, h = 1.85, 40, 30
    svg = Svg(int(x0 + 463 * s + 40))
    y = caption(svg, 16, 22, "Blocks of 8 values",
                "A block holds the 8 leading parts, then for each lower part the 8 fields and a byte of their "
                "signs. get(i) reads block i/8; SIMD decodes a block with byte shuffles.")
    y += 16
    for j in range(8):
        box(svg, x0 + 8 * j * s, y, 8 * s - 0.6, h, SERIES[j], f"value {j}: x0, raw f64, 8 bytes")
    outline(svg, x0, y, 64 * s, h)
    svg.text(x0 + 32 * s, y - 6, "x0 ×8", size=10, fill=INK, anchor="middle")
    for k in range(1, 8):
        xg = x0 + (64 + 57 * (k - 1)) * s
        for j in range(8):
            box(svg, xg + 7 * j * s, y, 7 * s - 0.6, h, SERIES[j], f"value {j}: x{k}, 7-byte field")
        box(svg, xg + 56 * s, y, s, h, SERIES[9], f"x{k}: the 8 values' signs, 1 byte")
        outline(svg, xg, y, 57 * s, h)
        svg.text(xg + 28.5 * s, y - 6, f"x{k} ×8 + signs", size=10, fill=INK, anchor="middle")
    yb = y + h + 10
    svg.line(x0, yb, x0 + 463 * s, yb, INK_SOFT)
    for xx in (x0, x0 + 463 * s):
        svg.line(xx, yb - 4, xx, yb + 4, INK_SOFT)
    svg.text(x0 + 463 * s / 2, yb + 16, "463 bytes: 8 values × 463 bits", size=10, anchor="middle", tabular=True)
    svg.text(x0, yb + 36, "Colors mark the 8 values of the block; gray is the sign byte of each lower part.",
             size=11, fill=INK_SOFT)
    return svg.finish(yb + 52)


def escape():
    """a value that does not fit the codes, and the side table"""
    s, x0, h = 1.6, 40, 28
    svg = Svg(int(x0 + 463 * s + 60))
    y = caption(svg, 16, 22, "The side table",
                "A value that does not fit the codes keeps its 7 lower parts raw in a side table; its slot keeps "
                "x0 and the table index.")
    box(svg, x0, y, 64 * s, h, FRAC, "x0, raw", "x0")
    outline(svg, x0, y, 64 * s, h)
    xs = x0 + 64 * s
    box(svg, xs, y, s, h, SIGN, "sign 0")
    box(svg, xs + s, y, 4 * s, h, CODE, "code 15")
    box(svg, xs + 5 * s, y, 52 * s, h, FRAC, "index k into the side table", "index k")
    outline(svg, xs, y, 57 * s, h)
    hatch(svg, xs + 57 * s, y, 6 * 57 * s, h, "fields 2 to 7: zero")
    svg.text(xs + 57 * s + 3 * 57 * s, y + h + 14, "zero", size=10, anchor="middle")
    svg.text(xs + 2.5 * s, y - 6, "15", size=10, fill=INK, anchor="middle", weight="bold")
    y2 = y + h + 54
    svg.text(x0, y2 - 8, "side table, row k", size=10)
    for k in range(7):
        box(svg, x0 + k * 64 * s, y2, 64 * s - 1, h, SERIES[9], f"x{k + 1}, raw 64 bits",
            f"x{k + 1}")
    outline(svg, x0, y2, 7 * 64 * s, h)
    ax = xs + 30 * s
    svg.line(ax, y + h + 2, ax, y2 - 14, INK_SOFT, 1.2)
    svg.add(f'<polygon points="{ax:.1f},{y2 - 13:.1f} {ax - 4:.1f},{y2 - 21:.1f} {ax + 4:.1f},{y2 - 21:.1f}" '
            f'fill="{INK_SOFT}"/>')
    svg.text(x0, y2 + h + 22, "Used for a part 52 or more than 64 places down, a subnormal, infinite or NaN lower "
             "part, or a nonzero lower part under a non-normal x0.", size=11, fill=INK_SOFT)
    return svg.finish(y2 + h + 40)


# bits per octo-double on 6,921 octo-double Taylor coefficients of a numerical continuation: scripts/pack_sizes.py,
# and the packed format's own size from PackedOD::size_bits on the same values
SIZES = [
    ("raw parts", 512.0, True),
    ("lzma on the raw parts", 495.5, False),
    ("Blosc-style bit shuffle + zlib", 466.4, False),
    ("pack::PackedOD", 464.77, True),
    ("Blosc-style byte shuffle + lzma", 454.0, False),
    ("variable-length gap code", 449.4, False),
    ("exponent delta, byte shuffle, lzma", 443.8, False),
]


def sizes():
    x, w, bh, gap = 250, 430, 18, 8
    svg = Svg(x + w + 110)
    y = caption(svg, 16, 22, "Bits per octo-double",
                "Blue formats read any value alone; orange ones decode a block or the whole stream.")
    h = len(SIZES) * (bh + gap)
    lo, hi = 400, 520
    sx = lambda v: x + (v - lo) / (hi - lo) * w
    for v in range(lo, hi + 1, 20):
        svg.line(sx(v), y, sx(v), y + h, GRID)
        svg.text(sx(v), y + h + 15, str(v), size=11, anchor="middle", tabular=True)
    print(f"{'format':40s} {'bits':>6s} {'change':>8s} random access")
    for i, (name, v, ra) in enumerate(SIZES):
        yy = y + i * (bh + gap) + gap / 2
        color = SERIES[0] if ra else SERIES[1]
        svg.add(f'<path d="{bar_path(sx(lo), yy, sx(v) - sx(lo), bh)}" fill="{color}">'
                f'<title>{esc(name)}: {v:.1f} bits</title></path>')
        svg.text(x - 8, yy + bh / 2 + 4, name, size=11, fill=INK, anchor="end")
        change = (v - 512) / 512 * 100
        label = f"{v:.0f}" + ("" if v == 512 else f"  {change:+.1f}%")
        if name == "pack::PackedOD":
            callout(svg, sx(v), yy + bh / 2, label + ", read by index", dx=26, dy=0)
        else:
            svg.text(sx(v) + 6, yy + bh / 2 + 4, label, size=10, anchor="start", tabular=True)
        print(f"{name:40s} {v:6.1f} {change:+7.1f}% {'yes' if ra else 'no'}")
    svg.line(x, y + h, x + w, y + h, INK_SOFT)
    svg.text(x + w / 2, y + h + 34, "bits per value (x axis starts at 400)", size=12, fill=INK, anchor="middle")
    better_hint(svg, x, y, w, h, where="axis", label="smaller", reverse=True)
    legend(svg, x + w + 100, y - 18, [("read by index", SERIES[0]), ("block or stream", SERIES[1])])
    bottom = footnote(svg, ["data: 6,921 octo-double Taylor coefficients of a numerical continuation",
                            "zlib, lzma: Python 3.13 stdlib", "shuffles simulated in numpy",
                            "multidouble pack"], host_specs(), [], y + h + 46, REPO)
    return svg.finish(bottom)


if __name__ == "__main__":
    for name, fn in (("layout", layout), ("field", field), ("stream", stream), ("escape", escape),
                     ("sizes", sizes)):
        path = os.path.join(OUT, f"pack-{name}.svg")
        with open(path, "w") as f:
            f.write(fn())
        print("wrote", os.path.basename(path))
