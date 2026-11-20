"""This repository's own helpers for its graph scripts, beside the vendored data_graphs.py: superscript text and the
SMIL animation of the animated graphs. The animation moves geometry and opacity only, so the dark-mode swap of
data_graphs.Svg.finish, which rewrites fill and stroke attributes by value, still reaches every color. Each animated
element's static attributes are its last frame, so a viewer without SMIL shows the finished graph.
"""

from data_graphs import esc

SUP = str.maketrans("0123456789-+.", "⁰¹²³⁴⁵⁶⁷⁸⁹⁻⁺·")


def sup(v):
    """v in superscript characters, e.g. sup(-20) is ⁻²⁰"""
    return str(v).translate(SUP)


def decade(e):
    """10 to the power e as text, 1 for e = 0"""
    return "1" if e == 0 else f"10{sup(e)}"


def keys(dur, *times):
    """keyTimes for the instants times (in seconds) of a cycle of dur seconds, from 0 to 1"""
    return ";".join(f"{t / dur:.4f}".rstrip("0").rstrip(".") or "0" for t in (0.0, *times, dur))


def reveal_clip(svg, cid, x, y, w, h, dur, t_end):
    """A clip path whose rect widens from 0 at the cycle's start to w at t_end, then holds, repeating every dur
    seconds; draw what it reveals inside group(svg, clip=cid)."""
    svg.add(f'<defs><clipPath id="{cid}"><rect x="{x:.1f}" y="{y:.1f}" width="{w:.1f}" height="{h:.1f}">'
            f'<animate attributeName="width" values="0;{w:.1f};{w:.1f}" keyTimes="{keys(dur, t_end)}" '
            f'dur="{dur}s" repeatCount="indefinite"/></rect></clipPath></defs>')


def cursor(svg, x, y, h, w, dur, t_end, stroke):
    """A vertical line at the reveal's edge: from x to x + w over [0, t_end], hidden after it and without SMIL."""
    svg.add(f'<line x1="{x:.1f}" y1="{y:.1f}" x2="{x:.1f}" y2="{y + h:.1f}" stroke="{stroke}" stroke-width="1" '
            f'opacity="0"><animateTransform attributeName="transform" type="translate" '
            f'values="0 0;{w:.1f} 0;{w:.1f} 0" keyTimes="{keys(dur, t_end)}" dur="{dur}s" repeatCount="indefinite"/>'
            f'<animate attributeName="opacity" values="0.7;0.7;0;0" keyTimes="{keys(dur, t_end, t_end + 0.01)}" '
            f'dur="{dur}s" repeatCount="indefinite"/></line>')


def group(svg, clip=None, fade=None, dur=None):
    """Open a group, clipped by the clip path clip or faded in over fade = (t0, t1) seconds of a dur-second cycle;
    close it with end(svg)."""
    attrs = f' clip-path="url(#{clip})"' if clip else ""
    svg.add(f"<g{attrs}>")
    if fade:
        t0, t1 = fade
        svg.add(f'<animate attributeName="opacity" values="0;0;1;1" keyTimes="{keys(dur, t0, t1)}" dur="{dur}s" '
                f'repeatCount="indefinite"/>')


def end(svg):
    svg.add("</g>")


def polyline(svg, pts, stroke, width=2.0, dash=None, title=None):
    """An open line through the pixel points pts, dashed when dash is a dasharray"""
    d = " ".join(f"{'M' if i == 0 else 'L'}{x:.1f} {y:.1f}" for i, (x, y) in enumerate(pts))
    extra = f' stroke-dasharray="{dash}"' if dash else ""
    tip = f"<title>{esc(title)}</title>" if title else ""
    svg.add(f'<path d="{d}" fill="none" stroke="{stroke}" stroke-width="{width}" stroke-linejoin="round" '
            f'stroke-linecap="round"{extra}>{tip}</path>')
