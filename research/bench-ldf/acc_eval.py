#!/usr/bin/env python3
"""Maximum relative error of every operation's results against exact rational arithmetic (fractions), which shares no
code with either library. Square roots are rounded to 2^-400 relative by integer square roots.

  acc_eval.py DATADIR OUTDIR LIB [LIB ...]     prints a table, writes OUTDIR/acc.json
  acc_eval.py DATADIR OUTDIR --selftest        the controls: results with a part dropped must exceed the bounds

Errors are relative to the exact result, |computed - exact| / |exact|, and are given in units of u^n (u = 2^-53,
n = 2 for double-double, 4 for quad-double). The "_c" sets are the near-cancelling sums (gen_inputs.py).
"""

import json
import math
import os
import struct
import sys
from fractions import Fraction

U = Fraction(1, 1 << 53)


def load(path):
    with open(path, "rb") as fh:
        b = fh.read()
    return struct.unpack("<%dd" % (len(b) // 8), b)


def values(flat, parts):
    return [sum((Fraction(flat[parts * i + k]) for k in range(parts)), Fraction(0)) for i in range(len(flat) // parts)]


def fsqrt(x, bits=400):
    """sqrt of a positive rational to about 2^-bits relative"""
    p, q = x.numerator, x.denominator
    k = bits + max(0, (q.bit_length() - p.bit_length()) // 2 + 2)
    return Fraction(math.isqrt(p * q * (1 << (2 * k))), q * (1 << k))


OPS = {
    # op: (parts, exact(a, b, f), sets)
    "dd_add": (2, lambda a, b, f: a + b, ("", "_c")),
    "dd_sub": (2, lambda a, b, f: a - b, ("", "_c")),
    "dd_mul": (2, lambda a, b, f: a * b, ("",)),
    "dd_div": (2, lambda a, b, f: a / b, ("",)),
    "dd_mul_f": (2, lambda a, b, f: a * f, ("",)),
    "dd_sqrt": (2, lambda a, b, f: fsqrt(abs(a)), ("",)),
    "qd_add_sloppy": (4, lambda a, b, f: a + b, ("", "_c")),
    "qd_add_ieee": (4, lambda a, b, f: a + b, ("", "_c")),
    "qd_sub_sloppy": (4, lambda a, b, f: a - b, ("", "_c")),
    "qd_sub_ieee": (4, lambda a, b, f: a - b, ("", "_c")),
    "qd_mul_sloppy": (4, lambda a, b, f: a * b, ("",)),
    "qd_mul_accurate": (4, lambda a, b, f: a * b, ("",)),
    "qd_div_sloppy": (4, lambda a, b, f: a / b, ("",)),
    "qd_div_accurate": (4, lambda a, b, f: a / b, ("",)),
    "qd_mul_f": (4, lambda a, b, f: a * f, ("",)),
    "qd_add_f": (4, lambda a, b, f: a + f, ("",)),
    "qd_sqrt": (4, lambda a, b, f: fsqrt(abs(a)), ("",)),
}


class Data:
    def __init__(self, d):
        self.d = d
        self.cache = {}

    def get(self, name, parts):
        key = (name, parts)
        if key not in self.cache:
            flat = load(os.path.join(self.d, name + ".bin"))
            self.cache[key] = values(flat, parts) if parts else [Fraction(x) for x in flat]
        return self.cache[key]


def exact_of(data, op, s):
    parts, fn, _ = OPS[op]
    tag = op[:2]
    a = data.get(tag + ("_ca" if s else "_a"), parts)
    # the subtractions' cancelling set is (ca, -cb), so that a - b cancels
    b = data.get(tag + (("_cbn" if "sub" in op else "_cb") if s else "_b"), parts)
    f = data.get("f", 0)
    return [fn(a[i], b[i], f[i]) for i in range(len(a))]


def errors(computed, exact):
    """max and median relative error, and the index of the max"""
    errs = []
    for c, e in zip(computed, exact):
        errs.append(abs(c - e) / abs(e) if e != 0 else abs(c))
    i = max(range(len(errs)), key=lambda k: errs[k])
    srt = sorted(errs)
    return errs[i], srt[len(srt) // 2], i


def evaluate(datadir, outdir, libs):
    data = Data(datadir)
    res = {}
    for op in OPS:
        parts = OPS[op][0]
        unit = U ** parts
        for s in OPS[op][2]:
            ex = exact_of(data, op, s)
            for lib in libs:
                path = os.path.join(outdir, "%s_%s%s.bin" % (lib, op, s))
                if not os.path.exists(path):
                    continue
                mx, med, i = errors(values(load(path), parts), ex)
                res.setdefault(op + s, {})[lib] = {
                    "max_rel": float(mx),
                    "max_units": float(mx / unit),
                    "med_units": float(med / unit),
                    "argmax": i,
                }
    return res


def show(res, libs):
    print("%-22s" % "op (units of u^n)" + "".join("%28s" % (l + " max / median") for l in libs))
    for op, r in res.items():
        cells = []
        for l in libs:
            if l in r:
                cells.append("%28s" % ("%.3g / %.3g" % (r[l]["max_units"], r[l]["med_units"])))
            else:
                cells.append("%28s" % "-")
        print("%-22s" % op + "".join(cells))


def selftest(datadir, outdir):
    """drop the last part of a result: the error must jump past each operation's bound"""
    data = Data(datadir)
    ok = True
    for op, bound in (("dd_mul", 5), ("qd_add_ieee", 8), ("qd_mul_accurate", 8), ("qd_sqrt", 32)):
        parts = OPS[op][0]
        flat = list(load(os.path.join(outdir, "md_%s.bin" % op)))
        good = errors(values(flat, parts), exact_of(data, op, ""))[0] / U ** parts
        for i in range(len(flat) // parts):
            flat[parts * i + parts - 1] = 0.0
        bad = errors(values(flat, parts), exact_of(data, op, ""))[0] / U ** parts
        fired = good <= bound < bad
        ok &= fired
        print("control %-16s intact %.3g u^%d, last part dropped %.3g u^%d: %s"
              % (op, good, parts, bad, parts, "fires" if fired else "DOES NOT FIRE"))
    return ok


def main():
    datadir, outdir = sys.argv[1], sys.argv[2]
    if sys.argv[3:] == ["--selftest"]:
        sys.exit(0 if selftest(datadir, outdir) else 1)
    libs = sys.argv[3:]
    res = evaluate(datadir, outdir, libs)
    show(res, libs)
    with open(os.path.join(outdir, "acc.json"), "w") as fh:
        json.dump(res, fh, indent=1)


if __name__ == "__main__":
    main()
