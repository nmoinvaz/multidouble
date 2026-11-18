#!/usr/bin/env python3
"""Summarizes interleaved timing runs (run_series.sh) and the accuracy table (acc_eval.py).

  analyze.py RESULTSDIR ACC_JSON [CLUSTER]     writes RESULTSDIR/summary.md and RESULTSDIR/summary.json

Each run gives, per (op, mode), the minimum over its samples on one CPU cluster ("b", CPUs 6-9, the default, or "a",
CPUs 0-5; ldf_bench.c). The tables give the median over runs of that minimum with its range (min-max over runs),
and the signed difference of the medians, (md - ldf) / ldf, negative when multidouble is faster. A comparison whose
two ranges overlap is flagged.
"""

import collections
import glob
import json
import os
import re
import statistics
import sys

PAIRS = [
    # width, op, multidouble variant, LIB-Dekker-Float variant
    ("dd", "dd_add", "DD + (accurate, two two-sums)", "Float64x2_add (Dekker, branch on |hi|)"),
    ("dd", "dd_sub", "DD -", "Float64x2_sub"),
    ("dd", "dd_mul", "DD * (FMA two-prod)", "Float64x2_mul (Dekker split)"),
    ("dd", "dd_div", "DD / (three quotients)", "Float64x2_div (one correction)"),
    ("dd", "dd_mul_f", "DD::mul_f", "Float64x2_mul_dx2_d"),
    ("dd", "dd_sqrt", "none", "Float64x2_sqrt"),
    ("qd", "qd_add_sloppy", "QD + (sloppy_add)", "Float64x4_add_quick"),
    ("qd", "qd_add_ieee", "QD::ieee_add", "Float64x4_add_accurate"),
    ("qd", "qd_sub_sloppy", "QD -", "Float64x4_sub_quick"),
    ("qd", "qd_sub_ieee", "QD::ieee_sub", "Float64x4_sub_accurate"),
    ("qd", "qd_mul_sloppy", "QD * (sloppy_mul)", "Float64x4_mul_quick"),
    ("qd", "qd_mul_accurate", "QD::accurate_mul", "Float64x4_mul_accurate"),
    ("qd", "qd_div_sloppy", "QD / (sloppy_div)", "Float64x4_div_quick"),
    ("qd", "qd_div_accurate", "QD::accurate_div", "Float64x4_div_accurate"),
    ("qd", "qd_sqrt", "QD::sqrt", "Float64x4_sqrt"),
    ("qd", "qd_mul_f", "QD::mul_f", "Float64x4_mul_dx4_d"),
    ("qd", "qd_add_f", "QD::add_f", "Float64x4_add_dx4_d"),
]


def load_runs(d):
    runs = collections.defaultdict(list)  # (lib, op, mode) -> [record per run]
    for path in sorted(glob.glob(os.path.join(d, "run*_*.jsonl"))):
        for line in open(path):
            r = json.loads(line)
            runs[(r["lib"], r["op"], r["mode"])].append(r)
    return runs


def stat(recs, cluster):
    key = cluster + "_min_ns"
    v = [r[key] for r in recs if r[key] > 0]
    if not v:
        return None
    return {"median": statistics.median(v), "min": min(v), "max": max(v), "runs": len(v)}


def fmt(s):
    if s is None:
        return "-"
    if s["median"] >= 100:
        return "%.0f (%.0f-%.0f)" % (s["median"], s["min"], s["max"])
    if s["median"] >= 10:
        return "%.1f (%.1f-%.1f)" % (s["median"], s["min"], s["max"])
    return "%.2f (%.2f-%.2f)" % (s["median"], s["min"], s["max"])


def diff(m, l):
    if m is None or l is None:
        return "-", False
    d = 100.0 * (m["median"] - l["median"]) / l["median"]
    overlap = not (m["max"] < l["min"] or l["max"] < m["min"])
    return "%+.0f%%%s" % (d, " (overlap)" if overlap else ""), overlap


def units(acc, op, lib, s=""):
    r = acc.get(op + s, {}).get(lib)
    if r is None:
        return "-"
    x = r["max_units"]
    return "%.3g" % x


def main():
    d, accp = sys.argv[1], sys.argv[2]
    cluster = sys.argv[3] if len(sys.argv) > 3 else "b"
    runs = load_runs(d)
    acc = json.load(open(accp))
    out = []
    summary = {}
    loads = re.findall(r"load averages: ([0-9.]+)", open(os.path.join(d, "series.log")).read())
    loads = [float(x) for x in loads]
    out.append("Cluster %s; %d runs per library; 1-min load average %.1f-%.1f (median %.1f).\n"
               % (cluster, len(glob.glob(os.path.join(d, "run*_md.jsonl"))), min(loads), max(loads),
                  statistics.median(loads)))
    for width, title, u in (("dd", "double-double", "u^2"), ("qd", "quad-double", "u^4")):
        out.append("### %s\n" % title)
        out.append("| op | multidouble | LIB-Dekker-Float | thr md | thr ldf | thr diff | lat md | lat ldf | lat diff "
                   "| max err md (%s) | max err ldf (%s) |" % (u, u))
        out.append("|---|---|---|---|---|---|---|---|---|---|---|")
        for w, op, mv, lv in PAIRS:
            if w != width:
                continue
            row = {}
            for mode in ("thr", "lat"):
                m = stat(runs.get(("md", op, mode), []), cluster)
                l = stat(runs.get(("ldf", op, mode), []), cluster)
                dtxt, ov = diff(m, l)
                row[mode] = {"md": m, "ldf": l, "diff": dtxt, "overlap": ov}
            em, el = units(acc, op, "md"), units(acc, op, "ldf")
            if op + "_c" in acc:
                em += " / %s" % units(acc, op, "md", "_c")
                el += " / %s" % units(acc, op, "ldf", "_c")
            row["err"] = {"md": em, "ldf": el}
            summary[op] = row
            out.append("| %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s |" % (
                op, mv, lv, fmt(row["thr"]["md"]), fmt(row["thr"]["ldf"]), row["thr"]["diff"],
                fmt(row["lat"]["md"]), fmt(row["lat"]["ldf"]), row["lat"]["diff"], em, el))
        out.append("")
    out.append("### multidouble lanes (no LIB-Dekker-Float counterpart on arm64)\n")
    out.append("| op | thr ns/element | lat ns/lane op (8 elements) | scalar md thr | ldf scalar thr |")
    out.append("|---|---|---|---|---|")
    for key in sorted({k[1] for k in runs if k[0] == "md" and k[1][:2] in ("dv", "qv")}):
        sop = ("dd" if key.startswith("dv") else "qd") + key[2:]
        t = stat(runs[("md", key, "thr")], cluster)
        la = stat(runs[("md", key, "lat")], cluster)
        st = stat(runs.get(("md", sop, "thr"), []), cluster)
        lt = stat(runs.get(("ldf", sop, "thr"), []), cluster)
        summary[key] = {"thr": t, "lat": la}
        out.append("| %s | %s | %s | %s | %s |" % (key, fmt(t), fmt(la), fmt(st), fmt(lt)))
    text = "\n".join(out) + "\n"
    with open(os.path.join(d, "summary_%s.md" % cluster), "w") as fh:
        fh.write(text)
    with open(os.path.join(d, "summary_%s.json" % cluster), "w") as fh:
        json.dump(summary, fh, indent=1)
    print(text)


if __name__ == "__main__":
    main()
