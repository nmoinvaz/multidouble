#!/bin/bash
# One process at a time, nice 10, a time cap per (op, p).
PY=/Users/nathan/Source/choptuik-large-d/.venv/bin/python
cd "$(dirname "$0")"
for p in 6 8 10 53; do
  for o in qd_sloppy_add qd_ieee_add qd_add_d qd_accurate_mul qd_sloppy_mul qd_mul_d qd_sloppy_div qd_accurate_div cp_certified_add cp_certified_add_d cp_bailey_add_renorm_M; do
    nice -n 10 $PY attack.py $o 10000000 7 $p 25 out/sweep_hits.jsonl
  done
done
