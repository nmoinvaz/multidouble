#!/bin/bash
# Runs after climbs.sh finishes, one process at a time under nice 10.
PY=/Users/nathan/Source/choptuik-large-d/.venv/bin/python
cd "$(dirname "$0")"
until grep -q CLIMBS-DONE out/climb.log; do sleep 5; done
for p in 6 8 10 53; do
  for o in qd_accurate_mul qd_sloppy_mul cp_certified_add; do
    nice -n 10 timeout 120 $PY mul_cancel.py $o $p 40000 3 out/mul_cancel.jsonl
  done
done
echo QUEUE2-DONE
