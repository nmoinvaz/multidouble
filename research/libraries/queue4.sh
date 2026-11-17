#!/bin/bash
# CAMPARY's QD-like multiplication, after queue3, one process at a time under nice 10.
PY=/Users/nathan/Source/choptuik-large-d/.venv/bin/python
cd "$(dirname "$0")"
until grep -q QUEUE3-DONE out/queue3.log 2>/dev/null; do sleep 5; done
nice -n 10 $PY attack.py cp_bailey_mul_renorm 10000000 5 53 40 out/sweep_hits.jsonl
nice -n 10 timeout 120 $PY mul_cancel.py cp_bailey_mul_renorm 53 40000 3 out/mul_cancel.jsonl
nice -n 10 $PY climb.py cp_bailey_mul_renorm 1 53 60 out/climb.jsonl
echo QUEUE4-DONE
