#!/bin/bash
PY=/Users/nathan/Source/choptuik-large-d/.venv/bin/python
cd "$(dirname "$0")"
until grep -q MASTER-DONE out/master.log 2>/dev/null; do sleep 5; done
nice -n 10 $PY climb.py qd_ieee_add_fix2 1 53 120 out/climb.jsonl
nice -n 10 $PY climb.py qd_ieee_add_fix2 2 8 60 out/climb.jsonl
echo FOLLOWUP-DONE
