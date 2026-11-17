#!/bin/bash
PY=/Users/nathan/Source/choptuik-large-d/.venv/bin/python
cd "$(dirname "$0")"
until grep -q FOLLOWUP-DONE out/followup.log 2>/dev/null; do sleep 5; done
nice -n 10 $PY climb.py l3_bf_mul 1 53 90 out/climb.jsonl
nice -n 10 $PY climb.py l3_bf_add 1 53 60 out/climb.jsonl
nice -n 10 $PY climb.py l3_bf_add 2 8 60 out/climb.jsonl
echo FOLLOWUP2-DONE
