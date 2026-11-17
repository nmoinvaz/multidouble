#!/bin/bash
PY=/Users/nathan/Source/choptuik-large-d/.venv/bin/python
cd "$(dirname "$0")"
until grep -q FOLLOWUP2-DONE out/followup2.log 2>/dev/null; do sleep 5; done
nice -n 10 $PY dd_climb.py boost_div 7 53 90 out/dd.jsonl
nice -n 10 $PY dd_climb.py df_div 7 53 60 out/dd.jsonl
nice -n 10 $PY dd_climb.py boost_mul 7 53 45 out/dd.jsonl
echo FOLLOWUP3-DONE
