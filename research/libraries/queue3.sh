#!/bin/bash
# Double-word maxima, after queue2, one process at a time under nice 10.
PY=/Users/nathan/Source/choptuik-large-d/.venv/bin/python
cd "$(dirname "$0")"
until grep -q QUEUE2-DONE out/queue2.log 2>/dev/null; do sleep 5; done
for o in df_add boost_add df_mul boost_mul jmp_div_dw2 df_div boost_div boost_sqrt; do
  nice -n 10 $PY dd_climb.py $o 1 8 30 out/dd.jsonl
  nice -n 10 $PY dd_climb.py $o 1 53 45 out/dd.jsonl
done
echo QUEUE3-DONE
