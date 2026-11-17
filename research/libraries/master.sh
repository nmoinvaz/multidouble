#!/bin/bash
# Priority queue, one process at a time under nice 10, each run with a time cap.
PY=/Users/nathan/Source/choptuik-large-d/.venv/bin/python
cd "$(dirname "$0")"
c() { nice -n 10 $PY climb.py "$1" "$2" "$3" "$4" out/climb.jsonl; }
c qd_ieee_add_fixed 1 53 150
c qd_ieee_add_fixed 2 8 90
c qd_ieee_add_fixed 3 10 60
nice -n 10 $PY attack.py qd_ieee_add_fixed 10000000 4 53 40 out/sweep_hits.jsonl
c gqd_mul_d 1 53 60
c gqd_add_d 1 53 45
for o in qd_accurate_mul qd_sloppy_mul cp_bailey_mul_renorm gqd_mul; do
  nice -n 10 timeout 100 $PY mul_cancel.py $o 53 30000 3 out/mul_cancel.jsonl
done
c cp_bailey_mul_renorm 1 53 60
for o in df_add boost_add df_mul boost_mul jmp_div_dw2 df_div boost_div boost_sqrt; do
  nice -n 10 $PY dd_climb.py $o 1 8 20 out/dd.jsonl
  nice -n 10 $PY dd_climb.py $o 1 53 30 out/dd.jsonl
done
echo MASTER-DONE
