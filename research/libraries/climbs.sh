#!/bin/bash
# Hill climbs, one process at a time under nice 10, each with a time cap (seconds).
PY=/Users/nathan/Source/choptuik-large-d/.venv/bin/python
cd "$(dirname "$0")"
run() { nice -n 10 $PY climb.py "$1" "$2" "$3" "$4" out/climb.jsonl; }
run qd_sloppy_add 1 53 120
run qd_accurate_mul 1 53 120
run cp_certified_add 1 53 120
run qd_ieee_add 1 53 90
run qd_mul_d 1 53 60
run qd_add_d 1 53 60
run qd_sloppy_mul 1 53 60
run qd_accurate_div 1 53 60
run qd_sloppy_div 1 53 60
run cp_bailey_add_renorm 1 53 30
run qd_sloppy_add 2 8 60
run qd_accurate_mul 2 8 60
run cp_certified_add 2 8 60
run cp_certified_add_d 2 8 60
echo CLIMBS-DONE
