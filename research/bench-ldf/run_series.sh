#!/bin/bash
# Interleaved timing runs, A B A B ..., one process at a time under nice -n 10, with uptime before each run.
#   run_series.sh OUTDIR PAIRS [ldf_binary md_binary]
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
out=$1
pairs=$2
ldf=${3:-$HOME/Source/ext-ldf/build/ldf_bench}
md=${4:-$here/md/target/release/md-bench-ldf}
mkdir -p "$out"
for i in $(seq 1 "$pairs"); do
    for lib in ldf md; do
        bin=$ldf
        [ "$lib" = md ] && bin=$md
        echo "run $i $lib start $(date -u '+%Y-%m-%dT%H:%M:%SZ') uptime $(uptime)" >> "$out/series.log"
        nice -n 10 "$bin" time "$here/data" > "$out/run${i}_${lib}.jsonl"
        echo "run $i $lib end $(date -u '+%Y-%m-%dT%H:%M:%SZ')" >> "$out/series.log"
    done
done
