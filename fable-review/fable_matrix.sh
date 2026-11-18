#!/bin/bash
# fable_matrix.sh DIR [extra cargo args]: the test matrix of a worktree, one build at a time under nice
# (default, portable, mutate), into DIR/matrix-*.log with the pass and fail counts printed.

dir="$1"
export CARGO_TARGET_DIR="$dir/target"  # one per worktree: a shared one reuses the first worktree's library (same package hash, older source mtimes)
cd "$dir" || exit 1
for cfg in default portable mutate; do
    feat=()
    [ "$cfg" != default ] && feat=(--features "$cfg")
    log="matrix-$cfg.log"
    nice -n 10 cargo test --release --no-fail-fast ${feat[@]+"${feat[@]}"} >"$log" 2>&1
    echo "$cfg: exit $? passed $(grep -h 'test result' "$log" | awk '{s+=$4} END {print s}') failed $(grep -h 'test result' "$log" | awk '{s+=$6} END {print s}') ignored $(grep -h 'test result' "$log" | awk '{s+=$8} END {print s}')"
done
date -u '+%Y-%m-%d %H:%M'
