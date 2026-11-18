#!/bin/bash
# Builds both harnesses. LIB-Dekker-Float is compiled from its headers only (header-only arithmetic), with this
# script's compiler command; binaries go to $LDF_BUILD (outside this repository, beside the clone).
#
#   ldf_bench, md-bench-ldf      the timed builds: loop vectorizer off on both sides, SLP vectorizer on
#   ldf_bench_def, md (target-def)  the same with the loop vectorizer on (compiler defaults), for one sensitivity pair
#   ldf_bench_ieee, ldf_bench_nofma accuracy only: FLOAT64X4_IEEE_MODE, and -ffp-contract=off
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
LDF_SRC=${LDF_SRC:-$HOME/Source/ext-ldf/LIB-Dekker-Float}
LDF_BUILD=${LDF_BUILD:-$HOME/Source/ext-ldf/build}
mkdir -p "$LDF_BUILD"
CFLAGS="-std=c11 -O3 -mcpu=native -ffp-contract=on -Wall -Wextra"
clang $CFLAGS -fno-vectorize -I "$LDF_SRC" "$here/ldf_bench.c" -o "$LDF_BUILD/ldf_bench"
clang $CFLAGS '-DPREFIX="ldfdef"' -I "$LDF_SRC" "$here/ldf_bench.c" -o "$LDF_BUILD/ldf_bench_def"
clang $CFLAGS -fno-vectorize -DFLOAT64X4_IEEE_MODE '-DPREFIX="ldfieee"' -I "$LDF_SRC" "$here/ldf_bench.c" \
    -o "$LDF_BUILD/ldf_bench_ieee"
clang ${CFLAGS/-ffp-contract=on/-ffp-contract=off} -fno-vectorize '-DPREFIX="ldfnofma"' -I "$LDF_SRC" \
    "$here/ldf_bench.c" -o "$LDF_BUILD/ldf_bench_nofma"
cd "$here/md"
RUSTFLAGS="-C target-cpu=native -C no-vectorize-loops" cargo build --release --offline
RUSTFLAGS="-C target-cpu=native" CARGO_TARGET_DIR="$here/md/target-def" cargo build --release --offline
clang --version | head -1
rustc --version
