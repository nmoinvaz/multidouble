#!/usr/bin/env python3
"""Operands for the multidouble / LIB-Dekker-Float comparison, written once and read by both harnesses.

Every value is a random rational of 320 significant bits, split greedily into round-to-nearest doubles (the canonical
nonoverlapping expansion). Files are raw little-endian f64, values interleaved by part:

  dd_a, dd_b    N double-doubles (2 f64 each), random signs, exponents in [-20, 20]
  dd_ca, dd_cb  N near-cancelling pairs, b = -a (1 + e) with |e| = 2^-k, k uniform in [1, 110]
  dd_cbn        -dd_cb, the operand that makes a - b cancel
  qd_a, qd_b    N quad-doubles (4 f64 each), as dd_a, dd_b
  qd_ca, qd_cb  N near-cancelling pairs, k uniform in [1, 215]; qd_cbn = -qd_cb
  f             N doubles, random signs, exponents in [-20, 20] (operand of mul_f, add_f)
  lat_dd, lat_qd, lat_f  N operands for the dependent chains, magnitudes in [0.5, 2), random signs

Usage: gen_inputs.py OUTDIR [N] [SEED]
"""

import hashlib
import os
import random
import struct
import sys
from fractions import Fraction

BITS = 320


def rand_mag(rng, emin, emax):
    """a random rational in [1, 2) * 2^e with BITS significant bits"""
    m = rng.getrandbits(BITS - 1) | (1 << (BITS - 1))
    e = rng.randint(emin, emax)
    return Fraction(m, 1 << (BITS - 1)) * Fraction(2) ** e


def expand(x, parts):
    """greedy round-to-nearest split of a rational into `parts` doubles"""
    out = []
    r = Fraction(x)
    for _ in range(parts):
        d = float(r)  # correctly rounded
        out.append(d)
        r -= Fraction(d)
    return out


def write(path, vals):
    with open(path, "wb") as fh:
        fh.write(struct.pack("<%dd" % len(vals), *vals))


def main():
    outdir = sys.argv[1]
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 4096
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 20261117
    rng = random.Random(seed)
    os.makedirs(outdir, exist_ok=True)

    def sgn():
        return 1 if rng.random() < 0.5 else -1

    def rand_val(emin=-20, emax=20):
        return sgn() * rand_mag(rng, emin, emax)

    def near_one():
        # [0.5, 2), random sign
        return sgn() * rand_mag(rng, -1, 0)

    files = {}
    for parts, tag, kmax in ((2, "dd", 110), (4, "qd", 215)):
        a, b, ca, cb = [], [], [], []
        for _ in range(n):
            a += expand(rand_val(), parts)
            b += expand(rand_val(), parts)
            x = rand_val()
            k = rng.randint(1, kmax)
            e = sgn() * Fraction(1, 1 << k) * (1 + Fraction(rng.getrandbits(60), 1 << 60))
            ca += expand(x, parts)
            cb += expand(-x * (1 + e), parts)
        files[tag + "_a"] = a
        files[tag + "_b"] = b
        files[tag + "_ca"] = ca
        files[tag + "_cb"] = cb
        files[tag + "_cbn"] = [-x for x in cb]
    files["f"] = [float(rand_val()) for _ in range(n)]
    files["lat_dd"] = [d for _ in range(n) for d in expand(near_one(), 2)]
    files["lat_qd"] = [d for _ in range(n) for d in expand(near_one(), 4)]
    files["lat_f"] = [float(near_one()) for _ in range(n)]

    h = hashlib.sha256()
    for name in sorted(files):
        write(os.path.join(outdir, name + ".bin"), files[name])
        with open(os.path.join(outdir, name + ".bin"), "rb") as fh:
            h.update(name.encode() + fh.read())
    with open(os.path.join(outdir, "meta.txt"), "w") as fh:
        fh.write("n %d\nseed %d\nsha256 %s\n" % (n, seed, h.hexdigest()))
    print("n", n, "seed", seed, "sha256", h.hexdigest())


if __name__ == "__main__":
    main()
