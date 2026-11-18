"""The emulator's square root (fpemu.od_sqrt) against multidouble's OD::sqrt, bit for bit, on positive octo-doubles:
the greedy parts of random values over a wide exponent range, ladders with a gap after a part, a zero part between
nonzero ones, and the top of the ladder H(2), each part in (1/2, 1] ulp of the one above, where the two-sum of a_0 and
a_1 moves a_0. Writes the inputs to a file, runs the crate on them (accumulator/acc_check, mode sqrt8) and
compares. usage: sqrt_bits.py [N [seed [manifest [control]]]]     prints the count of inputs and of mismatches;
exits 1 on a mismatch. control: the emulator skips its second Newton step (fpemu DROP 'sqrt_iter'), so every input
must mismatch, and the exit status is 1 unless all do. control2: the emulator skips the two-sum of a_0 and a_1 (fpemu
DROP 'sqrt_two_sum'), so some of the ladder inputs must mismatch, and the exit status is 1 unless one does. manifest: the Cargo.toml of a driver built against another copy of the crate (default
accumulator/acc_check)."""
import math
import os
import random
import struct
import subprocess
import sys
import tempfile
from fractions import Fraction as Q

import fpemu as F

HERE = os.path.dirname(os.path.abspath(__file__))


def bits(t):
    return struct.unpack('<Q', struct.pack('<d', t))[0]


def greedy(z, n=8):
    """the n greedy parts of z > 0, each the nearest double to what is left"""
    out = []
    for _ in range(n):
        x = float(z)
        out.append(x)
        z -= Q(x)
    return out


def inputs(N, seed):
    r = random.Random(seed)
    xs = []
    for k in range(N):
        e = r.randint(-300, 300)
        x = greedy(Q(r.getrandbits(400) | (1 << 399), 1 << 399) * Q(2) ** e)
        if k % 4 == 1:
            g = r.randint(1, 6)  # a gap after part g: the parts below it scaled down
            x = x[:g] + [t * 2.0 ** -r.randint(1, 40) for t in x[g:]]
        elif k % 4 == 2:
            x[r.randint(2, 6)] = 0.0  # a zero part between nonzero ones
        elif k % 4 == 3:
            for i in range(1, 8):  # the top of the ladder H(2): each part in (1/2, 1] ulp of the one above
                x[i] = r.choice((-1.0, 1.0)) * (0.5 + 0.5 * r.random()) * math.ulp(x[i - 1])
        xs.append(x)
    return xs


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    manifest = sys.argv[3] if len(sys.argv) > 3 else os.path.join(HERE, 'accumulator', 'acc_check', 'Cargo.toml')
    control = sys.argv[4] if len(sys.argv) > 4 else None
    if control == 'control':
        F.DROP = 'sqrt_iter'
    elif control == 'control2':
        F.DROP = 'sqrt_two_sum'
    xs = inputs(N, seed)
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, 'xs.txt')
        with open(path, 'w') as fh:
            for x in xs:
                fh.write(' '.join(f'{bits(t):016x}' for t in x) + '\n')
        out = subprocess.run(['cargo', 'run', '-q', '--release', '--manifest-path', manifest, '--', 'sqrt8', path],
                             capture_output=True, text=True, check=True).stdout.split('\n')
    if len([line for line in out if line.strip()]) != N:
        sys.exit(f'the driver printed {len(out)} lines for {N} inputs')
    bad = 0
    for x, line in zip(xs, out):
        got = F.od_sqrt([F.from_bits(bits(t)) for t in x])
        bad += ' '.join(f'{F.to_bits(y):016x}' for y in got) != line.strip()
    print(f'{N} inputs, {bad} mismatches' + (f' ({control})' if control else ''))
    if control == 'control':
        sys.exit(0 if bad == N else 1)
    if control == 'control2':
        sys.exit(0 if bad else 1)
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
