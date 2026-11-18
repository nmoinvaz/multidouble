"""Review check of sqrt_bits.py's inputs: do they reach the quick two-sum of (a_0, a_1)? Runs the crate's driver
(manifest, built against #79) on sqrt_bits.py's own inputs and on ladder inputs with |a_1| between half an ulp and an
ulp of a_0, and compares with fpemu.od_sqrt and with a copy of it without the quick two-sum.
usage: fable_sqrt_bits_variants.py manifest [N [seed]]"""
import math
import os
import random
import subprocess
import sys
import tempfile

import fpemu as F
import sqrt_bits as S


def od_sqrt_no_fast2sum(x, mode=None):
    """fpemu.od_sqrt with (a0, a1) taken as they are"""
    n = len(x)
    if x[0][0] == 0:
        return [F.PZ] * n
    s = F.pow2_floor(F.fsqrt(x[0]))
    inv = F.div(F.ONE, s)
    a = [F.mul(F.mul(xk, inv), inv) for xk in x]
    a0, a1 = a[0], a[1]
    sh = F.fsqrt(a0)
    yh, yl = F.quick_two_sum(sh, F.div(F.add(a1, F.fma(F.neg(sh), sh, a0)), F.add(sh, sh)))
    th = F.div(F.ONE, yh)
    ch, cl1 = F.two_prod(yh, th)
    g, tl1 = F.quick_two_sum(ch, F.mul(yl, th))
    rh, rl = F.quick_two_sum(g, F.add(tl1, cl1))
    r0, r1 = F.quick_two_sum(th, F.div(F.sub(F.sub(F.ONE, rh), rl), yh))
    r = [r0, r1] + [F.PZ] * (n - 2)
    h = [F.mul(ak, F.HALF) for ak in a]
    c = F.od_add_f(F.od_neg(F.od_mul(h, F.od_mul(r, r, mode), mode)), F.HALF, mode)
    c2 = F.od_mul(c, c, mode)
    w = F.od_add(c, F.od_add(c2, [F.mul(t, F.HALF) for t in c2], mode), mode)
    r = F.od_add(r, F.od_mul(w, r, mode), mode)
    c = F.od_add_f(F.od_neg(F.od_mul(h, F.od_mul(r, r, mode), mode)), F.HALF, mode)
    r = F.od_add(r, F.od_mul(c, r, mode), mode)
    r = F.od_mul(r, a, mode)
    return [F.mul(rk, s) for rk in r]


def ladder_inputs(N, seed):
    """|x_i| in (1/2, 1] ulp of the part above: H(2), where the quick two-sum of (a_0, a_1) moves a_0"""
    r = random.Random(seed)
    xs = []
    for _ in range(N):
        x = [math.ldexp(1 + r.random(), r.randint(-300, 300))]
        for _ in range(7):
            x.append(r.choice((-1.0, 1.0)) * (0.5 + 0.5 * r.random()) * math.ulp(x[-1]))
        xs.append(x)
    return xs


def run(manifest, xs):
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, 'xs.txt')
        with open(path, 'w') as fh:
            for x in xs:
                fh.write(' '.join(f'{S.bits(t):016x}' for t in x) + '\n')
        out = subprocess.run(['cargo', 'run', '-q', '--release', '--manifest-path', manifest, '--', 'sqrt8', path],
                             capture_output=True, text=True, check=True).stdout.split('\n')
    assert len(out) >= len(xs), (len(out), len(xs))
    return [line.strip() for line in out[:len(xs)]]


def count(xs, lines, f):
    return sum(' '.join(f'{F.to_bits(y):016x}' for y in f([F.from_bits(S.bits(t)) for t in x])) != line
               for x, line in zip(xs, lines))


def main():
    manifest = sys.argv[1]
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    for name, xs in (("sqrt_bits.py's inputs", S.inputs(N, seed)), ('ladder inputs, |a_1| in (1/2, 1] ulp', ladder_inputs(N, seed))):
        moved = sum(x[0] + x[1] != x[0] for x in xs)
        lines = run(manifest, xs)
        print(f'{name}: {len(xs)}; the quick two-sum moves a_0 on {moved}; mismatches: emulator {count(xs, lines, F.od_sqrt)}, '
              f'emulator without the quick two-sum {count(xs, lines, od_sqrt_no_fast2sum)}')


if __name__ == '__main__':
    main()
