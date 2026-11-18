"""Runs a p = 53, n = 8 construction (construct.py's file) through multidouble's OdAcc (add, and add_prod with b = 1)
and through the referee's model, and measures each error exactly from the returned parts.

python3 run53.py out/c53_2048.txt [prefixes...]
"""
from fractions import Fraction as Fr
from math import log2
import subprocess
import sys

import construct as C
import reffp as F
from crosscheck import BIN, hx

F.setp(53)
u = Fr(1, 2 ** 53)


def main():
    terms = C.load(sys.argv[1])
    prefixes = [int(v) for v in sys.argv[2:]] or [len(terms)]
    one = [(1, 0)] + [F.ZERO] * 7
    lines = []
    for K in prefixes:
        lines.append('Z')
        lines += [f'X {hx(a)}' for a in terms[:K]]
        lines.append('F')
        lines.append('Z')
        lines += [f'P {hx(a)} {hx(one)}' for a in terms[:K]]
        lines.append('F')
    out = subprocess.run([BIN], input='\n'.join(lines) + '\n', capture_output=True, text=True,
                         check=True).stdout.split('\n')
    print(f"{'K':>5} {'model err/(u^8|Z|)':>20} {'log2':>8} {'crate add':>8} {'crate add_prod':>14} "
          f"{'W/|Z|-1':>10} {'err/(8(8+K)u^8W)':>16}")
    for i, K in enumerate(prefixes):
        ts = terms[:K]
        Z = sum(sum(F.frac(v) for v in a) for a in ts)
        W = sum(abs(F.frac(a[0])) for a in ts)
        r = C.evaluate(ts, 8, 53)
        res = []
        for j in (0, 1):
            L = [F.from_f64_hex(h) for h in out[4 * i + 2 * j].split()[1:]]
            R = [F.from_f64_hex(h) for h in out[4 * i + 2 * j + 1].split()[1:]]
            same = L == r['levels'] and R == r['x']
            err = abs(Z - sum(F.frac(v) for v in R))
            res.append((same, err))
        err = r['err']
        assert all(e == err for _, e in res)
        print(f"{K:>5} {float(err / (u ** 8 * abs(Z))):>20.6g} {log2(err / (u ** 8 * abs(Z))):>8.3f} "
              f"{'same' if res[0][0] else 'DIFF':>8} {'same' if res[1][0] else 'DIFF':>14} "
              f"{float(W / abs(Z) - 1):>10.3g} {float(err / (8 * (8 + K) * u ** 8 * W)):>16.4g}")


if __name__ == '__main__':
    main()
