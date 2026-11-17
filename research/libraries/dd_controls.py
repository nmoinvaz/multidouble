"""Controls for dd_climb.py: the relative-error measure must fire on a broken double-word multiply (the x_l y_h term
dropped) and stay quiet (<= JMP17's bound) on JMP17's Algorithm 10 port (DoubleFloats mul_dddd_dd).
Exit status 1 if a control misbehaves."""
import random
import sys
from fractions import Fraction

import dd_climb as C
import dd_ports as D
from ports import F, add, mul


def broken_mul(x, y):
    hi, lo = D.jl_two_prod(x[0], y[0])
    t = add(lo, mul(x[0], y[1]))  # x[1] * y[0] dropped
    return list(D.bx_two_hilo_sum(hi, t))


def main():
    F.set_p(53)
    rng = random.Random(2)
    wb = wg = Fraction(0)
    for _ in range(3000):
        x, y = C.rand_dw(rng, 53), C.rand_dw(rng, 53)
        wb = max(wb, C.rel_err_u2(broken_mul, 'mul', x, y))
        wg = max(wg, C.rel_err_u2(D.df_mul, 'mul', x, y))
    print(f"broken mul worst {float(wb):.3g} u^2 (must exceed 7), DoubleFloats mul worst {float(wg):.3g} u^2 (must not)")
    ok = wb > 7 and wg <= 7
    print("PASS" if ok else "CONTROL FAILED")
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
