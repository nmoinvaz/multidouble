"""Random operands satisfying H(theta) (|a_i| <= (theta u)^i |a_0|), as reffp floats, for any p and n."""
from fractions import Fraction
import random

import reffp as F


def rand_float(rng, e_top):
    """a random p-bit float with exponent e_top (value in [2^e_top, 2^(e_top+1)))"""
    m = rng.randrange(1 << (F.P - 1), 1 << F.P)
    return F.rn(m, e_top - F.P + 1)


def operand(rng, n, theta, e0=0, style='mix', sign=None):
    """n parts satisfying H(theta). style: 'edge' (parts near the ladder), 'greedy' (|a_{i+1}| <= ulp(a_i)/2),
    'mix' (random depths, zero parts, far parts)"""
    s0 = sign if sign is not None else rng.choice((1, -1))
    a0 = rand_float(rng, e0)
    if s0 < 0:
        a0 = F.neg(a0)
    parts = [a0]
    u = Fraction(1, 2 ** F.P)
    A0 = abs(F.frac(a0))
    st = style if style != 'mix' else rng.choice(('edge', 'greedy', 'deep', 'zero'))
    for i in range(1, n):
        bound = (theta * u) ** i * A0
        if st == 'greedy':
            prev = parts[-1]
            if prev[0] == 0:
                parts.append(F.ZERO)
                continue
            lim = F.frac(F.ulp(prev)) / 2
            bound = min(bound, lim)
        if st == 'zero' and rng.random() < 0.3:
            parts.append(F.ZERO)
            continue
        # top exponent with 2^(e+1) <= bound, or the edge itself
        e = bound.numerator.bit_length() - bound.denominator.bit_length()
        while Fraction(2) ** (e + 1) > bound:
            e -= 1
        if st == 'deep' and rng.random() < 0.5:
            e -= rng.randrange(0, 3 * F.P)
        elif st != 'edge':
            e -= rng.randrange(0, 4)
        x = rand_float(rng, e)
        if st in ('edge', 'greedy') and rng.random() < 0.5:
            # the largest float <= bound
            y = F.rn(int(bound * 2 ** (F.P - e)) , e - F.P)
            while F.frac(y) > bound:
                y = F.sub(y, F.ulp(y))
            if y[0] != 0 and F.frac(y) > 0:
                x = y
        if rng.random() < 0.5:
            x = F.neg(x)
        parts.append(x)
    for i in range(1, n):
        assert abs(F.frac(parts[i])) <= (theta * u) ** i * A0, (i, parts)
    return parts


def check_H(a, theta):
    u = Fraction(1, 2 ** F.P)
    A0 = abs(F.frac(a[0]))
    return all(abs(F.frac(a[i])) <= (theta * u) ** i * A0 for i in range(1, len(a)))
