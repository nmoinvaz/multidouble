"""Directed rounding of the numbers the scripts of this folder print.

A printed upper bound is rounded up and a printed lower bound down, at the digits shown, so no printed bound is
below (or above) the rational it stands for. The functions take a fractions.Fraction and return the text to print.

    python3 rounding.py   # checks the functions on values next to their rounding boundaries, with controls that
                          # round the wrong way and must be rejected, prints PASS
"""
from fractions import Fraction as Fr
import math


def _bits(x, bits, upward):
    """A positive rational rounded to `bits` significant bits, up or down."""
    num, den = x.numerator, x.denominator
    shift = bits - (num.bit_length() - den.bit_length())
    if shift >= 0:
        q, r = divmod(num << shift, den)
        return Fr(q + (1 if upward and r else 0), 1 << shift)
    q, r = divmod(num, den << -shift)
    return Fr(q + (1 if upward and r else 0)) * (1 << -shift)


def _lg2(x, k, upward):
    """The least (upward) or greatest multiple c of 10^-k with x <= 2^c (x >= 2^c), as an integer c 10^k."""
    x = Fr(x)
    assert x > 0
    s = 10 ** k
    # x itself when it is short, else its rounding outward to 192 bits: the comparison below is then exact for a
    # value on the safe side of x
    if x.numerator.bit_length() + x.denominator.bit_length() > 400:
        x = _bits(x, 192, upward)
    b = x.numerator.bit_length() - x.denominator.bit_length()
    a = math.floor((b + math.log2(float(x / Fr(2) ** b))) * s)
    xs = x ** s

    def le(c):  # x <= 2^(c / s)
        return xs <= Fr(2) ** c

    def ge(c):  # x >= 2^(c / s)
        return xs >= Fr(2) ** c

    if upward:
        while not le(a):
            a += 1
        while le(a - 1):
            a -= 1
    else:
        while not ge(a):
            a -= 1
        while ge(a + 1):
            a += 1
    return a


def _text(a, k):
    sign = '-' if a < 0 else ''
    a = abs(a)
    return f'{sign}{a // 10 ** k}.{a % 10 ** k:0{k}d}' if k else f'{sign}{a}'


def lg2_up(x, k=2):
    """log2 x rounded up to k decimals: x <= 2^(the value printed)."""
    return _text(_lg2(x, k, True), k)


def lg2_down(x, k=2):
    """log2 x rounded down to k decimals: x >= 2^(the value printed)."""
    return _text(_lg2(x, k, False), k)


def dec_up(x, k=6):
    """x >= 0 rounded up to k decimals."""
    x = Fr(x)
    assert x >= 0
    return _text(-(-x.numerator * 10 ** k // x.denominator), k)


def dec_down(x, k=6):
    """x >= 0 rounded down to k decimals."""
    x = Fr(x)
    assert x >= 0
    return _text(x.numerator * 10 ** k // x.denominator, k)


def sig_up(x, s=6):
    """x > 0 rounded up to s significant digits, as mantissa and power of ten."""
    x = Fr(x)
    assert x > 0
    e = len(str(x.numerator)) - len(str(x.denominator))
    while Fr(10) ** e > x:
        e -= 1
    while Fr(10) ** (e + 1) <= x:
        e += 1
    y = x / Fr(10) ** (e - s + 1)
    m = -(-y.numerator // y.denominator)
    if m == 10 ** s:
        m //= 10
        e += 1
    digits = str(m)
    if -5 <= e < s:  # plain decimal
        if e >= 0:
            frac = digits[e + 1:]
            return digits[: e + 1] + ('.' + frac if frac else '')
        return '0.' + '0' * (-e - 1) + digits
    return f'{digits[0]}.{digits[1:]}e{e:+03d}' if s > 1 else f'{digits}e{e:+03d}'


def _selfcheck(lg_up, lg_down, d_up, d_down, s_up):
    """True if the functions round as their names say, on values next to their rounding boundaries."""
    ok = True
    for k in (0, 1, 2, 4):
        for c in (-43907, 3792, -5, 0, 7, 100000):
            if c % 10 ** k:
                continue
            for off in (-1, 0, 1):
                x = Fr(2) ** (c // 10 ** k) * (1 + Fr(off, 2 ** 80))
                ok &= lg_up(x, k) == _text(c + (1 if off > 0 else 0), k)
                ok &= lg_down(x, k) == _text(c - (1 if off < 0 else 0), k)
    ok &= lg_up(Fr(3), 2) == '1.59' and lg_down(Fr(3), 2) == '1.58' and lg_up(Fr(1, 3), 1) == '-1.5'
    ok &= lg_up(Fr(2) ** -439 * Fr(1001, 1000), 2) == '-438.99'
    ok &= d_up(Fr(3163167393, 10 ** 9), 6) == '3.163168' and d_down(Fr(3163167393, 10 ** 9), 6) == '3.163167'
    ok &= d_up(Fr(2), 3) == '2.000' and s_up(Fr(1119746000014, 10 ** 6), 4) == '1.120e+06'
    ok &= s_up(Fr(72), 3) == '72.0' and s_up(Fr(999999, 10 ** 7), 3) == '0.100' and s_up(Fr(5, 10 ** 9), 2) == '5.0e-09'
    return ok


if __name__ == '__main__':
    good = _selfcheck(lg2_up, lg2_down, dec_up, dec_down, sig_up)
    # controls: a bound rounded the wrong way must be rejected
    wrong_lg = not _selfcheck(lg2_down, lg2_down, dec_up, dec_down, sig_up)
    wrong_dec = not _selfcheck(lg2_up, lg2_down, dec_down, dec_down, sig_up)
    print(f'controls: log2 rounded down in place of up is rejected: {wrong_lg}; decimals rounded down in place of '
          f'up are rejected: {wrong_dec}')
    ok = good and wrong_lg and wrong_dec
    print('PASS' if ok else 'FAIL')
    raise SystemExit(0 if ok else 1)
