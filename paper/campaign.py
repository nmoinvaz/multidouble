#!/usr/bin/env python3
"""The tests of Theorems 9, 15 and 19, Corollary 18 and Proposition 24 that Section VIII reports, run from this folder
on the emulator fpemu.py, with multidouble's bits taken through accumulator/acc_check.

    python3 campaign.py bits [N [seed]]   # ADD, ADDF, MULF, MUL and DIV at p = 53 and n = 8, N inputs each (default
                                          # 10000): the emulator against multidouble, bit for bit, each error against
                                          # its bound in exact arithmetic, and the results against the ladder H(2)
    python3 campaign.py small             # exhaustive runs at small precision: Theorem 9 on every tuple of a family
                                          # of terms in every order, Theorems 15 and 19 on families of ladders
    python3 campaign.py sharp             # the inputs of Proposition 24 for n = 2 to 8
    python3 campaign.py all [N [seed]]    # the three; campaign/ holds the output of each

Each mode ends with PASS or FAIL and exits nonzero on FAIL. Each has controls that must fire: an emulator with one
error term dropped or a broken two-sum, a second pass with Fast2Sum throughout, and a halved bound.
"""
import functools
import os
import random
import subprocess
import sys
import tempfile
from fractions import Fraction as Fr
from itertools import product

import fpemu as E
from constants import consts
from div_consts import div_consts
from rounding import dec_up

print = functools.partial(print, flush=True)
HERE = os.path.dirname(os.path.abspath(__file__))
MANIFEST = os.path.join(HERE, 'accumulator', 'acc_check', 'Cargo.toml')


def val(x):
    m, e = x
    return Fr(0) if m == 0 else Fr(m) * Fr(2) ** e


def total(xs):
    return sum((val(x) for x in xs), Fr(0))


def on_ladder(a, p, theta=2):
    """H(theta), exactly"""
    a0 = abs(val(a[0]))
    rho = Fr(theta, 2 ** p)
    return all(abs(val(x)) <= rho ** i * a0 for i, x in enumerate(a))


def bound(op, a, b, n, p, kappa):
    """(|Z|, the bound of Theorem 15 or 19) for the exact result Z"""
    u = Fr(1, 2 ** p)
    A = total(a)
    if op in ('add', 'mul', 'div'):
        B, b0 = total(b), abs(val(b[0]))
    else:
        B = b0 = None
    a0 = abs(val(a[0]))
    if op == 'add':
        Z, M = A + B, a0 + b0
    elif op == 'addf':
        Z, M = A + val(b), a0 + abs(val(b))
    elif op == 'mul':
        Z, M = A * B, a0 * b0
    elif op == 'mulf':
        Z, M = A * val(b), a0 * abs(val(b))
    else:
        Z = A / B
        return Z, (u ** n + kappa * u ** (n + 1)) * abs(Z)
    return Z, u ** n * abs(Z) + kappa * u ** (n + 1) * M


OPS = {'add': E.od_add, 'addf': E.od_add_f, 'mulf': E.od_mul_f, 'mul': E.od_mul, 'div': E.od_div}
CONST_NAME = {'add': 'add', 'addf': 'add_f', 'mulf': 'mul_f', 'mul': 'mul'}


def kappa_of(op, n, p):
    if op == 'div':
        return div_consts(n, p, 2)['K']
    return consts(CONST_NAME[op], n, 2, Fr(1, 2 ** p))['kappa']


# ---------------------------------------------------------------------------------------------------------------
# bits: p = 53, n = 8, against the crate
# ---------------------------------------------------------------------------------------------------------------

KINDS = ('dense', 'top', 'gap', 'zero', 'mixed')


def operand(rng, kind, e0, n=8, p=53, gap=10):
    """An n-part operand on H(2) with leading exponent e0: dense parts, each below half an ulp of the one above;
    parts at the top of the ladder, (2u)^i |a_0|; gaps of up to `gap` bits; zero parts; or parts anywhere below
    the ladder's edge."""
    def mant():
        return rng.getrandbits(p - 1) | (1 << (p - 1))

    def sign():
        return rng.choice((1, -1))

    m0 = mant()
    a = [E.rnd(sign() * m0, e0 - (p - 1))]
    top = e0
    for i in range(1, n):
        if kind == 'top':
            a.append(E.rnd(sign() * m0, e0 - (p - 1) - (p - 1) * i))
            continue
        if kind == 'mixed':
            t = e0 - (p - 1) * i - rng.randint(1, gap)
        else:
            t = top - p - 1 - (rng.randint(0, gap) if kind in ('gap', 'zero') else 0)
            t = min(t, e0 - (p - 1) * i - 1)  # after a zero part, still below the ladder's edge
        if kind == 'zero' and rng.random() < 0.3:
            a.append(E.PZ)
        else:
            a.append(E.rnd(sign() * mant(), t - (p - 1)))
            top = t
    return a


def scalar(rng, e0, p=53):
    return E.rnd(rng.choice((1, -1)) * (rng.getrandbits(p - 1) | (1 << (p - 1))), e0 - (p - 1))


def make_inputs(op, N, rng):
    """N operand pairs for the operation, cycling over the kinds; for ADD every fifth pair cancels."""
    out = []
    k = 0
    while len(out) < N:
        ka, kb = KINDS[k % 5], KINDS[(k // 5) % 5]
        ea = rng.randint(-20, 20)
        a = operand(rng, ka, ea, gap=6 if op == 'div' else 10)
        if op in ('addf', 'mulf'):
            b = scalar(rng, ea + rng.randint(-70, 70) if op == 'addf' else rng.randint(-20, 20))
        else:
            eb = ea + rng.choice((0, 0, rng.randint(-60, 60))) if op == 'add' else rng.randint(-20, 20)
            b = operand(rng, kb, eb, gap=6 if op == 'div' else 10)
            if op == 'add' and k % 5 == 4:
                # a cancelling pair: b = -a in its leading parts, with other parts below
                j = rng.randint(1, 7)
                tail = operand(rng, 'dense', 0)
                low = min((abs(x[0]).bit_length() + x[1] - 1) for x in a[:j] if x[0] != 0)
                # the tail starts below the last part kept and below the ladder's edge at its index
                start = min(low - 54, ea - 53 * j - 1)
                shift = start - (abs(tail[0][0]).bit_length() + tail[0][1] - 1)
                b = [E.neg(x) for x in a[:j]] + [(m, e + shift) if m else (m, e) for m, e in tail[: 8 - j]]
        if not on_ladder(a, 53) or (op in ('add', 'mul', 'div') and not on_ladder(b, 53)):
            raise AssertionError('an operand left the ladder')
        dense = ka == 'dense' and (op in ('addf', 'mulf') or (kb == 'dense' and not (op == 'add' and k % 5 == 4)))
        out.append((a, b, dense))
        k += 1
    return out


def hexline(parts):
    return ' '.join(f'{E.to_bits(x):016x}' for x in parts)


def crate(mode, lines):
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, 'in.txt')
        with open(path, 'w') as f:
            f.write('\n'.join(lines) + '\n')
        out = subprocess.run(['cargo', 'run', '-q', '--release', '--manifest-path', MANIFEST, '--', mode, path],
                             capture_output=True, text=True, check=True).stdout
    return out.split('\n')[: len(lines)]


def emu(op, a, b, drop=None, mutate=None):
    """the emulator's result, or None if a value of the run left binary64's normal range"""
    E.set_p(53, range_check=True)
    E.DROP, E.MUTATE = drop, mutate
    try:
        x = OPS[op](a, b)
    finally:
        E.DROP = E.MUTATE = None
    return None if E.range_hits else x


CRATE_MODE = {'add': 'addn8', 'addf': 'addf8', 'mulf': 'mulf8', 'mul': 'mul8', 'div': 'div8'}
CONTROL = {'add': ('add_t1', None, "the error of a_1 + b_1 dropped"),
           'addf': (None, 'two_sum_sign', "two-sum's error with the wrong sign"),
           'mulf': ('mulf_e3', None, "the error of a_3 f dropped"),
           'mul': ('mul_e23', None, "the error of a_2 b_3 dropped"),
           'div': ('div_rem', None, "one remainder update skipped")}


def bits(N, seed):
    ok = True
    print(f'bits: p = 53, n = 8, {N} inputs per operation, seed {seed}; operands dense, at the top of the ladder, '
          f'with gaps, with zero parts and anywhere below the edge; every fifth ADD pair cancels')
    for op in ('add', 'addf', 'mulf', 'mul', 'div'):
        rng = random.Random(seed * 1000 + len(op) * 7 + ord(op[0]) + ord(op[-1]))
        kappa = kappa_of(op, 8, 53)
        runs = []
        for a, b, dense in make_inputs(op, N, rng):
            x = emu(op, a, b)
            if x is not None:
                runs.append((a, b, x, dense))
        skipped = N - len(runs)
        lines = [hexline(a + (b if isinstance(b, list) else [b])) for a, b, _, _ in runs]
        got = crate(CRATE_MODE[op], lines)
        mism = sum(hexline(x) != g for (_, _, x, _), g in zip(runs, got))
        worst, worst_lead, worst_dense, ndense, off, checked = Fr(0), Fr(0), Fr(0), 0, 0, 0
        u8 = Fr(1, 2 ** 424)
        for a, b, x, dense in runs:
            Z, bd = bound(op, a, b, 8, 53, kappa)
            err = abs(Z - total(x))
            if bd:
                worst = max(worst, err / bd)
            if Z:
                worst_lead = max(worst_lead, err / (u8 * abs(Z)))
                if dense:
                    ndense += 1
                    worst_dense = max(worst_dense, err / (u8 * abs(Z)))
            same_sign = op in ('mul', 'mulf') or (op != 'div' and (a[0][0] > 0) == ((b[0] if op == 'add' else b)[0] > 0))
            if same_sign and x[0][0] != 0:
                checked += 1
                off += not on_ladder(x, 53)
        line = (f'{op.upper():4s} {len(runs)} inputs ({skipped} left the normal range and are not counted), '
                f'{mism} mismatches with multidouble; largest error / bound {dec_up(worst, 4)}')
        if op in ('mul', 'mulf', 'div'):
            line += f', largest error / (u^8 |Z|) {dec_up(worst_lead, 4)}'
        if op != 'div':
            line += f'; {off} of {checked} results off the ladder H(2)'
        print(line)
        print(f'     the {ndense} with dense random parts: largest error / (u^8 |Z|) {dec_up(worst_dense, 4)}')
        ok &= mism == 0 and worst <= 1 and off == 0 and len(runs) > 0.9 * N
        # control: a broken emulator must mismatch
        drop, mutate, what = CONTROL[op]
        sub = runs[: min(300, len(runs))]
        bad = 0
        for (a, b, _, _), g in zip(sub, got):
            y = emu(op, a, b, drop, mutate)
            bad += y is None or hexline(y) != g
        print(f'     control ({what}): {bad} of {len(sub)} mismatch')
        ok &= bad > 0
    # Proposition 24's inputs at n = 8, through multidouble
    E.set_p(53)
    same = []
    for op, a, b, _, s in sharp_inputs(8):
        got = crate(CRATE_MODE[op], [hexline(a + (b if isinstance(b, list) else [b]))])[0]
        want = hexline([(s, -53 * k) for k in range(8)])
        same.append(got == want and hexline(OPS[op](a, b)) == want)
    print(f'multidouble returns +-(1, u, ..., u^7) on the {len(same)} inputs of Proposition 24 at n = 8: {all(same)}')
    return ok and all(same)


# ---------------------------------------------------------------------------------------------------------------
# small: exhaustive runs at small precision
# ---------------------------------------------------------------------------------------------------------------

def family9(p, exps, mants=None):
    """zero and every float of precision p with leading exponent in exps and mantissa in mants (all by default),
    both signs"""
    out = [E.PZ]
    for k in exps:
        for m in mants or range(2 ** (p - 1), 2 ** p):
            for s in (1, -1):
                out.append(E.rnd(s * m, k - (p - 1)))
    return out


def theorem9(p, n, exps, N=None, mants=None):
    """Theorem 9 on every N-tuple of the family (N = n + 1 by default), in every order, the first term not negative
    (RN is odd, so a tuple and its negation behave alike). Returns the counts."""
    E.set_p(p)
    N = n + 1 if N is None else N
    fam = family9(p, exps, mants)
    vals = {x: val(x) for x in fam}
    us = Fr(1, 2 ** p + 1)
    first = [x for x in fam if x[0] >= 0]
    count = lossy = attained = viol = half = fastbad = not_emit = 0
    for c0 in first:
        for rest in product(fam, repeat=N - 1):
            c = (c0,) + rest
            v = E.vecsum(c)
            x, k = E.second_pass(v, n, 'two')
            S = sum(vals[t] for t in c)
            count += 1
            err = S - total(x)
            if total(v) != S:
                viol += 1
            if err:
                lossy += 1
                if N <= n or k != n - 1:
                    not_emit += 1
                av = [abs(val(t)) for t in v]
                B = min(us ** (n - j) * av[j] + sum(us ** (n + 1 - i) * av[i] for i in range(j + 1, n + 1))
                        for j in range(n + 1))
                e = abs(err)
                if e > B:
                    viol += 1
                elif e == B:
                    attained += 1
                if 2 * e > B:
                    half += 1
            xf, _ = E.second_pass(v, n, 'fast')
            if N == n + 1:
                ef = abs(S - total(xf))
                if ef and (not err or ef > abs(err)):
                    fastbad += 1
            elif total(xf) != S:
                fastbad += 1
    return dict(count=count, lossy=lossy, attained=attained, viol=viol, half=half, fastbad=fastbad,
                not_emit=not_emit, size=len(fam))


def family15(p, n, choices):
    """operands on H(2) with a_0 every mantissa at exponent 0 and each later part one of: zero, the ladder's edge
    T = (2u)^i a_0 ('T'), the largest float below u^i ('D'), a power of two far below the edge ('G'), with signs"""
    out = []
    for m0 in range(2 ** (p - 1), 2 ** p):
        opts = []
        for i in range(1, n):
            o = [E.PZ]
            for s in (1, -1):
                if 'T' in choices:
                    o.append(E.rnd(s * m0, -(p - 1) - (p - 1) * i))
                if 'D' in choices:
                    o.append(E.rnd(s * (2 ** p - 1), -p * i - p))
                if 'G' in choices:
                    o.append(E.rnd(s, -(p - 1) * i - p - 3))
            opts.append(o)
        for tail in product(*opts):
            out.append([E.rnd(m0, -(p - 1))] + list(tail))
    return out


def run_ops(p, n, fam_a, pairs_b, scalars, div_b, mutate=None, limit=None):
    """each operation on the pairs (DIV on the divisors div_b); returns per operation (count, largest error /
    bound, violations)"""
    E.set_p(p)
    E.MUTATE = mutate
    res = {}
    try:
        for op in ('add', 'addf', 'mulf', 'mul', 'div'):
            kappa = kappa_of(op, n, p)
            count = viol = 0
            worst = Fr(0)
            bs = scalars if op in ('addf', 'mulf') else div_b if op == 'div' else pairs_b
            for a in fam_a:
                for b in bs:
                    if op == 'add' or op == 'div':
                        variants = (b, [E.neg(t) for t in b])
                    else:
                        variants = (b,)
                    for bb in variants:
                        x = OPS[op](a, bb)
                        Z, bd = bound(op, a, bb, n, p, kappa)
                        r = abs(Z - total(x)) / bd
                        count += 1
                        if r > 1:
                            viol += 1
                        if r > worst:
                            worst = r
                if limit and count >= limit:
                    break
            res[op] = (count, worst, viol)
    finally:
        E.MUTATE = None
    return res


def small():
    ok = True
    print('small: Theorem 9 at p = 3, every tuple of the family in every order, first term not negative')
    for n, exps, N, mants in ((2, range(-8, 2), 3, None), (3, range(-9, 1), 3, None), (3, range(-9, 1), 4, (4, 5, 7))):
        r = theorem9(3, n, exps, N, mants)
        what = (f'n = {n}, {N} terms from {r["size"]} values (leading exponents {exps[0]} to {exps[-1]}, '
                f'{"mantissas 1, 5/4 and 7/4" if mants else "every mantissa"})')
        if N <= n:
            print(f'  {what}: {r["count"]} tuples, {r["lossy"]} lossy (Theorem 9(a): none); control, Fast2Sum '
                  f'throughout: {r["fastbad"]} lossy')
            ok &= r['lossy'] == 0 and r['viol'] == 0 and r['fastbad'] > 0
        else:
            print(f'  {what}: {r["count"]} tuples, {r["lossy"]} lossy, {r["viol"]} beyond min_k B_k, '
                  f'{r["not_emit"]} lossy without n - 1 emissions, {r["attained"]} with |E| = min_k B_k; controls: '
                  f'{r["half"]} beyond half the bound, {r["fastbad"]} where Fast2Sum throughout loses more')
            # at n = 2 the two second passes agree: the only step after an emission is the last
            ok &= r['viol'] == 0 and r['not_emit'] == 0 and r['attained'] > 0 and r['half'] > 0
            ok &= r['fastbad'] > 0 or n == 2
    print('small: Theorems 15 and 19, operands on H(2): a_0 every mantissa, each later part zero, the ladder\'s '
          'edge, the largest float below u^i or a power of two far below, with both signs')
    for p, n, choices, bchoices in ((5, 3, 'TDG', 'TD'), (7, 4, 'TD', 'T')):
        fam = family15(p, n, choices)
        famb = family15(p, n, bchoices)
        rng = random.Random(p * 100 + n)
        full = len(fam)
        if n == 4:
            fam = rng.sample(fam, 2000)
            famb = rng.sample(famb, 24)
        scal = [E.rnd(s * m, k - (p - 1)) for m in range(2 ** (p - 1), 2 ** p) for k in (-p - 1, -1, 0, 3)
                for s in (1, -1)]
        if n == 4:
            scal = rng.sample(scal, 48)
        divb = rng.sample(famb, 16 if n == 3 else 4)
        res = run_ops(p, n, fam, famb, scal, divb)
        print(f'  p = {p}, n = {n}: {len(fam)} operands a (of the family\'s {full}), {len(famb)} operands b (and their negations for ADD), '
              f'{len(divb)} of them as divisors (and their negations), {len(scal)} floats f')
        for op, (count, worst, viol) in res.items():
            print(f'    {op.upper():4s} {count} pairs, {viol} beyond the bound, largest error / bound '
                  f'{dec_up(worst, 4)}')
            ok &= viol == 0
        ctl = run_ops(p, n, fam, famb, scal, divb, mutate='two_sum_sign', limit=5000)
        print('    control (two-sum\'s error with the wrong sign), pairs beyond the bound: '
              + ', '.join(f'{op.upper()} {v} of {c}' for op, (c, _, v) in ctl.items()))
        ok &= all(v > 0 for _, _, v in ctl.values())
    return ok


# ---------------------------------------------------------------------------------------------------------------
# sharp: Proposition 24
# ---------------------------------------------------------------------------------------------------------------

def sharp_inputs(n, p=53):
    """Proposition 24's inputs: (operation, a, b, the error it states, the sign of the result)"""
    u = Fr(1, 2 ** p)
    one, z = (1, 0), E.PZ

    def pw(k):
        return (1, -p * k)

    rows = []
    if n >= 3:
        a = [pw(k) for k in range(n - 1)] + [z]
        b = [one] + [z] * (n - 2) + [pw(n - 1)]
        rows.append(('mul', a, b, sum(u ** k for k in range(n, 2 * n - 2)), 1))
    a = [pw(k) for k in range(n)]
    rows.append(('add', a, [pw(n)] + [z] * (n - 1), u ** n, 1))
    rows.append(('addf', a, pw(n), u ** n, 1))
    # (c): 2^53 + 1 = 3 g, a_0 = 3/2, f = (1 + u) / a_0
    g, rem = divmod(2 ** p + 1, 3)
    assert rem == 0
    f = E.rnd(g, 1 - p)
    assert val(f) * Fr(3, 2) == 1 + u
    am = [E.rnd(3, -1 - p * i) if i % 2 == 0 else z for i in range(n)]
    if n % 2 == 0:
        am[n - 1] = E.rnd(3, -1 - p * n)
    rows.append(('mulf', am, f, u ** n if n % 2 else u ** n + u ** (n + 1), 1))
    rows.append(('div', [one] + [z] * (n - 1), [(-1, 0), pw(1)] + [z] * (n - 2), u ** n / (1 - u), -1))
    return rows


def sharp():
    ok = True
    p = 53
    E.set_p(p)
    u = Fr(1, 2 ** p)
    z = E.PZ

    def pw(k):
        return (1, -p * k)

    print('sharp: Proposition 24 at p = 53; error / (u^n |Z|) is 1 - O(u) in every case')
    for n in range(2, 9):
        want = [u ** k for k in range(n)]
        rows = sharp_inputs(n)
        line = []
        for op, a, b, err_want, s in rows:
            x = OPS[op](a, b)
            kappa = kappa_of(op, n, p)
            Z, bd = bound(op, a, b, n, p, kappa)
            err = abs(Z - total(x))
            good = err == err_want and [s * val(t) for t in x] == want and err <= bd
            fires = 2 * err > bd
            ok &= good and fires
            line.append(f'{op.upper()} {"ok" if good else "DIFFERS"}, 1 - error / (u^n |Z|) = '
                        f'{float(1 - err / (u ** n * abs(Z))):.2e}, half the bound {"fires" if fires else "holds"}')
        print(f'  n = {n}: ' + '; '.join(line))
    # control: with ties away from zero the chain of ties breaks
    E.MUTATE = 'ties_away'
    try:
        x = E.od_add([pw(k) for k in range(8)], [pw(8)] + [z] * 7)
    finally:
        E.MUTATE = None
    changed = [val(t) for t in x] != [u ** k for k in range(8)]
    print(f'  control (ties away from zero): the result of the ADD input at n = 8 changes: {changed}')
    return ok and changed


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else 'all'
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 10000
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    ok = True
    if mode in ('sharp', 'all'):
        ok &= sharp()
    if mode in ('small', 'all'):
        ok &= small()
    if mode in ('bits', 'all'):
        ok &= bits(N, seed)
    print('PASS' if ok else 'FAIL')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
