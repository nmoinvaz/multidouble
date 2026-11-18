"""Bitwise comparison of the referee's model (reffp.Acc, n = 8, p = 53) with multidouble's OdAcc (rs/, the crate in
this worktree). Values are compared (signed zeros ignored), level by level and part by part.

python3 crosscheck.py [samples] [seed]              the comparison
python3 crosscheck.py [samples] [seed] control      controls: the model with deposit order reversed, the model's
                                                    finish without its last ADDF, and the crate with ACC_L3; each
                                                    must give mismatches
"""
import random
import subprocess
import sys

import reffp as F
from gen import operand

HERE = __import__('os').path.dirname(__file__) or '.'
BIN = f'{HERE}/rs/target/release/acc_referee'
BIN_MUT = f'{HERE}/rs/target/mut/release/acc_referee'


def hx(a):
    return ' '.join(F.to_f64_hex(x) for x in a)


def make_case(rng, K):
    terms = []
    for _ in range(K):
        e0 = rng.randrange(-40, 40) if rng.random() < 0.3 else rng.randrange(-3, 3)
        th = rng.choice((1, 2))
        if rng.random() < 0.7:
            terms.append(('P', operand(rng, 8, th, e0), operand(rng, 8, th, rng.randrange(-3, 3))))
        else:
            terms.append(('X', operand(rng, 8, th, e0)))
    return terms


def model_run(terms, order='normal'):
    acc = F.Acc(8)
    for t in terms:
        if t[0] == 'P':
            lev = F.mul_levels(t[1], t[2])
        else:
            lev = t[1]
        if order == 'reversed':
            for l in reversed(range(8)):
                F.dep(acc.s, l, lev[l])
            if len(lev) == 9:
                acc.s[8] = F.add(acc.s[8], lev[8])
        else:
            acc.deposit(lev)
    return acc.s, acc.finish()


def rust_run(cases, binary=BIN, args=()):
    lines = []
    for terms in cases:
        lines.append('Z')
        for t in terms:
            lines.append(f'P {hx(t[1])} {hx(t[2])}' if t[0] == 'P' else f'X {hx(t[1])}')
        lines.append('F')
    r = subprocess.run([binary, *args], input='\n'.join(lines) + '\n', capture_output=True, text=True, check=True)
    out = r.stdout.split('\n')
    res = []
    for i in range(0, 2 * len(cases), 2):
        L = [F.from_f64_hex(h) for h in out[i].split()[1:]]
        R = [F.from_f64_hex(h) for h in out[i + 1].split()[1:]]
        res.append((L, R))
    return res


def main():
    ns = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    control = len(sys.argv) > 3 and sys.argv[3] == 'control'
    rng = random.Random(seed)
    F.setp(53)
    cases = [make_case(rng, rng.choice((1, 2, 3, 5, 8, 16, 33, 64))) for _ in range(ns)]
    nterm = sum(len(c) for c in cases)
    rs = rust_run(cases)
    variants = [('model', 'normal', rs)]
    if control:
        variants = [('model, deposits in reversed order', 'reversed', rs),
                    ('model, finish without its last ADDF', 'skiplast', rs),
                    ('crate with ACC_L3 (mutation 8)', 'normal', rust_run(cases, BIN_MUT, ('8',)))]
    for name, order, rres in variants:
        lev_mis = res_mis = 0
        for terms, (L, R) in zip(cases, rres):
            if order == 'skiplast':
                F.MUT.add('finish_skip_last')
            s, x = model_run(terms, 'normal' if order == 'skiplast' else order)
            F.MUT.discard('finish_skip_last')
            lev_mis += s != L
            res_mis += x != R
        print(f'{name}: {ns} cases, {nterm} terms; level mismatches {lev_mis}, finish mismatches {res_mis}')
        if not control and (lev_mis or res_mis):
            sys.exit(1)
        if control and lev_mis + res_mis == 0:
            print('CONTROL DID NOT FIRE')
            sys.exit(1)


if __name__ == '__main__':
    main()
