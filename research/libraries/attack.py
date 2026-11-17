"""Search for inputs on which a shipped expansion algorithm exceeds its documented error bound.

Inputs are valid by construction: each operand is the greedy round-to-nearest expansion of an exact dyadic value,
so |x_{i+1}| <= ulp(x_i)/2 with zeros only at the tail (QD's normal form, and CAMPARY's ulp-nonoverlapping form).
The value is a random sum of doubles at random scales, which gives gaps, and the second operand can be the
negated first plus a small perturbation, which gives cancellation.

usage: attack.py OP TRIALS SEED [P] [SECONDS] [OUT.jsonl]
"""
import json
import random
import sys
import time
from fractions import Fraction

import ports as X
from ports import F, val, vsum

OPS = {}


def op(name, n, bound_kind, k_bound, kind):
    def deco(fn):
        OPS[name] = dict(fn=fn, n=n, bound=bound_kind, k=k_bound, kind=kind)
        return fn
    return deco


# documented bounds, as functions of p (u = 2^-p)
#  'cray': |err| <= k u^n max(|a|,|b|)   (HLB 2001 Lemma 12 and the sentence after it: eps_qd = 2^-211 = 2u^4)
#  'rel':  |err| <= k u^n |Z|            (HLB 2001 Sec. 3.2 and 3.4 for QD; CAMPARY source comments)
#  'camp': |err| <= k 2^{-(p-1)R} |Z|    (CAMPARY addition.h:45 and :91)

@op('qd_sloppy_add', 4, 'cray', 2, 'add')
def _(a, b):
    return X.qd_sloppy_add(a, b)


@op('qd_ieee_add', 4, 'rel', 4, 'add')  # "|delta| <= 2 eps_qd or so", 2 eps_qd = 4u^4
def _(a, b):
    return X.qd_ieee_add(a, b)


@op('qd_ieee_add_fixed', 4, 'rel', 4, 'add')  # BL-highprecision/QD 92d99c8, the k == 3 fix
def _(a, b):
    return X.qd_ieee_add_fixed(a, b)


@op('qd_ieee_add_fix2', 4, 'rel', 4, 'add')  # our candidate repair, ports.qd_ieee_add_fix2
def _(a, b):
    return X.qd_ieee_add_fix2(a, b)


@op('l3_bf_add', 4, 'rel', 2, 'add')  # libQD3 QD_BF addition; eps_qd |Z| for reference (no bound stated)
def _(a, b):
    return X.l3_bf_add(a, b)


@op('l3_bf_add_M', 4, 'cray', 2, 'add')  # the same, against QD's Cray-style addition bound
def _(a, b):
    return X.l3_bf_add(a, b)


@op('l3_bf_mul', 4, 'rel', 2, 'mul')  # libQD3 QD_BF multiplication; eps_qd |Z| for reference
def _(a, b):
    return X.l3_bf_mul(a, b)


@op('td_ieee_add', 3, 'rel', 4, 'add')  # td_real::ieee_add against td_real::_eps = 2^-157 = 4u^3, relative
def _(a, b):
    return X.td_ieee_add(a, b)


@op('qd_accurate_mul', 4, 'rel', 2, 'mul')
def _(a, b):
    return X.qd_accurate_mul(a, b)


@op('qd_sloppy_mul', 4, 'rel', 2, 'mul')  # no stated bound ("slightly inaccurate"); eps_qd for reference
def _(a, b):
    return X.qd_sloppy_mul(a, b)


@op('qd_mul_d', 4, 'rel', 2, 'muld')
def _(a, b):
    return X.qd_mul_d(a, b[0])


@op('qd_add_d', 4, 'cray', 2, 'addd')
def _(a, b):
    return X.qd_add_d(a, b[0])


@op('qd_sloppy_div', 4, 'rel', 2, 'div')  # no stated bound; eps_qd for reference
def _(a, b):
    return X.qd_sloppy_div(a, b)


@op('qd_accurate_div', 4, 'rel', 2, 'div')
def _(a, b):
    return X.qd_accurate_div(a, b)


@op('cp_certified_add', 4, 'camp', 4.5, 'add')
def _(a, b):
    return X.cp_certified_add(a, b, 4)


@op('cp_bailey_add_renorm', 4, 'camp', 24, 'add')
def _(a, b):
    return X.cp_bailey_add_renorm(a, b, 4)


@op('cp_bailey_add_renorm_M', 4, 'campM', 24, 'add')  # the same bound read as relative to max(|x|, |y|)
def _(a, b):
    return X.cp_bailey_add_renorm(a, b, 4)


@op('cp_bailey_mul_renorm', 4, 'campmul', 1, 'mul')  # multiplication.h:396, K = L = R = 4
def _(a, b):
    return X.cp_bailey_mul_renorm(a, b, 4)


@op('gqd_add', 4, 'cray', 2, 'add')  # GQD documents QD's bounds by inheritance (a port of QD)
def _(a, b):
    return X.gqd_add(a, b)


@op('gqd_add_d', 4, 'cray', 2, 'addd')
def _(a, b):
    return X.gqd_add_d(a, b[0])


@op('gqd_mul_d', 4, 'rel', 2, 'muld')
def _(a, b):
    return X.gqd_mul_d(a, b[0])


@op('gqd_mul', 4, 'rel', 2, 'mul')
def _(a, b):
    return X.gqd_mul(a, b)


@op('cp_certified_add_d', 4, 'camp', 4.5, 'addd')
def _(a, b):
    return X.cp_certified_add(a, [b[0]], 4)


def exact(kind, a, b):
    A, B = vsum(a), vsum(b)
    if kind == 'add':
        return A + B
    if kind == 'addd':
        return A + val(b[0])
    if kind == 'mul':
        return A * B
    if kind == 'muld':
        return A * val(b[0])
    if kind == 'div':
        return A / B
    raise ValueError(kind)


def bound(spec, a, b, Zx, p):
    u = Fraction(1, 2 ** p)
    n = spec['n']
    k = Fraction(spec['k']).limit_denominator(100)
    if spec['bound'] == 'cray':
        bb = [b[0]] if spec['kind'] == 'addd' else b
        return k * u ** n * max(abs(vsum(a)), abs(vsum(bb)))
    if spec['bound'] == 'rel':
        return k * u ** n * abs(Zx)
    if spec['bound'] == 'camp':
        return k * Fraction(1, 2 ** ((p - 1) * n)) * abs(Zx)
    if spec['bound'] == 'campmul':
        # 2^{-(p-1)(R+1)} (128/127 (K+L) - 129/254 R - 385/254 + 2^{p-1} + 2^{-p-r}(R^2+R)((R+1)!)^2), r = 0
        R = K_ = L_ = n
        c = (Fraction(128, 127) * (K_ + L_) - Fraction(129, 254) * R - Fraction(385, 254) + 2 ** (p - 1)
             + Fraction(1, 2 ** p) * (R * R + R) * 14400)
        return Fraction(1, 2 ** ((p - 1) * (R + 1))) * c * abs(Zx)
    if spec['bound'] == 'campM':
        return k * Fraction(1, 2 ** ((p - 1) * n)) * max(abs(vsum(a)), abs(vsum(b)))
    raise ValueError(spec['bound'])


def rnd_frac(x):
    """RN-even of a nonzero dyadic Fraction to P bits, as an fpemu tuple"""
    num, den = x.numerator, x.denominator
    e = -(den.bit_length() - 1)
    assert den == 1 << -e, "dyadic only"
    return F.rnd(num, e)


def expand(Xv, n):
    out = []
    r = Xv
    for _ in range(n):
        if r == 0:
            out.append(F.PZ)
            continue
        t = rnd_frac(r)
        out.append(t)
        r -= val(t)
    return out


def rand_double(rng, p, scale):
    m = rng.getrandbits(p) | (1 << (p - 1))
    k = rng.choice([p, p, p, rng.randint(1, p)])  # sometimes short mantissas (sparse bit patterns)
    m >>= (p - k)
    s = -1 if rng.random() < 0.5 else 1
    return Fraction(s * m) * Fraction(2) ** (scale - k + 1)


def rand_value(rng, p, n):
    """a sum of up to n + 2 doubles at decreasing random scales, so that gaps and dense runs both occur"""
    v = Fraction(0)
    scale = 0
    for i in range(rng.randint(1, n + 2)):
        v += rand_double(rng, p, scale)
        scale -= rng.choice([p, p, p + 1, p - 1, p - 2, p + rng.randint(0, 3 * p), rng.randint(1, 2 * p)])
    return v


def rand_pair(rng, p, n, kind):
    A = rand_value(rng, p, n)
    while A == 0:
        A = rand_value(rng, p, n)
    r = rng.random()
    if kind in ('add', 'addd') and r < 0.6:
        # cancellation: B = -A + D with D at a random depth below A
        depth = rng.randint(0, (n + 1) * p)
        D = rand_value(rng, p, n) * Fraction(2) ** (-depth) * abs(A)
        D = Fraction(round(D * 2 ** (n * p + 4 * p + depth))) / 2 ** (n * p + 4 * p + depth)  # keep it dyadic
        B = -A + D
        if rng.random() < 0.5:
            B = -B  # also test a - b form via a + (-b) with the sign flipped later
            B = -B
    elif kind in ('mul', 'muld', 'div') and r < 0.3:
        B = A  # squares and self-quotients stress symmetric levels
        if rng.random() < 0.5:
            B = rand_value(rng, p, n)
    else:
        B = rand_value(rng, p, n)
    if B == 0:
        B = Fraction(1)
    a = expand(A, n)
    nb = 1 if kind in ('addd', 'muld') else n
    b = expand(B, nb) + [F.PZ] * (n - nb)
    return a, b


def nonoverlap_violation(x):
    """index i where |x_{i+1}| > ulp(x_i) (CAMPARY's ulp-nonoverlapping), or interior zero followed by nonzero"""
    for i in range(len(x) - 1):
        if x[i][0] == 0:
            if any(y[0] != 0 for y in x[i + 1:]):
                return i
            return None
        if x[i + 1][0] == 0:
            continue
        m, e = x[i]
        ulp = Fraction(2) ** (abs(m).bit_length() - 1 + e - F.P + 1)
        if abs(val(x[i + 1])) > ulp:
            return i
    return None


def run_case(spec, a, b, p):
    Zx = exact(spec['kind'], a, b)
    out = spec['fn'](a, b)
    err = abs(Zx - vsum(out))
    bd = bound(spec, a, b, Zx, p)
    ratio = err / bd if bd else (Fraction(0) if err == 0 else Fraction(10 ** 9))
    return ratio, out, err, Zx


def hexs(x):
    """C99 hex-float literal of a p = 53 value"""
    import struct
    return float.hex(struct.unpack('<d', F.to_bits(x).to_bytes(8, 'little'))[0])


def main():
    name = sys.argv[1]
    trials = int(sys.argv[2])
    seed = int(sys.argv[3])
    p = int(sys.argv[4]) if len(sys.argv) > 4 else 53
    secs = float(sys.argv[5]) if len(sys.argv) > 5 else 600
    outp = sys.argv[6] if len(sys.argv) > 6 else None
    F.set_p(p)
    spec = OPS[name]
    rng = random.Random(seed)
    t0 = time.time()
    worst = Fraction(0)
    hits = 0
    nov = 0
    rows = []
    done = 0
    for t in range(trials):
        if time.time() - t0 > secs:
            break
        a, b = rand_pair(rng, p, spec['n'], spec['kind'])
        try:
            ratio, out, err, Zx = run_case(spec, a, b, p)
        except ZeroDivisionError:
            continue
        done += 1
        bad_inv = nonoverlap_violation(out)
        if bad_inv is not None:
            nov += 1
        if ratio > 1:
            hits += 1
        if ratio > worst or (ratio > 1 and len(rows) < 50):
            worst = max(worst, ratio)
            rows.append(dict(op=name, p=p, seed=seed, trial=t, ratio=float(ratio), log2_ratio=_l2(ratio),
                             a=[list(x) for x in a], b=[list(x) for x in b], out=[list(x) for x in out],
                             nonoverlap_violation=bad_inv))
    print(f"{name} p={p} seed={seed} trials={done} worst_ratio={float(worst):.4g} (log2 {_l2(worst):.2f}) "
          f"over_bound={hits} nonoverlap_violations={nov} time={time.time() - t0:.1f}s")
    if outp:
        with open(outp, 'a') as f:
            for r in rows[-20:]:
                f.write(json.dumps(r) + '\n')


def _l2(r):
    if r == 0:
        return float('-inf')
    return (r.numerator.bit_length() - r.denominator.bit_length())


if __name__ == '__main__':
    main()
