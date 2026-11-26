#!/usr/bin/env python3
"""The Lean modules of Theorem 42's constant at n = 8, paper/lean/ExpansionBounds/Log8/Data.lean and Run*.lean, and
the numbers they certify, on the definitions of LogEval.lean and Log8/Defs.lean in exact rational arithmetic: the
convex variant of the bound of a case (VecSum's second bound alone, b' and pi' without their minima, t-bar_j = 2^j b'
for r <= 0), evaluated at the two ends of the case's interval of l = |ln x|, each value rounded up to 200 bits as the
kernel rounds it. One state (p_q, b_T) of Horner's rule and step (3) serves the cases of a group (m, d), for k = 0
and k != 0, both ends and both signs, wherever the bound stays under 9.926 u^8 l (+ 2^-509 from l = 0); step (5)'s
series, c (x) h and ADDF(c (x) h, 1) run once, on a state above every case's. Every domination that the Lean proof
takes as a hypothesis is asserted here.
Usage: log_lean.py [dir]          print the layout and its largest values; with a directory, write Log8/Data.lean
                                   and the first module
       log_lean.py dir all        write every module"""
import sys, os
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import trig_lean as TL  # noqa: E402
import exp_lean as XL  # noqa: E402
import explog_consts as XC  # noqa: E402

N, U, up, pair, wrap = TL.N, TL.U, TL.up, TL.pair, TL.wrap
US = U / (1 + U)
ETA0, B, Q, S, DEG = XL.ETA0, XL.B, 4, XL.S, XL.DEG
BOUND, FLOOR = Fr(9926, 1000), Fr(1, 2 ** 509)
STEP = 2
DROP = False                         # the control: no error of the last ADD


def down(q):
    return -up(-q) if q else q


# -- the mirrors of LogEval.lean
def Vc(Xl, j):
    return US * (1 + U) ** (N - j) * sum(Xl[j - 1:N + 1])


def g_parts_c(Xl, Zb, Fb):
    V = [None] + [Vc(Xl, j) for j in range(1, N + 1)]
    out = [(1 + U) * (Zb + Fb + sum(V[2:N + 1]))]
    for i in range(N - 1):
        out.append((1 + U) * (U * out[i] + sum(V[i + 2:N + 1])))
    return out


def g_err_c(Xl, Zb, Fb):
    return U ** N * Zb + (1 + U ** N) * Fb + sum((U ** N + U ** (N + 1 - j)) * Vc(Xl, j) for j in range(1, N + 1))


def g_mul_c(a, b, Zb):
    Xl, F = TL.mul_x(a, b)
    return g_err_c(Xl, Zb, F), g_parts_c(Xl, Zb, F)


def g_add_c(a, b, Zb):
    Xl, F = TL.pair_x([x + y for x, y in zip(a, b)])
    return g_err_c(Xl, Zb, F), g_parts_c(Xl, Zb, F)


def g_addf_c(al, lam0, Zb):
    Xl = TL.addf_x(al, lam0)
    return g_err_c(Xl, Zb, 0), g_parts_c(Xl, Zb, 0)


def horner_step_c(pz, zb, eta, Fk, phik, vk, vk1, st):
    """hornerStepLC with eps_z = 0"""
    e1, p1 = st
    Zm = zb * (vk1 + e1)
    em, mu = g_mul_c(pz, p1, Zm)
    D = zb * e1 + phik + (em + N * eta)
    ea, pa = g_add_c([abs(x) for x in Fk], [x + eta for x in mu], vk + D)
    return up(D + ea), [up(x) for x in pa]


def exp_w(pq, bp, st):
    Zw = bp * (XL.core_v(bp, 2) + st[0])
    e1, w1 = g_mul_c(pq, st[1], Zw)
    return ((up(Zw + e1), up(e1 + bp * st[0])), [up(x) for x in w1])


def exp_y(pq, bp, D, d, st):
    e2, w = g_mul_c(pq, st[1], bp * st[0][0])
    return (up(e2 + bp * st[0][1] + XL.etr(bp, d) + D), [up(x) for x in w])


def exp_t(pq, T0, eta, st):
    e3, pa = g_add_c(pq, st[1], T0 + st[0])
    return (up(st[0] + e3 + N * eta), [up(x + eta) for x in pa])


def exp_sq(T, T2, g, st):
    E, ps = st
    em, nu = g_mul_c(ps, ps, (T + E) ** 2)
    ea, pa = g_add_c([2 * x for x in ps], nu, T2 + 2 * E * (1 + T) + E ** 2 + em)
    return (up(2 * g * E + E ** 2 + em + ea), [up(x) for x in pa])


def core_tc(pos, bp, j):
    return up(XL.exp_up(2 ** j * bp) - 1) if pos else up(2 ** j * bp)


def log_v(C, q, i):
    return sum(C ** l / (i + l) for l in range(q + 1 - i))


def c4a(D, eta, pphi, phib, tb, xs, st):
    e, parts = g_mul_c(pphi, st[1], phib * (tb + st[0]))
    es, ps = g_add_c(pphi, st[1], xs + st[0] + D)
    return ((up(e + N * eta + Fr(1, 2 ** (B + 12)) * max(phib, tb + st[0])), up(es)),
            ([up(x + eta) for x in parts], [up(x) for x in ps]))


def c4b(D, pphi, tb, cs, xd, xi, st0, sa):
    base = xi * st0[0] + (xd + D * (1 + tb + st0[0])) + sa[0][0] + sa[0][1]
    ec, pc = g_add_c(sa[1][1], sa[1][0], cs + base)
    _, p2 = g_add_c(pphi, st0[1], cs + (base + ec))
    return (up(base + ec), [up(max(x, y)) for x, y in zip(pc, p2)])


def log_h(eta, chi, C, q, st):
    Zh = C * (log_v(C, q, 2) + st[0])
    e, parts = g_mul_c(chi, st[1], Zh)
    return ((up(Zh + (e + N * eta)), up(e + N * eta)), [up(x + eta) for x in parts])


def log_g(st):
    lam = 1 + st[0][0] + sum(st[1][1:N])
    e, parts = g_addf_c(st[1], lam, 1 + st[0][0])
    return (up(e), [up(x) for x in parts])


def log_p(eta, chi, C, Ec, e2, hb, eh, q, st):
    e, parts = g_mul_c(chi, st[1], C * (1 + hb + st[0]))
    P = e + N * eta + C * (st[0] + eh + C * e2) + max(C ** (q + 1) / (q + 1), Fr(1, 2 ** (B + 13)) * C) / (1 - C) \
        + Ec / (1 - C)
    return (up(P), [up(max(x + eta, c)) for x, c in zip(parts, chi)])


def log_end(py, l, st):
    return (Fr(0) if DROP else g_add_c(py, st[1], l + st[0])[0]) + st[0]


# -- the constants of Log8/Defs.lean
CONST = XL.CONST
CL = [Fr(x) for x in CONST['dd']]
SER = [[], []] + [[Fr(x) for x in XL.EC.greedy(Fr((-1) ** (i + 1), i), N)] for i in range(2, Q + 1)]
SPHI = [None, None] + [abs(sum(SER[i]) - Fr((-1) ** (i + 1), i)) for i in range(2, Q + 1)]
EA = 3 * U ** 2 / (1 - 4 * U)
EPSDW = Fr(15351, 1000) * U ** 2
_w = 6 * U / (1 - 6 * U) * (2 * U) / (1 - 2 * (2 * U) - 6 * U / (1 - 6 * U) * (2 * U))
D0 = _w / (1 - _w)
ETAL = max(abs(XL.LN2A - sum(CL)), abs(XL.LN2B - sum(CL)))
E1 = EPSDW + EA
E0 = EPSDW * D0 + D0 + Fr(1, 2 ** 1071) + EA + ETAL + Fr(1, 2 ** 2000)
D4 = N * (2 * ETA0)


def eta1(m):
    return ETA0 if m else Fr(0)


def args(l):
    Eq = up(E0 + E1 * l)
    y0 = (l + Eq) * (1 - U) / (1 - 2 * U)
    return Eq, [y0, U * y0] + [Fr(0)] * (N - 2)


def red_s(l):
    """(log8RMax l, log8Alpha l, log8DeltaS l)"""
    Eq, py = args(l)
    xt = 2 * U * (l + Eq)
    rmax = (Fr(1, 2) + (l + Eq) / (1 - U) * (XL.RED_DL + U * XL.CR)) * XL.LN2B + xt
    al = [rmax + xt + 1075 * max(abs(XL.CH - XL.LN2A), abs(XL.CH - XL.LN2B))] + py[1:]
    keta = 1075 * XL.RED_ETA
    return rmax, al, up(XL.RED_E1 + g_add_c(al, XL.RED_MU, rmax + keta + XL.RED_E1)[0] + keta)


def red(l, b):
    """(log8Delta l b, log8PiR l b)"""
    rmax, al, ds = red_s(l)
    keta = 1075 * XL.RED_ETA
    e2, pr = g_add_c(al, XL.RED_MU, b + ds + keta + XL.RED_E1)
    return up(XL.RED_E1 + e2 + keta), [up(x) for x in pr]


def bp_of(m, b):
    return b / 2 ** m + N * eta1(m)


# -- a head: Horner's run and step (3) on a state (pq, bp)
HEADS = {}


def head(pq, bp, d, m):
    key = (tuple(pq), bp, d, m > 0)
    if key not in HEADS:
        h = dict(pq=list(pq), bp=bp, d=d, m=m, id=len(HEADS))
        if d == 1:
            t = (XL.etr(bp, 1) + 2 * N * eta1(m), list(pq))          # exact: the state of core0C_cert_one is rounded
            h['t'] = {True: (up(t[0]), t[1]), False: (up(t[0]), t[1])}
        else:
            st = (XL.PHI[d], [abs(x) for x in XL.FK[d]])
            hs = [st]
            for j in range(1, d - 1):
                k = d - j
                st = horner_step_c(pq, bp, Fr(0), XL.FK[k], XL.PHI[k], XL.core_v(bp, k), XL.core_v(bp, k + 1), st)
                hs.append(st)
            h['hs'] = hs
            h['w'] = exp_w(pq, bp, st)
            h['y'] = exp_y(pq, bp, 2 * N * eta1(m), d, h['w'])
            h['t'] = {s: exp_t(pq, core_tc(s, bp, 0), ETA0, h['y']) for s in (True, False)}
        HEADS[key] = h
    return HEADS[key]


def evaluate(k0, pos, m, a, b, l, dl, pr, h, shared=None):
    """the checks of a case at an end l, on the head h; shared = (chiM, CM, sH, hh, gg)"""
    Eq, py = args(l)
    bpB = bp_of(m, b)
    assert bpB <= h['bp'] and all(x / 2 ** m + eta1(m) <= y for x, y in zip(pr, h['pq'])), 'head state below the case'
    assert 0 <= a <= 1 and 0 <= b and h['bp'] < 1 and 2 ** m * h['bp'] <= 1
    assert max(abs(Eq + dl - a), abs(Eq + b + dl)) <= 1
    ap = a / 2 ** m
    st = h['t'][pos]
    sq = [st]
    for j in range(m):
        st = exp_sq(core_tc(pos, bpB, j), core_tc(pos, bpB, j + 1), XL.core_g(pos, ap, bpB, j), st)
        sq.append(st)
    xi = up((XL.exp_up(Eq + dl - a) if pos else XL.exp_up(Eq + b + dl)) + D4)
    phib = max(xi - 1, Eq + b + dl + D4)
    pxq = [(2 * U) ** i * (xi * (1 - 2 * U) / (1 - 4 * U)) + 2 * ETA0 for i in range(N)]
    pphi = [up(x) for x in g_addf_c(pxq, phib + sum(pxq[1:]), phib)[1]]
    tb = core_tc(pos, bpB, m)
    xs = up(2 * (XL.exp_up(b + dl) - 1 - (b + dl)) + XL.exp_up(b + dl) * (XL.exp_up(Eq + dl) - 1))
    cs = up(XL.exp_up(Eq) - 1)
    xd = up(XL.exp_up(Eq) * (XL.exp_up(dl) - 1))
    sa = c4a(D4, 2 * ETA0, pphi, phib, tb, xs, st)
    c4 = c4b(D4, pphi, tb, cs, xd, xi, st, sa)
    r = dict(k0=k0, pos=pos, m=m, a=a, b=b, l=l, dl=dl, h=h, sq=sq, xi=xi, xs=xs, cs=cs, xd=xd, pphi=pphi, sa=sa,
             c4=c4, C=cs + c4[0])
    if shared:
        chiM, CM, sH, hh, gg = shared
        if not (all(x <= y for x, y in zip(c4[1], chiM)) and r['C'] <= CM < 1):
            r['v'] = None                    # not below the shared state: rejected, as a case past the bound is
            return r
        pp = log_p(ETA0, c4[1], r['C'], c4[0], sH[0], hh[0][0], hh[0][1], Q, gg)
    else:
        sH, hh, gg = series(c4[1], r['C'])
        pp = log_p(ETA0, c4[1], r['C'], c4[0], sH[0], hh[0][0], hh[0][1], Q, gg)
    r['v'] = log_end(py, l, pp)
    return r


def series(chiM, CM):
    sH = (SPHI[Q], [abs(x) for x in SER[Q]])
    for k in range(Q - 1, 1, -1):
        sH = horner_step_c(chiM, CM, ETA0, SER[k], SPHI[k], log_v(CM, Q, k), log_v(CM, Q, k + 1), sH)
    hh = log_h(ETA0, chiM, CM, Q, sH)
    return sH, hh, log_g(hh)


# -- the cases, as explog_consts.log_bound enumerates them, with dyadic ends
def groups():
    M_ = XC.Expansion(N, 53, convex=True)
    Ex = XC.Exp(M_, S, DEG, 2)
    zk = up(1 / (2 * XC.L2E * (1 - U)))
    K0 = {}
    for (m, d, lo, hi, cap) in Ex.groups(Fr(0), up(zk * (1 + 3 * U))):
        ylo = down(lo * (1 - U) / (1 + U))
        llo = Fr(0) if lo == 0 else max(Fr(0), down((ylo - E0) / (1 + E1)))
        K0[(m, d)] = dict(a=ylo, hi=hi, lo=Fr(0) if llo < XC.LTINY else llo, lhi=up((hi + E0) / (1 - E1)))
        K0[(m, d)]['const'] = K0[(m, d)]['lo'] == 0 and hi <= E0
    lk = down(((1 - U) / (2 * XC.L2E * (1 + U)) - E0) / (1 + E1))
    # k != 0: |r| <= r_max + delta* and sum_{i >= 1} |r_i| <= the tail of pi^r, both at l = X, on Lean's mirrors
    rmax, al, ds = red_s(XC.XMAX)
    assert al[0] < Fr(1, 2) and (XC.XMAX + args(XC.XMAX)[0]) / (1 - U) <= Fr(7453, 10), 'Lemma 38 does not apply'
    top = up(rmax + ds)
    tail = up(sum(red(XC.XMAX, top)[1][1:]))
    K1 = {(m, d): dict(rlo=rlo, rhi=rhi) for (m, d, rlo, rhi, cap) in Ex.groups(tail, top)}
    assert set(K0) == set(K1)
    return K0, K1, lk


def st_k0(g, m, l):
    Eq, py = args(l)
    b = g['hi'] if g['const'] else l + Eq
    return dict(l=l, b=b, dl=Fr(0), pr=py)


def st_k1(l, b):
    dl, pr = red(l, b)
    return dict(l=l, b=b, dl=dl, pr=pr)


def hstate(m, sts):
    """a state above the cases sts, rounded up"""
    return ([up(max(s['pr'][i] for s in sts) / 2 ** m + eta1(m)) for i in range(N)],
            up(max(bp_of(m, s['b']) for s in sts)))


def under(e):
    return all(r['v'] is not None and r['v'] <= BOUND * U ** N * r['l'] + (FLOOR if e['ends'][0]['l'] == 0 else 0)
               for r in e['res'])


def layout(shared=None, fixed=None):
    """the entries (case, sign) with the head each takes; fixed: the heads of a first pass"""
    K0, K1, lk = groups()
    out = []
    for gi, key in enumerate(sorted(K0, key=lambda t: (-t[0], -t[1]))):
        m, d = key
        g0, g1 = K0[key], K1[key]
        e0s = [st_k0(g0, m, g0['lo']), st_k0(g0, m, g0['lhi'])]
        e1top = st_k1(XC.XMAX, g1['rhi'])
        joint = hstate(m, [e0s[1], e1top])
        own = hstate(m, [e0s[1]])
        for pos in (True, False):
            cands = [('joint', [joint, joint]), ('own', [own, own]), ('ends', [hstate(m, [s]) for s in e0s])]
            for lev, hs in cands:
                e = dict(gi=gi, k0=True, pos=pos, m=m, d=d, a=g0['a'], ends=e0s, lev=lev, bi=0)
                e['res'] = [evaluate(True, pos, m, g0['a'], s['b'], s['l'], s['dl'], s['pr'], head(h[0], h[1], d, m),
                                     shared) for s, h in zip(e0s, hs)]
                if under(e):
                    break
            assert under(e), ('k = 0', key, pos)
            out.append(e)
            for bins in ([(g1['rlo'], g1['rhi'])], XC.edges(g1['rlo'], g1['rhi'], 4)):
                res = []
                for bi, (ra, rb) in enumerate(bins):
                    ra = down(ra)                                    # a lower bound of |r| in 200 bits
                    ends = [st_k1(lk, rb), st_k1(XC.XMAX, rb)]
                    e = dict(gi=gi, k0=False, pos=pos, m=m, d=d, a=ra, ends=ends, lev='joint', bi=bi)
                    e['res'] = [evaluate(False, pos, m, ra, s['b'], s['l'], s['dl'], s['pr'],
                                         head(joint[0], joint[1], d, m), shared) for s in ends]
                    res.append(e)
                if all(under(e) for e in res):
                    break
            assert all(under(e) for e in res), ('k != 0', key, pos)
            out += res
    return out


# -- the Lean text
def lit(q):
    if q == 0:
        return '0'
    d = q.denominator
    return f'(dyQ {pair(q)})' if d & (d - 1) == 0 else f'({q.numerator} / {q.denominator} : ℚ)'


def st_text(st, ind):
    return f'({pair(st[0])},\n{" " * ind}[' + wrap([pair(x) for x in st[1]], ', ', ind + 1) + '])'


def stw_text(st, ind):
    return (f'(({pair(st[0][0])},\n{" " * ind}  {pair(st[0][1])}),\n{" " * ind}[' + wrap([pair(x) for x in st[1]], ', ', ind + 1)
            + '])')


def st4_text(st, ind):
    return (f'(({pair(st[0][0])},\n{" " * ind}  {pair(st[0][1])}),\n{" " * ind}([' + wrap([pair(x) for x in st[1][0]], ', ', ind + 2)
            + f'],\n{" " * ind} [' + wrap([pair(x) for x in st[1][1]], ', ', ind + 2) + ']))')


DEC = 'set_option maxHeartbeats 4000000 in\n'
KD = ' := by\n  decide +kernel\n'
T_ST, T_STW = '(ℤ × ℕ) × List (ℤ × ℕ)', '((ℤ × ℕ) × (ℤ × ℕ)) × List (ℤ × ℕ)'
T_ST4 = '((ℤ × ℕ) × (ℤ × ℕ)) × (List (ℤ × ℕ) × List (ℤ × ℕ))'
BL = {True: 'true', False: 'false'}


def head_text(h):
    """a state of a group: Horner's run in pieces, step (3)'s products, and its sum for each sign"""
    tag, d, m = f'log8_h{h["id"]}', h['d'], h['m']
    o = [f'\ndef {tag}_pq : List ℚ :=\n  [' + wrap([lit(x) for x in h['pq']], ', ', 3) + ']\n',
         f'\ndef {tag}_bp : ℚ := {lit(h["bp"])}\n']
    if d == 1:
        return ''.join(o)
    hs = h['hs']
    cuts = [j for j in range(len(hs)) if j % STEP == 0 or j == len(hs) - 1]
    for j in cuts[1:]:
        o.append(f'\ndef {tag}_s{j} : {T_ST} :=\n  {st_text(hs[j], 4)}\n')
    for a, b in zip(cuts, cuts[1:]):
        start = f'(hornerInitL 8 exp8F exp8Phi {d})' if a == 0 else f'(dySt {tag}_s{a})'
        o.append(f'\n{DEC}theorem {tag}_r{a}_{b} :\n    log8Run {tag}_pq {tag}_bp {d} {a} {b - a} {start} = '
                 f'dySt {tag}_s{b}{KD}')
    last = f'(hornerInitL 8 exp8F exp8Phi {d})' if len(hs) == 1 else f'(dySt {tag}_s{len(hs) - 1})'
    o.append(f'\ndef {tag}_w : {T_STW} :=\n  {stw_text(h["w"], 4)}\n')
    o.append(f'\n{DEC}theorem {tag}_wt : log8W {tag}_pq {tag}_bp {last} = dyStW {tag}_w{KD}')
    o.append(f'\ndef {tag}_y : {T_ST} :=\n  {st_text(h["y"], 4)}\n')
    o.append(f'\n{DEC}theorem {tag}_yt : log8Y {m} {d} {tag}_pq {tag}_bp (dyStW {tag}_w) = dySt {tag}_y{KD}')
    for s, sg in ((True, 'p'), (False, 'm')):
        o.append(f'\ndef {tag}_t{sg} : {T_ST} :=\n  {st_text(h["t"][s], 4)}\n')
        o.append(f'\n{DEC}theorem {tag}_t{sg}t :\n    log8T {BL[s]} {tag}_pq {tag}_bp (dySt {tag}_y) = dySt {tag}_t{sg}{KD}')
    return ''.join(o)


def eval_text(e, ei, r):
    """the checks of a case, a sign and an end"""
    h, m, pos = r['h'], r['m'], r['pos']
    ht = f'log8_h{h["id"]}'
    tag = f'log8_g{e["gi"]}{"z" if e["k0"] else "n"}{"p" if pos else "m"}{e["bi"]}e{ei}'
    A, Bq, Dl, L = lit(r['a']), lit(r['b']), lit(r['dl']), lit(r['l'])
    o = [f'\ndef {tag}_v : ℚ × ℚ × ℚ × ℚ :=\n  ({A},\n   {Bq},\n   {Dl},\n   {L})\n',
         f'\ndef {tag}_x : ℚ × ℚ × ℚ × ℚ :=\n  ({lit(r["xi"])},\n   {lit(r["xs"])},\n   {lit(r["cs"])},\n'
         f'   {lit(r["xd"])})\n',
         f'\ndef {tag}_ph : List ℚ :=\n  [' + wrap([lit(x) for x in r['pphi']], ', ', 3) + ']\n']
    va, vb, vd, vl = (f'{tag}_v.1', f'{tag}_v.2.1', f'{tag}_v.2.2.1', f'{tag}_v.2.2.2')
    xi, xs, cs, xd = (f'{tag}_x.1', f'{tag}_x.2.1', f'{tag}_x.2.2.1', f'{tag}_x.2.2.2')
    o.append(f'\n{DEC}theorem {tag}_leaf :\n    Log8Leaf {BL[e["k0"]]} {BL[pos]} {m} {va} {vb} {vd} {vl}\n'
             f'      {ht}_bp {ht}_pq {xi} {xs} {cs} {xd}\n      {tag}_ph{KD}')
    if h['d'] == 1:
        cur = f'(upQ 200 (eTrQ {ht}_bp 1 + 2 * ((8 : ℕ) : ℚ) * exp8Eta1 {m}), {ht}_pq)'
    else:
        cur = f'(dySt {ht}_t{"p" if pos else "m"})'
    j = 0
    while j < m:
        k = min(j + STEP, m)
        o.append(f'\ndef {tag}_s{k} : {T_ST} :=\n  {st_text(r["sq"][k], 4)}\n')
        term = cur
        for i in range(j, k):
            term = f'(log8Sq {BL[pos]} {m} {va} {vb} {i}\n        {term})'
        o.append(f'\n{DEC}theorem {tag}_q{j}_{k} :\n    {term[1:-1]} =\n      dySt {tag}_s{k}{KD}')
        cur = f'(dySt {tag}_s{k})'
        j = k
    o.append(f'\ndef {tag}_sa : {T_ST4} :=\n  {st4_text(r["sa"], 4)}\n')
    o.append(f'\n{DEC}theorem {tag}_a :\n    log8C4a {BL[pos]} {m} {vb} {vd} {vl}\n      {xi} {xs} {tag}_ph\n'
             f'      {cur} = dySt4 {tag}_sa{KD}')
    o.append(f'\ndef {tag}_c4 : {T_ST} :=\n  {st_text(r["c4"], 4)}\n')
    o.append(f'\n{DEC}theorem {tag}_b :\n    log8C4b {BL[pos]} {m} {vb} {xi} {cs} {xd}\n      {tag}_ph {cur}\n'
             f'      (dySt4 {tag}_sa) = dySt {tag}_c4{KD}')
    o.append(f'\n{DEC}theorem {tag}_end : Log8End {BL[e["ends"][0]["l"] == 0]} {vl} {cs} (dySt {tag}_c4){KD}')
    return ''.join(o)


DATA = '''import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation

/-!
# Theorem 42 at `n = 8` and `p = 53`: the series' coefficients and the shared state of step (5)

The eight parts of the coefficients `F'_k` of `(-1)^{k+1}/k`, `2 ≤ k ≤ 4`, each the greedy rounding to eight binary64
numbers, and the two parts of multidouble's double-double `ln 2`, as dyadic pairs `(m, k)` for `m / 2 ^ k`; a state
`(χ^M, C^M)` above step (4)'s `(χ, C)` of every case, and the states of Horner's rule on the series, of `c ⊗ h` and of
`ADDF(c ⊗ h, 1)` on it. This file is written by `log_lean.py`.
-/

namespace ExpansionBounds
'''

RUN = '''import ExpansionBounds.Log8.Defs

/-!
# Theorem 42 at `n = 8` and `p = 53`: the kernel's checks, part PART

For a state `(p_q, b_T)` of a group the kernel checks Horner's convex run in pieces of at most STEP steps, from the
state before a piece to the state after it, and step (3)'s two products and its sum for each sign. For a case, a sign
and an end `ℓ` of its interval it checks the rational bounds of the case's arguments (`Log8Leaf`), the squarings in
pieces of at most STEP, the two pieces of step (4), and the last product, the last ADD and the bound `9.926u^8 ℓ`,
plus `2^{-509}` at both ends of an interval from `ℓ = 0` (`Log8End`). `h` names a state, `g` a group, `z` a case of
`k = 0` and `n` one of `k ≠ 0`, `p` and `m` the sign of `r`, and `e0` and `e1` the ends. This file is written by
`log_lean.py`.
-/

namespace ExpansionBounds
'''


def data_text(shared):
    chiM, CM, sH, hh, gg = shared
    o = [DATA, '\n/-- the parts of the coefficients `F\'_k` -/\ndef log8Ser : List (List (ℤ × ℕ)) := [\n'
         + ',\n'.join('  [' + wrap([pair(x) for x in row], ', ', 3) + ']' for row in SER) + ']\n',
         f'\n/-- the leading part of the double-double `ln 2` -/\ndef log8CL0 : ℤ × ℕ :=\n  {pair(CL[0])}\n',
         f'\n/-- the trailing part of the double-double `ln 2` -/\ndef log8CL1 : ℤ × ℕ :=\n  {pair(CL[1])}\n',
         '\n/-- `χ^M`, above step (4)\'s `χ` of every case -/\ndef log8ChiM : List (ℤ × ℕ) :=\n  ['
         + wrap([pair(x) for x in chiM], ', ', 3) + ']\n',
         f'\n/-- `C^M`, above `C = e^E - 1 + E_c` of every case -/\ndef log8CM : ℤ × ℕ :=\n  {pair(CM)}\n',
         f'\n/-- Horner\'s rule on the series at `(χ^M, C^M)` -/\ndef log8SH : {T_ST} :=\n  {st_text(sH, 4)}\n',
         f'\n/-- `c ⊗ h` at `(χ^M, C^M)` -/\ndef log8HH : {T_STW} :=\n  {stw_text(hh, 4)}\n',
         f'\n/-- `ADDF(c ⊗ h, 1)` at `(χ^M, C^M)` -/\ndef log8GG : {T_ST} :=\n  {st_text(gg, 4)}\n']
    return ''.join(o) + '\nend ExpansionBounds\n'


TARGET = 450                         # seconds of one module, by the costs below


def cost_head(h):
    """seconds of the kernel on a state: about 1.8 a step of Horner's rule, and step (3)"""
    return 0 if h['d'] == 1 else 1.8 * (h['d'] - 2) + 3.6


def cost_eval(r):
    """seconds of the kernel on an evaluation"""
    return 5.5 + 1.8 * r['m'] + (0 if r['k0'] else 1.5)


def modules(ents):
    """the groups in modules: the first group alone, the others balanced by cost"""
    info = []
    for gi in sorted({e['gi'] for e in ents}):
        es = [e for e in ents if e['gi'] == gi]
        hs = sorted({id(r['h']): r['h'] for e in es for r in e['res']}.values(), key=lambda h: h['id'])
        info.append(dict(gi=gi, hs=hs, es=es,
                         cost=sum(cost_head(h) for h in hs) + sum(cost_eval(r) for e in es for r in e['res'])))
    ids = [h['id'] for g in info for h in g['hs']]
    assert len(ids) == len(set(ids)), 'a state in two groups'
    rest = sorted(info[1:], key=lambda g: -g['cost'])
    mods = [[] for _ in range(max(1, round(sum(g['cost'] for g in rest) / TARGET)))]
    for g in rest:
        min(mods, key=lambda b: sum(x['cost'] for x in b)).append(g)
    return [[info[0]]] + [sorted(b, key=lambda g: g['gi']) for b in mods]


ALL = '''IMPORTS
import ExpansionBounds.Log8.Table

/-!
# Theorem 42 at `n = 8` and `p = 53`: every state and every evaluation

The kernel's checks of `Log8/Run0.lean` to `RunLAST.lean` joined: `Log8Head` for each state of a group and each sign,
from the pieces of Horner's run, the two products and the sum; and `Log8Eval` for each case, sign and end, from its
rational bounds, its state, the squarings, the two pieces of step (4) and the bound. This file is written by
`log_lean.py`.
-/

namespace ExpansionBounds
BODY
end ExpansionBounds
'''


def head_all(h):
    """Log8Head of a state, for each sign"""
    tag, d, m = f'log8_h{h["id"]}', h['d'], h['m']
    o = [f'\ntheorem {tag}_q : ∀ q ∈ {tag}_pq, 0 ≤ q := by\n  decide +kernel\n']
    if d == 1:
        for s, sg in ((True, 'p'), (False, 'm')):
            o.append(f'\ntheorem {tag}_h{sg} : Log8Head {BL[s]} {m} 1 {tag}_pq {tag}_bp\n'
                     f'    (upQ 200 (eTrQ {tag}_bp 1 + 2 * ((8 : ℕ) : ℚ) * exp8Eta1 {m}), {tag}_pq) :=\n'
                     f'  Log8Head.mk_one {BL[s]} {m} {tag}_bp {tag}_q\n')
        return ''.join(o)
    hs = h['hs']
    cuts = [j for j in range(len(hs)) if j % STEP == 0 or j == len(hs) - 1]
    names = [(f'{tag}_r{a}_{b}', b - a) for a, b in zip(cuts, cuts[1:])]
    run = f'log8Run {tag}_pq {tag}_bp {d} 0 {d - 2} (hornerInitL 8 exp8F exp8Phi {d})'
    if not names:
        o.append(f'\ntheorem {tag}_r : {run} =\n    (hornerInitL 8 exp8F exp8Phi {d}) := rfl\n')
    else:
        term, rest = names[-1]
        for nm, k in reversed(names[:-1]):
            term = f'log8Run_cut {tag}_pq {tag}_bp {d} _ {k} {rest} {nm}\n    ({term})'
            rest += k
        o.append(f'\ntheorem {tag}_r : {run} =\n    dySt {tag}_s{len(hs) - 1} :=\n  {term}\n')
    for s, sg in ((True, 'p'), (False, 'm')):
        o.append(f'\ntheorem {tag}_h{sg} : Log8Head {BL[s]} {m} {d} {tag}_pq {tag}_bp (dySt {tag}_t{sg}) :=\n'
                 f'  Log8Head.mk_ne (by decide) {tag}_q {tag}_r {tag}_wt {tag}_yt {tag}_t{sg}t\n')
    return ''.join(o)


def eval_all(e, ei, r):
    """Log8Eval of a case, a sign and an end"""
    h, m, pos = r['h'], r['m'], r['pos']
    ht, sg = f'log8_h{h["id"]}', 'p' if pos else 'm'
    tag = f'log8_g{e["gi"]}{"z" if e["k0"] else "n"}{sg}{e["bi"]}e{ei}'
    va, vb, vd, vl = (f'{tag}_v.1', f'{tag}_v.2.1', f'{tag}_v.2.2.1', f'{tag}_v.2.2.2')
    if h['d'] == 1:
        t0 = f'(upQ 200 (eTrQ {ht}_bp 1 + 2 * ((8 : ℕ) : ℚ) * exp8Eta1 {m}), {ht}_pq)'
    else:
        t0 = f'(dySt {ht}_t{sg})'
    o = []
    sq = 'rfl'
    if m:
        term = t0
        for i in range(m):
            term = f'(log8Sq {BL[pos]} {m} {va} {vb} {i}\n      {term})'
        pieces = ', '.join(f'{tag}_q{j}_{min(j + STEP, m)}' for j in range(0, m, STEP))
        o.append(f'\ntheorem {tag}_sq :\n    log8SqRun {BL[pos]} {m} {va} {vb} {m} {t0} =\n      dySt {tag}_s{m} := by\n'
                 f'  show {term[1:-1]} = _\n  rw [{pieces}]\n')
        sq = f'{tag}_sq'
    zero = BL[e['ends'][0]['l'] == 0]
    o.append(f'\ntheorem {tag}_ev :\n    Log8Eval {BL[e["k0"]]} {BL[pos]} {m} {h["d"]} {va} {vl} {zero} {vb} {vd} :=\n'
             f'  Log8Eval.mk {tag}_leaf {ht}_h{sg} {sq} {tag}_a {tag}_b {tag}_end\n')
    return ''.join(o)


def all_text(mods, parts=None, tabs=None):
    parts = range(len(mods)) if parts is None else parts
    body = []
    for i in parts:
        for g in mods[i]:
            body += [head_all(h) for h in g['hs']]
            body += [eval_all(e, ei, r) for e in g['es'] for ei, r in enumerate(e['res'])]
    if tabs:
        body.append(groups_all(tabs[0], tabs[1], one=len(list(parts)) == 1))
    return (ALL.replace('IMPORTS', '\n'.join(f'import ExpansionBounds.Log8.Run{i}' for i in parts))
            .replace('LAST', str(len(mods) - 1)).replace('BODY', ''.join(body)))


UB = Fr(1, 2 ** 46)
TOP0 = 1 / (2 * XL.CR) * (1 + U)     # log8Top0


def egroups():
    """(m, d) -> (e_lo, e_hi, last): the exponents of a group, as exp_lean.groups enumerates them"""
    out, e = {}, -2
    while True:
        m = max(0, e + S + 1)
        d, e_lo = XL.degree(e - m), e
        while m == 0 and e_lo - 1 >= -1 - B and XL.degree(e_lo - 1) == d:
            e_lo -= 1
        out[(m, d)] = (e_lo, e, d == 1)
        if d == 1:
            return out
        e = e_lo - 1


def tables(ents):
    """the groups of k = 0 and of k != 0 as Log8/Groups.lean holds them, with Log8G0Ok and Log8G1Ok asserted"""
    K0, K1, lk = groups()
    eg = egroups()
    assert set(eg) == set(K0)
    rmax, al, ds = red_s(XC.XMAX)
    top = up(rmax + ds)
    tail = up(sum(red(XC.XMAX, top)[1][1:]))
    assert TOP0 < Fr(1, 2) * (1 - UB) * (1 - U) / (1 + U) and top < Fr(1, 2) * (1 - UB) - 2 * tail, 'e = -1 selected'
    assert lk * (1 + E1) + E0 <= (1 - U) / (2 * XL.CR * (1 + U))
    t0, t1 = [], []
    for gi, key in enumerate(sorted(K0, key=lambda t: (-t[0], -t[1]))):
        m, d = key
        e_lo, e_hi, last = eg[key]
        g0, g1 = K0[key], K1[key]
        es = [e for e in ents if e['gi'] == gi]
        z = [e for e in es if e['k0']][0]
        l1, l2, b1, b2 = z['ends'][0]['l'], z['ends'][1]['l'], z['ends'][0]['b'], z['ends'][1]['b']
        assert all(e['ends'][i]['b'] == (b1, b2)[i] for e in es if e['k0'] for i in (0, 1))
        a, hi = g0['a'], g0['hi']
        assert (a == 0 if last else 0 <= a <= Fr(2) ** e_lo * (1 - UB) * (1 - U) / (1 + U))
        assert min(TOP0, Fr(2) ** (e_hi + 1)) <= hi and 0 <= l1 and (l1 == 0 or l1 * (1 + E1) + E0 <= a)
        assert hi + E0 <= l2 * (1 - E1) and b2 + args(l2)[0] <= Fr(3, 5)
        assert (hi <= b1 and hi <= b2) if g0['const'] else (l1 + args(l1)[0] <= b1 and l2 + args(l2)[0] <= b2)
        t0.append(dict(gi=gi, m=m, d=d, elo=e_lo, ehi=e_hi, a=a, hi=hi, l1=l1, l2=l2, cst=g0['const'], zero=l1 == 0,
                       b1=b1, b2=b2, last=last))
        bins = {}
        for pos in (True, False):
            bs = sorted([e for e in es if not e['k0'] and e['pos'] == pos], key=lambda e: e['bi'])
            bins[pos] = [(e['a'], e['ends'][0]['b'], e['ends'][0]['dl'], e['ends'][1]['dl']) for e in bs]
            lo = bins[pos][0][0]
            for (ba, bb, _, d2), nxt in zip(bins[pos], bins[pos][1:] + [None]):
                assert bb + args(XC.XMAX)[0] + d2 <= Fr(3, 5)
                assert nxt[0] <= bb if nxt else g1['rhi'] <= bb
        lo = bins[True][0][0]
        assert bins[False][0][0] == lo and (lo == 0 if last else
                                            lo <= max(Fr(0), Fr(2) ** e_lo * (1 - UB) - 2 * tail))
        assert min(top, Fr(2) ** (e_hi + 1)) <= g1['rhi']
        t1.append(dict(gi=gi, m=m, d=d, elo=e_lo, ehi=e_hi, lo=lo, hi=g1['rhi'], bins=bins, last=last))
    return t0, t1, lk, top, tail


TABLE = '''import ExpansionBounds.Log8.Groups

/-!
# Theorem 42 at `n = 8` and `p = 53`: the tables of cases

The groups of exponents `e` of step (2)'s `U` with the same `m` and degree `d'`, for `k = 0` (`log8Grp0`, and the
last, of degree 1, `log8Last0`) and for `k ≠ 0` (`log8Grp1`, `log8Last1`), as `Log8/Groups.lean` describes them; the
lower end `ℓ_k^-` of `|ln x|` for `k ≠ 0`, and bounds of `|r|` and of `∑_{i ≥ 1}|r_i|` for `k ≠ 0`. This file is
written by `log_lean.py`.
-/

namespace ExpansionBounds
'''


def g0_text(g):
    return (f'{{ m := {g["m"]}, d := {g["d"]}, elo := {g["elo"]}, ehi := {g["ehi"]},\n    a := {lit(g["a"])},\n'
            f'    hi := {lit(g["hi"])},\n    l₁ := {lit(g["l1"])},\n    l₂ := {lit(g["l2"])},\n'
            f'    cst := {BL[g["cst"]]}, zero := {BL[g["zero"]]},\n    b₁ := {lit(g["b1"])},\n    b₂ := {lit(g["b2"])} }}')


def g1_text(g):
    bt = lambda bs: '[' + ',\n      '.join('(' + ',\n       '.join(lit(v) for v in bn) + ')' for bn in bs) + ']'
    return (f'{{ m := {g["m"]}, d := {g["d"]}, elo := {g["elo"]}, ehi := {g["ehi"]},\n    lo := {lit(g["lo"])},\n'
            f'    hi := {lit(g["hi"])},\n    binsP :=\n     {bt(g["bins"][True])},\n    binsN :=\n     '
            f'{bt(g["bins"][False])} }}')


def table_text(t0, t1, lk, top, tail):
    o = [TABLE, f'\n/-- `ℓ_k^-`: `|ln x|` is at least this for `k ≠ 0` -/\ndef log8Lk : ℚ :=\n  {lit(lk)}\n',
         f'\n/-- a bound of `|r|` for `k ≠ 0` -/\ndef log8Top1 : ℚ :=\n  {lit(top)}\n',
         f'\n/-- a bound of `∑_{{i ≥ 1}} |r_i|` for `k ≠ 0` -/\ndef log8Tail1 : ℚ :=\n  {lit(tail)}\n']
    for nm, ty, tx, t, k in (('0', 'Log8G0', g0_text, t0, '='), ('1', 'Log8G1', g1_text, t1, '≠')):
        o.append(f'\n/-- the groups for `k {k} 0`, but the last -/\ndef log8Grp{nm} : List {ty} := [\n  '
                 + ',\n  '.join(tx(g) for g in t[:-1]) + ']\n')
        o.append(f'\n/-- the last group for `k {k} 0`: degree 1, every `e` up to its `e_hi` -/\n'
                 f'def log8Last{nm} : {ty} :=\n  {tx(t[-1])}\n')
    return ''.join(o) + '\nend ExpansionBounds\n'


def tag_of(gi, k0, pos, bi, ei):
    return f'log8_g{gi}{"z" if k0 else "n"}{"p" if pos else "m"}{bi}e{ei}_ev'


def groups_all(t0, t1, one=False):
    """Log8Group0 and Log8Group1 of every group, from the evaluations"""
    def p0(g, ind):
        return (f'{ind}intro pos\n{ind}cases pos\n'
                f'{ind}· exact ⟨{tag_of(g["gi"], True, False, 0, 0)}, {tag_of(g["gi"], True, False, 0, 1)}⟩\n'
                f'{ind}· exact ⟨{tag_of(g["gi"], True, True, 0, 0)}, {tag_of(g["gi"], True, True, 0, 1)}⟩')

    def p1(g, ind, name=''):
        o = []
        for pos in (True, False):
            n = len(g['bins'][pos])
            o.append(f'{ind}· simp only [{name}List.mem_cons, List.not_mem_nil, or_false] at hb\n'
                     f'{ind}  rcases hb with '
                     + ' | '.join(['rfl'] * n) + '\n'
                     + '\n'.join(f'{ind}  · exact ⟨{tag_of(g["gi"], False, pos, bi, 0)}, '
                                  f'{tag_of(g["gi"], False, pos, bi, 1)}⟩' for bi in range(n)))
        return f'{ind}refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩\n' + '\n'.join(o)

    if one:
        return (f'\ntheorem log8_test0 : Log8Group0\n  {g0_text(t0[0])} := by\n{p0(t0[0], "  ")}\n'
                f'\ntheorem log8_test1 : Log8Group1 log8Lk\n  {g1_text(t1[0])} := by\n{p1(t1[0], "  ")}\n')
    o = ['\ntheorem log8_all0 : ∀ g ∈ log8Grp0, Log8Group0 g := by\n  intro g hg\n'
         '  simp only [log8Grp0, List.mem_cons, List.not_mem_nil, or_false] at hg\n  rcases hg with\n    '
         + wrap(['rfl'] * (len(t0) - 1), ' | ', 4) + '\n' + '\n'.join(f'  ·\n{p0(g, "    ")}' for g in t0[:-1])
         + '\n',
         f'\ntheorem log8_last0 : Log8Group0 log8Last0 := by\n{p0(t0[-1], "  ")}\n',
         '\ntheorem log8_all1 : ∀ g ∈ log8Grp1, Log8Group1 log8Lk g := by\n  intro g hg\n'
         '  simp only [log8Grp1, List.mem_cons, List.not_mem_nil, or_false] at hg\n  rcases hg with\n    '
         + wrap(['rfl'] * (len(t1) - 1), ' | ', 4) + '\n' + '\n'.join(f'  ·\n{p1(g, "    ")}' for g in t1[:-1]) + '\n',
         f'\ntheorem log8_last1 : Log8Group1 log8Lk log8Last1 := by\n{p1(t1[-1], "  ", "log8Last1, ")}\n']
    return ''.join(o)


PSI = """import ExpansionBounds.Log8.All
import ExpansionBounds.Log8.Psi

/-!
# Theorem 42 at `n = 8` and `p = 53`: the parts of `t` at the upper end of every case

For each case and sign the kernel checks that the part bounds of the state after the squarings, at the upper end of
the case's interval of `|ln x|`, sum to at most 1 (`Log8Psi`), on the states of `Log8/Run0.lean` to
`RunLAST.lean`; then `Log8GroupT0` and `Log8GroupT1` of every group. The largest sum is LARGEST. This file is
written by `log_lean.py`.
-/

namespace ExpansionBounds
BODY
end ExpansionBounds
"""


def psi_sum(r):
    return sum(r['sq'][r['m']][1])


def psi_tag(gi, k0, pos, bi):
    return f'log8_g{gi}{"z" if k0 else "n"}{"p" if pos else "m"}{bi}e1'


def psi_one(e, r):
    """Log8Psi of a case and a sign at the upper end"""
    h, m, pos = r['h'], r['m'], r['pos']
    ht, sg = f'log8_h{h["id"]}', 'p' if pos else 'm'
    tag = psi_tag(e['gi'], e['k0'], pos, e['bi'])
    assert psi_sum(r) <= 1, 'the part bounds of t sum above 1'
    sq = f'{tag}_sq' if m else 'rfl'
    return (f'\n{DEC}theorem {tag}_ps :\n    Log8Psi {BL[e["k0"]]} {BL[pos]} {m} {h["d"]} {tag}_v.1 {tag}_v.2.2.2 '
            f'{tag}_v.2.1 {tag}_v.2.2.1 :=\n  Log8Psi.mk {tag}_leaf {ht}_h{sg} {sq} (by decide +kernel)\n')


def psi_text(mods, tabs):
    t0, t1 = tabs[0], tabs[1]

    def p0(g, ind):
        return (f'{ind}intro pos\n{ind}cases pos\n{ind}· exact {psi_tag(g["gi"], True, False, 0)}_ps\n'
                f'{ind}· exact {psi_tag(g["gi"], True, True, 0)}_ps')

    def p1(g, ind, name=''):
        o = []
        for pos in (True, False):
            n = len(g['bins'][pos])
            o.append(f'{ind}· simp only [{name}List.mem_cons, List.not_mem_nil, or_false] at hb\n'
                     f'{ind}  rcases hb with ' + ' | '.join(['rfl'] * n) + '\n'
                     + '\n'.join(f'{ind}  · exact {psi_tag(g["gi"], False, pos, bi)}_ps' for bi in range(n)))
        return f'{ind}refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩\n' + '\n'.join(o)

    es = [e for b in mods for g in b for e in g['es']]
    body = [psi_one(e, e['res'][1]) for e in es]
    big = max(psi_sum(e['res'][1]) for e in es)
    body += ['\ntheorem log8_psi0 : ∀ g ∈ log8Grp0, Log8GroupT0 g := by\n  intro g hg\n'
             '  simp only [log8Grp0, List.mem_cons, List.not_mem_nil, or_false] at hg\n  rcases hg with\n    '
             + wrap(['rfl'] * (len(t0) - 1), ' | ', 4) + '\n' + '\n'.join(f'  ·\n{p0(g, "    ")}' for g in t0[:-1])
             + '\n',
             f'\ntheorem log8_psi_last0 : Log8GroupT0 log8Last0 := by\n{p0(t0[-1], "  ")}\n',
             '\ntheorem log8_psi1 : ∀ g ∈ log8Grp1, Log8GroupT1 g := by\n  intro g hg\n'
             '  simp only [log8Grp1, List.mem_cons, List.not_mem_nil, or_false] at hg\n  rcases hg with\n    '
             + wrap(['rfl'] * (len(t1) - 1), ' | ', 4) + '\n' + '\n'.join(f'  ·\n{p1(g, "    ")}' for g in t1[:-1])
             + '\n',
             f'\ntheorem log8_psi_last1 : Log8GroupT1 log8Last1 := by\n{p1(t1[-1], "  ", "log8Last1, ")}\n']
    return (PSI.replace('LAST', str(len(mods) - 1)).replace('LARGEST', f'{float(big):.6f}')
            .replace('BODY', ''.join(body))), len(es), big


def run_text(part, heads, evals, with_shared):
    o = [RUN.replace('PART', str(part)).replace('STEP', str(STEP))]
    if with_shared:
        o.append(f'\n{DEC}theorem log8_shared : Log8Shared{KD}')
    o += [head_text(h) for h in heads]
    o += [eval_text(e, ei, r) for e in evals for ei, r in enumerate(e['res'])]
    return ''.join(o) + '\nend ExpansionBounds\n'


if __name__ == '__main__':
    u8 = U ** N
    first = layout()
    chiM = [max(r['c4'][1][i] for e in first for r in e['res']) for i in range(N)]
    CM = up(max(r['C'] for e in first for r in e['res']))
    shared = (chiM, CM) + series(chiM, CM)
    HEADS.clear()
    ents = layout(shared)
    assert [(e['gi'], e['k0'], e['pos'], e['bi'], e['lev']) for e in ents] == \
        [(e['gi'], e['k0'], e['pos'], e['bi'], e['lev']) for e in first], 'the shared state changes the layout'
    rel = max((r['v'] - (FLOOR if e['ends'][0]['l'] == 0 else 0)) / r['l'] for e in ents for r in e['res'] if r['l'])
    fl = max(r['v'] for e in ents for r in e['res'] if r['l'] == 0)
    used = {id(r['h']): r['h'] for e in ents for r in e['res']}
    runs = [h for h in used.values() if h['d'] > 1]
    print(f'{len(ents)} cases with a sign, {sum(len(e["res"]) for e in ents)} evaluations, {len(runs)} runs of '
          f'Horner\'s rule of {sum(h["d"] - 2 for h in runs)} steps, {sum(e["m"] * len(e["res"]) for e in ents)} squarings')
    print(f'the largest (E - 2^-509)/l on intervals from 0, E/l otherwise: {XC.up_dec(rel / u8, 9)} u^8; '
          f'the largest E(0): 2^{XC.lg2_up(fl, 4)}; C^M <= 2^'
          f'{XC.lg2_up(CM, 2)}')
    ok = rel <= BOUND * u8 and fl <= FLOOR
    print(f'within {float(BOUND)} u^8 and 2^-509: {ok}')
    last = Fr(9925818, 10 ** 6)
    tight = rel > last * u8 and fl > FLOOR / 2
    print(f'control, {XC.up_dec(last, 6)} u^8 and 2^-510 must not hold: {tight}')
    DROP = True
    ctl = max(evaluate(r['k0'], r['pos'], r['m'], r['a'], r['b'], r['l'], r['dl'], [Fr(0)] * N, r['h'], shared)['v']
              / r['l'] for e in ents if e['gi'] == 0 and not e['k0'] for r in e['res'][:1])
    DROP = False
    caught = ctl < last * u8
    print(f'control, no error of the last ADD, falls below it: {caught}')
    ok = ok and tight and caught
    mods = modules(ents)
    print('modules, estimated seconds:', ', '.join(f'{sum(g["cost"] for g in b):.0f}' for b in mods))
    tabs = tables(ents)
    psi, npsi, big = psi_text(mods, tabs)
    print(f'checks of the parts of t: {npsi}, the largest sum {float(big):.9f}')
    if len(sys.argv) > 1 and ok:
        os.makedirs(os.path.join(sys.argv[1], 'Log8'), exist_ok=True)
        files = {'Log8/Data.lean': data_text(shared)}
        for i, b in enumerate(mods if len(sys.argv) > 2 and sys.argv[2] == 'all' else mods[:1]):
            files[f'Log8/Run{i}.lean'] = run_text(i, [h for g in b for h in g['hs']], [e for g in b for e in g['es']],
                                                  i == 0)
        if len(sys.argv) > 2 and sys.argv[2] == 'all':
            files['Log8/Table.lean'] = table_text(*tabs)
            files['Log8/All.lean'] = all_text(mods, tabs=tabs)
            files['Log8/PsiAll.lean'] = psi
        if len(sys.argv) > 3:                # a part alone, to test the joining before every module is built
            with open(sys.argv[3], 'w', encoding='utf-8') as f:
                f.write(all_text(mods, [0], tabs=tabs))
        for name, text in files.items():
            path = os.path.join(sys.argv[1], name)
            if os.path.exists(path) and open(path, encoding='utf-8').read() == text:
                continue
            with open(path, 'w', encoding='utf-8') as f:
                f.write(text)
            print('wrote', path, len(text.split('\n')), 'lines')
    sys.exit(0 if ok else 1)
