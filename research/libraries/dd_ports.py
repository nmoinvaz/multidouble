"""Double-word (two-part) algorithms of shipped libraries, ported onto paper/fpemu.py.

Sources (read as data only):
  Boost.Multiprecision develop @ 42cfe9ebd6 (2026-02-06): include/boost/multiprecision/cpp_double_fp.hpp,
    include/boost/multiprecision/cpp_df_qf/cpp_df_qf_detail.hpp. Its tutorial (doc/tutorial_cpp_double_fp_backend.qbk:72)
    defers error bounds to Joldes, Muller and Popescu 2017 (JMP17).
  DoubleFloats.jl 1.12.0 @ 60b72ca: src/math/ops/op_dddd_dd.jl.
JMP17 bounds used for reference: Alg. 6 AccurateDWPlusDW 3u^2/(1-4u); Alg. 10 DWTimesDW1 7u^2/(1+u)^2;
Alg. 17 DWDivDW2 15u^2 + 56u^3.
"""
from ports import F, add, sub, mul, fma, div, neg

SPLIT = None


def split_const():
    """split_maker<double>::value = 1 + 2^n_shl with n_shl = (digits + 1)/2 (cpp_df_qf_detail.hpp)"""
    s = (F.P + 1) // 2
    return F.rnd((1 << s) + 1, 0)


# --- cpp_df_qf_detail.hpp exact_arithmetic ---
def bx_two_sum(a, b):  # cpp_df_qf_detail.hpp two_sum
    hi = add(a, b)
    a1 = sub(hi, b)
    return hi, add(sub(a, a1), sub(b, sub(hi, a1)))


def bx_two_diff(a, b):  # cpp_df_qf_detail.hpp two_diff
    hi = sub(a, b)
    a1 = add(hi, b)
    return hi, sub(sub(a, a1), add(b, sub(hi, a1)))


def bx_two_hilo_sum(a, b):  # cpp_df_qf_detail.hpp two_hilo_sum (Fast2Sum)
    hi = add(a, b)
    return hi, sub(b, sub(hi, a))


def boost_add(x, y):  # cpp_double_fp.hpp add_unchecked (lines 1030-1053)
    thi, tlo = bx_two_sum(x[1], y[1])
    h, l = bx_two_sum(x[0], y[0])
    h, l = bx_two_hilo_sum(h, add(l, thi))
    return list(bx_two_hilo_sum(h, add(tlo, l)))


def boost_mul(x, y):  # cpp_double_fp.hpp mul_unchecked (lines 1055-1132), no-overflow path
    S = split_const()
    C = mul(S, x[0])
    hu = sub(C, sub(C, x[0]))
    C = mul(x[0], y[0])
    c = mul(S, y[0])
    hv = sub(c, sub(c, y[0]))
    tv = sub(y[0], hv)
    t1 = fma(hu, tv, fma(hu, hv, neg(C)))
    tu = sub(x[0], hu)
    c = add(add(fma(tu, tv, fma(tu, hv, t1)), mul(x[0], y[1])), mul(x[1], y[0]))
    h = add(C, c)
    return [h, add(sub(C, h), c)]


def boost_div(x, y):  # cpp_double_fp.hpp operator/= (lines 696-764), no-overflow path
    S = split_const()
    C = div(x[0], y[0])
    c = mul(S, C)
    hc = sub(c, sub(c, C))
    u = mul(S, y[0])
    hv = sub(u, sub(u, y[0]))
    U = mul(C, y[0])
    u = fma(hc, hv, neg(U))
    tv = sub(y[0], hv)
    u = fma(hc, tv, u)
    tc = sub(C, hc)
    u = fma(tc, hv, u)
    u = fma(tc, tv, u)
    c = add(sub(sub(x[0], U), u), x[1])
    c = div(sub(c, mul(C, y[1])), y[0])
    h = add(C, c)
    return [h, add(sub(C, h), c)]


def boost_sqrt(x):  # cpp_double_fp.hpp eval_sqrt (lines 1463-1510)
    S = split_const()
    c = F.fsqrt(x[0])
    p = mul(S, c)
    hx = add(sub(c, p), p)
    tx = sub(c, hx)
    q = mul(hx, tx)
    q = add(q, q)
    p = mul(hx, hx)
    u = add(p, q)
    uu = fma(tx, tx, add(sub(p, u), q))
    cc = div(add(sub(sub(x[0], u), uu), x[1]), add(c, c))
    h = add(c, cc)
    return [h, add(sub(c, h), cc)]


# --- DoubleFloats.jl src/math/ops/op_dddd_dd.jl ---
def jl_two_sum(a, b):  # errorfree.jl two_sum (Knuth)
    s = add(a, b)
    v = sub(s, a)
    return s, add(sub(a, sub(s, v)), sub(b, v))


def jl_two_prod(a, b):
    p = mul(a, b)
    return p, fma(a, b, neg(p))


def df_add(x, y):  # op_dddd_dd.jl:2-12 (Alg. 6)
    hi, lo = jl_two_sum(x[0], y[0])
    thi, tlo = jl_two_sum(x[1], y[1])
    c = add(lo, thi)
    hi, lo = bx_two_hilo_sum(hi, c)
    c = add(tlo, lo)
    return list(bx_two_hilo_sum(hi, c))


def df_mul(x, y):  # op_dddd_dd.jl:29-39 (Alg. 10)
    hi, lo = jl_two_prod(x[0], y[0])
    t = add(mul(x[0], y[1]), mul(x[1], y[0]))
    t = add(lo, t)
    return list(bx_two_hilo_sum(hi, t))


def df_div(x, y):  # op_dddd_dd.jl:80-91
    hi = div(x[0], y[0])
    uh, ul = jl_two_prod(hi, y[0])
    lo = div(sub(add(sub(sub(x[0], uh), ul), x[1]), mul(hi, y[1])), y[0])
    return list(bx_two_hilo_sum(hi, lo))


# --- JMP17 reference algorithms (for the controls) ---
def jmp_dw_times_fp1(x, y):  # JMP17 Alg. 7
    ch, cl1 = jl_two_prod(x[0], y)
    cl2 = mul(x[1], y)
    th, tl1 = bx_two_hilo_sum(ch, cl2)
    tl2 = add(tl1, cl1)
    return list(bx_two_hilo_sum(th, tl2))


def jmp_div_dw2(x, y):  # JMP17 Alg. 17
    th = div(x[0], y[0])
    rh, rl = jmp_dw_times_fp1(y, th)
    ph = sub(x[0], rh)
    dl = sub(x[1], rl)
    d = add(ph, dl)
    tl = div(d, y[0])
    return list(bx_two_hilo_sum(th, tl))
