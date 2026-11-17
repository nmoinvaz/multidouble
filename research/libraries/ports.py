"""Faithful ports of shipped expansion arithmetic onto paper/fpemu.py (exact p-bit RN-even emulation).

Every function names its source file and line. External code was read as data only; nothing was built or run.
Sources:
  QD 2.3.24 (qd-2.3.24.tar.gz from LBNL), include/qd/inline.h, include/qd/qd_inline.h, src/qd_real.cpp.
  CAMPARY, mirror github.com/LegalizeAdulthood/campary at e805449 (2025-08-05), Doubles/src_cpu/*.h.
Values are fpemu tuples (m, e). Two-prod uses the FMA form (QD_FMS / CAMPARY two_prod), as on every current CPU.
"""
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'paper'))
import fpemu as F  # noqa: E402

add, sub, mul, fma, div, neg = F.add, F.sub, F.mul, F.fma, F.div, F.neg
Z = F.PZ


def val(x):
    m, e = x
    if m == 0:
        return Fraction(0)
    return Fraction(m) * (Fraction(2) ** e)


def vsum(xs):
    return sum((val(x) for x in xs), Fraction(0))


def fabs_gt(x, y):
    """|x| > |y| (std::abs(x) > std::abs(y), fabs(x) > fabs(y))"""
    return abs(val(x)) > abs(val(y))


# ------------------------------------------------------------------------------------------------------------
# QD 2.3.24 error-free transformations, include/qd/inline.h
# ------------------------------------------------------------------------------------------------------------

def qd_quick_two_sum(a, b):  # inline.h:36-40
    s = add(a, b)
    return s, sub(b, sub(s, a))


def qd_two_sum(a, b):  # inline.h:50-55
    s = add(a, b)
    bb = sub(s, a)
    return s, add(sub(a, sub(s, bb)), sub(b, bb))


def qd_two_prod(a, b):  # inline.h:85-89 (QD_FMS branch)
    p = mul(a, b)
    return p, fma(a, b, neg(p))


# ------------------------------------------------------------------------------------------------------------
# QD 2.3.24 qd_real, include/qd/qd_inline.h
# ------------------------------------------------------------------------------------------------------------

def qd_renorm4(c0, c1, c2, c3):  # qd_inline.h:95-125
    s2 = s3 = Z
    s0, c3 = qd_quick_two_sum(c2, c3)
    s0, c2 = qd_quick_two_sum(c1, s0)
    c0, c1 = qd_quick_two_sum(c0, s0)
    s0 = c0
    s1 = c1
    if s1[0] != 0:
        s1, s2 = qd_quick_two_sum(s1, c2)
        if s2[0] != 0:
            s2, s3 = qd_quick_two_sum(s2, c3)
        else:
            s1, s2 = qd_quick_two_sum(s1, c3)
    else:
        s0, s1 = qd_quick_two_sum(s0, c2)
        if s1[0] != 0:
            s1, s2 = qd_quick_two_sum(s1, c3)
        else:
            s0, s1 = qd_quick_two_sum(s0, c3)
    return [s0, s1, s2, s3]


def qd_renorm5(c0, c1, c2, c3, c4):  # qd_inline.h:127-177
    s2 = s3 = Z
    s0, c4 = qd_quick_two_sum(c3, c4)
    s0, c3 = qd_quick_two_sum(c2, s0)
    s0, c2 = qd_quick_two_sum(c1, s0)
    c0, c1 = qd_quick_two_sum(c0, s0)
    s0 = c0
    s1 = c1
    if s1[0] != 0:
        s1, s2 = qd_quick_two_sum(s1, c2)
        if s2[0] != 0:
            s2, s3 = qd_quick_two_sum(s2, c3)
            if s3[0] != 0:
                s3 = add(s3, c4)
            else:
                s2, s3 = qd_quick_two_sum(s2, c4)
        else:
            s1, s2 = qd_quick_two_sum(s1, c3)
            if s2[0] != 0:
                s2, s3 = qd_quick_two_sum(s2, c4)
            else:
                s1, s2 = qd_quick_two_sum(s1, c4)
    else:
        s0, s1 = qd_quick_two_sum(s0, c2)
        if s1[0] != 0:
            s1, s2 = qd_quick_two_sum(s1, c3)
            if s2[0] != 0:
                s2, s3 = qd_quick_two_sum(s2, c4)
            else:
                s1, s2 = qd_quick_two_sum(s1, c4)
        else:
            s0, s1 = qd_quick_two_sum(s0, c3)
            if s1[0] != 0:
                s1, s2 = qd_quick_two_sum(s1, c4)
            else:
                s0, s1 = qd_quick_two_sum(s0, c4)
    return [s0, s1, s2, s3]


def qd_three_sum(a, b, c):  # qd_inline.h:192-197
    t1, t2 = qd_two_sum(a, b)
    a, t3 = qd_two_sum(c, t1)
    b, c = qd_two_sum(t2, t3)
    return a, b, c


def qd_three_sum2(a, b, c):  # qd_inline.h:199-204
    t1, t2 = qd_two_sum(a, b)
    a, t3 = qd_two_sum(c, t1)
    b = add(t2, t3)
    return a, b, c


def qd_add_d(a, b):  # qd_inline.h:209-221, quad-double + double
    c0, e = qd_two_sum(a[0], b)
    c1, e = qd_two_sum(a[1], e)
    c2, e = qd_two_sum(a[2], e)
    c3, e = qd_two_sum(a[3], e)
    return qd_renorm5(c0, c1, c2, c3, e)


def qd_sloppy_add(a, b):  # qd_inline.h:360-405 (the live code; 340-355 is the commented reference version)
    s0, t0 = qd_two_sum(a[0], b[0])  # 367-395 is two_sum written out per lane
    s1, t1 = qd_two_sum(a[1], b[1])
    s2, t2 = qd_two_sum(a[2], b[2])
    s3, t3 = qd_two_sum(a[3], b[3])
    s1, t0 = qd_two_sum(s1, t0)  # 397
    s2, t0, t1 = qd_three_sum(s2, t0, t1)  # 398
    s3, t0, t2 = qd_three_sum2(s3, t0, t2)  # 399
    t0 = add(add(t0, t1), t3)  # 400
    return qd_renorm5(s0, s1, s2, s3, t0)  # 403


def qd_quick_three_accum(a, b, c):  # qd_inline.h:261-282; returns (s, a, b)
    s, b = qd_two_sum(b, c)
    s, a = qd_two_sum(a, s)
    za = a[0] != 0
    zb = b[0] != 0
    if za and zb:
        return s, a, b
    if not zb:
        b = a
        a = s
    else:
        a = s
    return Z, a, b


def qd_ieee_add(a, b):  # qd_inline.h:286-336
    i = j = k = 0
    x = [Z, Z, Z, Z]
    if fabs_gt(a[i], b[j]):
        u = a[i]; i += 1
    else:
        u = b[j]; j += 1
    if fabs_gt(a[i], b[j]):
        v = a[i]; i += 1
    else:
        v = b[j]; j += 1
    u, v = qd_quick_two_sum(u, v)
    while k < 4:
        if i >= 4 and j >= 4:
            x[k] = u
            if k < 3:
                k += 1
                x[k] = v
            break
        if i >= 4:
            t = b[j]; j += 1
        elif j >= 4:
            t = a[i]; i += 1
        elif fabs_gt(a[i], b[j]):
            t = a[i]; i += 1
        else:
            t = b[j]; j += 1
        s, u, v = qd_quick_three_accum(u, v, t)
        if s[0] != 0:
            x[k] = s
            k += 1
    for kk in range(i, 4):
        x[3] = add(x[3], a[kk])
    for kk in range(j, 4):
        x[3] = add(x[3], b[kk])
    return qd_renorm4(*x)


def qd_mul_d(a, b):  # qd_inline.h:490-513, quad-double * double
    p0, q0 = qd_two_prod(a[0], b)
    p1, q1 = qd_two_prod(a[1], b)
    p2, q2 = qd_two_prod(a[2], b)
    p3 = mul(a[3], b)
    s0 = p0
    s1, s2 = qd_two_sum(q0, p1)
    s2, q1, p2 = qd_three_sum(s2, q1, p2)
    q1, q2, p3 = qd_three_sum2(q1, q2, p3)
    s3 = q1
    s4 = add(q2, p2)
    return qd_renorm5(s0, s1, s2, s3, s4)


def qd_sloppy_mul(a, b):  # qd_inline.h:567-599
    p0, q0 = qd_two_prod(a[0], b[0])
    p1, q1 = qd_two_prod(a[0], b[1])
    p2, q2 = qd_two_prod(a[1], b[0])
    p3, q3 = qd_two_prod(a[0], b[2])
    p4, q4 = qd_two_prod(a[1], b[1])
    p5, q5 = qd_two_prod(a[2], b[0])
    p1, p2, q0 = qd_three_sum(p1, p2, q0)
    p2, q1, q2 = qd_three_sum(p2, q1, q2)
    p3, p4, p5 = qd_three_sum(p3, p4, p5)
    s0, t0 = qd_two_sum(p2, p3)
    s1, t1 = qd_two_sum(q1, p4)
    s2 = add(q2, p5)
    s1, t0 = qd_two_sum(s1, t0)
    s2 = add(s2, add(t0, t1))
    # 596: s1 += a0*b3 + a1*b2 + a2*b1 + a3*b0 + q0 + q3 + q4 + q5 (C++ left-to-right, then +=)
    acc = mul(a[0], b[3])
    for t in (mul(a[1], b[2]), mul(a[2], b[1]), mul(a[3], b[0]), q0, q3, q4, q5):
        acc = add(acc, t)
    s1 = add(s1, acc)
    return qd_renorm5(p0, p1, s0, s1, s2)


def qd_accurate_mul(a, b):  # qd_inline.h:601-661
    p0, q0 = qd_two_prod(a[0], b[0])
    p1, q1 = qd_two_prod(a[0], b[1])
    p2, q2 = qd_two_prod(a[1], b[0])
    p3, q3 = qd_two_prod(a[0], b[2])
    p4, q4 = qd_two_prod(a[1], b[1])
    p5, q5 = qd_two_prod(a[2], b[0])
    p1, p2, q0 = qd_three_sum(p1, p2, q0)
    p2, q1, q2 = qd_three_sum(p2, q1, q2)
    p3, p4, p5 = qd_three_sum(p3, p4, p5)
    s0, t0 = qd_two_sum(p2, p3)
    s1, t1 = qd_two_sum(q1, p4)
    s2 = add(q2, p5)
    s1, t0 = qd_two_sum(s1, t0)
    s2 = add(s2, add(t0, t1))
    p6, q6 = qd_two_prod(a[0], b[3])
    p7, q7 = qd_two_prod(a[1], b[2])
    p8, q8 = qd_two_prod(a[2], b[1])
    p9, q9 = qd_two_prod(a[3], b[0])
    q0, q3 = qd_two_sum(q0, q3)
    q4, q5 = qd_two_sum(q4, q5)
    p6, p7 = qd_two_sum(p6, p7)
    p8, p9 = qd_two_sum(p8, p9)
    t0, t1 = qd_two_sum(q0, q4)
    t1 = add(t1, add(q3, q5))
    r0, r1 = qd_two_sum(p6, p8)
    r1 = add(r1, add(p7, p9))
    q3, q4 = qd_two_sum(t0, r0)
    q4 = add(q4, add(t1, r1))
    t0, t1 = qd_two_sum(q3, s1)
    t1 = add(t1, q4)
    # 657: t1 += a1*b3 + a2*b2 + a3*b1 + q6 + q7 + q8 + q9 + s2
    acc = mul(a[1], b[3])
    for t in (mul(a[2], b[2]), mul(a[3], b[1]), q6, q7, q8, q9, s2):
        acc = add(acc, t)
    t1 = add(t1, acc)
    return qd_renorm5(p0, p1, s0, t0, t1)


def qd_neg(a):  # qd_inline.h:438-440
    return [neg(x) for x in a]


def qd_sub(a, b, ieee=False):  # qd_inline.h:459-461, a + (-b), with the default sloppy add
    return (qd_ieee_add if ieee else qd_sloppy_add)(a, qd_neg(b))


def qd_sloppy_div(a, b, ieee=False):  # src/qd_real.cpp:693-712 (the default, QD_SLOPPY_DIV)
    q0 = div(a[0], b[0])
    r = qd_sub(a, qd_mul_d(b, q0), ieee)
    q1 = div(r[0], b[0])
    r = qd_sub(r, qd_mul_d(b, q1), ieee)
    q2 = div(r[0], b[0])
    r = qd_sub(r, qd_mul_d(b, q2), ieee)
    q3 = div(r[0], b[0])
    return qd_renorm4(q0, q1, q2, q3)


def qd_accurate_div(a, b, ieee=False):  # src/qd_real.cpp:714-736
    q0 = div(a[0], b[0])
    r = qd_sub(a, qd_mul_d(b, q0), ieee)
    q1 = div(r[0], b[0])
    r = qd_sub(r, qd_mul_d(b, q1), ieee)
    q2 = div(r[0], b[0])
    r = qd_sub(r, qd_mul_d(b, q2), ieee)
    q3 = div(r[0], b[0])
    r = qd_sub(r, qd_mul_d(b, q3), ieee)
    q4 = div(r[0], b[0])
    return qd_renorm5(q0, q1, q2, q3, q4)


# ------------------------------------------------------------------------------------------------------------
# CAMPARY, Doubles/src_cpu (errorFreeTransf.h, renorm.h, addition.h)
# ------------------------------------------------------------------------------------------------------------

def cp_fast_two_sum(a, b):  # errorFreeTransf.h:38-43
    s = add(a, b)
    z = add(s, neg(a))
    return s, add(b, neg(z))


def cp_two_sum(a, b):  # errorFreeTransf.h:54-62
    s = add(a, b)
    aa = add(s, neg(b))
    bb = add(s, neg(aa))
    da = add(a, neg(aa))
    db = add(b, neg(bb))
    return s, add(da, db)


def cp_vecsum(x):  # renorm.h:100-108 (non-unrolled branch); r[0] is the sum
    sX = len(x)
    r = [Z] * sX
    s, r[sX - 1] = cp_fast_two_sum(x[sX - 2], x[sX - 1])
    for i in range(sX - 3, 0, -1):
        s, r[i + 1] = cp_two_sum(x[i], s)
    r[0], r[1] = cp_two_sum(x[0], s)
    return r


def cp_second_pass(f, sR):  # renorm.h:234-241 (shared by renorm2L, renorm2L_4Add1, renorm_rand2L)
    sX = len(f)
    r = [Z] * sR
    ptr = 0
    i = 2
    if f[1][0] == 0:
        e = f[0]
    else:
        r[0] = f[0]
        e = f[1]
        ptr += 1
    while ptr < sR and i < sX:
        r[ptr], e = cp_fast_two_sum(e, f[i])
        i += 1
        if e[0] == 0:
            e = r[ptr]
        else:
            ptr += 1
    if ptr < sR and e[0] != 0:
        r[ptr] = e
        ptr += 1
    for k in range(ptr, sR):
        r[k] = Z
    return r


def cp_renorm2L(x, sR):  # renorm.h:228-242
    return cp_second_pass(cp_vecsum(x), sR)


def cp_vecsum_4add1(x, y):  # renorm.h:112-120
    sX = len(x)
    r = [Z] * (sX + 1)
    s, r[sX] = cp_two_sum(x[sX - 1], y)
    for i in range(sX - 2, 0, -1):
        s, r[i + 1] = cp_two_sum(x[i], s)
    r[0], r[1] = cp_two_sum(x[0], s)
    return r


def cp_renorm2L_4add1(x, y, sR):  # renorm.h:247-261
    return cp_second_pass(cp_vecsum_4add1(x, y), sR)


def cp_renorm_rand2L(x, sR):  # renorm.h:346-366
    sX = len(x)
    f = [Z] * sX
    f[0], f[1] = cp_two_sum(x[0], x[1])
    for i in range(2, sX):
        pr, f[i] = cp_two_sum(f[i - 1], x[i])
        for j in range(i - 2, 0, -1):
            pr, f[j + 1] = cp_two_sum(f[j], pr)
        f[0], f[1] = cp_fast_two_sum(f[0], pr)
    return cp_second_pass(f, sR)


def cp_fast_vecsum(x):  # renorm.h:78-86
    sX = len(x)
    r = [Z] * sX
    s, r[sX - 1] = cp_fast_two_sum(x[sX - 2], x[sX - 1])
    for i in range(sX - 3, 0, -1):
        s, r[i + 1] = cp_fast_two_sum(x[i], s)
    r[0], r[1] = cp_fast_two_sum(x[0], s)
    return r


def cp_fast_renorm2L(x, sR):  # renorm.h:195-209
    return cp_second_pass(cp_fast_vecsum(x), sR)


def cp_merge(x, y):  # addition.h:35-41
    K, L = len(x), len(y)
    z = []
    i = j = 0
    for _ in range(K + L):
        if i == K or (j < L and fabs_gt(y[j], x[i])):
            z.append(y[j]); j += 1
        else:
            z.append(x[i]); i += 1
    return z


def cp_certified_add(x, y, R):  # addition.h:47-55, "relative error < 4.5 * 2^{-(prec-1)R}"
    if len(x) == 1:
        return cp_renorm2L_4add1(y, x[0], R)
    if len(y) == 1:
        return cp_renorm2L_4add1(x, y[0], R)
    return cp_renorm2L(cp_merge(x, y), R)


def _bailey_levels(x, y, R):  # addition.h:66-83 and 97-114 (identical level builders)
    K, L = len(x), len(y)
    f = [Z] * (R + 1)
    for i in range(K, R):
        f[i] = Z
    nn = R
    if nn < L:
        f[nn] = add(x[nn], y[nn])
    elif nn < K:
        f[nn] = x[nn]
    else:
        f[nn] = Z
    for n in range((K - 1) if R + 1 > K else (R - 1), L - 1, -1):
        f[n] = x[n]
    for n in range((L - 1) if R + 1 > L else (R - 1), -1, -1):
        f[n], e = cp_two_sum(x[n], y[n])
        for i in range(n + 1, R):
            f[i], e = cp_two_sum(f[i], e)
        f[R] = add(f[R], e)
    return f


def cp_bailey_add_renorm(x, y, R):  # addition.h:93-118, "relative error < 24 * 2^{-(prec-1)R}"
    if len(y) == 1:
        return cp_renorm2L_4add1(x, y[0], R)
    return cp_renorm_rand2L(_bailey_levels(x, y, R), R)


def cp_bailey_add_fast(x, y, R):  # addition.h:62-87, "quick and dirty", no bound stated
    if len(y) == 1:
        return cp_renorm2L_4add1(x, y[0], R)
    return cp_fast_renorm2L(_bailey_levels(x, y, R), R)


def cp_bailey_mul_levels(x, y, R):  # multiplication.h:398-485 (the level builder, same as baileyMul_fast 301-392)
    K, L = len(x), len(y)
    assert K >= L
    f = [Z] * (R + 1)
    nn = R
    if nn < L:
        f[nn] = mul(x[0], y[nn])
        for i in range(1, nn + 1):
            f[nn] = fma(x[i], y[nn - i], f[nn])  # FP_FAST_FMA branch
    elif nn < K:
        f[nn] = mul(x[nn], y[0])
        for j in range(1, L):
            f[nn] = fma(x[nn - j], y[j], f[nn])
    elif nn < K + L - 1:
        f[nn] = mul(x[nn - L + 1], y[L - 1])
        for i in range(nn - L + 2, K):
            f[nn] = fma(x[i], y[nn - i], f[nn])
    else:
        f[nn] = Z

    def carry(n, e):
        for j in range(n + 1, R):
            f[j], e = cp_two_sum(f[j], e)
        f[R] = add(f[R], e)

    for n in range((K + L - 2) if R + 1 > K + L - 1 else (R - 1), K - 1, -1):
        f[n], e = X_two_prod(x[n - L + 1], y[L - 1])
        carry(n, e)
        for i in range(n - L + 2, K):
            p, e = X_two_prod(x[i], y[n - i])
            carry(n, e)
            f[n], e = cp_two_sum(f[n], p)
            carry(n, e)
    for n in range((K - 1) if R + 1 > K else (R - 1), L - 1, -1):
        f[n], e = X_two_prod(x[n], y[0])
        carry(n, e)
        for j in range(1, L):
            p, e = X_two_prod(x[n - j], y[j])
            carry(n, e)
            f[n], e = cp_two_sum(f[n], p)
            carry(n, e)
    for n in range((L - 1) if R + 1 > L else (R - 1), -1, -1):
        f[n], e = X_two_prod(x[0], y[n])
        carry(n, e)
        for i in range(1, n + 1):
            p, e = X_two_prod(x[i], y[n - i])
            carry(n, e)
            f[n], e = cp_two_sum(f[n], p)
            carry(n, e)
    return f


def X_two_prod(a, b):  # errorFreeTransf.h:76-80
    p = mul(a, b)
    return p, fma(a, b, neg(p))


def cp_bailey_mul_renorm(x, y, R):  # multiplication.h:396-487
    return cp_renorm_rand2L(cp_bailey_mul_levels(x, y, R), R)


def cp_bailey_mul_fast(x, y, R):  # multiplication.h:298-393 (no bound stated)
    return cp_fast_renorm2L(cp_bailey_mul_levels(x, y, R), R)


# ------------------------------------------------------------------------------------------------------------
# GQD (Lu, He and Luo; github.com/lumianph/gpuprec @ 452baddaf6, 2015-12-23), gqd/gqd_basic.cu. Its two_sum,
# quick_two_sum (inline.cu) return the same values as QD's (they only short-circuit a zero operand), and its
# Dekker two_prod is exact in the normal range, so the QD ports above serve for them.
# ------------------------------------------------------------------------------------------------------------

def gqd_renorm5(c0, c1, c2, c3, c4):  # gqd_basic.cu:61-112
    s2 = s3 = Z
    s0, c4 = qd_quick_two_sum(c3, c4)
    s0, c3 = qd_quick_two_sum(c2, s0)
    s0, c2 = qd_quick_two_sum(c1, s0)
    c0, c1 = qd_quick_two_sum(c0, s0)
    s0 = c0
    s1 = c1
    s0, s1 = qd_quick_two_sum(c0, c1)  # gqd_basic.cu:78, not in QD
    if s1[0] != 0:
        s1, s2 = qd_quick_two_sum(s1, c2)
        if s2[0] != 0:
            s2, s3 = qd_quick_two_sum(s2, c3)
            if s3[0] != 0:
                s3 = add(s3, c4)
            else:
                s2 = add(s2, c4)  # gqd_basic.cu:84; QD has s2 = quick_two_sum(s2, c4, s3)
        else:
            s1, s2 = qd_quick_two_sum(s1, c3)
            if s2[0] != 0:
                s2, s3 = qd_quick_two_sum(s2, c4)
            else:
                s1, s2 = qd_quick_two_sum(s1, c4)
    else:
        s0, s1 = qd_quick_two_sum(s0, c2)
        if s1[0] != 0:
            s1, s2 = qd_quick_two_sum(s1, c3)
            if s2[0] != 0:
                s2, s3 = qd_quick_two_sum(s2, c4)
            else:
                s1, s2 = qd_quick_two_sum(s1, c4)
        else:
            s0, s1 = qd_quick_two_sum(s0, c3)
            if s1[0] != 0:
                s1, s2 = qd_quick_two_sum(s1, c4)
            else:
                s0, s1 = qd_quick_two_sum(s0, c4)
    return [s0, s1, s2, s3]


def _with_renorm5(fn, a, b):
    global qd_renorm5
    saved = qd_renorm5
    qd_renorm5 = gqd_renorm5
    try:
        return fn(a, b)
    finally:
        qd_renorm5 = saved


def gqd_add(a, b):  # gqd_basic.cu:168-220 (operator+ is sloppy_add); identical to QD's sloppy_add but for renorm
    return _with_renorm5(qd_sloppy_add, a, b)


def gqd_add_d(a, b):  # gqd_basic.cu:144-157
    return _with_renorm5(qd_add_d, a, b)


def gqd_mul_d(a, b):  # gqd_basic.cu:252-275
    return _with_renorm5(qd_mul_d, a, b)


def gqd_mul(a, b):  # gqd_basic.cu:284-332 (operator* is sloppy_mul)
    return _with_renorm5(qd_sloppy_mul, a, b)


def qd_ieee_add_fixed(a, b):
    """BL-highprecision/QD @ 92d99c8 (2026-10-23), include/qd/qd_inline.h:286-345: ieee_add with the k == 3
    remainder renormalized as five terms. Every other line is as in 2.3.24."""
    i = j = k = 0
    x = [Z, Z, Z, Z]
    if fabs_gt(a[i], b[j]):
        u = a[i]; i += 1
    else:
        u = b[j]; j += 1
    if fabs_gt(a[i], b[j]):
        v = a[i]; i += 1
    else:
        v = b[j]; j += 1
    u, v = qd_quick_two_sum(u, v)
    while k < 4:
        if i >= 4 and j >= 4:
            x[k] = u
            if k < 3:
                k += 1
                x[k] = v
            else:
                return qd_renorm5(x[0], x[1], x[2], x[3], v)
            break
        if i >= 4:
            t = b[j]; j += 1
        elif j >= 4:
            t = a[i]; i += 1
        elif fabs_gt(a[i], b[j]):
            t = a[i]; i += 1
        else:
            t = b[j]; j += 1
        s, u, v = qd_quick_three_accum(u, v, t)
        if s[0] != 0:
            x[k] = s
            k += 1
    for kk in range(i, 4):
        x[3] = add(x[3], a[kk])
    for kk in range(j, 4):
        x[3] = add(x[3], b[kk])
    return qd_renorm4(*x)


def qd_ieee_add_fix2(a, b):
    """A candidate complete repair (ours, not shipped): ieee_add's merge and double-length accumulation unchanged,
    but at loop exit every word still held (the accumulator's u and v, and any unconsumed input) joins the emitted
    parts in one renormalization with TwoSum in both passes (paper/fpemu.py renorm, mode 'two'), which is exact
    for terms in any order up to its last step."""
    i = j = k = 0
    x = []
    if fabs_gt(a[i], b[j]):
        u = a[i]; i += 1
    else:
        u = b[j]; j += 1
    if fabs_gt(a[i], b[j]):
        v = a[i]; i += 1
    else:
        v = b[j]; j += 1
    u, v = qd_quick_two_sum(u, v)
    while len(x) < 4 and (i < 4 or j < 4):
        if i >= 4:
            t = b[j]; j += 1
        elif j >= 4:
            t = a[i]; i += 1
        elif fabs_gt(a[i], b[j]):
            t = a[i]; i += 1
        else:
            t = b[j]; j += 1
        s, u, v = qd_quick_three_accum(u, v, t)
        if s[0] != 0:
            x.append(s)
    terms = x + [u, v] + list(a[i:]) + list(b[j:])
    return F.renorm(terms, 4, 'two')


# ------------------------------------------------------------------------------------------------------------
# libQD3 1.6.0 (github.com/nakatamaho/libQD3 @ 93ee743), include/qd/qd_inline.h: the branch-free quad-double add
# and mul selected by QD_BF (MPLAPACK builds libQD3 with -DQD_ENABLE_BF=ON). They transcribe Kouya's Algorithms 13
# and 14 (arXiv:2603.14926v2), which transcribe Zhang and Aiken's networks.
# ------------------------------------------------------------------------------------------------------------

def l3_bf_add(a, b):  # qd_inline.h:415-450
    TS, QTS = qd_two_sum, qd_quick_two_sum
    a1, b1 = TS(a[0], b[0]); c1, d1 = TS(a[1], b[1]); e1, f1 = TS(a[2], b[2]); g1, h1 = TS(a[3], b[3])
    a2, c2 = QTS(a1, c1); b2 = add(b1, h1); d2, e2 = TS(d1, e1); f2, g2 = TS(f1, g1)
    b3, g3 = TS(b2, g2); c3, d3 = QTS(c2, d2); e3, f3 = TS(e2, f2)
    a4, c4 = QTS(a2, c3); d4, e4 = QTS(d3, e3)
    b5, d5 = TS(b3, d4); e5 = add(e4, f3)
    b6, c6 = TS(b5, c4); d6, e6 = TS(d5, e5)
    a7, b7 = QTS(a4, b6); c7, d7 = QTS(c6, d6)
    e8 = add(e6, g3); b8, c8 = QTS(b7, c7)
    d9 = add(d7, e8); c0, b10 = QTS(a7, b8)
    c10, d10 = QTS(c8, d9); c1o, c11 = QTS(b10, c10)
    c2o, c3o = QTS(c11, d10)
    return [c0, c1o, c2o, c3o]


def l3_bf_mul(a, b):  # qd_inline.h:710-756
    TS, QTS, TP = qd_two_sum, qd_quick_two_sum, qd_two_prod
    a0, b0 = TP(a[0], b[0]); c0, e0 = TP(a[0], b[1]); d0, f0 = TP(a[1], b[0])
    g0, j0 = TP(a[0], b[2]); h0, k0 = TP(a[1], b[1]); i0, l0 = TP(a[2], b[0])
    m0 = mul(a[0], b[3]); n0 = mul(a[1], b[2]); o0 = mul(a[2], b[1]); p0 = mul(a[3], b[0])
    c1, d1 = TS(c0, d0); e1, f1 = TS(e0, f0); g1, i1 = TS(g0, i0)
    j1 = add(j0, l0); m1 = add(m0, p0); n1 = add(n0, o0)
    b2, c2 = TS(b0, c1); e2, h2 = TS(e1, h0); f2 = add(f1, j1); i2 = add(i1, k0); m2 = add(m1, n1)
    a3, b3 = QTS(a0, b2); c3, d3 = QTS(c2, d1); e3, g3 = TS(e2, g1)
    f3 = add(f2, m2); h3 = add(h2, i2)
    c4, e4 = TS(c3, e3); d4 = add(d3, h3); f4 = add(f3, g3)
    d5 = add(d4, e4)
    c6, d6 = TS(c4, d5)
    b7, c7 = TS(b3, c6)
    d7 = add(d6, f4)
    c0o, b8 = QTS(a3, b7)
    c8, d8 = TS(c7, d7)
    c1o, c9 = TS(b8, c8)
    c2o, c3o = QTS(c9, d8)
    return [c0o, c1o, c2o, c3o]


# ------------------------------------------------------------------------------------------------------------
# Triple-double td_real, BL-highprecision/QD @ 92d99c8, include/qd/td_inline.h (the same code is in libQD3 1.6.0)
# ------------------------------------------------------------------------------------------------------------

def td_renorm4(c0, c1, c2, c3):  # td_inline.h:69-101, four terms to three parts
    s2 = Z
    s0, c3 = qd_quick_two_sum(c2, c3)
    s0, c2 = qd_quick_two_sum(c1, s0)
    c0, c1 = qd_quick_two_sum(c0, s0)
    s0, s1 = c0, c1
    if s1[0] != 0:
        s1, s2 = qd_quick_two_sum(s1, c2)
        if s2[0] != 0:
            s2 = add(s2, c3)
        else:
            s1, s2 = qd_quick_two_sum(s1, c3)
    else:
        s0, s1 = qd_quick_two_sum(s0, c2)
        if s1[0] != 0:
            s1, s2 = qd_quick_two_sum(s1, c3)
        else:
            s0, s1 = qd_quick_two_sum(s0, c3)
    return [s0, s1, s2]


def td_ieee_add(a, b):  # td_inline.h:271-312
    i = j = k = 0
    x = [Z, Z, Z, Z]
    if fabs_gt(a[i], b[j]):
        u = a[i]; i += 1
    else:
        u = b[j]; j += 1
    if i >= 3:
        v = b[j]; j += 1
    elif j >= 3:
        v = a[i]; i += 1
    elif fabs_gt(a[i], b[j]):
        v = a[i]; i += 1
    else:
        v = b[j]; j += 1
    u, v = qd_quick_two_sum(u, v)
    while k < 3:
        if i >= 3 and j >= 3:
            x[k] = u
            if k < 2:
                k += 1
                x[k] = v
            else:
                x[3] = add(x[3], v)
            break
        if i >= 3:
            t = b[j]; j += 1
        elif j >= 3:
            t = a[i]; i += 1
        elif fabs_gt(a[i], b[j]):
            t = a[i]; i += 1
        else:
            t = b[j]; j += 1
        s, u, v = qd_quick_three_accum(u, v, t)
        if s[0] != 0:
            x[k] = s
            k += 1
    for kk in range(i, 3):
        x[3] = add(x[3], a[kk])
    for kk in range(j, 3):
        x[3] = add(x[3], b[kk])
    return td_renorm4(*x)


def td_sloppy_add(a, b):  # td_inline.h:252-266
    s0, t0 = qd_two_sum(a[0], b[0])
    s1, t1 = qd_two_sum(a[1], b[1])
    s2, t2 = qd_two_sum(a[2], b[2])
    s1, t0 = qd_two_sum(s1, t0)
    s2 = add(s2, add(t0, t1))
    t0 = t2
    return td_renorm4(s0, s1, s2, t0)
