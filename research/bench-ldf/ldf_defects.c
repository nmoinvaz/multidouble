// ldf_defects.c -- inputs that show defects of LIB-Dekker-Float's C API (the C++ ones are in ldf_defects.cpp).
// Prints the parts of each result in hex; ldf_defects.py checks them against exact rational arithmetic.
//
//   build: clang -std=c11 -O3 -mcpu=native -ffp-contract=on -I LDF_SRC ldf_defects.c            (default mode)
//          clang ... -DFLOAT64X4_IEEE_MODE ldf_defects.c                                        (IEEE mode)

#include <math.h>
#include <stdio.h>

#include "Float64x4/Float64x4.h"

static void p4(const char* tag, Float64x4 r) {
    printf("%s %a %a %a %a\n", tag, r.val[0], r.val[1], r.val[2], r.val[3]);
}

int main(void) {
#ifndef FLOAT64X4_IEEE_MODE
    // 1. Float64_isnan tests "exponent not all ones" (the opposite), so finite numbers are NaN and NaN is not
    Float64x2 one_half = {1.5, 0.0}, nan2 = {NAN, 0.0};
    printf("isnan(1.5) %d isnan(NaN) %d\n", Float64x2_isnan(one_half), Float64x2_isnan(nan2));

    // 2. the double-double add (Dekker's, without the second two-sum): when the hi parts cancel, the lo parts are
    // summed in one rounding, so the result keeps 53 bits. a = 1 + (2^-54 + 2^-106), b = -1 + 3 2^-108.
    Float64x2 a = {1.0, 0x1p-54 + 0x1p-106}, b = {-1.0, 3 * 0x1p-108};
    Float64x2 s = Float64x2_add(a, b);
    printf("dd_add %a %a\n", s.hi, s.lo);

    // 3. Float64x4_add_accurate (QD's ieee_add) keeps QD's loss of a term after cancellation: the worst input of
    // the cancelling set (index 3358)
    Float64x4 x = {{-0x1.2069d768735c3p-8, -0x1.e6fe6600c0040p-63, -0x1.48b21f064d551p-117, 0x1.9a6511e87ea76p-171}};
    Float64x4 y = {{0x1.20f8a227c3e64p-8, 0x1.a4becffadf20ap-65, -0x1.faa58966080b5p-119, 0x1.fec036f4d4027p-173}};
    p4("qd_add_accurate", Float64x4_add_accurate(x, y));
#else
    // 4. FLOAT64X4_IEEE_MODE: Float64x4_accurate_renorm adds val[2] twice and never val[3] (its second step reads
    // val[2] where QD reads val[3], and its index test `err_hi != 0.0` is always true). It never writes s[3], nor
    // s[2] when s[1] is zero, so those parts of the result are uninitialized. Every IEEE-mode add, sub, div and
    // sqrt goes through it.
    // the input of the random set (index 1125) with the largest IEEE-mode add error
    Float64x4 u = {{-0x1.e7c3a633d8879p+0, -0x1.90080fd14ebd0p-54, -0x1.f4a4906597005p-113, 0x1.89cf65a8383b5p-167}};
    Float64x4 v = {{-0x1.ed387f10e504bp+2, 0x1.55fae5265b70ep-52, 0x1.4f62e25e56f0ap-106, -0x1.f5b32cc80ae9bp-163}};
    p4("ieee_mode_add", Float64x4_add(u, v));
#endif
    return 0;
}
