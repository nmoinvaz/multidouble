// ldf_defects.cpp -- defects of LIB-Dekker-Float's C++ API for Float64x2 (Float64x2.hpp)
//
//   build: clang++ -std=c++20 -O1 -I LDF_SRC ldf_defects.cpp

#include <cstdio>

#include "Float64x2/Float64x2.h"

int main() {
    // 5. LDF::mul_pwr2<Float64x2, fp64, Float64x2> returns {x * y.hi, x * y.hi}: the low part is the high part.
    // 2 * (1 + 2^-60) gives 4.
    Float64x2 y = {1.0, 0x1p-60};
    Float64x2 r = LDF::mul_pwr2<Float64x2, fp64, Float64x2>(2.0, y);
    std::printf("mul_pwr2(2, 1 + 2^-60) = %a + %a\n", r.hi, r.lo);

    // 6. operator==(fp64, Float64x2) compares x with y.lo: 1.0 == Float64x2(1.0) is false, Float64x2(1.0) == 1.0 true
    Float64x2 one = {1.0, 0.0};
    std::printf("1.0 == one: %d, one == 1.0: %d\n", 1.0 == one, one == 1.0);

    // 7. bitwise_and/andnot/or/xor<Float64x2, fp64> compute into ret and return x unchanged
    Float64x2 m = LDF::bitwise_and<Float64x2, fp64>(Float64x2{1.5, 0x1p-60}, 0.0);
    std::printf("bitwise_and({1.5, 2^-60}, 0.0) = %a %a\n", m.hi, m.lo);
    return 0;
}
