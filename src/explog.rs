//! The exponential and the natural logarithm of the double-double, quad-double and octo-double types (`exp`, `ln`,
//! with `f64`'s names and special values), written once over each precision's operations (`Prec`).
//!
//! * exp: x = k ln 2 + r with k = round(x_0 / ln 2) and |r| <= ln 2 / 2 + 2^-41, in the manner of W. J. Cody and
//!   W. Waite (Software Manual for the Elementary Functions, Prentice-Hall, 1980): ln 2 = `LN2_HI` + `LN2_LO`, with
//!   `LN2_HI` of 42 bits, so that k `LN2_HI` and x_0 - k `LN2_HI` are exact for |k| < 2^11, and r is that difference
//!   with x's lower parts, plus `LN2_LO` times -k, in one addition of the precision. Then r is scaled by 2^-m, m the
//!   least count that brings a bound of |r| below 2^-S; t ~ e^(r 2^-m) - 1 is the Taylor polynomial, by Horner's rule,
//!   as r' + r' (r' q), of degree `DEG` or, for a small r', of the least degree whose remainder is below 2^-B |r'|, so
//!   that no negligible term is formed; m steps t <- 2t + t^2 take t to e^r - 1, an error that grows by one rounding
//!   per step where squaring 1 + t would double it (the form of `exp` in the QD library of Y. Hida, X. S. Li and
//!   D. H. Bailey, version 2.3.7, src/dd_real.cpp and src/qd_real.cpp); and the result is (1 + t) 2^k, scaled exactly
//!   in two steps while its parts stay normal.
//! * ln: one Newton step on exp from y0, the double-double logarithm (for the double-double, `ln_f64` of the leading
//!   part, this module's own binary64 logarithm with a proven error, plus lo / hi; for a leading part at least 2^1023,
//!   that of x/2 plus ln 2, as x's double-double can round past f64::MAX there): with (k, t) the reduction of
//!   exp(-y0) above, x 2^k is exact and f = x 2^k - 1 is exact (its leading part lies in [1/2, 2], Sterbenz), so
//!   c = x e^(-y0) - 1 = (f + t) + f t keeps its relative accuracy near x = 1, and y = y0 + log(1 + c) with log(1 + c)
//!   = c (1 + c h(c)) to order `Q` (the QD library's own log takes y0 + c, the plain Newton step on exp, from f64's
//!   logarithm). `QD::ln` runs these steps with QD's operations, from the same start (`start_dd`) and with Q = 2, so
//!   its correction is c (1 - c/2).
//!
//! A product of a small factor is formed from the factor scaled by a power of two to below 2, from a bound of its
//! whole value (`bound_expo`), and scaled back after, so that no product's parts leave the normal range because the
//! argument is small; the scalings are exact while the parts stay normal, and each part that falls below 2^-1022 loses
//! at most 2^-1075.
//!
//! Error bounds (u = 2^-53): `OD::exp` errs by at most 3.661 u^8 e^x + 8 2^-1074 for a finite result, e^x below
//! f64::MAX + ulp/2 (an overflowing one is +inf, outside the bounds), and `OD::ln` by 9.926 u^8 |ln x| + 2^-509, for
//! inputs on the ladder |x_i| <= (2u)^i |x_0| whose run leaves no product, fused multiply-add or quotient below the
//! normal range (the paper's (A2), apart from the scalings above, whose losses the bounds include, and the products
//! that only choose k, m, the degree or a branch of ln), proved in the paper (paper/expansion-error-bounds.pdf, its
//! appendix on exp and log) from Lemma 20 at every operation; `DD::exp` errs by at most 5.465 u^2 e^x + 2 2^-1074 for a
//! finite result, and `DD::ln` by 15.351 u^2 |ln x| + 2^-1071, for double-words under the same condition, from the
//! published bounds of the double-word operations they use and the proven bound of `ln_f64`. An emulator of these steps
//! with every product hooked finds none below the normal range at any binade of the argument, the closest 48 binades
//! above it (the paper's appendix on exp and log), so the argument's size does not break the condition there; a part
//! far below the one above it can make a product underflow, as for the other operations. The constants come from
//! `paper/explog_consts.py`. The quad-double functions use QD's own operations, which have no proven bounds, and are
//! tested to: exp within 64 u^4 e^x + 4 2^-1074 for a finite result (the absolute term, as above, from the parts that
//! fall below 2^-1022), ln to 64 u^4 |ln x|.
//!
//! Range: exp gives +inf for x_0 > 709.79 and +0 for x_0 < -745.2, and computes in between, where an overflowing
//! result is +inf and an underflowing one loses its lower parts to the subnormals as the other operations do. ln
//! gives NaN for a negative or NaN leading part, -inf for a zero one and +inf for +inf, and works on every positive
//! finite value, subnormal leading parts included.
use crate::dd::{quick_two_sum, two_prod, two_sum, DD};
use crate::od::OD;
use crate::qd::QD;

/// Deliberate breakage for the controls (feature `mutate`; ids below, 0 = none).
pub mod mutate {
    /// exp's reduction: ln 2's tail `LN2_LO` cut to its first part, an error of about |k| 2^-102 in r
    pub const RED_TAIL: u32 = 1;
    /// exp: the Taylor polynomial cut to half its degree
    pub const TAYLOR_HALF: u32 = 2;
    /// ln: the Newton step skipped, the start returned
    pub const LN_STEP: u32 = 3;
    /// ln: the double-double start (`ln_f64`) off by 2^-20 relative, past the error its proof allows
    pub const LN_START: u32 = 4;
    /// ln: log(1 + c) cut to c, an error of about c^2 / 2, below `OD::ln`'s absolute term near x = 1
    pub const LN_SERIES: u32 = 5;
    /// number of ids
    pub const N: u32 = 5;
    /// the mutations' descriptions, by id
    pub const NAMES: [&str; 6] = [
        "none",
        "exp: ln 2's tail cut to one part",
        "exp: Taylor polynomial at half its degree",
        "ln: Newton step skipped",
        "ln: start off by 2^-20",
        "ln: log(1 + c) cut to c",
    ];

    #[cfg(feature = "mutate")]
    thread_local!(static ID: std::cell::Cell<u32> = const { std::cell::Cell::new(0) });

    /// select the mutation for the current thread (0 = none)
    #[cfg(feature = "mutate")]
    pub fn set(id: u32) {
        ID.with(|m| m.set(id));
    }

    /// whether mutation id is selected in the current thread
    #[cfg(feature = "mutate")]
    #[inline(always)]
    pub fn on(id: u32) -> bool {
        ID.with(|m| m.get() == id)
    }

    /// whether mutation id is selected: never, without the feature `mutate`
    #[cfg(not(feature = "mutate"))]
    #[inline(always)]
    pub fn on(_id: u32) -> bool {
        false
    }
}

/// exp is +inf above this leading part (e^709.79 > f64::MAX)
const EXP_MAX: f64 = 709.79;
/// exp is +0 below this leading part (e^-745.2 < 2^-1075)
const EXP_MIN: f64 = -745.2;

// generated by scripts/explog_constants.py, do not edit
/// ln 2 rounded to 42 significant bits: k LN2_HI is exact for every integer |k| < 2^11
const LN2_HI: f64 = f64::from_bits(0x3fe62e42fefa3800);
/// ln 2 - LN2_HI, greedy eight parts
const LN2_LO: [f64; 8] = [
    f64::from_bits(0x3d2ef35793c76730),
    f64::from_bits(0x398f97b57a079a19),
    f64::from_bits(0x3619ca62d8b62834),
    f64::from_bits(0x32b75b8baafa2be8),
    f64::from_bits(0xaf51e277e48514da),
    f64::from_bits(0x2bd56554bed2be87),
    f64::from_bits(0xa86de25a2a3947d9),
    f64::from_bits(0x24c0a213ab9d9489),
];
/// ln 2, greedy two parts
const LN2_DD: [f64; 2] = [f64::from_bits(0x3fe62e42fefa39ef), f64::from_bits(0x3c7abc9e3b39803f)];
/// 1/j! for j = 0..=43, greedy eight parts
const INV_FACT: [[f64; 8]; 44] = [
    [
        f64::from_bits(0x3ff0000000000000),
        f64::from_bits(0x0000000000000000),
        f64::from_bits(0x0000000000000000),
        f64::from_bits(0x0000000000000000),
        f64::from_bits(0x0000000000000000),
        f64::from_bits(0x0000000000000000),
        f64::from_bits(0x0000000000000000),
        f64::from_bits(0x0000000000000000),
    ],
    [
        f64::from_bits(0x3ff0000000000000),
        f64::from_bits(0x0000000000000000),
        f64::from_bits(0x0000000000000000),
        f64::from_bits(0x0000000000000000),
        f64::from_bits(0x0000000000000000),
        f64::from_bits(0x0000000000000000),
        f64::from_bits(0x0000000000000000),
        f64::from_bits(0x0000000000000000),
    ],
    [
        f64::from_bits(0x3fe0000000000000),
        f64::from_bits(0x0000000000000000),
        f64::from_bits(0x0000000000000000),
        f64::from_bits(0x0000000000000000),
        f64::from_bits(0x0000000000000000),
        f64::from_bits(0x0000000000000000),
        f64::from_bits(0x0000000000000000),
        f64::from_bits(0x0000000000000000),
    ],
    [
        f64::from_bits(0x3fc5555555555555),
        f64::from_bits(0x3c65555555555555),
        f64::from_bits(0x3905555555555555),
        f64::from_bits(0x35a5555555555555),
        f64::from_bits(0x3245555555555555),
        f64::from_bits(0x2ee5555555555555),
        f64::from_bits(0x2b85555555555555),
        f64::from_bits(0x2825555555555555),
    ],
    [
        f64::from_bits(0x3fa5555555555555),
        f64::from_bits(0x3c45555555555555),
        f64::from_bits(0x38e5555555555555),
        f64::from_bits(0x3585555555555555),
        f64::from_bits(0x3225555555555555),
        f64::from_bits(0x2ec5555555555555),
        f64::from_bits(0x2b65555555555555),
        f64::from_bits(0x2805555555555555),
    ],
    [
        f64::from_bits(0x3f81111111111111),
        f64::from_bits(0x3c01111111111111),
        f64::from_bits(0x3881111111111111),
        f64::from_bits(0x3501111111111111),
        f64::from_bits(0x3181111111111111),
        f64::from_bits(0x2e01111111111111),
        f64::from_bits(0x2a81111111111111),
        f64::from_bits(0x2701111111111111),
    ],
    [
        f64::from_bits(0x3f56c16c16c16c17),
        f64::from_bits(0xbbef49f49f49f49f),
        f64::from_bits(0xb8827d27d27d27d2),
        f64::from_bits(0xb52f49f49f49f49f),
        f64::from_bits(0xb1c27d27d27d27d2),
        f64::from_bits(0xae6f49f49f49f49f),
        f64::from_bits(0xab027d27d27d27d2),
        f64::from_bits(0xa7af49f49f49f49f),
    ],
    [
        f64::from_bits(0x3f2a01a01a01a01a),
        f64::from_bits(0x3b6a01a01a01a01a),
        f64::from_bits(0x37aa01a01a01a01a),
        f64::from_bits(0x33ea01a01a01a01a),
        f64::from_bits(0x302a01a01a01a01a),
        f64::from_bits(0x2c6a01a01a01a01a),
        f64::from_bits(0x28aa01a01a01a01a),
        f64::from_bits(0x24ea01a01a01a01a),
    ],
    [
        f64::from_bits(0x3efa01a01a01a01a),
        f64::from_bits(0x3b3a01a01a01a01a),
        f64::from_bits(0x377a01a01a01a01a),
        f64::from_bits(0x33ba01a01a01a01a),
        f64::from_bits(0x2ffa01a01a01a01a),
        f64::from_bits(0x2c3a01a01a01a01a),
        f64::from_bits(0x287a01a01a01a01a),
        f64::from_bits(0x24ba01a01a01a01a),
    ],
    [
        f64::from_bits(0x3ec71de3a556c734),
        f64::from_bits(0xbb6c154f8ddc6c00),
        f64::from_bits(0x38071de3a556c734),
        f64::from_bits(0xb4ac154f8ddc6c00),
        f64::from_bits(0x31471de3a556c734),
        f64::from_bits(0xadec154f8ddc6c00),
        f64::from_bits(0x2a871de3a556c734),
        f64::from_bits(0xa72c154f8ddc6c00),
    ],
    [
        f64::from_bits(0x3e927e4fb7789f5c),
        f64::from_bits(0x3b3cbbc05b4fa99a),
        f64::from_bits(0xb7bc6d278883e8f5),
        f64::from_bits(0x34595567d3a50cce),
        f64::from_bits(0xb0c69c6f77527ad8),
        f64::from_bits(0xad310c717d2332e9),
        f64::from_bits(0xa9ccfa2aa85ae0b4),
        f64::from_bits(0x26611a5038eccd61),
    ],
    [
        f64::from_bits(0x3e5ae64567f544e4),
        f64::from_bits(0xbafc062e06d1f209),
        f64::from_bits(0x377c7880adcbc46e),
        f64::from_bits(0xb415553a6f0fed60),
        f64::from_bits(0xb09071c56e0d709d),
        f64::from_bits(0xad1d78e373529e26),
        f64::from_bits(0xa9b0e7aaaa3f1195),
        f64::from_bits(0xa625ab2e38d61b16),
    ],
    [
        f64::from_bits(0x3e21eed8eff8d898),
        f64::from_bits(0xbac2aec959e14c06),
        f64::from_bits(0x3742fb0073dd2d9e),
        f64::from_bits(0x33ec71d90b4ab715),
        f64::from_bits(0x308297b46da86d3b),
        f64::from_bits(0x2d12e097b663c827),
        f64::from_bits(0x29be975c71d013de),
        f64::from_bits(0x264f8c6f097b8a1a),
    ],
    [
        f64::from_bits(0x3de6124613a86d09),
        f64::from_bits(0x3a8f28e0cc748ebe),
        f64::from_bits(0xb727b2c4c8a840bc),
        f64::from_bits(0x33cc71cca1034c07),
        f64::from_bits(0xb06cbda1195605c6),
        f64::from_bits(0xad0aa25ed03f6b0e),
        f64::from_bits(0x29a8660e38e4ef5d),
        f64::from_bits(0x2641322fed0980c7),
    ],
    [
        f64::from_bits(0x3da93974a8c07c9d),
        f64::from_bits(0x3a305d6f8a2efd1f),
        f64::from_bits(0x36c3aa3346236a5d),
        f64::from_bits(0x336d75f096ea801e),
        f64::from_bits(0xafdb17039e931c58),
        f64::from_bits(0xac77321dbfeab8cd),
        f64::from_bits(0xa91f228a2870173f),
        f64::from_bits(0xa5b4424bda122cb9),
    ],
    [
        f64::from_bits(0x3d6ae7f3e733b81f),
        f64::from_bits(0x39e1d8656b0ee8cb),
        f64::from_bits(0xb626e142a138f825),
        f64::from_bits(0x32b43c0c38ccdcc6),
        f64::from_bits(0xaf5b225fe7ac8e6d),
        f64::from_bits(0x2bfa868cce37f24d),
        f64::from_bits(0x285f6ca1aa91de98),
        f64::from_bits(0x24ffaf1764148fe6),
    ],
    [
        f64::from_bits(0x3d2ae7f3e733b81f),
        f64::from_bits(0x39a1d8656b0ee8cb),
        f64::from_bits(0xb5e6e142a138f825),
        f64::from_bits(0x32743c0c38ccdcc6),
        f64::from_bits(0xaf1b225fe7ac8e6d),
        f64::from_bits(0x2bba868cce37f24d),
        f64::from_bits(0x281f6ca1aa91de98),
        f64::from_bits(0x24bfaf1764148fe6),
    ],
    [
        f64::from_bits(0x3ce952c77030ad4a),
        f64::from_bits(0x398ac981465ddc6c),
        f64::from_bits(0xb5a588b72e53bc5f),
        f64::from_bits(0x3227079e8909271a),
        f64::from_bits(0xaecc7cf0c326b1bd),
        f64::from_bits(0xab6599514ea5bf6f),
        f64::from_bits(0xa7815664674f395b),
        f64::from_bits(0x242fe4a25cc5a297),
    ],
    [
        f64::from_bits(0x3ca6827863b97d97),
        f64::from_bits(0x394eec01221a8b0b),
        f64::from_bits(0xb5e568798662118b),
        f64::from_bits(0x321f00d8b9e49291),
        f64::from_bits(0x2e8f90f119a4b758),
        f64::from_bits(0xab2332f2f09354d4),
        f64::from_bits(0xa7cc8130593f62de),
        f64::from_bits(0x24668e20905276c9),
    ],
    [
        f64::from_bits(0x3c62f49b46814157),
        f64::from_bits(0x38f2650f61dbdcb4),
        f64::from_bits(0xb5969502917cbf3b),
        f64::from_bits(0x320e35fbddac4553),
        f64::from_bits(0xaea729e1e158c7b1),
        f64::from_bits(0xab47d4e1832a5c10),
        f64::from_bits(0xa7e137983711ad17),
        f64::from_bits(0xa4703fa0d3c7ef66),
    ],
    [
        f64::from_bits(0x3c1e542ba4020225),
        f64::from_bits(0x387ea72b4afe3c2f),
        f64::from_bits(0xb5144020dfd65c8c),
        f64::from_bits(0xb186e69b50fc88ab),
        f64::from_bits(0xadf0c0c089e97a26),
        f64::from_bits(0xaa80b468eeb00d04),
        f64::from_bits(0x270ae5b62dd61c65),
        f64::from_bits(0xa398690c19647b2a),
    ],
    [
        f64::from_bits(0x3bd71b8ef6dcf572),
        f64::from_bits(0xb87d043ae40c4647),
        f64::from_bits(0x34f486121e81d5fe),
        f64::from_bits(0xb192d4ba8e1e64c7),
        f64::from_bits(0xae1eacf61a05d3bd),
        f64::from_bits(0xaaba0112e90a30d7),
        f64::from_bits(0x273ea2e421cbf0ee),
        f64::from_bits(0x23d41e29de668edf),
    ],
    [
        f64::from_bits(0x3b90ce396db7f853),
        f64::from_bits(0xb83aebcdbd20331c),
        f64::from_bits(0xb4d38a88578b4d75),
        f64::from_bits(0x316c0fbc29694fb8),
        f64::from_bits(0xae0a0fb9482f1340),
        f64::from_bits(0x2a9e2e59a7156b7c),
        f64::from_bits(0xa7247cd3fced75bc),
        f64::from_bits(0x23baee36286fbce3),
    ],
    [
        f64::from_bits(0x3b4761b41316381a),
        f64::from_bits(0xb7d3423c7d91404f),
        f64::from_bits(0x346e6135bfc1194a),
        f64::from_bits(0xb10ba7b1a3077b39),
        f64::from_bits(0x2d9b7bf8dd95d7a8),
        f64::from_bits(0x2a31330fbaaae84d),
        f64::from_bits(0x26ddee26f924ece4),
        f64::from_bits(0x237ddd5d53c82a5b),
    ],
    [
        f64::from_bits(0x3aff2cf01972f578),
        f64::from_bits(0xb789ada5fcc1ab14),
        f64::from_bits(0x342440ce7fd610dc),
        f64::from_bits(0xb0c26fcbc204fcd1),
        f64::from_bits(0x2d6e7ea849dc9d38),
        f64::from_bits(0x29e6eebfa38e8b12),
        f64::from_bits(0xa65613b59e762126),
        f64::from_bits(0x22f3e3e37dac6e75),
    ],
    [
        f64::from_bits(0x3ab3f3ccdd165fa9),
        f64::from_bits(0xb7458ddadf344487),
        f64::from_bits(0xb3ee8ed8001ad67e),
        f64::from_bits(0x30880a5edffcced7),
        f64::from_bits(0xad22e223a7c4ba1a),
        f64::from_bits(0x29cd44eb76543f36),
        f64::from_bits(0x2642b6be453e3aca),
        f64::from_bits(0xa2db899e29550d0c),
    ],
    [
        f64::from_bits(0x3a688e85fc6a4e5a),
        f64::from_bits(0xb7071c37ebd16540),
        f64::from_bits(0x33a494676265a364),
        f64::from_bits(0xb02397b40007db79),
        f64::from_bits(0xacc5dde19cf7f17a),
        f64::from_bits(0x2938fe6b9053a1b3),
        f64::from_bits(0xa5d519e12143cae4),
        f64::from_bits(0x227ead3f9a42560a),
    ],
    [
        f64::from_bits(0x3a1d1ab1c2dccea3),
        f64::from_bits(0x36a054d0c78aea14),
        f64::from_bits(0xb34196bf16c33a56),
        f64::from_bits(0x2fef0e65ed04d346),
        f64::from_bits(0x2c843a24f850a04f),
        f64::from_bits(0x292beceb85f33b63),
        f64::from_bits(0xa5cba31a2863d624),
        f64::from_bits(0x225781f675ab0344),
    ],
    [
        f64::from_bits(0x39d0a18a2635085d),
        f64::from_bits(0x366b9e2e28e1aa54),
        f64::from_bits(0x330a8549a9d99586),
        f64::from_bits(0xaf5141dcc8cc5668),
        f64::from_bits(0x2bd09cd93b9b8469),
        f64::from_bits(0x284d880d99ac4f03),
        f64::from_bits(0x24e4567f1bcd64fe),
        f64::from_bits(0xa1800ae73c8e8deb),
    ],
    [
        f64::from_bits(0x398259f98b4358ad),
        f64::from_bits(0x362eaf8c39dd9bc5),
        f64::from_bits(0xb2c6e29990a26fb6),
        f64::from_bits(0xaf42d867809b5568),
        f64::from_bits(0xabe15e662f862571),
        f64::from_bits(0x285afdee944e015d),
        f64::from_bits(0xa4f033796509b339),
        f64::from_bits(0xa19ac265171cf0cb),
    ],
    [
        f64::from_bits(0x3933932c5047d60e),
        f64::from_bits(0x35d832b7b530a627),
        f64::from_bits(0x3255d2c61f6d124c),
        f64::from_bits(0x2eff192b328d82c4),
        f64::from_bits(0xab575c254d35b232),
        f64::from_bits(0xa7f3379ca17bb8d4),
        f64::from_bits(0x2490a3414a95f91f),
        f64::from_bits(0x211ba74c079192d8),
    ],
    [
        f64::from_bits(0x38e434d2e783f5bc),
        f64::from_bits(0x3580b87b91be9aff),
        f64::from_bits(0x31fc89db1796db75),
        f64::from_bits(0xae98923b7699c8be),
        f64::from_bits(0x2af1d668aaebfb77),
        f64::from_bits(0x277f3d030c866cc8),
        f64::from_bits(0x2415c84cba83e83b),
        f64::from_bits(0xa0b34bc621ec3c31),
    ],
    [
        f64::from_bits(0x389434d2e783f5bc),
        f64::from_bits(0x3530b87b91be9aff),
        f64::from_bits(0x31ac89db1796db75),
        f64::from_bits(0xae48923b7699c8be),
        f64::from_bits(0x2aa1d668aaebfb77),
        f64::from_bits(0x272f3d030c866cc8),
        f64::from_bits(0x23c5c84cba83e83b),
        f64::from_bits(0xa0634bc621ec3c31),
    ],
    [
        f64::from_bits(0x3843981254dd0d52),
        f64::from_bits(0xb4e2b1f4c8015a2f),
        f64::from_bits(0xb18d82af23edb6db),
        f64::from_bits(0x2e2a1cd20123a99b),
        f64::from_bits(0x2ac958e5a4343645),
        f64::from_bits(0xa75c00bd1450f203),
        f64::from_bits(0xa3deb344a7d736aa),
        f64::from_bits(0x206c819525c289d0),
    ],
    [
        f64::from_bits(0x37f2710231c0fd7a),
        f64::from_bits(0x3473f8a2b4af9d6b),
        f64::from_bits(0x311c32215a9f317e),
        f64::from_bits(0xadad451e158a1205),
        f64::from_bits(0x2a4cf7b201892024),
        f64::from_bits(0xa6363ea01c78d66f),
        f64::from_bits(0xa2dc5f4a18322b80),
        f64::from_bits(0x1f57d50b7184b411),
    ],
    [
        f64::from_bits(0x37a0dc59c716d91f),
        f64::from_bits(0x343419e3fad3f031),
        f64::from_bits(0x30bd9d7ed1981ffc),
        f64::from_bits(0xad3345ea5d66a84b),
        f64::from_bits(0xa9c285e2b2f07400),
        f64::from_bits(0xa5e45683c242982b),
        f64::from_bits(0xa2881c9b83d61924),
        f64::from_bits(0x9f2f1fc2debd18ac),
    ],
    [
        f64::from_bits(0x374df983290c2ca9),
        f64::from_bits(0x33d5835c6895393b),
        f64::from_bits(0xb060578f45b1aaae),
        f64::from_bits(0xad0281508688972d),
        f64::from_bits(0xa99256a427c3a800),
        f64::from_bits(0xa59214035757a3b5),
        f64::from_bits(0x222c3eeb8766efbf),
        f64::from_bits(0x1eb1562eaf26c4ba),
    ],
    [
        f64::from_bits(0x36f9ec8d1c94e85b),
        f64::from_bits(0xb36670e9d4784ec6),
        f64::from_bits(0x30079fe5954939a2),
        f64::from_bits(0x2c882e418d9b0c9e),
        f64::from_bits(0x29126a441d4e7c8a),
        f64::from_bits(0x25b81814bbf34cbb),
        f64::from_bits(0x22546b74b00666dd),
        f64::from_bits(0x1ee7d7a47b670cc6),
    ],
    [
        f64::from_bits(0x36a5d4acb9c0c3ab),
        f64::from_bits(0xb326ec2c8f5b13b2),
        f64::from_bits(0x2fce2860aaa59188),
        f64::from_bits(0xac6866eba0408569),
        f64::from_bits(0x29088c546d54f915),
        f64::from_bits(0xa59f25e2debdf7ec),
        f64::from_bits(0xa2320fa2dfff537d),
        f64::from_bits(0x1eb27e3d933e1da3),
    ],
    [
        f64::from_bits(0x3651e99449a4bace),
        f64::from_bits(0xb2dfefbb89514b3c),
        f64::from_bits(0xaf753433f743a2d9),
        f64::from_bits(0x2bf25f70d1395dd7),
        f64::from_bits(0xa89a192c8c09ef53),
        f64::from_bits(0x252334e2e34edf6f),
        f64::from_bits(0xa1c588a6f96d60c8),
        f64::from_bits(0x1e305d79ede680e5),
    ],
    [
        f64::from_bits(0x35fca8ed42a12ae3),
        f64::from_bits(0x31fa07244abad2ab),
        f64::from_bits(0x2e9facdac6fb71b7),
        f64::from_bits(0xaacca2f486d514e1),
        f64::from_bits(0x273f1ff01aaea3dc),
        f64::from_bits(0x23dbe90be5f2217e),
        f64::from_bits(0xa056515e027fe5d1),
        f64::from_bits(0x1ce4be5200b75141),
    ],
    [
        f64::from_bits(0x35a65e61c39d0241),
        f64::from_bits(0xb23c0ed181727269),
        f64::from_bits(0xaebabbd2f56bbc2f),
        f64::from_bits(0xab518ff57fdc2e4e),
        f64::from_bits(0xa7f36ae11f3e65fa),
        f64::from_bits(0xa4925ae2605f425d),
        f64::from_bits(0x2126250e608382a2),
        f64::from_bits(0x1dc72185254caee6),
    ],
    [
        f64::from_bits(0x35510af527530de8),
        f64::from_bits(0x31eb626c912ee5c8),
        f64::from_bits(0x2e8349f032c6e859),
        f64::from_bits(0xab2ec616617f45c6),
        f64::from_bits(0x27bd2c9e0c7a83d1),
        f64::from_bits(0x245a880b4900483e),
        f64::from_bits(0x20e4a06700321962),
        f64::from_bits(0x1d8b18f5c51105ad),
    ],
    [
        f64::from_bits(0x34f95db45257e512),
        f64::from_bits(0x3186e5d72b6f79b9),
        f64::from_bits(0x2dcb830cf0b5b5c6),
        f64::from_bits(0x2a629276833f5728),
        f64::from_bits(0xa70b6b869bcfa969),
        f64::from_bits(0xa3a1da2df40a5f99),
        f64::from_bits(0xa021b5f4052c22d2),
        f64::from_bits(0x1cc237ba717f229d),
    ],
];
/// 1/3, greedy eight parts
const THIRD: [f64; 8] = [
    f64::from_bits(0x3fd5555555555555),
    f64::from_bits(0x3c75555555555555),
    f64::from_bits(0x3915555555555555),
    f64::from_bits(0x35b5555555555555),
    f64::from_bits(0x3255555555555555),
    f64::from_bits(0x2ef5555555555555),
    f64::from_bits(0x2b95555555555555),
    f64::from_bits(0x2835555555555555),
];
// end of generated constants

/// LN2_LO cut to its first part (`mutate::RED_TAIL`)
const LN2_LO_CUT: [f64; 8] = [LN2_LO[0], 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];

/// One precision's operations, in the forms the error bounds are proved for.
trait Prec: Copy {
    /// m squarings bring a bound of the reduced argument below 2^-S
    const S: i32;
    /// the Taylor polynomial's largest degree: |r'|^(DEG + 1) / (DEG + 1)! below 2^-12 of the unit roundoff for |r'| <
    /// 2^-S
    const DEG: usize;
    /// the order of ln's series of log(1 + c), for the start's error
    const Q: usize;
    /// 53 n + 12 for n parts: a term below 2^-B of the result's scale is negligible, 2^-12 of the unit roundoff
    const B: i32;
    fn from_f64(x: f64) -> Self;
    /// the leading part
    fn hi(self) -> f64;
    /// |x_0| + |x_1| + ... in f64, from the leading part down
    fn abs_sum(self) -> f64;
    /// the first parts of a greedy eight-part constant
    fn konst(c: &[f64; 8]) -> Self;
    fn plus(self, b: Self) -> Self;
    fn times(self, b: Self) -> Self;
    fn plus_one(self) -> Self;
    /// times a normal power of two, exact barring underflow and overflow
    fn times_pwr2(self, b: f64) -> Self;
    fn neg(self) -> Self;
    /// self - k ln 2 for an integer k, 0 < |k| < 2^11, with ln 2 = LN2_HI + lo: (x_0 - k LN2_HI, x_1, ...), exact,
    /// plus lo times -k
    fn reduce(self, k: f64, lo: &[f64; 8]) -> Self;
    /// self - 1, exact for a leading part in [1/2, 2]
    fn sub_one(self) -> Self;
    /// ln's start
    fn ln_start(self) -> Self;
    /// ln's result from its start and the correction
    fn ln_finish(y0: Self, corr: Self) -> Self;
}

/// 2^k for -1022 <= k <= 1023
#[inline(always)]
fn pow2(k: i32) -> f64 {
    f64::from_bits(((k + 1023) as u64) << 52)
}

/// floor(log2 |h|) for a normal h, -1023 for a zero or subnormal one (the biased exponent field less 1023)
#[inline(always)]
fn expo(h: f64) -> i32 {
    ((h.to_bits() >> 52) & 0x7ff) as i32 - 1023
}

/// the exponent e of U = RN(RN(sum |v_i|) (1 + 2^-48)), 2^e <= U < 2^(e+1), -1023 for a zero or subnormal U: |v| <=
/// sum |v_i| <= U < 2^(e+1) whatever v's parts, where the leading part's exponent alone bounds nothing (a renormalized
/// expansion can be led by a part below half its value)
#[inline(always)]
fn bound_expo<T: Prec>(v: T) -> i32 {
    expo(v.abs_sum() * (1.0 + 2f64.powi(-48)))
}

/// a b for a with sum |a_i| < 2^(e+1) (`bound_expo`), -1022 <= e: formed as 2^e ((a 2^-e) b), so that the product's
/// parts are formed near b's scale and only the last power-of-two scaling, exact while the parts stay normal, can
/// leave the normal range
#[inline(always)]
fn times_scaled<T: Prec>(a: T, e: i32, b: T) -> T {
    a.times_pwr2(pow2(-e)).times(b).times_pwr2(pow2(e))
}

/// x 2^k in two exact steps, -1076 <= k <= 1076
#[inline(always)]
fn scale<T: Prec>(x: T, k: i32) -> T {
    let k1 = k / 2;
    x.times_pwr2(pow2(k1)).times_pwr2(pow2(k - k1))
}

/// (k, t) with e^x ~ 2^k (1 + t), for |x_0| <= 745.2: the reduction, the Taylor polynomial and the squarings
#[inline(always)]
fn expm1_red<T: Prec>(x: T) -> (i32, T) {
    let k = (x.hi() * std::f64::consts::LOG2_E).round();
    let r = if k == 0.0 {
        x
    } else {
        x.reduce(
            k,
            if mutate::on(mutate::RED_TAIL) {
                &LN2_LO_CUT
            } else {
                &LN2_LO
            },
        )
    };
    // m = max(0, e + S + 1) with 2^e <= RN(RN(sum |r_i|) (1 + 2^-48)) < 2^(e+1), so that |r| < 2^(e+1) and |r| 2^-m <
    // 2^-S whatever r's parts (a zero or subnormal sum gives e = -1023)
    let e = bound_expo(r);
    let m = (e + T::S + 1).max(0);
    let r = if m > 0 { r.times_pwr2(pow2(-m)) } else { r };
    // the degree d = min(DEG, ceil(B / (-er - 1))), |r'| < 2^(er+1) <= 2^-S: the terms of degree above d sum to below
    // 2^-B |r'|, and none is formed, so a small r' forms no product of negligible size (d = 1 for |r'| < 2^-B: t = r')
    let er = e - m;
    let d = if er >= -1 - T::B {
        T::DEG.min((T::B / (-er - 1) + (T::B % (-er - 1) != 0) as i32) as usize)
    } else {
        1
    };
    let d = if mutate::on(mutate::TAYLOR_HALF) {
        (d / 2).max(1)
    } else {
        d
    };
    let mut t = if d == 1 {
        r
    } else {
        // q = sum_(j=2)^d r^(j-2) / j! by Horner's rule, and t = r + r (r q), the outer product and sum in r 2^-er
        let mut q = T::konst(&INV_FACT[d]);
        for j in (2..d).rev() {
            q = T::konst(&INV_FACT[j]).plus(r.times(q));
        }
        let w = r.times(q);
        let rs = r.times_pwr2(pow2(-er));
        rs.plus(rs.times(w)).times_pwr2(pow2(er))
    };
    for _ in 0..m {
        t = t.times_pwr2(2.0).plus(t.times(t));
    }
    (k as i32, t)
}

/// e^x (see the module doc)
#[inline(always)]
fn exp_of<T: Prec>(x: T) -> T {
    let h = x.hi();
    if h.is_nan() {
        return T::from_f64(h);
    }
    if h > EXP_MAX {
        return T::from_f64(f64::INFINITY);
    }
    if h < EXP_MIN {
        return T::from_f64(0.0);
    }
    let (k, t) = expm1_red(x);
    let y = scale(t.plus_one(), k);
    if y.hi() == f64::INFINITY {
        T::from_f64(f64::INFINITY)
    } else {
        y
    }
}

/// (-1)^(i+1) / i, the coefficients of log(1 + c), 2 <= i <= 4
#[inline(always)]
fn series<T: Prec>(i: usize) -> T {
    match i {
        2 => T::from_f64(-0.5),
        3 => T::konst(&THIRD),
        _ => T::from_f64(-0.25),
    }
}

/// ln x (see the module doc)
#[inline(always)]
fn ln_of<T: Prec>(x: T) -> T {
    let h = x.hi();
    if h.is_nan() || h < 0.0 {
        return T::from_f64(f64::NAN);
    }
    if h == 0.0 {
        return T::from_f64(f64::NEG_INFINITY);
    }
    if h == f64::INFINITY {
        return T::from_f64(f64::INFINITY);
    }
    let y0 = x.ln_start();
    if mutate::on(mutate::LN_STEP) {
        return y0;
    }
    // e^-y0 ~ 2^k (1 + t); f = x 2^k - 1 exactly; c = x e^-y0 - 1 = (f + t) + f t, f t formed from f 2^-ef and t 2^-et,
    // both near 1, and dropped when |f| or |t| is below 2^-(B + 12), with ef and et the exponents of bounds of the
    // whole values (`bound_expo`), as the leading parts' do not bound them
    let (k, t) = expm1_red(y0.neg());
    let f = scale(x, k).sub_one();
    let (ef, et) = (bound_expo(f), bound_expo(t));
    let c = if ef.min(et) < -T::B - 13 {
        f.plus(t)
    } else {
        let p = f.times_pwr2(pow2(-ef)).times(t.times_pwr2(pow2(-et)));
        f.plus(t).plus(p.times_pwr2(pow2(ef)).times_pwr2(pow2(et)))
    };
    // log(1 + c) = c (1 + c h), h = -1/2 + c (1/3 - c / 4 ...) to order Q, each product with c at the other factor's
    // scale; for |c| below 2^-(B + 12), c alone
    let ec = bound_expo(c);
    let corr = if ec < -T::B - 13 || mutate::on(mutate::LN_SERIES) {
        c
    } else {
        let mut h = series::<T>(T::Q);
        for i in (2..T::Q).rev() {
            h = series::<T>(i).plus(times_scaled(c, ec, h));
        }
        times_scaled(c, ec, times_scaled(c, ec, h).plus_one())
    };
    T::ln_finish(y0, corr)
}

/// the start of the quad-double and octo-double ln: the double-double ln of x's double-double, or, for a leading part
/// x_0 >= 2^1023, where that conversion can round past f64::MAX, the double-double ln of x/2's plus ln 2 (`LN2_DD`)
#[inline(always)]
fn start_dd(x0: f64, dd: impl Fn() -> DD, half: impl Fn() -> DD) -> DD {
    if x0 >= pow2(1023) {
        half().ln()
            + DD {
                hi: LN2_DD[0],
                lo: LN2_DD[1],
            }
    } else {
        dd().ln()
    }
}

/// ln h for a positive finite h, within 5.915 u |ln h| (u = 2^-53; paper/explog_consts.py), and 0 for h = 1: h = 2^e m
/// with m in (mu/2, mu], mu = RN(sqrt 2), m - 1 exact, and ln m = 2 atanh(s), s = (m - 1) / (m + 1), |s| <= 0.1716,
/// by the first ten terms of its series in s^2 (by Horner's rule with fused multiply-adds), whose remainder is below
/// 0.22 u relative; then e ln 2 is added by one fused multiply-add. No library logarithm is called, so the start of
/// `DD::ln` has a proven error. Public for the tests only.
#[doc(hidden)]
#[inline(always)]
pub fn ln_f64(h: f64) -> f64 {
    let (h, e0) = if h < f64::MIN_POSITIVE {
        (h * pow2(54), -54)
    } else {
        (h, 0)
    };
    let mut e = expo(h) + e0;
    let mut m = f64::from_bits((h.to_bits() & 0x000f_ffff_ffff_ffff) | 0x3ff0_0000_0000_0000);
    if m > std::f64::consts::SQRT_2 {
        m *= 0.5;
        e += 1;
    }
    let s = (m - 1.0) / (m + 1.0);
    let z = s * s;
    let mut v = LN_SERIES[LN_SERIES.len() - 1];
    for &c in LN_SERIES[..LN_SERIES.len() - 1].iter().rev() {
        v = z.mul_add(v, c);
    }
    let y = (e as f64).mul_add(std::f64::consts::LN_2, (s + s) * v);
    if mutate::on(mutate::LN_START) {
        y * (1.0 + 2f64.powi(-20))
    } else {
        y
    }
}

/// 1 / (2j + 1) for j = 0..=9, rounded to nearest
const LN_SERIES: [f64; 10] = [
    1.0,
    1.0 / 3.0,
    1.0 / 5.0,
    1.0 / 7.0,
    1.0 / 9.0,
    1.0 / 11.0,
    1.0 / 13.0,
    1.0 / 15.0,
    1.0 / 17.0,
    1.0 / 19.0,
];

/// a + b for a double-word a and an f64 b: DWPlusFP, Algorithm 4 of M. Joldes, J.-M. Muller, V. Popescu, "Tight and
/// rigorous error bounds for basic building blocks of double-word arithmetic", ACM Trans. Math. Softw. 44(2), 2017,
/// doi:10.1145/3121432, within 2u^2 / (1 - 2u) relative (u = 2^-53)
#[inline(always)]
fn dw_plus_fp(a: DD, b: f64) -> DD {
    let (sh, sl) = two_sum(a.hi, b);
    let v = a.lo + sl;
    let (zh, zl) = quick_two_sum(sh, v);
    DD { hi: zh, lo: zl }
}

/// a b for double-words: DWTimesDW2, Algorithm 11 of Joldes, Muller and Popescu (2017), within 5u^2 / (1 + u)^2
/// relative, the bound J.-M. Muller and L. Rideau proved formally (ACM Trans. Math. Softw. 48(1), 2022,
/// doi:10.1145/3484514). `DD`'s `*` sums its terms in another order, for which no bound is published.
#[inline(always)]
fn dw_times_dw(a: DD, b: DD) -> DD {
    let (ch, cl1) = two_prod(a.hi, b.hi);
    let tl = a.hi * b.lo;
    let cl2 = a.lo.mul_add(b.hi, tl);
    let (zh, zl) = quick_two_sum(ch, cl1 + cl2);
    DD { hi: zh, lo: zl }
}

/// The double-double: `+` is AccurateDWPlusDW (Joldes, Muller, Popescu 2017, Theorem 3.1: 3u^2 / (1 - 4u)), `mul_f`
/// DWTimesFP3 (their Algorithm 9: 2u^2), and the products and the f64 sums are `dw_times_dw` and `dw_plus_fp`.
impl Prec for DD {
    const S: i32 = 1;
    const DEG: usize = 27;
    const Q: usize = 3;
    const B: i32 = 118;
    #[inline(always)]
    fn from_f64(x: f64) -> DD {
        DD::from_f64(x)
    }
    #[inline(always)]
    fn hi(self) -> f64 {
        self.hi
    }
    #[inline(always)]
    fn abs_sum(self) -> f64 {
        self.hi.abs() + self.lo.abs()
    }
    #[inline(always)]
    fn konst(c: &[f64; 8]) -> DD {
        DD { hi: c[0], lo: c[1] }
    }
    #[inline(always)]
    fn plus(self, b: DD) -> DD {
        self + b
    }
    #[inline(always)]
    fn times(self, b: DD) -> DD {
        dw_times_dw(self, b)
    }
    #[inline(always)]
    fn plus_one(self) -> DD {
        dw_plus_fp(self, 1.0)
    }
    #[inline(always)]
    fn times_pwr2(self, b: f64) -> DD {
        self.mul_pwr2(b)
    }
    #[inline(always)]
    fn neg(self) -> DD {
        -self
    }
    #[inline(always)]
    fn reduce(self, k: f64, lo: &[f64; 8]) -> DD {
        let a = self.hi - k * LN2_HI;
        let p = DD { hi: lo[0], lo: lo[1] }.mul_f(-k);
        dw_plus_fp(dw_plus_fp(p, self.lo), a)
    }
    #[inline(always)]
    fn sub_one(self) -> DD {
        let (h, l) = two_sum(self.hi - 1.0, self.lo);
        DD { hi: h, lo: l }
    }
    /// the logarithm of the leading part (`ln_f64`), plus lo / hi
    #[inline(always)]
    fn ln_start(self) -> DD {
        DD::from_f64(ln_f64(self.hi) + self.lo / self.hi)
    }
    #[inline(always)]
    fn ln_finish(y0: DD, corr: DD) -> DD {
        dw_plus_fp(corr, y0.hi)
    }
}

/// The quad-double: QD's default `+` and `*` (the sloppy add and multiply), `add_f` and `mul_f`.
impl Prec for QD {
    const S: i32 = 6;
    const DEG: usize = 24;
    const Q: usize = 2;
    const B: i32 = 224;
    #[inline(always)]
    fn from_f64(x: f64) -> QD {
        QD::from_f64(x)
    }
    #[inline(always)]
    fn hi(self) -> f64 {
        self.x[0]
    }
    #[inline(always)]
    fn abs_sum(self) -> f64 {
        self.x.iter().fold(0.0, |a, v| a + v.abs())
    }
    #[inline(always)]
    fn konst(c: &[f64; 8]) -> QD {
        QD {
            x: [c[0], c[1], c[2], c[3]],
        }
    }
    #[inline(always)]
    fn plus(self, b: QD) -> QD {
        self + b
    }
    #[inline(always)]
    fn times(self, b: QD) -> QD {
        self * b
    }
    #[inline(always)]
    fn plus_one(self) -> QD {
        self.add_f(1.0)
    }
    #[inline(always)]
    fn times_pwr2(self, b: f64) -> QD {
        self.mul_pwr2(b)
    }
    #[inline(always)]
    fn neg(self) -> QD {
        -self
    }
    /// the exact x - k LN2_HI renormalized in any order (`QD::from_sum`), as QD's add expects ordered parts
    #[inline(always)]
    fn reduce(self, k: f64, lo: &[f64; 8]) -> QD {
        let x = self.x;
        QD::from_sum(x[0] - k * LN2_HI, x[1], x[2], x[3]) + QD::konst(lo).mul_f(-k)
    }
    #[inline(always)]
    fn sub_one(self) -> QD {
        let x = self.x;
        QD::from_sum(x[0] - 1.0, x[1], x[2], x[3])
    }
    #[inline(always)]
    fn ln_start(self) -> QD {
        QD::from_dd(start_dd(self.x[0], || self.to_dd(), || self.times_pwr2(0.5).to_dd()))
    }
    #[inline(always)]
    fn ln_finish(y0: QD, corr: QD) -> QD {
        y0 + corr
    }
}

/// The octo-double: the paper's ADD, MUL, ADDF and MULF (`+`, `*`, `add_f`, `mul_f`).
impl Prec for OD {
    const S: i32 = 6;
    const DEG: usize = 43;
    const Q: usize = 4;
    const B: i32 = 436;
    #[inline(always)]
    fn from_f64(x: f64) -> OD {
        OD::from_f64(x)
    }
    #[inline(always)]
    fn hi(self) -> f64 {
        self.x[0]
    }
    #[inline(always)]
    fn abs_sum(self) -> f64 {
        self.x.iter().fold(0.0, |a, v| a + v.abs())
    }
    #[inline(always)]
    fn konst(c: &[f64; 8]) -> OD {
        OD { x: *c }
    }
    #[inline(always)]
    fn plus(self, b: OD) -> OD {
        self + b
    }
    #[inline(always)]
    fn times(self, b: OD) -> OD {
        self * b
    }
    #[inline(always)]
    fn plus_one(self) -> OD {
        self.add_f(1.0)
    }
    #[inline(always)]
    fn times_pwr2(self, b: f64) -> OD {
        self.mul_pwr2(b)
    }
    #[inline(always)]
    fn neg(self) -> OD {
        -self
    }
    /// (x_0 - k LN2_HI, x_1, ..., x_7) as it is, an operand of `+` whatever its parts' order
    #[inline(always)]
    fn reduce(self, k: f64, lo: &[f64; 8]) -> OD {
        let mut x = self;
        x.x[0] = self.x[0] - k * LN2_HI;
        x + OD { x: *lo }.mul_f(-k)
    }
    /// exact: x_0 - 1 by Sterbenz, the other parts' two-sums with zero, and nine levels whose last is zero
    #[inline(always)]
    fn sub_one(self) -> OD {
        self.add_f(-1.0)
    }
    #[inline(always)]
    fn ln_start(self) -> OD {
        OD::from_dd(start_dd(self.x[0], || self.to_dd(), || self.times_pwr2(0.5).to_dd()))
    }
    /// y0 + corr, by `add_dd` (the bits of `+` with y0's zero parts)
    #[inline(always)]
    fn ln_finish(y0: OD, corr: OD) -> OD {
        corr.add_dd(DD {
            hi: y0.x[0],
            lo: y0.x[1],
        })
    }
}

impl DD {
    /// e^self, within 5.465 u^2 e^x + 2 2^-1074 (u = 2^-53) for a double-word whose e^x is below f64::MAX + ulp/2, from
    /// the published bounds of the double-word operations it uses (see the module doc for the condition); +inf above
    /// 709.79 and where the result overflows, +0 below -745.2
    pub fn exp(self) -> DD {
        exp_of(self)
    }
    /// the natural logarithm, within 15.351 u^2 |ln x| + 2^-1071 for a double-word, from its own start `ln_f64` (see
    /// the module doc for the condition); NaN for a negative argument, -inf for zero
    pub fn ln(self) -> DD {
        ln_of(self)
    }
}

impl QD {
    /// e^self (see the module doc; QD's operations, tested to 64 u^4 e^x + 4 2^-1074 where e^x is below f64::MAX +
    /// ulp/2); +inf above 709.79 and where the result overflows, +0 below -745.2
    pub fn exp(self) -> QD {
        exp_of(self)
    }
    /// the natural logarithm (see the module doc; tested to 64 u^4 |ln x|); NaN for a negative argument, -inf for
    /// zero
    pub fn ln(self) -> QD {
        ln_of(self)
    }
}

impl OD {
    /// e^self, within 3.661 u^8 e^x + 8 2^-1074 (u = 2^-53) for an argument on the ladder whose e^x is below f64::MAX +
    /// ulp/2 (see the module doc for the condition); +inf above 709.79 and where the result overflows, +0 below -745.2
    pub fn exp(self) -> OD {
        exp_of(self)
    }
    /// the natural logarithm, within 9.926 u^8 |ln x| + 2^-509 for an argument on the ladder (see the module doc
    /// for the condition); NaN for a negative argument, -inf for zero
    pub fn ln(self) -> OD {
        ln_of(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::exact::{BigU, Dy};

    /// |sum parts - num / den| <= 2^lim2 |num / den|, in exact arithmetic: |den sum - num| 2^-lim2 <= num
    fn within(parts: &[f64], num: &Dy, den: &Dy, lim2: i64) -> bool {
        let d = Dy::sum(parts).mul(den).sub(num).abs();
        d.ldexp(-lim2).cmp_abs(num) != std::cmp::Ordering::Greater
    }

    /// ln 2 from sum 1/(j 2^j) in 1600-bit fixed point, within 2^-1585 below: no code shared with the generator
    fn ln2() -> Dy {
        let p = 1600u64;
        let mut s = BigU::zero();
        for j in 1..=p {
            s = s.add(&BigU::from_u64(1).shl(p - j).divrem_small(j).0);
        }
        Dy {
            neg: false,
            m: s,
            e: -(p as i64),
        }
    }

    /// The generated constants against exact arithmetic: 1/j! and 1/3 to their eight-part greedy rounding (within
    /// 2^-423 relative), ln 2 against its series in Rust (LN2_HI + LN2_LO within 2^-466, LN2_DD within 2^-107), LN2_HI
    /// of 42 bits. Control: each check fails with the last part moved by 2^-421 of the value (2^-460 for ln 2, 2^-104
    /// for LN2_DD).
    #[test]
    fn constants_are_exact_roundings() {
        let one = Dy::from_f64(1.0);
        let mut f = Dy::from_f64(1.0);
        for (j, c) in INV_FACT.iter().enumerate() {
            if j > 0 {
                f = f.mul(&Dy::from_f64(j as f64));
            }
            assert!(within(c, &one, &f, -423), "1/{j}!");
            let mut bad = *c;
            bad[7] += 2f64.powi(-421) * c[0];
            assert!(!within(&bad, &one, &f, -423), "control 1/{j}!");
        }
        assert!(within(&THIRD, &one, &Dy::from_f64(3.0), -423));
        let mut bad = THIRD;
        bad[7] += 2f64.powi(-421) * THIRD[0];
        assert!(!within(&bad, &one, &Dy::from_f64(3.0), -423), "control 1/3");
        let mut lo = vec![LN2_HI];
        lo.extend_from_slice(&LN2_LO);
        let l2 = ln2();
        assert!(within(&lo, &l2, &one, -466), "ln 2");
        lo[8] += 2f64.powi(-460);
        assert!(!within(&lo, &l2, &one, -466), "control ln 2");
        assert_eq!(LN2_HI.to_bits() & ((1 << 11) - 1), 0, "LN2_HI has more than 42 bits");
        // LN2_DD, ln 2's greedy two parts, within 2^-107 relative, and its control
        assert!(within(&LN2_DD, &l2, &one, -107), "LN2_DD");
        let mut bad = LN2_DD;
        bad[1] += 2f64.powi(-104);
        assert!(!within(&bad, &l2, &one, -107), "control LN2_DD");
        assert!((LN2_HI - std::f64::consts::LN_2).abs() < 2f64.powi(-42));
    }
}
