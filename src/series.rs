//! Products of power series whose coefficients are double-, quad- or octo-double lanes.
//!
//! * [`mullow`]: the truncated product c_k = sum_(i=0..=k) a_i b_(k-i), k < n, of two series of an [`Expansion`]
//!   ([`DV`], [`QV`], [`OV`]) on each of the 8 lanes, by block scaling and exact integer convolution, added into the
//!   expansion's accumulators; [`mullow_naive`] is its reference, each sum formed term by term.
//! * [`Relaxed`]: the product of two series of fields whose coefficients become known one order at a time, as in a
//!   recurrence that solves for order k with the products' coefficients of order k. The products of blocks of earlier
//!   coefficients are formed ahead by [`Lane::block_mul`] (by `mullow` on `DV`, `QV`, `OV` and their dual lanes), and
//!   the terms with a recent coefficient are summed directly.
//!
//! # The exact product
//!
//! Scaling. a_i and b_i are multiplied by 2^(s i) on each lane, s an integer slope from the series' leading exponents
//! (least squares), which multiplies c_k by 2^(s k) exactly.
//!
//! Blocks. Each scaled series is cut into runs of indices whose leading exponents lie within h bits on every lane. In
//! a block of largest exponent F (per lane) the coefficient becomes the integer X_i = a_i 2^(s i + W - F) with each
//! part rounded, W = 16 t - 2 bits for t digits, so it keeps W - h - 5 bits or more. Every pair of blocks whose
//! product reaches below n is multiplied exactly, and the pair's terms then err by 2^-prec of its smallest term or
//! less, prec = 53 times the expansion's parts by default ([`Cfg::prec`]). The slope (from both series, from a or from
//! b) and h ([`Cfg::spread`] times 1, 2 or 4) are those of least estimated cost: flat series are one block each.
//!
//! Convolution. Each integer is t balanced 16-bit digits. The digit sequences are transformed by f64 FFTs (two real
//! sequences per complex transform), the digit products summed by weight r + r' in the frequency domain, and the
//! weights transformed back. Every value is then an integer below 2^44. Its distance from the computed value is
//! checked to be under 1/4 before any of the pair's terms is used, so the convolution is exact and its bits depend on
//! no libm; a pair that fails the check (none has in the tests) is formed term by term ([`Stats::fallback`]). Weights
//! too small to reach 2^-prec of the smallest term are not formed. The integer at each index is carried into balanced
//! digits and added into the index's accumulator: on octo-double lanes cut into eight 53-bit parts from its top bit
//! (2^-424 of it or less dropped), on double- and quad-double lanes as chunks of three digits (exact in f64), the top
//! first, which the accumulator rounds to its precision.
//!
//! The bits do not depend on the backend: the transforms' operations are the lanes' own, and their results are
//! rounded to the exact integers. They differ from the naive sums' bits by about the expansion's rounding.
//!
//! J. van der Hoeven, "Making fast multiplication of polynomials numerically stable", preprint, Universite Paris-Sud
//! (2008); the blocks are those of F. Johansson's Arb (`arb_poly_mullow_block`), "Arb: efficient arbitrary-precision
//! midpoint-radius interval arithmetic", IEEE Trans. Comput. 66, 1281-1292 (2017), doi:10.1109/TC.2017.2690633.
//!
//! # Relaxed products
//!
//! In a recurrence, order k of a product x y is needed before x_k and y_k are known: x_k is solved for with it. The
//! terms of c_k with both indices i, k - i >= d (d = s0 + 1) are covered by van der Hoeven's squares, of side 2^p >= s0
//! (a power of two) with the corner at (m 2^p + 1, 2^p + 1), m >= 1, and their transposes, m >= 2. Such a square
//! needs coefficients up to order (m + 1) 2^p, so it is formed at the end of step e = (m + 1) 2^p + 1 ([`Relaxed::step`])
//! from orders below e, and its first term is of order e + 1. The terms with an index below d, 2d of them per order,
//! are summed directly when the coefficient is read ([`Relaxed::sum`]), with whatever values the caller has then.
//! To order n a product forms about 2n/s squares of side s for each of the O(log n) sides s >= s0, which cost
//! O(n M(s) / s) each with M(s) the cost of an s-term product by `mullow`, and 2d direct terms per order: O(M(n) log n)
//! and O(s0 n) in all, where `mullow`'s pairs are convolved (pairs past its FFT tables, s > 4096, are formed term by
//! term). J. van der Hoeven, "Relax, but don't be too lazy", J. Symbolic Comput. 34, 479-542 (2002),
//! doi:10.1006/jsco.2002.0562.
use crate::dual::{Du, Lane, Ou, Qu};
use crate::dv::{DDotAcc, DV};
use crate::field::Fl;
use crate::ov::{ODotAcc, OV};
use crate::qv::{QDotAcc, QV};
use crate::simd::Simd;
use crate::v8::V8;
use std::sync::OnceLock;

/// lanes of a vector
const LN: usize = 8;
/// bits of a digit
const DB: i32 = 16;
const R16: f64 = 65536.0;
const IR16: f64 = 1.0 / 65536.0;
/// largest FFT length (a block pair of up to 2^LMAX_LOG2 - 1 terms)
const LMAX_LOG2: usize = 13;
/// most digits per coefficient: W = 16 T_MAX - 2 = 958 bits keeps the scaled coefficient finite, and its scale
/// 2^k (k <= W + 1074) within pow2_split's 2^2044; parts_of's limbs hold the 2 T_MAX + 2 digits of a product
const T_MAX: usize = 60;

/// lane-wise f64 values
type L8 = [f64; LN];

/// A lane type whose values are sums of NP f64 parts (`DV`, `QV`, `OV`), the coefficients `mullow` takes, with the
/// accumulator its naive sums use.
pub trait Expansion<S: Simd>: Copy + Send + Sync + 'static {
    /// parts per value
    const NP: usize;
    /// the cost model's seconds per product into the accumulator, 8 lanes (an Apple M5, `examples/series_squares.rs`)
    const PROD_S: f64;
    /// the accumulator of sums of products
    type Acc: Copy + Send + Sync + 'static;
    /// part i, the largest first
    fn part(&self, i: usize) -> V8<S>;
    /// the value whose parts are p (NP of them), as they are
    fn from_parts(p: &[V8<S>]) -> Self;
    fn acc_zero() -> Self::Acc;
    /// acc + a b
    fn acc_prod(acc: &mut Self::Acc, a: &Self, b: &Self);
    /// acc + the value whose parts are p (NP of them, not overlapping)
    fn acc_parts(acc: &mut Self::Acc, p: &[V8<S>]);
    fn acc_fin(acc: &Self::Acc) -> Self;
}

impl<S: Simd> Expansion<S> for DV<S> {
    const NP: usize = 2;
    const PROD_S: f64 = 6e-9;
    type Acc = DDotAcc<S>;
    #[inline(always)]
    fn part(&self, i: usize) -> V8<S> {
        if i == 0 {
            self.hi
        } else {
            self.lo
        }
    }
    #[inline(always)]
    fn from_parts(p: &[V8<S>]) -> Self {
        DV { hi: p[0], lo: p[1] }
    }
    #[inline(always)]
    fn acc_zero() -> Self::Acc {
        DDotAcc::zero()
    }
    #[inline(always)]
    fn acc_prod(acc: &mut Self::Acc, a: &Self, b: &Self) {
        *acc = acc.add_prod(*a, *b);
    }
    #[inline(always)]
    fn acc_parts(acc: &mut Self::Acc, p: &[V8<S>]) {
        *acc = acc.add(DV { hi: p[0], lo: p[1] });
    }
    #[inline(always)]
    fn acc_fin(acc: &Self::Acc) -> Self {
        acc.finish()
    }
}

impl<S: Simd> Expansion<S> for QV<S> {
    const NP: usize = 4;
    const PROD_S: f64 = 50e-9;
    type Acc = QDotAcc<S>;
    #[inline(always)]
    fn part(&self, i: usize) -> V8<S> {
        self.c[i]
    }
    #[inline(always)]
    fn from_parts(p: &[V8<S>]) -> Self {
        QV {
            c: [p[0], p[1], p[2], p[3]],
        }
    }
    #[inline(always)]
    fn acc_zero() -> Self::Acc {
        QDotAcc::zero()
    }
    #[inline(always)]
    fn acc_prod(acc: &mut Self::Acc, a: &Self, b: &Self) {
        acc.add_prod_mut(a, b);
    }
    #[inline(always)]
    fn acc_parts(acc: &mut Self::Acc, p: &[V8<S>]) {
        *acc = acc.add(QV {
            c: [p[0], p[1], p[2], p[3]],
        });
    }
    #[inline(always)]
    fn acc_fin(acc: &Self::Acc) -> Self {
        acc.finish()
    }
}

impl<S: Simd> Expansion<S> for OV<S> {
    const NP: usize = 8;
    const PROD_S: f64 = 0.6e-6;
    type Acc = ODotAcc<S>;
    #[inline(always)]
    fn part(&self, i: usize) -> V8<S> {
        self.c[i]
    }
    #[inline(always)]
    fn from_parts(p: &[V8<S>]) -> Self {
        OV {
            c: std::array::from_fn(|i| p[i]),
        }
    }
    #[inline(always)]
    fn acc_zero() -> Self::Acc {
        ODotAcc::zero()
    }
    #[inline(always)]
    fn acc_prod(acc: &mut Self::Acc, a: &Self, b: &Self) {
        acc.add_prod_mut(a, b);
    }
    #[inline(always)]
    fn acc_parts(acc: &mut Self::Acc, p: &[V8<S>]) {
        *acc = acc.add(OV {
            c: std::array::from_fn(|i| p[i]),
        });
    }
    #[inline(always)]
    fn acc_fin(acc: &Self::Acc) -> Self {
        acc.finish()
    }
}

/// The product's parameters.
#[derive(Clone, Copy, Debug)]
pub struct Cfg {
    /// bits kept below the smallest term of a block pair (the product's accuracy, relative to sum |a_i| |b_(k-i)|);
    /// 0, the default, 53 times the expansion's parts (106, 212 or 424)
    pub prec: i32,
    /// the largest spread in bits of the scaled leading exponents within a block
    pub spread: i32,
    /// the slope 2^(s i) on; off, s = 0
    pub scale: bool,
    /// blocks on; off, each series is one block and its digits are those of `spread` (a control: the blocks' and
    /// the slope's guarantee removed)
    pub blocks: bool,
    /// the controls, 0 off: MUT_ZERO_LANE scales zero lanes as the others, MUT_E2_PLAIN scales the direct pairs' first
    /// factor by 2^e2 as one f64, MUT_E2_SPLIT_ALWAYS splits 2^e2 between the factors also at e2 = 0, MUT_E2_PRESCALE
    /// splits it between the factors by their top exponents, MUT_DROP_PAIR drops the first block pair formed by
    /// convolution, MUT_SLOPE takes the output's scale from the slope plus one, MUT_CHUNK_TOP reads double- and
    /// quad-double outputs in chunks also at the top of f64's range
    pub mutate: u8,
}

/// `Cfg::mutate`: zero lanes scaled like the others (their scale can lie outside f64's range)
pub const MUT_ZERO_LANE: u8 = 1;
/// `Cfg::mutate`: the direct pairs' 2^e2 formed as one f64 on the first factor (it can overflow)
pub const MUT_E2_PLAIN: u8 = 2;
/// `Cfg::mutate`: the direct pairs' split of 2^e2 between the factors also at e2 = 0 (where it can underflow a
/// small coefficient of a wide factor)
pub const MUT_E2_SPLIT_ALWAYS: u8 = 4;
/// `Cfg::mutate`: the direct pairs' 2^e2 split between the factors by their top exponents at e2 != 0 (a wide factor's
/// small coefficients can underflow)
pub const MUT_E2_PRESCALE: u8 = 5;
/// `Cfg::mutate`: the first block pair formed by convolution left out
pub const MUT_DROP_PAIR: u8 = 6;
/// `Cfg::mutate`: the outputs unscaled by 2^-((s + 1) k) instead of 2^-(s k), a wrong slope
pub const MUT_SLOPE: u8 = 7;
/// `Cfg::mutate`: double- and quad-double outputs read in chunks also at the top of f64's range, where a balanced
/// chunk can overflow
pub const MUT_CHUNK_TOP: u8 = 8;

impl Default for Cfg {
    fn default() -> Self {
        Cfg {
            prec: 0,
            spread: 32,
            scale: true,
            blocks: true,
            mutate: 0,
        }
    }
}

impl Cfg {
    /// prec, or the expansion's 53 NP bits where it is 0
    fn prec_of<S: Simd, E: Expansion<S>>(&self) -> Cfg {
        Cfg {
            prec: if self.prec > 0 { self.prec } else { 53 * E::NP as i32 },
            ..*self
        }
    }
}

/// What one product did.
#[derive(Clone, Copy, Debug, Default)]
pub struct Stats {
    /// products formed
    pub calls: usize,
    /// block pairs multiplied
    pub pairs: usize,
    /// of them, those formed term by term (past the FFT tables or too wide in digits)
    pub direct: usize,
    /// of them, those whose convolution missed the 1/4 check and were then formed term by term
    pub fallback: usize,
    /// blocks of a and of b
    pub blocks: (usize, usize),
    /// the largest distance of an inverse transform's value from its integer (exact while below 1/2); infinite when a
    /// factor is not finite (the product then formed term by term)
    pub max_frac: f64,
    /// digits per coefficient (largest over the pairs)
    pub digits: usize,
}

impl Stats {
    pub fn merge(&mut self, o: &Stats) {
        self.calls += o.calls;
        self.pairs += o.pairs;
        self.direct += o.direct;
        self.fallback += o.fallback;
        self.blocks = (self.blocks.0.max(o.blocks.0), self.blocks.1.max(o.blocks.1));
        self.max_frac = self.max_frac.max(o.max_frac);
        self.digits = self.digits.max(o.digits);
    }
}

/// c_k = sum_(i=0..=k) a_i b_(k-i), k < n, each sum in the expansion's accumulator (the reference); an empty factor
/// gives zeros
pub fn mullow_naive<S: Simd, E: Expansion<S>>(a: &[E], b: &[E], n: usize) -> Vec<E> {
    (0..n)
        .map(|k| {
            let mut acc = E::acc_zero();
            for i in 0..a.len().min(k + 1) {
                if k - i < b.len() {
                    E::acc_prod(&mut acc, &a[i], &b[k - i]);
                }
            }
            E::acc_fin(&acc)
        })
        .collect()
}

/// c_k for k < n added into acc\[k\] (acc of n entries or more) by the block-scaled exact product (module doc)
pub fn mullow<S: Simd, E: Expansion<S>>(a: &[E], b: &[E], n: usize, cfg: &Cfg, acc: &mut [E::Acc]) -> Stats {
    mullow_pow2(a, b, n, cfg, 0, acc)
}

/// `mullow` with c_k 2^e2 added (exactly: e2 enters the parts' exponents)
pub fn mullow_pow2<S: Simd, E: Expansion<S>>(
    a: &[E],
    b: &[E],
    n: usize,
    cfg: &Cfg,
    e2: i32,
    acc: &mut [E::Acc],
) -> Stats {
    let cfg = &cfg.prec_of::<S, E>();
    let (na, nb) = (a.len().min(n), b.len().min(n));
    let mut st = Stats {
        calls: 1,
        ..Stats::default()
    };
    if na == 0 || nb == 0 || n == 0 {
        return st;
    }
    // a factor that is not finite: the product term by term, so that its NaNs and infinities reach the sums as in the
    // naive product, and reported (max_frac infinite)
    let finite = |v: &[E]| {
        v.iter()
            .all(|x| (0..E::NP).all(|p| x.part(p).to_array().iter().all(|q| q.is_finite())))
    };
    if !finite(&a[..na]) || !finite(&b[..nb]) {
        st.max_frac = f64::INFINITY;
        st.pairs = 1;
        st.direct = 1;
        direct(&a[..na], &b[..nb], 0, n, cfg, e2, acc);
        return st;
    }
    let (ea, eb) = (exponents(&a[..na]), exponents(&b[..nb]));
    // the slope and the blocks' spread limit of least estimated cost: the slope from both series, from a alone and
    // from b alone, and the limit cfg.spread, twice and four times it (one limit and no slope without the blocks)
    let (fa, fb): ([f64; LN], [f64; LN]) = (
        std::array::from_fn(|l| fit(&ea, l)),
        std::array::from_fn(|l| fit(&eb, l)),
    );
    let slopes: Vec<[i32; LN]> = if cfg.scale {
        vec![
            std::array::from_fn(|l| (-(fa[l] + fb[l]) * 0.5).round() as i32),
            std::array::from_fn(|l| (-fa[l]).round() as i32),
            std::array::from_fn(|l| (-fb[l]).round() as i32),
        ]
    } else {
        vec![[0; LN]]
    };
    let limits: &[i32] = if cfg.blocks { &[1, 2, 4] } else { &[1] };
    let mut best: Option<Choice> = None;
    for sl in &slopes {
        for &m in limits {
            let h = cfg.spread * m;
            let (ba, bb) = (blocks(&ea, sl, h, cfg), blocks(&eb, sl, h, cfg));
            let c = cost::<S, E>(&ba, &bb, n, cfg);
            if best.as_ref().is_none_or(|b| c < b.0) {
                best = Some((c, *sl, ba, bb));
            }
        }
    }
    let (_, s, ba, bb) = best.expect("a slope and a limit");
    let (ba, bb) = if cfg.blocks {
        shorten::<S, E>(ba, bb, &ea, &eb, &s, n, cfg)
    } else {
        (ba, bb)
    };
    st.blocks = (ba.len(), bb.len());
    // the scratch of this thread, kept between calls (its slabs are megabytes), one per backend
    thread_local! {
        static WS: std::cell::RefCell<Option<Box<dyn std::any::Any>>> = const { std::cell::RefCell::new(None) };
    }
    WS.with(|w| {
        let mut w = w.borrow_mut();
        if !w.as_ref().is_some_and(|x| x.is::<Work<S>>()) {
            *w = Some(Box::new(Work::<S>::new()));
        }
        let ws = w
            .as_mut()
            .and_then(|x| x.downcast_mut::<Work<S>>())
            .expect("this backend's scratch");
        mullow_pairs(a, b, n, cfg, e2, acc, &ba, &bb, &s, &mut st, ws);
    });
    st
}

/// a plan's estimated cost, slope and blocks of a and b
type Choice = (f64, [i32; LN], Vec<Block>, Vec<Block>);

/// every block pair of `mullow` reaching below n
#[allow(clippy::too_many_arguments)]
fn mullow_pairs<S: Simd, E: Expansion<S>>(
    a: &[E],
    b: &[E],
    n: usize,
    cfg: &Cfg,
    e2: i32,
    acc: &mut [E::Acc],
    ba: &[Block],
    bb: &[Block],
    s: &[i32; LN],
    st: &mut Stats,
    ws: &mut Work<S>,
) {
    // the control MUT_DROP_PAIR: the first pair that would be convolved
    let mut drop = None;
    if cfg.mutate == MUT_DROP_PAIR {
        'find: for (ia, xa) in ba.iter().enumerate() {
            for (ib, xb) in bb.iter().enumerate() {
                let o = xa.start + xb.start;
                if o < n {
                    let (la, lb) = ((xa.end - xa.start).min(n - o), (xb.end - xb.start).min(n - o));
                    if la + lb - 1 <= 1 << LMAX_LOG2 && plan(cfg, xa.spread, xb.spread, la, lb).is_some() {
                        drop = Some((ia, ib));
                        break 'find;
                    }
                }
            }
        }
    }
    for (ia, xa) in ba.iter().enumerate() {
        for (ib, xb) in bb.iter().enumerate() {
            let o = xa.start + xb.start;
            if o >= n {
                continue;
            }
            st.pairs += 1;
            let (x, y) = (&a[xa.start..xa.end], &b[xb.start..xb.end]);
            let (la, lb) = (x.len().min(n - o), y.len().min(n - o));
            // past the FFT tables, or digits too wide for digits and parts_of: the pair term by term
            if la + lb - 1 > 1 << LMAX_LOG2 || plan(cfg, xa.spread, xb.spread, la, lb).is_none() {
                st.direct += 1;
                direct(x, y, o, n - o, cfg, e2, acc);
                continue;
            }
            if drop == Some((ia, ib)) {
                continue;
            }
            if !pair(x, y, xa, xb, s, n - o, o, cfg, e2, acc, st, ws) {
                st.fallback += 1;
                direct(x, y, o, n - o, cfg, e2, acc);
            }
        }
    }
}

/// x times y truncated to nout terms added into acc\[o..\] term by term, the terms of each index in the order of x's.
/// At e2 = 0 the factors are used as they are. Otherwise each term's 2^e2 is split per lane between its two
/// coefficients by their own exponents, so that both and their product keep the range of the term: only a term
/// below 2^-1022 itself rounds.
fn direct<S: Simd, E: Expansion<S>>(x: &[E], y: &[E], o: usize, nout: usize, cfg: &Cfg, e2: i32, acc: &mut [E::Acc]) {
    // the pair's terms reach x.len() + y.len() - 1 outputs (both factors nonempty)
    let nout = nout.min(x.len() + y.len() - 1);
    let prescale = (e2 != 0 && cfg.mutate == MUT_E2_PRESCALE) || (e2 == 0 && cfg.mutate == MUT_E2_SPLIT_ALWAYS);
    let plain = e2 != 0 && cfg.mutate == MUT_E2_PLAIN;
    if e2 != 0 && !prescale && !plain {
        let ex = |v: &E| -> [i32; LN] { v.part(0).to_array().map(|p| if p == 0.0 { 0 } else { expo(p) }) };
        let (xe, ye): (Vec<_>, Vec<_>) = (x.iter().map(ex).collect(), y.iter().map(ex).collect());
        for k in 0..nout {
            for i in k.saturating_sub(y.len() - 1)..x.len().min(k + 1) {
                let al: [i32; LN] = std::array::from_fn(|l| (ye[k - i][l] - xe[i][l] + e2).div_euclid(2));
                let be: [i32; LN] = std::array::from_fn(|l| e2 - al[l]);
                E::acc_prod(&mut acc[o + k], &scale_lanes(&x[i], &al), &scale_lanes(&y[k - i], &be));
            }
        }
        return;
    }
    let (xs, ys) = if plain {
        // the control: 2^e2 as one f64 on the first factor, by a plain multiply (infinite for a large e2)
        let f = V8::splat(2f64.powi(e2));
        let pl = |v: &E| -> E {
            let p: Vec<V8<S>> = (0..E::NP).map(|i| v.part(i).mul(f)).collect();
            E::from_parts(&p)
        };
        (x.iter().map(pl).collect::<Vec<_>>(), y.to_vec())
    } else if prescale {
        // the controls: 2^e2 split between the factors by their top exponents
        let top = |v: &[E]| -> [i32; LN] {
            std::array::from_fn(|l| {
                v.iter()
                    .map(|c| c.part(0).to_array()[l])
                    .filter(|&p| p != 0.0)
                    .map(expo)
                    .max()
                    .unwrap_or(0)
            })
        };
        let (tx, ty) = (top(x), top(y));
        let al: [i32; LN] = std::array::from_fn(|l| (ty[l] - tx[l] + e2).div_euclid(2));
        let be: [i32; LN] = std::array::from_fn(|l| e2 - al[l]);
        (
            x.iter().map(|v| scale_lanes(v, &al)).collect(),
            y.iter().map(|v| scale_lanes(v, &be)).collect(),
        )
    } else {
        // no scale, so none that could underflow a small coefficient of a wide factor
        (x.to_vec(), y.to_vec())
    };
    for k in 0..nout {
        for i in k.saturating_sub(ys.len() - 1)..xs.len().min(k + 1) {
            E::acc_prod(&mut acc[o + k], &xs[i], &ys[k - i]);
        }
    }
}

/// the leading exponent e (|x| in [2^(e-1), 2^e)) of every coefficient's leading part per lane, i32::MIN for zero
fn exponents<S: Simd, E: Expansion<S>>(a: &[E]) -> Vec<[i32; LN]> {
    a.iter()
        .map(|v| v.part(0).to_array().map(|x| if x == 0.0 { i32::MIN } else { expo(x) }))
        .collect()
}

#[inline]
fn expo(x: f64) -> i32 {
    let b = x.to_bits();
    let ex = ((b >> 52) & 0x7ff) as i32;
    if ex == 0 {
        -1010 - (b & ((1u64 << 52) - 1)).leading_zeros() as i32
    } else {
        ex - 1022
    }
}

/// the least-squares slope of the nonzero exponents of a series on lane l (0 with fewer than two)
fn fit(e: &[[i32; LN]], l: usize) -> f64 {
    let (mut n, mut sx, mut sy, mut sxx, mut sxy) = (0.0, 0.0, 0.0, 0.0, 0.0);
    for (i, v) in e.iter().enumerate() {
        if v[l] != i32::MIN {
            let (x, y) = (i as f64, v[l] as f64);
            n += 1.0;
            sx += x;
            sy += y;
            sxx += x * x;
            sxy += x * y;
        }
    }
    let d = n * sxx - sx * sx;
    if n < 2.0 || d <= 0.0 {
        0.0
    } else {
        (n * sxy - sx * sy) / d
    }
}

/// a block: indices start..end, its largest scaled exponent per lane, and its spread (largest over the lanes)
#[derive(Clone)]
struct Block {
    start: usize,
    end: usize,
    frame: [i32; LN],
    spread: i32,
}

/// the blocks of a series (module doc), each of spread h or less; one block when cfg.blocks is off, taken to have the
/// spread cfg.spread
fn blocks(e: &[[i32; LN]], s: &[i32; LN], h: i32, cfg: &Cfg) -> Vec<Block> {
    let mut out = Vec::new();
    let mut start = 0;
    let (mut lo, mut hi) = ([i32::MAX; LN], [i32::MIN; LN]);
    let close = |start: usize, end: usize, lo: &[i32; LN], hi: &[i32; LN], out: &mut Vec<Block>| {
        let spread = (0..LN)
            .filter(|&l| hi[l] != i32::MIN)
            .map(|l| hi[l] - lo[l])
            .max()
            .unwrap_or(0);
        let frame = std::array::from_fn(|l| if hi[l] == i32::MIN { 0 } else { hi[l] });
        out.push(Block {
            start,
            end,
            frame,
            spread: if cfg.blocks { spread } else { cfg.spread },
        });
    };
    for (i, v) in e.iter().enumerate() {
        let mut split = false;
        let mut nlo = lo;
        let mut nhi = hi;
        for l in 0..LN {
            if v[l] != i32::MIN {
                let x = v[l] + s[l] * i as i32;
                nlo[l] = nlo[l].min(x);
                nhi[l] = nhi[l].max(x);
                split |= nhi[l] - nlo[l] > h;
            }
        }
        if split && cfg.blocks && i > start {
            close(start, i, &lo, &hi, &mut out);
            start = i;
            for l in 0..LN {
                let x = v[l].saturating_add(s[l] * i as i32);
                (lo[l], hi[l]) = if v[l] == i32::MIN { (i32::MAX, i32::MIN) } else { (x, x) };
            }
        } else {
            (lo, hi) = (nlo, nhi);
        }
    }
    close(start, e.len(), &lo, &hi, &mut out);
    out
}

/// the block of indices start..end of a series (its frame and spread, as `blocks` closes one)
fn block_of(e: &[[i32; LN]], s: &[i32; LN], start: usize, end: usize, cfg: &Cfg) -> Block {
    let (mut lo, mut hi) = ([i32::MAX; LN], [i32::MIN; LN]);
    for (i, v) in e.iter().enumerate().take(end).skip(start) {
        for l in 0..LN {
            if v[l] != i32::MIN {
                let x = v[l] + s[l] * i as i32;
                lo[l] = lo[l].min(x);
                hi[l] = hi[l].max(x);
            }
        }
    }
    let spread = (0..LN)
        .filter(|&l| hi[l] != i32::MIN)
        .map(|l| hi[l] - lo[l])
        .max()
        .unwrap_or(0);
    let frame = std::array::from_fn(|l| if hi[l] == i32::MIN { 0 } else { hi[l] });
    Block {
        start,
        end,
        frame,
        spread: if cfg.blocks { spread } else { cfg.spread },
    }
}

/// The blocks with a pair's terms that just exceed a power of two cut down: each block of one series whose pair with
/// the other's first block has P > L/2 terms (L = P rounded up to a power of two) while its outputs fit in L/2 is cut
/// where that pair's terms become L/2, its last few coefficients a block of their own (a small pair). Kept for each
/// series when the estimated cost falls (an FFT length halved).
#[allow(clippy::too_many_arguments)]
fn shorten<S: Simd, E: Expansion<S>>(
    ba: Vec<Block>,
    bb: Vec<Block>,
    ea: &[[i32; LN]],
    eb: &[[i32; LN]],
    s: &[i32; LN],
    n: usize,
    cfg: &Cfg,
) -> (Vec<Block>, Vec<Block>) {
    let (mut ba, mut bb) = (ba, bb);
    for side in 0..2 {
        let (xs, ys, ex) = if side == 0 { (&ba, &bb, ea) } else { (&bb, &ba, eb) };
        let y0 = &ys[0];
        let mut cut: Vec<Block> = Vec::with_capacity(xs.len() + 1);
        for x in xs {
            let o = x.start + y0.start;
            let fits = o < n && {
                let (la, lb) = ((x.end - x.start).min(n - o), (y0.end - y0.start).min(n - o));
                let p = la + lb - 1;
                let l = p.next_power_of_two();
                let at = x.start + (l / 2 + 1).saturating_sub(lb);
                if p > l / 2 && n - o <= l / 2 && at > x.start && at < x.start + la {
                    cut.push(block_of(ex, s, x.start, at, cfg));
                    cut.push(block_of(ex, s, at, x.end, cfg));
                    true
                } else {
                    false
                }
            };
            if !fits {
                cut.push(x.clone());
            }
        }
        if cut.len() > xs.len() {
            let c0 = cost::<S, E>(&ba, &bb, n, cfg);
            let c1 = if side == 0 {
                cost::<S, E>(&cut, &bb, n, cfg)
            } else {
                cost::<S, E>(&ba, &cut, n, cfg)
            };
            if c1 < c0 {
                if side == 0 {
                    ba = cut;
                } else {
                    bb = cut;
                }
            }
        }
    }
    (ba, bb)
}

/// A block pair's digits: t per coefficient (even), W = 16 t - 2 >= prec + spread + 5 bits, which keeps every
/// coefficient to 2^-(prec + 1) of itself, and the weights q0..=2t-2 formed (nq of them, even): those below sum to
/// under 2^-prec of the smallest term, 2^(2W - h_a - h_b - 2). None past T_MAX digits, which the digits' scales and
/// parts_of's limbs do not hold.
struct Plan {
    t: usize,
    w: i32,
    q0: usize,
    nq: usize,
}

fn plan(cfg: &Cfg, ha: i32, hb: i32, la: usize, lb: usize) -> Option<Plan> {
    let t = ((cfg.prec + ha.max(hb) + 7 + DB - 1) / DB) as usize;
    let t = t + t % 2;
    if t > T_MAX {
        return None;
    }
    let w = DB * t as i32 - 2;
    let lg = ((t * la.min(lb)) as f64).log2().ceil() as i32;
    let q0 = (((2 * w - ha - hb - 2 - cfg.prec - 14 - lg) / DB).max(0) as usize).min(2 * t - 2);
    let nq = (2 * t - 1 - q0).div_ceil(2) * 2;
    Some(Plan { t, w, q0, nq })
}

/// The estimated seconds of the block pairs reaching below n, per pair: 0.76 us per coefficient's digits (octo-double;
/// in proportion to the parts), 6.5 ns per butterfly of a transform's slab (t forward slabs, nq / 2 inverse), 6.2 ns
/// per digit product at each of the L/2 + 1 frequencies, and 1.1 us per output index (in proportion to the parts),
/// measured on an M5 at n = 251; a pair formed term by term costs E::PROD_S per product.
fn cost<S: Simd, E: Expansion<S>>(ba: &[Block], bb: &[Block], n: usize, cfg: &Cfg) -> f64 {
    let np = E::NP as f64 / 8.0;
    let mut c = 0.0;
    for xa in ba {
        for xb in bb {
            let o = xa.start + xb.start;
            if o >= n {
                continue;
            }
            let (la, lb) = ((xa.end - xa.start).min(n - o), (xb.end - xb.start).min(n - o));
            let lc = (la + lb - 1).min(n - o);
            let l = (la + lb - 1).next_power_of_two();
            let Some(pl) = plan(cfg, xa.spread, xb.spread, la, lb) else {
                c += E::PROD_S * (la * lb) as f64;
                continue;
            };
            let prods: usize = (pl.q0..=2 * pl.t - 2)
                .map(|q| q.min(pl.t - 1) - q.saturating_sub(pl.t - 1) + 1)
                .sum();
            let bfly = (l / 2) as f64 * (l as f64).log2().max(1.0);
            c += 0.76e-6 * np * (la + lb) as f64
                + 6.5e-9 * (pl.t + pl.nq / 2) as f64 * bfly
                + 6.2e-9 * (l / 2 + 1) as f64 * prods as f64
                + 1.1e-6 * np * lc as f64;
        }
    }
    c
}

/// 2^e for e in [-1022, 1023]
#[inline(always)]
fn pow2(e: i32) -> f64 {
    f64::from_bits(((e + 1023) as u64) << 52)
}

/// x 2^n with one rounding (musl's scalbn): the factor applied in steps that keep the intermediate normal, so a
/// result past f64's range is infinite and one below it rounds to a subnormal or zero once
fn scalbn(mut x: f64, mut n: i32) -> f64 {
    const SUB: i32 = 1022 - 53;
    if n > 1023 {
        x *= pow2(1023);
        n -= 1023;
        if n > 1023 {
            x *= pow2(1023);
            n = (n - 1023).min(1023);
        }
    } else if n < -1022 {
        x *= pow2(-SUB);
        n += SUB;
        if n < -1022 {
            x *= pow2(-SUB);
            n = (n + SUB).max(-1022);
        }
    }
    x * pow2(n)
}

/// lane l of every part of v times 2^e\[l\] (`scalbn`)
fn scale_lanes<S: Simd, E: Expansion<S>>(v: &E, e: &[i32; LN]) -> E {
    let p: Vec<V8<S>> = (0..E::NP)
        .map(|i| V8::from_array(std::array::from_fn(|l| scalbn(v.part(i).to_array()[l], e[l]))))
        .collect();
    E::from_parts(&p)
}

/// per-lane factors f1, f2, each a normal power of two, with f1 f2 = 2^e (|e| <= 2044)
#[inline(always)]
fn pow2_split(e: &[i32; LN]) -> (L8, L8) {
    (
        std::array::from_fn(|l| pow2(e[l] / 2)),
        std::array::from_fn(|l| pow2(e[l] - e[l] / 2)),
    )
}

/// 1.5 2^52: (x + MAGIC) - MAGIC is x rounded to an integer (to nearest, ties to even) for |x| < 2^51
const MAGIC: f64 = 6755399441055744.0;

/// x rounded to an integer on every lane (|x| < 2^51)
#[inline(always)]
fn rnd<S: Simd>(x: V8<S>) -> V8<S> {
    let m = V8::splat(MAGIC);
    x.add(m).sub(m)
}

/// The digits of a coefficient's 8 lanes: lane l of x times 2^k\[l\], each part rounded to an integer (so the lane is
/// within NP / 2 of x 2^k), as t balanced 16-bit digits d\[r\] (|d| <= 2^15). Each part p is split exactly into digits
/// from its largest lane's top digit down to its smallest lane's lowest one, each digit the nearest integer to the
/// remainder over 2^(16 r) and the remainder then reduced by it (exact, since it is the remainder's low bits); the
/// digit sums are then carried into balanced form. |x 2^k| must be below 2^(16 t - 1). Public for the tests.
#[doc(hidden)]
pub fn digits<S: Simd, E: Expansion<S>>(x: &E, k: &[i32; LN], t: usize, d: &mut [V8<S>]) {
    let (f1, f2) = pow2_split(k);
    let (f1, f2) = (V8::from_array(f1), V8::from_array(f2));
    for dr in d.iter_mut().take(t) {
        *dr = V8::zero();
    }
    let (one, inf) = (V8::splat(1.0), V8::splat(f64::INFINITY));
    for pi in 0..E::NP {
        let mut rem = x.part(pi).mul(f1).mul(f2);
        let a = rem.abs();
        let amax = a.hmax();
        if amax < 0.5 {
            continue;
        }
        let amin = -a.ge(one).sel(a, inf).neg().hmax();
        let rhi = (((expo(amax) - 1).max(0) / DB) as usize).min(t - 1);
        let rlo = if amin.is_finite() {
            ((expo(amin) - 54).max(0) / DB) as usize
        } else {
            0
        };
        for r in (rlo.min(rhi)..=rhi).rev() {
            let q = rnd(rem.mul(V8::splat(pow2(-DB * r as i32))));
            d[r] = d[r].add(q);
            rem = rem.sub(q.mul(V8::splat(pow2(DB * r as i32))));
        }
    }
    let (ir, r16) = (V8::splat(IR16), V8::splat(R16));
    let mut carry = V8::zero();
    for dr in d.iter_mut().take(t) {
        let v = dr.add(carry);
        let hi = rnd(v.mul(ir));
        *dr = v.sub(hi.mul(r16));
        carry = hi;
    }
    // a coefficient scaled out of f64's range (the control MUT_ZERO_LANE) leaves NaNs, which pair's 1/4 check rejects
    debug_assert!(
        carry.to_array().iter().all(|&c| c == 0.0 || !c.is_finite()),
        "digits: |x 2^k| too large"
    );
}

/// The integer v = sum_q d\[q\]\[ln\] 2^(16 q) (balanced digits of lane ln) times 2^e as out.len() parts: |v| cut
/// into chunks of 53 bits from its top bit down, each part a chunk with v's sign, so the parts do not overlap and their
/// sum is v 2^e truncated below the last chunk (2^-(53 out.len()) of v or less). Each chunk is scaled with one
/// rounding (`scalbn`), so below 2^-1022 each part rounds to the subnormal grid on its own.
fn parts_of(d: &[L8], ln: usize, e: i32, out: &mut [f64]) {
    const NL: usize = T_MAX / 2 + 3;
    let nl = d.len().div_ceil(4) + 1;
    assert!(nl <= NL, "parts_of: {} digits", d.len());
    let mut w = [0u64; NL];
    let mut carry: i128 = 0;
    for (li, wl) in w.iter_mut().enumerate().take(nl) {
        let mut v = carry;
        for j in 0..4 {
            if let Some(dq) = d.get(4 * li + j) {
                v += (dq[ln] as i64 as i128) << (16 * j);
            }
        }
        *wl = v as u64;
        carry = v >> 64;
    }
    let neg = carry < 0;
    if neg {
        let mut c = true;
        for wl in w.iter_mut().take(nl) {
            let (r, cc) = (!*wl).overflowing_add(c as u64);
            *wl = r;
            c = cc;
        }
    }
    let Some(top) = (0..nl).rev().find(|&i| w[i] != 0) else {
        out.fill(0.0);
        return;
    };
    let hb = 64 * top as i64 + 63 - w[top].leading_zeros() as i64;
    let bit = |b: i64| -> u64 {
        // bits b..b + 53 of |v| (zero below bit 0)
        if b + 53 <= 0 {
            return 0;
        }
        let (bb, sh) = if b < 0 { (0, -b) } else { (b, 0) };
        let (li, bo) = ((bb / 64) as usize, (bb % 64) as u32);
        let lo = w[li] >> bo;
        let hi = if bo > 0 && li + 1 < nl {
            w[li + 1] << (64 - bo)
        } else {
            0
        };
        (((lo | hi) & ((1u64 << 53) - 1)) << sh) & ((1u64 << 53) - 1)
    };
    let sg = if neg { -1.0 } else { 1.0 };
    for (j, o) in out.iter_mut().enumerate() {
        let b = hb - 52 - 53 * j as i64;
        let c = bit(b);
        *o = if c == 0 {
            0.0
        } else {
            let ex = (b + e as i64).clamp(-4000, 4000) as i32;
            scalbn(sg * c as f64, ex)
        };
    }
}

/// FFT tables of length 2^m: twiddles exp(-2 pi i k / L), k < L/2, and the bit reversal
struct Tables {
    tw: Vec<(f64, f64)>,
    rev: Vec<usize>,
}

fn tables(m: usize) -> &'static Tables {
    static T: OnceLock<Vec<Tables>> = OnceLock::new();
    &T.get_or_init(|| {
        (0..=LMAX_LOG2)
            .map(|m| {
                let l = 1usize << m;
                let tw = (0..l / 2)
                    .map(|k| {
                        let a = -2.0 * std::f64::consts::PI * k as f64 / l as f64;
                        (a.cos(), a.sin())
                    })
                    .collect();
                let rev = (0..l)
                    .map(|i| {
                        if m == 0 {
                            0
                        } else {
                            i.reverse_bits() >> (usize::BITS as usize - m)
                        }
                    })
                    .collect();
                Tables { tw, rev }
            })
            .collect()
    })[m]
}

/// a row of a slab: 8 lanes' real parts, then their imaginary parts
type C8<S> = [V8<S>; 2];

#[inline(always)]
fn c0<S: Simd>() -> C8<S> {
    [V8::zero(), V8::zero()]
}

/// in-place forward DIF FFT of one slab of L rows (rows nz.. zero on input); output in bit-reversed row order
fn fft_dif<S: Simd>(x: &mut [C8<S>], tb: &Tables, nz: usize) {
    let l = x.len();
    let mut h = l / 2;
    let mut first = true;
    while h >= 1 {
        let step = l / (2 * h);
        for g in (0..l).step_by(2 * h) {
            let (lo, hi) = x[g..g + 2 * h].split_at_mut(h);
            for (k, (a, b)) in lo.iter_mut().zip(hi.iter_mut()).enumerate() {
                let (wr, wi) = tb.tw[k * step];
                let (wr, wi) = (V8::splat(wr), V8::splat(wi));
                if first && g + k + h >= nz {
                    if g + k >= nz {
                        continue;
                    }
                    let (ur, ui) = (a[0], a[1]);
                    *b = [ur.fma(wr, ui.mul(wi).neg()), ur.fma(wi, ui.mul(wr))];
                } else {
                    let (ur, ui, vr, vi) = (a[0], a[1], b[0], b[1]);
                    *a = [ur.add(vr), ui.add(vi)];
                    let (dr, di) = (ur.sub(vr), ui.sub(vi));
                    *b = [dr.fma(wr, di.mul(wi).neg()), dr.fma(wi, di.mul(wr))];
                }
            }
        }
        first = false;
        h /= 2;
    }
}

/// in-place inverse DIT FFT (unnormalized, conjugate twiddles) of one slab, bit-reversed rows to natural rows
fn ifft_dit<S: Simd>(x: &mut [C8<S>], tb: &Tables) {
    let l = x.len();
    let mut h = 1;
    while h < l {
        let step = l / (2 * h);
        for g in (0..l).step_by(2 * h) {
            let (lo, hi) = x[g..g + 2 * h].split_at_mut(h);
            for (k, (a, b)) in lo.iter_mut().zip(hi.iter_mut()).enumerate() {
                let (wr, wi) = tb.tw[k * step];
                let (wr, wi) = (V8::splat(wr), V8::splat(wi));
                let (vr, vi) = (b[0], b[1]);
                let tr = vr.fma(wr, vi.mul(wi));
                let ti = vi.fma(wr, vr.mul(wi).neg());
                let (ur, ui) = (a[0], a[1]);
                *a = [ur.add(tr), ui.add(ti)];
                *b = [ur.sub(tr), ui.sub(ti)];
            }
        }
        h *= 2;
    }
}

/// scratch of a block pair
struct Work<S: Simd> {
    xs: Vec<C8<S>>,
    ys: Vec<C8<S>>,
    vs: Vec<C8<S>>,
    dig: Vec<V8<S>>,
    dl: Vec<L8>,
    xh: Vec<[V8<S>; 3]>,
    yh: Vec<[V8<S>; 2]>,
    cq: Vec<V8<S>>,
}

impl<S: Simd> Work<S> {
    fn new() -> Self {
        Work {
            xs: Vec::new(),
            ys: Vec::new(),
            vs: Vec::new(),
            dig: Vec::new(),
            dl: Vec::new(),
            xh: Vec::new(),
            yh: Vec::new(),
            cq: Vec::new(),
        }
    }
}

/// a block's first `len` coefficients as t digits in t/2 slabs of L rows (digit 2u in the real parts and 2u + 1 in
/// the imaginary parts of slab u), then each slab's forward FFT
#[allow(clippy::too_many_arguments)]
fn load<S: Simd, E: Expansion<S>>(
    a: &[E],
    len: usize,
    start: usize,
    frame: &[i32; LN],
    s: &[i32; LN],
    t: usize,
    l: usize,
    xs: &mut Vec<C8<S>>,
    dig: &mut Vec<V8<S>>,
    tb: &Tables,
    mutate: u8,
) {
    let w = DB * t as i32 - 2;
    xs.clear();
    xs.resize(t / 2 * l, c0());
    dig.resize(t, V8::zero());
    for (i, v) in a.iter().enumerate().take(len) {
        // a zero lane is not scaled: its scale can lie outside f64's range, and 0 times infinity is not zero
        let hi = v.part(0).to_array();
        let k: [i32; LN] = std::array::from_fn(|ln| {
            if hi[ln] == 0.0 && mutate != MUT_ZERO_LANE {
                0
            } else {
                s[ln] * (start + i) as i32 + w - frame[ln]
            }
        });
        digits(v, &k, t, dig);
        for u in 0..t / 2 {
            xs[u * l + i] = [dig[2 * u], dig[2 * u + 1]];
        }
    }
    for slab in xs.chunks_exact_mut(l) {
        fft_dif(slab, tb, len);
    }
}

/// the spectra (twice them) of digits 2u and 2u + 1 at frequency f from slab rows f (z) and -f (w): z + conj w, and
/// -i (z - conj w), each as (re, im, -im)
#[inline(always)]
fn unpack3<S: Simd>(z: &C8<S>, w: &C8<S>) -> ([V8<S>; 3], [V8<S>; 3]) {
    let (zr, zi, wr, wi) = (z[0], z[1], w[0], w[1]);
    let (ei, oi) = (zi.sub(wi), wr.sub(zr));
    ([zr.add(wr), ei, ei.neg()], [zi.add(wi), oi, oi.neg()])
}

/// `unpack3` without the negated imaginary parts
#[inline(always)]
fn unpack2<S: Simd>(z: &C8<S>, w: &C8<S>) -> ([V8<S>; 2], [V8<S>; 2]) {
    let (zr, zi, wr, wi) = (z[0], z[1], w[0], w[1]);
    ([zr.add(wr), zi.sub(wi)], [zi.add(wi), wr.sub(zr)])
}

/// (ar, ai) += x y, x = (re, im, -im), y = (re, im)
#[inline(always)]
fn cmac<S: Simd>(ar: &mut V8<S>, ai: &mut V8<S>, x: &[V8<S>; 3], y: &[V8<S>; 2]) {
    *ar = x[0].fma(y[0], x[2].fma(y[1], *ar));
    *ai = x[0].fma(y[1], x[1].fma(y[0], *ai));
}

/// C_q = sum_(r + r' = q) X_r Y_r' for q = q0..=2t-2 at one frequency, x\[r\] holding (re, im, -im) of digit r and
/// y\[r\] (re, im); C_q into c\[2(q - q0)\] (re), c\[2(q - q0) + 1\] (im). Weights in pairs q, q + 1, which share
/// each x_r, and y_(q+1-r) is the y_(q-r') of the step before.
#[inline(always)]
fn conv<S: Simd>(x: &[[V8<S>; 3]], y: &[[V8<S>; 2]], t: usize, q0: usize, c: &mut [V8<S>]) {
    let qe = 2 * t - 2;
    let mut q = q0;
    while q < qe {
        let (lo, hi) = (q.saturating_sub(t - 1), q.min(t - 1));
        let (lo1, hi1) = ((q + 1).saturating_sub(t - 1), (q + 1).min(t - 1));
        let (mut ar, mut ai, mut br, mut bi) = (V8::zero(), V8::zero(), V8::zero(), V8::zero());
        if lo < lo1 {
            cmac(&mut ar, &mut ai, &x[lo], &y[q - lo]);
        }
        let mut p = y[q + 1 - lo1];
        for (xv, y0) in x[lo1..=hi].iter().zip(y[q - hi..=q - lo1].iter().rev()) {
            ar = xv[0].fma(y0[0], xv[2].fma(y0[1], ar));
            ai = xv[0].fma(y0[1], xv[1].fma(y0[0], ai));
            br = xv[0].fma(p[0], xv[2].fma(p[1], br));
            bi = xv[0].fma(p[1], xv[1].fma(p[0], bi));
            p = *y0;
        }
        if hi1 > hi {
            cmac(&mut br, &mut bi, &x[hi1], &y[q + 1 - hi1]);
        }
        let j = 2 * (q - q0);
        c[j] = ar;
        c[j + 1] = ai;
        c[j + 2] = br;
        c[j + 3] = bi;
        q += 2;
    }
    if q == qe {
        let (lo, hi) = (q.saturating_sub(t - 1), q.min(t - 1));
        let (mut ar, mut ai) = (V8::zero(), V8::zero());
        for (xv, yv) in x[lo..=hi].iter().zip(y[q - hi..=q - lo].iter().rev()) {
            cmac(&mut ar, &mut ai, xv, yv);
        }
        let j = 2 * (q - q0);
        c[j] = ar;
        c[j + 1] = ai;
    }
}

/// One block pair by convolution: x (block xa of a, from xa.start) times y (block xb of b), output indices
/// o..o + nout added into acc. False, with acc unchanged, when an inverse transform's value lies 1/4 or more from its
/// integer (or is not a number), so the caller forms the pair term by term.
#[allow(clippy::too_many_arguments)]
fn pair<S: Simd, E: Expansion<S>>(
    x: &[E],
    y: &[E],
    xa: &Block,
    xb: &Block,
    s: &[i32; LN],
    nout: usize,
    o: usize,
    cfg: &Cfg,
    e2: i32,
    acc: &mut [E::Acc],
    st: &mut Stats,
    ws: &mut Work<S>,
) -> bool {
    let (la, lb) = (x.len().min(nout), y.len().min(nout));
    let lc = (la + lb - 1).min(nout);
    let m = (la + lb - 1).next_power_of_two().trailing_zeros() as usize;
    debug_assert!(m <= LMAX_LOG2, "series: block pair of {} terms", la + lb - 1);
    let l = 1usize << m;
    let tb = tables(m);
    let Plan { t, w, q0, nq } = plan(cfg, xa.spread, xb.spread, la, lb).expect("a pair within T_MAX digits");
    st.digits = st.digits.max(t);
    load(
        x,
        la,
        xa.start,
        &xa.frame,
        s,
        t,
        l,
        &mut ws.xs,
        &mut ws.dig,
        tb,
        cfg.mutate,
    );
    load(
        y,
        lb,
        xb.start,
        &xb.frame,
        s,
        t,
        l,
        &mut ws.ys,
        &mut ws.dig,
        tb,
        cfg.mutate,
    );
    ws.vs.clear();
    ws.vs.resize(nq / 2 * l, c0());
    ws.xh.resize(t, [V8::zero(); 3]);
    ws.yh.resize(t, [V8::zero(); 2]);
    ws.cq.resize(2 * nq, V8::zero());
    // the padding weight (nq past 2t - 1 - q0), which conv does not write
    for c in ws.cq[2 * (2 * t - 1 - q0)..].iter_mut() {
        *c = V8::zero();
    }
    for f in 0..=l / 2 {
        let (pf, pg) = (tb.rev[f], tb.rev[(l - f) & (l - 1)]);
        for u in 0..t / 2 {
            (ws.xh[2 * u], ws.xh[2 * u + 1]) = unpack3(&ws.xs[u * l + pf], &ws.xs[u * l + pg]);
            (ws.yh[2 * u], ws.yh[2 * u + 1]) = unpack2(&ws.ys[u * l + pf], &ws.ys[u * l + pg]);
        }
        conv(&ws.xh, &ws.yh, t, q0, &mut ws.cq);
        // the inverse's input at rows f and -f: C_(2u) + i C_(2u+1), and at -f the conjugates' combination
        for u in 0..nq / 2 {
            let (er, ei, or, oi) = (ws.cq[4 * u], ws.cq[4 * u + 1], ws.cq[4 * u + 2], ws.cq[4 * u + 3]);
            let (rf, rg) = (u * l + pf, u * l + pg);
            if pf == pg {
                ws.vs[rf] = [er, or];
            } else {
                ws.vs[rf] = [er.sub(oi), ei.add(or)];
                ws.vs[rg] = [er.add(oi), or.sub(ei)];
            }
        }
    }
    for slab in ws.vs.chunks_exact_mut(l) {
        ifft_dit(slab, tb);
    }
    // each unpacked spectrum was twice its value, so each product four times: the inverse is scaled by 1/(4L)
    let sc = 0.25 / l as f64;
    let scv = V8::splat(sc);
    // every value used within 1/4 of its integer, checked before any is added
    let mut frac = V8::zero();
    // lanes whose distance from the integer is not a number (a NaN or infinity in a factor), which V8::max can drop
    let mut bad = V8::zero().ne(V8::zero());
    for mi in 0..lc {
        for qi in 0..nq {
            let z = ws.vs[qi / 2 * l + mi][qi % 2].mul(scv);
            let e = z.sub(rnd(z)).abs();
            bad = bad.or(e.ne(e));
            frac = frac.max(e);
        }
    }
    let fr = if bad.bits() != 0 { f64::INFINITY } else { frac.hmax() };
    st.max_frac = st.max_frac.max(fr);
    if fr.is_nan() || fr >= 0.25 {
        return false;
    }
    let nd = 2 * t + 2 - q0;
    ws.dig.resize(nd, V8::zero());
    ws.dl.resize(nd, [0.0; LN]);
    let (ir, r16) = (V8::splat(IR16), V8::splat(R16));
    // the control MUT_SLOPE: the outputs unscaled with the slope plus one
    let ds = (cfg.mutate == MUT_SLOPE) as i32;
    let mut pv = [[0.0f64; 8]; LN];
    for mi in 0..lc {
        let mut carry = V8::zero();
        for qi in 0..nd {
            let mut v = carry;
            if qi < nq {
                v = v.add(rnd(ws.vs[qi / 2 * l + mi][qi % 2].mul(scv)));
            }
            let hi = rnd(v.mul(ir));
            ws.dig[qi] = v.sub(hi.mul(r16));
            carry = hi;
        }
        debug_assert!(
            carry.to_array().iter().all(|&c| c == 0.0),
            "series: digits past the top"
        );
        let k = o + mi;
        let e0: [i32; LN] = std::array::from_fn(|ln| {
            xa.frame[ln] + xb.frame[ln] - 2 * w - (s[ln] + ds) * k as i32 + DB * q0 as i32 + e2
        });
        // the chunks' weights 2^(48 c + e0): near the top of f64's range a balanced chunk can exceed f64::MAX where
        // the value does not (the digits' signs differ), so there the exact cut below
        let nc = nd.div_ceil(3);
        let top = e0.iter().copied().max().unwrap_or(0) + 48 * nc as i32;
        if E::NP <= 4 && (top <= 960 || cfg.mutate == MUT_CHUNK_TOP) {
            // double- and quad-double: the integer in chunks of three digits, each exact in f64 (an integer below
            // 2^48), the top chunk first, each scaled by its weight 2^(48 c + e0) and added into the accumulator, which
            // rounds the sum to the expansion's precision (2^-(53 NP) of the value, about)
            let (r16, r32) = (V8::splat(R16), V8::splat(R16 * R16));
            for c in (0..nc).rev() {
                let q = 3 * c;
                let mut v = ws.dig[q];
                if q + 1 < nd {
                    v = v.add(ws.dig[q + 1].mul(r16));
                }
                if q + 2 < nd {
                    v = v.add(ws.dig[q + 2].mul(r32));
                }
                if v.ne(V8::zero()).bits() == 0 {
                    continue;
                }
                let ex: [i32; LN] = std::array::from_fn(|ln| (e0[ln] + 48 * c as i32).clamp(-2044, 2044));
                let (f1, f2) = pow2_split(&ex);
                let mut parts = [V8::zero(); 4];
                parts[0] = v.mul(V8::from_array(f1)).mul(V8::from_array(f2));
                E::acc_parts(&mut acc[k], &parts[..E::NP]);
            }
            continue;
        }
        // octo-double: the integer at index k on each lane, digit 0 of weight 2^e0, as eight 53-bit parts
        for (dl, d) in ws.dl.iter_mut().zip(&ws.dig) {
            *dl = d.to_array();
        }
        for (ln, pl) in pv.iter_mut().enumerate() {
            parts_of(&ws.dl[..nd], ln, e0[ln], &mut pl[..E::NP]);
        }
        let parts: [V8<S>; 8] = std::array::from_fn(|q| V8::from_array(std::array::from_fn(|ln| pv[ln][q])));
        E::acc_parts(&mut acc[k], &parts[..E::NP]);
    }
    true
}

/// `Lane::block_mul` of an expansion lane: every product x_i y_j with i + j < acc.len() into acc\[i + j\] by `mullow`
pub(crate) fn block_mul_expansion<S: Simd, E: Expansion<S>>(x: &[E], y: &[E], acc: &mut [E::Acc]) {
    if !x.is_empty() && !y.is_empty() {
        mullow(x, y, acc.len(), &Cfg::default(), acc);
    }
}

/// `Lane::block_mul` of a dual lane with value v and tangent d over an expansion E: the value's product into the
/// accumulators' first parts, the tangent's v_x d_y + d_x v_y into their second
pub(crate) fn block_mul_dual<S: Simd, E: Expansion<S>, L: Copy>(
    x: &[L],
    y: &[L],
    acc: &mut [(E::Acc, E::Acc)],
    vd: impl Fn(&L) -> (E, E),
) {
    if x.is_empty() || y.is_empty() {
        return;
    }
    let n = acc.len();
    let cfg = Cfg::default();
    let (xv, xd): (Vec<E>, Vec<E>) = x.iter().map(&vd).unzip();
    let (yv, yd): (Vec<E>, Vec<E>) = y.iter().map(&vd).unzip();
    let (mut av, mut ad): (Vec<E::Acc>, Vec<E::Acc>) = acc.iter().copied().unzip();
    mullow(&xv, &yv, n, &cfg, &mut av);
    mullow(&xv, &yd, n, &cfg, &mut ad);
    mullow(&xd, &yv, n, &cfg, &mut ad);
    for (a, (v, d)) in acc.iter_mut().zip(av.into_iter().zip(ad)) {
        *a = (v, d);
    }
}

impl<S: Simd> Du<S> {
    pub(crate) fn split(&self) -> (DV<S>, DV<S>) {
        (self.v, self.d)
    }
}
impl<S: Simd> Qu<S> {
    pub(crate) fn split(&self) -> (QV<S>, QV<S>) {
        (self.v, self.d)
    }
}
impl<S: Simd> Ou<S> {
    pub(crate) fn split(&self) -> (OV<S>, OV<S>) {
        (self.v, self.d)
    }
}

/// `Relaxed::mutate`: the first square formed left out (the control of the relaxed products' checks)
pub const RELAXED_MUT_DROP: u8 = 1;

/// The product c = x y of two series of fields (B lane vectors of a lane type T) whose coefficients become known one
/// order at a time (module doc): call `step(x, y, e)` at the end of each step e = 0, 1, 2, ... of the recurrence, once
/// x and y are final to order e - 1, and read c's coefficient of order k, or the sum of its terms i = lo..=hi, with
/// `sum` once steps 0..k - 1 are done. The terms with i >= d and k - i >= d come from the squares formed at those steps
/// and are the same for every range that contains them; the others are summed from x and y as they are when `sum` is
/// called, each lane vector's in the order i = lo..=hi after the squares' sum.
///
/// The squares' products are `Lane::block_mul`'s. On lanes without a fast one (`Lane::BLOCK_MIN` 0) there are no
/// squares, and `sum` is bitwise `field::cs_range`.
pub struct Relaxed<T: Lane, const B: usize> {
    /// acc\[b\]\[k\]: lane vector b's sum of the squares' terms of order k
    acc: Vec<Vec<T::Acc>>,
    /// the smallest square's side, a power of two; 0, none
    s0: usize,
    /// the next step to form
    next: usize,
    /// coefficients of the product
    len: usize,
    /// the control `RELAXED_MUT_DROP`, 0 off
    pub mutate: u8,
    /// squares formed, and their terms
    pub squares: usize,
    pub terms: u64,
}

impl<T: Lane, const B: usize> Relaxed<T, B> {
    /// a product of len coefficients (orders 0..len - 1) with squares of side T::BLOCK_MIN and up
    pub fn new(len: usize) -> Self {
        Self::with_min(len, T::BLOCK_MIN)
    }
    /// a product of len coefficients with squares of side s0 (rounded up to a power of two) and up; s0 = 0, none
    pub fn with_min(len: usize, s0: usize) -> Self {
        let s0 = if s0 == 0 { 0 } else { s0.next_power_of_two() };
        let acc = if s0 == 0 {
            Vec::new()
        } else {
            (0..B).map(|_| vec![T::acc0(); len]).collect()
        };
        Relaxed {
            acc,
            s0,
            next: 0,
            len,
            mutate: 0,
            squares: 0,
            terms: 0,
        }
    }
    /// the bound d: the terms with both indices d or more come from squares (usize::MAX without squares)
    pub fn direct_below(&self) -> usize {
        if self.s0 == 0 {
            usize::MAX
        } else {
            self.s0 + 1
        }
    }
    /// whether step e forms squares (`step`'s condition): e - 1 a multiple of s0 and at least 2 s0
    pub fn squares_at(&self, e: usize) -> bool {
        self.s0 > 0 && e > 2 * self.s0 && (e - 1).is_multiple_of(self.s0)
    }
    /// The squares formed at the end of step e (e = the next step; x and y final to order e - 1): those of side
    /// 2^p >= s0 with (m + 1) 2^p = e - 1, the square at (m 2^p + 1, 2^p + 1) and, for m >= 2, its transpose. The B
    /// lane vectors are formed on rayon's threads when the squares are large enough; their bits do not depend on it.
    pub fn step(&mut self, x: &[Fl<T, B>], y: &[Fl<T, B>], e: usize) {
        assert_eq!(e, self.next, "Relaxed::step: step {e} after {}", self.next);
        self.next += 1;
        if self.s0 == 0 || e < 2 || B == 0 {
            return;
        }
        let len = self.len;
        let e1 = e - 1;
        // (i0, j0, side) of every square of this step whose first term is below len
        let mut sq: Vec<(usize, usize, usize)> = Vec::new();
        let mut s = self.s0;
        while 2 * s <= e1 {
            if e1.is_multiple_of(s) {
                let m = e1 / s - 1;
                if e + 1 < len {
                    sq.push((m * s + 1, s + 1, s));
                    if m >= 2 {
                        sq.push((s + 1, m * s + 1, s));
                    }
                }
            }
            s *= 2;
        }
        if sq.is_empty() {
            return;
        }
        assert!(
            x.len() >= e && y.len() >= e,
            "Relaxed::step: factors of {} and {} coefficients at step {e}",
            x.len(),
            y.len()
        );
        if self.mutate == RELAXED_MUT_DROP && self.squares == 0 {
            sq.remove(0);
        }
        self.squares += sq.len();
        self.terms += sq.iter().map(|&(_, _, s)| (s * s) as u64).sum::<u64>();
        let work: usize = sq.iter().map(|&(_, _, s)| s).sum();
        let form = |b: usize, acc: &mut Vec<T::Acc>| {
            for &(i0, j0, s) in &sq {
                let o = i0 + j0;
                let n = (2 * s - 1).min(len - o);
                let xs: Vec<T> = x[i0..i0 + s].iter().map(|f| f.0[b]).collect();
                let ys: Vec<T> = y[j0..j0 + s].iter().map(|f| f.0[b]).collect();
                T::block_mul(&xs, &ys, &mut acc[o..o + n]);
            }
        };
        if B > 1 && work >= 64 {
            use rayon::prelude::*;
            self.acc.par_iter_mut().enumerate().for_each(|(b, a)| form(b, a));
        } else {
            for (b, a) in self.acc.iter_mut().enumerate() {
                form(b, a);
            }
        }
    }
    /// sum_(i=lo..=hi) x_i y_(k-i): the squares' terms of order k (all of those with i, k - i >= d lie in lo..=hi)
    /// and the others from x and y as they are now
    pub fn sum(&self, x: &[Fl<T, B>], y: &[Fl<T, B>], k: usize, lo: usize, hi: usize) -> Fl<T, B> {
        let mut out = Fl::<T, B>::zero();
        self.sum_into(&mut out, x, y, k, lo, hi);
        out
    }
    /// `sum` into out
    pub fn sum_into(&self, out: &mut Fl<T, B>, x: &[Fl<T, B>], y: &[Fl<T, B>], k: usize, lo: usize, hi: usize) {
        let d = self.direct_below();
        if self.s0 == 0 || k < 2 * d {
            crate::field::cs_range_into(out, x, y, k, lo, hi);
            return;
        }
        assert!(
            self.next >= k,
            "Relaxed::sum: order {k} before step {} is formed",
            k - 1
        );
        assert!(
            lo <= d && hi + d >= k,
            "Relaxed::sum: range {lo}..={hi} at order {k} cuts the squares' terms"
        );
        // the terms i < d, then i > k - d
        let (a1, b0) = (hi.min(d - 1), lo.max(k + 1 - d));
        for (b, o) in out.0.iter_mut().enumerate() {
            let mut a = self.acc[b][k];
            for i in lo..=a1 {
                T::acc_mut(&mut a, &x[i].0[b], &y[k - i].0[b]);
            }
            for i in b0..=hi {
                T::acc_mut(&mut a, &x[i].0[b], &y[k - i].0[b]);
            }
            *o = T::fin(a);
        }
    }
}
