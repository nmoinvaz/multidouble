//! The 8-lane types against the scalar ones, bit for bit, on every backend this CPU runs (`simd::available()`:
//! avx512, avx2, sse2, neon, portable), so one run checks that they all agree.
#![allow(clippy::needless_range_loop)]
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::dv::{DotAcc, DV};
use multidouble::qd::QD;
use multidouble::qv::QV;
use multidouble::simd::{self, Kernel, Simd};
use multidouble::v8::V8;

const ROUNDS: usize = 4000;

fn same(a: f64, b: f64) -> bool {
    a.to_bits() == b.to_bits() || (a.is_nan() && b.is_nan())
}

fn dd8<S: Simd>(r: &mut Rng) -> ([DD; 8], DV<S>) {
    let x: [DD; 8] = std::array::from_fn(|_| r.dd(20));
    let hi: Vec<f64> = x.iter().map(|d| d.hi).collect();
    let lo: Vec<f64> = x.iter().map(|d| d.lo).collect();
    (x, DV::load(&hi, &lo))
}

/// k, a check that panics on a mismatch, run on every backend this CPU has
fn on_every_backend<K: Kernel<Output = ()> + Clone>(k: K) {
    let ran: Vec<&str> = simd::for_each_available(k).into_iter().map(|r| r.0).collect();
    assert_eq!(ran, simd::available());
    println!("checked on {ran:?}");
}

#[test]
fn backends_are_reported() {
    let all = simd::available();
    assert!(
        all.iter()
            .all(|n| ["avx512", "avx2", "sse2", "neon", "portable"].contains(n)),
        "{all:?}"
    );
    assert!(all.contains(&simd::isa()) && all.last() == Some(&"portable"));
    println!("backends {all:?}, dispatch picks {}", simd::isa());
}

/// a lane operation's result and the scalar result per lane
type Op<'a, S> = (V8<S>, &'a dyn Fn(usize) -> f64);

#[derive(Clone)]
struct V8MatchesF64;

impl Kernel for V8MatchesF64 {
    type Output = ();
    #[inline(always)]
    fn run<S: Simd>(self) {
        let mut r = Rng(11);
        for _ in 0..ROUNDS {
            let a: [f64; 8] = std::array::from_fn(|_| r.dd(40).hi);
            let b: [f64; 8] = std::array::from_fn(|_| r.dd(40).hi);
            let c: [f64; 8] = std::array::from_fn(|_| r.dd(40).hi);
            let (va, vb, vc) = (V8::<S>::from_array(a), V8::from_array(b), V8::from_array(c));
            let ops: [Op<S>; 8] = [
                (va.add(vb), &|j| a[j] + b[j]),
                (va.sub(vb), &|j| a[j] - b[j]),
                (va.mul(vb), &|j| a[j] * b[j]),
                (va.div(vb), &|j| a[j] / b[j]),
                (va.fma(vb, vc), &|j| a[j].mul_add(b[j], c[j])),
                (va.fms(vb, vc), &|j| a[j].mul_add(b[j], -c[j])),
                (va.abs().sqrt(), &|j| a[j].abs().sqrt()),
                (va.max(vb), &|j| a[j].max(b[j])),
            ];
            for (k, (v, f)) in ops.iter().enumerate() {
                let got = v.to_array();
                for j in 0..8 {
                    assert!(
                        same(got[j], f(j)),
                        "{}: op {k} lane {j}: {} vs {}",
                        S::NAME,
                        got[j],
                        f(j)
                    );
                }
            }
            let bc = va.bcast(3).to_array();
            assert!(bc.iter().all(|&x| same(x, a[3])), "{}: bcast", S::NAME);
            assert!(
                same(va.hmax(), a.iter().cloned().fold(f64::NEG_INFINITY, f64::max)),
                "{}: hmax",
                S::NAME
            );
        }
    }
}

#[test]
fn v8_matches_f64() {
    on_every_backend(V8MatchesF64);
}

/// Divisions that a quotient off by a fraction of an ulp gets wrong: a / b within t / B ulps of a midpoint between two
/// doubles (b = B 2^k, A 2^54 = B M - t for an odd M of 54 bits and a small t), divisors with a significand of all
/// ones, every pair of significands within 64 ulps of all ones (where `div_by`'s single correction has the least
/// margin), exact quotients, and every pair of special values (zeros, subnormals, the edges of `div_by`'s reciprocal
/// range, infinities, NaN).
fn div_cases() -> Vec<(f64, f64)> {
    let mut r = Rng(14);
    let mut v = Vec::new();
    let m54 = (1u64 << 54) - 1;
    let sign = |r: &mut Rng, x: f64| if r.next_u64() & 1 == 0 { x } else { -x };
    while v.len() < 40_000 {
        let m = (r.next_u64() & m54) | 1 << 53 | 1;
        // the inverse of m mod 2^64 by Newton's iteration, each step doubling the correct low bits
        let mut inv = m;
        for _ in 0..6 {
            inv = inv.wrapping_mul(2u64.wrapping_sub(m.wrapping_mul(inv)));
        }
        let t = (r.next_u64() % 64) as i64 - 32;
        let b = (t as u64).wrapping_mul(inv) & m54;
        if t == 0 || !(1u64 << 52..1u64 << 53).contains(&b) {
            continue;
        }
        let a = ((b as u128 * m as u128) as i128 - t as i128) >> 54;
        let (ea, eb) = ((r.next_u64() % 200) as i32 - 100, (r.next_u64() % 200) as i32 - 100);
        v.push((
            sign(&mut r, a as f64 * 2f64.powi(ea)),
            sign(&mut r, b as f64 * 2f64.powi(eb)),
        ));
    }
    for _ in 0..4000 {
        let e = (r.next_u64() % 1000) as i32 - 500;
        let ones = sign(&mut r, (2.0 - 2f64.powi(-52)) * 2f64.powi(e));
        v.push((r.dd(400).hi, ones));
        let (p, q) = ((r.next_u64() >> 38) as f64, (r.next_u64() >> 38) as f64 + 1.0);
        v.push((sign(&mut r, p * q * 2f64.powi(e / 2)), q));
    }
    let u = 2f64.powi(-52);
    for i in 1..=64 {
        for j in 1..=64 {
            let (a, b) = (2.0 - i as f64 * u, 2.0 - j as f64 * u);
            v.push((a, b));
            v.push((sign(&mut r, a * 2f64.powi(300)), sign(&mut r, b * 2f64.powi(-170))));
        }
    }
    let lo = 2f64.powi(-500);
    let hi = 2f64.powi(500);
    let special = [
        0.0,
        f64::MIN_POSITIVE,
        f64::MIN_POSITIVE / 3.0,
        5e-324,
        lo,
        lo * (1.0 - 2f64.powi(-53)),
        lo * (1.0 + 2f64.powi(-52)),
        hi,
        hi * (1.0 - 2f64.powi(-53)),
        hi * (1.0 + 2f64.powi(-52)),
        1.0,
        3.0,
        2.0 - 2f64.powi(-52),
        1e300,
        f64::MAX,
        f64::INFINITY,
        f64::NAN,
    ];
    for &a in &special {
        for &b in &special {
            for (x, y) in [(a, b), (-a, b), (a, -b), (-a, -b)] {
                v.push((x, y));
            }
        }
    }
    v
}

/// the lanes of `div_cases` where div differs from `/`, bit for bit
#[inline(always)]
fn div_mismatches(cases: &[(f64, f64)], div: impl Fn([f64; 8], [f64; 8]) -> [f64; 8]) -> usize {
    let mut bad = 0;
    for c in cases.chunks(8) {
        let a: [f64; 8] = std::array::from_fn(|j| c.get(j).map_or(1.0, |p| p.0));
        let b: [f64; 8] = std::array::from_fn(|j| c.get(j).map_or(1.0, |p| p.1));
        let q = div(a, b);
        bad += (0..8).filter(|&j| !same(q[j], a[j] / b[j])).count();
    }
    bad
}

#[derive(Clone)]
struct DivByMatchesDiv;

impl Kernel for DivByMatchesDiv {
    type Output = ();
    #[inline(always)]
    fn run<S: Simd>(self) {
        let cases = div_cases();
        let bad = div_mismatches(
            &cases,
            #[inline(always)]
            |a, b| V8::<S>::from_array(a).div_by(V8::from_array(b).divisor()).to_array(),
        );
        assert_eq!(
            bad,
            0,
            "{}: div_by differs from div in {bad} of {} lanes",
            S::NAME,
            cases.len()
        );
    }
}

#[test]
fn div_by_matches_div() {
    on_every_backend(DivByMatchesDiv);
}

/// `div_by`'s algorithm in scalar f64 with the reciprocal y given: RN(a y) and one correction, `/` where |a| or |b|
/// is out of [2^-500, 2^500] or a is zero
fn div_model(a: f64, b: f64, y: f64) -> f64 {
    let range = 2f64.powi(-500)..=2f64.powi(500);
    if a == 0.0 || !range.contains(&a.abs()) || !range.contains(&b.abs()) {
        return a / b;
    }
    let q = a * y;
    (-b).mul_add(q, a).mul_add(y, q)
}

/// The model with y = RN(1/b) matches `/` on every case, on every target. Control: the same cases catch it with a
/// reciprocal one ulp off, and with the power of two below 1/b for a significand of all ones (`div_by` without the
/// last bit it sets there).
#[test]
fn div_model_matches_div_and_controls_are_caught() {
    let cases = div_cases();
    let model =
        |y: fn(f64) -> f64| div_mismatches(&cases, |a, b| std::array::from_fn(|j| div_model(a[j], b[j], y(b[j]))));
    let exact = model(|b| 1.0 / b);
    let off = model(|b| f64::from_bits((1.0 / b).to_bits() + 1));
    let ones = model(|b| {
        let sig = (1u64 << 52) - 1;
        if b.to_bits() & sig == sig {
            f64::from_bits((1.0 / b).to_bits() & !sig)
        } else {
            1.0 / b
        }
    });
    println!(
        "mismatches of {}: model {exact}, reciprocal one ulp off {off}, all ones unfixed {ones}",
        cases.len()
    );
    assert_eq!(exact, 0);
    assert!(off > 0 && ones > 0);
}

#[derive(Clone)]
struct DvMatchesDd;

impl Kernel for DvMatchesDd {
    type Output = ();
    #[inline(always)]
    fn run<S: Simd>(self) {
        let mut r = Rng(12);
        for _ in 0..ROUNDS {
            let (x, vx) = dd8::<S>(&mut r);
            let (y, vy) = dd8::<S>(&mut r);
            let s = r.dd(5).hi;
            let lanes = [vx + vy, vx - vy, vx * vy, vx / vy, -vx, vx.mul_f(s)];
            for j in 0..8 {
                let want = [x[j] + y[j], x[j] - y[j], x[j] * y[j], x[j] / y[j], -x[j], x[j].mul_f(s)];
                for (k, w) in want.iter().enumerate() {
                    let g = lanes[k].lane(j);
                    assert!(
                        same(g.hi, w.hi) && same(g.lo, w.lo),
                        "{}: op {k} lane {j}: {g:?} vs {w:?}",
                        S::NAME
                    );
                }
            }
            // the accumulator: a sum of products, against the same sum in scalar double-double to its own accuracy
            let acc = DotAcc::zero().add_prod(vx, vy).add_prod(vy, vy).add(vx).finish();
            for j in 0..8 {
                let w = x[j] * y[j] + y[j] * y[j] + x[j];
                let g = acc.lane(j);
                let scale = (x[j] * y[j]).hi.abs() + (y[j] * y[j]).hi.abs() + x[j].hi.abs();
                assert!(
                    ((g - w).to_f64()).abs() <= 1e-30 * scale,
                    "{}: acc lane {j}: {g:?} vs {w:?}",
                    S::NAME
                );
            }
        }
    }
}

#[test]
fn dv_matches_dd() {
    on_every_backend(DvMatchesDd);
}

#[derive(Clone)]
struct QvMatchesQd;

impl Kernel for QvMatchesQd {
    type Output = ();
    #[inline(always)]
    fn run<S: Simd>(self) {
        let mut r = Rng(13);
        let qd = |r: &mut Rng| {
            let a = r.dd(15);
            let b = r.dd(15);
            QD::from_dd(a).add_dd(DD::new(b.hi * 2f64.powi(-106), b.lo * 2f64.powi(-106)))
        };
        for _ in 0..ROUNDS / 4 {
            let x: [QD; 8] = std::array::from_fn(|_| qd(&mut r));
            let y: [QD; 8] = std::array::from_fn(|_| qd(&mut r));
            let (vx, vy) = (QV::<S>::from_lanes(&x), QV::from_lanes(&y));
            let lanes = [
                vx + vy,
                vx - vy,
                vx * vy,
                vx / vy,
                vx.ieee_add(vy),
                vx.accurate_mul(vy),
                vx.accurate_div(vy),
                vx.abs().sqrt(),
                vx.sqr(),
            ];
            for j in 0..8 {
                let want = [
                    x[j] + y[j],
                    x[j] - y[j],
                    x[j] * y[j],
                    x[j] / y[j],
                    x[j].ieee_add(y[j]),
                    x[j].accurate_mul(y[j]),
                    x[j].accurate_div(y[j]),
                    x[j].abs().sqrt(),
                    x[j].sqr(),
                ];
                for (k, w) in want.iter().enumerate() {
                    let g = lanes[k].lane(j);
                    assert!(
                        g.x.iter().zip(w.x.iter()).all(|(a, b)| same(*a, *b)),
                        "{}: op {k} lane {j}: {g:?} vs {w:?}",
                        S::NAME
                    );
                }
            }
        }
    }
}

#[test]
fn qv_matches_qd() {
    on_every_backend(QvMatchesQd);
}

/// Values with signed zeros in every part: the lanes must give the same zero signs as the scalar types. Negation
/// is the case that differed (the lanes formed 0 - x, which turns -(+0) into +0); the other operations run here too.
#[derive(Clone)]
struct SignedZerosMatchScalar;

/// double-doubles with a zero or signed-zero part: hi in {+0, -0, 1, -1, 2^-60}, lo in {+0, -0}
fn zero_dds() -> Vec<DD> {
    let mut v = Vec::new();
    for hi in [0.0, -0.0, 1.0, -1.0, 2f64.powi(-60)] {
        for lo in [0.0, -0.0] {
            v.push(DD { hi, lo });
        }
    }
    v
}

impl Kernel for SignedZerosMatchScalar {
    type Output = ();
    #[inline(always)]
    fn run<S: Simd>(self) {
        let zs = zero_dds();
        let qs: Vec<QD> = zs
            .iter()
            .flat_map(|d| {
                [
                    QD {
                        x: [d.hi, d.lo, 0.0, -0.0],
                    },
                    QD {
                        x: [d.hi, d.lo, -0.0, 0.0],
                    },
                ]
            })
            .collect();
        let dd_same = |g: DD, w: DD| same(g.hi, w.hi) && same(g.lo, w.lo);
        let qd_same = |g: QD, w: QD| g.x.iter().zip(w.x.iter()).all(|(a, b)| same(*a, *b));
        for &a in &zs {
            let x = V8::<S>::splat(a.hi);
            assert!(same(x.neg().to_array()[0], -a.hi), "{}: V8 neg {:e}", S::NAME, a.hi);
            for &b in &zs {
                let (va, vb) = (DV::<S>::splat(a), DV::<S>::splat(b));
                let mut ops = vec![("neg", -va, -a), ("add", va + vb, a + b), ("sub", va - vb, a - b)];
                ops.push(("mul", va * vb, a * b));
                if b.hi != 0.0 {
                    ops.push(("div", va / vb, a / b));
                }
                for (name, g, w) in ops {
                    for j in 0..8 {
                        assert!(
                            dd_same(g.lane(j), w),
                            "{}: DV {name} {a:?} {b:?}: {:?} vs {w:?}",
                            S::NAME,
                            g.lane(j)
                        );
                    }
                }
            }
        }
        for &a in &qs {
            for &b in &qs {
                let (va, vb) = (QV::<S>::from_lanes(&[a; 8]), QV::<S>::from_lanes(&[b; 8]));
                let mut ops = vec![("neg", -va, -a), ("add", va + vb, a + b), ("sub", va - vb, a - b)];
                ops.push(("ieee_add", va.ieee_add(vb), a.ieee_add(b)));
                ops.push(("mul", va * vb, a * b));
                for (name, g, w) in ops {
                    for j in 0..8 {
                        assert!(
                            qd_same(g.lane(j), w),
                            "{}: QV {name} {a:?} {b:?}: {:?} vs {w:?}",
                            S::NAME,
                            g.lane(j)
                        );
                    }
                }
            }
        }
        // control: negation as 0 - x, which the lanes used, misses the sign of -(+0)
        let z = DD::ZERO;
        let old = DV::<S> {
            hi: V8::zero().sub(V8::splat(z.hi)),
            lo: V8::zero().sub(V8::splat(z.lo)),
        };
        assert!(
            !dd_same(old.lane(0), -z),
            "{}: control: 0 - x matches -x on +0",
            S::NAME
        );
    }
}

#[test]
fn signed_zeros_match_the_scalar_types() {
    on_every_backend(SignedZerosMatchScalar);
}

/// Negation leaves no negative zero in a lower part: -(hi, +-0) has lo = +0 in DD and on DV's lanes, and every zero
/// lower part of a negated QD or QV is +0; the leading part's sign is flipped as for f64. to_f64 then keeps a zero's
/// sign (the leading part's). The control is the plain sign flip of every part, which leaves -0 in a lower part.
#[derive(Clone)]
struct NegationLowerZerosArePositive;

impl Kernel for NegationLowerZerosArePositive {
    type Output = ();
    #[inline(always)]
    fn run<S: Simd>(self) {
        let pos = |x: f64| same(x, 0.0);
        for a in zero_dds() {
            let n = -a;
            assert!(same(n.hi, -a.hi), "DD neg {a:?}: hi {:e}", n.hi);
            assert!(pos(n.lo), "DD neg {a:?}: lo {:e}", n.lo);
            assert!(same(n.to_f64(), -a.hi), "DD neg {a:?}: to_f64 {:e}", n.to_f64());
            let v = -DV::<S>::splat(a);
            for j in 0..8 {
                let l = v.lane(j);
                assert!(same(l.hi, n.hi) && same(l.lo, n.lo), "{}: DV neg {a:?}: {l:?}", S::NAME);
            }
            let q = QD {
                x: [a.hi, a.lo, 0.0, -0.0],
            };
            let nq = -q;
            assert!(same(nq.x[0], -a.hi), "QD neg {q:?}: {nq:?}");
            assert!(nq.x[1..].iter().all(|&x| pos(x)), "QD neg {q:?}: {nq:?}");
            assert!(same(nq.to_f64(), -a.hi), "QD neg {q:?}: to_f64 {:e}", nq.to_f64());
            let vq = -QV::<S>::from_lanes(&[q; 8]);
            let (f, nf) = (QV::<S>::from_lanes(&[q; 8]).to_v8().to_array(), vq.to_v8().to_array());
            for j in 0..8 {
                assert!(same(f[j], q.to_f64()), "{}: QV to_v8 {q:?}: {:e}", S::NAME, f[j]);
                assert!(same(nf[j], nq.to_f64()), "{}: QV to_v8 of -{q:?}: {:e}", S::NAME, nf[j]);
                let l = vq.lane(j);
                assert!(
                    l.x.iter().zip(nq.x.iter()).all(|(x, y)| same(*x, *y)),
                    "{}: QV neg {q:?}: {l:?}",
                    S::NAME
                );
            }
            // control: flipping every part's sign leaves -0 in the lower part of -(x, +0)
            if same(a.lo, 0.0) {
                let flip = DV::<S> {
                    hi: V8::splat(a.hi).neg(),
                    lo: V8::splat(a.lo).neg(),
                };
                assert!(
                    !pos(flip.lane(0).lo),
                    "{}: control: a plain sign flip gives lo +0 for {a:?}",
                    S::NAME
                );
            }
        }
    }
}

#[test]
fn negation_lower_zeros_are_positive() {
    on_every_backend(NegationLowerZerosArePositive);
}
