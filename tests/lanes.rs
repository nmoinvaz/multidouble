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
