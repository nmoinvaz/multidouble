//! `sin`, `cos`, `tan` and `sin_cos` of the lane types `DV`, `QV` and `OV` against those of the scalar types `DD`, `QD`
//! and `OD`, bit for bit, on every backend this CPU runs (`simd::available()`). Each vector mixes the kinds of
//! argument lane by lane, so that one call has lanes in different buckets, with different series lengths, scalings,
//! quadrants and early returns: random arguments up to 2^52, results of arithmetic, small and tiny arguments, signed
//! zeros, near multiples of pi/2, near the reduction's correction of k, near and beyond 2^52, NaN and infinities, and
//! parts off the ladder. Every fourth vector has one kind on all lanes, for the paths where the lanes agree.
//!
//! The comparison is strict, NaN signs and payloads included: the lanes take a NaN lane's result from the scalar
//! function.
//!
//! Controls (feature `mutate`): with Horner's steps masked by lane 0's number of terms, lane 0's quadrant on every
//! lane, or the NaN lanes left to the lanes' arithmetic with their NaNs' signs flipped (`trig::mutate::LANE_TERMS`,
//! `LANE_QUADRANT`, `LANE_NAN`), the same check fails for each type on every backend.
#![allow(clippy::needless_range_loop)]
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::dv::DV;
use multidouble::od::OD;
use multidouble::ov::OV;
use multidouble::qd::QD;
use multidouble::qv::QV;
use multidouble::simd::{self, Kernel, Simd};
use std::ops::{Add, Div, Mul, Sub};

/// the reduction's threshold of |r_0|, RN(0.7854) (`trig::R_TH`), written out
#[allow(clippy::approx_constant)]
const R_TH: f64 = 0.7854;

fn same(a: f64, b: f64) -> bool {
    a.to_bits() == b.to_bits()
}

/// a scalar type: its parts, a renormalizing constructor, its arithmetic and its functions
trait Scalar:
    Copy + std::fmt::Debug + Add<Output = Self> + Sub<Output = Self> + Mul<Output = Self> + Div<Output = Self>
{
    const N: usize;
    fn parts(self) -> Vec<f64>;
    /// the parts as they are
    fn raw(p: &[f64]) -> Self;
    /// the parts renormalized
    fn sum(p: &[f64]) -> Self;
    fn pi() -> Self;
    fn tan(self) -> Self;
}

impl Scalar for DD {
    const N: usize = 2;
    fn parts(self) -> Vec<f64> {
        vec![self.hi, self.lo]
    }
    fn raw(p: &[f64]) -> DD {
        DD { hi: p[0], lo: p[1] }
    }
    fn sum(p: &[f64]) -> DD {
        DD::new(p[0], p[1])
    }
    fn pi() -> DD {
        QD::PI.to_dd()
    }
    fn tan(self) -> DD {
        DD::tan(self)
    }
}

impl Scalar for QD {
    const N: usize = 4;
    fn parts(self) -> Vec<f64> {
        self.x.to_vec()
    }
    fn raw(p: &[f64]) -> QD {
        QD {
            x: [p[0], p[1], p[2], p[3]],
        }
    }
    fn sum(p: &[f64]) -> QD {
        QD::new(p[0], p[1], p[2], p[3])
    }
    fn pi() -> QD {
        QD::PI
    }
    fn tan(self) -> QD {
        QD::tan(self)
    }
}

impl Scalar for OD {
    const N: usize = 8;
    fn parts(self) -> Vec<f64> {
        self.x.to_vec()
    }
    fn raw(p: &[f64]) -> OD {
        OD {
            x: std::array::from_fn(|i| p[i]),
        }
    }
    fn sum(p: &[f64]) -> OD {
        OD::new(std::array::from_fn(|i| p[i]))
    }
    fn pi() -> OD {
        OD::from_qd(QD::PI)
    }
    fn tan(self) -> OD {
        OD::tan(self)
    }
}

/// uniform in [lo, hi]
fn int(r: &mut Rng, lo: i64, hi: i64) -> i64 {
    lo + (r.next_u64() % (hi - lo + 1) as u64) as i64
}

fn sign(r: &mut Rng) -> f64 {
    if r.next_u64() & 1 == 0 {
        1.0
    } else {
        -1.0
    }
}

/// f64 parts: the first about 2^e with a random sign, each next one a random fraction of the first's 2^-53 times the
/// one before (zero where it underflows), so all n parts are in use
fn ladder(r: &mut Rng, e: i64, n: usize) -> Vec<f64> {
    let mut p = vec![sign(r) * (1.0 + r.unit()) * 2f64.powi(e as i32)];
    for i in 1..n {
        p.push(p[i - 1] * r.sym() * 2f64.powi(-53 - int(r, 0, 3) as i32));
    }
    p
}

/// a value at about 2^e, e uniform in [lo, hi], with all parts in use
fn full<T: Scalar>(r: &mut Rng, lo: i64, hi: i64) -> T {
    let e = int(r, lo, hi);
    T::sum(&ladder(r, e, T::N))
}

/// parts given in front, zeros after
fn padded<T: Scalar>(p: &[f64]) -> T {
    let mut q = vec![0.0; T::N];
    for (i, v) in p.iter().take(T::N).enumerate() {
        q[i] = *v;
    }
    T::raw(&q)
}

/// k pi/2 to the type's precision: from QD's pi, then one Newton step on tan, whose reduction is exact
fn half_pi_times<T: Scalar>(k: i64) -> T {
    let x = T::pi() * padded::<T>(&[k as f64 * 0.5]);
    if k % 2 == 0 {
        x - x.tan()
    } else {
        x + padded::<T>(&[1.0]) / x.tan()
    }
}

const KINDS: u64 = 11;

/// an argument of the given kind
fn arg<T: Scalar>(r: &mut Rng, kind: u64) -> T {
    let n = T::N;
    // log2 of the early return's threshold, 2^-(53 n / 2)
    let tiny = -(53 * n as i64) / 2;
    match kind {
        // random, |x| from 2^-8 to 2^52
        0 => full(r, -8, 51),
        // a b + c in the type's arithmetic, parts as its arithmetic leaves them
        1 => full::<T>(r, -2, 1) * full::<T>(r, -2, 0) + full::<T>(r, -30, 0),
        // small: the buckets from the early return's threshold up, and the binade below it
        2 => full(r, tiny - 1, -1),
        // tiny: the early return, down to the subnormals, and signed zeros
        3 => match int(r, 0, 3) {
            0 => padded(&[sign(r) * 0.0, 0.0]),
            1 => padded(&[sign(r) * f64::from_bits(1 + r.next_u64() % (1 << 52))]),
            _ => full(r, -1000, tiny - 1),
        },
        // near k pi/2, |k| up to 2^40, plus a few units of the last part's ulp
        4 => {
            let e = int(r, 0, 40);
            let k = (int(r, 1, 1 << e) as f64 * sign(r)) as i64;
            let x: T = half_pi_times(k);
            let last = x.parts()[n - 1];
            let ulp = f64::from_bits(last.abs().to_bits() & 0x7ff0_0000_0000_0000) * 2f64.powi(-52);
            x + padded::<T>(&[int(r, -3, 3) as f64 * ulp])
        }
        // k pi/2 +- 0.7854 (1 +- 2^-30): the reduction's top bucket and its correction of k
        5 => {
            let e = int(r, 1, 40);
            let k = int(r, 1, 1 << e);
            let off = sign(r) * R_TH * (1.0 + r.sym() * 2f64.powi(-30));
            half_pi_times::<T>(k) + padded::<T>(&[off])
        }
        // near 2^52: from 2^48 up, and +-2^52 and +-(2^52 - 1) with lower parts of either sign
        6 => match int(r, 0, 2) {
            0 => full(r, 48, 51),
            1 => T::sum(&[
                sign(r) * 2f64.powi(52),
                r.sym() * 0.5,
                r.sym() * 2f64.powi(-54),
                0.0,
                0.0,
                0.0,
                0.0,
                0.0,
            ]),
            _ => T::sum(&[
                sign(r) * (2f64.powi(52) - 1.0),
                r.sym() * 0.25,
                0.0,
                0.0,
                0.0,
                0.0,
                0.0,
                0.0,
            ]),
        },
        // beyond 2^52: NaN
        7 => match int(r, 0, 2) {
            0 => padded(&[sign(r) * (2f64.powi(52) + 1.0), r.sym() * 0.5]),
            1 => full(r, 53, 1000),
            _ => padded(&[sign(r) * f64::MAX]),
        },
        // NaN and the infinities, in the leading part or a lower one
        8 => match int(r, 0, 3) {
            0 => padded(&[f64::NAN]),
            1 => padded(&[sign(r) * f64::INFINITY]),
            2 => padded(&[r.sym(), f64::NAN]),
            _ => padded(&[0.0, sign(r) * f64::INFINITY]),
        },
        // parts off the ladder: lower parts as large as the first, larger, or below a tiny first part
        9 => match int(r, 0, 4) {
            0 => padded(&[1.0, 2f64.powi(60)]),
            1 => padded(&[r.sym(), r.sym(), r.sym(), r.sym(), r.sym(), r.sym(), r.sym(), r.sym()]),
            2 => padded(&[sign(r) * 1e-40, 1e20]),
            3 => padded(&[3.0 * r.sym(), 1e-3 * r.sym(), 1e-20, 1e-30, 1e-40, 1e-50, 1e-60, 1e-70]),
            // a second part from 1e8 to 1e300 below a first one under pi/4: results with NaN parts
            _ => {
                let e = int(r, 8, 300) as i32;
                padded(&[0.78 * r.sym(), sign(r) * 10f64.powi(e)])
            }
        },
        // signed zeros in the lower parts of a value in range
        _ => {
            let mut p = full::<T>(r, -3, 30).parts();
            for v in p.iter_mut().skip(1) {
                if r.next_u64() & 1 == 0 {
                    *v = sign(r) * 0.0;
                }
            }
            T::raw(&p)
        }
    }
}

/// 8 arguments: of one kind on every fourth call, of a kind per lane on the others
fn args<T: Scalar>(r: &mut Rng, round: usize) -> [T; 8] {
    let one = r.next_u64() % KINDS;
    std::array::from_fn(|_| {
        let kind = if round.is_multiple_of(4) {
            one
        } else {
            r.next_u64() % KINDS
        };
        arg(r, kind)
    })
}

/// the path of a lane, as the scalar results show it: NaN, the early return (sin x = x, cos x = 1), or the sign pair of
/// (sin x, cos x)
fn class(x: DD) -> usize {
    let (s, c) = x.sin_cos();
    if s.hi.is_nan() {
        0
    } else if s.hi.to_bits() == x.hi.to_bits() && s.lo.to_bits() == x.lo.to_bits() && c == DD::ONE {
        1
    } else {
        2 + (s.hi < 0.0) as usize + 2 * (c.hi < 0.0) as usize
    }
}

/// the share of vectors whose lanes take three classes or more, and the classes seen
fn mix(vectors: &[[DD; 8]]) -> (f64, [bool; 6]) {
    let mut seen = [false; 6];
    let mut mixed = 0;
    for v in vectors {
        let mut here = [false; 6];
        for x in v {
            here[class(*x)] = true;
        }
        mixed += (here.iter().filter(|&&b| b).count() >= 3) as usize;
        for k in 0..6 {
            seen[k] |= here[k];
        }
    }
    (mixed as f64 / vectors.len() as f64, seen)
}

/// The vectors of a kind per lane mix the lanes' paths: most have lanes in three classes or more of `class`, and every
/// class occurs. Control: vectors of tiny arguments only, one class, fail the same criterion.
#[test]
fn args_mix_paths() {
    let mut r = Rng(5);
    let mixed: Vec<[DD; 8]> = (0..400).filter(|i| i % 4 != 0).map(|i| args(&mut r, i)).collect();
    let (share, seen) = mix(&mixed);
    println!(
        "{:.0}% of the vectors have three classes or more, classes seen {seen:?}",
        100.0 * share
    );
    assert!(share > 0.9 && seen.iter().all(|&b| b), "{share} {seen:?}");
    let tiny: Vec<[DD; 8]> = (0..100).map(|_| std::array::from_fn(|_| arg(&mut r, 3))).collect();
    let (share, seen) = mix(&tiny);
    assert!(share < 0.9 && !seen.iter().all(|&b| b), "control: {share} {seen:?}");
}

/// the number of parts of `got` and `want` that differ in any bit, printing the first difference
fn diff<T: Scalar>(name: &str, what: &str, x: T, got: T, want: T, bad: &mut usize) {
    if !got.parts().iter().zip(want.parts()).all(|(a, b)| same(*a, b)) {
        if *bad == 0 {
            println!("{name} {what}({x:?}): lanes {got:?}, scalar {want:?}");
        }
        *bad += 1;
    }
}

/// a kernel that runs `rounds` vectors of the lane functions of one type and counts the lane results that differ from
/// the scalar ones
macro_rules! lanes_match {
    ($k:ident, $t:ty, $from:expr) => {
        #[derive(Clone)]
        struct $k(usize);

        impl Kernel for $k {
            type Output = usize;
            #[inline(always)]
            fn run<S: Simd>(self) -> usize {
                let mut bad = 0;
                let mut r = Rng(29 + <$t as Scalar>::N as u64);
                for round in 0..self.0 {
                    let x: [$t; 8] = args(&mut r, round);
                    let v = $from(&x);
                    let (vs, vc) = v.sin_cos();
                    let got = [v.sin(), v.cos(), v.tan(), vs, vc];
                    for l in 0..8 {
                        let (s, c) = x[l].sin_cos();
                        let want = [x[l].sin(), x[l].cos(), x[l].tan(), s, c];
                        for (k, what) in ["sin", "cos", "tan", "sin_cos.0", "sin_cos.1"].iter().enumerate() {
                            diff(S::NAME, what, x[l], got[k].lane(l), want[k], &mut bad);
                        }
                    }
                }
                bad
            }
        }
    };
}

fn dv_from<S: Simd>(x: &[DD; 8]) -> DV<S> {
    let (hi, lo): (Vec<f64>, Vec<f64>) = x.iter().map(|d| (d.hi, d.lo)).unzip();
    DV::load(&hi, &lo)
}

lanes_match!(DvTrig, DD, dv_from::<S>);
lanes_match!(QvTrig, QD, QV::<S>::from_lanes);
lanes_match!(OvTrig, OD, OV::<S>::from_lanes);

/// lane results that differ from the scalar ones, by backend
fn mismatches<K: Kernel<Output = usize> + Clone>(k: K) -> Vec<(&'static str, usize)> {
    let ran = simd::for_each_available(k);
    assert_eq!(ran.iter().map(|r| r.0).collect::<Vec<_>>(), simd::available());
    ran
}

#[test]
fn dv_trig_matches_dd() {
    common::big_stack(|| {
        let ran = mismatches(DvTrig(3000));
        assert!(ran.iter().all(|r| r.1 == 0), "lane results that differ: {ran:?}");
        println!("checked on {:?}", simd::available());
    });
}

#[test]
fn qv_trig_matches_qd() {
    common::big_stack(|| {
        let ran = mismatches(QvTrig(1000));
        assert!(ran.iter().all(|r| r.1 == 0), "lane results that differ: {ran:?}");
        println!("checked on {:?}", simd::available());
    });
}

#[test]
fn ov_trig_matches_od() {
    common::big_stack(|| {
        let ran = mismatches(OvTrig(300));
        assert!(ran.iter().all(|r| r.1 == 0), "lane results that differ: {ran:?}");
        println!("checked on {:?}", simd::available());
    });
}

/// Control (feature `mutate`): each per-lane breakage makes the same checks fail, for each type on every backend
#[cfg(feature = "mutate")]
#[test]
fn lanes_trig_controls() {
    common::big_stack(|| {
        use multidouble::trig::mutate;
        let mut missed = Vec::new();
        for id in [mutate::LANE_TERMS, mutate::LANE_QUADRANT, mutate::LANE_NAN] {
            mutate::set(id);
            let ran = [
                ("dv", mismatches(DvTrig(200))),
                ("qv", mismatches(QvTrig(100))),
                ("ov", mismatches(OvTrig(40))),
            ];
            mutate::set(0);
            for (t, by_backend) in ran {
                for (name, bad) in by_backend {
                    println!(
                        "'{}': {t} on {name}: {bad} lane results differ",
                        mutate::NAMES[id as usize]
                    );
                    if bad == 0 {
                        missed.push(format!("{t} on {name} under '{}'", mutate::NAMES[id as usize]));
                    }
                }
            }
        }
        assert!(missed.is_empty(), "controls that did not fail: {missed:#?}");
    });
}
