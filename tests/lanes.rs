//! The 8-lane types against the scalar ones, bit for bit, on whichever backend this build selected
//! (`V8::ISA`: avx512, avx2 or portable). CI runs these on every backend, so the three agree with each other too.
#![allow(clippy::needless_range_loop)]
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::dv::{DotAcc, DV};
use multidouble::qd::QD;
use multidouble::qv::QV;
use multidouble::v8::V8;

const ROUNDS: usize = 4000;

fn same(a: f64, b: f64) -> bool {
    a.to_bits() == b.to_bits() || (a.is_nan() && b.is_nan())
}

fn dd8(r: &mut Rng) -> ([DD; 8], DV) {
    let x: [DD; 8] = std::array::from_fn(|_| r.dd(20));
    let hi: Vec<f64> = x.iter().map(|d| d.hi).collect();
    let lo: Vec<f64> = x.iter().map(|d| d.lo).collect();
    (x, DV::load(&hi, &lo))
}

#[test]
fn backend_is_reported() {
    assert!(["avx512", "avx2", "portable"].contains(&V8::ISA), "{}", V8::ISA);
    println!("V8 backend: {}", V8::ISA);
}

#[test]
fn v8_matches_f64() {
    let mut r = Rng(11);
    for _ in 0..ROUNDS {
        let a: [f64; 8] = std::array::from_fn(|_| r.dd(40).hi);
        let b: [f64; 8] = std::array::from_fn(|_| r.dd(40).hi);
        let c: [f64; 8] = std::array::from_fn(|_| r.dd(40).hi);
        let (va, vb, vc) = (V8::from_array(a), V8::from_array(b), V8::from_array(c));
        let ops: [(V8, &dyn Fn(usize) -> f64); 8] = [
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
                assert!(same(got[j], f(j)), "op {k} lane {j}: {} vs {}", got[j], f(j));
            }
        }
        let bc = va.bcast(3).to_array();
        assert!(bc.iter().all(|&x| same(x, a[3])));
        assert!(same(va.hmax(), a.iter().cloned().fold(f64::NEG_INFINITY, f64::max)));
    }
}

#[test]
fn dv_matches_dd() {
    let mut r = Rng(12);
    for _ in 0..ROUNDS {
        let (x, vx) = dd8(&mut r);
        let (y, vy) = dd8(&mut r);
        let s = r.dd(5).hi;
        let lanes = [vx + vy, vx - vy, vx * vy, vx / vy, -vx, vx.mul_f(s)];
        for j in 0..8 {
            let want = [x[j] + y[j], x[j] - y[j], x[j] * y[j], x[j] / y[j], -x[j], x[j].mul_f(s)];
            for (k, w) in want.iter().enumerate() {
                let g = lanes[k].lane(j);
                assert!(same(g.hi, w.hi) && same(g.lo, w.lo), "op {k} lane {j}: {g:?} vs {w:?}");
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
                "acc lane {j}: {g:?} vs {w:?}"
            );
        }
    }
}

#[test]
fn qv_matches_qd() {
    let mut r = Rng(13);
    let qd = |r: &mut Rng| {
        let a = r.dd(15);
        let b = r.dd(15);
        QD::from_dd(a).add_dd(DD::new(b.hi * 2f64.powi(-106), b.lo * 2f64.powi(-106)))
    };
    for _ in 0..ROUNDS / 4 {
        let x: [QD; 8] = std::array::from_fn(|_| qd(&mut r));
        let y: [QD; 8] = std::array::from_fn(|_| qd(&mut r));
        let (vx, vy) = (QV::from_lanes(&x), QV::from_lanes(&y));
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
                    "op {k} lane {j}: {g:?} vs {w:?}"
                );
            }
        }
    }
}
