// jet.rs -- the octo-double jet against the quad-double one, one thread on the compile-time backend (`native`)
//
// The product of two jets of 24 coefficients (`*`, 300 products of coefficients through the dot accumulator), one
// term accumulated in place (`Lane::acc_mut`, the step of a Cauchy sum of jets), and a jet system of 24 orders on a
// field of M = 32 values solved order by order (`FieldSolve::solve_lanes_jet_refine` in quad-double with its two
// refinement steps, `solve_lanes_jet_refine_od` in octo-double with four, and with two for the same count), the
// system of a regular-horizon series: (omega(h) D + diag kappa(h)) x(h) = rhs(h), D a constant double-double matrix.

// Frames of jet fields, which nightly clippy's large_unopt_stack_frames flags in the unoptimized build. The
// benchmarks run optimized, and stable clippy does not know the lint.
#![allow(unknown_lints, clippy::large_unopt_stack_frames)]

use std::hint::black_box;
use std::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};
use multidouble::dd::DD;
use multidouble::dual::Lane;
use multidouble::field::{FieldSolve, Fl};
use multidouble::linalg::{ld_for, DDLu};
use multidouble::native::{DMat, OJet, QJet, OV, QV, V8};

const N: usize = 24;
const B: usize = 4;
const M: usize = 8 * B;

/// xorshift in [-0.5, 0.5)
struct Rng(u64);

impl Rng {
    /// the next value in [-0.5, 0.5)
    fn next(&mut self) -> f64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 >> 11) as f64 / (1u64 << 53) as f64 - 0.5
    }
    /// 8 lanes with every one of `parts` parts random (part q scaled by 2^-53q), plus c in the first
    fn parts<const P: usize>(&mut self, c: f64) -> [V8; P] {
        std::array::from_fn(|q| {
            let s = 2f64.powi(-53 * q as i32);
            let add = if q == 0 { c } else { 0.0 };
            V8::from_array(std::array::from_fn(|_| self.next() * s + add))
        })
    }
    /// a quad-double jet with every part random, plus c at order 0
    fn qjet(&mut self, c: f64) -> QJet<N> {
        QJet::from_coeffs(std::array::from_fn(|k| QV {
            c: self.parts(if k == 0 { c } else { 0.0 }),
        }))
    }
    /// an octo-double jet with every part random, plus c at order 0
    fn ojet(&mut self, c: f64) -> OJet<N> {
        OJet::from_coeffs(std::array::from_fn(|k| OV {
            c: self.parts(if k == 0 { c } else { 0.0 }),
        }))
    }
}

/// the product and one accumulated term, quad-double against octo-double
fn arithmetic(c: &mut Criterion) {
    let mut r = Rng(0x2545_f491_4f6c_dd1d);
    let (qx, qy) = (r.qjet(0.0), r.qjet(1.0));
    let (ox, oy) = (r.ojet(0.0), r.ojet(1.0));
    let mut g = c.benchmark_group(format!("jet arithmetic, N = {N}"));
    g.sample_size(20).measurement_time(Duration::from_secs(5));
    g.bench_function("QJet product", |bch| bch.iter(|| black_box(qx) * black_box(qy)));
    g.bench_function("OJet product", |bch| bch.iter(|| black_box(ox) * black_box(oy)));
    let mut qa = QJet::<N>::acc0();
    g.bench_function("QJet acc_mut", |bch| {
        bch.iter(|| QJet::<N>::acc_mut(black_box(&mut qa), black_box(&qx), black_box(&qy)))
    });
    let mut oa = OJet::<N>::acc0();
    g.bench_function("OJet acc_mut", |bch| {
        bch.iter(|| OJet::<N>::acc_mut(black_box(&mut oa), black_box(&ox), black_box(&oy)))
    });
    g.finish();
}

/// the jet system: D, omega(h) and kappa(h), the right-hand side, and the LU of A_0 in double-double
struct System {
    d: DMat<B>,
    omega_q: QJet<N>,
    omega_o: OJet<N>,
    kappa_q: Fl<QJet<N>, B>,
    kappa_o: Fl<OJet<N>, B>,
    rhs_q: Fl<QJet<N>, B>,
    rhs_o: Fl<OJet<N>, B>,
    lu: DDLu,
}

/// the system from a fixed seed: D's entries below 0.05, omega_0 = 1.5, kappa_0 in [2, 3), so A_0 is diagonally
/// dominant
fn system() -> System {
    let mut r = Rng(0x9e37_79b9_7f4a_7c15);
    let hi: Vec<f64> = (0..M * M).map(|_| 0.1 * r.next()).collect();
    let lo: Vec<f64> = hi.iter().map(|h| h * 1e-17).collect();
    let d = DMat::from_rows(&hi, &lo);
    let (omega_q, omega_o) = (QJet::splat(DD::from_f64(1.5)) + r.qjet(0.0).mul_pwr2(0.125), {
        OJet::splat(DD::from_f64(1.5)) + r.ojet(0.0).mul_pwr2(0.125)
    });
    let kappa_q = Fl(std::array::from_fn(|_| r.qjet(2.5)));
    let kappa_o = Fl(std::array::from_fn(|_| r.ojet(2.5)));
    let rhs_q = Fl(std::array::from_fn(|_| r.qjet(0.0)));
    let rhs_o = Fl(std::array::from_fn(|_| r.ojet(0.0)));
    let ld = ld_for(M);
    let (mut ch, mut cl) = (vec![0.0; ld * M], vec![0.0; ld * M]);
    let k0 = kappa_o.coef(0);
    for i in 0..M {
        for j in 0..M {
            let mut a = DD::from_f64(1.5) * DD::new(hi[i * M + j], lo[i * M + j]);
            if i == j {
                a = a + k0.get(i);
            }
            ch[j * ld + i] = a.hi;
            cl[j * ld + i] = a.lo;
        }
    }
    let lu = DDLu::factor(M, ld, ch, cl, false).unwrap();
    System {
        d,
        omega_q,
        omega_o,
        kappa_q,
        kappa_o,
        rhs_q,
        rhs_o,
        lu,
    }
}

/// the quad-double jet solve with psolve's coupling and residual
#[inline(never)]
fn solve_q(s: &System, steps: usize) -> Fl<QJet<N>, B> {
    let om: Vec<QV> = (0..N).map(|j| s.omega_q.coef_qd(j)).collect();
    let k0 = s.kappa_q.coef_qd(0);
    s.lu.solve_lanes_jet_refine(
        &s.rhs_q,
        steps,
        |j, x, r| (r - s.d.apply(x).mul_t(om[j])) - s.kappa_q.coef_qd(j) * *x,
        |r, x| *r - (s.d.apply(x).mul_t(om[0]) + k0 * *x),
    )
}

/// the octo-double jet solve with psolve's coupling and residual
#[inline(never)]
fn solve_o(s: &System, steps: usize) -> Fl<OJet<N>, B> {
    let om: Vec<OV> = (0..N).map(|j| s.omega_o.coef_od(j)).collect();
    let k0 = s.kappa_o.coef_od(0);
    s.lu.solve_lanes_jet_refine_od(
        &s.rhs_o,
        steps,
        |j, x, r| (r - s.d.apply(x).mul_t(om[j])) - s.kappa_o.coef_od(j) * *x,
        |r, x| *r - (s.d.apply(x).mul_t(om[0]) + k0 * *x),
    )
}

/// the jet solves, after checking that their outputs are finite
fn solves(c: &mut Criterion) {
    let s = system();
    let (xq, xo) = (solve_q(&s, 2), solve_o(&s, 4));
    assert!(
        (0..N)
            .all(|k| (0..M)
                .all(|i| xq.coef_qd(k).get(i).to_f64().is_finite() && xo.coef_od(k).get(i).to_f64().is_finite())),
        "a solve is not finite"
    );
    let mut g = c.benchmark_group(format!("jet solve, N = {N}, M = {M}"));
    g.sample_size(10).measurement_time(Duration::from_secs(10));
    g.bench_function("QJet, 2 steps", |bch| bch.iter(|| solve_q(black_box(&s), 2)));
    g.bench_function("OJet, 4 steps", |bch| bch.iter(|| solve_o(black_box(&s), 4)));
    g.bench_function("OJet, 2 steps", |bch| bch.iter(|| solve_o(black_box(&s), 2)));
    g.finish();
}

criterion_group!(benches, arithmetic, solves);
criterion_main!(benches);
