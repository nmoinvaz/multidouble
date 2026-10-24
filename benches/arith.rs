// arith.rs -- throughput of the arithmetic, scalar against 8-lane, f64 against double-double against quad-double
//
// Each benchmark runs a dependent chain over a small array, so the result is used and the compiler cannot drop the
// work; throughput is counted in element operations (8 per lane operation). The lane benchmarks run on every backend
// the CPU has, one group each ("lanes avx2", "lanes sse2", ...).

use std::cell::RefCell;
use std::hint::black_box;

use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use multidouble::dd::DD;
use multidouble::dv::{DotAcc, DV};
use multidouble::qd::QD;
use multidouble::qv::QV;
use multidouble::simd::{self, Kernel, Simd};
use multidouble::v8::V8;

const N: usize = 1024;

fn inputs() -> (Vec<f64>, Vec<f64>) {
    let mut s = 0x2545_f491_4f6c_dd1du64;
    let mut next = move || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        1.0 + (s >> 11) as f64 / (1u64 << 53) as f64
    };
    let a: Vec<f64> = (0..N).map(|_| next()).collect();
    let b: Vec<f64> = (0..N).map(|_| next() * 1e-17).collect();
    (a, b)
}

fn scalar(c: &mut Criterion) {
    let (a, b) = inputs();
    let dd: Vec<DD> = a.iter().zip(&b).map(|(&h, &l)| DD::new(h, l)).collect();
    let qd: Vec<QD> = dd.iter().map(|&d| QD::from_dd(d)).collect();
    let mut g = c.benchmark_group("scalar");
    g.throughput(Throughput::Elements(N as u64));
    g.bench_function("f64 mul_add", |bch| {
        bch.iter(|| a.iter().fold(0.0f64, |s, &x| x.mul_add(1.000_000_1, s)))
    });
    g.bench_function("dd add", |bch| bch.iter(|| dd.iter().fold(DD::ZERO, |s, &x| s + x)));
    g.bench_function("dd mul", |bch| {
        bch.iter(|| dd.iter().fold(DD::ONE, |s, &x| s * black_box(x)))
    });
    g.bench_function("dd div", |bch| bch.iter(|| dd.iter().fold(DD::ONE, |s, &x| s / x)));
    g.bench_function("qd add", |bch| {
        bch.iter(|| qd.iter().fold(QD::from_f64(0.0), |s, &x| s + x))
    });
    g.bench_function("qd ieee_add", |bch| {
        bch.iter(|| qd.iter().fold(QD::from_f64(0.0), |s, &x| s.ieee_add(x)))
    });
    g.bench_function("qd mul", |bch| {
        bch.iter(|| qd.iter().fold(QD::from_f64(1.0), |s, &x| s * x))
    });
    g.bench_function("qd div", |bch| {
        bch.iter(|| qd.iter().fold(QD::from_f64(1.0), |s, &x| s / x))
    });
    g.bench_function("qd sqrt", |bch| {
        bch.iter(|| qd.iter().map(|&x| x.sqrt()).fold(0.0, |s, r| s + r.x[0]))
    });
    g.finish();
}

/// the lane benchmarks on one backend; criterion calls each measured closure from its own code, so the closure enters
/// the backend's instructions again with `S::vectorize`
#[derive(Clone)]
struct Lanes<'a, 'b>(&'a RefCell<&'b mut Criterion>);

impl Kernel for Lanes<'_, '_> {
    type Output = ();
    #[inline(always)]
    fn run<S: Simd>(self) {
        let (a, b) = inputs();
        let dv: Vec<DV<S>> = (0..N / 8)
            .map(|i| DV::load(&a[8 * i..8 * i + 8], &b[8 * i..8 * i + 8]))
            .collect();
        let v8: Vec<V8<S>> = (0..N / 8).map(|i| V8::load(&a[8 * i..8 * i + 8])).collect();
        let qv: Vec<QV<S>> = dv.iter().map(|&d| QV::from_dv(d)).collect();
        let mut c = self.0.borrow_mut();
        let mut g = c.benchmark_group(format!("lanes {}", S::NAME));
        g.throughput(Throughput::Elements(N as u64));
        g.bench_function("v8 fma", |bch| {
            bch.iter(|| {
                S::vectorize(
                    #[inline(always)]
                    || v8.iter().fold(V8::zero(), |s, &x| x.fma(V8::splat(1.000_000_1), s)),
                )
            })
        });
        g.bench_function("dv add", |bch| {
            bch.iter(|| {
                S::vectorize(
                    #[inline(always)]
                    || dv.iter().fold(DV::zero(), |s, &x| s + x),
                )
            })
        });
        g.bench_function("dv mul", |bch| {
            bch.iter(|| {
                S::vectorize(
                    #[inline(always)]
                    || dv.iter().fold(DV::splat_f(1.0), |s, &x| s * black_box(x)),
                )
            })
        });
        g.bench_function("dv div", |bch| {
            bch.iter(|| {
                S::vectorize(
                    #[inline(always)]
                    || dv.iter().fold(DV::splat_f(1.0), |s, &x| s / x),
                )
            })
        });
        g.bench_function("dv dot (DotAcc)", |bch| {
            bch.iter(|| {
                S::vectorize(
                    #[inline(always)]
                    || dv.iter().fold(DotAcc::zero(), |s, &x| s.add_prod(x, x)).finish(),
                )
            })
        });
        g.bench_function("qv add", |bch| {
            bch.iter(|| {
                S::vectorize(
                    #[inline(always)]
                    || qv.iter().fold(QV::zero(), |s, &x| s + x),
                )
            })
        });
        g.bench_function("qv mul", |bch| {
            bch.iter(|| {
                S::vectorize(
                    #[inline(always)]
                    || qv.iter().fold(QV::splat_f(1.0), |s, &x| s * x),
                )
            })
        });
        g.bench_function("qv div", |bch| {
            bch.iter(|| {
                S::vectorize(
                    #[inline(always)]
                    || qv.iter().fold(QV::splat_f(1.0), |s, &x| s / x),
                )
            })
        });
        g.bench_function("qv sqrt", |bch| {
            bch.iter(|| {
                S::vectorize(
                    #[inline(always)]
                    || qv.iter().map(|&x| x.sqrt()).fold(QV::zero(), |s, r| s + r),
                )
            })
        });
        g.finish();
    }
}

fn lanes(c: &mut Criterion) {
    let c = RefCell::new(c);
    simd::for_each_available(Lanes(&c));
}

criterion_group!(benches, scalar, lanes);
criterion_main!(benches);
