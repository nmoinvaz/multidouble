// pack_simd.rs -- the bulk paths of the packed storage against the raw values, single-threaded, for 2, 3 and 8 parts,
// at a size that fits the caches (128 KiB of raw values per vector) and one that does not (256 MiB per vector)
//
// Throughput is counted in bytes of raw values (8 N per value, both vectors for a dot), so each line compares directly
// with the copy and with the raw dot. The dots: double-double through `DDotAcc` (`pack::dot_raw`, `Packed::dot`), the
// triple-word one of Mukunoki and Ozaki's quasi algorithms (QTWmul and QTWadd), octo-double through `ODotAcc`; the raw
// ones read arrays of structs, as they do, and the packed ones decode 8 values at a time (`Packed::blocks`).
//
// cargo bench --bench pack_simd -- --measurement-time 2
#![allow(clippy::needless_range_loop)]

use std::hint::black_box;
use std::time::Duration;

use criterion::{criterion_group, criterion_main, BenchmarkGroup, Criterion, Throughput};
use multidouble::dd::DD;
use multidouble::dv::{DDotAcc, DV};
use multidouble::ov::{ODotAcc, OV};
use multidouble::pack::{self, Packed};
use multidouble::simd::{self, Kernel, Simd};
use multidouble::v8::V8;

/// values of N parts near 1, each part 53 or more places below the one above
fn values<const N: usize>(n: usize, seed: u64) -> Vec<[f64; N]> {
    let mut s = seed;
    let mut sym = move || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        (s >> 11) as f64 / (1u64 << 53) as f64 - 0.5
    };
    (0..n)
        .map(|_| {
            let mut x = [0.0; N];
            x[0] = 1.0 + sym();
            for k in 1..N {
                x[k] = x[k - 1] * 2f64.powi(-53) * sym();
            }
            x
        })
        .collect()
}

/// block b of the raw values, parts planar, zero past the end
#[inline(always)]
fn planar<const N: usize>(v: &[[f64; N]], b: usize) -> [[f64; 8]; N] {
    let mut out = [[0.0; 8]; N];
    for j in 0..(v.len() - 8 * b).min(8) {
        for k in 0..N {
            out[k][j] = v[8 * b + j][k];
        }
    }
    out
}

#[inline(always)]
fn two_sum<S: Simd>(a: V8<S>, b: V8<S>) -> (V8<S>, V8<S>) {
    let s = a.add(b);
    let z = s.sub(a);
    (s, a.sub(s.sub(z)).add(b.sub(z)))
}

#[inline(always)]
fn two_prod<S: Simd>(a: V8<S>, b: V8<S>) -> (V8<S>, V8<S>) {
    let p = a.mul(b);
    (p, a.fms(b, p))
}

/// s + a b in quasi triple-word arithmetic: QTWmul then QTWadd (Mukunoki and Ozaki, arXiv:2510.13536, Alg. 7, 8)
#[inline(always)]
fn qtw_add_prod<S: Simd>(s: [V8<S>; 3], a: [V8<S>; 3], b: [V8<S>; 3]) -> [V8<S>; 3] {
    let (c1, e1) = two_prod(a[0], b[0]);
    let (t2, e2) = two_prod(a[0], b[1]);
    let (t3, e3) = two_prod(a[1], b[0]);
    let (c2, e4) = two_sum(t2, t3);
    let (c2, e5) = two_sum(c2, e1);
    let c3 = a[2]
        .fma(b[0], e2)
        .add(a[1].fma(b[1], e3))
        .add(a[0].fma(b[2], e4))
        .add(e5);
    let (d1, f1) = two_sum(s[0], c1);
    let (d2, f2) = two_sum(s[1], c2);
    let (d2, f3) = two_sum(d2, f1);
    [d1, d2, s[2].add(c3).add(f2).add(f3)]
}

/// the vectors of a dot product: raw arrays of structs, raw parts in arrays of their own (each part's array read
/// with plain vector loads, the fastest a raw layout gets), or packed
#[derive(Clone, Copy)]
enum Src<'a, const N: usize> {
    Raw(&'a [[f64; N]], &'a [[f64; N]]),
    Soa(&'a [Vec<f64>], &'a [Vec<f64>]),
    Packed(&'a Packed<N>, &'a Packed<N>),
}

/// a dot product's accumulator over lane vectors of N parts
trait Acc<S: Simd, const N: usize> {
    fn step(&mut self, x: [V8<S>; N], y: [V8<S>; N]);
    /// the sum of every lane of the finished accumulator, so that no lane's work is optimized away
    fn out(self) -> f64;
}

/// the sum of the lanes of v
fn lanes<S: Simd>(v: &[V8<S>]) -> f64 {
    v.iter().map(|x| x.to_array().iter().sum::<f64>()).sum()
}

/// double-double, through `DDotAcc`
struct Dd<S: Simd>(DDotAcc<S>);

impl<S: Simd> Acc<S, 2> for Dd<S> {
    #[inline(always)]
    fn step(&mut self, x: [V8<S>; 2], y: [V8<S>; 2]) {
        self.0 = self.0.add_prod(DV { hi: x[0], lo: x[1] }, DV { hi: y[0], lo: y[1] });
    }
    fn out(self) -> f64 {
        let f = self.0.finish();
        lanes(&[f.hi, f.lo])
    }
}

/// quasi triple-word
struct Qtw<S: Simd>([V8<S>; 3]);

impl<S: Simd> Acc<S, 3> for Qtw<S> {
    #[inline(always)]
    fn step(&mut self, x: [V8<S>; 3], y: [V8<S>; 3]) {
        self.0 = qtw_add_prod(self.0, x, y);
    }
    fn out(self) -> f64 {
        lanes(&self.0)
    }
}

/// octo-double, through `ODotAcc`
struct Od<S: Simd>(ODotAcc<S>);

impl<S: Simd> Acc<S, 8> for Od<S> {
    #[inline(always)]
    fn step(&mut self, x: [V8<S>; 8], y: [V8<S>; 8]) {
        self.0.add_prod_mut(&OV { c: x }, &OV { c: y });
    }
    fn out(self) -> f64 {
        lanes(&self.0.finish().c)
    }
}

/// acc stepped on every block of both vectors
#[inline(always)]
fn each<const N: usize, S: Simd, A: Acc<S, N>>(src: Src<'_, N>, mut acc: A) -> f64 {
    match src {
        Src::Raw(a, b) => {
            for blk in 0..a.len().div_ceil(8) {
                let (x, y) = (planar(a, blk), planar(b, blk));
                let (mut u, mut v) = ([V8::zero(); N], [V8::zero(); N]);
                for k in 0..N {
                    u[k] = V8::load(&x[k]);
                    v[k] = V8::load(&y[k]);
                }
                acc.step(u, v);
            }
        }
        Src::Soa(a, b) => {
            for blk in 0..a[0].len() / 8 {
                let (mut u, mut v) = ([V8::zero(); N], [V8::zero(); N]);
                for k in 0..N {
                    u[k] = V8::load(&a[k][8 * blk..]);
                    v[k] = V8::load(&b[k][8 * blk..]);
                }
                acc.step(u, v);
            }
        }
        Src::Packed(a, b) => {
            for (x, y) in a.blocks::<S>().zip(b.blocks::<S>()) {
                acc.step(x, y);
            }
        }
    }
    acc.out()
}

struct Dot2<'a>(Src<'a, 2>);
struct Dot3<'a>(Src<'a, 3>);
struct Dot8<'a>(Src<'a, 8>);

impl Kernel for Dot2<'_> {
    type Output = f64;
    #[inline(always)]
    fn run<S: Simd>(self) -> f64 {
        each(self.0, Dd(DDotAcc::<S>::zero()))
    }
}

impl Kernel for Dot3<'_> {
    type Output = f64;
    #[inline(always)]
    fn run<S: Simd>(self) -> f64 {
        each(self.0, Qtw([V8::<S>::zero(); 3]))
    }
}

impl Kernel for Dot8<'_> {
    type Output = f64;
    #[inline(always)]
    fn run<S: Simd>(self) -> f64 {
        each(self.0, Od(ODotAcc::<S>::zero()))
    }
}

fn dot2(src: Src<'_, 2>) -> f64 {
    simd::dispatch(Dot2(src))
}

fn dot3(src: Src<'_, 3>) -> f64 {
    simd::dispatch(Dot3(src))
}

fn dot8(src: Src<'_, 8>) -> f64 {
    simd::dispatch(Dot8(src))
}

fn group<const N: usize>(c: &mut Criterion, n: usize, label: &str, dot: fn(Src<'_, N>) -> f64) {
    let a = values::<N>(n, 0x9e37_79b9_7f4a_7c15);
    let b = values::<N>(n, 0x1234_5678_9abc_def1);
    let (pa, pb) = (Packed::<N>::pack(&a), Packed::<N>::pack(&b));
    let bytes = (n * 8 * N) as u64;
    let mut g: BenchmarkGroup<_> = c.benchmark_group(format!("pack {N} parts {label}"));
    g.sample_size(10)
        .warm_up_time(Duration::from_millis(500))
        .measurement_time(Duration::from_secs(2));
    g.throughput(Throughput::Bytes(bytes));
    let mut dst = vec![[0.0; N]; n];
    g.bench_function("copy raw", |bn| {
        bn.iter(|| {
            dst.copy_from_slice(black_box(&a));
            black_box(&dst);
        })
    });
    g.bench_function("unpack", |bn| {
        bn.iter(|| {
            black_box(&pa).unpack_into(0, &mut dst);
            black_box(&dst);
        })
    });
    g.throughput(Throughput::Bytes(2 * bytes));
    g.bench_function("dot raw", |bn| bn.iter(|| dot(Src::Raw(black_box(&a), black_box(&b)))));
    let soa = |v: &[[f64; N]]| -> Vec<Vec<f64>> { (0..N).map(|k| v.iter().map(|x| x[k]).collect()).collect() };
    let (sa, sb) = (soa(&a), soa(&b));
    assert_eq!(n % 8, 0, "whole blocks for the raw parts' arrays");
    g.bench_function("dot raw parts", |bn| {
        bn.iter(|| dot(Src::Soa(black_box(&sa), black_box(&sb))))
    });
    g.bench_function("dot packed", |bn| {
        bn.iter(|| dot(Src::Packed(black_box(&pa), black_box(&pb))))
    });
    if N == 2 {
        let a2: Vec<DD> = a.iter().map(|x| DD { hi: x[0], lo: x[1] }).collect();
        let b2: Vec<DD> = b.iter().map(|x| DD { hi: x[0], lo: x[1] }).collect();
        let (qa, qb) = (pack::PackedDD::pack(&a2), pack::PackedDD::pack(&b2));
        g.bench_function("dot_raw (DD)", |bn| {
            bn.iter(|| pack::dot_raw(black_box(&a2), black_box(&b2)))
        });
        g.bench_function("Packed::dot (DD)", |bn| bn.iter(|| black_box(&qa).dot(black_box(&qb))));
    }
    g.finish();
}

fn bench(c: &mut Criterion) {
    println!("pack_simd on {}", simd::isa());
    group::<2>(c, 1 << 13, "in cache", dot2);
    group::<3>(c, 5456, "in cache", dot3);
    group::<8>(c, 1 << 11, "in cache", dot8);
    group::<2>(c, 1 << 24, "out of cache", dot2);
    group::<3>(c, (1 << 28) / 24 / 8 * 8, "out of cache", dot3);
    group::<8>(c, 1 << 22, "out of cache", dot8);
}

criterion_group!(benches, bench);
criterion_main!(benches);
