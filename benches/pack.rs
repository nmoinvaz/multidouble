// pack.rs -- throughput of the packed storage against copying the raw values, on 2^20 octo-doubles (64 MiB raw)
//
// Throughput is counted in bytes of raw values (64 per octo-double), so each line compares directly with the copy.

use std::hint::black_box;

use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use multidouble::od::OD;
use multidouble::pack::PackedOD;

const N: usize = 1 << 20;

/// octo-doubles near 1 with all eight parts in use
fn values() -> Vec<OD> {
    let mut s = 0x9e37_79b9_7f4a_7c15u64;
    let mut sym = move || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        (s >> 11) as f64 / (1u64 << 53) as f64 - 0.5
    };
    (0..N)
        .map(|_| {
            let mut x = [0.0; 8];
            x[0] = 1.0 + sym();
            for i in 1..8 {
                x[i] = x[i - 1] * 2f64.powi(-53) * sym();
            }
            OD::new(x)
        })
        .collect()
}

fn bench(c: &mut Criterion) {
    let v = values();
    let p = PackedOD::pack(&v);
    let mut g = c.benchmark_group("pack od");
    g.throughput(Throughput::Bytes((N * 64) as u64));
    g.sample_size(20);
    let mut dst = vec![OD::from_f64(0.0); N];
    g.bench_function("copy raw", |b| {
        b.iter(|| {
            dst.copy_from_slice(black_box(&v));
            black_box(&dst);
        })
    });
    g.bench_function("pack", |b| b.iter(|| black_box(PackedOD::pack(black_box(&v)))));
    g.bench_function("unpack", |b| b.iter(|| black_box(black_box(&p).unpack::<OD>())));
    g.bench_function("get every index", |b| {
        b.iter(|| {
            let p = black_box(&p);
            let mut a = 0.0;
            for i in 0..N {
                a += p.get::<OD>(i).x[1];
            }
            black_box(a)
        })
    });
    g.finish();
}

criterion_group!(benches, bench);
criterion_main!(benches);
