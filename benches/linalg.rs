// linalg.rs -- double-double LU against the f64 blocked LU, factor and solve, one thread

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use multidouble::dd::DD;
use multidouble::linalg::{ld_for, DDLu};

fn matrix(n: usize) -> (usize, Vec<f64>, Vec<f64>) {
    let ld = ld_for(n);
    let mut s = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = move || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        (s >> 11) as f64 / (1u64 << 53) as f64 - 0.5
    };
    let (mut hi, mut lo) = (vec![0.0; ld * n], vec![0.0; ld * n]);
    for j in 0..n {
        for i in 0..n {
            hi[j * ld + i] = next() + if i == j { 4.0 } else { 0.0 };
            lo[j * ld + i] = next() * 1e-17;
        }
    }
    (ld, hi, lo)
}

fn lu(c: &mut Criterion) {
    let mut g = c.benchmark_group("lu");
    for &n in &[64usize, 128, 256] {
        let (ld, hi, lo) = matrix(n);
        g.throughput(Throughput::Elements((n * n * n) as u64 * 2 / 3));
        g.bench_with_input(BenchmarkId::new("dd factor", n), &n, |b, &n| {
            b.iter(|| DDLu::factor(n, ld, hi.clone(), lo.clone(), false).unwrap())
        });
        g.bench_with_input(BenchmarkId::new("f64 factor", n), &n, |b, &n| {
            b.iter(|| DDLu::factor_f64(n, ld, hi.clone(), false).unwrap())
        });
        let f = DDLu::factor(n, ld, hi.clone(), lo.clone(), false).unwrap();
        let rhs: Vec<DD> = (0..n).map(|i| DD::from_f64(i as f64)).collect();
        g.throughput(Throughput::Elements((n * n) as u64));
        g.bench_with_input(BenchmarkId::new("dd solve", n), &n, |b, _| {
            b.iter(|| {
                let mut x = rhs.clone();
                f.solve(&mut x);
                x
            })
        });
    }
    g.finish();
}

criterion_group!(benches, lu);
criterion_main!(benches);
