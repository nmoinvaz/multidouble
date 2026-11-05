// linalg.rs -- double-double LU against the f64 blocked LU, and the quad-double LU, factor and solve, one thread; the
// octo-double LU with its updates on the lanes and in scalar octo-double (larger orders: bench_od_lu in tests/odlu.rs)

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use multidouble::dd::DD;
use multidouble::linalg::{ld_for, DDLu, ODLu, OdLuControl, QDLu};
use multidouble::od::OD;
use multidouble::qd::QD;

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
        // the same matrix in quad-double, with full lower parts
        let qc: [Vec<f64>; 4] = {
            let mut c: [Vec<f64>; 4] = std::array::from_fn(|_| vec![0.0; ld * n]);
            for k in 0..ld * n {
                let v = QD::new(hi[k], lo[k], lo[k] * 3.1e-17, hi[k] * 7.3e-49);
                for (q, part) in c.iter_mut().enumerate() {
                    part[k] = v.x[q];
                }
            }
            c
        };
        g.bench_with_input(BenchmarkId::new("qd factor", n), &n, |b, &n| {
            b.iter(|| QDLu::factor(n, ld, qc.clone(), false).unwrap())
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
        let qf = QDLu::factor(n, ld, qc, false).unwrap();
        let qrhs: Vec<QD> = (0..n).map(|i| QD::from_f64(i as f64)).collect();
        g.bench_with_input(BenchmarkId::new("qd solve", n), &n, |b, _| {
            b.iter(|| {
                let mut x = qrhs.clone();
                qf.solve(&mut x);
                x
            })
        });
    }
    g.finish();
}

/// the double-double matrix as octo-double parts (the six lower parts zero; the factors fill them)
fn matrix_od(n: usize) -> (usize, [Vec<f64>; 8]) {
    let (ld, hi, lo) = matrix(n);
    let mut c: [Vec<f64>; 8] = std::array::from_fn(|_| vec![0.0; ld * n]);
    c[0] = hi;
    c[1] = lo;
    (ld, c)
}

fn lu_od(c: &mut Criterion) {
    let mut g = c.benchmark_group("od lu");
    g.sample_size(10);
    for &n in &[32usize, 64] {
        let (ld, a) = matrix_od(n);
        g.throughput(Throughput::Elements((n * n * n) as u64 * 2 / 3));
        g.bench_with_input(BenchmarkId::new("od factor, lanes", n), &n, |b, &n| {
            b.iter(|| ODLu::factor(n, ld, a.clone(), false).unwrap())
        });
        g.bench_with_input(BenchmarkId::new("od factor, scalar", n), &n, |b, &n| {
            b.iter(|| ODLu::factor_control(n, ld, a.clone(), false, OdLuControl::Scalar).unwrap())
        });
        let f = ODLu::factor(n, ld, a.clone(), false).unwrap();
        let rhs: Vec<OD> = (0..n).map(|i| OD::from_f64(i as f64)).collect();
        g.throughput(Throughput::Elements((n * n) as u64));
        g.bench_with_input(BenchmarkId::new("od solve", n), &n, |b, _| {
            b.iter(|| {
                let mut x = rhs.clone();
                f.solve(&mut x);
                x
            })
        });
    }
    g.finish();
}

criterion_group!(benches, lu, lu_od);
criterion_main!(benches);
