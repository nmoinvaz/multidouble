//! `ODLu`, the dense octo-double LU: solves and transpose solves against planted solutions, with right-hand sides
//! formed in exact arithmetic (`exact::Dy`) and rounded to eight parts, and the exact residual; the error against the
//! condition number from 1 to 1e30 (A = H1 D H2, Householder reflectors and a graded diagonal), where the quad-double
//! LU of the same system misses; the lanes against the scalar updates and the parallel update against the serial one,
//! bit for bit; zero, sparse, singular and non-finite inputs; and the pinned bits of a solve. Each accuracy check has a
//! control.
#![allow(clippy::needless_range_loop)]
mod common;
use common::Rng;
use multidouble::exact::Dy;
use multidouble::linalg::{ld_for, ODLu, OdLuControl, QDLu};
use multidouble::od::{OdAcc, OD};
use multidouble::qd::QD;

/// an octo-double h (1 + O(2^-53)) with all eight parts in use
fn od_of(r: &mut Rng, h: f64) -> OD {
    let mut x = [0.0; 8];
    x[0] = h;
    for i in 1..8 {
        x[i] = x[i - 1] * 2f64.powi(-53) * r.sym();
    }
    OD::new(x)
}

/// a random octo-double in [-1, 1) with all eight parts in use
fn rand_od(r: &mut Rng) -> OD {
    let h = r.sym();
    od_of(r, h)
}

/// a random n x n octo-double matrix in eight parts, column-major with leading dimension ld_for(n), made well
/// conditioned by a diagonal shift
fn matrix_od(n: usize, r: &mut Rng) -> (usize, [Vec<f64>; 8]) {
    let ld = ld_for(n);
    let mut c: [Vec<f64>; 8] = std::array::from_fn(|_| vec![0.0; ld * n]);
    for j in 0..n {
        for i in 0..n {
            let mut v = rand_od(r);
            if i == j {
                v = v + OD::from_f64(2.0 + (n as f64).sqrt());
            }
            for q in 0..8 {
                c[q][j * ld + i] = v.x[q];
            }
        }
    }
    (ld, c)
}

/// entry k (column-major) of a matrix in eight parts
fn entry(c: &[Vec<f64>; 8], k: usize) -> OD {
    OD {
        x: std::array::from_fn(|q| c[q][k]),
    }
}

/// eight parts of a dyadic by greedy round-to-nearest
fn greedy8(d: &Dy) -> OD {
    let mut r = d.clone();
    let mut x = [0.0; 8];
    for xi in x.iter_mut() {
        let c = r.to_f64();
        if c == 0.0 {
            break;
        }
        *xi = c;
        r = r.sub(&Dy::from_f64(c));
    }
    OD { x }
}

/// A x (or A^T x) exactly, and the sums of |A_ij x_j| per row
fn apply_exact(n: usize, ld: usize, c: &[Vec<f64>; 8], x: &[OD], transpose: bool) -> (Vec<Dy>, Vec<Dy>) {
    (0..n)
        .map(|i| {
            let (mut s, mut m) = (Dy::zero(), Dy::zero());
            for j in 0..n {
                let k = if transpose { i * ld + j } else { j * ld + i };
                let t = entry(c, k).exact().mul(&x[j].exact());
                m = m.add(&t.abs());
                s = s.add(&t);
            }
            (s, m)
        })
        .unzip()
}

/// max_i |x_i - y_i| / max_i |y_i|, exactly
fn max_rel_err(x: &[OD], y: &[OD]) -> f64 {
    let ym = y.iter().map(|v| v.exact().abs()).max_by(|a, b| a.cmp_abs(b)).unwrap();
    x.iter()
        .zip(y)
        .map(|(a, b)| a.exact().sub(&b.exact()).abs().ratio(&ym))
        .fold(0.0, f64::max)
}

/// the backward error of x: max_i |b_i - (A x)_i| / sum_j |A_ij x_j|, exactly
fn backward_err(n: usize, ld: usize, c: &[Vec<f64>; 8], x: &[OD], b: &[OD], transpose: bool) -> f64 {
    let (ax, m) = apply_exact(n, ld, c, x, transpose);
    (0..n)
        .map(|i| b[i].exact().sub(&ax[i]).abs().ratio(&m[i]))
        .fold(0.0, f64::max)
}

/// the forward and backward errors of ODLu's solve and transpose solve of a random well-conditioned system of order n
fn od_solve_errors(n: usize, seed: u64, par: bool, ctl: OdLuControl) -> (f64, f64) {
    let mut r = Rng(seed);
    let (ld, c) = matrix_od(n, &mut r);
    let x: Vec<OD> = (0..n).map(|_| rand_od(&mut r)).collect();
    let lu = ODLu::factor_control(n, ld, c.clone(), par, ctl).expect("factor");
    let (mut fwd, mut bwd) = (0.0f64, 0.0f64);
    for transpose in [false, true] {
        let b: Vec<OD> = apply_exact(n, ld, &c, &x, transpose).0.iter().map(greedy8).collect();
        let mut y = b.clone();
        if transpose {
            lu.solve_t(&mut y);
        } else {
            lu.solve(&mut y);
        }
        fwd = fwd.max(max_rel_err(&y, &x));
        bwd = bwd.max(backward_err(n, ld, &c, &y, &b, transpose));
    }
    (fwd, bwd)
}

/// Well-conditioned systems of order 1 to 70 (one row block, partial blocks, several): the solve and the transpose
/// solve recover the planted x within 1e-120 (about 1e-127 seen; the parts hold 2^-424, about 2e-128), and their exact
/// backward error is within n 2^-418 (partial pivoting is backward stable with a small growth factor here).
#[test]
fn od_lu_solves_to_octo_double() {
    for &n in &[1usize, 5, 8, 37, 70] {
        for &par in &[false, true] {
            let (f, b) = od_solve_errors(n, 61 + n as u64, par, OdLuControl::None);
            println!("ODLu n = {n}, par {par}: forward {f:.1e}, backward {b:.1e}");
            assert!(f < 1e-120, "n = {n}: forward {f:e}");
            assert!(b < n as f64 * OD::EPS, "n = {n}: backward {b:e}");
        }
    }
}

/// Control: the trailing update rounded to quad-double leaves the solve at quad-double accuracy, which the same
/// checks reject.
#[test]
fn control_od_lu_update_in_qd_is_caught() {
    let (f, b) = od_solve_errors(37, 125, false, OdLuControl::UpdateQd);
    println!("ODLu with the update in quad-double: forward {f:.1e}, backward {b:.1e}");
    assert!(f > 1e-90 && b > 1e-90, "{f:e} {b:e}");
}

/// the pivots and the bits of the factors
fn lu_bits(lu: &ODLu) -> (Vec<usize>, Vec<u64>) {
    (lu.perm.clone(), lu.c.iter().flatten().map(|v| v.to_bits()).collect())
}

/// The lanes' factorization and solve are the scalar octo-double updates (`OdLuControl::Scalar`, the same arithmetic
/// entry by entry) bit for bit, and so the same on every backend; the parallel update is the serial one bit for bit.
/// Control: a factorization of A with one part's last bit flipped differs.
#[test]
fn od_lu_lanes_are_the_scalar_updates() {
    let mut r = Rng(62);
    let n = 45;
    let (ld, c) = matrix_od(n, &mut r);
    let lanes = ODLu::factor(n, ld, c.clone(), false).unwrap();
    let scalar = ODLu::factor_control(n, ld, c.clone(), false, OdLuControl::Scalar).unwrap();
    let par = ODLu::factor(n, ld, c.clone(), true).unwrap();
    assert_eq!(lu_bits(&lanes), lu_bits(&scalar));
    assert_eq!(lu_bits(&lanes), lu_bits(&par));
    let mut c2 = c.clone();
    c2[3][7 * ld + 9] = f64::from_bits(c2[3][7 * ld + 9].to_bits() ^ 1);
    assert_ne!(lu_bits(&ODLu::factor(n, ld, c2, false).unwrap()), lu_bits(&lanes));
    let par_large = 160;
    let (ld, c) = matrix_od(par_large, &mut r);
    let a = ODLu::factor(par_large, ld, c.clone(), false).unwrap();
    let b = ODLu::factor(par_large, ld, c, true).unwrap();
    assert_eq!(lu_bits(&a), lu_bits(&b), "n = {par_large}: parallel against serial");
}

/// a Householder reflector I - 2 v v^T / v^T v of order n in octo-double
fn reflector(r: &mut Rng, n: usize) -> Vec<Vec<OD>> {
    let v: Vec<OD> = (0..n).map(|_| rand_od(r)).collect();
    let vv = v.iter().fold(OdAcc::zero(), |a, &x| a.add_prod(x, x)).finish();
    (0..n)
        .map(|i| {
            (0..n)
                .map(|j| {
                    let e = if i == j { OD::ONE } else { OD::ZERO };
                    e - (v[i] * v[j]).mul_f(2.0) / vv
                })
                .collect()
        })
        .collect()
}

/// A = H1 D H2 with D = diag(10^(-p i / (n - 1))): condition number 10^p (the reflectors are orthogonal to about
/// 2^-418), column-major in eight parts
fn conditioned(r: &mut Rng, n: usize, p: f64) -> (usize, [Vec<f64>; 8]) {
    let ld = ld_for(n);
    let (h1, h2) = (reflector(r, n), reflector(r, n));
    let d: Vec<OD> = (0..n)
        .map(|k| OD::from_f64(10f64.powf(-p * k as f64 / (n - 1) as f64)))
        .collect();
    let mut c: [Vec<f64>; 8] = std::array::from_fn(|_| vec![0.0; ld * n]);
    for i in 0..n {
        for j in 0..n {
            let s = (0..n)
                .fold(OdAcc::zero(), |a, k| a.add_prod(h1[i][k] * d[k], h2[k][j]))
                .finish();
            for q in 0..8 {
                c[q][j * ld + i] = s.x[q];
            }
        }
    }
    (ld, c)
}

/// The error against the condition number: for A = H1 D H2 of order 40 with condition 1, 1e10, 1e20 and 1e30, the
/// solve's forward error is within cond(A) 2^-418 + 1e-120 of the planted x and its exact backward error within
/// n 2^-418. The error follows the condition: at cond 10^p it is at least 10^(p - 5) times the error at cond 1 (the
/// systems are as ill-conditioned as built; about 10^(p - 3.6) to 10^(p - 0.2) seen, from 1.3e-130 at cond 1 to
/// 3.5e-104 at 1e30), and it is at most 2^-190 times the quad-double LU's error on the same system (A and b rounded to
/// quad-double; the parts hold 2^-424 against 2^-212; about 2^-220 seen at every condition). Control: the quad-double LU misses the octo-double bound by
/// more than 1e40 at cond 1e30.
#[test]
fn od_lu_error_follows_the_condition() {
    let mut r = Rng(63);
    let n = 40;
    let mut f0 = 0.0;
    for p in [0.0, 10.0, 20.0, 30.0] {
        let cond = 10f64.powf(p);
        let (ld, c) = conditioned(&mut r, n, p);
        let x: Vec<OD> = (0..n).map(|_| rand_od(&mut r)).collect();
        let b: Vec<OD> = apply_exact(n, ld, &c, &x, false).0.iter().map(greedy8).collect();
        let mut y = b.clone();
        ODLu::factor(n, ld, c.clone(), false).unwrap().solve(&mut y);
        let (f, bw) = (max_rel_err(&y, &x), backward_err(n, ld, &c, &y, &b, false));
        let cq: [Vec<f64>; 4] = std::array::from_fn(|q| (0..ld * n).map(|k| entry(&c, k).to_qd().x[q]).collect());
        let mut yq: Vec<QD> = b.iter().map(|v| v.to_qd()).collect();
        QDLu::factor(n, ld, cq, false).unwrap().solve(&mut yq);
        let eq = max_rel_err(&yq.iter().map(|&v| OD::from_qd(v)).collect::<Vec<_>>(), &x);
        let bound = cond * OD::EPS + 1e-120;
        println!(
            "cond 1e{p}: ODLu forward {f:.1e}, backward {bw:.1e}; QDLu forward {eq:.1e}; ratio 2^{:.1}",
            (f / eq).log2()
        );
        assert!(f <= bound, "cond 1e{p}: forward {f:e}, bound {bound:e}");
        assert!(bw <= n as f64 * OD::EPS, "cond 1e{p}: backward {bw:e}");
        assert!(
            f <= eq * 2f64.powi(-190),
            "cond 1e{p}: {f:e} against quad-double's {eq:e}"
        );
        if p == 0.0 {
            f0 = f;
        } else {
            assert!(
                f >= f0 * 10f64.powf(p - 5.0),
                "cond 1e{p}: forward {f:e} does not follow the condition"
            );
        }
        if p == 30.0 {
            assert!(eq > 1e40 * bound, "control: the quad-double LU passes ({eq:e})");
        }
    }
}

/// A block-bidiagonal matrix (8 x 8 blocks, zero elsewhere): the skipped zero updates leave the solve exact to
/// octo-double. An exactly zero column, a NaN and an infinite entry are reported as errors naming the column.
#[test]
fn od_lu_sparse_singular_and_non_finite() {
    let mut r = Rng(64);
    let n = 48;
    let ld = ld_for(n);
    let mut c: [Vec<f64>; 8] = std::array::from_fn(|_| vec![0.0; ld * n]);
    for j in 0..n {
        for i in 0..n {
            let (bi, bj) = (i / 8, j / 8);
            if bi == bj || bi == bj + 1 {
                let mut v = rand_od(&mut r);
                if i == j {
                    v = v + OD::from_f64(4.0);
                }
                for q in 0..8 {
                    c[q][j * ld + i] = v.x[q];
                }
            }
        }
    }
    let x: Vec<OD> = (0..n).map(|_| rand_od(&mut r)).collect();
    let b: Vec<OD> = apply_exact(n, ld, &c, &x, false).0.iter().map(greedy8).collect();
    let mut y = b.clone();
    ODLu::factor(n, ld, c.clone(), false).unwrap().solve(&mut y);
    let e = max_rel_err(&y, &x);
    assert!(e < 1e-120, "sparse: {e:e}");
    let mut z = c.clone();
    for i in 0..n {
        for q in 0..8 {
            z[q][5 * ld + i] = 0.0;
        }
    }
    let err = ODLu::factor(n, ld, z, false).err().expect("a zero column is singular");
    assert!(err.contains("column 5"), "{err}");
    for bad in [f64::NAN, f64::INFINITY] {
        let mut z = c.clone();
        z[0][0] = bad;
        let err = ODLu::factor(n, ld, z, false)
            .err()
            .expect("a non-finite pivot is an error");
        assert!(err.contains("non-finite pivot at column 0"), "{err}");
    }
}

/// part q of entry (i, j) of the pinned system's matrix, or of entry i of b when j is None: small integers over powers
/// of two, exact in f64, so that the Python tests (`od_pinned_system` in python/tests/test_od_solve.py) build the same
/// system. The parts overlap, so `OD::new` renormalizes them, as the Python binding does.
fn pinned_part(i: usize, j: Option<usize>, q: usize) -> f64 {
    let scale = 2f64.powi(-7 - 53 * q as i32);
    let t = match j {
        Some(j) => {
            ((i * 37 + j * 101 + q * 53 + i * j * 7) % 211) as f64 - 105.0 + if q == 0 && i == j { 64.0 } else { 0.0 }
        }
        None => ((i * 29 + q * 71) % 199) as f64 - 99.0,
    };
    t * scale
}

/// FNV-1a over the bits of x's parts, part 0 of every entry first, then part 1, ... (as the Python tests hash them)
fn parts_hash(x: &[OD]) -> u64 {
    let mut h = 0xcbf2_9ce4_8422_2325u64;
    for q in 0..8 {
        for v in x {
            h ^= v.x[q].to_bits();
            h = h.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    h
}

/// The pinned system's solutions of A x = b and A^T x = b by ODLu called directly (n = 37, so the last row block is
/// partial, with row swaps), each entry renormalized by `OD::new` as the Python binding does. The Python tests check
/// `od_solve` and `ODLu` against the same hashes, so the binding gives the Rust LU's bits; any change to the LU's bits
/// fails here. The solutions' exact backward errors are checked first. Control: the last bit of one entry's second
/// part flipped in b changes the hash.
#[test]
fn od_lu_pinned_bits() {
    let n = 37;
    let ld = ld_for(n);
    let mut c: [Vec<f64>; 8] = std::array::from_fn(|_| vec![0.0; ld * n]);
    for j in 0..n {
        for i in 0..n {
            let v = OD::new(std::array::from_fn(|q| pinned_part(i, Some(j), q)));
            for q in 0..8 {
                c[q][j * ld + i] = v.x[q];
            }
        }
    }
    let b: Vec<OD> = (0..n)
        .map(|i| OD::new(std::array::from_fn(|q| pinned_part(i, None, q))))
        .collect();
    let lu = ODLu::factor(n, ld, c.clone(), false).unwrap();
    assert!((0..n).any(|k| lu.perm[k] != k), "the pinned system should pivot");
    let mut x = b.clone();
    lu.solve(&mut x);
    let mut y = b.clone();
    lu.solve_t(&mut y);
    for (sol, t) in [(&x, false), (&y, true)] {
        let e = backward_err(n, ld, &c, sol, &b, t);
        println!("pinned system, transpose {t}: backward error {e:.1e}");
        assert!(e < n as f64 * OD::EPS, "{e:e}");
    }
    let (hx, hy) = (parts_hash(&x), parts_hash(&y));
    println!("pinned system: hashes {hx:#018x} {hy:#018x}");
    assert_eq!((hx, hy), (0x06ce_d95b_3a26_3818, 0x8cf2_f580_4d09_8c89));
    let mut z = b.clone();
    z[5].x[1] = f64::from_bits(z[5].x[1].to_bits() ^ 1);
    lu.solve(&mut z);
    assert_ne!(parts_hash(&z), hx);
}

/// cargo test --release --test odlu bench_od_lu -- --ignored --nocapture: seconds per factorization of a random
/// well-conditioned matrix of order 64, 256 and 800 (OD_LU_BENCH_N overrides, comma-separated), the trailing updates
/// in scalar octo-double (`OdLuControl::Scalar`) and on the 8-row lanes, serial and parallel, and QDLu's for scale;
/// the minimum of OD_LU_BENCH_REPS runs (default 3, one at n >= 500)
#[test]
#[ignore]
fn bench_od_lu() {
    use std::time::Instant;
    let sizes: Vec<usize> = std::env::var("OD_LU_BENCH_N")
        .map(|v| v.split(',').map(|t| t.trim().parse().unwrap()).collect())
        .unwrap_or_else(|_| vec![64, 256, 800]);
    let reps: usize = std::env::var("OD_LU_BENCH_REPS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(3);
    println!(
        "isa {}, threads {}: seconds per factorization (min of runs)",
        multidouble::simd::isa(),
        rayon::current_num_threads()
    );
    println!(
        "{:>5} {:>12} {:>12} {:>12} {:>12} {:>12}",
        "n", "od scalar", "od lanes", "od lanes par", "qd lanes", "qd par"
    );
    for n in sizes {
        let mut r = Rng(90 + n as u64);
        let (ld, c) = matrix_od(n, &mut r);
        let cq: [Vec<f64>; 4] = std::array::from_fn(|q| (0..ld * n).map(|k| entry(&c, k).to_qd().x[q]).collect());
        let reps = if n >= 500 { 1 } else { reps };
        let time = |f: &dyn Fn()| {
            (0..reps)
                .map(|_| {
                    let t = Instant::now();
                    f();
                    t.elapsed().as_secs_f64()
                })
                .fold(f64::INFINITY, f64::min)
        };
        let scalar = time(&|| drop(ODLu::factor_control(n, ld, c.clone(), false, OdLuControl::Scalar).unwrap()));
        let lanes = time(&|| drop(ODLu::factor(n, ld, c.clone(), false).unwrap()));
        let par = time(&|| drop(ODLu::factor(n, ld, c.clone(), true).unwrap()));
        let qd = time(&|| drop(QDLu::factor(n, ld, cq.clone(), false).unwrap()));
        let qdp = time(&|| drop(QDLu::factor(n, ld, cq.clone(), true).unwrap()));
        println!("{n:>5} {scalar:>12.4} {lanes:>12.4} {par:>12.4} {qd:>12.4} {qdp:>12.4}");
    }
}
