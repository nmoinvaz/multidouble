//! Double-double LU against known solutions: A x = b with x chosen first and b formed in double-double, so the
//! solve must give x back to about cond(A) u^2. Also the transpose solve, the many-right-hand-side solve (bitwise
//! the single solves), the f64 factorization, the determinant, and the unblocked/blocked dispatch.
#![allow(clippy::needless_range_loop)]
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::linalg::{gram, ld_for, DDLu};

/// a random n x n matrix, column-major with leading dimension ld, made well conditioned by a diagonal shift
fn matrix(n: usize, r: &mut Rng) -> (usize, Vec<f64>, Vec<f64>) {
    let ld = ld_for(n);
    let (mut hi, mut lo) = (vec![0.0; ld * n], vec![0.0; ld * n]);
    for j in 0..n {
        for i in 0..n {
            let mut v = DD::new(r.sym(), r.sym() * 1e-17);
            if i == j {
                v = v + DD::from_f64(2.0 + (n as f64).sqrt());
            }
            hi[j * ld + i] = v.hi;
            lo[j * ld + i] = v.lo;
        }
    }
    (ld, hi, lo)
}

/// A x (or A^T x) in double-double
fn apply(n: usize, ld: usize, hi: &[f64], lo: &[f64], x: &[DD], transpose: bool) -> Vec<DD> {
    (0..n)
        .map(|i| {
            let mut s = DD::ZERO;
            for j in 0..n {
                let k = if transpose { i * ld + j } else { j * ld + i };
                s = s + DD::new(hi[k], lo[k]) * x[j];
            }
            s
        })
        .collect()
}

fn max_rel_err(got: &[DD], want: &[DD]) -> f64 {
    let scale = want.iter().map(|w| w.hi.abs()).fold(0.0, f64::max);
    got.iter()
        .zip(want)
        .map(|(g, w)| (*g - *w).to_f64().abs() / scale)
        .fold(0.0, f64::max)
}

#[test]
fn solves_recover_the_solution() {
    let mut r = Rng(31);
    for &n in &[1usize, 5, 8, 37, 64, 130, 257] {
        for &par in &[false, true] {
            let (ld, hi, lo) = matrix(n, &mut r);
            let x: Vec<DD> = (0..n).map(|_| DD::new(r.sym(), r.sym() * 1e-17)).collect();
            let lu = DDLu::factor(n, ld, hi.clone(), lo.clone(), par).expect("factor");
            for transpose in [false, true] {
                let mut b = apply(n, ld, &hi, &lo, &x, transpose);
                if transpose {
                    lu.solve_t(&mut b)
                } else {
                    lu.solve(&mut b)
                }
                let e = max_rel_err(&b, &x);
                assert!(e < 1e-29, "n {n} par {par} transpose {transpose}: {e:e}");
            }
        }
    }
}

#[test]
fn solve_many_is_bitwise_the_single_solves() {
    let mut r = Rng(32);
    let n = 45;
    let (ld, hi, lo) = matrix(n, &mut r);
    let lu = DDLu::factor(n, ld, hi, lo, false).unwrap();
    let nrhs = 11;
    let b: Vec<DD> = (0..n * nrhs).map(|_| DD::new(r.sym(), r.sym() * 1e-17)).collect();
    for transpose in [false, true] {
        let mut bh: Vec<f64> = b.iter().map(|d| d.hi).collect();
        let mut bl: Vec<f64> = b.iter().map(|d| d.lo).collect();
        lu.solve_many(&mut bh, &mut bl, nrhs, transpose, true);
        for k in 0..nrhs {
            let mut one = b[k * n..(k + 1) * n].to_vec();
            if transpose {
                lu.solve_t(&mut one)
            } else {
                lu.solve(&mut one)
            }
            for i in 0..n {
                assert_eq!(one[i].hi.to_bits(), bh[k * n + i].to_bits());
                assert_eq!(one[i].lo.to_bits(), bl[k * n + i].to_bits());
            }
        }
    }
}

#[test]
fn f64_factorization_solves_to_f64_accuracy() {
    let mut r = Rng(33);
    for &n in &[7usize, 64, 200] {
        let (ld, hi, lo) = matrix(n, &mut r);
        let x: Vec<DD> = (0..n).map(|_| DD::from_f64(r.sym())).collect();
        let b = apply(n, ld, &hi, &lo, &x, false);
        let lu = DDLu::factor_f64(n, ld, hi.clone(), true).unwrap();
        let mut bh: Vec<f64> = b.iter().map(|d| d.to_f64()).collect();
        lu.solve_hi(&mut bh);
        let got: Vec<DD> = bh.iter().map(|&v| DD::from_f64(v)).collect();
        let e = max_rel_err(&got, &x);
        assert!(e < 1e-12, "n {n}: {e:e}");
    }
}

#[test]
fn determinant_of_a_triangular_matrix() {
    // upper triangular with diagonal 1..n: det = n!, no pivoting needed
    let n = 12;
    let ld = ld_for(n);
    let mut hi = vec![0.0; ld * n];
    for j in 0..n {
        for i in 0..=j {
            hi[j * ld + i] = if i == j { (j + 1) as f64 } else { 0.5 };
        }
    }
    let lu = DDLu::factor(n, ld, hi, vec![0.0; ld * n], false).unwrap();
    let (sign, ln) = lu.logdet();
    let want: f64 = (1..=n).map(|k| (k as f64).ln()).sum();
    assert_eq!(sign, 1.0);
    assert!((ln - want).abs() < 1e-13);
    let (pmin, pmax) = lu.pivot_range();
    assert_eq!((pmin, pmax), (1.0, n as f64));
}

#[test]
fn singular_matrix_is_reported() {
    let n = 4;
    let ld = ld_for(n);
    let hi = vec![0.0; ld * n];
    assert!(DDLu::factor(n, ld, hi, vec![0.0; ld * n], false).is_err());
}

#[test]
fn gram_matrix_is_j_transpose_j() {
    let mut r = Rng(34);
    let n = 9;
    let (ld, jh, jl) = matrix(n, &mut r);
    let b: Vec<DD> = (0..ld)
        .map(|i| if i < n { DD::new(r.sym(), 0.0) } else { DD::ZERO })
        .collect();
    let bh: Vec<f64> = b.iter().map(|d| d.hi).collect();
    let bl: Vec<f64> = b.iter().map(|d| d.lo).collect();
    let (gh, gl, g) = gram(n, ld, &jh, &jl, &bh, &bl);
    for a in 0..n {
        let col: Vec<DD> = (0..n).map(|i| DD::new(jh[a * ld + i], jl[a * ld + i])).collect();
        for c in 0..n {
            let mut s = DD::ZERO;
            for i in 0..n {
                s = s + col[i] * DD::new(jh[c * ld + i], jl[c * ld + i]);
            }
            let got = DD::new(gh[c * ld + a], gl[c * ld + a]);
            assert!((got - s).to_f64().abs() < 1e-29 * s.hi.abs().max(1.0));
        }
        let mut s = DD::ZERO;
        for i in 0..n {
            s = s + col[i] * b[i];
        }
        assert!((g[a] - s).to_f64().abs() < 1e-29 * s.hi.abs().max(1.0));
    }
}

/// Control: a solve with one factor entry perturbed in its low part misses the 1e-29 check.
#[test]
fn control_perturbed_factor_is_caught() {
    let mut r = Rng(35);
    let n = 20;
    let (ld, hi, lo) = matrix(n, &mut r);
    let x: Vec<DD> = (0..n).map(|_| DD::new(r.sym(), 0.0)).collect();
    let mut lo2 = lo.clone();
    lo2[3 * ld + 3] += 1e-20;
    let lu = DDLu::factor(n, ld, hi.clone(), lo2, false).unwrap();
    let mut b = apply(n, ld, &hi, &lo, &x, false);
    lu.solve(&mut b);
    assert!(max_rel_err(&b, &x) > 1e-29);
}
