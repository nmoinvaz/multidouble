//! Double-double LU against known solutions: A x = b with x chosen first and b formed in double-double, so the
//! solve must give x back to about cond(A) u^2. Also the transpose solve, the many-right-hand-side solve (bitwise
//! the single solves), the f64 factorization, the determinant, and the unblocked/blocked dispatch.
#![allow(clippy::needless_range_loop)]
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::linalg::{gram, ld_for, ColumnGroup, DDLu, StaircaseControl, StaircaseLu};
use multidouble::qd::QD;

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

/// A x = b solved to quad-double by `solve_refine_qd`: A a random quad-double matrix (each entry with four parts,
/// diagonally shifted), the LU of A rounded to double-double, b = A x formed in quad-double for a random quad-double x.
/// Two steps give x back to 1e-58 (relative to max |x|), and four steps to the same; control: without refinement the
/// solve misses by more than 1e-40 (A's rounding to double-double alone moves x by about 1e-32).
#[test]
fn refined_solve_reaches_quad_double() {
    let mut r = Rng(41);
    for n in [1usize, 7, 8, 33, 64] {
        let qd = |r: &mut Rng, scale: f64| {
            let h = r.sym() * scale;
            QD::new(
                h,
                h * 2f64.powi(-53) * r.sym(),
                h * 2f64.powi(-106) * r.sym(),
                h * 2f64.powi(-159) * r.sym(),
            )
        };
        let a: Vec<QD> = (0..n * n)
            .map(|k| {
                let v = qd(&mut r, 1.0);
                if k % (n + 1) == 0 {
                    v + QD::from_f64(2.0 + (n as f64).sqrt())
                } else {
                    v
                }
            })
            .collect();
        let x: Vec<QD> = (0..n).map(|_| qd(&mut r, 1.0)).collect();
        let apply = |v: &[QD]| -> Vec<QD> {
            (0..n)
                .map(|i| (0..n).fold(QD::ZERO, |s, j| s + a[i * n + j] * v[j]))
                .collect()
        };
        let b = apply(&x);
        let ld = ld_for(n);
        let (mut hi, mut lo) = (vec![0.0; ld * n], vec![0.0; ld * n]);
        for i in 0..n {
            for j in 0..n {
                let d = a[i * n + j].to_dd();
                hi[j * ld + i] = d.hi;
                lo[j * ld + i] = d.lo;
            }
        }
        let lu = DDLu::factor(n, ld, hi, lo, false).unwrap();
        let resid = |v: &[QD], out: &mut [QD]| {
            let av = apply(v);
            for i in 0..n {
                out[i] = b[i] - av[i];
            }
        };
        let xmax = x.iter().map(|v| v.to_f64().abs()).fold(0.0, f64::max);
        let err = |got: &[QD]| {
            got.iter()
                .zip(&x)
                .map(|(g, w)| (*g - *w).to_f64().abs())
                .fold(0.0, f64::max)
                / xmax
        };
        let (e0, e2, e4) = (
            err(&lu.solve_refine_qd(&b, 0, resid)),
            err(&lu.solve_refine_qd(&b, 2, resid)),
            err(&lu.solve_refine_qd(&b, 4, resid)),
        );
        println!("n = {n}: error {e0:.1e} unrefined, {e2:.1e} after two steps, {e4:.1e} after four");
        assert!(
            e2 < 1e-58 && e4 < 1e-58,
            "n = {n}: refined error {e2:e} (two steps), {e4:e} (four)"
        );
        assert!(
            e0 > 1e-40,
            "control, n = {n}: the unrefined solve is already quad-double ({e0:e})"
        );
    }
}

/// A random staircase system with the multiple-shooting structure: column groups of sizes a (first), b (k middle
/// ones), a (last); row blocks of b rows, block blk coupling an input group and a target group (target -I, segments
/// run outward up to inward_from and inward after); a parameter column in every row block and row0 on the first a/2
/// unknowns. Returns the dense column-major matrix (ld_for(n)), its size and leading dimension, and the layout.
#[allow(clippy::type_complexity)]
fn staircase_system(
    a: usize,
    b: usize,
    k: usize,
    inward_from: usize,
    seed: u64,
) -> (Vec<f64>, usize, usize, Vec<ColumnGroup>, Vec<(usize, usize)>) {
    let n = 2 * a + k * b + 1;
    let ld = ld_for(n);
    let mut r = Rng(seed);
    let mut m = vec![0.0f64; ld * n];
    let goff: Vec<usize> = (0..k + 2).map(|t| if t == 0 { 0 } else { a + (t - 1) * b }).collect();
    let glen: Vec<usize> = (0..k + 2).map(|t| if t == 0 || t == k + 1 { a } else { b }).collect();
    for blk in 0..k + 1 {
        let (inp, tgt) = if blk == 0 {
            (0, 1)
        } else if blk == k {
            (k + 1, k)
        } else if blk >= inward_from {
            (blk + 1, blk)
        } else {
            (blk, blk + 1)
        };
        // near-identity propagators (as for short segments), so a long chain stays well conditioned
        let sc = 1.0 / (glen[inp] as f64).sqrt();
        for i in 0..b {
            let row = blk * b + i;
            for c in 0..glen[inp] {
                m[(goff[inp] + c) * ld + row] = 0.5 * r.sym() * sc + if c == i % glen[inp] { 1.0 } else { 0.0 };
            }
            m[(goff[tgt] + i) * ld + row] -= 1.0;
            m[(n - 1) * ld + row] = 5.0 * r.sym();
        }
    }
    for c in 0..a / 2 {
        m[c * ld + n - 1] = 0.5 * r.sym() + 0.7;
    }
    let mut groups = vec![ColumnGroup {
        param: false,
        zoff: 0,
        zlen: a,
    }];
    for t in 1..=k {
        groups.push(ColumnGroup {
            param: true,
            zoff: goff[t],
            zlen: b,
        });
    }
    groups.push(ColumnGroup {
        param: true,
        zoff: goff[k + 1],
        zlen: a,
    });
    let rblocks = (0..k + 1).map(|blk| (blk * b, b)).collect();
    (m, n, ld, groups, rblocks)
}

/// the staircase LU of the dense matrix m (row0 and the parameter at index n - 1), filled from it
fn staircase(
    m: &[f64],
    n: usize,
    ld: usize,
    groups: &[ColumnGroup],
    rblocks: &[(usize, usize)],
    control: StaircaseControl,
) -> StaircaseLu {
    let gs = groups.to_vec();
    let fill = |s: usize, w: &mut [f64], wld: usize, r0: usize| -> Result<(), String> {
        let (p, q) = (gs[s], gs[s + 1]);
        let np = p.len();
        let (roff, rlen) = rblocks[s];
        // the column of z index zi in this step: group p, then group q; the parameter -> q's copy
        let pos = |zi: usize| -> Option<usize> {
            if zi == n - 1 {
                Some(np)
            } else if zi >= p.zoff && zi < p.zoff + p.zlen {
                Some(p.param as usize + zi - p.zoff)
            } else if zi >= q.zoff && zi < q.zoff + q.zlen {
                Some(np + q.param as usize + zi - q.zoff)
            } else {
                None
            }
        };
        for zi in 0..n {
            for i in 0..rlen {
                let v = m[zi * ld + roff + i];
                if v != 0.0 {
                    let c = pos(zi).ok_or(format!("entry outside the step's groups: row {} col {zi}", roff + i))?;
                    w[c * wld + r0 + i] = v;
                }
            }
            if s == 0 {
                let v = m[zi * ld + n - 1];
                if v != 0.0 {
                    w[pos(zi).unwrap() * wld + r0 - 1] = v;
                }
            }
        }
        Ok(())
    };
    StaircaseLu::factor_control(n, groups.to_vec(), rblocks, n - 1, n - 1, fill, true, control).unwrap()
}

fn rel_dd(x: &[DD], y: &[DD]) -> f64 {
    let ym = y.iter().map(|v| v.hi.abs()).fold(0.0, f64::max);
    x.iter()
        .zip(y)
        .map(|(a, b)| ((a.hi - b.hi) + (a.lo - b.lo)).abs())
        .fold(0.0, f64::max)
        / ym
}

/// The staircase LU's solves (f64 factors, double-double solves) agree with the double-double LU of the same f64
/// matrix (the reference, exact to about cond x 1e-32) as well as the dense f64 LU's solves do (DDLu::factor_f64):
/// error <= 100 x the dense f64 error + 1e-15, plain and transposed, with outward and inward segments. The controls
/// (a pivot scaled by 1 + 1e-6; the parameter copies untied) must fail the check.
#[test]
fn staircase_lu_matches_dense() {
    for (a, b, k, inward, seed) in [
        (10, 20, 4, 9, 1),
        (16, 32, 6, 4, 2),
        (40, 80, 12, 99, 3),
        (24, 48, 13, 8, 4),
    ] {
        let (m, n, ld, groups, rblocks) = staircase_system(a, b, k, inward, seed);
        let dense = DDLu::factor(n, ld, m.clone(), vec![0.0; m.len()], false).unwrap();
        let dense64 = DDLu::factor_f64(n, ld, m.clone(), false).unwrap();
        let rhs: Vec<DD> = (0..n)
            .map(|i| DD::from_f64(((i * 37) % 11) as f64 - 5.0 + 0.1 * (i % 3) as f64))
            .collect();
        let mut res = [[0.0f64; 2]; 3];
        let mut d64 = [0.0f64; 2];
        for (ti, t) in [false, true].into_iter().enumerate() {
            let (mut x, mut y) = (rhs.clone(), rhs.clone());
            if t {
                dense64.solve_t(&mut x);
                dense.solve_t(&mut y);
            } else {
                dense64.solve(&mut x);
                dense.solve(&mut y);
            }
            d64[ti] = rel_dd(&x, &y);
        }
        for (ci, control) in [StaircaseControl::None, StaircaseControl::Pivot, StaircaseControl::Link]
            .into_iter()
            .enumerate()
        {
            let lu = staircase(&m, n, ld, &groups, &rblocks, control);
            for (ti, t) in [false, true].into_iter().enumerate() {
                let (mut x, mut y) = (rhs.clone(), rhs.clone());
                if t {
                    lu.solve_t(&mut x);
                    dense.solve_t(&mut y);
                } else {
                    lu.solve(&mut x);
                    dense.solve(&mut y);
                }
                res[ci][ti] = rel_dd(&x, &y);
            }
        }
        println!(
            "a {a} b {b} k {k} (n {n}): error against the dd LU: staircase {:.1e} (transposed {:.1e}), dense f64 LU {:.1e} \
             ({:.1e}); pivot control {:.1e} / {:.1e}; link control {:.1e} / {:.1e}",
            res[0][0], res[0][1], d64[0], d64[1], res[1][0], res[1][1], res[2][0], res[2][1]
        );
        let lim = [100.0 * d64[0] + 1e-15, 100.0 * d64[1] + 1e-15];
        assert!(
            res[0][0] <= lim[0] && res[0][1] <= lim[1],
            "staircase LU less accurate than the dense f64 LU: {:?} vs {d64:?}",
            res[0]
        );
        assert!(
            res[1][0] > lim[0] && res[1][1] > lim[1],
            "the pivot control does not fire: {:?}",
            res[1]
        );
        assert!(
            res[2][0] > lim[0] && res[2][1] > lim[1],
            "the link control does not fire: {:?}",
            res[2]
        );
    }
}

/// solve_many gives each right-hand side bitwise as solve / solve_t; a bad layout is reported
#[test]
fn staircase_solve_many_is_solve() {
    let (m, n, ld, groups, rblocks) = staircase_system(12, 24, 5, 3, 7);
    let lu = staircase(&m, n, ld, &groups, &rblocks, StaircaseControl::None);
    let k = 5;
    let mut r = Rng(3);
    let bh: Vec<f64> = (0..k * n).map(|_| 0.5 * r.sym()).collect();
    let bl = vec![0.0; k * n];
    for t in [false, true] {
        let (mut xh, mut xl) = (bh.clone(), bl.clone());
        lu.solve_many(&mut xh, &mut xl, k, t, true);
        for row in 0..k {
            let mut v: Vec<DD> = (0..n)
                .map(|i| DD {
                    hi: bh[row * n + i],
                    lo: 0.0,
                })
                .collect();
            if t {
                lu.solve_t(&mut v);
            } else {
                lu.solve(&mut v);
            }
            for i in 0..n {
                assert_eq!(v[i].hi.to_bits(), xh[row * n + i].to_bits());
                assert_eq!(v[i].lo.to_bits(), xl[row * n + i].to_bits());
            }
        }
    }
    let (lo, hi) = lu.pivot_range();
    assert!(lo > 0.0 && hi >= lo && lu.bytes() > 0);
    let mut bad = groups.clone();
    bad[0].param = true;
    assert!(StaircaseLu::factor(n, bad, &rblocks, n - 1, n - 1, |_, _, _, _| Ok(()), false).is_err());
}
