//! Double-double LU against known solutions: A x = b with x chosen first and b formed in double-double, so the
//! solve must give x back to about cond(A) u^2. Also the transpose solve, the many-right-hand-side solve (bitwise
//! the single solves), the f64 factorization, the determinant, and the unblocked/blocked dispatch.
#![allow(clippy::needless_range_loop)]
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::linalg::{clu_logdet, gram, ld_for, ColumnGroup, DDLu, StaircaseControl, StaircaseLu};
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
    // zeros and negative zeros in some entries, so that columns are skipped in some lanes and not in others
    let b: Vec<DD> = (0..n * nrhs)
        .map(|j| match j % 7 {
            0 => DD::ZERO,
            3 => DD { hi: -0.0, lo: 0.0 },
            _ => DD::new(r.sym(), r.sym() * 1e-17),
        })
        .collect();
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

/// factor checks that the column groups with the parameter, and the row blocks with row0, each cover 0..n exactly once:
/// each malformed layout below is reported. The fill writes random entries into every step's rows whatever the layout,
/// so that only this check can catch them; with the true layout the same fill factors.
#[test]
fn staircase_rejects_bad_partitions() {
    let (_, n, _, groups, rblocks) = staircase_system(6, 12, 3, 2, 5);
    let try_factor = |g: Vec<ColumnGroup>, rb: &[(usize, usize)], irow0: usize, iparam: usize| {
        let mut r = Rng(1);
        let rows: Vec<usize> = rb.iter().map(|b| b.1).collect();
        StaircaseLu::factor(
            n,
            g,
            rb,
            irow0,
            iparam,
            |s, w: &mut [f64], wld, r0| {
                let start = if s == 0 { r0 - 1 } else { r0 };
                for c in 0..w.len() / wld {
                    for i in start..r0 + rows[s] {
                        w[c * wld + i] = r.sym();
                    }
                }
                Ok(())
            },
            false,
        )
    };
    assert!(try_factor(groups.clone(), &rblocks, n - 1, n - 1).is_ok());
    let mut g = groups.clone();
    g[1].zoff -= 1; // overlaps group 0, and leaves a gap at the end of group 1
    assert!(try_factor(g, &rblocks, n - 1, n - 1).is_err());
    assert!(try_factor(groups.clone(), &rblocks, n - 1, n).is_err()); // the parameter out of range
    assert!(try_factor(groups.clone(), &rblocks, n - 1, 0).is_err()); // the parameter inside group 0
    let mut rb = rblocks.clone();
    rb.last_mut().unwrap().0 += 1; // overlaps row0, and leaves a row uncovered
    assert!(try_factor(groups.clone(), &rb, n - 1, n - 1).is_err());
    assert!(try_factor(groups.clone(), &rblocks, 0, n - 1).is_err()); // row0 inside row block 0
    assert!(try_factor(groups.clone(), &rblocks, n, n - 1).is_err()); // row0 out of range
}

// ---------------------------------------------------------------------------------------------------------------
// quad-double LU
// ---------------------------------------------------------------------------------------------------------------

use multidouble::linalg::{QDLu, QdLuControl};
use multidouble::qd::QdAcc;

fn rand_qd(r: &mut Rng) -> QD {
    QD::new(r.sym(), r.sym() * 1e-17, r.sym() * 1e-34, r.sym() * 1e-51)
}

/// a random n x n quad-double matrix in four parts, column-major with leading dimension ld_for(n), made well
/// conditioned by a diagonal shift
fn matrix_qd(n: usize, r: &mut Rng) -> (usize, [Vec<f64>; 4]) {
    let ld = ld_for(n);
    let mut c: [Vec<f64>; 4] = std::array::from_fn(|_| vec![0.0; ld * n]);
    for j in 0..n {
        for i in 0..n {
            let mut v = rand_qd(r);
            if i == j {
                v = v + QD::from_f64(2.0 + (n as f64).sqrt());
            }
            for q in 0..4 {
                c[q][j * ld + i] = v.x[q];
            }
        }
    }
    (ld, c)
}

fn entry(c: &[Vec<f64>; 4], k: usize) -> QD {
    QD {
        x: std::array::from_fn(|q| c[q][k]),
    }
}

/// A x (or A^T x) in quad-double
fn apply_qd(n: usize, ld: usize, c: &[Vec<f64>; 4], x: &[QD], transpose: bool) -> Vec<QD> {
    (0..n)
        .map(|i| {
            let mut s = QdAcc::zero();
            for j in 0..n {
                let k = if transpose { i * ld + j } else { j * ld + i };
                s = s.add_prod(entry(c, k), x[j]);
            }
            s.finish()
        })
        .collect()
}

fn max_rel_err_qd(got: &[QD], want: &[QD]) -> f64 {
    let scale = want.iter().map(|w| w.x[0].abs()).fold(0.0, f64::max);
    got.iter()
        .zip(want)
        .map(|(g, w)| (*g - *w).to_f64().abs() / scale)
        .fold(0.0, f64::max)
}

/// the error of QDLu's solve and transpose solve of a random well-conditioned system of order n
fn qd_solve_errors(n: usize, seed: u64, par: bool, ctl: QdLuControl) -> f64 {
    let mut r = Rng(seed);
    let (ld, c) = matrix_qd(n, &mut r);
    let x: Vec<QD> = (0..n).map(|_| rand_qd(&mut r)).collect();
    let lu = QDLu::factor_control(n, ld, c.clone(), par, ctl).expect("factor");
    let mut worst = 0.0f64;
    for transpose in [false, true] {
        let mut b = apply_qd(n, ld, &c, &x, transpose);
        if transpose {
            lu.solve_t(&mut b);
        } else {
            lu.solve(&mut b);
        }
        worst = worst.max(max_rel_err_qd(&b, &x));
    }
    worst
}

#[test]
fn qd_lu_solves_to_quad_double() {
    for &n in &[1usize, 5, 8, 37, 64, 130] {
        for &par in &[false, true] {
            let e = qd_solve_errors(n, 61 + n as u64, par, QdLuControl::None);
            println!("QDLu n = {n}, par {par}: worst relative error {e:.1e}");
            assert!(e < 1e-57, "n = {n}: {e:e}");
        }
    }
}

/// Control: the trailing update rounded to double-double leaves the solve at double-double accuracy, which the same
/// check rejects.
#[test]
fn control_qd_lu_update_in_dd_is_caught() {
    let e = qd_solve_errors(64, 125, false, QdLuControl::UpdateDd);
    println!("QDLu with the update in double-double: worst relative error {e:.1e}");
    assert!(e > 1e-40, "{e:e}");
}

#[test]
fn qd_lu_parallel_is_bitwise_serial() {
    let mut r = Rng(62);
    let n = 200;
    let (ld, c) = matrix_qd(n, &mut r);
    let a = QDLu::factor(n, ld, c.clone(), false).unwrap();
    let b = QDLu::factor(n, ld, c, true).unwrap();
    assert_eq!(a.perm, b.perm);
    for q in 0..4 {
        assert!(
            a.c[q].iter().zip(&b.c[q]).all(|(u, v)| u.to_bits() == v.to_bits()),
            "part {q}"
        );
    }
}

/// A = H1 D H2 with Householder reflectors H1, H2 and D = diag(10^(-40 i / (n - 1))): condition number 1e40, beyond
/// double-double. The quad-double LU solves it to about 1e40 2^-209; the double-double LU of A rounded to double-double
/// has no correct digit.
#[test]
fn qd_lu_solves_what_dd_cannot() {
    let mut r = Rng(63);
    let n = 40;
    let ld = ld_for(n);
    let refl = |r: &mut Rng| -> Vec<Vec<QD>> {
        let v: Vec<QD> = (0..n).map(|_| rand_qd(r)).collect();
        let vv = v.iter().fold(QdAcc::zero(), |a, &x| a.add_prod(x, x)).finish();
        (0..n)
            .map(|i| {
                (0..n)
                    .map(|j| {
                        let e = if i == j { QD::ONE } else { QD::ZERO };
                        e - (v[i] * v[j]).mul_f(2.0) / vv
                    })
                    .collect()
            })
            .collect()
    };
    let (h1, h2) = (refl(&mut r), refl(&mut r));
    let d: Vec<QD> = (0..n)
        .map(|k| QD::from_f64(10f64.powf(-40.0 * k as f64 / (n - 1) as f64)))
        .collect();
    let mut c: [Vec<f64>; 4] = std::array::from_fn(|_| vec![0.0; ld * n]);
    for i in 0..n {
        for j in 0..n {
            let s = (0..n)
                .fold(QdAcc::zero(), |a, k| a.add_prod(h1[i][k] * d[k], h2[k][j]))
                .finish();
            for q in 0..4 {
                c[q][j * ld + i] = s.x[q];
            }
        }
    }
    let x: Vec<QD> = (0..n).map(|_| rand_qd(&mut r)).collect();
    let b = apply_qd(n, ld, &c, &x, false);
    let mut bq = b.clone();
    QDLu::factor(n, ld, c.clone(), false).unwrap().solve(&mut bq);
    let eq = max_rel_err_qd(&bq, &x);
    let (hi, lo): (Vec<f64>, Vec<f64>) = (0..ld * n).map(|k| entry(&c, k).to_dd()).map(|v| (v.hi, v.lo)).unzip();
    let mut bd: Vec<DD> = b.iter().map(|v| v.to_dd()).collect();
    DDLu::factor(n, ld, hi, lo, false).unwrap().solve(&mut bd);
    let ed = max_rel_err_qd(&bd.iter().map(|&v| QD::from_dd(v)).collect::<Vec<_>>(), &x);
    println!("cond 1e40: quad-double LU error {eq:.1e}, double-double LU error {ed:.1e}");
    assert!(eq < 1e-16, "quad-double: {eq:e}");
    assert!(ed > 1e-3, "double-double: {ed:e}");
}

/// a block-bidiagonal matrix (8 x 8 blocks, zero elsewhere): the skipped zero updates leave the solve exact to
/// quad-double, and an exactly zero column is reported as singular
#[test]
fn qd_lu_sparse_and_singular() {
    let mut r = Rng(64);
    let n = 48;
    let ld = ld_for(n);
    let mut c: [Vec<f64>; 4] = std::array::from_fn(|_| vec![0.0; ld * n]);
    for j in 0..n {
        for i in 0..n {
            let (bi, bj) = (i / 8, j / 8);
            if bi == bj || bi == bj + 1 {
                let mut v = rand_qd(&mut r);
                if i == j {
                    v = v + QD::from_f64(4.0);
                }
                for q in 0..4 {
                    c[q][j * ld + i] = v.x[q];
                }
            }
        }
    }
    let x: Vec<QD> = (0..n).map(|_| rand_qd(&mut r)).collect();
    let mut b = apply_qd(n, ld, &c, &x, false);
    QDLu::factor(n, ld, c.clone(), true).unwrap().solve(&mut b);
    let e = max_rel_err_qd(&b, &x);
    println!("block-bidiagonal QDLu: worst relative error {e:.1e}");
    assert!(e < 1e-58, "{e:e}");
    for q in 0..4 {
        for i in 0..n {
            c[q][5 * ld + i] = 0.0;
        }
    }
    assert!(QDLu::factor(n, ld, c, false).is_err());
}

// ---------------------------------------------------------------------------------------------------------------
// the determinant of a complex matrix
// ---------------------------------------------------------------------------------------------------------------

/// a random complex n x n matrix (column-major, leading dimension ld), well conditioned by a diagonal shift: real
/// parts (hi, lo), imaginary parts (hi, lo)
fn cmatrix(n: usize, r: &mut Rng) -> (usize, [Vec<f64>; 4]) {
    let ld = ld_for(n);
    let mut c: [Vec<f64>; 4] = std::array::from_fn(|_| vec![0.0; ld * n]);
    for j in 0..n {
        for i in 0..n {
            let mut re = DD::new(r.sym(), r.sym() * 1e-17);
            let im = DD::new(r.sym(), r.sym() * 1e-17);
            if i == j {
                re = re + DD::from_f64(2.0 + (n as f64).sqrt());
            }
            c[0][j * ld + i] = re.hi;
            c[1][j * ld + i] = re.lo;
            c[2][j * ld + i] = im.hi;
            c[3][j * ld + i] = im.lo;
        }
    }
    (ld, c)
}

fn clogdet(n: usize, ld: usize, c: &[Vec<f64>; 4]) -> (f64, f64, f64, f64) {
    clu_logdet(n, ld, c[0].clone(), c[1].clone(), c[2].clone(), c[3].clone(), false).unwrap()
}

/// the difference of two angles, wrapped into (-pi, pi]
fn dang(a: f64, b: f64) -> f64 {
    let d = (a - b).rem_euclid(2.0 * std::f64::consts::PI);
    if d > std::f64::consts::PI {
        d - 2.0 * std::f64::consts::PI
    } else {
        d
    }
}

/// A real matrix (imaginary parts zero) has the ln|det| and the pivot range of `DDLu::logdet` to 1e-12 (the same
/// pivots, updated by a different accumulation), and arg det 0 or pi as its sign is. Control: a wrong sign is caught.
#[test]
fn complex_logdet_of_a_real_matrix_is_logdet() {
    let mut r = Rng(81);
    for n in [1, 7, 20, 33] {
        let (ld, hi, lo) = matrix(n, &mut r);
        let z = vec![0.0; ld * n];
        let lu = DDLu::factor(n, ld, hi.clone(), lo.clone(), false).unwrap();
        let (sign, ln) = lu.logdet();
        let (pmin, pmax) = lu.pivot_range();
        let (la, arg, cmin, cmax) = clu_logdet(n, ld, hi, lo, z.clone(), z, false).unwrap();
        assert!((la - ln).abs() <= 1e-12 * ln.abs().max(1.0), "n {n}: {la} vs {ln}");
        let want = if sign > 0.0 { 0.0 } else { std::f64::consts::PI };
        assert!(dang(arg, want).abs() <= 1e-12, "n {n}: arg {arg} for sign {sign}");
        assert!(dang(arg, want + 1.0).abs() > 0.5, "control");
        assert!((cmin - pmin).abs() <= 1e-12 * pmin && (cmax - pmax).abs() <= 1e-12 * pmax);
    }
}

/// An upper triangular matrix with diagonal (k + 1) e^{i 0.3 (k + 1)} needs no pivoting: ln|det| = sum ln (k + 1)
/// and arg det = 0.3 sum (k + 1) wrapped, to 1e-13; the pivot range is 1 to n.
#[test]
fn complex_logdet_of_a_triangular_matrix() {
    let n = 12;
    let ld = ld_for(n);
    let mut c: [Vec<f64>; 4] = std::array::from_fn(|_| vec![0.0; ld * n]);
    for j in 0..n {
        for i in 0..=j {
            if i == j {
                let (rho, phi) = ((j + 1) as f64, 0.3 * (j + 1) as f64);
                c[0][j * ld + i] = rho * phi.cos();
                c[2][j * ld + i] = rho * phi.sin();
            } else {
                c[0][j * ld + i] = 0.5;
                c[2][j * ld + i] = 0.25;
            }
        }
    }
    let (la, arg, pmin, pmax) = clogdet(n, ld, &c);
    let want_ln: f64 = (1..=n).map(|k| (k as f64).ln()).sum();
    let want_arg = 0.3 * (n * (n + 1) / 2) as f64;
    assert!(
        (la - want_ln).abs() <= 1e-13 && dang(arg, want_arg).abs() <= 1e-13,
        "{la} {arg}"
    );
    assert!((pmin - 1.0).abs() <= 1e-13 && (pmax - n as f64).abs() <= 1e-12);
}

/// On random complex matrices: column 0 times e^{i theta} shifts arg det by theta and leaves ln|det| (to 1e-12); the
/// real 2n x 2n embedding [[R, -I], [I, R]] has determinant |det|^2, so `DDLu::logdet` of it gives 2 ln|det| and a
/// positive sign (to 1e-11). Controls: an entry's imaginary part scaled by 1 + 1e-3 breaks the embedding check; a
/// singular matrix is reported.
#[test]
fn complex_logdet_rotation_and_real_embedding() {
    let mut r = Rng(82);
    for n in [5, 16, 29] {
        let (ld, c) = cmatrix(n, &mut r);
        let (la, arg, _, _) = clogdet(n, ld, &c);
        let theta = 0.7f64;
        let mut rot = c.clone();
        for i in 0..n {
            let (re, im) = (DD::new(c[0][i], c[1][i]), DD::new(c[2][i], c[3][i]));
            let (cs, sn) = (DD::from_f64(theta.cos()), DD::from_f64(theta.sin()));
            let (nr, ni) = (re * cs - im * sn, re * sn + im * cs);
            rot[0][i] = nr.hi;
            rot[1][i] = nr.lo;
            rot[2][i] = ni.hi;
            rot[3][i] = ni.lo;
        }
        let (lr, ar, _, _) = clogdet(n, ld, &rot);
        assert!(
            (lr - la).abs() <= 1e-12 * la.abs().max(1.0),
            "n {n}: rotated ln {lr} vs {la}"
        );
        assert!(
            dang(ar, arg + theta).abs() <= 1e-12,
            "n {n}: rotated arg {ar} vs {arg} + {theta}"
        );
        let embed = |c: &[Vec<f64>; 4]| {
            let m = 2 * n;
            let ldm = ld_for(m);
            let (mut hi, mut lo) = (vec![0.0; ldm * m], vec![0.0; ldm * m]);
            for j in 0..n {
                for i in 0..n {
                    let (re, im) = (
                        (c[0][j * ld + i], c[1][j * ld + i]),
                        (c[2][j * ld + i], c[3][j * ld + i]),
                    );
                    hi[j * ldm + i] = re.0;
                    lo[j * ldm + i] = re.1;
                    hi[(j + n) * ldm + i + n] = re.0;
                    lo[(j + n) * ldm + i + n] = re.1;
                    hi[(j + n) * ldm + i] = -im.0;
                    lo[(j + n) * ldm + i] = -im.1;
                    hi[j * ldm + i + n] = im.0;
                    lo[j * ldm + i + n] = im.1;
                }
            }
            DDLu::factor(m, ldm, hi, lo, false).unwrap().logdet()
        };
        let (sign, ln2) = embed(&c);
        assert!(
            sign > 0.0 && (ln2 - 2.0 * la).abs() <= 1e-11 * la.abs().max(1.0),
            "n {n}: embedding {ln2} vs 2 x {la}"
        );
        let mut wrong = c.clone();
        wrong[2][0] *= 1.0 + 1e-3;
        let (_, lw) = embed(&wrong);
        assert!(
            (lw - 2.0 * la).abs() > 1e-11 * la.abs().max(1.0),
            "control: the perturbed embedding passes"
        );
    }
    let ld = ld_for(4);
    assert!(clu_logdet(
        4,
        ld,
        vec![0.0; ld * 4],
        vec![0.0; ld * 4],
        vec![0.0; ld * 4],
        vec![0.0; ld * 4],
        false
    )
    .is_err());
}

/// The parallel path of `clu_logdet` (par = true, taken above about 32768 updated entries per column step: n = 200
/// here) gives the serial path's results bit for bit: every column's update is the same operations, whichever thread
/// runs it. Control: the same matrix with one entry changed differs.
#[test]
fn complex_logdet_parallel_is_serial() {
    let mut r = Rng(83);
    let n = 200;
    let (ld, c) = cmatrix(n, &mut r);
    let serial = clogdet(n, ld, &c);
    let par = clu_logdet(n, ld, c[0].clone(), c[1].clone(), c[2].clone(), c[3].clone(), true).unwrap();
    let bits = |v: (f64, f64, f64, f64)| [v.0.to_bits(), v.1.to_bits(), v.2.to_bits(), v.3.to_bits()];
    assert_eq!(bits(serial), bits(par));
    let mut other = c.clone();
    other[0][ld + 1] += 1e-3;
    assert_ne!(bits(serial), bits(clogdet(n, ld, &other)), "control");
}

/// Pivots of any size: the matrix scaled by 2^-530 (moduli about 1e-160, whose squares underflow), by 2^530 (about
/// 1e160, whose squares overflow) and by 2^-10 gives the same arg det, ln|det| shifted by n ln 2^e to 1e-9, and
/// every pivot scaled bit for bit (the reciprocal's scaling is exact, so the factors are those of the unscaled
/// matrix times 2^e). Control: the shift with n - 1 in place of n must miss.
#[test]
fn complex_logdet_pivots_of_any_size() {
    let mut r = Rng(84);
    let n = 12;
    let (ld, c) = cmatrix(n, &mut r);
    let (la, arg, pmin, pmax) = clogdet(n, ld, &c);
    for e in [-530i32, 530, -10] {
        let s = 2f64.powi(e);
        let scaled: [Vec<f64>; 4] = std::array::from_fn(|q| c[q].iter().map(|v| v * s).collect());
        let (ls, as_, smin, smax) = clogdet(n, ld, &scaled);
        let shift = n as f64 * s.ln();
        assert!(
            (ls - la - shift).abs() <= 1e-9 * (la.abs() + shift.abs()),
            "2^{e}: {ls} vs {la} + {shift}"
        );
        assert!(dang(as_, arg).abs() <= 1e-12, "2^{e}: arg {as_} vs {arg}");
        assert_eq!(
            (smin.to_bits(), smax.to_bits()),
            ((pmin * s).to_bits(), (pmax * s).to_bits()),
            "2^{e}: pivots"
        );
        assert!(
            (ls - la - (n - 1) as f64 * s.ln()).abs() > 1e-9 * (la.abs() + shift.abs()),
            "control"
        );
    }
}

/// A subnormal pivot under an entry of its own size: the real matrix [[1e-310, 1], [1e-310, 2]] has determinant
/// 1e-310 (the multiplier is 1, the second pivot 1), so ln|det| = ln 1e-310, arg 0; the complex matrix with the first
/// column times i has the same ln|det| and arg pi/2. Control: the second pivot taken as 2 (no elimination) misses.
#[test]
fn complex_logdet_subnormal_pivot_with_finite_multipliers() {
    let ld = ld_for(2);
    let mut c: [Vec<f64>; 4] = std::array::from_fn(|_| vec![0.0; ld * 2]);
    c[0][0] = 1e-310;
    c[0][1] = 1e-310;
    c[0][ld] = 1.0;
    c[0][ld + 1] = 2.0;
    let (la, arg, pmin, pmax) = clogdet(2, ld, &c);
    let want = 1e-310f64.ln();
    assert!(
        (la - want).abs() <= 1e-12 * want.abs() && arg.abs() <= 1e-15,
        "{la} vs {want}, arg {arg}"
    );
    assert!(
        (pmin - 1e-310).abs() <= 1e-15 * 1e-310 && (pmax - 1.0).abs() <= 1e-15,
        "pivots {pmin} {pmax}"
    );
    assert!((la - want - 2f64.ln()).abs() > 0.1, "control");
    let mut ci = c.clone();
    ci[2][0] = 1e-310;
    ci[2][1] = 1e-310;
    ci[0][0] = 0.0;
    ci[0][1] = 0.0;
    let (li, ai, _, _) = clogdet(2, ld, &ci);
    assert!((li - want).abs() <= 1e-12 * want.abs() && dang(ai, std::f64::consts::FRAC_PI_2).abs() <= 1e-15);
}

/// NaN entries: a NaN on the diagonal of a column (in a hi or a lo part), or a column of NaN, is reported as a
/// non-finite pivot (not skipped in favour of a finite entry below it, as the real LU's `pivot_search` does not either)
#[test]
fn complex_logdet_reports_nan_pivots() {
    let mut r = Rng(85);
    let n = 6;
    let (ld, c) = cmatrix(n, &mut r);
    assert!(clogdet(n, ld, &c).0.is_finite());
    let mut diag = c.clone();
    diag[2][2 * ld + 2] = f64::NAN;
    assert!(clu_logdet(
        n,
        ld,
        diag[0].clone(),
        diag[1].clone(),
        diag[2].clone(),
        diag[3].clone(),
        false
    )
    .is_err());
    for (q, i) in [(1usize, 2usize), (3, 4)] {
        let mut lo = c.clone();
        lo[q][i * ld + i] = f64::NAN;
        assert!(
            clu_logdet(n, ld, lo[0].clone(), lo[1].clone(), lo[2].clone(), lo[3].clone(), false).is_err(),
            "lo part {q}"
        );
    }
    let mut col = c.clone();
    for i in 0..n {
        col[0][3 * ld + i] = f64::NAN;
    }
    assert!(clu_logdet(
        n,
        ld,
        col[0].clone(),
        col[1].clone(),
        col[2].clone(),
        col[3].clone(),
        false
    )
    .is_err());
}
