//! Fields (`field::Fl`): Cauchy products, Horner evaluation and constant-matrix products against scalar references,
//! in double-double (to its rounding, against quad-double sums), in the f64 lanes (bitwise the scalar fused
//! multiply-add chains in index order) and in quad-double; the counting lane's matrix product; and the field solves,
//! with the refinement of the double-double solve in the lane type (to quad-double for `QV`).
//! Each accuracy check has a control fed a wrong result.
#![allow(clippy::needless_range_loop)]
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::dual::{op, take_counts, Counted, Lane};
use multidouble::exact::Dy;
use multidouble::field::{cs, cs_range, cs_w, horner, DMat, FieldSolve, Fl, MatLane};
use multidouble::linalg::{ld_for, DDLu};
use multidouble::native::{Dtn, Fu, Fun, F8, QV};
use multidouble::qd::QD;
use multidouble::simd::Native;

type DV = multidouble::native::DV;
const B: usize = 2;
const M: usize = 8 * B;

fn field(r: &mut Rng, scale: f64) -> (Fl<DV, B>, Vec<DD>) {
    let v: Vec<DD> = (0..M)
        .map(|_| DD::new(scale * r.sym(), scale * r.sym() * 1e-17))
        .collect();
    let (h, l): (Vec<f64>, Vec<f64>) = v.iter().map(|d| (d.hi, d.lo)).unzip();
    (Fl::load(&h, &l), v)
}

fn q(d: DD) -> QD {
    QD::from_dd(d)
}

/// Cauchy products in double-double against quad-double sums of the same terms: within 2^-100 of sum |x_j y_{k-j}|
/// (w_j |x_j y_{k-j}| for cs_w). Control: the reference with y shifted by one order must miss that bound.
#[test]
fn cauchy_products_to_double_double() {
    let mut r = Rng(51);
    let n = 12;
    let (xs, xv): (Vec<Fl<DV, B>>, Vec<Vec<DD>>) = (0..n).map(|_| field(&mut r, 1.0)).unzip();
    let (ys, yv): (Vec<Fl<DV, B>>, Vec<Vec<DD>>) = (0..n).map(|_| field(&mut r, 1.0)).unzip();
    let w = |j: usize| (j + 1) as f64;
    let (mut worst, mut ctl) = (0.0f64, f64::INFINITY);
    for k in 0..n {
        let (lo, hi) = (k / 3, k - k / 4);
        let got = [
            cs(&xs, &ys, k),
            cs_range(&xs, &ys, k, lo, hi),
            cs_w(&xs, &ys, k, lo, hi, w),
        ];
        for i in 0..M {
            for (case, g) in got.iter().enumerate() {
                let (a, b, wt): (usize, usize, bool) = match case {
                    0 => (0, k, false),
                    1 => (lo, hi, false),
                    _ => (lo, hi, true),
                };
                let (mut s, mut size, mut sc) = (QD::ZERO, 0.0f64, QD::ZERO);
                for j in a..=b {
                    let f = if wt { w(j) } else { 1.0 };
                    let t = q(xv[j][i]).mul_f(f) * q(yv[k - j][i]);
                    s = s + t;
                    size += t.to_f64().abs();
                    if k > j {
                        sc = sc + q(xv[j][i]).mul_f(f) * q(yv[k - j - 1][i]);
                    }
                }
                let gi = q(g.get(i));
                worst = worst.max((gi - s).to_f64().abs() / size);
                if size > 0.0 {
                    ctl = ctl.min((gi - sc).to_f64().abs() / size);
                }
            }
        }
    }
    let bound = 2f64.powi(-100);
    println!(
        "Cauchy products: worst error {:.2e} of sum |terms| (bound {bound:.1e}); control (shifted) {ctl:.1e}",
        worst
    );
    assert!(worst <= bound, "{worst:e}");
    assert!(ctl > bound, "control: the shifted reference agrees ({ctl:e})");
}

/// In the f64 lanes a Cauchy product is the fused multiply-add chain in index order, bitwise (F8, and Fun<2>'s value
/// and tangents); Horner in double-double is the scalar Horner bitwise.
#[test]
fn f64_lanes_and_horner_are_the_scalar_chains() {
    let mut r = Rng(52);
    let n = 9;
    let xs: Vec<Fl<DV, B>> = (0..n).map(|_| field(&mut r, 1.0).0).collect();
    let ys: Vec<Fl<DV, B>> = (0..n).map(|_| field(&mut r, 1.0).0).collect();
    let f8 = |x: &Fl<DV, B>| Fl::<F8, B>::from_vt(x, &Fl::zero());
    let (x8, y8): (Vec<_>, Vec<_>) = (xs.iter().map(f8).collect(), ys.iter().map(f8).collect());
    for k in 0..n {
        let c = cs(&x8, &y8, k);
        let cw = cs_w(&x8, &y8, k, 0, k, |j| (2 * j + 1) as f64);
        for i in 0..M {
            let (mut a, mut aw) = (0.0f64, 0.0f64);
            for j in 0..=k {
                let (xj, yj) = (xs[j].get(i).hi, ys[k - j].get(i).hi);
                a = xj.mul_add(yj, a);
                aw = (xj * (2 * j + 1) as f64).mul_add(yj, aw);
            }
            assert_eq!(
                c.0[i / 8].0.to_array()[i % 8].to_bits(),
                a.to_bits(),
                "F8 cs k {k} i {i}"
            );
            assert_eq!(
                cw.0[i / 8].0.to_array()[i % 8].to_bits(),
                aw.to_bits(),
                "F8 cs_w k {k} i {i}"
            );
        }
    }
    let h = DD::new(0.3, 1e-18);
    let hv = horner(&xs, h);
    for i in 0..M {
        let mut s = DD::ZERO;
        for k in (0..n).rev() {
            s = s * h + xs[k].get(i);
        }
        let g = hv.get(i);
        assert!(
            g.hi.to_bits() == s.hi.to_bits() && g.lo.to_bits() == s.lo.to_bits(),
            "Horner i {i}"
        );
    }
}

fn matrix(r: &mut Rng) -> (DMat<Native, B>, Vec<DD>) {
    let a: Vec<DD> = (0..M * M).map(|_| DD::new(r.sym(), r.sym() * 1e-17)).collect();
    let (h, l): (Vec<f64>, Vec<f64>) = a.iter().map(|d| (d.hi, d.lo)).unzip();
    (DMat::from_rows(&h, &l), a)
}

/// D f for every lane type: double-double (DV, and Du's value and tangent) within 2^-100 of sum |D_ij f_j| of the
/// quad-double product (control: D transposed misses it); quad-double (QV) within 2^-200; the f64 lanes bitwise the
/// scalar fma chains over the columns' hi parts in column order (F8, Fu, Fun<2>, and Dtn<2>'s tangents, whose value is
/// DV's product bitwise); Counted<DV> bitwise DV's, counted as 8 B x B accc and B finish.
#[test]
fn matrix_products() {
    let mut r = Rng(53);
    let (d, a) = matrix(&mut r);
    let (f, fv) = field(&mut r, 1.0);
    let (t, tv) = field(&mut r, 1.0);
    let exact = |i: usize, v: &[DD], tr: bool| -> (QD, f64) {
        let mut s = QD::ZERO;
        let mut size = 0.0f64;
        for j in 0..M {
            let e = if tr { a[j * M + i] } else { a[i * M + j] };
            let p = q(e) * q(v[j]);
            s = s + p;
            size += p.to_f64().abs();
        }
        (s, size)
    };
    let dv = d.apply(&f);
    let du = d.apply(&Fl::<multidouble::native::Du, B>::from_vt(&f, &t));
    let (mut worst, mut ctl) = (0.0f64, f64::INFINITY);
    for i in 0..M {
        let (s, size) = exact(i, &fv, false);
        let (st, sizet) = exact(i, &tv, false);
        let (sx, _) = exact(i, &fv, true);
        worst = worst.max((q(dv.get(i)) - s).to_f64().abs() / size);
        worst = worst.max((q(du.val().get(i)) - s).to_f64().abs() / size);
        worst = worst.max((q(du.tan().get(i)) - st).to_f64().abs() / sizet);
        ctl = ctl.min((q(dv.get(i)) - sx).to_f64().abs() / size);
    }
    println!("D f in double-double: worst {worst:.2e} of sum |terms|; control (transposed) {ctl:.1e}");
    assert!(worst <= 2f64.powi(-100), "{worst:e}");
    assert!(
        ctl > 2f64.powi(-100),
        "control: the transposed product agrees ({ctl:e})"
    );
    // quad-double
    let fq = Fl::<QV, B>::from_vt(&f, &Fl::zero());
    let dq = d.apply(&fq);
    let mut wq = 0.0f64;
    for i in 0..M {
        let (s, size) = exact(i, &fv, false);
        wq = wq.max((dq.0[i / 8].lane(i % 8) - s).to_f64().abs() / size);
    }
    println!("D f in quad-double: worst {wq:.2e} of sum |terms|");
    assert!(wq <= 2f64.powi(-200), "{wq:e}");
    // the f64 lanes: scalar fma chains over the columns' hi parts
    let chain = |v: &[f64], i: usize| -> f64 {
        let mut s = 0.0f64;
        for j in 0..M {
            s = v[j].mul_add(a[i * M + j].hi, s);
        }
        s
    };
    let (fh, th): (Vec<f64>, Vec<f64>) = (fv.iter().map(|x| x.hi).collect(), tv.iter().map(|x| x.hi).collect());
    let lane = |v: multidouble::native::V8, i: usize| v.to_array()[i % 8].to_bits();
    let r8 = d.apply(&Fl::<F8, B>::from_vt(&f, &Fl::zero()));
    let ru = d.apply(&Fl::<Fu, B>::from_vt(&f, &t));
    let mut fun = Fl::<Fun<2>, B>::from_vt(&f, &Fl::zero());
    let mut dtn = Fl::<Dtn<2>, B>::from_vt(&f, &Fl::zero());
    for b in 0..B {
        for k in 0..2 {
            let tk = if k == 0 {
                t.0[b].hi
            } else {
                f.0[b].hi.mul(multidouble::native::V8::splat(0.5))
            };
            fun.0[b].set_tan64(k, tk);
            dtn.0[b].set_tan64(k, tk);
        }
    }
    let (rn, rt) = (d.apply(&fun), d.apply(&dtn));
    for i in 0..M {
        let (cf, ct) = (chain(&fh, i).to_bits(), chain(&th, i).to_bits());
        let half: Vec<f64> = fh.iter().map(|x| x * 0.5).collect();
        let ch = chain(&half, i).to_bits();
        assert_eq!(lane(r8.0[i / 8].0, i), cf, "F8 i {i}");
        assert_eq!((lane(ru.0[i / 8].v, i), lane(ru.0[i / 8].d, i)), (cf, ct), "Fu i {i}");
        assert_eq!(
            (
                lane(rn.0[i / 8].v, i),
                lane(rn.0[i / 8].d[0], i),
                lane(rn.0[i / 8].d[1], i)
            ),
            (cf, ct, ch),
            "Fun i {i}"
        );
        assert_eq!(
            (lane(rt.0[i / 8].d[0], i), lane(rt.0[i / 8].d[1], i)),
            (ct, ch),
            "Dtn tangents i {i}"
        );
        let (v, w) = (rt.0[i / 8].v.lane(i % 8), dv.get(i));
        assert!(
            v.hi.to_bits() == w.hi.to_bits() && v.lo.to_bits() == w.lo.to_bits(),
            "Dtn value i {i}"
        );
    }
    // the counting lane
    let fc = Fl(f.0.map(Counted));
    take_counts();
    let dc = d.apply(&fc);
    let n = take_counts();
    for i in 0..M {
        let (x, y) = (dc.0[i / 8].0.lane(i % 8), dv.get(i));
        assert!(
            x.hi.to_bits() == y.hi.to_bits() && x.lo.to_bits() == y.lo.to_bits(),
            "Counted i {i}"
        );
    }
    // the default product (apply_dd) run through Counted's own per-operation counts must count the same
    take_counts();
    let dd = d.apply_dd(&fc);
    let nd = take_counts();
    assert_eq!(
        n, nd,
        "Counted::dmat_apply against the default product on counting lanes"
    );
    for i in 0..M {
        let (x, y) = (dd.0[i / 8].0.lane(i % 8), dv.get(i));
        assert!(
            x.hi.to_bits() == y.hi.to_bits() && x.lo.to_bits() == y.lo.to_bits(),
            "apply_dd i {i}"
        );
    }
    assert_eq!(n[op::ACCC], (8 * B * B) as u64);
    assert_eq!(n[op::FIN], B as u64);
    assert_eq!(n.iter().sum::<u64>(), (8 * B * B + B) as u64);
    let _ = <Counted<DV> as MatLane>::dmat_apply::<B>;
}

/// The field solves are DDLu's solves of the stored vector, bitwise
#[test]
fn field_solves_are_the_lu_solves() {
    let mut r = Rng(54);
    let ld = ld_for(M);
    let (mut h, mut l) = (vec![0.0; ld * M], vec![0.0; ld * M]);
    for j in 0..M {
        for i in 0..M {
            let v = DD::new(r.sym() + if i == j { 4.0 } else { 0.0 }, r.sym() * 1e-17);
            h[j * ld + i] = v.hi;
            l[j * ld + i] = v.lo;
        }
    }
    let lu = DDLu::factor(M, ld, h, l, false).unwrap();
    let (f, fv) = field(&mut r, 1.0);
    let x = lu.solve_lanes(&f);
    let mut b = fv.clone();
    lu.solve(&mut b);
    let mut bh: Vec<f64> = fv.iter().map(|v| v.hi).collect();
    lu.solve_hi(&mut bh);
    let xh = lu.solve_lanes_hi(&f);
    for i in 0..M {
        let g = x.get(i);
        assert!(
            g.hi.to_bits() == b[i].hi.to_bits() && g.lo.to_bits() == b[i].lo.to_bits(),
            "solve_lanes i {i}"
        );
        assert!(
            xh.get(i).hi.to_bits() == bh[i].to_bits() && xh.get(i).lo == 0.0,
            "solve_lanes_hi i {i}"
        );
    }
}

/// A DDLu whose order is not 8 B is refused by both field solves (smaller: the rest of the field would pass through
/// unsolved; larger: an index past the end)
fn lu_of_order(n: usize) -> DDLu {
    let ld = ld_for(n);
    let mut h = vec![0.0; ld * n];
    for i in 0..n {
        h[i * ld + i] = 2.0;
    }
    DDLu::factor(n, ld, h, vec![0.0; ld * n], false).unwrap()
}

#[test]
#[should_panic(expected = "FieldSolve: a DDLu of order 8 for a field of 16 values")]
fn field_solve_refuses_a_smaller_lu() {
    let (f, _) = field(&mut Rng(3), 1.0);
    lu_of_order(M - 8).solve_lanes(&f);
}

#[test]
#[should_panic(expected = "FieldSolve: a DDLu of order 24 for a field of 16 values")]
fn field_solve_hi_refuses_a_larger_lu() {
    let (f, _) = field(&mut Rng(3), 1.0);
    lu_of_order(M + 8).solve_lanes_hi(&f);
}

/// a quad-double field from 8 B values
fn qfield(v: &[QD]) -> Fl<QV, B> {
    Fl(std::array::from_fn(|b| {
        QV::from_lanes(v[8 * b..8 * b + 8].try_into().unwrap())
    }))
}

/// the 8 B values of a quad-double field
fn qvalues(f: &Fl<QV, B>) -> Vec<QD> {
    f.0.iter().flat_map(|v| v.lanes()).collect()
}

/// A x0 = b: A a diagonally dominant double-double matrix (as the constant matrix for the quad-double residual and
/// as its LU for the solves), x0 a random quad-double field (four parts), b = A x0 formed exactly (dyadic arithmetic)
/// and rounded to quad-double
fn qd_system(r: &mut Rng) -> (DMat<Native, B>, DDLu, Vec<QD>, Vec<QD>) {
    let a: Vec<DD> = (0..M * M)
        .map(|k| DD::new(r.sym() + if k / M == k % M { 4.0 } else { 0.0 }, r.sym() * 1e-17))
        .collect();
    let (h, l): (Vec<f64>, Vec<f64>) = a.iter().map(|d| (d.hi, d.lo)).unzip();
    let ld = ld_for(M);
    let (mut ch, mut cl) = (vec![0.0; ld * M], vec![0.0; ld * M]);
    for i in 0..M {
        for j in 0..M {
            ch[j * ld + i] = h[i * M + j];
            cl[j * ld + i] = l[i * M + j];
        }
    }
    let lu = DDLu::factor(M, ld, ch, cl, false).unwrap();
    let x0: Vec<QD> = (0..M)
        .map(|_| {
            let v = r.sym();
            QD::new(
                v,
                v * 2f64.powi(-53) * r.sym(),
                v * 2f64.powi(-106) * r.sym(),
                v * 2f64.powi(-159) * r.sym(),
            )
        })
        .collect();
    let b: Vec<QD> = (0..M)
        .map(|i| {
            let mut s = Dy::zero();
            for j in 0..M {
                let aij = Dy::from_f64(h[i * M + j]).add(&Dy::from_f64(l[i * M + j]));
                s = s.add(&aij.mul(&x0[j].exact()));
            }
            QD { x: s.greedy4() }
        })
        .collect();
    (DMat::from_rows(&h, &l), lu, x0, b)
}

/// max |x_i - y_i| / max |y_i|, in quad-double
fn qd_err(x: &[QD], y: &[QD]) -> f64 {
    let ym = y.iter().map(|v| v.x[0].abs()).fold(0.0, f64::max);
    x.iter()
        .zip(y)
        .map(|(a, b)| (*a - *b).to_f64().abs())
        .fold(0.0, f64::max)
        / ym
}

/// The field refinement in quad-double lanes is DDLu::solve_refine_qd on the field's values, bitwise (both with the
/// same residual function), for 0 to 3 steps; with no steps it is the double-double field solve of the values, in
/// QV and in DV lanes alike.
#[test]
fn field_refine_is_solve_refine_qd() {
    let mut r = Rng(61);
    let (d, lu, _, b) = qd_system(&mut r);
    let bq = qfield(&b);
    let resid = |x: &Fl<QV, B>| bq - d.apply(x);
    for steps in 0..4 {
        let x = qvalues(&lu.solve_lanes_refine(&bq, steps, resid));
        let y = lu.solve_refine_qd(&b, steps, |x, out| out.copy_from_slice(&qvalues(&resid(&qfield(x)))));
        for i in 0..M {
            assert!(
                x[i].x
                    .iter()
                    .zip(y[i].x.iter())
                    .all(|(p, q)| p.to_bits() == q.to_bits()),
                "steps {steps} i {i}: {:?} vs {:?}",
                x[i],
                y[i]
            );
        }
    }
    let plain = lu.solve_lanes(&bq.val());
    let x0 = lu.solve_lanes_refine(&bq, 0, |_| unreachable!());
    let (f, _) = field(&mut r, 1.0);
    let xd = lu.solve_lanes_refine(&f, 0, |_| unreachable!());
    let fd = lu.solve_lanes(&f);
    for i in 0..M {
        let (p, q) = (x0.0[i / 8].lane(i % 8), plain.get(i));
        assert!(p.x[0].to_bits() == q.hi.to_bits() && p.x[1].to_bits() == q.lo.to_bits() && p.x[2] == 0.0);
        assert!(xd.get(i).hi.to_bits() == fd.get(i).hi.to_bits() && xd.get(i).lo.to_bits() == fd.get(i).lo.to_bits());
    }
}

/// A x = b to quad-double by the field refinement: two steps give x0 back within 1e-60 of max |x0| (about 1e-64 seen;
/// b's rounding to quad-double and A's condition number allow about 1e-62), and three the same. Controls: without
/// refinement the solve misses by more than 1e-40 (double-double accuracy, about 1e-32 seen); with a residual off by
/// 1e-40 relative (A scaled by 1 + 1e-40 in it) the refinement converges to the wrong system and misses 1e-60.
#[test]
fn field_refine_reaches_quad_double() {
    let mut r = Rng(62);
    for _ in 0..4 {
        let (d, lu, x0, b) = qd_system(&mut r);
        let bq = qfield(&b);
        let resid = |x: &Fl<QV, B>| bq - d.apply(x);
        let e2 = qd_err(&qvalues(&lu.solve_lanes_refine(&bq, 2, resid)), &x0);
        let e3 = qd_err(&qvalues(&lu.solve_lanes_refine(&bq, 3, resid)), &x0);
        assert!(
            e2 <= 1e-60 && e3 <= 1e-60,
            "refined: {e2:e} (2 steps), {e3:e} (3 steps)"
        );
        let e0 = qd_err(&qvalues(&lu.solve_lanes_refine(&bq, 0, resid)), &x0);
        assert!(e0 > 1e-40, "control: the unrefined solve is within 1e-40 ({e0:e})");
        let s = QV::splat(QD::from_f64(1.0).add_f(1e-40));
        let wrong = |x: &Fl<QV, B>| bq - Fl(d.apply(x).0.map(|v| v * s));
        let ew = qd_err(&qvalues(&lu.solve_lanes_refine(&bq, 3, wrong)), &x0);
        assert!(ew > 1e-60, "control: a residual off by 1e-40 passes ({ew:e})");
    }
}

#[test]
#[should_panic(expected = "FieldSolve: a DDLu of order 8 for a field of 16 values")]
fn field_refine_refuses_a_smaller_lu() {
    let f = qfield(&[QD::from_f64(1.0); M]);
    lu_of_order(M - 8).solve_lanes_refine(&f, 2, |x| *x);
}
