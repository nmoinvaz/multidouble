//! `Ou`, the octo-double dual (value and tangent in `OV`): its value and partial derivatives against exact arithmetic
//! (`exact::Dy`) to octo-double accuracy, on a polynomial and, by its residuals, on a rational function; Jacobian
//! columns of a field function seeded with `Fl::from_vt_od` and unit tangents against the exact Jacobian; the
//! refinement of a solve with a matrix tangent (`FieldSolve::solve_lanes_refine_t`) against a reference; and bit for
//! bit, the value against `OV` through every `Lane` method, the accessors, `Counted` and pinned outputs. `OJet<2>`
//! agrees with it to octo-double rounding.
//!
//! Controls: the quad-double dual `Qu` on the octo-double checks, the transposed matrix in the Jacobian, too few
//! refinement steps and a residual off by 1e-100, and (feature `mutate`) a tangent term of the product dropped
//! (`dual::mutate::OU_TAN`).
//!
//! Every check runs on a thread with a 64 MiB stack (`common::big_stack`).
#![allow(clippy::needless_range_loop)]
mod common;
use common::{big_stack, Rng};
use multidouble::dd::DD;
use multidouble::dual::{Counted, Lane};
use multidouble::dv::DV;
use multidouble::exact::Dy;
use multidouble::field::{DMat, FieldSolve, Fl};
use multidouble::linalg::{ld_for, DDLu};
use multidouble::native::{OJet, Ou, Qu, OV, QV};
use multidouble::od::OD;
use multidouble::qd::QD;
use multidouble::simd::Native;

type Dv = DV<Native>;
const B: usize = 2;
const M: usize = 8 * B;

/// octo-double accuracy, about 700 units of 2^-418
const OD_TOL: f64 = 1e-123;

/// h (1 + O(2^-53)) with all eight parts in use
fn od_of(r: &mut Rng, h: f64) -> OD {
    let mut x = [0.0; 8];
    x[0] = h;
    for i in 1..8 {
        x[i] = x[i - 1] * 2f64.powi(-53) * r.sym();
    }
    OD::new(x)
}

/// an octo-double lo + w u, u uniform in [0, 1), with all eight parts in use
fn od_u(r: &mut Rng, lo: f64, w: f64) -> OD {
    let h = lo + w * r.unit();
    od_of(r, h)
}

/// an octo-double w u, u uniform in [-1, 1), with all eight parts in use
fn od_s(r: &mut Rng, w: f64) -> OD {
    let h = w * r.sym();
    od_of(r, h)
}

fn dv(v: &[DD; 8]) -> Dv {
    let hi: Vec<f64> = v.iter().map(|d| d.hi).collect();
    let lo: Vec<f64> = v.iter().map(|d| d.lo).collect();
    DV::load(&hi, &lo)
}

fn pow(x: &Dy, k: usize) -> Dy {
    (0..k).fold(Dy::from_f64(1.0), |p, _| p.mul(x))
}

/// |got - want| / scale, exactly up to the f64 of the ratio
fn err(got: &Dy, want: &Dy, scale: &Dy) -> f64 {
    got.sub(want).abs().ratio(scale)
}

/// the bits of every part of every lane
fn obits(v: OV) -> Vec<u64> {
    v.lanes().iter().flat_map(|d| d.x.map(f64::to_bits)).collect()
}

/// a lane of octo-double values with a tangent of one or zero
fn seeded(x: &[OD; 8], t: f64) -> Ou {
    Ou {
        v: OV::from_lanes(x),
        d: OV::splat_f(t),
    }
}

// ---------------------------------------------------------------------------------------------------------------
// against exact derivatives
// ---------------------------------------------------------------------------------------------------------------

/// p(x, y) = x^5 - 3 x^3 y + c x + 2 y^2, written once over `Lane`
fn poly<T: Lane>(x: T, y: T, c: DD) -> T {
    let x2 = x * x;
    let x3 = x2 * x;
    x3 * x2 - (x3 * y).mulf(3.0) + x.muls(c) + (y * y).mul_pwr2(2.0)
}

/// the terms of p, of dp/dx = 5 x^4 - 9 x^2 y + c and of dp/dy = -3 x^3 + 4 y, exactly
fn poly_terms(x: &Dy, y: &Dy, c: &Dy) -> [Vec<Dy>; 3] {
    let f = Dy::from_f64;
    [
        vec![
            pow(x, 5),
            pow(x, 3).mul(y).mul(&f(-3.0)),
            c.mul(x),
            y.mul(y).mul(&f(2.0)),
        ],
        vec![pow(x, 4).mul(&f(5.0)), pow(x, 2).mul(y).mul(&f(-9.0)), c.clone()],
        vec![pow(x, 3).mul(&f(-3.0)), y.mul(&f(4.0))],
    ]
}

/// the worst error of p and its partials at octo-double inputs, relative to the sum of the terms' magnitudes, from the
/// value and the tangents `eval(x, y, c)` returns per lane ([p, dp/dx, dp/dy] at lane j, exactly)
fn poly_error(rounds: usize, eval: impl Fn(&[OD; 8], &[OD; 8], DD) -> Vec<[Dy; 3]>) -> f64 {
    let mut r = Rng(31);
    let mut worst = 0.0f64;
    for _ in 0..rounds {
        let xs: [OD; 8] = std::array::from_fn(|_| od_s(&mut r, 2.0));
        let ys: [OD; 8] = std::array::from_fn(|_| od_s(&mut r, 2.0));
        let c = r.dd(1);
        let got = eval(&xs, &ys, c);
        for j in 0..8 {
            let terms = poly_terms(&xs[j].exact(), &ys[j].exact(), &Dy::sum(&[c.hi, c.lo]));
            for (t, g) in terms.iter().zip(got[j].iter()) {
                let want = t.iter().fold(Dy::zero(), |s, x| s.add(x));
                let mag = t.iter().fold(Dy::zero(), |s, x| s.add(&x.abs()));
                worst = worst.max(err(g, &want, &mag));
            }
        }
    }
    worst
}

/// p and its partials from `Ou` lanes: one evaluation per partial, the value of both evaluations checked
fn poly_ou(xs: &[OD; 8], ys: &[OD; 8], c: DD) -> Vec<[Dy; 3]> {
    let gx = poly(seeded(xs, 1.0), seeded(ys, 0.0), c);
    let gy = poly(seeded(xs, 0.0), seeded(ys, 1.0), c);
    assert_eq!(obits(gx.v), obits(gy.v), "the value depends on the seed");
    (0..8)
        .map(|j| [gx.v.lane(j).exact(), gx.d.lane(j).exact(), gy.d.lane(j).exact()])
        .collect()
}

/// Ou's value and partial derivatives of p within OD_TOL of the exact ones; `Qu` on the same check (the inputs rounded
/// to quad-double) errs by quad-double rounding (the control that the bound tells the two apart)
#[test]
fn ou_gives_exact_partial_derivatives_of_a_polynomial() {
    big_stack(|| {
        let e = poly_error(40, poly_ou);
        println!("Ou on x^5 - 3 x^3 y + c x + 2 y^2: worst error {e:.1e} of the terms' magnitudes");
        assert!(e < OD_TOL, "{e:e}");
        let eq = poly_error(10, |xs, ys, c| {
            let q = |v: &[OD; 8], t: f64| Qu {
                v: QV::from_lanes(&v.map(|x| x.to_qd())),
                d: QV::splat_f(t),
            };
            let gx = poly(q(xs, 1.0), q(ys, 0.0), c);
            let gy = poly(q(xs, 0.0), q(ys, 1.0), c);
            (0..8)
                .map(|j| [gx.v.lane(j).exact(), gx.d.lane(j).exact(), gy.d.lane(j).exact()])
                .collect()
        });
        println!("Qu on the octo-double check: {eq:.1e}");
        assert!(
            eq > 1e3 * OD_TOL && eq < 1e-58,
            "control: the quad-double dual's error {eq:e}"
        );
    })
}

/// f(x, y) = (x^3 + 2 x y) / (x + 3), written over `Lane`
fn f<T: Lane>(x: T, y: T) -> T {
    (x * x * x + (x * y).mulf(2.0)) / x.addc(DV::splat_f(3.0))
}

/// f = N / D with N = x^3 + 2 x y and D = x + 3, by the residuals of its value and partials, exactly: f D - N,
/// f_x D^2 - (N_x D - N) with N_x = 3 x^2 + 2 y, and f_y D - 2 x, each relative to the magnitudes of its terms. All
/// within OD_TOL.
#[test]
fn ou_gives_exact_derivatives_of_a_rational_function() {
    big_stack(|| {
        let mut r = Rng(32);
        let mut worst = 0.0f64;
        for _ in 0..40 {
            let xs: [OD; 8] = std::array::from_fn(|_| od_u(&mut r, 1.0, 4.0));
            let ys: [OD; 8] = std::array::from_fn(|_| od_s(&mut r, 5.0));
            let gx = f(seeded(&xs, 1.0), seeded(&ys, 0.0));
            let gy = f(seeded(&xs, 0.0), seeded(&ys, 1.0));
            let k = Dy::from_f64;
            for j in 0..8 {
                let (x, y) = (xs[j].exact(), ys[j].exact());
                let (v, fx, fy) = (gx.v.lane(j).exact(), gx.d.lane(j).exact(), gy.d.lane(j).exact());
                let n = pow(&x, 3).add(&k(2.0).mul(&x).mul(&y));
                let d = x.add(&k(3.0));
                let nx = k(3.0).mul(&x).mul(&x).add(&k(2.0).mul(&y));
                let ny = k(2.0).mul(&x);
                let res = [
                    (v.mul(&d), n.clone()),
                    (fx.mul(&d).mul(&d), nx.mul(&d).sub(&n)),
                    (fy.mul(&d), ny),
                ];
                for (a, b) in res {
                    let scale = a.abs().add(&b.abs());
                    worst = worst.max(err(&a, &b, &scale));
                }
            }
        }
        println!("Ou on (x^3 + 2 x y) / (x + 3): worst residual {worst:.1e}");
        assert!(worst < OD_TOL, "{worst:e}");
    })
}

/// Control with the built-in breakage: the product without its tangent term d o.v (`dual::mutate::OU_TAN`) fails the
/// exact check of the polynomial's partials.
#[cfg(feature = "mutate")]
#[test]
fn control_dropped_tangent_is_caught() {
    big_stack(|| {
        use multidouble::dual::mutate;
        mutate::set(mutate::OU_TAN);
        let e = poly_error(2, poly_ou);
        mutate::set(0);
        println!("control: the product's tangent without d o.v {e:.1e}");
        assert!(e > 1e-3, "control: a dropped tangent term passes ({e:e})");
    })
}

// ---------------------------------------------------------------------------------------------------------------
// Jacobian columns and solves
// ---------------------------------------------------------------------------------------------------------------

/// a double-double matrix of order M, row-major, diagonally dominant
fn dd_matrix(r: &mut Rng) -> Vec<DD> {
    (0..M * M)
        .map(|k| {
            let d = if k / M == k % M { 4.0 } else { 0.0 };
            DD::new(r.sym() + d, r.sym() * 1e-17)
        })
        .collect()
}

fn dmat(a: &[DD]) -> DMat<Native, B> {
    let (h, l): (Vec<f64>, Vec<f64>) = a.iter().map(|d| (d.hi, d.lo)).unzip();
    DMat::from_rows(&h, &l)
}

fn ofield(v: &[OD]) -> Fl<OV, B> {
    Fl(std::array::from_fn(|b| {
        OV::from_lanes(v[8 * b..8 * b + 8].try_into().unwrap())
    }))
}

fn ovalues(f: &Fl<OV, B>) -> Vec<OD> {
    (0..M).map(|i| f.get(i)).collect()
}

/// F(f) = (D f) f + 3 f, pointwise products, over any lane type
fn field_fn<T: multidouble::field::MatLane<S = Native>>(d: &DMat<Native, B>, f: &Fl<T, B>) -> Fl<T, B> {
    d.apply(f) * *f + f.mulf(3.0)
}

/// the worst error of Jacobian columns j of F at x, `col(j)` (value i exactly), against the exact
/// J_ij = D_ij x_i + delta_ij ((D x)_i + 3), relative to sum_l |D_il x_l| + |D_ij x_i| + 3
fn jac_error(a: &[DD], x: &[OD], col: impl Fn(usize) -> Vec<Dy>) -> f64 {
    let ae: Vec<Dy> = a.iter().map(|d| Dy::sum(&[d.hi, d.lo])).collect();
    let xe: Vec<Dy> = x.iter().map(|v| v.exact()).collect();
    let mut worst = 0.0f64;
    for j in [0, 3, 8, M - 1] {
        let c = col(j);
        for i in 0..M {
            let (mut dx, mut mag) = (Dy::zero(), Dy::zero());
            for l in 0..M {
                let t = ae[i * M + l].mul(&xe[l]);
                mag = mag.add(&t.abs());
                dx = dx.add(&t);
            }
            let mut want = ae[i * M + j].mul(&xe[i]);
            mag = mag.add(&want.abs()).add(&Dy::from_f64(3.0));
            if i == j {
                want = want.add(&dx).add(&Dy::from_f64(3.0));
            }
            worst = worst.max(err(&c[i], &want, &mag));
        }
    }
    worst
}

/// Jacobian columns by forward mode: `Fl::<Ou, B>::from_vt_od(x, unit(j))`, F evaluated once per column, its tangent
/// against the exact J's column j within OD_TOL, its value bitwise F on `OV`. Controls: `Qu` columns (x rounded to
/// quad-double) miss the bound, and the columns of D transposed miss by far.
#[test]
fn ou_jacobian_columns_are_exact() {
    big_stack(|| {
        let mut r = Rng(33);
        let a = dd_matrix(&mut r);
        let d = dmat(&a);
        let x: Vec<OD> = (0..M).map(|_| od_s(&mut r, 1.0)).collect();
        let fv = field_fn(&d, &ofield(&x));
        let col = |j: usize| -> Vec<Dy> {
            let s = field_fn(&d, &Fl::<Ou, B>::from_vt_od(&ofield(&x), &Fl::<OV, B>::unit(j)));
            assert!(
                (0..M).all(|i| obits(OV::splat(s.coef_od(0).get(i))) == obits(OV::splat(fv.get(i)))),
                "the value of column {j} is not F on OV"
            );
            ovalues(&s.coef_od(1)).iter().map(|v| v.exact()).collect()
        };
        let e = jac_error(&a, &x, col);
        println!("Ou Jacobian columns of (D f) f + 3 f: worst error {e:.1e}");
        assert!(e < OD_TOL, "{e:e}");
        let eq = jac_error(&a, &x, |j| {
            let xq: Fl<QV, B> = Fl(std::array::from_fn(|b| {
                QV::from_lanes(&std::array::from_fn(|l| x[8 * b + l].to_qd()))
            }));
            let s = field_fn(&d, &Fl::<Qu, B>::from_vt_qd(&xq, &Fl::<QV, B>::unit(j)));
            (0..M).map(|i| s.coef_qd(1).get(i).exact()).collect()
        });
        assert!(
            eq > 1e3 * OD_TOL && eq < 1e-58,
            "control: the quad-double columns' error {eq:e}"
        );
        let at: Vec<DD> = (0..M * M).map(|k| a[(k % M) * M + k / M]).collect();
        let dt = dmat(&at);
        let et = jac_error(&a, &x, |j| {
            let s = field_fn(&dt, &Fl::<Ou, B>::from_vt_od(&ofield(&x), &Fl::<OV, B>::unit(j)));
            ovalues(&s.coef_od(1)).iter().map(|v| v.exact()).collect()
        });
        assert!(et > 1e-3, "control: the transposed matrix's columns pass ({et:e})");
    })
}

/// the double-double LU of a row-major matrix of order M
fn lu_of(a: &[DD]) -> DDLu {
    let ld = ld_for(M);
    let (mut ch, mut cl) = (vec![0.0; ld * M], vec![0.0; ld * M]);
    for i in 0..M {
        for j in 0..M {
            ch[j * ld + i] = a[i * M + j].hi;
            cl[j * ld + i] = a[i * M + j].lo;
        }
    }
    DDLu::factor(M, ld, ch, cl, false).unwrap()
}

/// max |x_i - y_i| / max |y_i|
fn od_err(x: &[OD], y: &[OD]) -> f64 {
    let ym = y.iter().map(|v| v.x[0].abs()).fold(0.0, f64::max);
    x.iter()
        .zip(y)
        .map(|(a, b)| (*a - *b).to_f64().abs())
        .fold(0.0, f64::max)
        / ym
}

/// A(t) x(t) = b with A(t) = A + t E: the tangent of x is -A^-1 E x. With `Ou` lanes whose residual carries E x_v on
/// the tangent, five refinement steps of `solve_lanes_refine_t` give the value within 1e-120 of `solve_lanes_refine`'s
/// on `OV` and the tangent within 1e-118 of the reference -A^-1 E x, both refined to octo-double: twice `Qu`'s steps
/// and one more for the tangent. Controls: three steps leave the tangent above 1e-118, and a residual with E scaled by
/// 1 + 1e-100 converges to the wrong tangent.
#[test]
fn ou_refine_t_reaches_octo_double_with_a_matrix_tangent() {
    big_stack(|| {
        let mut r = Rng(34);
        let a = dd_matrix(&mut r);
        let (d, lu) = (dmat(&a), lu_of(&a));
        let e = dmat(&dd_matrix(&mut r));
        let bq = ofield(&(0..M).map(|_| od_s(&mut r, 1.0)).collect::<Vec<_>>());
        let xv = lu.solve_lanes_refine(&bq, 6, |x: &Fl<OV, B>| bq - d.apply(x));
        let ex = -e.apply(&xv);
        let t_ref = lu.solve_lanes_refine(&ex, 6, |x: &Fl<OV, B>| ex - d.apply(x));
        let rhs = Fl::<Ou, B>::from_vt_od(&bq, &Fl::zero());
        let resid = |scale: OD| {
            let (e, d, rhs) = (&e, &d, &rhs);
            move |x: &Fl<Ou, B>| {
                let ev = e.apply(&x.coef_od(0));
                *rhs - d.apply(x) - Fl::<Ou, B>::from_vt_od(&Fl::zero(), &Fl(ev.0.map(|v| v * OV::splat(scale))))
            }
        };
        let x5 = lu.solve_lanes_refine_t(&lu, &rhs, 5, resid(OD::ONE));
        let (ev, et) = (
            od_err(&ovalues(&x5.coef_od(0)), &ovalues(&xv)),
            od_err(&ovalues(&x5.coef_od(1)), &ovalues(&t_ref)),
        );
        println!("Ou refinement, five steps: value {ev:.1e}, tangent {et:.1e}");
        assert!(ev <= 1e-120 && et <= 1e-118, "value {ev:e}, tangent {et:e}");
        let x3 = lu.solve_lanes_refine_t(&lu, &rhs, 3, resid(OD::ONE));
        let e3 = od_err(&ovalues(&x3.coef_od(1)), &ovalues(&t_ref));
        assert!(e3 > 1e-118, "control: three steps give the tangent to {e3:e}");
        let xw = lu.solve_lanes_refine_t(&lu, &rhs, 5, resid(OD::ONE.add_f(1e-100)));
        let ew = od_err(&ovalues(&xw.coef_od(1)), &ovalues(&t_ref));
        assert!(ew > 1e-118, "control: E scaled by 1 + 1e-100 passes ({ew:e})");
    })
}

// ---------------------------------------------------------------------------------------------------------------
// bit for bit: the value, OJet<2>, accessors, pins
// ---------------------------------------------------------------------------------------------------------------

/// g(x, y, c) = ((c x - s y)(x/2) + x y + c x - (y + c)) / (x_0 + 3), written once over `Lane` through every one of
/// its methods (the product sum by the accumulator, x_0 by `bcast`)
fn every<T: Lane>(x: T, y: T, c: DV<T::S>, s: DD) -> T {
    let a = x.mulc(c) - y.muls(s);
    let p = T::fin(T::acc1(T::accc(T::acc(T::acc0(), x, y), x, c), -y.addc(c)));
    T::zero() + (a * x.mulf(0.5) + p) / (x.bcast(0) + T::splat(DD::from_f64(3.0)))
}

/// Ou's value is `OV`'s bit for bit through every `Lane` method (`every`), with octo-double inputs and double-double
/// constants; and `OJet<2>` gives Ou's value and tangent to octo-double rounding (within OD_TOL of max(1, |Ou|)), its
/// order 0 being `OV`'s bit for bit too
#[test]
fn ou_value_is_ov_and_ojet_two_is_ou() {
    big_stack(|| {
        let mut r = Rng(35);
        let s = DD::ONE / DD::from_f64(3.0);
        let mut worst = 0.0f64;
        for _ in 0..50 {
            let xs: [OD; 8] = std::array::from_fn(|_| od_u(&mut r, 2.0, 1.0));
            let ys: [OD; 8] = std::array::from_fn(|_| od_u(&mut r, 1.0, 1.0));
            let c = dv(&std::array::from_fn(|_| DD::new(1.0 + r.unit(), r.sym() * 1e-16)));
            let (x, y) = (OV::from_lanes(&xs), OV::from_lanes(&ys));
            let gv = every(x, y, c, s);
            let gu = every(seeded(&xs, 1.0), seeded(&ys, 0.0), c, s);
            assert_eq!(obits(gu.v), obits(gv), "Ou's value is not OV's");
            let jet = |v: OV, t: f64| OJet::<2>::from_coeffs([v, OV::splat_f(t)]);
            let gj = every(jet(x, 1.0), jet(y, 0.0), c, s);
            assert_eq!(obits(gj.c[0]), obits(gv), "OJet<2>'s order 0 is not OV's");
            for l in 0..8 {
                let (a, b) = (gj.c[1].lane(l), gu.d.lane(l));
                worst = worst.max((a - b).to_f64().abs() / b.to_f64().abs().max(1.0));
            }
        }
        println!("OJet<2> against Ou: worst tangent difference {worst:.1e}");
        assert!(worst < OD_TOL, "{worst:e}");
    })
}

/// the flags, the accessors (`coef_od` exact, `coef_qd`, `val`, `tan` rounded), `from_vt`, `mul_pwr2`, `bcast`,
/// `Counted`, `Fl::from_vt_od` and the matrix product (`MatLane`), whose value is `OV`'s bit for bit
#[test]
fn ou_accessors_flags_and_counted() {
    big_stack(|| {
        fn flags<T: Lane>() -> (bool, bool, bool, usize) {
            (T::TANGENT, T::VAL_QD, T::VAL_OD, T::NJ)
        }
        assert_eq!(flags::<Ou>(), (true, false, true, 0));
        assert_eq!(flags::<Counted<Ou>>(), (true, false, true, 0));
        let mut r = Rng(36);
        for _ in 0..20 {
            let u = Ou {
                v: OV::from_lanes(&std::array::from_fn(|_| od_s(&mut r, 3.0))),
                d: OV::from_lanes(&std::array::from_fn(|_| od_s(&mut r, 3.0))),
            };
            assert_eq!(obits(u.coef_od(0)), obits(u.v), "coef_od(0)");
            assert_eq!(obits(u.coef_od(1)), obits(u.d), "coef_od(1)");
            assert_eq!(obits(u.coef_od(2)), obits(OV::zero()), "coef_od(2)");
            assert_eq!(obits(Counted(u).coef_od(1)), obits(u.d), "Counted coef_od");
            for l in 0..8 {
                assert_eq!(u.coef_qd(1).lane(l).x, u.d.lane(l).to_qd().x, "coef_qd rounds");
                assert_eq!(u.val().lane(l), u.v.lane(l).to_dd(), "val rounds");
                assert_eq!(u.tan().lane(l), u.d.lane(l).to_dd(), "tan rounds");
            }
            let (vd, td) = (u.v.to_dv(), u.d.to_dv());
            let w = Ou::from_vt(vd, td);
            assert_eq!(obits(w.v), obits(OV::from_dv(vd)), "from_vt");
            assert_eq!(obits(w.d), obits(OV::from_dv(td)), "from_vt tangent");
            let p = 2f64.powi((r.next_u64() % 401) as i32 - 200);
            let (a, b) = (u.mul_pwr2(p), u.mulf(p));
            assert!(obits(a.v) == obits(b.v) && obits(a.d) == obits(b.d), "mul_pwr2");
            let bc = u.bcast(6);
            assert_eq!(obits(bc.d), obits(OV::splat(u.d.lane(6))), "bcast");
        }
        let a = dd_matrix(&mut r);
        let d = dmat(&a);
        let (v, t) = (
            ofield(&(0..M).map(|_| od_s(&mut r, 1.0)).collect::<Vec<_>>()),
            ofield(&(0..M).map(|_| od_s(&mut r, 1.0)).collect::<Vec<_>>()),
        );
        let f = Fl::<Ou, B>::from_vt_od(&v, &t);
        for i in 0..M {
            assert!(
                obits(OV::splat(f.coef_od(0).get(i))) == obits(OV::splat(v.get(i))),
                "from_vt_od value"
            );
            assert!(
                obits(OV::splat(f.coef_od(1).get(i))) == obits(OV::splat(t.get(i))),
                "from_vt_od tangent"
            );
        }
        let (pu, pv, pt) = (d.apply(&f), d.apply(&v), d.apply(&t));
        for i in 0..M {
            assert!(
                obits(OV::splat(pu.coef_od(0).get(i))) == obits(OV::splat(pv.get(i))),
                "D f value"
            );
            assert!(
                obits(OV::splat(pu.coef_od(1).get(i))) == obits(OV::splat(pt.get(i))),
                "D f tangent"
            );
        }
    })
}

/// FNV-1a over the bits of every part of every lane
fn fold_bits(h: u64, v: &[OV]) -> u64 {
    v.iter()
        .flat_map(|x| x.lanes())
        .flat_map(|l| l.x.map(f64::to_bits))
        .fold(h, |h, w| (h ^ w).wrapping_mul(0x0000_0100_0000_01b3))
}

/// Ou's outputs pinned bit for bit on fixed inputs, against hashes recorded with the first implementation: the
/// product and quotient, the accumulator, and `every`. Every backend gives these bits (tests/lanes.rs checks the lanes
/// against scalar octo-double formulas).
#[test]
fn ou_outputs_are_pinned() {
    big_stack(|| {
        let mut r = Rng(37);
        let fnv = 0xcbf2_9ce4_8422_2325u64;
        let mut h = [fnv; 3];
        let s = DD::ONE / DD::from_f64(7.0);
        for _ in 0..20 {
            let lane = |r: &mut Rng, lo: f64| Ou {
                v: OV::from_lanes(&std::array::from_fn(|_| od_u(r, lo, 1.0))),
                d: OV::from_lanes(&std::array::from_fn(|_| od_s(r, 1.0))),
            };
            let (x, y) = (lane(&mut r, 0.0), lane(&mut r, 1.0));
            let c = dv(&std::array::from_fn(|_| r.dd(2)));
            let (p, q) = (x * y, x / y);
            h[0] = fold_bits(h[0], &[p.v, p.d, q.v, q.d]);
            let a = Ou::fin(Ou::acc1(Ou::accc(Ou::acc(Ou::acc0(), x, y), y, c), x));
            h[1] = fold_bits(h[1], &[a.v, a.d]);
            let e = every(x, y, c, s);
            h[2] = fold_bits(h[2], &[e.v, e.d]);
        }
        let want: [u64; 3] = [0x7148_53fe_4e83_a63b, 0xb21b_51fe_70f7_c42f, 0x8e16_687c_c7cf_cb6b];
        let names = ["product and quotient", "accumulator", "every Lane method"];
        let bad: Vec<String> = (0..3)
            .filter(|&i| h[i] != want[i])
            .map(|i| format!("{}: {:#018x} pinned {:#018x}", names[i], h[i], want[i]))
            .collect();
        assert!(bad.is_empty(), "{bad:?}");
        let _ = QD::ZERO;
    })
}
