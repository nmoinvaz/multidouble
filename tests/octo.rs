//! `OV` as a `Lane`: every trait method against the scalar `OD` operations bit for bit, generic code run in octo-double
//! against exact arithmetic (`exact::Dy`) and against the same code in quad-double, a constant double-double matrix
//! applied to an octo-double field (`DMat::apply`), and `FieldSolve::solve_lanes_refine` refining a double-double LU's
//! solve to octo-double. The outputs of the lanes are pinned bit for bit. Each accuracy check has a control.
#![allow(clippy::needless_range_loop)]
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::dual::{Counted, Lane};
use multidouble::exact::Dy;
use multidouble::field::{DMat, FieldSolve, Fl};
use multidouble::linalg::{ld_for, DDLu};
use multidouble::native::{ODotAcc, OV, QV};
use multidouble::od::{OdAcc, OD};
use multidouble::qd::QD;
use multidouble::simd::Native;

type Dv = multidouble::dv::DV<Native>;
const B: usize = 2;
const M: usize = 8 * B;

/// an octo-double h (1 + O(2^-53)) with all eight parts in use
fn od_of(r: &mut Rng, h: f64) -> OD {
    let mut x = [0.0; 8];
    x[0] = h;
    for i in 1..8 {
        x[i] = x[i - 1] * 2f64.powi(-53) * r.sym();
    }
    OD::new(x)
}

/// an octo-double lo + u, u uniform in [0, 1)
fn od_u(r: &mut Rng, lo: f64) -> OD {
    let h = lo + r.unit();
    od_of(r, h)
}

fn od_s(r: &mut Rng, w: f64) -> OD {
    let h = w * r.sym();
    od_of(r, h)
}

fn dv(v: &[DD; 8]) -> Dv {
    let hi: Vec<f64> = v.iter().map(|d| d.hi).collect();
    let lo: Vec<f64> = v.iter().map(|d| d.lo).collect();
    Dv::load(&hi, &lo)
}

fn same(a: OD, b: OD) -> bool {
    a.x.iter().zip(b.x.iter()).all(|(x, y)| x.to_bits() == y.to_bits())
}

fn assert_lanes(what: &str, v: OV, want: impl Fn(usize) -> OD) {
    for j in 0..8 {
        let (g, w) = (v.lane(j), want(j));
        assert!(same(g, w), "{what} lane {j}: {:?} vs {:?}", g.x, w.x);
    }
}

/// Every `Lane` method of `OV` is the scalar operation it stands for, lane by lane and bit for bit: constants enter
/// as double-double exactly, `val` is `to_dd`, `coef_qd(0)` is `to_qd`, the accumulator is `OdAcc`. `Counted<OV>`
/// forwards the constants and the values.
#[test]
fn ov_lane_methods_are_the_scalar_operations() {
    const { assert!(OV::VAL_OD && !OV::VAL_QD && !OV::TANGENT && OV::NJ == 0) };
    const { assert!(Counted::<OV>::VAL_OD && !Counted::<OV>::VAL_QD) };
    const { assert!(!QV::VAL_OD && !multidouble::native::DV::VAL_OD) };
    let mut r = Rng(81);
    for _ in 0..50 {
        let xs: [OD; 8] = std::array::from_fn(|_| od_s(&mut r, 4.0));
        let ys: [OD; 8] = std::array::from_fn(|_| od_u(&mut r, 1.0));
        let cs: [DD; 8] = std::array::from_fn(|_| r.dd(3));
        let (x, y, c) = (OV::from_lanes(&xs), OV::from_lanes(&ys), dv(&cs));
        let cd = |j: usize| OD::from_dd(cs[j]);
        assert_lanes("cst", <OV as Lane>::cst(c), cd);
        assert_lanes("mulc", x.mulc(c), |j| xs[j] * cd(j));
        assert_lanes("muls", x.muls(cs[0]), |j| xs[j] * cd(0));
        assert_lanes("addc", x.addc(c), |j| xs[j] + cd(j));
        assert_lanes("mulf", x.mulf(3.0), |j| xs[j].mul_f(3.0));
        assert_lanes("mul_pwr2", Lane::mul_pwr2(x, 0.125), |j| xs[j].mul_pwr2(0.125));
        assert_lanes("bcast", Lane::bcast(x, 5), |_| xs[5]);
        assert_lanes("from_vt", OV::from_vt(c, c), cd);
        assert_lanes("add", x + y, |j| xs[j] + ys[j]);
        assert_lanes("sub", x - y, |j| xs[j] - ys[j]);
        assert_lanes("mul", x * y, |j| xs[j] * ys[j]);
        assert_lanes("div", x / y, |j| xs[j] / ys[j]);
        assert_lanes("neg", -x, |j| -xs[j]);
        let a = OV::fin(OV::acc1(OV::accc(OV::acc(OV::acc0(), x, y), y, c), x));
        assert_lanes("acc", a, |j| {
            OdAcc::zero()
                .add_prod(xs[j], ys[j])
                .add_prod(ys[j], cd(j))
                .add(xs[j])
                .finish()
        });
        let v = x.val();
        let q = x.coef_qd(0);
        for j in 0..8 {
            assert_eq!(v.lane(j), xs[j].to_dd(), "val lane {j}");
            assert_eq!(x.coef(0).lane(j), xs[j].to_dd(), "coef(0) lane {j}");
            assert_eq!(q.lane(j).x, xs[j].to_qd().x, "coef_qd(0) lane {j}");
            assert_eq!(x.tan().lane(j), DD::ZERO);
            assert_eq!(x.coef_qd(1).lane(j).x, [0.0; 4]);
        }
        let cx = Counted(x) * Counted(y) + Counted(x);
        assert_lanes("Counted", cx.0, |j| xs[j] * ys[j] + xs[j]);
    }
}

fn pow(x: &Dy, k: usize) -> Dy {
    (0..k).fold(Dy::from_f64(1.0), |p, _| p.mul(x))
}

/// p(x) = x^5 - 3 x^3 y + c x + 2 y^2, written once over `Lane`
fn poly<T: Lane>(x: T, y: T, c: DD) -> T {
    let x2 = x * x;
    let x3 = x2 * x;
    x3 * x2 - (x3 * y).mulf(3.0) + x.muls(c) + (y * y).mul_pwr2(2.0)
}

/// Generic code over `Lane` in octo-double: a polynomial against its exact value, within 2^-410 of the sum of its
/// terms' magnitudes (4e-124 relative; about 2e-129 seen), and against the same code in quad-double (QV) within
/// 1e-60 of that sum. Control: the quad-double lanes miss the octo-double bound by more than 1e50.
#[test]
fn generic_lane_code_in_octo_double() {
    let mut r = Rng(82);
    let tol = 2f64.powi(-410);
    let (mut worst, mut worst_q) = (0f64, 0f64);
    for _ in 0..40 {
        let xs: [OD; 8] = std::array::from_fn(|_| od_s(&mut r, 2.0));
        let ys: [OD; 8] = std::array::from_fn(|_| od_s(&mut r, 2.0));
        let c = r.dd(1);
        let p = poly(OV::from_lanes(&xs), OV::from_lanes(&ys), c);
        let pq = poly(
            QV::from_lanes(&std::array::from_fn(|j| xs[j].to_qd())),
            QV::from_lanes(&std::array::from_fn(|j| ys[j].to_qd())),
            c,
        );
        for j in 0..8 {
            // the exact value of the polynomial at the octo-double inputs, and the sum of its terms' magnitudes
            let (x, y, cc) = (xs[j].exact(), ys[j].exact(), Dy::sum(&[c.hi, c.lo]));
            let terms = [
                pow(&x, 5),
                pow(&x, 3).mul(&y).mul(&Dy::from_f64(-3.0)),
                cc.mul(&x),
                y.mul(&y).mul(&Dy::from_f64(2.0)),
            ];
            let exact = terms.iter().fold(Dy::zero(), |s, t| s.add(t));
            let mag = terms.iter().fold(Dy::zero(), |s, t| s.add(&t.abs()));
            let e = p.lane(j).exact().sub(&exact).abs().ratio(&mag);
            let eq = pq.lane(j).exact().sub(&exact).abs().ratio(&mag);
            assert!(e <= tol, "lane {j}: {e:e} of the terms");
            assert!(eq <= 1e-60, "quad-double lane {j}: {eq:e} of the terms");
            worst = worst.max(e);
            worst_q = worst_q.max(eq);
        }
    }
    println!("polynomial: octo-double {worst:.2e}, quad-double {worst_q:.2e} of the terms' magnitudes");
    assert!(
        worst_q > 1e50 * tol,
        "control: the quad-double lanes pass the octo-double bound ({worst_q:e})"
    );
}

/// a double-double matrix of order M (rows i, columns j at [i * M + j]): diagonally dominant, or random with rows and
/// columns scaled by 2^-(i + j)/2 (2^0 to 2^-15), a larger condition number
fn dd_matrix(r: &mut Rng, graded: bool) -> Vec<DD> {
    (0..M * M)
        .map(|k| {
            let (i, j) = (k / M, k % M);
            let s = if graded {
                2f64.powf(-((i + j) as f64) / 2.0)
            } else {
                1.0
            };
            let d = if i == j && !graded { 4.0 } else { 0.0 };
            DD::new(s * (r.sym() + d), s * r.sym() * 1e-17)
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
    f.0.iter().flat_map(|v| v.lanes()).collect()
}

/// the exact A x rounded to eight parts (greedy) and the exact sum of |A_ij x_j| per row
fn exact_matvec(a: &[DD], x: &[OD]) -> (Vec<Dy>, Vec<Dy>) {
    (0..M)
        .map(|i| {
            let (mut s, mut m) = (Dy::zero(), Dy::zero());
            for j in 0..M {
                let t = Dy::sum(&[a[i * M + j].hi, a[i * M + j].lo]).mul(&x[j].exact());
                m = m.add(&t.abs());
                s = s.add(&t);
            }
            (s, m)
        })
        .unzip()
}

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

/// D f for octo-double lanes: each row's sum of |D_ij f_j| bounds the error by 2^-418 (about 2^-431 seen), and the
/// product is the scalar accumulator over the columns in order, bit for bit. Control: D transposed misses the bound.
#[test]
fn matrix_product_in_octo_double() {
    let mut r = Rng(83);
    let a = dd_matrix(&mut r, false);
    let d = dmat(&a);
    let x: Vec<OD> = (0..M).map(|_| od_s(&mut r, 1.0)).collect();
    let y = ovalues(&d.apply(&ofield(&x)));
    let (want, mag) = exact_matvec(&a, &x);
    let at: Vec<DD> = (0..M * M).map(|k| a[(k % M) * M + k / M]).collect();
    let yt = ovalues(&dmat(&at).apply(&ofield(&x)));
    let mut worst_t = 0f64;
    for i in 0..M {
        let e = y[i].exact().sub(&want[i]).abs().ratio(&mag[i]);
        assert!(e <= OD::EPS, "row {i}: {e:e}");
        worst_t = worst_t.max(yt[i].exact().sub(&want[i]).abs().ratio(&mag[i]));
        let mut s = OdAcc::zero();
        for j in 0..M {
            s = s.add_prod(x[j], OD::from_dd(a[i * M + j]));
        }
        assert!(same(s.finish(), y[i]), "row {i}: not the scalar accumulator");
    }
    assert!(worst_t > 1e-10, "control: the transposed product passes ({worst_t:e})");
    let _ = ODotAcc::zero();
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

/// A x = b to octo-double by refining a double-double LU's solve with the residual b - A x in octo-double lanes
/// (`solve_lanes_refine` on `OV`), b = A x0 formed exactly and rounded to eight parts. Each step multiplies the error
/// by about cond(A) 2^-104: on diagonally dominant matrices four steps reach x0 within 1e-120 (about 1e-131 seen),
/// and on a random graded one five do. Controls: two steps, the quad-double count, miss by more than 1e-100, and a
/// residual off by 1e-100 relative converges to the wrong system.
#[test]
fn field_refine_reaches_octo_double() {
    let mut r = Rng(84);
    for (graded, steps) in [(false, 4), (false, 4), (true, 5)] {
        let a = dd_matrix(&mut r, graded);
        let (d, lu) = (dmat(&a), lu_of(&a));
        let x0: Vec<OD> = (0..M).map(|_| od_s(&mut r, 1.0)).collect();
        let b: Vec<OD> = exact_matvec(&a, &x0).0.iter().map(greedy8).collect();
        let bf = ofield(&b);
        let resid = |x: &Fl<OV, B>| bf - d.apply(x);
        let e = od_err(&ovalues(&lu.solve_lanes_refine(&bf, steps, resid)), &x0);
        let e1 = od_err(&ovalues(&lu.solve_lanes_refine(&bf, steps + 1, resid)), &x0);
        assert!(
            e <= 1e-120 && e1 <= 1e-120,
            "graded {graded}: {e:e} ({steps} steps), {e1:e}"
        );
        let e2 = od_err(&ovalues(&lu.solve_lanes_refine(&bf, 2, resid)), &x0);
        assert!(e2 > 1e-100, "control: two steps reach 1e-100 ({e2:e})");
        let s = OV::splat(OD::ONE.add_f(1e-100));
        let wrong = |x: &Fl<OV, B>| bf - Fl(d.apply(x).0.map(|v| v * s));
        let ew = od_err(&ovalues(&lu.solve_lanes_refine(&bf, steps, wrong)), &x0);
        assert!(ew > 1e-120, "control: a residual off by 1e-100 passes ({ew:e})");
        println!("graded {graded}: {steps} steps {e:.1e}, two steps {e2:.1e}");
    }
}

/// FNV-1a over the bits of every part of every lane, in order
fn fold_bits(h: u64, v: &[OV]) -> u64 {
    let mut h = h;
    for x in v {
        for l in x.lanes() {
            for w in l.x.map(f64::to_bits) {
                h = (h ^ w).wrapping_mul(0x0000_0100_0000_01b3);
            }
        }
    }
    h
}

/// The lanes' outputs pinned bit for bit on fixed inputs, against hashes recorded with the first implementation:
/// add, sub, mul, div, div_by, sqrt, od + f64, od x f64, the accumulator, and the conversions. Every backend gives
/// these bits (the lanes are the scalar arithmetic's, `tests/lanes.rs`).
#[test]
fn octo_double_outputs_are_pinned() {
    let mut r = Rng(85);
    let fnv = 0xcbf2_9ce4_8422_2325u64;
    let mut h = [fnv; 6];
    for _ in 0..40 {
        let x = OV::from_lanes(&std::array::from_fn(|_| od_s(&mut r, 8.0)));
        let y = OV::from_lanes(&std::array::from_fn(|_| od_u(&mut r, 1.0)));
        let f = multidouble::v8::V8::from_array(std::array::from_fn(|_| r.dd(5).hi));
        h[0] = fold_bits(h[0], &[x + y, x - y, -x]);
        h[1] = fold_bits(h[1], &[x * y, x.mul_v(f), x.add_v(f)]);
        h[2] = fold_bits(h[2], &[x / y, x.div_by(y, y.c[0].divisor()), y.recip()]);
        h[3] = fold_bits(h[3], &[y.sqrt(), x.abs().sqrt()]);
        let acc = ODotAcc::zero().add_prod(x, y).add_prod(y, y).add(x).finish();
        h[4] = fold_bits(h[4], &[acc]);
        let c = [OV::from_qv(x.to_qv()), OV::from_dv(x.to_dv()), OV::from_v8(x.to_v8())];
        h[5] = fold_bits(h[5], &c);
    }
    let want: [u64; 6] = [
        0x655b_a7a1_b76c_0210,
        0x9498_3801_6702_91da,
        0x8c28_dd00_f1e5_9716,
        0xb29b_ca8b_321a_996c,
        0xecd0_e4f5_cde6_4549,
        0xecbd_3e15_e6e7_2432,
    ];
    let names = ["add", "mul", "div", "sqrt", "accumulator", "conversions"];
    let mut bad = Vec::new();
    for i in 0..6 {
        if h[i] != want[i] {
            bad.push(format!("{}: {:#018x} pinned {:#018x}", names[i], h[i], want[i]));
        }
    }
    assert!(bad.is_empty(), "{bad:?}");
    let _ = QD::ZERO;
}
