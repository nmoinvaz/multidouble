//! The jets' order-k operations (`Lane::acc_at`, `fin_at`, `mul_at`, `div_at`, `mulp_at`, `copy_at`, and the field's
//! `cs_at`, `cs_range_at`, `cs_w_at`, `mul_at`, `mul_t_at`, `div_at`, `mulp_at`, `copy_at`): each order formed alone,
//! from the lower orders kept, is the full jet operation's coefficient, bit for bit, on `Jet<N>`, `QJet<N>` and
//! `OJet<N>`. A Taylor recursion in x whose coefficients are jets, formed one jet order at a time with every
//! intermediate that enters a product kept, is the recursion in full jet arithmetic, bit for bit.
//!
//! Controls: a quotient's order k from lower coefficients that are not the quotient's, and the recursion with the
//! kept series cleared before each order, differ from the full operations.
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::dual::{Counted, Lane, Param};
use multidouble::field::{cs, cs_at, cs_range, cs_range_at, cs_w, cs_w_at, Fl};
use multidouble::native::{Jet, OJet, QJet, OV};
use multidouble::od::OD;
use multidouble::simd::Native;

/// lane vectors per field
const B: usize = 2;
/// orders of the recursion in x
const M: usize = 8;

/// h (1 + O(2^-53)) with all eight parts in use
fn od_of(r: &mut Rng, h: f64) -> OD {
    let mut x = [0.0; 8];
    x[0] = h;
    for i in 1..8 {
        x[i] = x[i - 1] * 2f64.powi(-53) * r.sym();
    }
    OD::new(x)
}

/// a jet whose coefficients are in [-1, 1), with coefficient 0 in [1, 2) for a divisor, rounded to the lane's precision
fn lane<T: Lane<S = Native>>(r: &mut Rng, divisor: bool) -> T {
    let mut x = T::zero();
    for k in 0..T::NJ {
        let v = OV::from_lanes(&std::array::from_fn(|_| {
            let h = if k == 0 && divisor { 1.0 + r.unit() } else { r.sym() };
            od_of(r, h)
        }));
        x.set_coef_od(k, v);
    }
    x
}

fn field<T: Lane<S = Native>>(r: &mut Rng, divisor: bool) -> Fl<T, B> {
    Fl(std::array::from_fn(|_| lane::<T>(r, divisor)))
}

/// a parameter series with every coefficient in use: (c1 + h)(c2 + h) / (c3 + h)
fn param<T: Lane<S = Native>>(r: &mut Rng) -> T::P {
    let mut c = || DD::from_f64(1.0 + r.unit());
    let (c1, c2, c3) = (c(), c(), c());
    T::P::var(c1) * T::P::var(c2) / T::P::var(c3)
}

/// the bits of coefficient k, all eight parts of every lane (exact on every jet: `coef_od`)
fn bits<T: Lane<S = Native>>(x: &T, k: usize) -> Vec<u64> {
    x.coef_od(k)
        .lanes()
        .iter()
        .flat_map(|d| d.x.map(f64::to_bits))
        .collect()
}

fn fbits<T: Lane<S = Native>>(x: &Fl<T, B>, k: usize) -> Vec<u64> {
    x.0.iter().flat_map(|l| bits(l, k)).collect()
}

/// whether out holds want's coefficient k and bg's others, bit for bit
fn set_at<T: Lane<S = Native>>(out: &T, want: &T, bg: &T, k: usize) -> bool {
    (0..T::NJ).all(|i| bits(out, i) == bits(if i == k { want } else { bg }, i))
}

/// (mismatches, control differences) of the lane operations at every order
fn lane_ops<T: Lane<S = Native>>(r: &mut Rng) -> (usize, usize) {
    let (x, y, d, e) = (
        lane::<T>(r, false),
        lane::<T>(r, false),
        lane::<T>(r, true),
        lane::<T>(r, false),
    );
    let p = param::<T>(r);
    let (xy, xd, xp) = (x * y, x / d, x.mulp(p));
    let sum = T::fin(T::acc(T::acc(T::acc0(), x, y), e, d));
    // the outputs start from bg, whose coefficients other than k must stay as they are
    let bg = lane::<T>(r, false);
    let (mut bad, mut control) = (0, 0);
    let mut q = T::zero();
    for k in 0..T::NJ {
        let mut m = bg;
        T::mul_at(&x, &y, k, &mut m);
        bad += !set_at(&m, &xy, &bg, k) as usize;
        let mut mp = bg;
        T::mulp_at(&x, &p, k, &mut mp);
        bad += !set_at(&mp, &xp, &bg, k) as usize;
        T::div_at(&x, &d, k, &mut q);
        bad += (bits(&q, k) != bits(&xd, k)) as usize;
        let mut a = T::acc0();
        T::acc_at(&mut a, &x, &y, k);
        T::acc_at(&mut a, &e, &d, k);
        let mut f = bg;
        T::fin_at(&a, k, &mut f);
        bad += !set_at(&f, &sum, &bg, k) as usize;
        let mut c = bg;
        T::copy_at(&x, k, &mut c);
        bad += !set_at(&c, &x, &bg, k) as usize;
        // the control: the quotient's order k from zero lower coefficients
        let mut z = T::zero();
        T::div_at(&x, &d, k, &mut z);
        control += (bits(&z, k) != bits(&xd, k)) as usize;
    }
    (bad, control)
}

/// mismatches of the field's Cauchy sums at every order, every j < J
fn field_sums<T: Lane<S = Native>>(r: &mut Rng) -> usize {
    const J: usize = 6;
    let xs: Vec<Fl<T, B>> = (0..J).map(|_| field::<T>(r, false)).collect();
    let ys: Vec<Fl<T, B>> = (0..J).map(|_| field::<T>(r, false)).collect();
    let w = |i: usize| (i + 1) as f64;
    let bg = field::<T>(r, false);
    let mut bad = 0;
    for j in 0..J {
        let full = [
            cs(&xs, &ys, j),
            cs_range(&xs, &ys, j, j / 2, j),
            cs_w(&xs, &ys, j, 0, j, w),
        ];
        for k in 0..T::NJ {
            let mut o = [bg; 3];
            cs_at(&mut o[0], &xs, &ys, j, k);
            cs_range_at(&mut o[1], &xs, &ys, j, j / 2, j, k);
            cs_w_at(&mut o[2], &xs, &ys, j, 0, j, w, k);
            let kept = |f: &Fl<T, B>| (0..T::NJ).all(|i| i == k || fbits(f, i) == fbits(&bg, i));
            bad += (0..3)
                .filter(|&i| fbits(&o[i], k) != fbits(&full[i], k) || !kept(&o[i]))
                .count();
        }
    }
    bad
}

/// The recursion y_(m+1) = ((y y)_m p + y_m s) / (w0 (m + 1)) in x, from y_0, with the jet p a parameter series, s a
/// jet and w0 a divisor field, in full jet arithmetic
fn recursion_full<T: Lane<S = Native>>(y0: &Fl<T, B>, p: T::P, s: T, w0: &Fl<T, B>) -> Vec<Fl<T, B>> {
    let iw = Fl::<T, B>::splat(DD::ONE) / *w0;
    let mut y = vec![*y0];
    for m in 0..M {
        let v = cs(&y, &y, m).mulp(p) + y[m].mul_t(s);
        y.push((v * iw).mulf(1.0 / (m + 1) as f64));
    }
    y
}

/// The same recursion one jet order at a time: the series that enter a product (y, (y y)_m, its product with p, the
/// sum v, the reciprocal of w0) kept from order to order. `keep` false clears them before each order (the control).
fn recursion_orders<T: Lane<S = Native>>(y0: &Fl<T, B>, p: T::P, s: T, w0: &Fl<T, B>, keep: bool) -> Vec<Fl<T, B>> {
    let z = Fl::<T, B>::zero();
    let one = Fl::<T, B>::splat(DD::ONE);
    let (mut y, mut yy, mut u, mut ys, mut v, mut w) = (
        vec![z; M + 1],
        vec![z; M],
        vec![z; M],
        vec![z; M],
        vec![z; M],
        vec![z; M],
    );
    let mut iw = z;
    for k in 0..T::NJ {
        if !keep {
            for a in [&mut y, &mut yy, &mut u, &mut ys, &mut v, &mut w] {
                a.iter_mut().for_each(|f| *f = z);
            }
            iw = z;
        }
        one.div_at(w0, k, &mut iw);
        y[0].copy_at(y0, k);
        for m in 0..M {
            let mut t = z;
            cs_at(&mut t, &y, &y, m, k);
            yy[m].copy_at(&t, k);
            yy[m].mulp_at(&p, k, &mut u[m]);
            y[m].mul_t_at(&s, k, &mut ys[m]);
            v[m].copy_at(&(u[m] + ys[m]), k);
            v[m].mul_at(&iw, k, &mut w[m]);
            let next = w[m].mulf(1.0 / (m + 1) as f64);
            y[m + 1].copy_at(&next, k);
        }
    }
    y
}

/// (mismatches, control differences) of the recursion over every x-order and jet order
fn recursion<T: Lane<S = Native>>(r: &mut Rng) -> (usize, usize) {
    let (y0, w0) = (field::<T>(r, false), field::<T>(r, true));
    let (p, s) = (param::<T>(r), lane::<T>(r, false));
    let full = recursion_full(&y0, p, s, &w0);
    let count = |y: &[Fl<T, B>]| -> usize {
        (0..=M)
            .map(|m| (0..T::NJ).filter(|&k| fbits(&y[m], k) != fbits(&full[m], k)).count())
            .sum()
    };
    (
        count(&recursion_orders(&y0, p, s, &w0, true)),
        count(&recursion_orders(&y0, p, s, &w0, false)),
    )
}

/// Pass, written before the first run: on `Jet<12>`, `QJet<12>`, `OJet<12>` and the counting lane over `OJet<12>`,
/// every order-k lane operation is the full operation's coefficient k bit for bit and leaves the output's other
/// coefficients as they were (0 mismatches), every order-k Cauchy sum is `cs`'s, `cs_range`'s and `cs_w`'s
/// coefficient k for j < 6 and keeps the others, and the recursion formed one order at a time is the full recursion at
/// every x-order and jet order. Controls: the quotient from zero lower coefficients differs at every order k >= 1 (11
/// of 12), and the recursion with its kept series cleared differs.
#[test]
fn orders_one_at_a_time_match_the_jets() {
    fn run<T: Lane<S = Native>>(name: &str, seed: u64) {
        let mut r = Rng(seed);
        let (bad, ctl) = lane_ops::<T>(&mut r);
        let sums = field_sums::<T>(&mut r);
        let (rec, rec_ctl) = recursion::<T>(&mut r);
        println!(
            "{name}: lane operations {bad} mismatches (control {ctl} of {}), Cauchy sums {sums}, recursion {rec} \
             (control {rec_ctl} of {})",
            T::NJ,
            (M + 1) * T::NJ
        );
        assert_eq!(
            (bad, sums, rec),
            (0, 0, 0),
            "{name}: an order-k operation is not the jet's coefficient"
        );
        assert_eq!(
            ctl,
            T::NJ - 1,
            "{name}: the quotient control did not fire at every order k >= 1"
        );
        assert!(rec_ctl > 0, "{name}: the recursion control did not fire");
    }
    run::<Jet<12>>("Jet<12>", 1);
    run::<QJet<12>>("QJet<12>", 2);
    run::<OJet<12>>("OJet<12>", 3);
    run::<Counted<OJet<12>>>("Counted<OJet<12>>", 4);
}
