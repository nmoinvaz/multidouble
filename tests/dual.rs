//! Forward-mode dual lanes: one generic function evaluated with value lanes, with a double-double tangent (`Du`), with
//! N f64 tangents (`Dtn<N>`) and in plain f64 (`Fu`), against derivatives written out by hand in scalar double-double.
#![allow(clippy::needless_range_loop)]
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::dual::{Dtn, Du, Fu, Lane};
use multidouble::dv::DV;
use multidouble::v8::V8;

/// f(x, y) = (x^3 + 2 x y) / (x + 3), written once over the `Lane` trait
fn f<T: Lane>(x: T, y: T) -> T {
    let two = T::cst(DV::splat_f(2.0));
    let three = T::cst(DV::splat_f(3.0));
    (x * x * x + two * x * y) / (x + three)
}

/// f and its partial derivatives in scalar double-double, by hand
fn f_dd(x: DD, y: DD) -> (DD, DD, DD) {
    let two = DD::from_f64(2.0);
    let three = DD::from_f64(3.0);
    let num = x * x * x + two * x * y;
    let den = x + three;
    let fx = ((DD::from_f64(3.0) * x * x + two * y) * den - num) / (den * den);
    let fy = (two * x) / den;
    (num / den, fx, fy)
}

fn inputs(r: &mut Rng) -> ([DD; 8], [DD; 8]) {
    // x away from -3, the pole
    let x = std::array::from_fn(|_| DD::new(1.0 + 4.0 * r.unit(), r.sym() * 1e-17));
    let y = std::array::from_fn(|_| DD::new(r.sym() * 5.0, r.sym() * 1e-17));
    (x, y)
}

fn dv(v: &[DD; 8]) -> DV {
    let hi: Vec<f64> = v.iter().map(|d| d.hi).collect();
    let lo: Vec<f64> = v.iter().map(|d| d.lo).collect();
    DV::load(&hi, &lo)
}

fn rel(a: DD, b: DD) -> f64 {
    ((a - b).to_f64() / b.to_f64()).abs()
}

#[test]
fn values_match_the_scalar_formula() {
    let mut r = Rng(21);
    for _ in 0..500 {
        let (x, y) = inputs(&mut r);
        let v = f(dv(&x), dv(&y));
        for j in 0..8 {
            assert!(rel(v.lane(j), f_dd(x[j], y[j]).0) < 1e-30);
        }
    }
}

#[test]
fn du_gives_exact_partial_derivatives() {
    let mut r = Rng(22);
    let mut worst: f64 = 0.0;
    for _ in 0..500 {
        let (x, y) = inputs(&mut r);
        let one = DV::splat_f(1.0);
        // d/dx: tangent 1 on x; d/dy: tangent 1 on y
        let gx = f(Du::from_vt(dv(&x), one), Du::from_vt(dv(&y), DV::zero()));
        let gy = f(Du::from_vt(dv(&x), DV::zero()), Du::from_vt(dv(&y), one));
        for j in 0..8 {
            let (val, fx, fy) = f_dd(x[j], y[j]);
            for (got, want) in [(gx.val().lane(j), val), (gx.tan().lane(j), fx), (gy.tan().lane(j), fy)] {
                let e = rel(got, want);
                worst = worst.max(e);
                assert!(e < 1e-29, "lane {j}: {got:?} vs {want:?}");
            }
        }
    }
    println!("Du: worst relative error {worst:.1e}");
}

#[test]
fn dtn_gives_both_partials_in_one_pass() {
    let mut r = Rng(23);
    for _ in 0..500 {
        let (x, y) = inputs(&mut r);
        let (one, zero) = (V8::splat(1.0), V8::zero());
        let xs = Dtn::<2> {
            v: dv(&x),
            d: [one, zero],
        };
        let ys = Dtn::<2> {
            v: dv(&y),
            d: [zero, one],
        };
        let g = f(xs, ys);
        let (dx, dy) = (g.d[0].to_array(), g.d[1].to_array());
        for j in 0..8 {
            let (val, fx, fy) = f_dd(x[j], y[j]);
            // value in double-double, tangents in f64
            assert!(rel(g.v.lane(j), val) < 1e-30);
            assert!(
                ((dx[j] - fx.to_f64()) / fx.to_f64()).abs() < 1e-13,
                "lane {j}: {} vs {:?}",
                dx[j],
                fx
            );
            assert!(
                ((dy[j] - fy.to_f64()) / fy.to_f64()).abs() < 1e-13,
                "lane {j}: {} vs {:?}",
                dy[j],
                fy
            );
        }
    }
}

#[test]
fn fu_is_plain_f64_forward_mode() {
    let mut r = Rng(24);
    for _ in 0..500 {
        let (x, y) = inputs(&mut r);
        let hx = V8::from_array(std::array::from_fn(|j| x[j].hi));
        let hy = V8::from_array(std::array::from_fn(|j| y[j].hi));
        let g = f(
            Fu {
                v: hx,
                d: V8::splat(1.0),
            },
            Fu { v: hy, d: V8::zero() },
        );
        let (v, d) = (g.v.to_array(), g.d.to_array());
        for j in 0..8 {
            let (xh, yh) = (x[j].hi, y[j].hi);
            let (val, fx, _) = f_dd(DD::from_f64(xh), DD::from_f64(yh));
            // f64 errors relative to the size of the terms (the numerator can cancel)
            let scale = (xh.powi(3).abs() + (2.0 * xh * yh).abs()) / (xh + 3.0);
            let dscale = (3.0 * xh * xh + (2.0 * yh).abs()) / (xh + 3.0) + scale / (xh + 3.0);
            assert!(
                (v[j] - val.to_f64()).abs() < 1e-14 * scale,
                "lane {j}: {} vs {:?}",
                v[j],
                val
            );
            assert!(
                (d[j] - fx.to_f64()).abs() < 1e-14 * dscale,
                "lane {j}: {} vs {:?}",
                d[j],
                fx
            );
        }
    }
}

/// Control: a wrong hand derivative (the quotient rule's sign flipped) is caught by the same comparison.
#[test]
fn control_wrong_derivative_is_caught() {
    let mut r = Rng(25);
    let (x, y) = inputs(&mut r);
    let one = DV::splat_f(1.0);
    let gx = f(Du::from_vt(dv(&x), one), Du::from_vt(dv(&y), DV::zero()));
    let caught = (0..8).any(|j| {
        let (val, fx, _) = f_dd(x[j], y[j]);
        let wrong = fx + DD::from_f64(2.0) * val / (x[j] + DD::from_f64(3.0));
        rel(gx.tan().lane(j), wrong) > 1e-29
    });
    assert!(caught);
}
