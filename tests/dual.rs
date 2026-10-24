//! Forward-mode dual lanes: one generic function evaluated with value lanes, with a double-double tangent (`Du`), with
//! N f64 tangents (`Dtn<N>`) and in plain f64 (`Fu`), against derivatives written out by hand in scalar double-double.
//! A second function goes through every method of `Lane` on all six lane types, and `mul_pwr2` is checked bit for bit.
#![allow(clippy::needless_range_loop)]
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::dual::{Dtn, Du, Fu, Fun, Lane, F8};
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

/// g(x, y) = ((c x - s y)(x/2) + x y + c x - (y + c)) / (x_0 + 3), written once over `Lane` through every one of its
/// methods: the product sum by the accumulator, and x_0, lane 0's x, by `bcast`
fn g<T: Lane>(x: T, y: T, c: DV, s: DD) -> T {
    let a = x.mulc(c) - y.muls(s);
    let p = T::fin(T::acc1(T::accc(T::acc(T::acc0(), x, y), x, c), -y.addc(c)));
    T::zero() + (a * x.mulf(0.5) + p) / (x.bcast(0) + T::splat(DD::from_f64(3.0)))
}

type Reference = fn(DD, DD, DD, DD, DD) -> (DD, DD, DD);

/// g and its partials in scalar double-double, by hand, at one lane. The tangent seeds every lane, so x_0 moves with x.
fn g_dd(x: DD, y: DD, c: DD, s: DD, x0: DD) -> (DD, DD, DD) {
    let half = DD::from_f64(0.5);
    let den = x0 + DD::from_f64(3.0);
    let q = (c * x - s * y) * (x * half) + x * y + c * x - (y + c);
    let qx = c * x - s * y * half + y + c;
    let qy = x - s * x * half - DD::ONE;
    (q / den, (qx * den - q) / (den * den), qy / den)
}

/// worst relative errors of g on lane type T against `reference`: value, d/dx, d/dy. The inputs keep every term of
/// g, its partials and their numerators positive, so the errors are relative to well-conditioned values.
fn errors<T: Lane>(reference: Reference) -> [f64; 3] {
    let mut r = Rng(26);
    let s = DD::ONE / DD::from_f64(3.0);
    let (one, zero) = (DV::splat_f(1.0), DV::zero());
    let mut worst = [0.0f64; 3];
    for _ in 0..200 {
        let x: [DD; 8] = std::array::from_fn(|_| DD::new(2.0 + r.unit(), r.sym() * 1e-16));
        let y: [DD; 8] = std::array::from_fn(|_| DD::new(1.0 + r.unit(), r.sym() * 1e-16));
        let c: [DD; 8] = std::array::from_fn(|_| DD::new(1.0 + r.unit(), r.sym() * 1e-16));
        let gx = g(T::from_vt(dv(&x), one), T::from_vt(dv(&y), zero), dv(&c), s);
        // d/dy through the last f64 tangent where the lane has them, through `from_vt` otherwise
        let k = T::NT.saturating_sub(1);
        let mut ys = T::from_vt(dv(&y), if T::TAN_F64 { zero } else { one });
        if T::TAN_F64 {
            ys.set_tan64(k, V8::splat(1.0));
        }
        let gy = g(T::from_vt(dv(&x), zero), ys, dv(&c), s);
        let gy_tan = if T::TAN_F64 {
            DV {
                hi: gy.tan64(k),
                lo: V8::zero(),
            }
        } else {
            gy.tan()
        };
        for j in 0..8 {
            // f64-valued lanes see the hi parts of the inputs and constants
            let h = |d: DD| if T::VAL_F64 { DD::from_f64(d.hi) } else { d };
            let (val, fx, fy) = reference(h(x[j]), h(y[j]), h(c[j]), h(s), h(x[0]));
            worst[0] = worst[0].max(rel(gx.val().lane(j), val));
            if T::TANGENT {
                worst[1] = worst[1].max(rel(gx.tan().lane(j), fx));
                worst[2] = worst[2].max(rel(gy_tan.lane(j), fy));
            }
        }
    }
    worst
}

/// double-double accuracy for double-double parts, f64 accuracy for f64 parts
fn within<T: Lane>(e: [f64; 3]) -> bool {
    let tv = if T::VAL_F64 { 1e-13 } else { 1e-29 };
    let tt = if T::TAN_F64 { 1e-13 } else { 1e-29 };
    e[0] < tv && e[1] < tt && e[2] < tt
}

#[test]
fn every_lane_method_on_every_lane_type() {
    fn run<T: Lane>(name: &str) {
        let e = errors::<T>(g_dd);
        println!(
            "{name}: worst relative errors {:.1e} value, {:.1e} d/dx, {:.1e} d/dy",
            e[0], e[1], e[2]
        );
        assert!(within::<T>(e), "{name}: {e:?}");
    }
    run::<DV>("DV");
    run::<F8>("F8");
    run::<Du>("Du");
    run::<Fu>("Fu");
    run::<Dtn<2>>("Dtn<2>");
    run::<Fun<2>>("Fun<2>");
}

/// Controls: hand references that get `bcast` wrong are caught. A value with each lane's own x in place of lane 0's,
/// on the value lanes, and a d/dx that misses the tangent `bcast` carries from lane 0, on every tangent lane type.
#[test]
fn controls_on_bcast_are_caught() {
    fn own_x(x: DD, y: DD, c: DD, s: DD, _x0: DD) -> (DD, DD, DD) {
        g_dd(x, y, c, s, x)
    }
    assert!(!within::<DV>(errors::<DV>(own_x)));
    assert!(!within::<F8>(errors::<F8>(own_x)));
    fn no_bcast_tangent(x: DD, y: DD, c: DD, s: DD, x0: DD) -> (DD, DD, DD) {
        let (val, _, fy) = g_dd(x, y, c, s, x0);
        let qx = c * x - s * y * DD::from_f64(0.5) + y + c;
        (val, qx / (x0 + DD::from_f64(3.0)), fy)
    }
    assert!(!within::<Du>(errors::<Du>(no_bcast_tangent)));
    assert!(!within::<Fu>(errors::<Fu>(no_bcast_tangent)));
    assert!(!within::<Dtn<2>>(errors::<Dtn<2>>(no_bcast_tangent)));
    assert!(!within::<Fun<2>>(errors::<Fun<2>>(no_bcast_tangent)));
}

/// every part of a lane, value and tangents, as bits
fn parts<T: Lane>(x: T) -> Vec<u64> {
    let mut out = Vec::new();
    let mut push = |v: V8| {
        let mut a = [0.0; 8];
        v.store(&mut a);
        out.extend(a.iter().map(|f| f.to_bits()));
    };
    let v = x.val();
    push(v.hi);
    push(v.lo);
    if T::TAN_F64 {
        for k in 0..T::NT {
            push(x.tan64(k));
        }
    } else if T::TANGENT {
        let t = x.tan();
        push(t.hi);
        push(t.lo);
    }
    out
}

/// a lane with random normalized parts of either sign: value, and every tangent
fn random_lane<T: Lane>(r: &mut Rng) -> T {
    let v: [DD; 8] = std::array::from_fn(|_| r.dd(8));
    let t: [DD; 8] = std::array::from_fn(|_| r.dd(8));
    let mut x = T::from_vt(dv(&v), dv(&t));
    if T::TAN_F64 {
        for k in 0..T::NT {
            let a: [f64; 8] = std::array::from_fn(|_| r.dd(8).hi);
            x.set_tan64(k, V8::load(&a));
        }
    }
    x
}

/// `scale` (the method under test, or a wrong one in the controls) against `mulf`, bit for bit, at random powers of
/// two 2^-200..2^200 (every part stays normal), and the round trip: scaling by 2^k and then by 2^-k gives every part
/// back bit for bit
fn scales_exactly<T: Lane>(scale: impl Fn(T, f64) -> T) -> bool {
    let mut r = Rng(53);
    for _ in 0..2000 {
        let x = random_lane::<T>(&mut r);
        let s = 2f64.powi((r.next_u64() % 401) as i32 - 200);
        let y = scale(x, s);
        if parts(y) != parts(x.mulf(s)) || parts(scale(y, 1.0 / s)) != parts(x) {
            return false;
        }
    }
    true
}

#[test]
fn mul_pwr2_is_exact_on_every_lane_type() {
    assert!(scales_exactly::<DV>(|x, s| x.mul_pwr2(s)), "DV");
    assert!(scales_exactly::<F8>(|x, s| x.mul_pwr2(s)), "F8");
    assert!(scales_exactly::<Du>(|x, s| x.mul_pwr2(s)), "Du");
    assert!(scales_exactly::<Fu>(|x, s| x.mul_pwr2(s)), "Fu");
    assert!(scales_exactly::<Dtn<2>>(|x, s| x.mul_pwr2(s)), "Dtn<2>");
    assert!(scales_exactly::<Fun<2>>(|x, s| x.mul_pwr2(s)), "Fun<2>");
    // the scalar double-double, through lane 0 of DV
    let mut r = Rng(54);
    for _ in 0..2000 {
        let x = r.dd(30);
        let s = 2f64.powi((r.next_u64() % 401) as i32 - 200);
        let y = x.mul_pwr2(s);
        assert_eq!((y.hi.to_bits(), y.lo.to_bits()), {
            let m = x.mul_f(s);
            (m.hi.to_bits(), m.lo.to_bits())
        });
        assert_eq!(y.mul_pwr2(1.0 / s), x);
    }
}

/// Controls: wrong scalings are caught. One power of two too many, on every lane type; the low part left unscaled, on
/// the double-double value lanes; the (first) tangent left unscaled, on every tangent lane type.
#[test]
fn controls_on_mul_pwr2_are_caught() {
    fn wrong_power<T: Lane>(x: T, s: f64) -> T {
        x.mul_pwr2(2.0 * s)
    }
    assert!(!scales_exactly::<DV>(wrong_power));
    assert!(!scales_exactly::<F8>(wrong_power));
    assert!(!scales_exactly::<Du>(wrong_power));
    assert!(!scales_exactly::<Fu>(wrong_power));
    assert!(!scales_exactly::<Dtn<2>>(wrong_power));
    assert!(!scales_exactly::<Fun<2>>(wrong_power));
    fn lo_unscaled<T: Lane>(x: T, s: f64) -> T {
        let y = x.mul_pwr2(s);
        let v = DV {
            hi: y.val().hi,
            lo: x.val().lo,
        };
        let mut z = T::from_vt(v, y.tan());
        if T::TAN_F64 {
            for k in 0..T::NT {
                z.set_tan64(k, y.tan64(k));
            }
        }
        z
    }
    assert!(!scales_exactly::<DV>(lo_unscaled));
    assert!(!scales_exactly::<Du>(lo_unscaled));
    assert!(!scales_exactly::<Dtn<2>>(lo_unscaled));
    fn tangent_unscaled<T: Lane>(x: T, s: f64) -> T {
        let mut y = x.mul_pwr2(s);
        if T::TAN_F64 {
            y.set_tan64(0, x.tan64(0));
        } else {
            y = T::from_vt(y.val(), x.tan());
        }
        y
    }
    assert!(!scales_exactly::<Du>(tangent_unscaled));
    assert!(!scales_exactly::<Fu>(tangent_unscaled));
    assert!(!scales_exactly::<Dtn<2>>(tangent_unscaled));
    assert!(!scales_exactly::<Fun<2>>(tangent_unscaled));
}

/// the scales `mul_pwr2` accepts: normal powers of two of either sign, nothing else
#[test]
fn is_pwr2_accepts_normal_powers_of_two_only() {
    use multidouble::dd::is_pwr2;
    for k in -1022..=1023 {
        assert!(is_pwr2(2f64.powi(k)) && is_pwr2(-(2f64.powi(k))), "2^{k}");
    }
    for b in [
        0.0,
        -0.0,
        3.0,
        0.75,
        1.0 + f64::EPSILON,
        f64::MIN_POSITIVE / 2.0,
        f64::INFINITY,
        f64::NAN,
    ] {
        assert!(!is_pwr2(b), "{b:e}");
    }
}

/// in debug builds, a scale that is not a power of two is refused (release builds do not check)
#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "not a power of two")]
fn mul_pwr2_refuses_other_scales_in_debug() {
    let _ = Du::from_vt(DV::splat_f(1.0), DV::splat_f(1.0)).mul_pwr2(3.0);
}
