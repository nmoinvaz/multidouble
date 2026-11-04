//! Slope errors near cancellation: the order-1 coefficient (the derivative) and order 2 of a jet, where the
//! computation cancels (a^2 - 1 and a - a^3 at a = 1 + delta), alone, times a large factor and as a divisor,
//! against exact arithmetic (`exact::Dy`). Each error is bounded by C eps kappa_k: eps the type's rounding unit,
//! kappa_k the conditioning of coefficient k (the rounding of the cancelling term times its weight in coefficient k,
//! over |coefficient k|), so the double-double jet's bound is eps_dd kappa and the quad-double jet's eps_qd kappa.
//! The bounds are also shown to be tight (the worst error is within a factor of the bound wherever kappa is large),
//! and the quad-double jet removes the double-double jet's error on the same inputs, by about 32 digits.
//! Controls: the double-double jet on the quad-double bound, and a relative error of 2^-90 put into the cancelling
//! term of the double-double jet, are each caught.
#![allow(clippy::needless_range_loop)]
mod common;
use common::{Rng, U2};
use multidouble::dd::DD;
use multidouble::dual::Lane;
use multidouble::dv::DV;
use multidouble::exact::Dy;
use multidouble::native::{Jet, QJet};
use multidouble::qd::QD;

/// the double-double unit, 2^-106
const EPS_DD: f64 = U2;
/// the quad-double unit, 2^-209
const EPS_QD: f64 = QD::EPS;

fn one<T: Lane>() -> T {
    T::splat(DD::ONE)
}
/// a^2 - 1
fn sq_m1<T: Lane>(x: T) -> T {
    x * x - one()
}
/// a - a^3
fn lin_m_cube<T: Lane>(x: T) -> T {
    x - x * x * x
}

/// The cases: the function on a jet, its coefficients k = 0, 1, 2 exactly as N_k / D_k, and kappa_k.
struct Case {
    name: &'static str,
    dd: fn(Jet<3>) -> Jet<3>,
    qd: fn(QJet<3>) -> QJet<3>,
    exact: fn(&Dy, usize) -> (Dy, Dy),
    kappa: fn(f64, f64, usize) -> f64,
    /// a product with the large factor 1/(a - 1), whose slope the double-double jet loses
    product: bool,
}

fn n(x: f64) -> Dy {
    Dy::from_f64(x)
}
fn pw(x: &Dy, k: usize) -> Dy {
    (0..k).fold(n(1.0), |p, _| p.mul(x))
}
/// the coefficients of x(x + 1) at a: a^2 + a, 2a + 1, 1
fn x_x1(a: &Dy, k: usize) -> Dy {
    [a.mul(a).add(a), n(2.0).mul(a).add(&n(1.0)), n(1.0)][k].clone()
}
/// coefficient k of 1/(x - 1) at a = 1 + d: (-1)^k / d^(k+1)
fn pole(d: f64, k: usize) -> f64 {
    (if k % 2 == 1 { -1.0 } else { 1.0 }) / d.powi(k as i32 + 1)
}
/// kappa_k of the product u L of a cancelling factor u, whose value carries the rounding of m (a^2 or a^3), and the
/// large factor L: (m |L_k| + sum_i |u_i| |L_(k-i)|) / |g_k|
fn kappa_product(m: f64, u: [f64; 3], l: [f64; 3], g: [f64; 3], k: usize) -> f64 {
    let s: f64 = (0..=k).map(|i| u[i].abs() * l[k - i].abs()).sum();
    (m * l[k].abs() + s) / g[k].abs()
}

const CASES: [Case; 6] = [
    Case {
        name: "a^2 - 1",
        dd: sq_m1,
        qd: sq_m1,
        exact: |a, k| {
            let c = [a.mul(a).sub(&n(1.0)), n(2.0).mul(a), n(1.0)];
            (c[k].clone(), n(1.0))
        },
        // the value carries the rounding of a^2; the slope 2a and the order 2 are exact sums
        kappa: |a, d, k| if k == 0 { a * a / (d * (a + 1.0)) } else { 1.0 },
        product: false,
    },
    Case {
        name: "a - a^3",
        dd: lin_m_cube,
        qd: lin_m_cube,
        exact: |a, k| {
            let a3 = a.mul(a).mul(a);
            let c = [a.sub(&a3), n(1.0).sub(&n(3.0).mul(&a.mul(a))), n(-3.0).mul(a)];
            (c[k].clone(), n(1.0))
        },
        kappa: |a, d, k| match k {
            0 => a * a / (d * (a + 1.0)),
            1 => 3.0 * a * a / (3.0 * a * a - 1.0),
            _ => 1.0,
        },
        product: false,
    },
    Case {
        name: "(a^2 - 1) a / (a - 1)",
        dd: |x| sq_m1(x) * (x / (x - one())),
        qd: |x| sq_m1(x) * (x / (x - one())),
        exact: |a, k| (x_x1(a, k), n(1.0)),
        kappa: |a, d, k| {
            let l = [a / d, pole(d, 1), pole(d, 2)];
            kappa_product(
                a * a,
                [d * (a + 1.0), 2.0 * a, 1.0],
                l,
                [a * a + a, 2.0 * a + 1.0, 1.0],
                k,
            )
        },
        product: true,
    },
    Case {
        name: "(a - a^3) / (a - 1)",
        dd: |x| lin_m_cube(x) * (one::<Jet<3>>() / (x - one())),
        qd: |x| lin_m_cube(x) * (one::<QJet<3>>() / (x - one())),
        exact: |a, k| (x_x1(a, k).neg(), n(1.0)),
        kappa: |a, d, k| {
            let l = [pole(d, 0), pole(d, 1), pole(d, 2)];
            let u = [a * d * (a + 1.0), 3.0 * a * a - 1.0, 3.0 * a];
            kappa_product(a * a * a, u, l, [a * a + a, 2.0 * a + 1.0, 1.0], k)
        },
        product: true,
    },
    Case {
        name: "(a + 1) / (a^2 - 1)",
        dd: |x| (x + one()) / sq_m1(x),
        qd: |x| (x + one()) / sq_m1(x),
        // 1/(x - 1): (-1)^k / d^(k+1)
        exact: |a, k| {
            let d = a.sub(&n(1.0));
            (n(if k % 2 == 1 { -1.0 } else { 1.0 }), pw(&d, k + 1))
        },
        // q_k goes as u_0^-(k+1): the relative error of u_0, a^2 eps / |a^2 - 1|, k + 1 times, and the recurrence's
        kappa: |a, d, k| (k as f64 + 1.0) * (a * a / (d * (a + 1.0)) + 1.0),
        product: false,
    },
    Case {
        name: "a / (a - a^3)",
        dd: |x| x / lin_m_cube(x),
        qd: |x| x / lin_m_cube(x),
        // 1/(1 - x^2) = (1/2)(1/(1 - x) + 1/(1 + x)): (-1)^k (d^(k+1) - (1 + a)^(k+1)) / (2 d^(k+1) (1 + a)^(k+1))
        exact: |a, k| {
            let d = a.sub(&n(1.0));
            let (dk, ak) = (pw(&d, k + 1), pw(&a.add(&n(1.0)), k + 1));
            let den = n(2.0).mul(&dk).mul(&ak);
            (dk.sub(&ak), if k % 2 == 1 { den.neg() } else { den })
        },
        kappa: |a, d, k| (k as f64 + 1.0) * (a * a / (d * (a + 1.0)) + 1.0),
        product: false,
    },
];

/// |c D - N| / |N|: the relative error of c against N / D, exactly
fn rel(c: &Dy, nd: &(Dy, Dy)) -> f64 {
    c.mul(&nd.1).sub(&nd.0).abs().ratio(&nd.0)
}

/// a = 1 + delta t, t in [1, 2), as a double-double with both parts in use (so a^2 is not exact in double-double)
fn a_dd(r: &mut Rng, delta: f64) -> DD {
    let t = delta * (1.0 + r.unit());
    DD::ONE + DD::new(t, t * r.sym() * 2f64.powi(-53))
}

/// a = 1 + delta t as a quad-double with all four parts in use (so a^2 is not exact in quad-double)
fn a_qd(r: &mut Rng, delta: f64) -> QD {
    let t = delta * (1.0 + r.unit());
    let s = [r.sym(), r.sym(), r.sym()];
    QD::ONE
        .add_dd(DD::new(t, t * s[0] * 2f64.powi(-53)))
        .add_dd(DD::new(t * s[1] * 2f64.powi(-106), t * s[2] * 2f64.powi(-159)))
}

/// a's value and its distance from 1 in f64, for kappa
fn a_d(a: &Dy) -> (f64, f64) {
    (a.to_f64(), a.sub(&n(1.0)).to_f64())
}

/// the bound's constant: every error is at most C eps kappa_k (the worst seen is 4.4 for double-double, 0.82 for
/// quad-double)
const C: f64 = 8.0;
/// where kappa_k is at least this, the worst error is at least eps kappa_k / C: the bound is tight to a factor C^2
const AMPLIFIED: f64 = 1e3;

/// over the inputs, the worst error of each coefficient k = 0, 1, 2, and the worst of error / (eps kappa_k)
#[derive(Default, Clone, Copy, Debug)]
struct Worst {
    err: [f64; 3],
    ratio: [f64; 3],
    kappa: [f64; 3],
}

const ROUNDS: usize = 50;
const DELTAS: [f64; 2] = [1e-6, 1e-12];

fn record(w: &mut Worst, k: usize, e: f64, eps: f64, kappa: f64) {
    w.err[k] = w.err[k].max(e);
    w.ratio[k] = w.ratio[k].max(e / (eps * kappa));
    w.kappa[k] = w.kappa[k].max(kappa);
}

/// a = 1 + delta t on the 8 lanes, from the seed: double-double, or quad-double with all four parts in use
fn inputs_dd(seed: u64, round: usize, delta: f64) -> [DD; 8] {
    let mut r = Rng(seed + 1000 * round as u64);
    std::array::from_fn(|_| a_dd(&mut r, delta))
}
fn inputs_qd(seed: u64, round: usize, delta: f64) -> [QD; 8] {
    let mut r = Rng(seed + 1000 * round as u64);
    std::array::from_fn(|_| a_qd(&mut r, delta))
}

/// the double-double jet's errors on double-double inputs, the function f (the case's, or a wrong one in a control)
/// against the case's exact coefficients
fn dd_worst(c: &Case, f: fn(Jet<3>) -> Jet<3>, delta: f64, seed: u64, eps: f64) -> Worst {
    let mut w = Worst::default();
    for round in 0..ROUNDS {
        let a = inputs_dd(seed, round, delta);
        let g = f(Jet::<3>::var_lanes(&a));
        for j in 0..8 {
            let ae = Dy::sum(&[a[j].hi, a[j].lo]);
            let (af, d) = a_d(&ae);
            for k in 0..3 {
                let cj = g.c[k].lane(j);
                let e = rel(&Dy::sum(&[cj.hi, cj.lo]), &(c.exact)(&ae, k));
                record(&mut w, k, e, eps, (c.kappa)(af, d, k));
            }
        }
    }
    w
}

/// the quad-double jet's errors, on quad-double inputs with all four parts in use (full) or on the double-double
/// inputs of `dd_worst` with the same seed
fn qd_worst(c: &Case, delta: f64, seed: u64, full: bool) -> Worst {
    let mut w = Worst::default();
    for round in 0..ROUNDS {
        let a: [QD; 8] = if full {
            inputs_qd(seed, round, delta)
        } else {
            inputs_dd(seed, round, delta).map(QD::from_dd)
        };
        let g = (c.qd)(QJet::<3>::var_lanes(&a));
        for j in 0..8 {
            let ae = a[j].exact();
            let (af, d) = a_d(&ae);
            for k in 0..3 {
                let e = rel(&g.c[k].lane(j).exact(), &(c.exact)(&ae, k));
                record(&mut w, k, e, EPS_QD, (c.kappa)(af, d, k));
            }
        }
    }
    w
}

fn seed(ci: usize, di: usize) -> u64 {
    100 + 10 * ci as u64 + di as u64
}

/// every error within C eps kappa_k, and within a factor C of eps kappa_k where kappa_k >= AMPLIFIED
fn check(name: &str, delta: f64, w: &Worst) {
    println!(
        "{name:22} delta {delta:.0e}: errors {:.1e} {:.1e} {:.1e}, error / (eps kappa) {:.2} {:.2} {:.2}, kappa {:.1e} \
         {:.1e} {:.1e}",
        w.err[0], w.err[1], w.err[2], w.ratio[0], w.ratio[1], w.ratio[2], w.kappa[0], w.kappa[1], w.kappa[2]
    );
    for k in 0..3 {
        assert!(
            w.ratio[k] <= C,
            "{name}, delta {delta:e}, order {k}: error {:e} is {} eps kappa",
            w.err[k],
            w.ratio[k]
        );
        if w.kappa[k] >= AMPLIFIED {
            assert!(
                w.ratio[k] >= 1.0 / C,
                "{name}, delta {delta:e}, order {k}: the bound is not tight ({})",
                w.ratio[k]
            );
        }
    }
}

/// the double-double jet: the value, slope and order 2 of each case within C eps_dd kappa_k, and the bound tight.
/// Control: a relative error of 2^-90 put into x^2 of the product case is caught.
#[test]
fn double_double_jet_slope_errors_are_within_eps_dd_kappa() {
    for (ci, c) in CASES.iter().enumerate() {
        for (di, &delta) in DELTAS.iter().enumerate() {
            check(c.name, delta, &dd_worst(c, c.dd, delta, seed(ci, di), EPS_DD));
        }
    }
    let bad: fn(Jet<3>) -> Jet<3> =
        |x| ((x * x).mulc(DV::splat(DD::new(1.0, 2f64.powi(-90)))) - one()) * (x / (x - one()));
    let w = dd_worst(&CASES[2], bad, 1e-6, seed(2, 0), EPS_DD);
    assert!(
        (0..3).all(|k| w.ratio[k] > C),
        "control: x^2 off by 2^-90 passes, {:?}",
        w.ratio
    );
}

/// the quad-double jet on quad-double inputs: each case within C eps_qd kappa_k, and the bound tight. Control: the
/// double-double jet fails the quad-double bound on every amplified coefficient.
#[test]
fn quad_double_jet_slope_errors_are_within_eps_qd_kappa() {
    for (ci, c) in CASES.iter().enumerate() {
        for (di, &delta) in DELTAS.iter().enumerate() {
            check(c.name, delta, &qd_worst(c, delta, seed(ci, di), true));
            let w = dd_worst(c, c.dd, delta, seed(ci, di), EPS_QD);
            for k in 0..3 {
                if w.kappa[k] >= AMPLIFIED {
                    assert!(
                        w.ratio[k] > C,
                        "control: {}, order {k}: the double-double jet passes",
                        c.name
                    );
                }
            }
        }
    }
}

/// On the same double-double inputs, the quad-double jet removes the double-double jet's error: where the slope of
/// the products with 1/(a - 1) keeps fewer than 10 digits in double-double (delta = 1e-12, kappa about 3e23), and on
/// every amplified coefficient of every case, the quad-double error is at least 30 digits smaller (about 32, the
/// ratio of the units, is seen).
#[test]
fn quad_double_jet_removes_the_double_double_slope_error() {
    for (ci, c) in CASES.iter().enumerate() {
        for (di, &delta) in DELTAS.iter().enumerate() {
            let d = dd_worst(c, c.dd, delta, seed(ci, di), EPS_DD);
            let q = qd_worst(c, delta, seed(ci, di), false);
            for k in 0..3 {
                if d.kappa[k] < AMPLIFIED {
                    continue;
                }
                let digits = (d.err[k] / q.err[k]).log10();
                println!(
                    "{:22} delta {delta:.0e} order {k}: double-double {:.1e}, quad-double {:.1e}, {digits:.1} digits",
                    c.name, d.err[k], q.err[k]
                );
                assert!(
                    q.err[k] <= 1e-30 * d.err[k],
                    "{}, delta {delta:e}, order {k}: {digits:.1} digits",
                    c.name
                );
            }
            if c.product && delta == 1e-12 {
                assert!(
                    d.err[1] > 1e-10,
                    "{}: the double-double slope error {:e} is not large",
                    c.name,
                    d.err[1]
                );
            }
        }
    }
}
