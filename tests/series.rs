//! Series products (`series`): the exact product `mullow` against the naive sums of the same terms formed in
//! octo-double, on double-, quad- and octo-double lanes, and the relaxed products (`Relaxed`) of online recurrences
//! against their planted solutions and their naive online sums.
//!
//! Pass, fixed before the first run. `mullow` on every planted case (below) at n = 128, 251 and 512 is within
//! 1e-30 (DV), 1e-60 (QV) and 1e-120 (OV) of the octo-double reference relative to sum |a_i| |b_(k-i)|, with every
//! inverse transform's value within 1/4 of its integer and no fallback; on small integers it is exact. Controls, which
//! must fail: the slope and the blocks removed on the cases spanning 10^+-60; the last block pair dropped; the output
//! unscaled with a wrong slope; a NaN in an output, and in an input (which also makes `max_frac` infinite).
//!
//! The relaxed products: on recurrences whose solutions are dyadic integers (exact in every precision), the online
//! solution equals the planted one bit for bit, for one factor known (a series quotient) and both online (a square
//! root), with squares from side 4 and with the lanes' own `BLOCK_MIN`; on full-precision coefficients the online
//! solutions with relaxed and with naive sums agree to 1e-28 (DV), 1e-58 (QV), 1e-118 (OV) relative to each
//! coefficient. Controls: the first square dropped (`RELAXED_MUT_DROP`) must break both. Without squares (`with_min`
//! 0) `sum` is bitwise `cs_range`.
//!
//! Planted cases (8 lanes, random signs, all parts random, each lane its own offsets): `flat`, |a_i| ~ 2^(-0.7 i) and
//! |b_i| ~ 2^(-0.4 i), each times 2^(+-4) at random; `ramp`, log10 |a_i| from -60 to +60 and log10 |b_i| from +60 to
//! -60, each +-1 at random; `bumpy`, log10 |a_i| = 60 sin(2 pi 1.3 i / n + phase), log10 |b_i| = 60 cos(...);
//! `holes`, `flat` with a third of the coefficients and one whole lane zero; `ints`, integers in [-1000, 1000].
#![allow(clippy::needless_range_loop)]
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::dual::Lane;
use multidouble::field::{cs_range, Fl};
use multidouble::native::{Du, DV, OV, QV, V8};
use multidouble::od::OD;
use multidouble::series::{
    mullow, mullow_naive, mullow_pow2, Cfg, Expansion, Relaxed, Stats, MUT_DROP_PAIR, MUT_E2_PLAIN, MUT_E2_PRESCALE,
    MUT_E2_SPLIT_ALWAYS, MUT_SLOPE, MUT_ZERO_LANE, RELAXED_MUT_DROP,
};
use multidouble::simd::Native;

const L10: f64 = std::f64::consts::LOG2_10;

/// a random octo-double of magnitude 2^e (within a factor 2), random sign, all eight parts in use
fn rand_od(r: &mut Rng, e: f64) -> OD {
    let sign = if r.next_u64() & 1 == 0 { 1.0 } else { -1.0 };
    let e0 = e.floor();
    let mut x = [0.0f64; 8];
    x[0] = sign * (1.0 + r.unit()) * (e0 - 1.0).exp2();
    for j in 1..8 {
        x[j] = (r.unit() - 0.5) * x[j - 1].abs() * (-52.0f64).exp2();
    }
    OD::new(x)
}

/// an expansion with lane l the first NP parts of lanes\[l\]
fn make<E: Expansion<Native>>(lanes: &[OD; 8]) -> E {
    let p: Vec<V8> = (0..E::NP)
        .map(|q| V8::from_array(std::array::from_fn(|l| lanes[l].x[q])))
        .collect();
    E::from_parts(&p)
}

/// lane l of x as an octo-double, exactly
fn od_lane<E: Expansion<Native>>(x: &E, l: usize) -> OD {
    OD::new(std::array::from_fn(|q| {
        if q < E::NP {
            x.part(q).to_array()[l]
        } else {
            0.0
        }
    }))
}

/// x as octo-double lanes, exactly
fn promote<E: Expansion<Native>>(x: &E) -> OV {
    OV::from_lanes(&std::array::from_fn(|l| od_lane(x, l)))
}

/// a series of n coefficients, log2 |coefficient i| on lane l given by lg(i, l), zero where zero(i, l)
fn series<E: Expansion<Native>>(
    r: &mut Rng,
    n: usize,
    lg: impl Fn(usize, usize, &mut Rng) -> f64,
    zero: impl Fn(usize, usize) -> bool,
) -> Vec<E> {
    (0..n)
        .map(|i| {
            let lanes: [OD; 8] = std::array::from_fn(|l| {
                if zero(i, l) {
                    OD::ZERO
                } else {
                    let e = lg(i, l, r);
                    rand_od(r, e)
                }
            });
            make(&lanes)
        })
        .collect()
}

/// the planted pair (a, b) of a case
fn case<E: Expansion<Native>>(name: &str, n: usize, seed: u64) -> (Vec<E>, Vec<E>) {
    let mut r = Rng(seed);
    let nf = n as f64;
    let no = |_: usize, _: usize| false;
    match name {
        "flat" | "holes" => {
            let holes = name == "holes";
            let z = move |i: usize, l: usize| holes && (l == 5 || (i * 7 + l).is_multiple_of(3));
            let a = series(
                &mut r,
                n,
                |i, l, r| -0.7 * i as f64 + l as f64 + 8.0 * (r.unit() - 0.5),
                z,
            );
            let b = series(
                &mut r,
                n,
                |i, l, r| -0.4 * i as f64 - l as f64 + 8.0 * (r.unit() - 0.5),
                z,
            );
            (a, b)
        }
        "ramp" => {
            let ramp = |i: usize| 120.0 * i as f64 / (nf - 1.0);
            let a = series(
                &mut r,
                n,
                |i, l, r| L10 * (-60.0 + ramp(i) + 2.0 * (r.unit() - 0.5)) + l as f64,
                no,
            );
            let b = series(
                &mut r,
                n,
                |i, l, r| L10 * (60.0 - ramp(i) + 2.0 * (r.unit() - 0.5)) - l as f64,
                no,
            );
            (a, b)
        }
        "bumpy" => {
            let tp = 2.0 * std::f64::consts::PI;
            let a = series(
                &mut r,
                n,
                |i, l, _| L10 * 60.0 * (tp * 1.3 * i as f64 / nf + 0.3 * l as f64).sin(),
                no,
            );
            let b = series(
                &mut r,
                n,
                |i, l, _| L10 * 60.0 * (tp * 0.8 * i as f64 / nf + 0.2 * l as f64).cos(),
                no,
            );
            (a, b)
        }
        "ints" => {
            let int = |r: &mut Rng| -> Vec<E> {
                (0..n)
                    .map(|_| {
                        make(&std::array::from_fn(|_| {
                            OD::from_f64((r.next_u64() % 2001) as f64 - 1000.0)
                        }))
                    })
                    .collect()
            };
            let a = int(&mut r);
            let b = int(&mut r);
            (a, b)
        }
        _ => panic!("case {name}"),
    }
}

/// the fast product into fresh accumulators
fn fast<E: Expansion<Native>>(a: &[E], b: &[E], n: usize, cfg: &Cfg) -> (Vec<E>, Stats) {
    let mut acc = vec![E::acc_zero(); n];
    let st = mullow(a, b, n, cfg, &mut acc);
    (acc.iter().map(E::acc_fin).collect(), st)
}

/// the reference: the naive sums of the terms promoted to octo-double
fn reference<E: Expansion<Native>>(a: &[E], b: &[E], n: usize) -> Vec<OV> {
    let (ao, bo): (Vec<OV>, Vec<OV>) = (a.iter().map(promote).collect(), b.iter().map(promote).collect());
    mullow_naive(&ao, &bo, n)
}

/// max over k and lanes of |x - y| / sum_i |a_i| |b_(k-i)| and of |x - y| / |y| (y nonzero), the difference in
/// octo-double, both infinite where a part of x or y is not finite; and the number of coefficients that differ from y
/// (y rounded to x's parts) in any bit
fn compare<E: Expansion<Native>>(x: &[E], y: &[OV], a: &[E], b: &[E]) -> (f64, f64, usize) {
    let ah: Vec<[f64; 8]> = a.iter().map(|v| v.part(0).to_array().map(f64::abs)).collect();
    let bh: Vec<[f64; 8]> = b.iter().map(|v| v.part(0).to_array().map(f64::abs)).collect();
    let (mut ra, mut rc, mut differ) = (0.0f64, 0.0f64, 0);
    for k in 0..y.len() {
        let yl = y[k].lanes();
        for l in 0..8 {
            let xl = od_lane(&x[k], l);
            let d = (xl - yl[l]).to_f64().abs();
            if xl.x.iter().chain(yl[l].x.iter()).any(|p| !p.is_finite()) || !d.is_finite() {
                (ra, rc, differ) = (f64::INFINITY, f64::INFINITY, differ + 1);
                continue;
            }
            let ab: f64 = (0..=k)
                .filter(|&i| i < ah.len() && k - i < bh.len())
                .map(|i| ah[i][l] * bh[k - i][l])
                .sum();
            if ab > 0.0 {
                ra = ra.max(d / ab);
            } else if d > 0.0 {
                ra = f64::INFINITY;
            }
            let yv = yl[l].to_f64().abs();
            if yv > 0.0 {
                rc = rc.max(d / yv);
            }
            if d != 0.0 {
                differ += 1;
            }
        }
    }
    (ra, rc, differ)
}

/// the bound of each expansion's checks, relative to sum |a_i| |b_(k-i)|
fn bound<E: Expansion<Native>>() -> f64 {
    match E::NP {
        2 => 1e-30,
        4 => 1e-60,
        _ => 1e-120,
    }
}

/// every planted case at n = 128, 251, 512 within the bound with max_frac < 1/4 and no fallback, the integers exact,
/// and the controls failing; the report of each case on stdout
fn planted<E: Expansion<Native>>(name: &str) -> bool {
    let cfg = Cfg::default();
    let tol = bound::<E>();
    let mut ok = true;
    for &n in &[128usize, 251, 512] {
        for (ci, case_name) in ["flat", "holes", "ramp", "bumpy", "ints"].iter().enumerate() {
            let (a, b) = case::<E>(case_name, n, 1000 + 17 * n as u64 + ci as u64);
            let rf = reference(&a, &b, n);
            let (fx, st) = fast(&a, &b, n, &cfg);
            let (ra, rc, differ) = compare(&fx, &rf, &a, &b);
            let (na, _, _) = compare(&mullow_naive(&a, &b, n), &rf, &a, &b);
            let pass = ra <= tol && st.max_frac < 0.25 && st.fallback == 0 && (*case_name != "ints" || differ == 0);
            // the controls: the slope and blocks off on the wide cases; the last convolved pair dropped where there
            // are two or more; a wrong slope where the slope is not zero
            let wide = *case_name == "ramp" || *case_name == "bumpy";
            let (c0, _, _) = compare(
                &fast(
                    &a,
                    &b,
                    n,
                    &Cfg {
                        scale: false,
                        blocks: false,
                        ..cfg
                    },
                )
                .0,
                &rf,
                &a,
                &b,
            );
            let (c1, _, _) = compare(
                &fast(
                    &a,
                    &b,
                    n,
                    &Cfg {
                        mutate: MUT_DROP_PAIR,
                        ..cfg
                    },
                )
                .0,
                &rf,
                &a,
                &b,
            );
            let (c2, _, _) = compare(
                &fast(
                    &a,
                    &b,
                    n,
                    &Cfg {
                        mutate: MUT_SLOPE,
                        ..cfg
                    },
                )
                .0,
                &rf,
                &a,
                &b,
            );
            let ctrl = (!wide || c0 > tol) && c1 > tol && (*case_name == "ints" || c2 > tol);
            ok &= pass && ctrl;
            println!(
                "{name} {case_name:5} {n:3}: blocks {:2}x{:<2} pairs {:3} digits {:2} max_frac {:.1e} rel|a||b| \
                 {ra:.2e} (naive {na:.2e}) rel|c| {rc:.2e} differ {differ:4} | controls {c0:.1e} {c1:.1e} {c2:.1e} \
                 {}",
                st.blocks.0,
                st.blocks.1,
                st.pairs,
                st.digits,
                st.max_frac,
                if pass && ctrl { "PASS" } else { "FAIL" }
            );
        }
    }
    // NaN controls: one in an output coefficient (compare fails), one in an input (max_frac infinite, and the NaN
    // reaches the sums)
    let (a, b) = case::<E>("flat", 128, 77);
    let rf = reference(&a, &b, 128);
    let (mut fx, _) = fast(&a, &b, 128, &cfg);
    let mut lanes: [OD; 8] = std::array::from_fn(|l| od_lane(&fx[40], l));
    lanes[3].x[1] = f64::NAN;
    fx[40] = make(&lanes);
    let (r1, _, _) = compare(&fx, &rf, &a, &b);
    let mut a2 = a.clone();
    let mut lanes: [OD; 8] = std::array::from_fn(|l| od_lane(&a2[17], l));
    lanes[5].x[0] = f64::NAN;
    a2[17] = make(&lanes);
    let (fx2, st2) = fast(&a2, &b, 128, &cfg);
    let (r2, _, _) = compare(&fx2, &reference(&a2, &b, 128), &a2, &b);
    // a NaN compares false, so each must not pass its bound
    let passes = |v: f64, b: f64| v <= b;
    let fired = !passes(r1, tol) && !passes(st2.max_frac, 0.2499) && !passes(r2, tol);
    println!(
        "{name} NaN controls: output {r1:.1e}, input max_frac {:.1e} rel {r2:.1e}: fired {fired}",
        st2.max_frac
    );
    ok && fired
}

#[test]
fn mullow_planted_dv() {
    assert!(planted::<DV>("DV"));
}

#[test]
fn mullow_planted_qv() {
    assert!(planted::<QV>("QV"));
}

#[test]
fn mullow_planted_ov() {
    assert!(planted::<OV>("OV"));
}

/// the digits of a coefficient against its value, sum_r d_r 2^(16 r) - x 2^k per lane in octo-double, within 8; the
/// control, one digit one off, must miss it
fn digit_check<E: Expansion<Native>>(mutate: bool) -> f64 {
    let mut r = Rng(5);
    let mut worst = 0.0f64;
    for it in 0..2000 {
        let e = (r.unit() * 40.0) as i32 - 20;
        let lanes: [OD; 8] = std::array::from_fn(|_| rand_od(&mut r, e as f64));
        let x: E = make(&lanes);
        let t = 28;
        let w = 16 * t as i32 - 2;
        let k: [i32; 8] = std::array::from_fn(|_| w - e - 1 - (it % 7));
        let mut dv = vec![V8::zero(); t];
        multidouble::series::digits(&x, &k, t, &mut dv);
        let mut d: Vec<[f64; 8]> = dv.iter().map(|v| v.to_array()).collect();
        if mutate && it == 0 {
            d[3][2] += 1.0;
        }
        for l in 0..8 {
            let mut acc = OD::ZERO;
            for (q, dq) in d.iter().enumerate() {
                acc = acc + OD::from_f64(dq[l]).mul_pwr2((16.0 * q as f64).exp2());
            }
            let xv = od_lane(&x, l).mul_pwr2((k[l] as f64).exp2());
            let diff = (acc - xv).to_f64().abs();
            worst = if diff.is_finite() {
                worst.max(diff)
            } else {
                f64::INFINITY
            };
        }
    }
    worst
}

#[test]
fn digits_exact() {
    for (name, w, wm) in [
        ("DV", digit_check::<DV>(false), digit_check::<DV>(true)),
        ("QV", digit_check::<QV>(false), digit_check::<QV>(true)),
        ("OV", digit_check::<OV>(false), digit_check::<OV>(true)),
    ] {
        println!("digits {name}: worst {w:.2e}, control {wm:.2e}");
        assert!(w <= 8.0, "{name} digits");
        assert!(wm > 8.0, "{name} digit control did not fail");
    }
}

/// splat of an f64 as an expansion
fn splat<E: Expansion<Native>>(x: f64) -> E {
    make(&[OD::from_f64(x); 8])
}

/// exactly v on every lane, its lower parts zero
fn exact<E: Expansion<Native>>(c: &[E], v: f64) -> bool {
    c.iter()
        .all(|x| (0..8).all(|l| od_lane(x, l).x[0] == v && od_lane(x, l).x[1..].iter().all(|&p| p == 0.0)))
}

/// The edge cases under a control (`Cfg::mutate`, 0 off), each against the reference or its exact value: a product
/// past the FFT tables (8193 ones times one); a lane whose planned scale lies outside f64's range (lane 0 of a =
/// 2^800, 2^-802, 0 and b zero; MUT_ZERO_LANE fails it); 2^e2 on the long route at the ends of the range, 8193
/// copies of 2^-600 times 2^-600 at e2 1200 and of 2^1023 times 2^-1000 at e2 1, exactly 1 and 2^24 (MUT_E2_PLAIN
/// fails it); 2^-1074 and 2^-537 squared; a block too wide for the digits (1 and 2^-1024 squared, spread 1024, no
/// slope); the direct route at e2 = 0 on 2^1023 and 2^-900 (MUT_E2_SPLIT_ALWAYS fails it); and at e2 != 0 on 2^900,
/// 2^-900 at e2 1 and 2^1000, 2^-900 times 2^-100 at e2 100 (MUT_E2_PRESCALE fails it)
fn edges<E: Expansion<Native>>(mutate: u8) -> bool {
    let cfg = Cfg {
        mutate,
        ..Cfg::default()
    };
    let tol = bound::<E>();
    let one: E = splat(1.0);
    let long: Vec<E> = vec![one; 8193];
    let (fx, st) = fast(&long, &[one], 8193, &cfg);
    let (r1, _, _) = compare(&fx, &reference(&long, &[one], 8193), &long, &[one]);
    let lane0 = |x: [f64; 3]| -> Vec<E> {
        x.iter()
            .map(|&v| {
                let mut l = [OD::from_f64(1.0); 8];
                l[0] = OD::from_f64(v);
                make(&l)
            })
            .collect()
    };
    let a = lane0([800f64.exp2(), (-802f64).exp2(), 0.0]);
    let b = lane0([0.0, 0.0, 0.0]);
    let (fx2, st2) = fast(&a, &b, 3, &cfg);
    let (r2, _, _) = compare(&fx2, &reference(&a, &b, 3), &a, &b);
    let e2case = |x: f64, y: f64, e2: i32, want: f64| -> bool {
        let xs: Vec<E> = vec![splat(x); 8193];
        let mut acc = vec![E::acc_zero(); 8193];
        let st = mullow_pow2(&xs, &[splat::<E>(y)], 8193, &cfg, e2, &mut acc);
        let c: Vec<E> = acc.iter().map(E::acc_fin).collect();
        st.max_frac < 0.25 && exact(&c, want)
    };
    let e2a = e2case((-600f64).exp2(), (-600f64).exp2(), 1200, 1.0);
    let e2b = e2case(1023f64.exp2(), (-1000f64).exp2(), 1, 24f64.exp2());
    let tiny = |x: f64| -> f64 {
        let v: Vec<E> = vec![splat(x)];
        let (c, st) = fast(&v, &v, 1, &cfg);
        let (r, _, _) = compare(&c, &reference(&v, &v, 1), &v, &v);
        if st.max_frac < 0.25 {
            r
        } else {
            f64::INFINITY
        }
    };
    let (u1, u2) = (tiny((-1074f64).exp2()), tiny((-537f64).exp2()));
    let wide = Cfg {
        scale: false,
        spread: 1024,
        ..cfg
    };
    let w2: Vec<E> = vec![one, splat((-1024f64).exp2())];
    let mut accw = vec![E::acc_zero(); 2];
    let stw = mullow(&w2, &w2, 2, &wide, &mut accw);
    let cw: Vec<E> = accw.iter().map(E::acc_fin).collect();
    let (rw, _, _) = compare(&cw, &reference(&w2, &w2, 2), &w2, &w2);
    let wide_ok = exact(&cw[..1], 1.0) && rw <= tol && stw.direct > 0;
    let flat = Cfg {
        scale: false,
        blocks: false,
        spread: 2048,
        ..cfg
    };
    let w3: Vec<E> = vec![splat(1023f64.exp2()), splat((-900f64).exp2())];
    let mut acc3 = vec![E::acc_zero(); 2];
    let st3 = mullow(&w3, &[one], 2, &flat, &mut acc3);
    let c3: Vec<E> = acc3.iter().map(E::acc_fin).collect();
    let wide0_ok = exact(&c3[..1], 1023f64.exp2()) && exact(&c3[1..], (-900f64).exp2()) && st3.direct > 0;
    let wide_e2 = |a: [f64; 2], b: f64, e2: i32, want: [f64; 2]| -> bool {
        let x: Vec<E> = vec![splat(a[0].exp2()), splat(a[1].exp2())];
        let mut acc = vec![E::acc_zero(); 2];
        let st = mullow_pow2(&x, &[splat::<E>(b.exp2())], 2, &flat, e2, &mut acc);
        let c: Vec<E> = acc.iter().map(E::acc_fin).collect();
        st.direct > 0 && exact(&c[..1], want[0].exp2()) && exact(&c[1..], want[1].exp2())
    };
    let we1 = wide_e2([900.0, -900.0], 0.0, 1, [901.0, -899.0]);
    let we2 = wide_e2([1000.0, -900.0], -100.0, 100, [1000.0, -900.0]);
    let ok = r1 <= tol
        && r2 <= tol
        && st.max_frac < 0.25
        && st2.max_frac < 0.25
        && e2a
        && e2b
        && u1 <= tol
        && u2 <= tol
        && wide_ok
        && wide0_ok
        && we1
        && we2;
    println!(
        "edges {} (mutate {mutate}): {r1:.1e} {r2:.1e} {e2a} {e2b} {u1:.1e} {u2:.1e} {wide_ok} {wide0_ok} {we1} {we2}",
        E::NP
    );
    ok
}

/// the edge cases and their controls; the zero-lane control only where the case goes by convolution (`zero_lane`):
/// the double- and quad-double cost models form that 3-term pair term by term, where no lane is scaled
fn edges_all<E: Expansion<Native>>(zero_lane: bool) {
    assert!(edges::<E>(0), "edge cases");
    if zero_lane {
        assert!(!edges::<E>(MUT_ZERO_LANE), "the zero-lane control did not fail");
    }
    assert!(!edges::<E>(MUT_E2_PLAIN), "the e2 control did not fail");
    assert!(
        !edges::<E>(MUT_E2_SPLIT_ALWAYS),
        "the e2 = 0 split control did not fail"
    );
    assert!(!edges::<E>(MUT_E2_PRESCALE), "the e2 prescale control did not fail");
}

#[test]
fn mullow_edges() {
    edges_all::<DV>(false);
    edges_all::<QV>(false);
    edges_all::<OV>(true);
}

#[test]
fn mullow_empty() {
    let (a, _) = case::<QV>("flat", 16, 3);
    let none: Vec<QV> = Vec::new();
    for (x, y) in [(&none, &a), (&a, &none), (&none, &none)] {
        let (fx, _) = fast(x, y, 16, &Cfg::default());
        assert!(fx.len() == 16 && exact(&fx, 0.0), "empty factors give zeros");
    }
}

// ---- relaxed products

const B: usize = 2;

/// a field series from per-index point values and tangents: coefficient i, point p = 8 b + l
fn field_series<T: Lane<S = Native>>(
    n: usize,
    v: impl Fn(usize, usize) -> DD,
    t: impl Fn(usize, usize) -> DD,
) -> Vec<Fl<T, B>> {
    let load = |f: &dyn Fn(usize) -> DD| -> Fl<DV, B> {
        let (h, l): (Vec<f64>, Vec<f64>) = (0..8 * B).map(|p| (f(p).hi, f(p).lo)).unzip();
        Fl::load(&h, &l)
    };
    (0..n)
        .map(|i| {
            let (fv, ft) = (load(&|p| v(i, p)), load(&|p| t(i, p)));
            Fl(std::array::from_fn(|b| T::from_vt(fv.0[b], ft.0[b])))
        })
        .collect()
}

/// u and v bit for bit: every lane vector's value and tangent in octo-double
fn same<T: Lane<S = Native>>(u: &[Fl<T, B>], v: &[Fl<T, B>]) -> bool {
    let bits = |x: OV| x.c.map(|p| p.to_array().map(f64::to_bits));
    u.len() == v.len()
        && u.iter()
            .zip(v)
            .all(|(p, q)| (0..B).all(|b| (0..2).all(|c| bits(p.0[b].coef_od(c)) == bits(q.0[b].coef_od(c)))))
}

/// The planted quotient y = r / a solved online, y_k = r_k - sum_(i=1..=k) a_i y_(k-i) (a_0 = 1), by the relaxed
/// product of a and y with squares from side s0 (0: none, the naive sums), and the planted square root x of r = x^2,
/// x_k = r_k - sum_(i=1..k-1) x_i x_(k-i) (x_0 = 1/2). Their coefficients and tangents are integers in [-1000, 1000]
/// times 2^-floor(i/4) (a_0 and x_0 without tangents), so every sum is exact and the solutions are the planted ones bit
/// for bit. Returns whether both are.
fn relaxed_exact<T: Lane<S = Native>>(n: usize, s0: usize, mutate: u8) -> bool {
    let mut r = Rng(11);
    let tab: Vec<Vec<f64>> = (0..6)
        .map(|_| (0..n * 8 * B).map(|_| (r.next_u64() % 2001) as f64 - 1000.0).collect())
        .collect();
    let g = |t: usize, i: usize, p: usize| DD::from_f64(tab[t][i * 8 * B + p] * (-((i / 4) as f64)).exp2());
    let a = field_series::<T>(
        n,
        |i, p| if i == 0 { DD::ONE } else { g(0, i, p) },
        |i, p| if i == 0 { DD::ZERO } else { g(1, i, p) },
    );
    let y = field_series::<T>(n, |i, p| g(2, i, p), |i, p| g(3, i, p));
    let x = field_series::<T>(
        n,
        |i, p| if i == 0 { DD::from_f64(0.5) } else { g(4, i, p) },
        |i, p| if i == 0 { DD::ZERO } else { g(5, i, p) },
    );
    let ry: Vec<Fl<T, B>> = (0..n).map(|k| cs_range(&a, &y, k, 0, k)).collect();
    let rx: Vec<Fl<T, B>> = (0..n).map(|k| cs_range(&x, &x, k, 0, k)).collect();
    let mut pa = Relaxed::<T, B>::with_min(n, s0);
    let mut px = Relaxed::<T, B>::with_min(n, s0);
    pa.mutate = mutate;
    px.mutate = mutate;
    let mut ys = vec![Fl::<T, B>::zero(); n];
    let mut xs = vec![Fl::<T, B>::zero(); n];
    for k in 0..n {
        ys[k] = if k == 0 {
            ry[0]
        } else {
            ry[k] - pa.sum(&a, &ys, k, 1, k)
        };
        xs[k] = match k {
            0 => x[0],
            1 => rx[1],
            _ => rx[k] - px.sum(&xs, &xs, k, 1, k - 1),
        };
        pa.step(&a, &ys, k);
        px.step(&xs, &xs, k);
    }
    same(&ys, &y) && same(&xs, &x)
}

#[test]
fn relaxed_planted_exact() {
    let run = |n: usize, s: [usize; 4], m: u8| -> [bool; 4] {
        [
            relaxed_exact::<DV>(n, s[0], m),
            relaxed_exact::<QV>(n, s[1], m),
            relaxed_exact::<OV>(n, s[2], m),
            relaxed_exact::<Du>(n, s[3], m),
        ]
    };
    let own = [DV::BLOCK_MIN, QV::BLOCK_MIN, OV::BLOCK_MIN, Du::BLOCK_MIN];
    for (n, s) in [(300usize, [4usize; 4]), (300, [16; 4]), (2100, own)] {
        let ok = run(n, s, 0);
        println!("relaxed exact n {n}, squares from {s:?}: DV QV OV Du {ok:?}");
        assert!(ok.iter().all(|&o| o), "planted solutions not recovered");
        let ctl = run(n, s, RELAXED_MUT_DROP);
        println!("  control, the first square dropped: {ctl:?} (must be all false)");
        assert!(ctl.iter().all(|&o| !o), "the dropped-square control did not fail");
    }
}

/// Without squares `sum` is bitwise `cs_range`, on a lane with squares (DV) and on one without (F8)
#[test]
fn relaxed_without_squares_is_cs_range() {
    use multidouble::native::F8;
    let mut r = Rng(3);
    let tab: Vec<DD> = (0..40 * 8 * B).map(|_| DD::new(r.sym(), r.sym() * 1e-17)).collect();
    let x = field_series::<DV>(40, |i, p| tab[i * 8 * B + p], |_, _| DD::ZERO);
    let p = Relaxed::<DV, B>::with_min(40, 0);
    let pf = Relaxed::<F8, B>::new(40);
    let xf: Vec<Fl<F8, B>> = x.iter().map(|f| Fl(f.0.map(F8::cst))).collect();
    for k in 0..40 {
        assert!(
            same(&[p.sum(&x, &x, k, 1, k)], &[cs_range(&x, &x, k, 1, k)]),
            "DV order {k}"
        );
        let (u, w) = (pf.sum(&xf, &xf, k, 0, k), cs_range(&xf, &xf, k, 0, k));
        assert!(
            (0..B).all(|b| u.0[b].val().hi.to_array() == w.0[b].val().hi.to_array()),
            "F8 order {k}"
        );
    }
}

/// The planted quotient on full-precision coefficients: a_0 = 1, |a_i| ~ 2^(-2i - 3), |y_i| ~ 2^-0.5i, r = a y in
/// octo-double rounded to the lane; y solved online with relaxed sums (squares from s0) and with naive sums. Returns
/// max_k max_lanes |y_relaxed - y_naive| / sum_i |a_i| |y_(k-i)|.
fn relaxed_accuracy<E: Expansion<Native> + Lane<S = Native>>(n: usize, s0: usize, mutate: u8) -> f64 {
    let mut r = Rng(29);
    let sr = |r: &mut Rng, g: f64, c: f64| -> Vec<Fl<E, B>> {
        (0..n)
            .map(|i| {
                Fl(std::array::from_fn(|_| {
                    make::<E>(&std::array::from_fn(|_| {
                        let e = -g * i as f64 - c + 2.0 * (r.unit() - 0.5);
                        rand_od(r, e)
                    }))
                }))
            })
            .collect()
    };
    let mut a = sr(&mut r, 2.0, 3.0);
    a[0] = Fl::splat(DD::ONE);
    let y = sr(&mut r, 0.5, 0.0);
    let ab = |b: usize| -> (Vec<OV>, Vec<OV>) {
        (
            a.iter().map(|f| promote(&f.0[b])).collect(),
            y.iter().map(|f| promote(&f.0[b])).collect(),
        )
    };
    // r in octo-double, rounded to E
    let rr: Vec<Fl<E, B>> = {
        let per: Vec<Vec<OV>> = (0..B)
            .map(|b| {
                let (x, z) = ab(b);
                mullow_naive(&x, &z, n)
            })
            .collect();
        (0..n)
            .map(|k| Fl(std::array::from_fn(|b| make::<E>(&per[b][k].lanes()))))
            .collect()
    };
    let solve = |s: Option<usize>| -> Vec<Fl<E, B>> {
        let mut p = Relaxed::<E, B>::with_min(n, s.unwrap_or(0));
        p.mutate = mutate;
        let mut ys = vec![Fl::<E, B>::zero(); n];
        for k in 0..n {
            ys[k] = if k == 0 { rr[0] } else { rr[k] - p.sum(&a, &ys, k, 1, k) };
            p.step(&a, &ys, k);
        }
        ys
    };
    let (yr, yn) = (solve(Some(s0)), solve(None));
    let mut worst = 0.0f64;
    for b in 0..B {
        let ah: Vec<[f64; 8]> = a.iter().map(|f| f.0[b].part(0).to_array().map(f64::abs)).collect();
        let yh: Vec<[f64; 8]> = yn.iter().map(|f| f.0[b].part(0).to_array().map(f64::abs)).collect();
        for k in 0..n {
            for l in 0..8 {
                let d = (od_lane(&yr[k].0[b], l) - od_lane(&yn[k].0[b], l)).to_f64().abs();
                let sc: f64 = (0..=k).map(|i| ah[i][l] * yh[k - i][l]).sum();
                worst = if d.is_finite() {
                    worst.max(d / sc)
                } else {
                    f64::INFINITY
                };
            }
        }
    }
    worst
}

#[test]
fn relaxed_accuracy_against_naive() {
    let t = |np: usize| match np {
        2 => 1e-28,
        4 => 1e-58,
        _ => 1e-118,
    };
    for (name, s0, w, wc, tol) in [
        (
            "DV",
            16,
            relaxed_accuracy::<DV>(700, 16, 0),
            relaxed_accuracy::<DV>(700, 16, RELAXED_MUT_DROP),
            t(2),
        ),
        (
            "QV",
            16,
            relaxed_accuracy::<QV>(700, 16, 0),
            relaxed_accuracy::<QV>(700, 16, RELAXED_MUT_DROP),
            t(4),
        ),
        (
            "OV",
            16,
            relaxed_accuracy::<OV>(700, 16, 0),
            relaxed_accuracy::<OV>(700, 16, RELAXED_MUT_DROP),
            t(8),
        ),
    ] {
        println!("relaxed accuracy {name} (squares from {s0}, n 700): {w:.2e}, control {wc:.2e} (bound {tol:.0e})");
        assert!(w <= tol, "{name} relaxed against naive");
        assert!(wc > tol, "{name} dropped-square control did not fail");
    }
}
