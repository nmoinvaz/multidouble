//! Review checks for `DD::sloppy_div`: the worst error against exact arithmetic over generators that put the divisor's
//! and the dividend's low parts at their largest, the special values against `/`, and the lanes on them.
mod common;
use common::{Rng, U2};
use multidouble::dd::DD;
use multidouble::exact::Dy;
use multidouble::native::DV;

fn exact(x: DD) -> Dy {
    Dy::from_f64(x.hi).add(&Dy::from_f64(x.lo))
}

fn quotient_err(q: DD, a: DD, b: DD) -> f64 {
    exact(q).mul(&exact(b)).sub(&exact(a)).ratio(&exact(a)).abs() / U2
}

fn ulp(x: f64) -> f64 {
    f64::from_bits(x.abs().to_bits() + 1) - x.abs()
}

/// hi by kind, lo near half an ulp of hi or anywhere below it
fn dd(r: &mut Rng, kind: usize) -> DD {
    let hi = match kind {
        0 => 1.0 + r.unit(),
        1 => 1.0 + r.unit() * 2f64.powi(-((r.next_u64() % 50) as i32) - 1),
        2 => 2.0 - r.unit() * 2f64.powi(-((r.next_u64() % 50) as i32)),
        _ => 1.0 + (r.next_u64() % 64) as f64 * 2f64.powi(-((r.next_u64() % 47) as i32) - 6),
    };
    let s = if r.next_u64() & 1 == 0 { 1.0 } else { -1.0 };
    let lo = if r.next_u64() & 1 == 0 {
        s * 0.5 * ulp(hi) * (1.0 - r.unit() * 2f64.powi(-((r.next_u64() % 40) as i32)))
    } else {
        r.sym() * 0.5 * ulp(hi)
    };
    DD::new(hi, lo)
}

#[test]
fn worst_error() {
    let n: usize = std::env::var("FABLE_N").ok().and_then(|v| v.parse().ok()).unwrap_or(400_000);
    let (mut worst, mut wdiv) = (0.0f64, 0.0f64);
    let mut at = (DD::ZERO, DD::ZERO);
    for ka in 0..4 {
        for kb in 0..4 {
            let mut r = Rng(1000 + (4 * ka + kb) as u64);
            let (mut w, mut wd) = (0.0f64, 0.0f64);
            for _ in 0..n / 16 {
                let (a, b) = (dd(&mut r, ka), dd(&mut r, kb));
                let e = quotient_err(a.sloppy_div(b), a, b);
                wd = wd.max(quotient_err(a / b, a, b));
                if e > w {
                    w = e;
                    if e > worst {
                        at = (a, b);
                    }
                }
            }
            println!("dividend kind {ka}, divisor kind {kb}: sloppy_div worst {w:.3} u^2, `/` worst {wd:.3} u^2");
            worst = worst.max(w);
            wdiv = wdiv.max(wd);
        }
    }
    println!("sloppy_div worst {worst:.3} u^2 at {at:?}; `/` worst {wdiv:.3} u^2");
    assert!(worst <= 15.0 + 56.0 * 2f64.powi(-53));
}

/// the test's own generator for divisors near a power of two: how often is the low part within a factor of four of
/// half an ulp, and how often does it move hi off 2^k (1 +- 2^-j)?
#[test]
fn pr_generator_low_parts() {
    let mut r = Rng(13);
    let p2 = |k: i32| 2f64.powi(k);
    let (mut full, mut moved, mut n) = (0, 0, 0);
    for i in 0..20_000 {
        let _a = r.dd(20);
        if i % 2 == 0 {
            let _b = r.dd(20);
            continue;
        }
        let k = r.dd(20).hi.abs().log2().floor() as i32;
        let j = 1 + (r.dd(0).hi.abs() * 50.0) as i32 % 52;
        let s = if r.dd(0).hi > 0.0 { 1.0 } else { -1.0 };
        let hi = p2(k) * (1.0 + s * p2(-j));
        let b = DD::new(hi, r.dd(20).lo * p2(k));
        n += 1;
        moved += (b.hi != hi) as usize;
        full += (b.lo.abs() >= 0.125 * ulp(b.hi)) as usize;
    }
    println!("divisors near a power of two: {n}; hi moved off 2^k (1 +- 2^-j) by the low part: {moved}; |lo| >= ulp/8: {full}");
}

fn same(a: f64, b: f64) -> bool {
    a.to_bits() == b.to_bits() || (a.is_nan() && b.is_nan())
}

#[test]
fn special_values() {
    let d = |hi: f64, lo: f64| DD { hi, lo };
    let vals = [
        d(0.0, 0.0),
        d(-0.0, 0.0),
        d(1.0, 0.0),
        d(-3.0, 1e-17),
        d(f64::INFINITY, 0.0),
        d(f64::NEG_INFINITY, 0.0),
        d(f64::NAN, 0.0),
        d(f64::MAX, f64::MAX * 2f64.powi(-54)),
        d(f64::MIN_POSITIVE, 0.0),
        d(5e-324, 0.0),
        d(1e-300, 1e-317),
        d(2f64.powi(-970), 2f64.powi(-1024)),
    ];
    let mut differ = Vec::new();
    for &a in &vals {
        for &b in &vals {
            let (s, q) = (a.sloppy_div(b), a / b);
            let lanes = DV::splat(a).sloppy_div(DV::splat(b));
            for j in 0..8 {
                let g = lanes.lane(j);
                assert!(same(g.hi, s.hi) && same(g.lo, s.lo), "lane {j}: {a:?} / {b:?}: {g:?} vs {s:?}");
            }
            let class = |x: DD| {
                if x.hi.is_nan() || x.lo.is_nan() {
                    "nan".to_string()
                } else if x.hi.is_infinite() {
                    format!("{}", x.hi)
                } else if x.hi == 0.0 {
                    format!("{:?}", x.hi)
                } else {
                    "finite".to_string()
                }
            };
            if class(s) != class(q) || (class(s) == "finite" && ((s.hi - q.hi) / q.hi).abs() > 1e-25) {
                differ.push(format!("{a:?} / {b:?}: sloppy_div {s:?}, `/` {q:?}"));
            }
        }
    }
    println!("{} of {} special pairs differ in class or value between sloppy_div and `/`:", differ.len(), vals.len() * vals.len());
    for l in &differ {
        println!("  {l}");
    }
}

/// the PR's test loop, with its generator (`r.dd(20).lo`) and with the low part at the divisor's own scale
/// (`r.dd(0).lo`), and with the dividend near a power of two as well
#[test]
fn pr_test_with_scaled_low_part() {
    let p2 = |k: i32| 2f64.powi(k);
    for variant in 0..3 {
        let mut r = Rng(13);
        let mut worst: f64 = 0.0;
        let near = |r: &mut Rng, variant: usize| {
            let k = r.dd(20).hi.abs().log2().floor() as i32;
            let j = 1 + (r.dd(0).hi.abs() * 50.0) as i32 % 52;
            let s = if r.dd(0).hi > 0.0 { 1.0 } else { -1.0 };
            let lo = if variant == 0 { r.dd(20).lo } else { r.dd(0).lo };
            DD::new(p2(k) * (1.0 + s * p2(-j)), lo * p2(k))
        };
        for i in 0..20_000 {
            let a = if variant == 2 && i % 2 == 1 { near(&mut r, 1) } else { r.dd(20) };
            let b = if i % 2 == 0 { r.dd(20) } else { near(&mut r, variant) };
            worst = worst.max(quotient_err(a.sloppy_div(b), a, b));
        }
        println!("variant {variant}: worst {worst:.3} u^2");
    }
}
