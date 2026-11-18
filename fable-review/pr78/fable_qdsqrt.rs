//! Review check for the quad-double square root from the double-double start: the worst error against exact
//! arithmetic of the new `QD::sqrt` and of the three Newton steps it replaces, on the same inputs, random and chosen
//! where the double-double start is worst (a0 just above a power of four, a1 at its largest); the lanes against the
//! scalar bit for bit; and the special values.
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::exact::Dy;
use multidouble::native::QV;
use multidouble::qd::QD;

/// main's square root (three Newton steps on 1/sqrt(a) from a double), through the public operations
fn sqrt_newton3(x: QD) -> QD {
    if x.is_zero() {
        return QD::ZERO;
    }
    let s = f64::from_bits(x.x[0].sqrt().to_bits() & 0x7ff0_0000_0000_0000);
    let inv = 1.0 / s;
    let a = x.mul_pwr2(inv).mul_pwr2(inv);
    let mut r = QD::from_f64(1.0 / a.x[0].sqrt());
    let h = a.mul_pwr2(0.5);
    for _ in 0..3 {
        r = r + (-(h * r.sqr())).add_f(0.5) * r;
    }
    (r * a).mul_pwr2(s)
}

/// |r^2 - a| / (2 a) in units of u^4 = 2^-212: the relative error of r as sqrt(a), to first order
fn err(r: QD, a: QD) -> f64 {
    let (re, ae) = (r.exact(), a.exact());
    re.mul(&re).sub(&ae).abs().ratio(&ae.ldexp(1)) / 2f64.powi(-212)
}

/// the double-double start's relative error against sqrt(a), in units of u^2 (y^2 - a over 2 a)
fn start_err(a: QD) -> f64 {
    let y = DD { hi: a.x[0], lo: a.x[1] }.sqrt();
    let ye = Dy::sum(&[y.hi, y.lo]);
    ye.mul(&ye).sub(&a.exact()).ratio(&a.exact().ldexp(1)) / 2f64.powi(-106)
}

fn input(r: &mut Rng, kind: usize) -> QD {
    let sgn = |r: &mut Rng| if r.next_u64() & 1 == 0 { 1.0 } else { -1.0 };
    let a0 = match kind {
        // anywhere in [1, 4)
        0 => (1.0 + r.unit()) * if r.next_u64() & 1 == 0 { 1.0 } else { 2.0 },
        // just above 1, where an ulp of the root is largest relative to it
        1 => 1.0 + r.unit() * 2f64.powi(-((r.next_u64() % 40) as i32) - 1),
        // just above 2 (the root's binade [sqrt 2, 2))
        2 => 2.0 + r.unit() * 2f64.powi(-((r.next_u64() % 40) as i32)),
        // just below 4
        _ => 4.0 - r.unit() * 2f64.powi(-((r.next_u64() % 40) as i32)),
    };
    // a1 near its largest, half an ulp of a0, or anywhere
    let ulp = f64::from_bits(a0.to_bits() + 1) - a0;
    let a1 = if r.next_u64() & 1 == 0 {
        sgn(r) * 0.5 * ulp * (1.0 - r.unit() * 2f64.powi(-((r.next_u64() % 30) as i32)))
    } else {
        r.sym() * 0.5 * ulp
    };
    let a2 = r.sym() * a1.abs() * 2f64.powi(-53);
    let a3 = r.sym() * a2.abs() * 2f64.powi(-53);
    QD::from_sum(a0, a1, a2, a3)
}

#[test]
fn worst_error_new_and_old() {
    let n: usize = std::env::var("FABLE_N").ok().and_then(|v| v.parse().ok()).unwrap_or(300_000);
    for kind in 0..4 {
        let mut r = Rng(0x5a17 + kind as u64);
        let (mut wn, mut wo, mut ws) = ((0.0f64, QD::ZERO), (0.0f64, QD::ZERO), 0.0f64);
        let mut hist = [0usize; 8];
        for _ in 0..n {
            let a = input(&mut r, kind);
            let (en, eo) = (err(a.sqrt(), a), err(sqrt_newton3(a), a));
            ws = ws.max(start_err(a).abs());
            if en > wn.0 {
                wn = (en, a);
            }
            if eo > wo.0 {
                wo = (eo, a);
            }
            hist[(en.max(1e-9).log2().floor() as i32 + 2).clamp(0, 7) as usize] += 1;
        }
        println!(
            "kind {kind}: n {n}: worst new {:.3} u^4 at {:x?}; worst old {:.3} u^4; worst start {ws:.3} u^2; new's histogram by log2 from -2: {hist:?}",
            wn.0,
            wn.1.x.map(f64::to_bits),
            wo.0
        );
        // the test's threshold: 4 units of 2^-209 = 32 u^4
        assert!(wn.0 <= 32.0);
    }
}

fn same(a: QD, b: QD) -> bool {
    a.x.iter().zip(b.x.iter()).all(|(x, y)| x.to_bits() == y.to_bits() || (x.is_nan() && y.is_nan()))
}

#[test]
fn lanes_match_scalar() {
    let mut r = Rng(77);
    for round in 0..200_000 {
        let a: [QD; 8] = std::array::from_fn(|l| {
            let q = input(&mut r, (round + l) % 4);
            let e = (r.next_u64() % 2100) as i32 - 1060;
            let q = q.mul_pwr2(2f64.powi(e.clamp(-1000, 1000))).mul_pwr2(2f64.powi(e - e.clamp(-1000, 1000)));
            if r.next_u64() % 50 == 0 { QD::ZERO } else { q }
        });
        let got = QV::from_lanes(&a).sqrt().lanes();
        for l in 0..8 {
            assert!(same(got[l], a[l].sqrt()), "lane {l}: sqrt {:?} = {:?}, scalar {:?}", a[l], got[l], a[l].sqrt());
        }
    }
}

#[test]
fn special_values() {
    let q = |x: [f64; 4]| QD { x };
    let cases = [
        q([0.0; 4]),
        q([-0.0, 0.0, 0.0, 0.0]),
        q([-1.0, 0.0, 0.0, 0.0]),
        q([-4.0, 1e-20, 0.0, 0.0]),
        q([f64::INFINITY, 0.0, 0.0, 0.0]),
        q([f64::NEG_INFINITY, 0.0, 0.0, 0.0]),
        q([f64::NAN, 0.0, 0.0, 0.0]),
        q([5e-324, 0.0, 0.0, 0.0]),
        q([1e-310, 0.0, 0.0, 0.0]),
        q([f64::MIN_POSITIVE, 0.0, 0.0, 0.0]),
        q([f64::MAX, f64::MAX * 2f64.powi(-54), f64::MAX * 2f64.powi(-108), f64::MAX * 2f64.powi(-162)]),
        q([4.0, -2f64.powi(-52), 0.0, 0.0]),
        q([1.0, 0.0, 0.0, 0.0]),
        q([4.0, 0.0, 0.0, 0.0]),
        q([2f64.powi(-1022), 2f64.powi(-1074), 0.0, 0.0]),
    ];
    for a in cases {
        let (new, old) = (a.sqrt(), sqrt_newton3(a));
        let lanes = QV::from_lanes(&[a; 8]).sqrt().lanes();
        let e = if a.x[0] > 0.0 && a.x[0].is_finite() { err(new, a) } else { f64::NAN };
        println!(
            "sqrt {:?}: new {:?}, old {:?}, lane {:?}, lanes same as scalar {}, err {e:.3} u^4",
            a.x,
            new.x,
            old.x,
            lanes[0].x,
            lanes.iter().all(|&l| same(l, new))
        );
    }
}

#[test]
fn new_and_old_bits() {
    let mut r = Rng(5);
    let (mut same_bits, mut n) = (0, 0);
    for i in 0..20000 {
        let a = input(&mut r, i % 4);
        let (new, old) = (a.sqrt(), sqrt_newton3(a));
        n += 1;
        same_bits += same(new, old) as usize;
        if i < 6 {
            println!("a {:x?}\n new {:x?} err {:.4}\n old {:x?} err {:.4}", a.x.map(f64::to_bits), new.x.map(f64::to_bits), err(new, a), old.x.map(f64::to_bits), err(old, a));
        }
    }
    println!("{same_bits} of {n} inputs give the same bits from the new and the old square root");
}

/// a_1 past half an ulp of a_0 (not a double-word pair, as a sum's renormalization can leave): the error of the new
/// square root
#[test]
fn leading_parts_not_double_word() {
    let mut r = Rng(99);
    for top in [0.75, 1.0, 4.0, 1024.0] {
        let (mut wn, mut wo) = (0.0f64, 0.0f64);
        for i in 0..200_000 {
            let mut a = input(&mut r, i % 4);
            let ulp = f64::from_bits(a.x[0].to_bits() + 1) - a.x[0];
            let s = if r.next_u64() & 1 == 0 { 1.0 } else { -1.0 };
            a.x[1] = s * (0.5 + (top - 0.5) * r.unit()) * ulp;
            wn = wn.max(err(a.sqrt(), a));
            wo = wo.max(err(sqrt_newton3(a), a));
        }
        println!("|a_1| up to {top} ulp(a_0): worst new {wn:.3} u^4, worst old {wo:.3} u^4");
    }
}
