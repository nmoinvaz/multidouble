//! Review checks for the octo-double square root from the double-double start: the worst error against exact
//! arithmetic on inputs at the top of the ladder H(2) (|x_i| up to an ulp of the part above), against the proven
//! bound 3.0000319 u^8, for the new `OD::sqrt` and for the four Newton steps it replaces; the lanes against the
//! scalar; special values; and, with the feature `mutate`, the old gap case under the mutation RENORM_FAST.
mod common;
use common::Rng;
use multidouble::native::OV;
use multidouble::od::OD;

/// main's square root (four Newton steps on 1/sqrt(a) from a double), through the public operations
fn sqrt_newton4(x: OD) -> OD {
    if x.is_zero() {
        return OD::from_f64(0.0);
    }
    let s = f64::from_bits(x.x[0].sqrt().to_bits() & 0x7ff0_0000_0000_0000);
    let inv = 1.0 / s;
    let a = x.mul_pwr2(inv).mul_pwr2(inv);
    let mut r = OD::from_f64(1.0 / a.x[0].sqrt());
    let h = a.mul_pwr2(0.5);
    for _ in 0..4 {
        r = r + (-(h * (r * r))).add_f(0.5) * r;
    }
    (r * a).mul_pwr2(s)
}

/// |r^2 - a| / (2 a) in units of u^8 = 2^-424
fn err(r: OD, a: OD) -> f64 {
    let (re, ae) = (r.exact(), a.exact());
    re.mul(&re).sub(&ae).abs().ratio(&ae.ldexp(1)) / 2f64.powi(-424)
}

fn ulp(x: f64) -> f64 {
    f64::from_bits(x.abs().to_bits() + 1) - x.abs()
}

/// a value on the ladder H(2): each part m ulp of the part above, m by kind
fn input(r: &mut Rng, kind: usize) -> OD {
    let e = (r.next_u64() % 41) as i32 - 20;
    let mut x = [0.0; 8];
    x[0] = (1.0 + r.unit()) * 2f64.powi(e);
    if kind == 3 {
        // just above a power of four, where the double-double root's error is largest
        x[0] = (1.0 + r.unit() * 2f64.powi(-((r.next_u64() % 40) as i32) - 1)) * 4f64.powi(e / 2);
    }
    for i in 1..8 {
        let m = match kind {
            // greedy-like: up to half an ulp
            0 => 0.5 * r.unit(),
            // the top of the ladder: half an ulp to an ulp
            1 | 3 => 0.5 + 0.5 * r.unit(),
            // a whole ulp, or nearly
            _ => 1.0 - r.unit() * 2f64.powi(-((r.next_u64() % 50) as i32)),
        };
        let sgn = if r.next_u64() & 1 == 0 { 1.0 } else { -1.0 };
        x[i] = sgn * m * ulp(x[i - 1]);
        if x[i] == 0.0 {
            break;
        }
    }
    OD { x }
}

fn same(a: OD, b: OD) -> bool {
    a.x.iter().zip(b.x.iter()).all(|(x, y)| x.to_bits() == y.to_bits() || (x.is_nan() && y.is_nan()))
}

#[test]
fn worst_error_against_proven_bound() {
    let n: usize = std::env::var("FABLE_N").ok().and_then(|v| v.parse().ok()).unwrap_or(40_000);
    for kind in 0..4 {
        let mut r = Rng(0x0d5 + kind as u64);
        let (mut wn, mut wo, mut wa) = (0.0f64, 0.0f64, OD::from_f64(0.0));
        let mut differ = 0;
        for _ in 0..n {
            let a = input(&mut r, kind);
            let (new, old) = (a.sqrt(), sqrt_newton4(a));
            differ += !same(new, old) as usize;
            let (en, eo) = (err(new, a), err(old, a));
            if en > wn {
                (wn, wa) = (en, a);
            }
            wo = wo.max(eo);
        }
        println!(
            "kind {kind}: n {n}: worst new {wn:.4} u^8 at {:x?}; worst old {wo:.4} u^8; bits differ on {differ}",
            wa.x.map(f64::to_bits)
        );
        // Theorem 22 at theta = 2, as the test measure |z^2 - x| / (2 x) <= delta + delta^2 / 2
        assert!(wn <= 3.0000319 * (1.0 + 1e-12), "past the proven bound");
    }
}

#[test]
fn lanes_match_scalar() {
    let mut r = Rng(79);
    for round in 0..20_000 {
        let a: [OD; 8] = std::array::from_fn(|l| {
            let q = input(&mut r, (round + l) % 4);
            if r.next_u64() % 50 == 0 {
                OD::from_f64(0.0)
            } else {
                q
            }
        });
        let got = OV::from_lanes(&a).sqrt().lanes();
        for l in 0..8 {
            assert!(same(got[l], a[l].sqrt()), "lane {l}: sqrt {:?} = {:?}, scalar {:?}", a[l], got[l], a[l].sqrt());
        }
    }
}

#[test]
fn special_values() {
    let q = |x: &[f64]| {
        let mut p = [0.0; 8];
        p[..x.len()].copy_from_slice(x);
        OD { x: p }
    };
    let cases = [
        q(&[0.0]),
        q(&[-0.0]),
        q(&[-1.0]),
        q(&[-4.0, 1e-20]),
        q(&[f64::INFINITY]),
        q(&[f64::NEG_INFINITY]),
        q(&[f64::NAN]),
        q(&[5e-324]),
        q(&[1e-310]),
        q(&[f64::MIN_POSITIVE]),
        q(&[f64::MAX, f64::MAX * 2f64.powi(-54), f64::MAX * 2f64.powi(-108), f64::MAX * 2f64.powi(-162)]),
        q(&[4.0, -2f64.powi(-52)]),
        q(&[1.0, -2f64.powi(-53)]),
        q(&[1.0]),
        q(&[4.0]),
        // a_1 a whole ulp of a_0, which the quick two-sum folds into a_0
        q(&[1.0, 2f64.powi(-52), 2f64.powi(-104)]),
        q(&[4.0 - 2f64.powi(-50), 2f64.powi(-51) - 2f64.powi(-104)]),
        // a_1 above a_0: out of magnitude order
        q(&[1.0, 3.0]),
        q(&[2f64.powi(-600), 2f64.powi(-653)]),
    ];
    for a in cases {
        let (new, old) = (a.sqrt(), sqrt_newton4(a));
        let lanes = OV::from_lanes(&[a; 8]).sqrt().lanes();
        let pos = a.x[0] > 0.0 && a.x.iter().all(|v| v.is_finite());
        let (en, eo) = if pos { (err(new, a), err(old, a)) } else { (f64::NAN, f64::NAN) };
        println!(
            "sqrt {:?}:\n  new {:?} err {en:.3e} u^8\n  old {:?} err {eo:.3e} u^8\n  lanes same as scalar {}",
            a.x,
            new.x,
            old.x,
            lanes.iter().all(|&l| same(l, new))
        );
    }
}

/// The gap case that #79 replaces: within its threshold with and without the mutation?
#[cfg(feature = "mutate")]
#[test]
fn old_gap_case_under_renorm_fast() {
    use multidouble::od::mutate;
    let od = |h: [u64; 8]| OD { x: h.map(f64::from_bits) };
    let old_case = od([0x3ff97f22dc331771, 0x320e700ef097bbfd, 0, 0, 0, 0, 0, 0]);
    let new_case = od([
        0x3ff93b4a66f163b7,
        0x30a0f22c361cefdc,
        0,
        0x1e0c251714b46fe7,
        0,
        0x0bc7e97fd3b29241,
        0x885f41d74c3832f1,
        0x84f56713803b93f1,
    ]);
    for (name, a) in [("old case", old_case), ("new case", new_case)] {
        let plain = a.sqrt();
        mutate::set(mutate::RENORM_FAST);
        let fast = a.sqrt();
        mutate::set(0);
        // units of 2^-418 as od_tests: 64 u^8
        println!(
            "{name}: err {:.4e} units of 2^-418, with RENORM_FAST {:.4e} units; H(2) ladder: {}",
            err(plain, a) / 64.0,
            err(fast, a) / 64.0,
            (1..8).all(|i| a.x[i].abs() <= 2f64.powi(-52 * i as i32) * a.x[0].abs())
        );
    }
}
