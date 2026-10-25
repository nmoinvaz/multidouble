//! Error bounds against exact dyadic arithmetic (`multidouble::exact`) for what `tests/dd.rs` leaves out: the LU's
//! update `dd_axpy`, the lane dot accumulator `DotAcc`, `recip` and `mul_pwr2`, the double-double operations over
//! the whole exponent range where their bounds hold, and the LU solve's backward error and its forward error on
//! ill-conditioned matrices. Errors are in units of u^2 = 2^-106. Every check has a control: a deliberately wrong
//! result that must break it.
#![allow(clippy::needless_range_loop)]
mod common;
use common::{Rng, U2};
use multidouble::dd::{two_prod, two_sum, DD};
use multidouble::exact::Dy;
use multidouble::linalg::{dd_axpy, ld_for, DDLu};
use multidouble::native::{DotAcc, DV};

const N: usize = 20_000;

fn exact(x: DD) -> Dy {
    Dy::from_f64(x.hi).add(&Dy::from_f64(x.lo))
}

/// |got - want| / |scale| in units of u^2
fn err_u2(got: DD, want: &Dy, scale: &Dy) -> f64 {
    exact(got).sub(want).ratio(scale) / U2
}

fn normalized(x: DD) -> bool {
    x.hi + x.lo == x.hi
}

/// a normalized double-double with a random sign and an exponent in [emin, emax]
fn dd_in(r: &mut Rng, emin: i32, emax: i32) -> DD {
    let e = emin + (r.next_u64() % (emax - emin + 1) as u64) as i32;
    let hi = (1.0 + r.unit()) * 2f64.powi(e) * if r.next_u64() & 1 == 0 { 1.0 } else { -1.0 };
    let lo = r.sym() * hi.abs() * 2f64.powi(-53);
    DD::new(hi, lo)
}

// ---------------------------------------------------------------------------------------------------------------
// dd_axpy: a + l t, the update of every LU step and solve
// ---------------------------------------------------------------------------------------------------------------

/// `dd_axpy` without the cross term l.lo t.hi: the control
fn axpy_no_cross(a: DD, l: DD, nt: DD) -> DD {
    let (p, pe) = two_prod(l.hi, nt.hi);
    let pe = l.hi.mul_add(nt.lo, pe);
    let (s, t) = two_sum(a.hi, p);
    let e = a.lo + (t + pe);
    let (h, lo) = two_sum(s, e);
    DD { hi: h, lo }
}

/// |dd_axpy(a, l, t) - (a + l t)| / (|a| + |l t|): the product's error is relative to |l t|, not to the sum, so the
/// bound is the Cray-style one. Every fourth case nearly cancels (a = -l t to about 2^-60). The bound, 7 u^2: the
/// dropped l.lo t.lo is at most u^2 |l t|, and the two f64 additions that form e (t + pe, then a.lo + that) round
/// terms of at most u (|a| + 2 |s| + 2 |l t|), |s| <= |a| + |l t|, at u each.
fn axpy_worst(f: fn(DD, DD, DD) -> DD, seed: u64) -> f64 {
    let mut r = Rng(seed);
    let mut worst: f64 = 0.0;
    for i in 0..N {
        let (l, t) = (r.dd(20), r.dd(20));
        let lt = exact(l).mul(&exact(t));
        let a = if i % 4 == 0 {
            let p = -(l * t);
            DD::new(p.hi, p.lo + r.sym() * p.hi.abs() * 2f64.powi(-60))
        } else {
            r.dd(20)
        };
        let got = f(a, l, t);
        assert!(normalized(got), "dd_axpy({a:?}, {l:?}, {t:?}) = {got:?}");
        let want = exact(a).add(&lt);
        worst = worst.max(err_u2(got, &want, &exact(a).abs().add(&lt.abs())));
    }
    worst
}

#[test]
fn dd_axpy_within_bound() {
    let worst = axpy_worst(dd_axpy, 101);
    println!("dd_axpy: worst {worst:.3} u^2 of |a| + |l t| (bound 7)");
    assert!(worst <= 7.0, "dd_axpy: {worst} u^2");
    // control: without the cross term the error is about |l.lo t.hi| ~ 2^-53 |l t|
    let broken = axpy_worst(axpy_no_cross, 101);
    assert!(
        broken > 7.0,
        "control: dd_axpy without the cross term passes ({broken} u^2)"
    );
}

// ---------------------------------------------------------------------------------------------------------------
// DotAcc: sums of double-double products on 8 lanes
// ---------------------------------------------------------------------------------------------------------------

/// worst |sum - exact| / sum |a_i b_i| over 8-lane dot products of length len, in u^2. cat: "random" (exponents in
/// [-3, 3]), "wide" ([-60, 60]) or "cancel" (the second half of the terms cancels the first to about 2^-30 each).
/// drop_e: the control, which returns only the accumulator's leading sum.
fn dot_worst(len: usize, cat: &str, seed: u64, drop_e: bool) -> f64 {
    let mut r = Rng(seed);
    let mut worst: f64 = 0.0;
    for _ in 0..(4096 / len).max(16) {
        let mut a = vec![[DD::ZERO; 8]; len];
        let mut b = vec![[DD::ZERO; 8]; len];
        for lane in 0..8 {
            for i in 0..len {
                let (x, y) = match cat {
                    "wide" => (dd_in(&mut r, -60, 60), dd_in(&mut r, -60, 60)),
                    "cancel" if i >= len / 2 && len > 1 => {
                        // a_i b_i = -(a_k b_k) (1 + d), |d| ~ 2^-30
                        let k = i - len / 2;
                        let ak = a[k][lane];
                        let d = DD::from_f64(1.0 + r.sym() * 2f64.powi(-30));
                        (-(ak * d), b[k][lane])
                    }
                    _ => (dd_in(&mut r, -3, 3), dd_in(&mut r, -3, 3)),
                };
                a[i][lane] = x;
                b[i][lane] = y;
            }
        }
        let lanes = |v: &[DD; 8]| DV::load(&v.map(|d| d.hi), &v.map(|d| d.lo));
        let mut acc = DotAcc::zero();
        for i in 0..len {
            acc = acc.add_prod(lanes(&a[i]), lanes(&b[i]));
        }
        let got = if drop_e {
            DV {
                hi: acc.s,
                lo: multidouble::native::V8::zero(),
            }
        } else {
            acc.finish()
        };
        for lane in 0..8 {
            let (mut s, mut m) = (Dy::zero(), Dy::zero());
            for i in 0..len {
                let t = exact(a[i][lane]).mul(&exact(b[i][lane]));
                m = m.add(&t.abs());
                s = s.add(&t);
            }
            let g = got.lane(lane);
            if !drop_e {
                assert!(normalized(g), "DotAcc len {len} {cat}: {g:?} not normalized");
            }
            worst = worst.max(err_u2(g, &s, &m));
        }
    }
    worst
}

/// The accumulator adds each product's leading part with an error-free sum and the rest (the product's error and the
/// sums' errors) in plain f64, so its error stays below (len + 4) u^2 of sum |a_i b_i| (about one u per f64 addition
/// of terms of size u sum |a_i b_i|, plus the product's own few u^2).
#[test]
fn dot_acc_within_bound() {
    for (ci, cat) in ["random", "wide", "cancel"].into_iter().enumerate() {
        for len in [1usize, 2, 7, 16, 64, 256] {
            let seed = 200 + 10 * ci as u64 + len as u64;
            let thr = len as f64 + 4.0;
            let worst = dot_worst(len, cat, seed, false);
            println!("DotAcc {cat:6} len {len:3}: worst {worst:.3} u^2 of sum |a b| (bound {thr})");
            assert!(worst <= thr, "DotAcc {cat} len {len}: {worst} u^2 (bound {thr})");
            // control: the leading sum alone misses by about u = 2^53 u^2 (len 1: by the product's low part)
            let broken = dot_worst(len, cat, seed, true);
            assert!(
                broken > thr,
                "control: DotAcc without e passes {cat} len {len} ({broken} u^2)"
            );
        }
    }
}

// ---------------------------------------------------------------------------------------------------------------
// recip and mul_pwr2
// ---------------------------------------------------------------------------------------------------------------

/// 1 / b: the residual q b - 1, exactly, is the quotient's relative error to first order (as tests/dd.rs bounds div)
#[test]
fn recip_within_bound() {
    let mut r = Rng(301);
    let mut worst: f64 = 0.0;
    let mut caught = false;
    for _ in 0..N {
        let b = r.dd(20);
        let q = b.recip();
        assert!(normalized(q));
        let one = Dy::from_f64(1.0);
        let e = exact(q).mul(&exact(b)).sub(&one).ratio(&one) / U2;
        worst = worst.max(e);
        assert!(e <= 8.0, "recip({b:?}): {e} u^2");
        // control: the f64 reciprocal alone
        let c = DD::from_f64(1.0 / b.hi);
        caught |= exact(c).mul(&exact(b)).sub(&one).ratio(&one) / U2 > 8.0;
    }
    println!("recip: worst {worst:.3} u^2 (bound 8)");
    assert!(caught, "control: the f64 reciprocal passes the recip bound");
}

/// x 2^k is exact while the parts stay normal
#[test]
fn mul_pwr2_is_exact() {
    let mut r = Rng(302);
    for _ in 0..N {
        let x = r.dd(100);
        let k = (r.next_u64() % 401) as i32 - 200;
        let p = 2f64.powi(k);
        let got = x.mul_pwr2(p);
        let want = exact(x).mul(&Dy::from_f64(p));
        assert!(exact(got).sub(&want).is_zero(), "{x:?} * 2^{k} = {got:?}");
        assert_eq!(got.hi, x.hi * p);
        assert_eq!(got.lo, x.lo * p);
    }
    // control: the check above sees a one-ulp change in the low part
    let x = DD::new(1.5, 2f64.powi(-60));
    let off = DD::new(x.hi * 4.0, (x.lo * 4.0) * (1.0 + f64::EPSILON));
    assert!(!exact(off).sub(&exact(x).mul(&Dy::from_f64(4.0))).is_zero());
}

// ---------------------------------------------------------------------------------------------------------------
// the whole exponent range
// ---------------------------------------------------------------------------------------------------------------

/// tests/dd.rs's bounds (add and sub 3 u^2, mul 5, div 8) over the exponents where they hold: add and sub up to
/// 2^1000 and down to 2^-960 (the low parts stay normal), mul and div with operands in 2^[-450, 450], so the
/// products, quotients and their error terms (down to |a b| 2^-106) stay normal. Control: dropping the low parts
/// breaks every bound.
#[test]
fn bounds_hold_over_the_exponent_range() {
    let mut r = Rng(401);
    let (mut wa, mut wm, mut wd) = (0f64, 0f64, 0f64);
    let mut caught = [false; 3];
    for i in 0..N {
        let a = dd_in(&mut r, -960, 1000);
        let b = if i % 4 == 0 {
            DD::new(-a.hi, r.sym() * a.hi.abs() * 2f64.powi(-60))
        } else {
            let e = a.hi.abs().log2() as i32;
            dd_in(&mut r, (e - 60).max(-960), (e + 60).min(1000))
        };
        let want = exact(a).add(&exact(b));
        let got = a + b;
        assert!(normalized(got));
        let e = err_u2(got, &want, &want);
        wa = wa.max(e);
        assert!(e <= 3.0, "{a:?} + {b:?}: {e} u^2");
        caught[0] |= err_u2(DD::from_f64(a.hi + b.hi), &want, &want) > 3.0;

        let (a, b) = (dd_in(&mut r, -450, 450), dd_in(&mut r, -450, 450));
        let want = exact(a).mul(&exact(b));
        let got = a * b;
        assert!(normalized(got));
        let e = err_u2(got, &want, &want);
        wm = wm.max(e);
        assert!(e <= 5.0, "{a:?} * {b:?}: {e} u^2");
        caught[1] |= err_u2(DD::from_f64(a.hi * b.hi), &want, &want) > 5.0;

        let q = a / b;
        assert!(normalized(q));
        let res = |q: DD| exact(q).mul(&exact(b)).sub(&exact(a)).ratio(&exact(a)) / U2;
        let e = res(q);
        wd = wd.max(e);
        assert!(e <= 8.0, "{a:?} / {b:?}: {e} u^2");
        caught[2] |= res(DD::from_f64(a.hi / b.hi)) > 8.0;
    }
    println!("exponent range: add/sub {wa:.3}, mul {wm:.3}, div {wd:.3} u^2 (bounds 3, 5, 8)");
    assert_eq!(caught, [true; 3], "controls (f64 add, mul, div) pass the bounds");
}

// ---------------------------------------------------------------------------------------------------------------
// the LU solve
// ---------------------------------------------------------------------------------------------------------------

/// column-major n x n with leading dimension ld_for(n), from entry(i, j)
fn dd_matrix(n: usize, mut entry: impl FnMut(usize, usize) -> DD) -> (usize, Vec<f64>, Vec<f64>) {
    let ld = ld_for(n);
    let (mut hi, mut lo) = (vec![0.0; ld * n], vec![0.0; ld * n]);
    for j in 0..n {
        for i in 0..n {
            let v = entry(i, j);
            hi[j * ld + i] = v.hi;
            lo[j * ld + i] = v.lo;
        }
    }
    (ld, hi, lo)
}

/// max_i |b - A x|_i / (|A| |x| + |b|)_i, exactly: the componentwise backward error of x
fn backward_error(n: usize, ld: usize, hi: &[f64], lo: &[f64], x: &[DD], b: &[DD]) -> f64 {
    let mut worst: f64 = 0.0;
    for i in 0..n {
        let (mut res, mut scale) = (exact(b[i]), exact(b[i]).abs());
        for j in 0..n {
            let t = exact(DD::new(hi[j * ld + i], lo[j * ld + i])).mul(&exact(x[j]));
            scale = scale.add(&t.abs());
            res = res.sub(&t);
        }
        worst = worst.max(res.ratio(&scale));
    }
    worst
}

/// The solve of the LU with partial pivoting is backward stable: on random matrices (no diagonal shift, so pivoting
/// matters) its componentwise backward error stays below n u^2 (Higham, ch. 9, with the small growth factors random
/// matrices have). Control: a factor with one pivot perturbed by 2^-80 relative breaks the bound.
#[test]
fn solve_is_backward_stable() {
    let mut r = Rng(501);
    for n in [3usize, 8, 31, 64, 100] {
        let (ld, hi, lo) = dd_matrix(n, |_, _| DD::new(r.sym(), r.sym() * 1e-17));
        let b: Vec<DD> = (0..n).map(|_| DD::new(r.sym(), r.sym() * 1e-17)).collect();
        let lu = DDLu::factor(n, ld, hi.clone(), lo.clone(), false).unwrap();
        let mut x = b.clone();
        lu.solve(&mut x);
        let e = backward_error(n, ld, &hi, &lo, &x, &b) / U2;
        println!("solve n {n:3}: backward error {e:.3} u^2 (bound n = {n})");
        assert!(e <= n as f64, "n {n}: backward error {e} u^2");

        let mut bad = lu.clone();
        let k = n / 2;
        bad.lo[k * ld + k] += bad.hi[k * ld + k].abs() * 2f64.powi(-80);
        let mut x = b.clone();
        bad.solve(&mut x);
        let e = backward_error(n, ld, &hi, &lo, &x, &b) / U2;
        assert!(e > n as f64, "control: perturbed pivot passes n {n} ({e} u^2)");
    }
}

/// The Hilbert matrix (entries 1 / (i + j + 1) rounded to double-double), the classic ill-conditioned case: with x
/// chosen and b = A x formed exactly and rounded, the forward error |x^ - x| / |x| (max norms) stays below
/// n cond(A) u^2, cond(A) the max-norm condition number of the rounded matrix (computed from its inverse by the same
/// solves; accurate to a few digits while cond(A) u^2 is below about 1e-8, so n up to 13). Control: a pivot
/// perturbed by 2^-60 relative (which moves x by about that much) misses the bound wherever the bound is below 1e-22.
#[test]
fn hilbert_forward_error_within_cond_bound() {
    let mut r = Rng(502);
    for n in [2usize, 4, 6, 8, 10, 12, 13] {
        let (ld, hi, lo) = dd_matrix(n, |i, j| DD::ONE / DD::from_f64((i + j + 1) as f64));
        let lu = DDLu::factor(n, ld, hi.clone(), lo.clone(), false).unwrap();
        // max-norm condition number
        let a_norm = (0..n)
            .map(|i| (0..n).map(|j| (hi[j * ld + i] + lo[j * ld + i]).abs()).sum::<f64>())
            .fold(0.0, f64::max);
        let mut rows = vec![0.0f64; n];
        for j in 0..n {
            let mut e = vec![DD::ZERO; n];
            e[j] = DD::ONE;
            lu.solve(&mut e);
            for i in 0..n {
                rows[i] += e[i].to_f64().abs();
            }
        }
        let cond = a_norm * rows.iter().fold(0.0f64, |m, &v| m.max(v));
        let x: Vec<DD> = (0..n).map(|_| DD::new(r.sym(), r.sym() * 1e-17)).collect();
        let b: Vec<DD> = (0..n)
            .map(|i| {
                let mut s = Dy::zero();
                for j in 0..n {
                    s = s.add(&exact(DD::new(hi[j * ld + i], lo[j * ld + i])).mul(&exact(x[j])));
                }
                let h = s.to_f64();
                DD::new(h, s.sub(&Dy::from_f64(h)).to_f64())
            })
            .collect();
        let fwd = |lu: &DDLu| {
            let mut y = b.clone();
            lu.solve(&mut y);
            let xn = x.iter().map(|v| v.hi.abs()).fold(0.0, f64::max);
            (0..n).map(|i| (y[i] - x[i]).to_f64().abs()).fold(0.0, f64::max) / xn
        };
        let bound = n as f64 * cond * U2;
        let e = fwd(&lu);
        println!(
            "Hilbert n {n:2}: cond {cond:.2e}, forward error {e:.2e} = {:.3} of the bound n cond u^2",
            e / bound
        );
        assert!(e <= bound, "Hilbert n {n}: forward error {e:e} above {bound:e}");
        if bound < 1e-22 {
            let mut bad = lu.clone();
            let k = n / 2;
            bad.lo[k * ld + k] += bad.hi[k * ld + k].abs() * 2f64.powi(-60);
            let e = fwd(&bad);
            assert!(e > bound, "control: perturbed pivot passes Hilbert n {n} ({e:e})");
        }
    }
}
