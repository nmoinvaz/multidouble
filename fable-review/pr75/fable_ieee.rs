//! Review check for the queue form of `QV::ieee_add`: every lane against `QD::ieee_add` bit for bit on inputs that
//! reach each exit of the merge (all parts read with k = 0..3 emitted, four emitted with 0..n parts unread), with
//! the exits mixed across the lanes of one call.
mod common;
use common::Rng;
use multidouble::qd::QD;
use multidouble::qv::QV;
use multidouble::simd::{self, Kernel, Simd};

fn two_sum(a: f64, b: f64) -> (f64, f64) {
    let s = a + b;
    let bb = s - a;
    (s, (a - (s - bb)) + (b - bb))
}

/// the exit of QD::ieee_add's merge: (k, parts not read), by a copy of its control flow
fn exit_of(a: [f64; 4], b: [f64; 4]) -> (usize, usize) {
    let gt = |x: f64, y: f64| x.abs() > y.abs();
    let (mut i, mut j, mut k) = (0usize, 0usize, 0usize);
    let (mut u, mut v);
    if gt(a[i], b[j]) {
        u = a[i];
        i += 1;
    } else {
        u = b[j];
        j += 1;
    }
    if gt(a[i], b[j]) {
        v = a[i];
        i += 1;
    } else {
        v = b[j];
        j += 1;
    }
    let s = u + v;
    v -= s - u;
    u = s;
    while k < 4 {
        if i >= 4 && j >= 4 {
            break;
        }
        let t;
        if i >= 4 {
            t = b[j];
            j += 1;
        } else if j >= 4 || gt(a[i], b[j]) {
            t = a[i];
            i += 1;
        } else {
            t = b[j];
            j += 1;
        }
        let (s, bb) = two_sum(v, t);
        let (s, aa) = two_sum(u, s);
        let (za, zb) = (aa != 0.0, bb != 0.0);
        let ret;
        if za && zb {
            ret = s;
            u = aa;
            v = bb;
        } else {
            ret = 0.0;
            u = s;
            v = if zb { bb } else { aa };
        }
        if ret != 0.0 {
            k += 1;
        }
    }
    (k, 8 - i - j)
}

/// parts of many shapes: normalized, with gaps, zero parts, overlapping, equal magnitudes, special values
fn parts(r: &mut Rng, kind: u64) -> [f64; 4] {
    let e0 = (r.next_u64() % 41) as i32 - 20;
    let m = |r: &mut Rng| (1.0 + r.unit()) * if r.next_u64() & 1 == 0 { 1.0 } else { -1.0 };
    let mut x = [0.0; 4];
    let mut e = e0;
    for p in x.iter_mut() {
        *p = m(r) * 2f64.powi(e);
        e -= match kind % 6 {
            0 => 53,
            1 => 53 + (r.next_u64() % 60) as i32,
            2 => (r.next_u64() % 54) as i32,
            3 => 0,
            4 => 54,
            _ => 53 + (r.next_u64() % 3) as i32,
        };
    }
    // zero parts, short significands, exact powers of two
    for p in x.iter_mut() {
        match r.next_u64() % 12 {
            0 => *p = 0.0,
            1 => *p = -0.0,
            2 => *p = f64::from_bits(p.to_bits() & !0xf_ffff_ffff),
            3 => *p = f64::from_bits(p.to_bits() & !0xf_ffff_ffff_ffff),
            _ => {}
        }
    }
    if kind % 97 == 0 {
        x[(r.next_u64() % 4) as usize] = [f64::NAN, f64::INFINITY, f64::NEG_INFINITY, 5e-324, 1e-310][(r.next_u64() % 5) as usize];
    }
    x
}

fn same(a: f64, b: f64) -> bool {
    a.to_bits() == b.to_bits() || (a.is_nan() && b.is_nan())
}

#[derive(Clone)]
struct Check;

impl Kernel for Check {
    type Output = [[u64; 8]; 5];
    #[inline(always)]
    fn run<S: Simd>(self) -> Self::Output {
        let mut r = Rng(0xfab1e);
        let mut seen = [[0u64; 8]; 5];
        for round in 0..400_000u64 {
            let mut a = [QD { x: [0.0; 4] }; 8];
            let mut b = a;
            for l in 0..8 {
                let kind = r.next_u64();
                a[l].x = parts(&mut r, kind);
                b[l].x = match r.next_u64() % 8 {
                    // b cancels a to a random depth
                    0 | 1 => {
                        let mut y = a[l].x.map(|p| -p);
                        let d = (r.next_u64() % 4) as usize;
                        y[d] = f64::from_bits(y[d].to_bits() ^ (1 << (r.next_u64() % 52)));
                        for p in y.iter_mut().skip(d + 1) {
                            if r.next_u64() & 1 == 0 {
                                *p = (1.0 + r.unit()) * p.abs().max(1e-300) * r.sym();
                            }
                        }
                        y
                    }
                    // a's parts again, shifted
                    2 => {
                        let s = 2f64.powi((r.next_u64() % 9) as i32 - 4);
                        a[l].x.map(|p| p * s)
                    }
                    3 => a[l].x,
                    _ => {
                        let k = r.next_u64();
                        parts(&mut r, k)
                    }
                };
            }
            let got = QV::<S>::from_lanes(&a).ieee_add(QV::from_lanes(&b)).lanes();
            for l in 0..8 {
                let want = a[l].ieee_add(b[l]);
                let (k, left) = exit_of(a[l].x, b[l].x);
                seen[k][left] += 1;
                assert!(
                    (0..4).all(|m| same(got[l].x[m], want.x[m])),
                    "{} round {round} lane {l} exit ({k}, {left}): {:?} + {:?} = {:?}, scalar {:?}",
                    S::NAME,
                    a[l].x,
                    b[l].x,
                    got[l].x,
                    want.x
                );
            }
        }
        seen
    }
}

#[test]
fn qv_ieee_add_matches_qd_on_every_exit() {
    for (name, seen) in simd::for_each_available(Check) {
        println!("{name}: exits (k emitted; columns parts unread 0..7)");
        for (k, row) in seen.iter().enumerate() {
            println!("  k {k}: {row:?}");
        }
        // every exit the merge has: all parts read with k = 0..3, and four emitted with 0..=2 unread (four emissions take six reads)
        for k in 0..4 {
            assert!(seen[k][0] > 0, "{name}: no case reads every part with {k} emitted");
        }
        for left in 0..=2 {
            assert!(seen[4][left] > 0, "{name}: no case emits four parts with {left} unread");
        }
    }
}
