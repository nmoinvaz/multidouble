//! The time of a square of a relaxed product, s x s terms into 2s - 1 accumulators, term by term and by
//! `Lane::block_mul` (`series::mullow` on DV, QV, OV and Du), for sides s = 8 to 4096 on one thread; the crossover is
//! each lane's `Lane::BLOCK_MIN`. The coefficients fall as 2^(-0.02 i), each within 2^+-2 of that, with random signs
//! and full-width parts, as the coefficients of a series summed near its radius of convergence do.
//!
//! ```text
//! cargo run --release --example series_squares [-- --max 4096]
//! ```
use multidouble::dd::DD;
use multidouble::dual::Lane;
use multidouble::native::{Du, DV, OV, QV, V8};
use multidouble::od::OD;
use std::time::Instant;

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    fn unit(&mut self) -> f64 {
        (self.next() >> 11) as f64 * (1.0 / (1u64 << 53) as f64)
    }
    /// an octo-double of magnitude about 2^e, random sign, all parts in use
    fn od(&mut self, e: f64) -> OD {
        let mut x = [0.0f64; 8];
        x[0] = if self.next() & 1 == 0 { 1.0 } else { -1.0 } * (1.0 + self.unit()) * e.exp2();
        for j in 1..8 {
            x[j] = (self.unit() - 0.5) * x[j - 1].abs() * (-52.0f64).exp2();
        }
        OD::new(x)
    }
}

/// a lane built from 8 octo-doubles (rounded to the lane's parts)
trait Make: Lane {
    fn make(x: &[OD; 8], t: &[OD; 8]) -> Self;
}
impl Make for OV {
    fn make(x: &[OD; 8], _t: &[OD; 8]) -> Self {
        OV::from_lanes(x)
    }
}
impl Make for QV {
    fn make(x: &[OD; 8], _t: &[OD; 8]) -> Self {
        OV::from_lanes(x).to_qv()
    }
}
impl Make for DV {
    fn make(x: &[OD; 8], _t: &[OD; 8]) -> Self {
        OV::from_lanes(x).to_dv()
    }
}
impl Make for Du {
    fn make(x: &[OD; 8], t: &[OD; 8]) -> Self {
        Du {
            v: OV::from_lanes(x).to_dv(),
            d: OV::from_lanes(t).to_dv(),
        }
    }
}

fn series<T: Make>(r: &mut Rng, n: usize, off: usize) -> Vec<T> {
    (0..n)
        .map(|i| {
            let e = -0.02 * (i + off) as f64;
            let x: [OD; 8] = std::array::from_fn(|_| {
                let u = 4.0 * (r.unit() - 0.5);
                r.od(e + u)
            });
            let t: [OD; 8] = std::array::from_fn(|_| {
                let u = 4.0 * (r.unit() - 0.5);
                r.od(e - 3.0 + u)
            });
            T::make(&x, &t)
        })
        .collect()
}

/// seconds per square, term by term and by block_mul, the best of reps
fn time<T: Make>(s: usize, reps: usize) -> (f64, f64, f64) {
    let mut r = Rng(s as u64);
    let (x, y) = (series::<T>(&mut r, s, s), series::<T>(&mut r, s, 2 * s));
    let n = 2 * s - 1;
    let (mut tn, mut tf) = (f64::INFINITY, f64::INFINITY);
    let mut sink = 0.0;
    for _ in 0..reps {
        let mut acc = vec![T::acc0(); n];
        let t0 = Instant::now();
        for (k, a) in acc.iter_mut().enumerate() {
            for i in k.saturating_sub(s - 1)..s.min(k + 1) {
                T::acc_mut(a, &x[i], &y[k - i]);
            }
        }
        tn = tn.min(t0.elapsed().as_secs_f64());
        sink += T::fin(acc[s]).val().hi.to_array()[0];
        let mut acc = vec![T::acc0(); n];
        let t0 = Instant::now();
        T::block_mul(&x, &y, &mut acc);
        tf = tf.min(t0.elapsed().as_secs_f64());
        sink += T::fin(acc[s]).val().hi.to_array()[0];
    }
    (tn, tf, sink)
}

fn row<T: Make>(name: &str, max: usize) {
    let mut s = 8;
    let mut line = format!("{name:3} (BLOCK_MIN {:4}):", T::BLOCK_MIN);
    while s <= max {
        let reps = (4_000_000 / (s * s)).clamp(1, 50);
        let (tn, tf, sink) = time::<T>(s, reps);
        assert!(sink.is_finite());
        line += &format!("  {s}: {:.3}/{:.3} ms {:.2}x", tn * 1e3, tf * 1e3, tn / tf);
        s *= 2;
    }
    println!("{line}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let max = args
        .iter()
        .position(|a| a == "--max")
        .map(|i| args[i + 1].parse().unwrap())
        .unwrap_or(4096);
    let _ = (DD::ONE, V8::zero());
    println!("a square of side s, s^2 terms: term by term / block_mul, ms, and their ratio (one thread)");
    row::<DV>("DV", max);
    row::<Du>("Du", max);
    row::<QV>("QV", max);
    row::<OV>("OV", max);
}
