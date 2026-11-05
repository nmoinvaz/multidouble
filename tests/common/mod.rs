//! Deterministic inputs for the tests: splitmix64, and double-double values with random exponents and full-width low
//! parts.
#![allow(dead_code)]
use multidouble::dd::DD;

pub struct Rng(pub u64);

impl Rng {
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    /// uniform in [0, 1)
    pub fn unit(&mut self) -> f64 {
        (self.next_u64() >> 11) as f64 * (1.0 / (1u64 << 53) as f64)
    }
    /// uniform in [-1, 1)
    pub fn sym(&mut self) -> f64 {
        2.0 * self.unit() - 1.0
    }
    /// a normalized double-double with a random sign and an exponent in [-emax, emax]
    pub fn dd(&mut self, emax: i32) -> DD {
        let e = (self.next_u64() % (2 * emax as u64 + 1)) as i32 - emax;
        let hi = (1.0 + self.unit()) * 2f64.powi(e) * if self.next_u64() & 1 == 0 { 1.0 } else { -1.0 };
        let lo = self.sym() * hi.abs() * 2f64.powi(-53);
        DD::new(hi, lo)
    }
}

/// u^2 = 2^-106, the unit of double-double error bounds
pub const U2: f64 = 1.232_595_164_407_831e-32;

/// f run on a thread with a 64 MiB stack, its panic passed on. Built without optimization (the coverage run) every
/// temporary has its own stack slot, and those of the octo-double jets' fields and accumulators can overflow a test
/// thread's 2 MiB.
pub fn big_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(f)
        .expect("a thread for the check")
        .join()
        .unwrap_or_else(|e| std::panic::resume_unwind(e))
}
