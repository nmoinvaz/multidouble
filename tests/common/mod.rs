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

/// FNV-1a over the words
pub fn fnv(words: &[u64]) -> u64 {
    words.iter().fold(0xcbf2_9ce4_8422_2325, |h, &w| {
        (h ^ w).wrapping_mul(0x0000_0100_0000_01b3)
    })
}

/// Outputs pinned bit for bit, so that a change of rounding anywhere in them fails. Group i's words
/// (the bits of its outputs) must hash (`fnv`) to `want[i]`. Control: the same outputs from inputs
/// with one bit flipped (`nudged[i]`) hash otherwise, so the group depends on that bit.
/// No word may be a NaN's: x86 and ARM give NaNs different bits, and the pins hold on both.
pub fn assert_pinned(names: &[&str], words: &[Vec<u64>], nudged: &[Vec<u64>], want: &[u64]) {
    let bad = pin_mismatches(names, words, nudged, want);
    assert!(bad.is_empty(), "{bad:?}");
}

/// `assert_pinned`'s groups that differ from their pins, as messages (the other checks panic)
pub fn pin_mismatches(names: &[&str], words: &[Vec<u64>], nudged: &[Vec<u64>], want: &[u64]) -> Vec<String> {
    assert!(names.len() == words.len() && names.len() == nudged.len() && names.len() == want.len());
    let mut bad = Vec::new();
    for i in 0..names.len() {
        assert!(!words[i].is_empty(), "{}: no outputs", names[i]);
        assert!(
            words[i].iter().all(|&w| !f64::from_bits(w).is_nan()),
            "{}: a NaN output",
            names[i]
        );
        let h = fnv(&words[i]);
        if h != want[i] {
            bad.push(format!("{}: {:#018x} pinned {:#018x}", names[i], h, want[i]));
        }
        assert!(
            fnv(&nudged[i]) != h,
            "control: {} does not depend on the nudged input",
            names[i]
        );
    }
    bad
}

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
