//! Exact arithmetic on dyadic rationals ±m·2^e (m an unsigned big integer) and on m / 10^k, with no dependency.
//!
//! Used by `qd` for decimal parsing (the exact decimal value, then the four components by greedy round-to-nearest) and
//! printing (the exact decimal expansion of the four-component sum, correctly rounded to the digits asked for), and by
//! the quad-double tests as their error-free reference. Nothing here is on a hot path; clarity over speed.
use std::cmp::Ordering;

/// Unsigned big integer, little-endian 64-bit limbs, no high zero limbs.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct BigU(pub Vec<u64>);

impl BigU {
    pub fn zero() -> BigU {
        BigU(Vec::new())
    }
    pub fn from_u64(x: u64) -> BigU {
        let mut r = BigU(vec![x]);
        r.trim();
        r
    }
    fn trim(&mut self) {
        while self.0.last() == Some(&0) {
            self.0.pop();
        }
    }
    pub fn is_zero(&self) -> bool {
        self.0.is_empty()
    }
    /// number of significant bits (0 for zero)
    pub fn bits(&self) -> u64 {
        match self.0.last() {
            None => 0,
            Some(&t) => 64 * (self.0.len() as u64 - 1) + (64 - t.leading_zeros() as u64),
        }
    }
    pub fn bit(&self, i: u64) -> bool {
        let (w, b) = ((i / 64) as usize, i % 64);
        w < self.0.len() && (self.0[w] >> b) & 1 == 1
    }
    /// any of the bits below bit n set
    pub fn any_below(&self, n: u64) -> bool {
        let (w, b) = ((n / 64) as usize, n % 64);
        for k in 0..w.min(self.0.len()) {
            if self.0[k] != 0 {
                return true;
            }
        }
        w < self.0.len() && b > 0 && (self.0[w] & ((1u64 << b) - 1)) != 0
    }
    pub fn shl(&self, n: u64) -> BigU {
        if self.is_zero() {
            return BigU::zero();
        }
        let (w, b) = ((n / 64) as usize, n % 64);
        let mut r = vec![0u64; w];
        if b == 0 {
            r.extend_from_slice(&self.0);
        } else {
            let mut carry = 0u64;
            for &x in &self.0 {
                r.push((x << b) | carry);
                carry = x >> (64 - b);
            }
            r.push(carry);
        }
        let mut r = BigU(r);
        r.trim();
        r
    }
    /// floor(self / 2^n)
    pub fn shr(&self, n: u64) -> BigU {
        let (w, b) = ((n / 64) as usize, n % 64);
        if w >= self.0.len() {
            return BigU::zero();
        }
        let s = &self.0[w..];
        let mut r = Vec::with_capacity(s.len());
        for k in 0..s.len() {
            let lo = s[k] >> b;
            let hi = if b > 0 && k + 1 < s.len() {
                s[k + 1] << (64 - b)
            } else {
                0
            };
            r.push(lo | hi);
        }
        let mut r = BigU(r);
        r.trim();
        r
    }
    pub fn cmp(&self, o: &BigU) -> Ordering {
        if self.0.len() != o.0.len() {
            return self.0.len().cmp(&o.0.len());
        }
        for k in (0..self.0.len()).rev() {
            if self.0[k] != o.0[k] {
                return self.0[k].cmp(&o.0[k]);
            }
        }
        Ordering::Equal
    }
    pub fn add(&self, o: &BigU) -> BigU {
        let n = self.0.len().max(o.0.len());
        let mut r = Vec::with_capacity(n + 1);
        let mut carry = 0u128;
        for k in 0..n {
            let s = *self.0.get(k).unwrap_or(&0) as u128 + *o.0.get(k).unwrap_or(&0) as u128 + carry;
            r.push(s as u64);
            carry = s >> 64;
        }
        r.push(carry as u64);
        let mut r = BigU(r);
        r.trim();
        r
    }
    /// self - o, requires self >= o
    pub fn sub(&self, o: &BigU) -> BigU {
        assert!(self.cmp(o) != Ordering::Less);
        let mut r = Vec::with_capacity(self.0.len());
        let mut borrow = 0i128;
        for k in 0..self.0.len() {
            let mut d = self.0[k] as i128 - *o.0.get(k).unwrap_or(&0) as i128 - borrow;
            borrow = 0;
            if d < 0 {
                d += 1i128 << 64;
                borrow = 1;
            }
            r.push(d as u64);
        }
        let mut r = BigU(r);
        r.trim();
        r
    }
    pub fn mul(&self, o: &BigU) -> BigU {
        if self.is_zero() || o.is_zero() {
            return BigU::zero();
        }
        let mut r = vec![0u64; self.0.len() + o.0.len()];
        for (i, &a) in self.0.iter().enumerate() {
            let mut carry = 0u128;
            for (j, &b) in o.0.iter().enumerate() {
                let t = a as u128 * b as u128 + r[i + j] as u128 + carry;
                r[i + j] = t as u64;
                carry = t >> 64;
            }
            r[i + o.0.len()] = carry as u64;
        }
        let mut r = BigU(r);
        r.trim();
        r
    }
    pub fn mul_small(&self, k: u64) -> BigU {
        self.mul(&BigU::from_u64(k))
    }
    /// (floor(self / d), self mod d), d > 0
    pub fn divrem_small(&self, d: u64) -> (BigU, u64) {
        assert!(d > 0);
        let mut q = vec![0u64; self.0.len()];
        let mut rem = 0u128;
        for k in (0..self.0.len()).rev() {
            let cur = (rem << 64) | self.0[k] as u128;
            q[k] = (cur / d as u128) as u64;
            rem = cur % d as u128;
        }
        let mut q = BigU(q);
        q.trim();
        (q, rem as u64)
    }
    pub fn pow_small(b: u64, mut n: u64) -> BigU {
        let mut r = BigU::from_u64(1);
        let mut p = BigU::from_u64(b);
        while n > 0 {
            if n & 1 == 1 {
                r = r.mul(&p);
            }
            n >>= 1;
            if n > 0 {
                p = p.mul(&p);
            }
        }
        r
    }
    /// (floor(self / 10^k), remainder != 0)
    pub fn div_pow10(&self, mut k: u64) -> (BigU, bool) {
        let mut q = self.clone();
        let mut sticky = false;
        while k > 0 {
            let s = k.min(19);
            let (qq, r) = q.divrem_small(10u64.pow(s as u32));
            q = qq;
            sticky |= r != 0;
            k -= s;
        }
        (q, sticky)
    }
    /// decimal digits ("0" for zero)
    pub fn to_dec(&self) -> String {
        if self.is_zero() {
            return "0".into();
        }
        let mut chunks = Vec::new();
        let mut q = self.clone();
        while !q.is_zero() {
            let (qq, r) = q.divrem_small(10_000_000_000_000_000_000);
            chunks.push(r);
            q = qq;
        }
        let mut s = format!("{}", chunks.last().unwrap());
        for c in chunks.iter().rev().skip(1) {
            s += &format!("{c:019}");
        }
        s
    }
    /// from a string of decimal digits
    pub fn from_dec(d: &str) -> BigU {
        let mut r = BigU::zero();
        for c in d.as_bytes().chunks(19) {
            let s = std::str::from_utf8(c).unwrap();
            r = r
                .mul_small(10u64.pow(c.len() as u32))
                .add(&BigU::from_u64(s.parse::<u64>().unwrap()));
        }
        r
    }
}

/// q·2^k for q < 2^54 when the result is exactly representable (or overflows to infinity)
fn ldexp_exact(q: u64, k: i64) -> f64 {
    if q == 0 {
        return 0.0;
    }
    let s = 53 - (64 - q.leading_zeros() as i64); // shift to put the leading bit at bit 52 (may be -1)
    let (q, k) = if s >= 0 { (q << s, k - s) } else { (q >> 1, k + 1) };
    let lead = k + 52;
    if lead > 1023 {
        return f64::INFINITY;
    }
    if lead >= -1022 {
        return f64::from_bits((((lead + 1023) as u64) << 52) | (q & ((1u64 << 52) - 1)));
    }
    // subnormal: q·2^k = (q >> (-1074 - k))·2^-1074, exact by assumption
    let sh = -1074 - k;
    if sh >= 64 {
        return 0.0;
    }
    f64::from_bits(q >> sh)
}

/// Round-to-nearest-even of m·2^e (+ a positive amount below 2^e if sticky) to f64, with subnormals and overflow.
pub fn round_to_f64(m: &BigU, e: i64, sticky: bool) -> f64 {
    let l = m.bits() as i64;
    if l == 0 {
        return 0.0;
    }
    let lead = e + l - 1;
    if lead > 1023 {
        return f64::INFINITY;
    }
    // bits of precision available at this exponent
    let p = if lead >= -1022 { 53 } else { lead + 1075 };
    let drop = l - p;
    // with no bits dropped a sticky amount could exceed half an ulp: callers pass enough bits
    assert!(!sticky || drop > 0, "round_to_f64: sticky with an exact mantissa");
    let (q, k) = if drop <= 0 {
        (m.0[0] << (-drop) as u64, e + drop) // exact (l <= p <= 53)
    } else {
        let d = drop as u64;
        let q = m.shr(d);
        let q = if q.is_zero() { 0 } else { q.0[0] };
        let half = m.bit(d - 1);
        let rest = sticky || m.any_below(d - 1);
        let up = half && (rest || q & 1 == 1);
        (q + up as u64, e + drop)
    };
    ldexp_exact(q, k)
}

/// Signed dyadic rational (-1)^neg · m · 2^e.
#[derive(Clone, Debug, Default)]
pub struct Dy {
    pub neg: bool,
    pub m: BigU,
    pub e: i64,
}

impl Dy {
    pub fn zero() -> Dy {
        Dy::default()
    }
    pub fn is_zero(&self) -> bool {
        self.m.is_zero()
    }
    /// exact value of a finite f64
    pub fn from_f64(x: f64) -> Dy {
        assert!(x.is_finite(), "Dy::from_f64({x})");
        let b = x.to_bits();
        let neg = b >> 63 == 1;
        let ex = ((b >> 52) & 0x7ff) as i64;
        let fr = b & ((1u64 << 52) - 1);
        let (m, e) = if ex == 0 {
            (fr, -1074)
        } else {
            (fr | (1u64 << 52), ex - 1075)
        };
        Dy {
            neg: neg && m != 0,
            m: BigU::from_u64(m),
            e,
        }
    }
    /// exact sum of finite f64
    pub fn sum(xs: &[f64]) -> Dy {
        xs.iter().fold(Dy::zero(), |a, &x| a.add(&Dy::from_f64(x)))
    }
    pub fn neg(&self) -> Dy {
        Dy {
            neg: !self.neg && !self.is_zero(),
            m: self.m.clone(),
            e: self.e,
        }
    }
    pub fn abs(&self) -> Dy {
        Dy {
            neg: false,
            m: self.m.clone(),
            e: self.e,
        }
    }
    fn align(&self, o: &Dy) -> (BigU, BigU, i64) {
        let e = self.e.min(o.e);
        (self.m.shl((self.e - e) as u64), o.m.shl((o.e - e) as u64), e)
    }
    pub fn add(&self, o: &Dy) -> Dy {
        if self.is_zero() {
            return o.clone();
        }
        if o.is_zero() {
            return self.clone();
        }
        let (a, b, e) = self.align(o);
        if self.neg == o.neg {
            return Dy {
                neg: self.neg,
                m: a.add(&b),
                e,
            };
        }
        match a.cmp(&b) {
            Ordering::Equal => Dy::zero(),
            Ordering::Greater => Dy {
                neg: self.neg,
                m: a.sub(&b),
                e,
            },
            Ordering::Less => Dy {
                neg: o.neg,
                m: b.sub(&a),
                e,
            },
        }
    }
    pub fn sub(&self, o: &Dy) -> Dy {
        self.add(&o.neg())
    }
    pub fn mul(&self, o: &Dy) -> Dy {
        let m = self.m.mul(&o.m);
        let z = m.is_zero();
        Dy {
            neg: (self.neg != o.neg) && !z,
            m,
            e: self.e + o.e,
        }
    }
    pub fn cmp_abs(&self, o: &Dy) -> Ordering {
        if self.is_zero() || o.is_zero() {
            return (!self.is_zero()).cmp(&!o.is_zero());
        }
        let la = self.m.bits() as i64 + self.e;
        let lb = o.m.bits() as i64 + o.e;
        if la != lb {
            return la.cmp(&lb);
        }
        let (a, b, _) = self.align(o);
        a.cmp(&b)
    }
    /// |self| ≈ f·2^k with f in [1, 2) (f to f64 precision), None for zero
    pub fn approx(&self) -> Option<(f64, i64)> {
        let l = self.m.bits() as i64;
        if l == 0 {
            return None;
        }
        // top 64 bits
        let t = if l > 64 {
            self.m.shr((l - 64) as u64).0[0]
        } else {
            self.m.0[0] << (64 - l)
        };
        Some((t as f64 / 2f64.powi(63), self.e + l - 1))
    }
    /// |self| / |o| as f64 (0 if self is zero, inf if o is zero); about 1e-16 relative
    pub fn ratio(&self, o: &Dy) -> f64 {
        match (self.approx(), o.approx()) {
            (None, _) => 0.0,
            (_, None) => f64::INFINITY,
            (Some((fa, ka)), Some((fb, kb))) => {
                let k = ka - kb;
                if k > 1000 {
                    f64::INFINITY
                } else if k < -1000 {
                    0.0
                } else {
                    fa / fb * 2f64.powi(k as i32)
                }
            }
        }
    }
    /// value rounded to nearest f64
    pub fn to_f64(&self) -> f64 {
        let v = round_to_f64(&self.m, self.e, false);
        if self.neg {
            -v
        } else {
            v
        }
    }
    /// four parts by greedy round-to-nearest (x0 = RN(v), x1 = RN(v - x0), ...): a normalized quad-double built
    /// without any quad-double arithmetic
    pub fn greedy4(&self) -> [f64; 4] {
        let mut r = self.clone();
        let mut x = [0.0; 4];
        for xi in x.iter_mut() {
            let c = r.to_f64();
            if c == 0.0 || !c.is_finite() {
                *xi = c;
                break;
            }
            *xi = c;
            r = r.sub(&Dy::from_f64(c));
        }
        x
    }
    /// times 2^k
    pub fn ldexp(&self, k: i64) -> Dy {
        Dy {
            neg: self.neg,
            m: self.m.clone(),
            e: self.e + k,
        }
    }
    /// exact decimal: (negative, digits, exponent) with value = digits · 10^exponent
    pub fn to_decimal(&self) -> (bool, BigU, i64) {
        if self.e >= 0 {
            (self.neg, self.m.shl(self.e as u64), 0)
        } else {
            (self.neg, self.m.mul(&BigU::pow_small(5, (-self.e) as u64)), self.e)
        }
    }
}

/// Signed rational n / (10^k · 2^t) (n a signed big integer, t of either sign), for the greedy conversion of a
/// decimal to f64 components.
#[derive(Clone, Debug)]
pub struct DecRat {
    pub neg: bool,
    pub n: BigU,
    pub k: u64,
    pub t: i64,
}

impl DecRat {
    /// round to nearest f64
    pub fn round(&self) -> f64 {
        if self.n.is_zero() {
            return 0.0;
        }
        // q = floor(n · 2^sh / 10^k) with at least 64 significant bits, value = q · 2^(-sh - t) (+ sticky)
        let est = self.n.bits() as i64 - (self.k as f64 * std::f64::consts::LOG2_10).floor() as i64;
        let sh = (70 - est).max(0) as u64;
        let (q, sticky) = self.n.shl(sh).div_pow10(self.k);
        let v = round_to_f64(&q, -(sh as i64) - self.t, sticky);
        if self.neg {
            -v
        } else {
            v
        }
    }
    /// self - c (c a finite f64)
    pub fn sub_f64(&self, c: f64) -> DecRat {
        let d = Dy::from_f64(c);
        if d.is_zero() {
            return self.clone();
        }
        // c = d.m·2^d.e = d.m·10^k·2^(d.e + t) / (10^k·2^t)
        let mut s = self.clone();
        let mut cm = d.m.mul(&BigU::pow_small(10, s.k));
        let p = d.e + s.t;
        if p >= 0 {
            cm = cm.shl(p as u64);
        } else {
            s.n = s.n.shl((-p) as u64);
            s.t -= p;
        }
        let (neg, n) = if s.neg == d.neg {
            match s.n.cmp(&cm) {
                Ordering::Less => (!s.neg, cm.sub(&s.n)),
                _ => (s.neg, s.n.sub(&cm)),
            }
        } else {
            (s.neg, s.n.add(&cm))
        };
        DecRat {
            neg: neg && !n.is_zero(),
            n,
            k: s.k,
            t: s.t,
        }
    }
}
