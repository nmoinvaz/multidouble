//! Packed storage of double-double, quad-double and octo-double values, lossless and in fewer bits.
//!
//! A value of N parts keeps its leading part as a raw `f64`. Each lower part takes 57 bits instead of 64: its sign, a
//! 4-bit code for its exponent and its 52 fraction bits. In a renormalized value each part lies 53 or more binary places
//! below the last nonzero part above it, so the 11 exponent bits of a lower part carry about 2 bits of information. A
//! value takes `64 + 57 (N - 1)` bits, 121 for a double-double, 235 for a quad-double and 463 for an octo-double (9.6%
//! less than 512). Values are stored back to back, so value i starts at bit `i * BITS` and any value is read alone.
//!
//! The 4-bit code of a lower part:
//! * 0 to 13: a normal `f64` whose biased exponent is 53 + code below that of the last nonzero part above it;
//! * 14: a zero, with its sign;
//! * 15: the value is in the side table, at the index held in this field's fraction bits.
//!
//! A value whose parts do not fit the codes (a part 52 or more than 66 places below the last nonzero one, a subnormal,
//! infinite or NaN lower part, or a nonzero lower part below a leading part that is not a normal number) keeps its lower
//! parts raw in the side table. Every value is restored bit for bit, signed zeros and NaN payloads included.
use crate::dd::DD;
use crate::od::OD;
use crate::qd::QD;

/// bits of a lower part: sign, code, fraction
const FIELD: usize = 57;
/// the smallest exponent drop a code holds
const DROP_MIN: u64 = 53;
/// codes 0 to 13 hold drops 53 to 66
const DROPS: u64 = 14;
const ZERO: u64 = 14;
const ESCAPE: u64 = 15;
const FRAC: u64 = (1 << 52) - 1;
const SIGN: u64 = 1 << 63;

/// A number type stored as N `f64` parts, largest first.
pub trait Parts<const N: usize>: Copy {
    fn to_parts(self) -> [f64; N];
    fn from_parts(p: [f64; N]) -> Self;
}

impl<const N: usize> Parts<N> for [f64; N] {
    fn to_parts(self) -> [f64; N] {
        self
    }
    fn from_parts(p: [f64; N]) -> Self {
        p
    }
}

impl Parts<2> for DD {
    fn to_parts(self) -> [f64; 2] {
        [self.hi, self.lo]
    }
    fn from_parts(p: [f64; 2]) -> Self {
        DD { hi: p[0], lo: p[1] }
    }
}

impl Parts<4> for QD {
    fn to_parts(self) -> [f64; 4] {
        self.x
    }
    fn from_parts(p: [f64; 4]) -> Self {
        QD { x: p }
    }
}

impl Parts<8> for OD {
    fn to_parts(self) -> [f64; 8] {
        self.x
    }
    fn from_parts(p: [f64; 8]) -> Self {
        OD { x: p }
    }
}

/// Packed values of N parts each, with the raw lower parts of the values that do not fit the codes.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Packed<const N: usize> {
    len: usize,
    words: Vec<u64>,
    side: Vec<u64>,
}

/// packed double-doubles, 121 bits each
pub type PackedDD = Packed<2>;
/// packed quad-doubles, 235 bits each
pub type PackedQD = Packed<4>;
/// packed octo-doubles, 463 bits each
pub type PackedOD = Packed<8>;

/// writes the low n bits of v at bit `at` of words that are zero there
#[inline]
fn put(words: &mut [u64], at: usize, v: u64, n: usize) {
    let (w, s) = (at / 64, at % 64);
    words[w] |= v << s;
    if s + n > 64 {
        words[w + 1] |= v >> (64 - s);
    }
}

/// reads n <= 64 bits at bit `at`
#[inline]
fn get_bits(words: &[u64], at: usize, n: usize) -> u64 {
    let (w, s) = (at / 64, at % 64);
    let mut v = words[w] >> s;
    if s + n > 64 {
        v |= words[w + 1] << (64 - s);
    }
    if n < 64 {
        v & ((1 << n) - 1)
    } else {
        v
    }
}

/// the biased exponent of a normal f64, or None
#[inline]
fn normal_exp(b: u64) -> Option<u64> {
    let e = (b >> 52) & 0x7ff;
    (1..=2046).contains(&e).then_some(e)
}

/// the fields of the lower parts (index 1 to N - 1), or None if one does not fit its code
fn fields<const N: usize>(p: &[u64; N]) -> Option<[u64; N]> {
    let mut f = [0; N];
    let mut last = normal_exp(p[0]);
    for k in 1..N {
        let sign = p[k] >> 63;
        let mag = p[k] & !SIGN;
        let (code, frac) = if mag == 0 {
            (ZERO, 0)
        } else {
            let e = normal_exp(mag)?;
            let drop = last?.checked_sub(e)?;
            if !(DROP_MIN..DROP_MIN + DROPS).contains(&drop) {
                return None;
            }
            last = Some(e);
            (drop - DROP_MIN, mag & FRAC)
        };
        f[k] = sign | code << 1 | frac << 5;
    }
    Some(f)
}

impl<const N: usize> Packed<N> {
    /// bits per value
    pub const BITS: usize = 64 + FIELD * (N - 1);

    pub fn new() -> Self {
        Packed {
            len: 0,
            words: Vec::new(),
            side: Vec::new(),
        }
    }

    /// the values packed, in order
    pub fn pack<T: Parts<N>>(v: &[T]) -> Self {
        let mut p = Packed {
            len: 0,
            words: Vec::with_capacity((v.len() * Self::BITS).div_ceil(64)),
            side: Vec::new(),
        };
        for &x in v {
            p.push(x);
        }
        p
    }

    /// appends one value
    pub fn push<T: Parts<N>>(&mut self, v: T) {
        let p = v.to_parts().map(f64::to_bits);
        let at = self.len * Self::BITS;
        self.words.resize((at + Self::BITS).div_ceil(64), 0);
        put(&mut self.words, at, p[0], 64);
        match fields(&p) {
            Some(f) => {
                for k in 1..N {
                    put(&mut self.words, at + 64 + (k - 1) * FIELD, f[k], FIELD);
                }
            }
            None => {
                let idx = (self.side.len() / (N - 1)) as u64;
                self.side.extend_from_slice(&p[1..]);
                put(&mut self.words, at + 64, ESCAPE << 1 | idx << 5, FIELD);
            }
        }
        self.len += 1;
    }

    /// value i
    pub fn get<T: Parts<N>>(&self, i: usize) -> T {
        assert!(
            i < self.len,
            "Packed::get: index {i} out of range for {} values",
            self.len
        );
        T::from_parts(self.raw(i).map(f64::from_bits))
    }

    /// all values, in order
    pub fn unpack<T: Parts<N>>(&self) -> Vec<T> {
        (0..self.len).map(|i| self.get(i)).collect()
    }

    /// the bits of value i's parts
    fn raw(&self, i: usize) -> [u64; N] {
        let at = i * Self::BITS;
        let mut p = [0; N];
        p[0] = get_bits(&self.words, at, 64);
        let mut last = (p[0] >> 52) & 0x7ff;
        for k in 1..N {
            let f = get_bits(&self.words, at + 64 + (k - 1) * FIELD, FIELD);
            let (sign, code, frac) = (f & 1, (f >> 1) & 15, f >> 5);
            match code {
                ESCAPE => {
                    let j = frac as usize * (N - 1);
                    p[1..].copy_from_slice(&self.side[j..j + N - 1]);
                    return p;
                }
                ZERO => p[k] = sign << 63,
                c => {
                    last -= c + DROP_MIN;
                    p[k] = sign << 63 | last << 52 | frac;
                }
            }
        }
        p
    }

    /// number of values
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// number of values kept in the side table
    pub fn escaped(&self) -> usize {
        if N > 1 {
            self.side.len() / (N - 1)
        } else {
            0
        }
    }

    /// storage in bits: the packed words and the side table
    pub fn size_bits(&self) -> usize {
        64 * (self.words.len() + self.side.len())
    }

    /// the packed words, `len * BITS` bits, unused high bits of the last word zero
    pub fn words(&self) -> &[u64] {
        &self.words
    }

    /// the side table, N - 1 raw parts per escaped value
    pub fn side(&self) -> &[u64] {
        &self.side
    }

    /// packed values from their words and side table (as `words` and `side` return them), or None if they are not a
    /// valid packing of `len` values
    pub fn from_raw(len: usize, words: Vec<u64>, side: Vec<u64>) -> Option<Self> {
        let used = len.checked_mul(Self::BITS)?;
        if words.len() != used.div_ceil(64)
            || (N > 1 && !side.len().is_multiple_of(N - 1))
            || (N == 1 && !side.is_empty())
        {
            return None;
        }
        if !used.is_multiple_of(64) && words.last().is_some_and(|w| w >> (used % 64) != 0) {
            return None;
        }
        let p = Packed { len, words, side };
        let escaped = p.escaped();
        let mut seen = 0;
        for i in 0..len {
            let at = i * Self::BITS;
            let mut last = normal_exp(get_bits(&p.words, at, 64));
            for k in 1..N {
                let f = get_bits(&p.words, at + 64 + (k - 1) * FIELD, FIELD);
                let (sign, code, frac) = (f & 1, (f >> 1) & 15, f >> 5);
                match code {
                    ESCAPE => {
                        // only in the first field, with the next index and zero fields after it
                        let rest = (k + 1..N).all(|m| get_bits(&p.words, at + 64 + (m - 1) * FIELD, FIELD) == 0);
                        if k != 1 || sign != 0 || frac != seen as u64 || !rest {
                            return None;
                        }
                        seen += 1;
                        break;
                    }
                    ZERO if frac != 0 => return None,
                    ZERO => {}
                    c => {
                        let e = last?.checked_sub(c + DROP_MIN).filter(|&e| e >= 1)?;
                        last = Some(e);
                    }
                }
            }
        }
        (seen == escaped).then_some(p)
    }
}
