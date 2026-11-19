//! Packed storage of double-double, quad-double and octo-double values, lossless and in fewer bits.
//!
//! A value of N parts keeps its leading part as a raw `f64`. Each lower part takes 57 bits instead of 64: its sign, a
//! 4-bit code for its exponent and its 52 fraction bits. In a renormalized value each part lies 53 or more binary
//! places below the last nonzero part above it, so the 11 exponent bits of a lower part carry about 2 bits of
//! information. A value takes `64 + 57 (N - 1)` bits, 121 for a double-double, 235 for a quad-double and 463 for an
//! octo-double (9.6% less than 512).
//!
//! Values are stored in blocks of 8, each `64 + 57 (N - 1)` bytes, so that 8 values are decoded at once with byte
//! shuffles. A block holds the 8 leading parts as raw little-endian `f64` (64 bytes), then for each lower part k a
//! group of 57 bytes: the 8 values' 56-bit fields `fraction | code << 52`, 7 bytes each, and one byte of their signs
//! (bit j for value j). Any value is still read alone, from its block.
//!
//! The 4-bit code t of a lower part:
//! * 0 to 11: a normal `f64` whose biased exponent is 64 - t below that of the last nonzero part above it (53 to 64);
//! * 12: a zero, with its sign;
//! * 15: the value is in the side table, at the row held in this field's fraction bits (first lower part only).
//!
//! The decoders add the field, with a constant top byte, to the exponent above: `fraction | t << 52 | 0xfc << 56` plus
//! `e << 52` is the part's bits without the sign, as the constant is `-64 << 52`.
//!
//! A value whose parts do not fit the codes (a part fewer than 53 or more than 64 places below the last nonzero one, a
//! subnormal, infinite or NaN lower part, or a nonzero lower part below a leading part that is not a normal number)
//! keeps its lower parts raw in the side table. Every value is restored bit for bit, signed zeros and NaN payloads
//! included. The places of a block past the last value hold +0.
//!
//! [`Packed::unpack_into`] and [`Packed::dot`] decode 8 values at once on the SIMD backend [`crate::simd::dispatch`]
//! picks (NEON, AVX2, AVX-512, or plain code elsewhere), with bitwise the same results on all. [`Packed::blocks`] gives
//! the decoded blocks as lane vectors to a kernel of one's own.
//!
//! The format, with diagrams, its size against general compressors and its speed:
//! <https://github.com/nmoinvaz/multidouble/blob/main/docs/pack.md>.
use crate::dd::DD;
use crate::dv::{DDotAcc, DV};
use crate::od::OD;
use crate::qd::QD;
use crate::simd::{Kernel, Simd};
use crate::v8::V8;
use std::marker::PhantomData;

mod dec;

/// bits of a lower part: sign, code, fraction
const FIELD: usize = 57;
/// the largest exponent drop a code holds (code 0); code t holds 64 - t
const DROP_MAX: u64 = 64;
/// the smallest (code 11)
const DROP_MIN: u64 = 53;
const ZERO: u64 = 12;
const ESCAPE: u64 = 15;
const FRAC: u64 = (1 << 52) - 1;
const SIGN: u64 = 1 << 63;
/// values per block
pub const BLOCK: usize = 8;

/// Deliberate breakage of the block decoders and kernels for the controls of `tests/pack_simd.rs` (feature `mutate`;
/// ids below, 0 = none): `set(id)` selects one in the current thread, and without the feature the hooks are
/// compile-time `false`.
pub mod mutate {
    /// block decoders: the signs of the lower parts dropped
    pub const DEC_SIGN: u32 = 1;
    /// block decoders: zero lower parts decoded as normal parts of code 12
    pub const DEC_ZERO: u32 = 2;
    /// block decoders: the exponent of a lower part taken from the leading part, not the last nonzero part above
    pub const DEC_LAST: u32 = 3;
    /// bulk paths: escaped values not restored from the side table
    pub const ESC_SKIP: u32 = 4;
    /// `Packed::dot`: the products of lane 7 dropped
    pub const DOT_LANE: u32 = 5;
    /// number of ids
    pub const N: u32 = 5;
    /// the mutations' descriptions, by id
    pub const NAMES: [&str; 6] = [
        "none",
        "decode: lower signs dropped",
        "decode: zero code decoded as a normal part",
        "decode: exponent from the leading part only",
        "bulk: escapes not restored",
        "dot: lane 7 dropped",
    ];

    #[cfg(feature = "mutate")]
    thread_local!(static ID: std::cell::Cell<u32> = const { std::cell::Cell::new(0) });

    /// select the mutation for the current thread (0 = none)
    #[cfg(feature = "mutate")]
    pub fn set(id: u32) {
        ID.with(|m| m.set(id));
    }

    /// whether mutation id is selected in the current thread
    #[cfg(feature = "mutate")]
    #[inline(always)]
    pub fn on(id: u32) -> bool {
        ID.with(|m| m.get() == id)
    }

    /// whether mutation id is selected: never, without the feature `mutate`
    #[cfg(not(feature = "mutate"))]
    #[inline(always)]
    pub fn on(_id: u32) -> bool {
        false
    }
}

/// A number type stored as N `f64` parts, largest first.
pub trait Parts<const N: usize>: Copy {
    fn to_parts(self) -> [f64; N];
    fn from_parts(p: [f64; N]) -> Self;
    /// whether the type is its N parts in order in memory and nothing else, so that the bulk paths may write it as
    /// `f64`: the crate's own types, checked again at run time (`f64s`)
    #[doc(hidden)]
    const F64S: bool = false;
}

/// whether T is its parts in order in memory: its `F64S`, its size, its alignment, and a value built from distinct
/// parts
fn f64s<const N: usize, T: Parts<N>>() -> bool {
    if !T::F64S || std::mem::size_of::<T>() != 8 * N || std::mem::align_of::<T>() != 8 {
        return false;
    }
    let p: [f64; N] = std::array::from_fn(|k| k as f64 + 1.5);
    let t = T::from_parts(p);
    // SAFETY: T is 8 N bytes of f64 fields (F64S), so its memory reads as N f64
    let m: [f64; N] = unsafe { std::mem::transmute_copy(&t) };
    m.map(f64::to_bits) == p.map(f64::to_bits)
}

impl<const N: usize> Parts<N> for [f64; N] {
    fn to_parts(self) -> [f64; N] {
        self
    }
    fn from_parts(p: [f64; N]) -> Self {
        p
    }
    const F64S: bool = true;
}

impl Parts<2> for DD {
    fn to_parts(self) -> [f64; 2] {
        [self.hi, self.lo]
    }
    fn from_parts(p: [f64; 2]) -> Self {
        DD { hi: p[0], lo: p[1] }
    }
    const F64S: bool = true;
}

impl Parts<4> for QD {
    fn to_parts(self) -> [f64; 4] {
        self.x
    }
    fn from_parts(p: [f64; 4]) -> Self {
        QD { x: p }
    }
    const F64S: bool = true;
}

impl Parts<8> for OD {
    fn to_parts(self) -> [f64; 8] {
        self.x
    }
    fn from_parts(p: [f64; 8]) -> Self {
        OD { x: p }
    }
    const F64S: bool = true;
}

/// Packed values of N parts each, with the raw lower parts of the values that do not fit the codes.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Packed<const N: usize> {
    len: usize,
    words: Vec<u64>,
    side: Vec<u64>,
    /// the indices of the escaped values, ascending (derived from the words)
    esc: Vec<usize>,
}

/// packed double-doubles, 121 bits each
pub type PackedDD = Packed<2>;
/// packed quad-doubles, 235 bits each
pub type PackedQD = Packed<4>;
/// packed octo-doubles, 463 bits each
pub type PackedOD = Packed<8>;

/// writes the low n bits of v at bit `at`, replacing what was there
#[inline]
fn put(words: &mut [u64], at: usize, v: u64, n: usize) {
    let mask = if n < 64 { (1 << n) - 1 } else { u64::MAX };
    let (w, s) = (at / 64, at % 64);
    words[w] = words[w] & !(mask << s) | (v & mask) << s;
    if s + n > 64 {
        words[w + 1] = words[w + 1] & !(mask >> (64 - s)) | (v & mask) >> (64 - s);
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

/// the fields `fraction | code << 52` and signs of the lower parts (index 1 to N - 1), or None if one does not fit
fn fields<const N: usize>(p: &[u64; N]) -> Option<[(u64, u64); N]> {
    let mut f = [(0, 0); N];
    let mut last = normal_exp(p[0]);
    for k in 1..N {
        let sign = p[k] >> 63;
        let mag = p[k] & !SIGN;
        let (code, frac) = if mag == 0 {
            (ZERO, 0)
        } else {
            let e = normal_exp(mag)?;
            let drop = last?.checked_sub(e)?;
            if !(DROP_MIN..=DROP_MAX).contains(&drop) {
                return None;
            }
            last = Some(e);
            (DROP_MAX - drop, mag & FRAC)
        };
        f[k] = (frac | code << 52, sign);
    }
    Some(f)
}

/// the field of a zero lower part
const ZERO_FIELD: u64 = ZERO << 52;

impl<const N: usize> Packed<N> {
    /// bits per value
    pub const BITS: usize = 64 + FIELD * (N - 1);
    /// bytes per block of 8 values
    pub const BLOCK_BYTES: usize = Self::BITS;

    pub fn new() -> Self {
        Packed {
            len: 0,
            words: Vec::new(),
            side: Vec::new(),
            esc: Vec::new(),
        }
    }

    /// bit offset of block b
    #[inline(always)]
    fn block_at(b: usize) -> usize {
        b * 8 * Self::BITS
    }

    /// bit offset of part k's group in a block: the leading parts, then 456 bits per lower part
    #[inline(always)]
    fn group_at(k: usize) -> usize {
        512 + 456 * (k - 1)
    }

    /// the values packed, in order
    pub fn pack<T: Parts<N>>(v: &[T]) -> Self {
        let mut p = Packed {
            len: 0,
            words: Vec::with_capacity((v.len().div_ceil(8) * Self::BITS).div_ceil(8)),
            side: Vec::new(),
            esc: Vec::new(),
        };
        for &x in v {
            p.push(x);
        }
        p
    }

    /// appends one value
    pub fn push<T: Parts<N>>(&mut self, v: T) {
        let p = v.to_parts().map(f64::to_bits);
        let (b, j) = (self.len / 8, self.len % 8);
        let at = Self::block_at(b);
        if j == 0 {
            // a new block, its 8 places +0
            self.words.resize(((b + 1) * Self::BITS).div_ceil(8), 0);
            for i in 0..8 {
                for k in 1..N {
                    put(&mut self.words, at + Self::group_at(k) + 56 * i, ZERO_FIELD, 56);
                }
            }
        }
        put(&mut self.words, at + 64 * j, p[0], 64);
        let f = fields(&p).unwrap_or_else(|| {
            // escaped: the side table row in the first field, zero fields after it
            let row = (self.side.len() / (N - 1)) as u64;
            self.side.extend_from_slice(&p[1..]);
            self.esc.push(self.len);
            let mut f = [(0, 0); N];
            f[1] = (ESCAPE << 52 | row, 0);
            f
        });
        for k in 1..N {
            let g = at + Self::group_at(k);
            put(&mut self.words, g + 56 * j, f[k].0, 56);
            put(&mut self.words, g + 448 + j, f[k].1, 1);
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
        let mut v = vec![T::from_parts([0.0; N]); self.len];
        self.unpack_into(0, &mut v);
        v
    }

    /// values `start..start + dst.len()` into dst, 8 at a time on the best SIMD backend (bitwise as [`Packed::get`])
    pub fn unpack_into<T: Parts<N>>(&self, start: usize, dst: &mut [T]) {
        assert!(
            start <= self.len && dst.len() <= self.len - start,
            "Packed::unpack_into: values {start}..{} out of range for {} values",
            start + dst.len(),
            self.len
        );
        crate::simd::dispatch(Unpack { p: self, start, dst });
    }

    /// the bits of value i's parts (inlined, so that the bulk loops that restore escapes make no calls and keep their
    /// registers)
    #[inline(always)]
    fn raw(&self, i: usize) -> [u64; N] {
        let (at, j) = (Self::block_at(i / 8), i % 8);
        let mut p = [0; N];
        p[0] = get_bits(&self.words, at + 64 * j, 64);
        let mut last = (p[0] >> 52) & 0x7ff;
        for k in 1..N {
            let g = at + Self::group_at(k);
            let f = get_bits(&self.words, g + 56 * j, 56);
            let s = get_bits(&self.words, g + 448 + j, 1);
            let (code, frac) = (f >> 52, f & FRAC);
            match code {
                ESCAPE => {
                    let r = frac as usize * (N - 1);
                    p[1..].copy_from_slice(&self.side[r..r + N - 1]);
                    return p;
                }
                ZERO => p[k] = s << 63,
                c => {
                    last = last + c - DROP_MAX;
                    p[k] = s << 63 | last << 52 | frac;
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
        self.esc.len()
    }

    /// storage in bits: the packed words and the side table
    pub fn size_bits(&self) -> usize {
        64 * (self.words.len() + self.side.len())
    }

    /// the packed words: `ceil(len / 8)` blocks of `BITS` bytes, byte i of the stream in bits `8 (i % 8)` up of word
    /// `i / 8`, unused high bits of the last word zero
    pub fn words(&self) -> &[u64] {
        &self.words
    }

    /// the side table, N - 1 raw parts per escaped value
    pub fn side(&self) -> &[u64] {
        &self.side
    }

    /// packed values from their words and side table (as `words` and `side` return them), or None if they are not a
    /// valid packing of `len` values. The length is the caller's to keep: a place past the last value holds +0, which
    /// is also a valid value, so a length that ends inside the last block, short of its padding, is not detected.
    pub fn from_raw(len: usize, words: Vec<u64>, side: Vec<u64>) -> Option<Self> {
        let blocks = len.div_ceil(8);
        let used = blocks.checked_mul(Self::BITS)?.checked_mul(8)?;
        if words.len() != used.div_ceil(64)
            || (N > 1 && !side.len().is_multiple_of(N - 1))
            || (N == 1 && !side.is_empty())
        {
            return None;
        }
        if !used.is_multiple_of(64) && words.last().is_some_and(|w| w >> (used % 64) != 0) {
            return None;
        }
        let mut p = Packed {
            len,
            words,
            side,
            esc: Vec::new(),
        };
        for i in 0..blocks * 8 {
            let (at, j) = (Self::block_at(i / 8), i % 8);
            let lead = get_bits(&p.words, at + 64 * j, 64);
            if i >= len && lead != 0 {
                return None;
            }
            let mut last = normal_exp(lead);
            let mut escaped = false;
            for k in 1..N {
                let g = at + Self::group_at(k);
                let f = get_bits(&p.words, g + 56 * j, 56);
                let s = get_bits(&p.words, g + 448 + j, 1);
                let (code, frac) = (f >> 52, f & FRAC);
                if i >= len {
                    // a place past the last value: +0
                    if f != ZERO_FIELD || s != 0 {
                        return None;
                    }
                } else if escaped {
                    // the fields after an escape are zero
                    if f != 0 || s != 0 {
                        return None;
                    }
                } else {
                    match code {
                        ESCAPE => {
                            if k != 1 || s != 0 || frac != p.esc.len() as u64 {
                                return None;
                            }
                            p.esc.push(i);
                            escaped = true;
                        }
                        ZERO if frac != 0 => return None,
                        ZERO => {}
                        c if c < ZERO => {
                            let e = (last? + c).checked_sub(DROP_MAX).filter(|&e| e >= 1)?;
                            last = Some(e);
                        }
                        _ => return None,
                    }
                }
            }
        }
        let rows = if N > 1 { p.side.len() / (N - 1) } else { 0 };
        (p.esc.len() == rows).then_some(p)
    }

    /// The decoded blocks of 8 values in order, as N lane vectors each (part k of value 8b + j in lane j of the
    /// k-th), on the backend S: for a [`Kernel`] of one's own. The places of the last block past the last value are
    /// +0.
    #[inline(always)]
    pub fn blocks<S: Simd>(&self) -> Blocks<'_, N, S> {
        Blocks {
            p: self,
            b: 0,
            nb: self.len.div_ceil(8),
            e: 0,
            _s: PhantomData,
        }
    }

    /// the first escape at index i or later
    fn esc_from(&self, i: usize) -> usize {
        self.esc.partition_point(|&e| e < i)
    }

    /// block b decoded, parts planar, the escapes in it restored from cursor `*e` on
    #[inline(always)]
    fn decode<S: Simd>(&self, b: usize, e: &mut usize, out: &mut [[f64; 8]; N]) {
        dec::block::<N, S>(&self.words, b, out);
        let end = 8 * b + 8;
        while *e < self.esc.len() && self.esc[*e] < end {
            if !mutate::on(mutate::ESC_SKIP) {
                let i = self.esc[*e];
                let p = self.raw(i);
                for k in 0..N {
                    out[k][i % 8] = f64::from_bits(p[k]);
                }
            }
            *e += 1;
        }
    }
}

/// the block decoder the backend S runs: neon, avx2, avx512 or portable (for the tests)
#[doc(hidden)]
pub fn decoder<S: Simd>() -> &'static str {
    dec::name::<S>()
}

/// The decoded blocks of a [`Packed`] in order, as lane vectors on the backend S ([`Packed::blocks`]).
pub struct Blocks<'a, const N: usize, S: Simd> {
    p: &'a Packed<N>,
    b: usize,
    nb: usize,
    e: usize,
    _s: PhantomData<S>,
}

impl<const N: usize, S: Simd> Iterator for Blocks<'_, N, S> {
    type Item = [V8<S>; N];
    #[inline(always)]
    fn next(&mut self) -> Option<[V8<S>; N]> {
        if self.b == self.nb {
            return None;
        }
        let mut out = [[0.0; 8]; N];
        self.p.decode::<S>(self.b, &mut self.e, &mut out);
        self.b += 1;
        Some(std::array::from_fn(
            #[inline(always)]
            |k| V8::load(&out[k]),
        ))
    }
}

/// the kernel of `unpack_into`
struct Unpack<'a, const N: usize, T> {
    p: &'a Packed<N>,
    start: usize,
    dst: &'a mut [T],
}

impl<const N: usize, T: Parts<N>> Kernel for Unpack<'_, N, T> {
    type Output = ();
    #[inline(always)]
    fn run<S: Simd>(self) {
        // its own function on SSE2, NEON and the portable backend (AVX2 and AVX-512 inline it), so that it is not
        // inlined whole into the caller of dispatch there
        S::outline(
            #[inline(always)]
            || self.body::<S>(),
        )
    }
}

impl<const N: usize, T: Parts<N>> Unpack<'_, N, T> {
    #[inline(always)]
    fn body<S: Simd>(self) {
        let Unpack { p, start, dst } = self;
        let end = start + dst.len();
        let plain = f64s::<N, T>();
        let mut i = start;
        let mut e = p.esc_from(start);
        let mut out = [[0.0; 8]; N];
        while i < end {
            let (b, j0) = (i / 8, i % 8);
            if plain && j0 == 0 && end - i >= 8 {
                // a whole block straight into dst, then its escapes
                // SAFETY: values i..i + 8 of dst, 8 N f64 as T is its parts (f64s)
                let d = unsafe { std::slice::from_raw_parts_mut(dst.as_mut_ptr().add(i - start) as *mut f64, 8 * N) };
                dec::block_aos::<N, S>(&p.words, b, d);
                while e < p.esc.len() && p.esc[e] < i + 8 {
                    if !mutate::on(mutate::ESC_SKIP) {
                        let x = p.esc[e];
                        dst[x - start] = T::from_parts(p.raw(x).map(f64::from_bits));
                    }
                    e += 1;
                }
                i += 8;
                continue;
            }
            p.decode::<S>(b, &mut e, &mut out);
            let j1 = (end - 8 * b).min(8);
            for j in j0..j1 {
                let mut v = [0.0; N];
                for k in 0..N {
                    v[k] = out[k][j];
                }
                dst[8 * b + j - start] = T::from_parts(v);
            }
            i = 8 * b + j1;
        }
    }
}

/// The double-double dot product of a and b as [`Packed::dot`] forms it, on the raw values: products i accumulated in
/// lane i mod 8 by [`DDotAcc`] (the last block padded with zeros), the lanes finished and added in order.
pub fn dot_raw(a: &[DD], b: &[DD]) -> DD {
    assert_eq!(a.len(), b.len(), "dot_raw: lengths {} and {}", a.len(), b.len());
    crate::simd::dispatch(DotRaw { a, b })
}

struct DotRaw<'a> {
    a: &'a [DD],
    b: &'a [DD],
}

impl Kernel for DotRaw<'_> {
    type Output = DD;
    #[inline(always)]
    fn run<S: Simd>(self) -> DD {
        S::outline(
            #[inline(always)]
            || self.body::<S>(),
        )
    }
}

impl DotRaw<'_> {
    #[inline(always)]
    fn body<S: Simd>(self) -> DD {
        let mut acc = DDotAcc::<S>::zero();
        let (a, b) = (self.a.chunks(8), self.b.chunks(8));
        for (u, v) in a.zip(b) {
            let mut x = [[0.0; 8]; 2];
            let mut y = [[0.0; 8]; 2];
            for j in 0..u.len() {
                x[0][j] = u[j].hi;
                x[1][j] = u[j].lo;
                y[0][j] = v[j].hi;
                y[1][j] = v[j].lo;
            }
            acc = acc.add_prod(dv(&x), dv(&y));
        }
        lane_sum(acc)
    }
}

#[inline(always)]
fn dv<S: Simd>(x: &[[f64; 8]; 2]) -> DV<S> {
    DV {
        hi: V8::load(&x[0]),
        lo: V8::load(&x[1]),
    }
}

/// the accumulator's lanes finished and added in order
#[inline(always)]
fn lane_sum<S: Simd>(acc: DDotAcc<S>) -> DD {
    let f = acc.finish();
    let mut s = f.lane(0);
    for j in 1..8 {
        s = s + f.lane(j);
    }
    s
}

impl Packed<2> {
    /// The double-double dot product with b, decoding both 8 values at a time on the best SIMD backend: products i
    /// accumulated in lane i mod 8 by [`DDotAcc`], the lanes finished and added in order. Bitwise [`dot_raw`] of the
    /// values.
    pub fn dot(&self, b: &Packed<2>) -> DD {
        assert_eq!(self.len, b.len, "Packed::dot: lengths {} and {}", self.len, b.len);
        crate::simd::dispatch(Dot { a: self, b })
    }
}

struct Dot<'a> {
    a: &'a Packed<2>,
    b: &'a Packed<2>,
}

impl Kernel for Dot<'_> {
    type Output = DD;
    #[inline(always)]
    fn run<S: Simd>(self) -> DD {
        S::outline(
            #[inline(always)]
            || self.body::<S>(),
        )
    }
}

impl Dot<'_> {
    #[inline(always)]
    fn body<S: Simd>(self) -> DD {
        let mut acc = DDotAcc::<S>::zero();
        for (mut x, y) in self.a.blocks::<S>().zip(self.b.blocks::<S>()) {
            if mutate::on(mutate::DOT_LANE) {
                for k in 0..2 {
                    let mut t = x[k].to_array();
                    t[7] = 0.0;
                    x[k] = V8::from_array(t);
                }
            }
            acc = acc.add_prod(DV { hi: x[0], lo: x[1] }, DV { hi: y[0], lo: y[1] });
        }
        lane_sum(acc)
    }
}
