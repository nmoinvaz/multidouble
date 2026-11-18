//! Block decoders, which decode one block of 8 values from the words with its parts planar (`out[k][j]` is part k of
//! value j). There is one per backend, each doing its integer work in the same steps, so all give the same bits. The
//! places of escaped values come out wrong, and `Packed::decode` restores them from the side table.
//!
//! Each lower part of a lane is `(field | 0xfc << 56) + (e << 52)` with its sign put on top, e the biased exponent of
//! the last nonzero part above. A part of code 12 is a zero with its sign.
use super::{mutate, Packed, ZERO};
use crate::simd::{backend, Simd};
use std::any::TypeId;

const EXP: u64 = 0x7ff << 52;
/// The top byte the decoders put on each field, -64 in the exponent.
const TOP: u64 = 0xfc << 56;
/// A zero part's field with that top byte.
const ZERO_TOP: u64 = TOP | ZERO << 52;

/// Whether S is the backend B.
#[inline(always)]
fn is<S: Simd, B: 'static>() -> bool {
    TypeId::of::<S>() == TypeId::of::<B>()
}

/// The name of the decoder `block` runs on the backend S, one of neon, avx2, avx512 and portable.
pub(super) fn name<S: Simd>() -> &'static str {
    #[cfg(all(target_arch = "aarch64", target_feature = "neon", target_endian = "little"))]
    if is::<S, backend::Neon>() {
        return "neon";
    }
    #[cfg(target_arch = "x86_64")]
    {
        if is::<S, backend::Avx512>() {
            return "avx512";
        }
        if is::<S, backend::Avx2>() {
            return "avx2";
        }
    }
    "portable"
}

/// Block b of the words, decoded on the backend S inside its `Simd::vectorize`.
#[inline(always)]
pub(super) fn block<const N: usize, S: Simd>(words: &[u64], b: usize, out: &mut [[f64; 8]; N]) {
    let bytes = Packed::<N>::BITS;
    assert!((b + 1) * bytes <= 8 * words.len(), "block {b} past the words");
    // SAFETY (all three): the decoders read only bytes of block b, which lie within the words. They run only on S,
    // whose features dispatch has checked. The words are little-endian in memory on these targets.
    #[cfg(all(target_arch = "aarch64", target_feature = "neon", target_endian = "little"))]
    if is::<S, backend::Neon>() {
        unsafe { neon::block::<N>((words.as_ptr() as *const u8).add(b * bytes), out) };
        return mutations(out);
    }
    #[cfg(target_arch = "x86_64")]
    {
        if is::<S, backend::Avx512>() {
            unsafe { avx512::block::<N>((words.as_ptr() as *const u8).add(b * bytes), out) };
            return mutations(out);
        }
        if is::<S, backend::Avx2>() {
            unsafe { avx2::block::<N>((words.as_ptr() as *const u8).add(b * bytes), out) };
            return mutations(out);
        }
    }
    portable::<N>(words, b, out);
    mutations(out)
}

/// Block b of the words, decoded on the backend S into out (8 N f64) value by value, part k of value j at N j + k.
#[inline(always)]
pub(super) fn block_aos<const N: usize, S: Simd>(words: &[u64], b: usize, out: &mut [f64]) {
    assert!(
        out.len() == 8 * N,
        "block_aos: {} f64 for 8 values of {N} parts",
        out.len()
    );
    #[cfg(all(target_arch = "aarch64", target_feature = "neon", target_endian = "little"))]
    if is::<S, backend::Neon>() && !any_mutation() {
        let bytes = Packed::<N>::BITS;
        assert!((b + 1) * bytes <= 8 * words.len(), "block {b} past the words");
        // SAFETY: as in `block`, and out holds the 8 N f64 the decoder writes.
        unsafe { neon::block_aos::<N>((words.as_ptr() as *const u8).add(b * bytes), out.as_mut_ptr()) };
        return;
    }
    // Planar, then value by value.
    let mut p = [[0.0; 8]; N];
    block::<N, S>(words, b, &mut p);
    for j in 0..8 {
        for k in 0..N {
            out[N * j + k] = p[k][j];
        }
    }
}

/// Whether a deliberate breakage of the decoders is selected, never without the feature `mutate`.
#[cfg(all(target_arch = "aarch64", target_feature = "neon", target_endian = "little"))]
#[inline(always)]
fn any_mutation() -> bool {
    mutate::on(mutate::DEC_SIGN) || mutate::on(mutate::DEC_ZERO) || mutate::on(mutate::DEC_LAST)
}

/// The decoder's deliberate breakages (feature `mutate`), applied to its output.
#[inline(always)]
fn mutations<const N: usize>(out: &mut [[f64; 8]; N]) {
    if mutate::on(mutate::DEC_SIGN) {
        for k in 1..N {
            for j in 0..8 {
                out[k][j] = out[k][j].abs();
            }
        }
    }
    if mutate::on(mutate::DEC_ZERO) {
        for j in 0..8 {
            let mut last = out[0][j].to_bits() & EXP;
            for k in 1..N {
                let x = out[k][j].to_bits();
                if x << 1 == 0 {
                    out[k][j] = f64::from_bits(x | ZERO_TOP.wrapping_add(last));
                } else {
                    last = x & EXP;
                }
            }
        }
    }
    if mutate::on(mutate::DEC_LAST) {
        for j in 0..8 {
            let lead = out[0][j].to_bits() & EXP;
            let mut last = lead;
            for k in 1..N {
                let x = out[k][j].to_bits();
                if x << 1 != 0 {
                    let e = x & EXP;
                    out[k][j] = f64::from_bits(x & !EXP | lead.wrapping_sub(last.wrapping_sub(e)) & EXP);
                    last = e;
                }
            }
        }
    }
}

/// Plain code, for every target and byte order.
#[inline(always)]
fn portable<const N: usize>(words: &[u64], b: usize, out: &mut [[f64; 8]; N]) {
    let at = Packed::<N>::block_at(b);
    for j in 0..8 {
        let lead = super::get_bits(words, at + 64 * j, 64);
        out[0][j] = f64::from_bits(lead);
        let mut last = lead & EXP;
        for k in 1..N {
            let g = at + Packed::<N>::group_at(k);
            let f = super::get_bits(words, g + 56 * j, 56) | TOP;
            let s = super::get_bits(words, g + 448 + j, 1);
            let v = if f == ZERO_TOP { 0 } else { f.wrapping_add(last) };
            out[k][j] = f64::from_bits(v | s << 63);
            if f != ZERO_TOP {
                last = v & EXP;
            }
        }
    }
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon", target_endian = "little"))]
mod neon {
    use super::{EXP, TOP, ZERO_TOP};
    use core::arch::aarch64::*;

    /// Lanes 2r and 2r + 1 of the block at p, all parts. TBX puts each 7-byte field under the top byte 0xfc. The last
    /// pair is loaded from byte 40 of the group, so as not to read past it.
    #[inline(always)]
    unsafe fn pair<const N: usize>(p: *const u8, r: usize) -> [uint64x2_t; N] {
        const IDX: [[u8; 16]; 2] = [
            [0, 1, 2, 3, 4, 5, 6, 255, 7, 8, 9, 10, 11, 12, 13, 255],
            [2, 3, 4, 5, 6, 7, 8, 255, 9, 10, 11, 12, 13, 14, 15, 255],
        ];
        const SH: [[i64; 2]; 4] = [[0, -1], [-2, -3], [-4, -5], [-6, -7]];
        let top = vreinterpretq_u8_u64(vdupq_n_u64(TOP));
        let zero = vdupq_n_u64(ZERO_TOP);
        let exp = vdupq_n_u64(EXP);
        let (idx, off) = if r == 3 {
            (vld1q_u8(IDX[1].as_ptr()), 40)
        } else {
            (vld1q_u8(IDX[0].as_ptr()), 14 * r)
        };
        let sh = vld1q_s64(SH[r].as_ptr());
        let mut out = [vdupq_n_u64(0); N];
        out[0] = vld1q_u64(p.add(16 * r) as *const u64);
        let mut last = vandq_u64(out[0], exp);
        for k in 1..N {
            let g = p.add(64 + 57 * (k - 1));
            let f = vreinterpretq_u64_u8(vqtbx1q_u8(top, vld1q_u8(g.add(off)), idx));
            let z = vceqq_u64(f, zero);
            let v = vbicq_u64(vaddq_u64(f, last), z);
            // Lane j's sign, bit j of the group's last byte, goes to bit 0 and is then inserted at bit 63.
            let s = vshlq_u64(vreinterpretq_u64_u8(vld1q_dup_u8(g.add(56))), sh);
            out[k] = vsliq_n_u64::<63>(v, s);
            if k + 1 < N {
                last = vbslq_u64(z, last, vandq_u64(v, exp));
            }
        }
        out
    }

    /// Parts planar.
    #[inline(always)]
    pub unsafe fn block<const N: usize>(p: *const u8, out: &mut [[f64; 8]; N]) {
        for r in 0..4 {
            let v = pair::<N>(p, r);
            for k in 0..N {
                vst1q_u64(out[k].as_mut_ptr().add(2 * r) as *mut u64, v[k]);
            }
        }
    }

    /// Value by value, interleaved by ST2, ST3, ST4 or pairs of parts zipped.
    #[inline(always)]
    pub unsafe fn block_aos<const N: usize>(p: *const u8, out: *mut f64) {
        for r in 0..4 {
            let v = pair::<N>(p, r);
            let d = out.add(2 * r * N) as *mut u64;
            match N {
                2 => vst2q_u64(d, uint64x2x2_t(v[0], v[1])),
                3 => vst3q_u64(d, uint64x2x3_t(v[0], v[1], v[2])),
                4 => vst4q_u64(d, uint64x2x4_t(v[0], v[1], v[2], v[3])),
                _ => {
                    let mut k = 0;
                    while k + 1 < N {
                        vst1q_u64(d.add(k), vzip1q_u64(v[k], v[k + 1]));
                        vst1q_u64(d.add(N + k), vzip2q_u64(v[k], v[k + 1]));
                        k += 2;
                    }
                    if k < N {
                        vst1q_lane_u64::<0>(d.add(k), v[k]);
                        vst1q_lane_u64::<1>(d.add(N + k), v[k]);
                    }
                }
            }
        }
    }
}

#[cfg(target_arch = "x86_64")]
mod avx2 {
    use super::{EXP, TOP, ZERO_TOP};
    use std::arch::x86_64::*;

    /// Lanes 4h to 4h + 3 at a time, from two 16-byte loads per half, by PSHUFB to the low 7 bytes of each lane. The
    /// last pair is loaded from byte 40 of the group, so as not to read past it.
    #[inline(always)]
    pub unsafe fn block<const N: usize>(p: *const u8, out: &mut [[f64; 8]; N]) {
        let idx = [
            _mm256_setr_epi8(
                0, 1, 2, 3, 4, 5, 6, -128, 7, 8, 9, 10, 11, 12, 13, -128, 0, 1, 2, 3, 4, 5, 6, -128, 7, 8, 9, 10, 11,
                12, 13, -128,
            ),
            _mm256_setr_epi8(
                0, 1, 2, 3, 4, 5, 6, -128, 7, 8, 9, 10, 11, 12, 13, -128, 2, 3, 4, 5, 6, 7, 8, -128, 9, 10, 11, 12, 13,
                14, 15, -128,
            ),
        ];
        let sh = [_mm256_setr_epi64x(63, 62, 61, 60), _mm256_setr_epi64x(59, 58, 57, 56)];
        let top = _mm256_set1_epi64x(TOP as i64);
        let zero = _mm256_set1_epi64x(ZERO_TOP as i64);
        let exp = _mm256_set1_epi64x(EXP as i64);
        let sign = _mm256_set1_epi64x(i64::MIN);
        for h in 0..2 {
            let lead = _mm256_loadu_si256(p.add(32 * h) as *const __m256i);
            _mm256_storeu_si256(out[0].as_mut_ptr().add(4 * h) as *mut __m256i, lead);
            let mut last = _mm256_and_si256(lead, exp);
            for k in 1..N {
                let g = p.add(64 + 57 * (k - 1));
                let (lo, hi) = if h == 0 { (0, 14) } else { (28, 40) };
                let raw = _mm256_loadu2_m128i(g.add(hi) as *const __m128i, g.add(lo) as *const __m128i);
                let f = _mm256_or_si256(_mm256_shuffle_epi8(raw, idx[h]), top);
                let z = _mm256_cmpeq_epi64(f, zero);
                let v = _mm256_andnot_si256(z, _mm256_add_epi64(f, last));
                // Lane j's sign, bit j of the group's last byte, goes to bit 63.
                let s = _mm256_sllv_epi64(_mm256_set1_epi64x(*g.add(56) as i64), sh[h]);
                let part = _mm256_or_si256(v, _mm256_and_si256(s, sign));
                _mm256_storeu_si256(out[k].as_mut_ptr().add(4 * h) as *mut __m256i, part);
                if k + 1 < N {
                    last = _mm256_blendv_epi8(_mm256_and_si256(v, exp), last, z);
                }
            }
        }
    }
}

#[cfg(target_arch = "x86_64")]
mod avx512 {
    use super::{EXP, TOP, ZERO_TOP};
    use std::arch::x86_64::*;

    /// All 8 lanes at once. Lane j's field, at bit 56 j of the group, comes from the words before and at its own by
    /// variable shifts. The last lane's upper word is not loaded, so as not to read past the group.
    #[inline(always)]
    pub unsafe fn block<const N: usize>(p: *const u8, out: &mut [[f64; 8]; N]) {
        let rsh = _mm512_setr_epi64(64, 56, 48, 40, 32, 24, 16, 8);
        let lsh = _mm512_setr_epi64(0, 8, 16, 24, 32, 40, 48, 56);
        let ssh = _mm512_setr_epi64(63, 62, 61, 60, 59, 58, 57, 56);
        let low = _mm512_set1_epi64(((1u64 << 56) - 1) as i64);
        let top = _mm512_set1_epi64(TOP as i64);
        let zero = _mm512_set1_epi64(ZERO_TOP as i64);
        let exp = _mm512_set1_epi64(EXP as i64);
        let sign = _mm512_set1_epi64(i64::MIN);
        let lead = _mm512_loadu_si512(p as *const __m512i);
        _mm512_storeu_si512(out[0].as_mut_ptr() as *mut __m512i, lead);
        let mut last = _mm512_and_si512(lead, exp);
        for k in 1..N {
            let g = p.add(64 + 57 * (k - 1));
            let l = _mm512_loadu_si512(g.sub(8) as *const __m512i);
            let h = _mm512_maskz_loadu_epi64(0x7f, g as *const i64);
            let x = _mm512_or_si512(_mm512_srlv_epi64(l, rsh), _mm512_sllv_epi64(h, lsh));
            // (x & low) | top
            let f = _mm512_ternarylogic_epi64::<0xea>(x, low, top);
            let nz = !_mm512_cmpeq_epi64_mask(f, zero);
            let v = _mm512_maskz_add_epi64(nz, f, last);
            let s = _mm512_sllv_epi64(_mm512_set1_epi64(*g.add(56) as i64), ssh);
            // v | (s & sign)
            let part = _mm512_ternarylogic_epi64::<0xf8>(v, s, sign);
            _mm512_storeu_si512(out[k].as_mut_ptr() as *mut __m512i, part);
            if k + 1 < N {
                last = _mm512_mask_and_epi64(last, nz, v, exp);
            }
        }
    }
}
