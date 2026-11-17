//! `pack` bulk paths: the block decoders of every backend this CPU has (`Packed::blocks` through
//! `simd::for_each_available`), `unpack_into` on ranges and `Packed::dot` give bitwise what the values, `get` and
//! `dot_raw` give, for 2, 3, 4 and 8 parts, on arithmetic results, signed zeros, interior zeros, exponent drops at both
//! ends of the codes, escapes and arbitrary bit patterns. The backends run their own SIMD decoders (`pack::decoder`).
//! Controls (feature `mutate`): each deliberate breakage of the decoders and kernels (`pack::mutate`) makes a check
//! fail.
//!
//! cargo test --release --test pack_simd                      the checks
//! cargo test --release --test pack_simd --features mutate    and their controls
#![allow(clippy::needless_range_loop)]
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::dv::{DotAcc, DV};
use multidouble::od::OD;
use multidouble::pack::{self, Packed, PackedDD, Parts};
use multidouble::qd::QD;
use multidouble::simd::{self, Kernel, Simd};

/// every place of every block decoded on the backend S, with the name of the decoder that ran
#[derive(Clone)]
struct Decode<'a, const N: usize>(&'a Packed<N>);

impl<const N: usize> Kernel for Decode<'_, N> {
    type Output = (&'static str, Vec<[u64; N]>);
    #[inline(always)]
    fn run<S: Simd>(self) -> Self::Output {
        let mut v = Vec::new();
        for blk in self.0.blocks::<S>() {
            let mut lanes = [[0.0; 8]; N];
            for k in 0..N {
                lanes[k] = blk[k].to_array();
            }
            for j in 0..8 {
                let mut x = [0; N];
                for k in 0..N {
                    x[k] = lanes[k][j].to_bits();
                }
                v.push(x);
            }
        }
        (pack::decoder::<S>(), v)
    }
}

/// the decoder each backend should run
fn decoder_of(backend: &str) -> &'static str {
    match backend {
        "neon" if cfg!(target_endian = "little") => "neon",
        "avx2" => "avx2",
        "avx512" => "avx512",
        _ => "portable",
    }
}

/// values of N parts: renormalized-like chains with drops of 53 to 70 places (some escaped), random signs and
/// exponents, interior and trailing zeros of both signs, non-normal leading parts, and arbitrary bit patterns
fn values<const N: usize>(r: &mut Rng, n: usize) -> Vec<[f64; N]> {
    (0..n)
        .map(|i| {
            let mut x = [0.0; N];
            match i % 11 {
                0 => {
                    for k in 0..N {
                        x[k] = f64::from_bits(r.next_u64());
                    }
                }
                1 => {
                    let lead = [0.0, -0.0, f64::INFINITY, f64::NAN, f64::from_bits(1)];
                    x[0] = lead[(r.next_u64() % 5) as usize];
                    for k in 1..N {
                        x[k] = if r.next_u64() & 1 == 0 { 0.0 } else { -0.0 };
                    }
                }
                _ => {
                    let e = (r.next_u64() % 1600) as i32 - 800;
                    x[0] = (1.0 + r.unit()) * 2f64.powi(e) * if r.next_u64() & 1 == 0 { 1.0 } else { -1.0 };
                    let mut last = x[0];
                    for k in 1..N {
                        if r.next_u64().is_multiple_of(6) {
                            x[k] = if r.next_u64() & 1 == 0 { 0.0 } else { -0.0 };
                            continue;
                        }
                        // mostly within the codes' drops 53 to 64, sometimes outside (escaped)
                        let drop = if r.next_u64().is_multiple_of(50) {
                            52 + (r.next_u64() % 19) as i32
                        } else {
                            53 + (r.next_u64() % 12) as i32
                        };
                        let m = 1.0 + r.unit();
                        let ex = last.abs().log2().floor() as i32 - drop;
                        x[k] = m * 2f64.powi(ex) * if r.next_u64() & 1 == 0 { 1.0 } else { -1.0 };
                        last = x[k];
                    }
                }
            }
            x
        })
        .collect()
}

/// the places where the bulk paths of p differ from the values v: every backend's blocks (and +0 past the last
/// value) and `unpack_into` on ranges; panics if a backend does not run its own decoder
fn mismatches<const N: usize, T: Parts<N> + PartialEq + std::fmt::Debug>(v: &[T]) -> usize {
    let p = Packed::<N>::pack(v);
    let want: Vec<[u64; N]> = v.iter().map(|x| x.to_parts().map(f64::to_bits)).collect();
    for i in 0..v.len() {
        assert_eq!(p.get::<T>(i).to_parts().map(f64::to_bits), want[i], "get {i}");
    }
    let mut bad = 0;
    for (backend, (decoder, got)) in simd::for_each_available(Decode(&p)) {
        assert_eq!(decoder, decoder_of(backend), "backend {backend}");
        assert_eq!(got.len(), v.len().div_ceil(8) * 8);
        bad += (0..v.len()).filter(|&i| got[i] != want[i]).count();
        bad += got[v.len()..].iter().filter(|x| x.iter().any(|&b| b != 0)).count();
    }
    let n = v.len();
    for (s, e) in [
        (0, n),
        (3.min(n), n),
        (0, n.saturating_sub(5)),
        (9.min(n), 17.min(n)),
        (n / 2, n / 2),
    ] {
        let mut d = vec![T::from_parts([0.0; N]); e - s];
        p.unpack_into(s, &mut d);
        bad += (s..e)
            .filter(|&i| d[i - s].to_parts().map(f64::to_bits) != want[i])
            .count();
    }
    let all: Vec<T> = p.unpack();
    bad += (0..n)
        .filter(|&i| all[i].to_parts().map(f64::to_bits) != want[i])
        .count();
    bad
}

/// the decode mismatches over all data sets
fn decode_mismatches() -> usize {
    let mut r = Rng(0x5eed);
    let mut bad = 0;
    for n in [0, 1, 7, 8, 9, 63, 1000] {
        bad += mismatches::<2, [f64; 2]>(&values::<2>(&mut r, n));
        bad += mismatches::<3, [f64; 3]>(&values::<3>(&mut r, n));
        bad += mismatches::<4, [f64; 4]>(&values::<4>(&mut r, n));
        bad += mismatches::<8, [f64; 8]>(&values::<8>(&mut r, n));
    }
    let dd: Vec<DD> = (0..3001).map(|_| r.dd(40)).collect();
    bad += mismatches::<2, DD>(&dd);
    let qd: Vec<QD> = values::<4>(&mut r, 1001).into_iter().map(|x| QD { x }).collect();
    bad += mismatches::<4, QD>(&qd);
    let od: Vec<OD> = values::<8>(&mut r, 1001).into_iter().map(|x| OD { x }).collect();
    bad += mismatches::<8, OD>(&od);
    bad
}

#[test]
fn bulk_decoders_restore_every_value_on_every_backend() {
    println!("pack decoders on {:?}", simd::available());
    let mut r = Rng(1);
    let v = values::<8>(&mut r, 1000);
    let p = Packed::<8>::pack(&v);
    assert!(p.escaped() > 50 && p.escaped() < 300, "{} escaped of 1000", p.escaped());
    assert_eq!(decode_mismatches(), 0);
}

/// the dot product of the decoded blocks on the backend S, as `Packed::dot` forms it
#[derive(Clone)]
struct DotBlocks<'a>(&'a PackedDD, &'a PackedDD);

impl Kernel for DotBlocks<'_> {
    type Output = DD;
    #[inline(always)]
    fn run<S: Simd>(self) -> DD {
        let mut acc = DotAcc::<S>::zero();
        for (x, y) in self.0.blocks::<S>().zip(self.1.blocks::<S>()) {
            acc = acc.add_prod(DV { hi: x[0], lo: x[1] }, DV { hi: y[0], lo: y[1] });
        }
        let f = acc.finish();
        let mut s = f.lane(0);
        for j in 1..8 {
            s = s + f.lane(j);
        }
        s
    }
}

/// double-doubles with zero, negative and escaped low parts
fn dd_values(r: &mut Rng, n: usize) -> Vec<DD> {
    (0..n)
        .map(|i| match i % 9 {
            0 => DD { hi: r.sym(), lo: 0.0 },
            1 => DD { hi: r.sym(), lo: -0.0 },
            2 => DD {
                hi: 1.0 + r.unit(),
                lo: 2f64.powi(-70) * r.sym(),
            },
            _ => r.dd(20),
        })
        .collect()
}

/// the lengths at which `Packed::dot` or the blocks' dot on some backend differ bitwise from `dot_raw`
fn dot_mismatches() -> Vec<usize> {
    let mut r = Rng(9);
    let mut bad = Vec::new();
    for n in [0, 1, 7, 8, 9, 100, 4099] {
        let a = dd_values(&mut r, n);
        let b = dd_values(&mut r, n);
        let (pa, pb) = (PackedDD::pack(&a), PackedDD::pack(&b));
        let want = pack::dot_raw(&a, &b);
        let same = |x: DD| x.hi.to_bits() == want.hi.to_bits() && x.lo.to_bits() == want.lo.to_bits();
        let blocks = simd::for_each_available(DotBlocks(&pa, &pb));
        if !same(pa.dot(&pb)) || !blocks.iter().all(|&(_, x)| same(x)) {
            bad.push(n);
        }
    }
    bad
}

#[test]
fn packed_dot_is_bitwise_dot_raw() {
    assert_eq!(dot_mismatches(), Vec::<usize>::new());
    // and dot_raw is a double-double dot product: within 2^-100 of the sum of |a_i b_i| of the quad-double one
    let mut r = Rng(4);
    let a = dd_values(&mut r, 5000);
    let b = dd_values(&mut r, 5000);
    let d = pack::dot_raw(&a, &b);
    let mut exact = QD::from_f64(0.0);
    let mut mag = 0.0;
    for i in 0..a.len() {
        let qa = QD {
            x: [a[i].hi, a[i].lo, 0.0, 0.0],
        };
        let qb = QD {
            x: [b[i].hi, b[i].lo, 0.0, 0.0],
        };
        exact = exact + qa * qb;
        mag += (a[i].hi * b[i].hi).abs();
    }
    let err = (QD {
        x: [d.hi, d.lo, 0.0, 0.0],
    } - exact)
        .to_f64()
        .abs();
    assert!(
        err <= 2f64.powi(-100) * mag,
        "error {err:e} for a sum of magnitudes {mag:e}"
    );
}

/// Control: every mutation of `pack::mutate` makes the decode or the dot checks fail.
#[cfg(feature = "mutate")]
#[test]
fn controls_every_mutation_is_seen() {
    let mut unseen = Vec::new();
    for id in 1..=pack::mutate::N {
        pack::mutate::set(id);
        let decode = decode_mismatches();
        let dot = dot_mismatches();
        pack::mutate::set(0);
        println!(
            "mutation {id} ({}): {decode} decode mismatches, dot differs at {dot:?}",
            pack::mutate::NAMES[id as usize]
        );
        if decode == 0 && dot.is_empty() {
            unseen.push(pack::mutate::NAMES[id as usize]);
        }
    }
    assert!(unseen.is_empty(), "mutations not seen: {unseen:?}");
    assert_eq!(decode_mismatches(), 0);
    assert!(dot_mismatches().is_empty());
}
