//! `pack`: packed double-doubles, quad-doubles and octo-doubles restore every value bit for bit, read alone by index or
//! all together, on arithmetic results and on the edge cases of the codes (signed zeros, NaN payloads, subnormals,
//! infinities, interior zeros, exponent drops at both ends of the codes, arbitrary bit patterns). `from_raw` accepts a
//! packing's own words and rejects altered ones. Control: every single-bit change to the words of normal values either
//! makes `from_raw` reject them or changes a restored value, so the round-trip checks would see a wrong packing.
#![allow(clippy::needless_range_loop)]
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::od::OD;
use multidouble::pack::{Packed, PackedDD, PackedOD, PackedQD, Parts};
use multidouble::qd::QD;

/// an octo-double h (1 + O(2^-53)) with all eight parts in use
fn od_of(r: &mut Rng, h: f64) -> OD {
    let mut x = [0.0; 8];
    x[0] = h;
    for i in 1..8 {
        x[i] = x[i - 1] * 2f64.powi(-53) * r.sym();
    }
    OD::new(x)
}

/// results of the octo-double arithmetic on random operands of mixed sizes
fn od_results(r: &mut Rng, n: usize) -> Vec<OD> {
    (0..n)
        .map(|i| {
            let ha = r.sym() * 2f64.powi((r.next_u64() % 40) as i32 - 20);
            let a = od_of(r, ha);
            let hb = r.sym() * 2f64.powi((r.next_u64() % 40) as i32 - 20);
            let b = od_of(r, hb);
            match i % 5 {
                0 => a + b,
                1 => a - b,
                2 => a * b,
                3 => a / b,
                _ => (a * a).sqrt(),
            }
        })
        .collect()
}

fn bits<const N: usize>(p: [f64; N]) -> [u64; N] {
    p.map(f64::to_bits)
}

/// packs the values, and checks every restored value bit for bit, by index and all together, and the sizes
fn round_trip<const N: usize, T: Parts<N>>(v: &[T]) -> Packed<N> {
    let p = Packed::<N>::pack(v);
    assert_eq!(p.len(), v.len());
    assert_eq!(p.words().len(), (v.len().div_ceil(8) * Packed::<N>::BITS).div_ceil(8));
    assert_eq!(p.side().len(), p.escaped() * (N - 1));
    for (i, &x) in v.iter().enumerate() {
        assert_eq!(bits(p.get::<T>(i).to_parts()), bits(x.to_parts()), "value {i}");
    }
    let all: Vec<T> = p.unpack();
    assert!(all.iter().zip(v).all(|(a, b)| bits(a.to_parts()) == bits(b.to_parts())));
    let again = Packed::<N>::from_raw(p.len(), p.words().to_vec(), p.side().to_vec()).expect("own words accepted");
    assert_eq!(again, p);
    p
}

#[test]
fn octo_double_results_round_trip_in_463_bits() {
    let mut r = Rng(0x9e37_79b9_7f4a_7c15);
    let v = od_results(&mut r, 20_000);
    let p = round_trip(&v);
    assert_eq!(PackedOD::BITS, 463);
    let per_value = p.size_bits() as f64 / v.len() as f64;
    println!(
        "octo-double: {} values, {} escaped, {per_value:.1} bits per value",
        v.len(),
        p.escaped()
    );
    assert!(p.escaped() * 100 < v.len(), "under 1% escaped");
    assert!(per_value < 470.0, "{per_value} bits per value");
}

#[test]
fn quad_and_double_double_results_round_trip() {
    let mut r = Rng(7);
    let qd: Vec<QD> = od_results(&mut r, 5_000)
        .iter()
        .map(|o| QD {
            x: [o.x[0], o.x[1], o.x[2], o.x[3]],
        })
        .collect();
    let p = round_trip(&qd);
    assert_eq!(PackedQD::BITS, 235);
    assert!(p.escaped() * 100 < qd.len());
    let dd: Vec<DD> = (0..5_000).map(|_| r.dd(40)).collect();
    let p = round_trip(&dd);
    assert_eq!(PackedDD::BITS, 121);
    assert!(p.escaped() * 100 < dd.len());
}

#[test]
fn edge_cases_round_trip() {
    let p2 = |e: i32| 2f64.powi(e);
    let nan = f64::from_bits(0x7ff8_0000_dead_beef);
    let sub = f64::from_bits(1);
    let cases: Vec<[f64; 8]> = vec![
        [0.0; 8],
        [-0.0; 8],
        [1.0, -0.0, 0.0, -0.0, 0.0, -0.0, 0.0, -0.0],
        [f64::INFINITY, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
        [nan, -0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
        [f64::INFINITY, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
        [nan, nan, nan, nan, nan, nan, nan, nan],
        [sub, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
        [sub, sub, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
        [1.0, sub, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
        [p2(-900), p2(-955), p2(-1015), 0.0, 0.0, 0.0, 0.0, 0.0],
        // drops 52, 53, 64, 65 below the part above
        [1.0, p2(-52), 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
        [1.0, p2(-53), 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
        [1.0, p2(-64), 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
        [1.0, p2(-65), 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
        // interior zeros: the drop counts from the last nonzero part
        [1.0, 0.0, -0.0, p2(-60), 0.0, p2(-120), 0.0, -p2(-180)],
        [1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, p2(-60)],
        [
            -1.5,
            1.25 * p2(-54),
            -p2(-110),
            p2(-170),
            -p2(-230),
            p2(-290),
            -p2(-350),
            p2(-410),
        ],
        [f64::MAX, f64::MAX * p2(-60), 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
        [
            f64::MIN_POSITIVE * p2(60),
            f64::MIN_POSITIVE,
            0.0,
            0.0,
            0.0,
            0.0,
            0.0,
            0.0,
        ],
    ];
    let p = round_trip(&cases);
    // the drops 52 and 65, and the subnormal, infinite and NaN lower parts, are escaped: code 15 in the first lower
    // part's field, 56 bits at bit 56 j of the group after the block's 8 leading parts
    let escaped: Vec<bool> = cases
        .iter()
        .enumerate()
        .map(|(i, _)| {
            let w = p.words();
            let at = (i / 8) * 8 * PackedOD::BITS + 512 + 56 * (i % 8);
            let (wi, s) = (at / 64, at % 64);
            let f = if s + 56 > 64 {
                (w[wi] >> s) | (w[wi + 1] << (64 - s))
            } else {
                w[wi] >> s
            };
            (f >> 52) & 15 == 15
        })
        .collect();
    assert_eq!(
        escaped,
        [
            false, false, false, false, false, true, true, false, true, true, false, true, false, false, true, false,
            false, false, false, false
        ]
    );
    // arbitrary bit patterns, mostly escaped
    let mut r = Rng(3);
    let junk: Vec<[f64; 8]> = (0..2000)
        .map(|_| std::array::from_fn(|_| f64::from_bits(r.next_u64())))
        .collect();
    let p = round_trip(&junk);
    assert!(p.escaped() > 1900);
}

#[test]
fn from_raw_rejects_bad_packings() {
    let mut r = Rng(11);
    // 55 values leave places past the last value in the last block, and unused bits in the last word
    let v = od_results(&mut r, 55);
    let p = PackedOD::pack(&v);
    assert_ne!(v.len().div_ceil(8) * PackedOD::BITS % 8, 0);
    let (w, s) = (p.words().to_vec(), p.side().to_vec());
    assert!(PackedOD::from_raw(v.len(), w.clone(), s.clone()).is_some());
    assert!(
        PackedOD::from_raw(v.len() + 8, w.clone(), s.clone()).is_none(),
        "length"
    );
    // the places past the last value hold +0: a packing of one more value, +0, but not of one with any of their bits
    let more = PackedOD::from_raw(v.len() + 1, w.clone(), s.clone()).expect("place 55 holds +0");
    assert_eq!(more.get::<OD>(55).x.map(f64::to_bits), [0; 8]);
    // place 55 is the last of block 6: its leading part, its last field and its last sign
    let end = 7 * 8 * PackedOD::BITS;
    for bit in [6 * 8 * PackedOD::BITS + 64 * 7 + 5, end - 64, end - 1] {
        let mut pad = w.clone();
        pad[bit / 64] ^= 1 << (bit % 64);
        assert!(
            PackedOD::from_raw(v.len(), pad, s.clone()).is_none(),
            "bit {bit} of a place past the last value"
        );
    }
    assert!(
        PackedOD::from_raw(v.len(), w[..w.len() - 1].to_vec(), s.clone()).is_none(),
        "words"
    );
    assert!(
        PackedOD::from_raw(v.len(), w.clone(), vec![0; 7]).is_none(),
        "side table without escapes"
    );
    let mut tail = w.clone();
    *tail.last_mut().unwrap() |= 1 << 63;
    assert!(
        PackedOD::from_raw(v.len(), tail, s.clone()).is_none(),
        "bits past the last value"
    );
}

/// Control: each single-bit change in the words of normal values is rejected or restores a different value.
#[test]
fn control_every_bit_flip_is_seen() {
    let mut r = Rng(5);
    let v: Vec<OD> = od_results(&mut r, 40)
        .into_iter()
        .filter(|x| x.x[0].is_normal())
        .collect();
    let p = PackedOD::pack(&v);
    assert_eq!(p.escaped(), 0, "the control needs values that all fit the codes");
    let used = v.len() * PackedOD::BITS;
    let mut unseen = 0;
    for b in 0..used {
        let mut w = p.words().to_vec();
        w[b / 64] ^= 1 << (b % 64);
        if let Some(q) = PackedOD::from_raw(v.len(), w, p.side().to_vec()) {
            let same = (0..v.len()).all(|i| bits(q.get::<OD>(i).x) == bits(v[i].x));
            unseen += same as usize;
        }
    }
    assert_eq!(unseen, 0, "{unseen} of {used} bit flips went unseen");
}
