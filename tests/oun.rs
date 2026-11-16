//! `Oun<N>`, the octo-double dual with N tangents, against `Ou`: generic lane code (sums, products, quotients, the
//! constant, scalar and parameter products, Cauchy sums through the dot accumulators, a constant matrix applied by
//! `MatLane`, Horner sums, and a refined solve with a double-double LU as `FieldSolve::solve_lanes_refine_t` does it)
//! run once on `Oun<4>` gives, for every tangent k, bit for bit the tangent of the same code run on `Ou` seeded with
//! tangent k alone, and bit for bit its value. Also the `Tangents` and `Lane::NTD` bookkeeping. Control: tangent k
//! against the `Ou` run of another tangent differs.
#![allow(clippy::needless_range_loop)]
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::dual::{Counted, Lane, Param, Tangents};
use multidouble::field::{cs, cs_w, horner, DMat, FieldSolve, Fl};
use multidouble::linalg::{ld_for, DDLu};
use multidouble::native::{Dtn, Du, OJet, Ou, Oun, Qu, DV, OV};
use multidouble::od::OD;
use multidouble::simd::Native;

const B: usize = 2;
const M: usize = 8 * B;
const N: usize = 4;
/// terms of the series in the Cauchy sums
const K: usize = 6;

/// h (1 + O(2^-53)) with all eight parts in use
fn od_of(r: &mut Rng, h: f64) -> OD {
    let mut x = [0.0; 8];
    x[0] = h;
    for i in 1..8 {
        x[i] = x[i - 1] * 2f64.powi(-53) * r.sym();
    }
    OD::new(x)
}

fn ofield(r: &mut Rng, lo: f64) -> Fl<OV, B> {
    Fl(std::array::from_fn(|_| {
        OV::from_lanes(&std::array::from_fn(|_| {
            let h = lo + r.sym();
            od_of(r, h)
        }))
    }))
}

/// a diagonally dominant double-double matrix, row-major, its `DMat` and its LU
fn matrix(r: &mut Rng) -> (DMat<Native, B>, DDLu) {
    let a: Vec<DD> = (0..M * M)
        .map(|k| {
            let d = if k / M == k % M { 4.0 } else { 0.0 };
            DD::new(r.sym() + d, r.sym() * 1e-17)
        })
        .collect();
    let (h, l): (Vec<f64>, Vec<f64>) = a.iter().map(|d| (d.hi, d.lo)).unzip();
    let ld = ld_for(M);
    let (mut ch, mut cl) = (vec![0.0; ld * M], vec![0.0; ld * M]);
    for i in 0..M {
        for j in 0..M {
            ch[j * ld + i] = a[i * M + j].hi;
            cl[j * ld + i] = a[i * M + j].lo;
        }
    }
    (DMat::from_rows(&h, &l), DDLu::factor(M, ld, ch, cl, false).unwrap())
}

/// The generic code: a series built from x and y by a recursion with Cauchy sums, weighted sums, products and
/// quotients, the constant matrix applied to it, a Horner sum, and the refined solve of (omega D + kappa) f = rhs.
fn compute<T: multidouble::field::MatLane<S = Native>>(
    x: &Fl<T, B>,
    y: &Fl<T, B>,
    omega: T,
    d: &DMat<Native, B>,
    lu: &DDLu,
) -> Vec<Fl<T, B>> {
    let mut s = vec![*x, *y];
    for k in 2..K {
        let c = cs(&s, &s, k - 1);
        let w = cs_w(&s, &s, k, 1, k - 1, |i| (k - i) as f64);
        let q = (c.muls(DD::from_f64(0.75)) + w.mulf(0.5)) / (s[0] + Fl::splat(DD::from_f64(3.0)));
        let p = q
            .mul_t(omega)
            .mulp(T::P::from_dd(DD::from_f64(1.25)))
            .addp(T::P::from_dd(DD::from_f64(-0.5)))
            .mul_pwr2(0.25);
        s.push(p - s[k - 1].adds(DD::from_f64(0.125)));
    }
    let ds = d.apply(&s[K - 1]).mul_t(omega);
    let h = horner(&s, DD::from_f64(0.3));
    let kappa = s[1] + Fl::splat(DD::from_f64(5.0));
    let rhs = ds + h;
    let f = lu.solve_lanes_refine_t(lu, &rhs, 5, |f| rhs - (d.apply(f).mul_t(omega) + kappa * *f));
    vec![s[K - 1], ds, h, f]
}

fn bits(f: &Fl<OV, B>) -> Vec<u64> {
    f.0.iter()
        .flat_map(|v| v.lanes().map(|o| o.x.map(f64::to_bits)))
        .flatten()
        .collect()
}

/// Pass, fixed before the first run: for random inputs with four tangents each (on x, y and omega), every output's
/// value and every tangent k of the `Oun<4>` run are bit for bit those of the `Ou` run seeded with tangent k, over
/// the series, the matrix product, the Horner sum and the refined solve (0 of 16 x 4 comparisons differ). Control:
/// tangent k against the `Ou` run of tangent k + 1 (mod 4) differs in every output.
#[test]
fn oun_tangents_are_ou_bitwise() {
    let mut r = Rng(41);
    let (d, lu) = matrix(&mut r);
    let (xv, yv) = (ofield(&mut r, 0.0), ofield(&mut r, 1.5));
    let xt: Vec<Fl<OV, B>> = (0..N).map(|_| ofield(&mut r, 0.0)).collect();
    let yt: Vec<Fl<OV, B>> = (0..N).map(|_| ofield(&mut r, 0.0)).collect();
    let lane = |r: &mut Rng, lo: f64| {
        OV::from_lanes(&std::array::from_fn(|_| {
            let h = lo + r.sym();
            od_of(r, h)
        }))
    };
    let ov = lane(&mut r, 2.0);
    let ot: Vec<OV> = (0..N).map(|_| lane(&mut r, 0.0)).collect();
    let many = compute(
        &Fl::<Oun<N>, B>::from_tangents(&xv, &xt),
        &Fl::<Oun<N>, B>::from_tangents(&yv, &yt),
        Oun::<N>::from_tangents(ov, &ot),
        &d,
        &lu,
    );
    let one: Vec<Vec<Fl<Ou, B>>> = (0..N)
        .map(|k| {
            compute(
                &Fl::<Ou, B>::from_tangents(&xv, &xt[k..=k]),
                &Fl::<Ou, B>::from_tangents(&yv, &yt[k..=k]),
                Ou::from_tangents(ov, &ot[k..=k]),
                &d,
                &lu,
            )
        })
        .collect();
    let (mut differ, mut control) = (0, 0);
    for (o, m) in many.iter().enumerate() {
        for k in 0..N {
            differ += (bits(&m.value()) != bits(&one[k][o].value())) as usize;
            differ += (bits(&m.tangent(k)) != bits(&one[k][o].tangent(0))) as usize;
            control += (bits(&m.tangent(k)) != bits(&one[(k + 1) % N][o].tangent(0))) as usize;
        }
    }
    println!(
        "Oun<{N}> against Ou: {differ} of {} comparisons differ; control {control} of {}",
        many.len() * N * 2,
        many.len() * N
    );
    assert_eq!(differ, 0, "a tangent or the value of Oun is not Ou's");
    assert_eq!(control, many.len() * N, "the control did not differ in every output");
}

/// whether two double-double lane vectors have the same bits
fn same(a: DV, b: DV) -> bool {
    a.hi.to_array() == b.hi.to_array() && a.lo.to_array() == b.lo.to_array()
}

/// whether a lane holds the value v and the tangents t, bit for bit (`Lane::val`, `Lane::tan_k`)
fn holds<T: Lane<S = Native>>(x: T, v: DV, t: &[DV]) -> bool {
    same(x.val(), v) && t.iter().enumerate().all(|(k, &tk)| same(x.tan_k(k), tk))
}

/// Pass, written before the first run: `Lane::NTD` is four on Oun<4> and on the counting lane over it, one on Ou, Qu
/// and Du, and none on the f64-tangent `Dtn`, the jets and the value lanes; `from_vt_n` and `tan_k` round-trip a
/// double-double value and four tangents exactly on Oun<4> and on Counted<Oun<4>>, and `from_tangents`, `value` and
/// `tangent` an octo-double one. Controls: the round-trip predicates reject a lane whose value, or one of whose
/// tangents, was moved by one unit in the last place.
#[test]
fn tangent_counts_and_round_trips() {
    assert_eq!(
        [
            <Oun<N> as Lane>::NTD,
            <Counted<Oun<N>> as Lane>::NTD,
            <Ou as Lane>::NTD,
            <Qu as Lane>::NTD,
            <Du as Lane>::NTD
        ],
        [4, 4, 1, 1, 1]
    );
    assert_eq!(
        [
            <Dtn<4> as Lane>::NTD,
            <OJet<8> as Lane>::NTD,
            <OV as Lane>::NTD,
            <DV as Lane>::NTD
        ],
        [0, 0, 0, 0]
    );
    let mut r = Rng(5);
    // normalized double-doubles: each low part below half an ulp of its high part
    let dv = |r: &mut Rng| {
        let hi: [f64; 8] = std::array::from_fn(|_| r.sym());
        let lo: [f64; 8] = std::array::from_fn(|j| hi[j] * 2f64.powi(-60) * r.sym());
        DV::load(&hi, &lo)
    };
    let v = dv(&mut r);
    let t: Vec<DV> = (0..N).map(|_| dv(&mut r)).collect();
    assert!(holds(Oun::<N>::from_vt_n(v, &t), v, &t), "Oun's round trip");
    assert!(
        holds(Counted::<Oun<N>>::from_vt_n(v, &t), v, &t),
        "Counted<Oun>'s round trip"
    );
    // controls: one ulp moved in the value, then in the last tangent
    let ulp = |x: DV| {
        let mut hi = x.hi.to_array();
        hi[3] = f64::from_bits(hi[3].to_bits() + 1);
        DV::load(&hi, &x.lo.to_array())
    };
    let x = Oun::<N>::from_vt_n(v, &t);
    let mut t_moved = t.clone();
    t_moved[N - 1] = ulp(t[N - 1]);
    assert!(!holds(x, ulp(v), &t), "control: a moved value passed");
    assert!(!holds(x, v, &t_moved), "control: a moved tangent passed");
    let lane = |r: &mut Rng| {
        OV::from_lanes(&std::array::from_fn(|_| {
            let h = r.sym();
            od_of(r, h)
        }))
    };
    let ov = lane(&mut r);
    let ot: Vec<OV> = (0..N).map(|_| lane(&mut r)).collect();
    let y = Oun::<N>::from_tangents(ov, &ot);
    let ob = |v: OV| v.lanes().map(|o| o.x.map(f64::to_bits));
    assert!(ob(y.value()) == ob(ov) && (0..N).all(|k| ob(y.tangent(k)) == ob(ot[k])));
}
