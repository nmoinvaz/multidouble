//! The in-place accumulation and Cauchy sums against the value-returning ones, bit for bit, on every backend this CPU
//! runs (`simd::for_each_available`), with random inputs in every part of every lane type: `Lane::acc_mut` against
//! `Lane::acc` for the double-double, quad-double and octo-double values, the dual and f64-tangent lanes, the jets
//! (`QJet<24>` among them) and the counting lane, `QDotAcc::add_prod_mut` against `add_prod`, and `field::cs_into`,
//! `cs_range_into`, `cs_w_into`, `cs_lane_into` and `cs_w_lane_into` against `cs`, `cs_range` and `cs_w`. Each check
//! has a control that must fail, the same comparison of a sum with two of its terms swapped, and for the field sums
//! also of a sum without its last term.
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::dual::{op, take_counts, Counted, Dc, Dtn, Du, Fu, Fun, Lane, Qu, F8};
use multidouble::dv::{DotAcc, DV};
use multidouble::field::{cs, cs_into, cs_lane_into, cs_range, cs_range_into, cs_w, cs_w_into, cs_w_lane_into, Fl};
use multidouble::jet::{Jet, QJet};
use multidouble::ov::OV;
use multidouble::qv::{QDotAcc, QV};
use multidouble::simd::{self, Kernel, Simd};
use multidouble::v8::V8;

/// A lane type with random values in every part, and the bits of every part of a value and of an accumulator.
trait Gen: Lane {
    fn gen(r: &mut Rng) -> Self;
    fn bits(&self, w: &mut Vec<u64>);
    fn acc_bits(a: &Self::Acc, w: &mut Vec<u64>);
}

/// 8 random f64 with exponents in [-2, 2]
fn v8<S: Simd>(r: &mut Rng) -> V8<S> {
    V8::from_array(std::array::from_fn(|_| r.dd(2).hi))
}

/// 8 random double-doubles with full-width low parts
fn dv<S: Simd>(r: &mut Rng) -> DV<S> {
    let x: [DD; 8] = std::array::from_fn(|_| r.dd(2));
    let (hi, lo): (Vec<f64>, Vec<f64>) = x.iter().map(|d| (d.hi, d.lo)).unzip();
    DV::load(&hi, &lo)
}

/// 8 random quad-doubles with all four parts in use: products of three double-doubles
fn qv<S: Simd>(r: &mut Rng) -> QV<S> {
    QV::from_dv(dv(r)) * QV::from_dv(dv(r)) * QV::from_dv(dv(r))
}

/// 8 random octo-doubles with all eight parts in use: products of four double-doubles
fn ov<S: Simd>(r: &mut Rng) -> OV<S> {
    OV::from_dv(dv(r)) * OV::from_dv(dv(r)) * (OV::from_dv(dv(r)) * OV::from_dv(dv(r)))
}

fn put<S: Simd>(w: &mut Vec<u64>, v: V8<S>) {
    w.extend(v.to_array().map(f64::to_bits));
}

fn put_dot<S: Simd>(w: &mut Vec<u64>, a: &DotAcc<S>) {
    put(w, a.s);
    put(w, a.e);
}

fn put_qdot<S: Simd>(w: &mut Vec<u64>, a: &QDotAcc<S>) {
    a.s.iter().for_each(|&s| put(w, s));
}

impl<S: Simd> Gen for DV<S> {
    fn gen(r: &mut Rng) -> Self {
        dv(r)
    }
    fn bits(&self, w: &mut Vec<u64>) {
        put(w, self.hi);
        put(w, self.lo);
    }
    fn acc_bits(a: &Self::Acc, w: &mut Vec<u64>) {
        put_dot(w, a);
    }
}

impl<S: Simd> Gen for QV<S> {
    fn gen(r: &mut Rng) -> Self {
        qv(r)
    }
    fn bits(&self, w: &mut Vec<u64>) {
        self.c.iter().for_each(|&c| put(w, c));
    }
    fn acc_bits(a: &Self::Acc, w: &mut Vec<u64>) {
        put_qdot(w, a);
    }
}

impl<S: Simd> Gen for OV<S> {
    fn gen(r: &mut Rng) -> Self {
        ov(r)
    }
    fn bits(&self, w: &mut Vec<u64>) {
        self.c.iter().for_each(|&c| put(w, c));
    }
    fn acc_bits(a: &Self::Acc, w: &mut Vec<u64>) {
        a.s.iter().for_each(|&s| put(w, s));
    }
}

impl<S: Simd> Gen for Du<S> {
    fn gen(r: &mut Rng) -> Self {
        Du { v: dv(r), d: dv(r) }
    }
    fn bits(&self, w: &mut Vec<u64>) {
        self.v.bits(w);
        self.d.bits(w);
    }
    fn acc_bits(a: &Self::Acc, w: &mut Vec<u64>) {
        put_dot(w, &a.0);
        put_dot(w, &a.1);
    }
}

impl<S: Simd> Gen for Dc<S> {
    fn gen(r: &mut Rng) -> Self {
        Dc {
            v: dv(r),
            r: dv(r),
            i: dv(r),
        }
    }
    fn bits(&self, w: &mut Vec<u64>) {
        self.v.bits(w);
        self.r.bits(w);
        self.i.bits(w);
    }
    fn acc_bits(a: &Self::Acc, w: &mut Vec<u64>) {
        put_dot(w, &a.0);
        put_dot(w, &a.1);
        put_dot(w, &a.2);
    }
}

impl<S: Simd> Gen for Qu<S> {
    fn gen(r: &mut Rng) -> Self {
        Qu { v: qv(r), d: qv(r) }
    }
    fn bits(&self, w: &mut Vec<u64>) {
        self.v.bits(w);
        self.d.bits(w);
    }
    fn acc_bits(a: &Self::Acc, w: &mut Vec<u64>) {
        put_qdot(w, &a.0);
        put_qdot(w, &a.1);
    }
}

impl<S: Simd> Gen for F8<S> {
    fn gen(r: &mut Rng) -> Self {
        F8(v8(r))
    }
    fn bits(&self, w: &mut Vec<u64>) {
        put(w, self.0);
    }
    fn acc_bits(a: &Self::Acc, w: &mut Vec<u64>) {
        put(w, *a);
    }
}

impl<S: Simd> Gen for Fu<S> {
    fn gen(r: &mut Rng) -> Self {
        Fu { v: v8(r), d: v8(r) }
    }
    fn bits(&self, w: &mut Vec<u64>) {
        put(w, self.v);
        put(w, self.d);
    }
    fn acc_bits(a: &Self::Acc, w: &mut Vec<u64>) {
        put(w, a.0);
        put(w, a.1);
    }
}

impl<S: Simd, const N: usize> Gen for Dtn<S, N> {
    fn gen(r: &mut Rng) -> Self {
        Dtn {
            v: dv(r),
            d: std::array::from_fn(|_| v8(r)),
        }
    }
    fn bits(&self, w: &mut Vec<u64>) {
        self.v.bits(w);
        self.d.iter().for_each(|&d| put(w, d));
    }
    fn acc_bits(a: &Self::Acc, w: &mut Vec<u64>) {
        put_dot(w, &a.0);
        a.1.iter().for_each(|&d| put(w, d));
    }
}

impl<S: Simd, const N: usize> Gen for Fun<S, N> {
    fn gen(r: &mut Rng) -> Self {
        Fun {
            v: v8(r),
            d: std::array::from_fn(|_| v8(r)),
        }
    }
    fn bits(&self, w: &mut Vec<u64>) {
        put(w, self.v);
        self.d.iter().for_each(|&d| put(w, d));
    }
    fn acc_bits(a: &Self::Acc, w: &mut Vec<u64>) {
        put(w, a.0);
        a.1.iter().for_each(|&d| put(w, d));
    }
}

impl<S: Simd, const N: usize> Gen for Jet<S, N> {
    fn gen(r: &mut Rng) -> Self {
        Jet::from_coeffs(std::array::from_fn(|_| dv(r)))
    }
    fn bits(&self, w: &mut Vec<u64>) {
        self.c.iter().for_each(|c| c.bits(w));
    }
    fn acc_bits(a: &Self::Acc, w: &mut Vec<u64>) {
        a.iter().for_each(|d| put_dot(w, d));
    }
}

impl<S: Simd, const N: usize> Gen for QJet<S, N> {
    fn gen(r: &mut Rng) -> Self {
        QJet::from_coeffs(std::array::from_fn(|_| qv(r)))
    }
    fn bits(&self, w: &mut Vec<u64>) {
        self.c.iter().for_each(|c| c.bits(w));
    }
    fn acc_bits(a: &Self::Acc, w: &mut Vec<u64>) {
        a.iter().for_each(|d| put_qdot(w, d));
    }
}

impl<L: Gen> Gen for Counted<L> {
    fn gen(r: &mut Rng) -> Self {
        Counted(L::gen(r))
    }
    fn bits(&self, w: &mut Vec<u64>) {
        self.0.bits(w);
    }
    fn acc_bits(a: &Self::Acc, w: &mut Vec<u64>) {
        L::acc_bits(a, w);
    }
}

/// the bits of every part of x
fn bits_of<T: Gen>(x: &T) -> Vec<u64> {
    let mut w = Vec::new();
    x.bits(&mut w);
    w
}

/// whether x and y are the same bits: the comparison of every check and of its control
fn same<T: Gen>(x: &T, y: &T) -> bool {
    bits_of(x) == bits_of(y)
}

/// whether the accumulators a and b and their finished sums are the same bits
fn same_acc<T: Gen>(a: &T::Acc, b: &T::Acc) -> bool {
    let (mut wa, mut wb) = (Vec::new(), Vec::new());
    T::acc_bits(a, &mut wa);
    T::acc_bits(b, &mut wb);
    wa == wb && same(&T::fin(*a), &T::fin(*b))
}

/// A check run for one lane type T.
trait Check {
    fn check<T: Gen>(&mut self, name: &str);
}

/// c for every lane type on the backend S: the values, the dual and f64-tangent lanes, the jets and the counting lane
fn every_lane<S: Simd>(c: &mut impl Check) {
    c.check::<DV<S>>("DV");
    c.check::<QV<S>>("QV");
    c.check::<OV<S>>("OV");
    c.check::<Du<S>>("Du");
    c.check::<Dc<S>>("Dc");
    c.check::<Qu<S>>("Qu");
    c.check::<F8<S>>("F8");
    c.check::<Fu<S>>("Fu");
    c.check::<Dtn<S, 3>>("Dtn<3>");
    c.check::<Fun<S, 3>>("Fun<3>");
    c.check::<Jet<S, 5>>("Jet<5>");
    c.check::<Jet<S, 24>>("Jet<24>");
    c.check::<QJet<S, 5>>("QJet<5>");
    c.check::<QJet<S, 24>>("QJet<24>");
    c.check::<Counted<DV<S>>>("Counted<DV>");
    c.check::<Counted<QJet<S, 5>>>("Counted<QJet<5>>");
}

/// k, a check that panics on a mismatch, run on every backend this CPU has
fn on_every_backend<K: Kernel<Output = ()> + Clone>(k: K) {
    let ran: Vec<&str> = simd::for_each_available(k).into_iter().map(|r| r.0).collect();
    assert_eq!(ran, simd::available());
    println!("checked on {ran:?}");
}

/// terms of each accumulation
const TERMS: usize = 40;

/// `acc_mut` against `acc` for one lane type, every part of the accumulator and of its `Lane::fin` after every term;
/// the control is the same chain with its first two terms swapped, which must differ from `acc`'s after some term
struct AccChain {
    backend: &'static str,
    seed: u64,
}

impl Check for AccChain {
    fn check<T: Gen>(&mut self, name: &str) {
        self.seed += 1;
        let mut r = Rng(self.seed);
        let terms: Vec<(T, T)> = (0..TERMS).map(|_| (T::gen(&mut r), T::gen(&mut r))).collect();
        let (mut a, mut m) = (T::acc0(), T::acc0());
        for (t, (x, y)) in terms.iter().enumerate() {
            take_counts();
            a = T::acc(a, *x, *y);
            let ca = take_counts();
            T::acc_mut(&mut m, x, y);
            let cm = take_counts();
            assert_eq!(ca, cm, "{} {name}: acc_mut counted otherwise than acc", self.backend);
            assert!(
                same_acc::<T>(&a, &m),
                "{} {name}: acc_mut differs from acc after term {t}",
                self.backend
            );
        }
        // the control: the chain with terms 0 and 1 swapped, against acc's after every term from the second
        let (mut a, mut swapped, mut caught) = (T::acc0(), T::acc0(), 0);
        for (t, u) in [1, 0].into_iter().chain(2..TERMS).enumerate() {
            a = T::acc(a, terms[t].0, terms[t].1);
            T::acc_mut(&mut swapped, &terms[u].0, &terms[u].1);
            caught += (t > 0 && !same_acc::<T>(&a, &swapped)) as usize;
        }
        assert!(
            caught > 0,
            "{} {name}: control: the sum with two terms swapped has acc's bits",
            self.backend
        );
        println!(
            "{} {name}: acc_mut matched acc at {TERMS} terms, the control caught {caught} of {}",
            self.backend,
            TERMS - 1
        );
    }
}

#[derive(Clone)]
struct AccMutIsAcc;

impl Kernel for AccMutIsAcc {
    type Output = ();
    #[inline(always)]
    fn run<S: Simd>(self) {
        every_lane::<S>(&mut AccChain {
            backend: S::NAME,
            seed: 70,
        });
    }
}

/// `Lane::acc_mut` is `Lane::acc` bit for bit, and counted as it on `Counted`, for every lane type on every backend.
/// Control: the chain with two terms swapped differs after some term.
#[test]
fn acc_mut_is_acc() {
    on_every_backend(AccMutIsAcc);
}

#[derive(Clone)]
struct AddProdMutIsAddProd;

impl Kernel for AddProdMutIsAddProd {
    type Output = ();
    #[inline(always)]
    fn run<S: Simd>(self) {
        let mut r = Rng(81);
        let terms: Vec<(QV<S>, QV<S>)> = (0..400).map(|_| (qv(&mut r), qv(&mut r))).collect();
        let acc_bits = |a: &QDotAcc<S>| -> Vec<u64> {
            let mut w = Vec::new();
            put_qdot(&mut w, a);
            w
        };
        let (mut a, mut m) = (QDotAcc::zero(), QDotAcc::zero());
        for (t, (x, y)) in terms.iter().enumerate() {
            a = a.add_prod(*x, *y);
            m.add_prod_mut(x, y);
            assert_eq!(
                acc_bits(&a),
                acc_bits(&m),
                "{}: add_prod_mut differs from add_prod after term {t}",
                S::NAME
            );
        }
        // the control: the chain with terms 0 and 1 swapped, against add_prod's after every term from the second
        let (mut a, mut swapped, mut caught) = (QDotAcc::zero(), QDotAcc::zero(), 0);
        for (t, u) in [1, 0].into_iter().chain(2..terms.len()).enumerate() {
            a = a.add_prod(terms[t].0, terms[t].1);
            swapped.add_prod_mut(&terms[u].0, &terms[u].1);
            caught += (t > 0 && acc_bits(&a) != acc_bits(&swapped)) as usize;
        }
        assert!(
            caught > 0,
            "{}: control: the sum with two terms swapped has add_prod's bits",
            S::NAME
        );
        println!(
            "{}: add_prod_mut matched add_prod at {} terms, the control caught {caught}",
            S::NAME,
            terms.len()
        );
    }
}

/// `QDotAcc::add_prod_mut` is `add_prod` bit for bit in every level of the accumulator, on every backend. Control:
/// the chain with two terms swapped differs after some term.
#[test]
fn add_prod_mut_is_add_prod() {
    on_every_backend(AddProdMutIsAddProd);
}

/// `Counted::acc_mut` counts one `op::ACC` and nothing else
#[test]
fn counted_acc_mut_counts_an_acc() {
    type C = Counted<multidouble::native::DV>;
    let x = Counted(multidouble::native::DV::splat(DD::ONE));
    let mut a = C::acc0();
    take_counts();
    C::acc_mut(&mut a, &x, &x);
    let c = take_counts();
    assert_eq!(c[op::ACC], 1);
    assert_eq!(c.iter().sum::<u64>(), 1);
}

// ---------------------------------------------------------------------------------------------------------------
// the in-place Cauchy sums
// ---------------------------------------------------------------------------------------------------------------

/// lane vectors of the fields: three, so that the f64 lanes' interleaved sums have an odd count
const B: usize = 3;
/// orders of the series x and y, so the sums of order k < ORDERS have up to ORDERS terms
const ORDERS: usize = 12;

fn fl_bits<T: Gen>(f: &Fl<T, B>) -> Vec<u64> {
    let mut w = Vec::new();
    f.0.iter().for_each(|v| v.bits(&mut w));
    w
}

/// `cs_into`, `cs_range_into`, `cs_w_into`, `cs_lane_into` and `cs_w_lane_into` for one lane type against `cs`,
/// `cs_range` and `cs_w` (lane vector b of them for the lane versions), at every order k < ORDERS with the ranges
/// 0..=k, k/3..=k - k/4 and an empty one, each written over a random destination. The controls are the in-place
/// range sum with the terms lo and lo + 1 swapped (x and y permuted so that the same products come in the other
/// order), which must differ from the reference for some k, except in octo-double, whose sums round the swap away,
/// and the sum without its last term, which must differ for every k.
struct Sums {
    backend: &'static str,
    seed: u64,
}

impl Check for Sums {
    fn check<T: Gen>(&mut self, name: &str) {
        self.seed += 1;
        let mut r = Rng(self.seed);
        let field = |r: &mut Rng| Fl::<T, B>(std::array::from_fn(|_| T::gen(r)));
        let x: Vec<Fl<T, B>> = (0..ORDERS).map(|_| field(&mut r)).collect();
        let y: Vec<Fl<T, B>> = (0..ORDERS).map(|_| field(&mut r)).collect();
        let w = |j: usize| (2 * j + 1) as f64;
        let be = self.backend;
        let (mut checks, mut controls, mut caught, mut dropped) = (0, 0, 0, 0);
        for k in 0..ORDERS {
            let mut out = field(&mut r);
            take_counts();
            let want = cs(&x, &y, k);
            let cv = take_counts();
            cs_into(&mut out, &x, &y, k);
            assert_eq!(
                take_counts(),
                cv,
                "{be} {name}: cs_into counted otherwise than cs, k {k}"
            );
            assert_eq!(fl_bits(&out), fl_bits(&want), "{be} {name}: cs_into, k {k}");
            checks += 1;
            for (lo, hi) in [(0, k), (k / 3, k - k / 4), (k + 1, k)] {
                let want = cs_range(&x, &y, k, lo, hi);
                let want_w = cs_w(&x, &y, k, lo, hi, w);
                let mut out = field(&mut r);
                cs_range_into(&mut out, &x, &y, k, lo, hi);
                assert_eq!(
                    fl_bits(&out),
                    fl_bits(&want),
                    "{be} {name}: cs_range_into, k {k}, {lo}..={hi}"
                );
                cs_w_into(&mut out, &x, &y, k, lo, hi, w);
                assert_eq!(
                    fl_bits(&out),
                    fl_bits(&want_w),
                    "{be} {name}: cs_w_into, k {k}, {lo}..={hi}"
                );
                for b in 0..B {
                    let mut o = T::gen(&mut r);
                    cs_lane_into(&mut o, b, &x, &y, k, lo, hi);
                    assert!(
                        same(&o, &want.0[b]),
                        "{be} {name}: cs_lane_into, k {k}, {lo}..={hi}, b {b}"
                    );
                    cs_w_lane_into(&mut o, b, &x, &y, k, lo, hi, w);
                    assert!(
                        same(&o, &want_w.0[b]),
                        "{be} {name}: cs_w_lane_into, k {k}, {lo}..={hi}, b {b}"
                    );
                }
                checks += 4;
                if lo < hi {
                    let (mut xs, mut ys) = (x.clone(), y.clone());
                    xs.swap(lo, lo + 1);
                    ys.swap(k - lo, k - lo - 1);
                    cs_range_into(&mut out, &xs, &ys, k, lo, hi);
                    controls += 1;
                    caught += (fl_bits(&out) != fl_bits(&want)) as usize;
                    cs_range_into(&mut out, &x, &y, k, lo, hi - 1);
                    dropped += (fl_bits(&out) != fl_bits(&want)) as usize;
                }
            }
        }
        // the octo-double sums round a swap of two terms away (their accumulators show it, acc_mut_is_acc)
        assert!(
            caught > 0 || T::VAL_OD,
            "{be} {name}: control: the sums with two terms swapped have the reference's bits"
        );
        assert_eq!(
            dropped, controls,
            "{be} {name}: control: a sum without its last term has the reference's bits"
        );
        println!(
            "{be} {name}: {checks} in-place sums matched; the controls caught {caught} of {controls} swaps and \
             {dropped} of {controls} dropped terms"
        );
    }
}

#[derive(Clone)]
struct InPlaceSumsAreTheSums;

impl Kernel for InPlaceSumsAreTheSums {
    type Output = ();
    #[inline(always)]
    fn run<S: Simd>(self) {
        every_lane::<S>(&mut Sums {
            backend: S::NAME,
            seed: 90,
        });
    }
}

/// The in-place Cauchy sums are the value-returning ones bit for bit, for every lane type on every backend. Controls:
/// a sum with two terms swapped and a sum without its last term differ.
#[test]
fn in_place_sums_are_the_sums() {
    on_every_backend(InPlaceSumsAreTheSums);
}
