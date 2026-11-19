//! The in-place accumulation and Cauchy sums against the value-returning ones, bit for bit, on every backend this CPU
//! runs (`simd::for_each_available`), with random inputs in every part of every lane type: `Lane::acc_mut` against
//! `Lane::acc` for the double-double, quad-double and octo-double values, the dual lanes (`Ou` among them) and the
//! f64-tangent lanes, the jets (`QJet<24>` among them, and `OJet<24>` in optimized builds) and the counting lane,
//! `QDotAcc::add_prod_mut` and `ODotAcc::add_prod_mut` against `add_prod`, and `field::cs_into`, `cs_range_into`,
//! `cs_w_into`, `cs_lane_into` and `cs_w_lane_into`, and the split sums `cs_par`, `cs_range_par` and `cs_w_par`,
//! against `cs`, `cs_range` and `cs_w`; the order-k sums one lane vector at a time, `cs_lane_at` and `cs_w_lane_at`,
//! and split, `cs_at_par`, `cs_range_at_par` and `cs_w_at_par`, against `cs_at`, `cs_range_at` and `cs_w_at`, and
//! `cs_w_at` against its terms' whole jets weighted, on random inputs and on jets holding signed zeros, zero parts,
//! extreme magnitudes, infinities and NaNs. Each check has a control that must fail, the same comparison of a sum with
//! two of its terms swapped, for the field sums also of a sum without its last term, for the split order-k sums of a
//! sum with one term moved by an ulp, and for the weighted ones of coefficient k left unweighted.
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::dual::{op, take_counts, Counted, Dc, Dtn, Du, Fu, Fun, Lane, Ou, Qu, F8};
use multidouble::dv::{DDotAcc, DV};
use multidouble::field::{
    cs, cs_at, cs_at_cost, cs_at_par, cs_at_splits, cs_into, cs_lane_at, cs_lane_into, cs_par, cs_range, cs_range_at,
    cs_range_at_par, cs_range_into, cs_range_par, cs_splits, cs_w, cs_w_at, cs_w_at_par, cs_w_into, cs_w_lane_at,
    cs_w_lane_into, cs_w_par, Fl, CS_AT_PAR_MIN,
};
use multidouble::jet::{Jet, OJet, QJet};
use multidouble::od::OD;
use multidouble::ov::{ODotAcc, OV};
use multidouble::qv::{QDotAcc, QV};
use multidouble::simd::{self, Kernel, Simd};
use multidouble::v8::V8;
use std::sync::atomic::{AtomicUsize, Ordering};

/// A lane type with random values in every part, and the bits of every part of a value and of an accumulator.
trait Gen: Lane {
    /// a value with every part random
    fn gen(r: &mut Rng) -> Self;
    /// the bits of every part, appended to w
    fn bits(&self, w: &mut Vec<u64>);
    /// the bits of every part of an accumulator, appended to w
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

/// the bits of the 8 lanes of v, appended to w
fn put<S: Simd>(w: &mut Vec<u64>, v: V8<S>) {
    w.extend(v.to_array().map(f64::to_bits));
}

/// the bits of a double-double accumulator, appended to w
fn put_dot<S: Simd>(w: &mut Vec<u64>, a: &DDotAcc<S>) {
    put(w, a.s);
    put(w, a.e);
}

/// the bits of every level of a quad-double accumulator, appended to w
fn put_qdot<S: Simd>(w: &mut Vec<u64>, a: &QDotAcc<S>) {
    a.s.iter().for_each(|&s| put(w, s));
}

/// the bits of every level of an octo-double accumulator, appended to w
fn put_odot<S: Simd>(w: &mut Vec<u64>, a: &ODotAcc<S>) {
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
        put_odot(w, a);
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

impl<S: Simd, const N: usize> Gen for OJet<S, N> {
    fn gen(r: &mut Rng) -> Self {
        OJet::from_coeffs(std::array::from_fn(|_| ov(r)))
    }
    fn bits(&self, w: &mut Vec<u64>) {
        self.c.iter().for_each(|c| c.bits(w));
    }
    fn acc_bits(a: &Self::Acc, w: &mut Vec<u64>) {
        a.iter().for_each(|d| put_odot(w, d));
    }
}

impl<S: Simd> Gen for Ou<S> {
    fn gen(r: &mut Rng) -> Self {
        Ou { v: ov(r), d: ov(r) }
    }
    fn bits(&self, w: &mut Vec<u64>) {
        self.v.bits(w);
        self.d.bits(w);
    }
    fn acc_bits(a: &Self::Acc, w: &mut Vec<u64>) {
        put_odot(w, &a.0);
        put_odot(w, &a.1);
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
    /// the check for T, named name in its messages; it panics on a mismatch or a control that is not caught
    fn check<T: Gen>(&mut self, name: &str);
}

/// c's check for T, a function of its own compiled with the backend's target features
/// (`Simd::vectorize`), so that on AVX2 and AVX-512 the check's lane operations inline and
/// `every_lane` is not one function of every check
#[inline(never)]
fn own<S: Simd, T: Gen>(c: &mut impl Check, name: &str) {
    S::vectorize(
        #[inline(always)]
        || c.check::<T>(name),
    )
}

/// c for every lane type on the backend S: the values, the dual and f64-tangent lanes, the jets and the counting lane
fn every_lane<S: Simd>(c: &mut impl Check) {
    own::<S, DV<S>>(c, "DV");
    own::<S, QV<S>>(c, "QV");
    own::<S, OV<S>>(c, "OV");
    own::<S, Du<S>>(c, "Du");
    own::<S, Dc<S>>(c, "Dc");
    own::<S, Qu<S>>(c, "Qu");
    own::<S, F8<S>>(c, "F8");
    own::<S, Fu<S>>(c, "Fu");
    own::<S, Dtn<S, 3>>(c, "Dtn<3>");
    own::<S, Fun<S, 3>>(c, "Fun<3>");
    own::<S, Jet<S, 5>>(c, "Jet<5>");
    own::<S, Jet<S, 24>>(c, "Jet<24>");
    own::<S, QJet<S, 5>>(c, "QJet<5>");
    own::<S, QJet<S, 24>>(c, "QJet<24>");
    own::<S, Counted<DV<S>>>(c, "Counted<DV>");
    own::<S, Counted<QJet<S, 5>>>(c, "Counted<QJet<5>>");
    // last, so that the checks above keep their seeds
    own::<S, OJet<S, 5>>(c, "OJet<5>");
    own::<S, Counted<OJet<S, 5>>>(c, "Counted<OJet<5>>");
    // optimized builds only: unoptimized (the coverage run) its sums take minutes, and the code is OJet<5>'s
    if !cfg!(debug_assertions) {
        own::<S, OJet<S, 24>>(c, "OJet<24>");
    }
    own::<S, Ou<S>>(c, "Ou");
}

/// k, a check that panics on a mismatch, run on every backend this CPU has, on a thread with a 64 MiB stack. Built
/// without optimization (the coverage run) every temporary of a check has its own stack slot, and those of
/// `QJet<24>`'s fields and accumulators overflow a test thread's 2 MiB on x86, where `Simd::hot` is always inlined.
fn on_every_backend<K: Kernel<Output = ()> + Clone + Send + 'static>(k: K) {
    let ran: Vec<&str> = std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || simd::for_each_available(k).into_iter().map(|r| r.0).collect())
        .expect("a thread for the check")
        .join()
        .unwrap_or_else(|e| std::panic::resume_unwind(e));
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
    /// the chain and its control for T, from the next seed
    #[inline(always)]
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

/// `acc_mut_is_acc` on one backend
#[derive(Clone)]
struct AccMutIsAcc;

impl Kernel for AccMutIsAcc {
    type Output = ();
    /// the check on the backend S
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

/// `add_prod_mut_is_add_prod` on one backend
#[derive(Clone)]
struct AddProdMutIsAddProd;

impl Kernel for AddProdMutIsAddProd {
    type Output = ();
    /// the check on the backend S
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

/// `odot_add_prod_mut_is_add_prod` on one backend
#[derive(Clone)]
struct OdotAddProdMutIsAddProd;

impl Kernel for OdotAddProdMutIsAddProd {
    type Output = ();
    /// the check on the backend S
    #[inline(always)]
    fn run<S: Simd>(self) {
        let mut r = Rng(82);
        let terms: Vec<(OV<S>, OV<S>)> = (0..200).map(|_| (ov(&mut r), ov(&mut r))).collect();
        let acc_bits = |a: &ODotAcc<S>| -> Vec<u64> {
            let mut w = Vec::new();
            put_odot(&mut w, a);
            w
        };
        let (mut a, mut m) = (ODotAcc::zero(), ODotAcc::zero());
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
        let (mut a, mut swapped, mut caught) = (ODotAcc::zero(), ODotAcc::zero(), 0);
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
            "{}: ODotAcc add_prod_mut matched add_prod at {} terms, the control caught {caught}",
            S::NAME,
            terms.len()
        );
    }
}

/// `ODotAcc::add_prod_mut` is `add_prod` bit for bit in every level of the accumulator, on every backend. Control:
/// the chain with two terms swapped differs after some term.
#[test]
fn odot_add_prod_mut_is_add_prod() {
    on_every_backend(OdotAddProdMutIsAddProd);
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

/// the bits of every part of every lane vector of f
fn fl_bits<T: Gen>(f: &Fl<T, B>) -> Vec<u64> {
    let mut w = Vec::new();
    f.0.iter().for_each(|v| v.bits(&mut w));
    w
}

/// `cs_into`, `cs_range_into`, `cs_w_into`, `cs_lane_into` and `cs_w_lane_into` for one lane type against `cs`,
/// `cs_range` and `cs_w` (lane vector b of them for the lane versions), at every order k < ORDERS with the ranges
/// 0..=k, k/3..=k - k/4 and an empty one, each written over a random destination, and `cs_par`, `cs_range_par` and
/// `cs_w_par` against the same, which must split some sums of every jet lane and none of the other lanes. A split
/// `cs_w_par` must take its weights on rayon's workers, and an unsplit one on the calling thread, outside the pool. The
/// controls are the in-place and the split range sum with the terms lo and lo + 1 swapped (x and y permuted so that
/// the same products come in the other order), which must differ from the reference for some k, except in
/// octo-double, whose sums round the swap away, and the sum without its last term, which must differ for every k.
struct Sums {
    backend: &'static str,
    seed: u64,
}

impl Check for Sums {
    /// every sum and its controls for T, from the next seed
    #[inline(always)]
    fn check<T: Gen>(&mut self, name: &str) {
        self.seed += 1;
        let mut r = Rng(self.seed);
        let field = |r: &mut Rng| Fl::<T, B>(std::array::from_fn(|_| T::gen(r)));
        let x: Vec<Fl<T, B>> = (0..ORDERS).map(|_| field(&mut r)).collect();
        let y: Vec<Fl<T, B>> = (0..ORDERS).map(|_| field(&mut r)).collect();
        let w = |j: usize| (2 * j + 1) as f64;
        let be = self.backend;
        let (mut checks, mut controls, mut caught, mut dropped) = (0, 0, 0, 0);
        let (mut split, mut caught_par, mut dropped_par) = (0, 0, 0);
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
            assert_eq!(
                fl_bits(&cs_par(&x, &y, k)),
                fl_bits(&want),
                "{be} {name}: cs_par, k {k}"
            );
            split += cs_splits::<T>(k + 1) as usize;
            checks += 2;
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
                assert_eq!(
                    fl_bits(&cs_range_par(&x, &y, k, lo, hi)),
                    fl_bits(&want),
                    "{be} {name}: cs_range_par, k {k}, {lo}..={hi}"
                );
                // the weights taken on rayon's workers, where only a split sum's tasks run
                let on_pool = AtomicUsize::new(0);
                let wp = |j: usize| {
                    on_pool.fetch_add(rayon::current_thread_index().is_some() as usize, Ordering::Relaxed);
                    w(j)
                };
                assert_eq!(
                    fl_bits(&cs_w_par(&x, &y, k, lo, hi, wp)),
                    fl_bits(&want_w),
                    "{be} {name}: cs_w_par, k {k}, {lo}..={hi}"
                );
                let splits = hi >= lo && cs_splits::<T>(hi - lo + 1);
                assert_eq!(
                    on_pool.load(Ordering::Relaxed) > 0,
                    splits,
                    "{be} {name}: cs_w_par, k {k}, {lo}..={hi}: weights on rayon's workers, the sum splits: {splits}"
                );
                split += 2 * splits as usize;
                checks += 6;
                if lo < hi {
                    let (mut xs, mut ys) = (x.clone(), y.clone());
                    xs.swap(lo, lo + 1);
                    ys.swap(k - lo, k - lo - 1);
                    cs_range_into(&mut out, &xs, &ys, k, lo, hi);
                    controls += 1;
                    caught += (fl_bits(&out) != fl_bits(&want)) as usize;
                    cs_range_into(&mut out, &x, &y, k, lo, hi - 1);
                    dropped += (fl_bits(&out) != fl_bits(&want)) as usize;
                    caught_par += (fl_bits(&cs_range_par(&xs, &ys, k, lo, hi)) != fl_bits(&want)) as usize;
                    dropped_par += (fl_bits(&cs_range_par(&x, &y, k, lo, hi - 1)) != fl_bits(&want)) as usize;
                }
            }
        }
        // the octo-double sums round a swap of two terms away (their accumulators show it, acc_mut_is_acc)
        assert!(
            caught > 0 || T::VAL_OD,
            "{be} {name}: control: the sums with two terms swapped have the reference's bits"
        );
        assert!(
            caught_par > 0 || T::VAL_OD,
            "{be} {name}: control: the split sums with two terms swapped have the reference's bits"
        );
        assert_eq!(
            dropped, controls,
            "{be} {name}: control: a sum without its last term has the reference's bits"
        );
        assert_eq!(
            dropped_par, controls,
            "{be} {name}: control: a split sum without its last term has the reference's bits"
        );
        assert_eq!(
            split > 0,
            T::NJ > 0,
            "{be} {name}: {split} sums split, a jet lane must split some and another lane none"
        );
        println!(
            "{be} {name}: {checks} in-place and split sums matched, {split} of them split; the controls caught \
             {caught} and {caught_par} of {controls} swaps and {dropped} and {dropped_par} of {controls} dropped terms"
        );
        at_sums::<T>(&mut r, be, name);
    }
}

/// x with the leading part of lane 0 of coefficient 0 of its lane vector 0 moved by one ulp (jets only)
fn ulp_moved<T: Gen>(x: &Fl<T, B>) -> Fl<T, B> {
    let mut f = *x;
    let v = f.0[0].coef_od(0);
    let mut lanes: [_; 8] = std::array::from_fn(|i| v.lane(i));
    lanes[0].x[0] = f64::from_bits(lanes[0].x[0].to_bits() + 1);
    f.0[0].set_coef_od(0, OV::from_lanes(&lanes));
    f
}

/// Terms of the series in the order-k checks: ORDERS, or on a jet lane enough that its last sum splits at the last
/// coefficient (`cs_at_splits`), 616 on `Jet<5>`, whose products weigh least
fn split_terms<T: Lane>() -> usize {
    match T::NJ {
        0 => ORDERS,
        nj => (CS_AT_PAR_MIN / (cs_at_cost::<T>() * nj) + 1).max(ORDERS),
    }
}

/// The series indices of the order-k checks for n terms: those below ORDERS, and n - 2 and n - 1
fn indices(n: usize) -> Vec<usize> {
    let mut js: Vec<usize> = (0..ORDERS).collect();
    js.extend([n - 2, n - 1].into_iter().filter(|&j| j >= ORDERS));
    js
}

/// `cs_w_at` with each term's whole jet weighted (`Lane::mulf`, every coefficient) rather than its coefficients 0..=k
/// (`Lane::mulf_upto`): coefficient k of the products into a copy of out, lane vector by lane vector, in `cs_w_at`'s
/// order (`Lane::acc_at`, `fin_at`)
#[allow(clippy::too_many_arguments)]
fn w_whole<T: Gen>(
    out: &Fl<T, B>,
    x: &[Fl<T, B>],
    y: &[Fl<T, B>],
    j: usize,
    lo: usize,
    hi: usize,
    w: impl Fn(usize) -> f64,
    k: usize,
) -> Fl<T, B> {
    let mut o = *out;
    for b in 0..B {
        let mut a = T::acc0();
        for i in lo..=hi {
            T::acc_at(&mut a, &x[i].0[b].mulf(w(i)), &y[j - i].0[b], k);
        }
        T::fin_at(&a, k, &mut o.0[b]);
    }
    o
}

/// The order-k sums at every coefficient k of the jet variable (k = 0 alone on the other lanes), for the series indices
/// `indices(split_terms)` with the ranges 0..=j, j/3..=j - j/4 and an empty one, each written over a random destination:
/// `cs_lane_at` and `cs_w_lane_at` against lane vector b of `cs_range_at` and `cs_w_at`, and `cs_at_par`,
/// `cs_range_at_par` and `cs_w_at_par` against `cs_at`, `cs_range_at` and `cs_w_at`, which must split some sums of
/// every jet lane and none of the other lanes, and `cs_w_at` against the whole weighted jets (`w_whole`). Control:
/// every split range sum with x[lo] moved by one ulp in its leading part (`ulp_moved`) differs from the reference.
fn at_sums<T: Gen>(r: &mut Rng, be: &str, name: &str) {
    let field = |r: &mut Rng| Fl::<T, B>(std::array::from_fn(|_| T::gen(r)));
    let n = split_terms::<T>();
    let x: Vec<Fl<T, B>> = (0..n).map(|_| field(r)).collect();
    let y: Vec<Fl<T, B>> = (0..n).map(|_| field(r)).collect();
    let (x, y) = (&x[..], &y[..]);
    let w = |i: usize| (2 * i + 1) as f64;
    let (mut checks, mut split, mut controls, mut caught, mut whole) = (0, 0, 0, 0, 0);
    for j in indices(n) {
        for k in 0..T::NJ.max(1) {
            let bg = field(r);
            let (mut want, mut out) = (bg, bg);
            cs_at(&mut want, x, y, j, k);
            cs_at_par(&mut out, x, y, j, k);
            assert_eq!(fl_bits(&out), fl_bits(&want), "{be} {name}: cs_at_par, j {j}, k {k}");
            split += cs_at_splits::<T>(j + 1, k) as usize;
            checks += 1;
            for (lo, hi) in [(0, j), (j / 3, j - j / 4), (j + 1, j)] {
                let (mut want, mut want_w) = (bg, bg);
                cs_range_at(&mut want, x, y, j, lo, hi, k);
                cs_w_at(&mut want_w, x, y, j, lo, hi, w, k);
                assert_eq!(
                    fl_bits(&want_w),
                    fl_bits(&w_whole(&bg, x, y, j, lo, hi, w, k)),
                    "{be} {name}: cs_w_at against the whole weighted jets, j {j}, {lo}..={hi}, k {k}"
                );
                whole += 1;
                for b in 0..B {
                    let mut o = bg.0[b];
                    cs_lane_at(&mut o, b, x, y, j, lo, hi, k);
                    assert!(
                        same(&o, &want.0[b]),
                        "{be} {name}: cs_lane_at, j {j}, {lo}..={hi}, k {k}, b {b}"
                    );
                    let mut o = bg.0[b];
                    cs_w_lane_at(&mut o, b, x, y, j, lo, hi, w, k);
                    assert!(
                        same(&o, &want_w.0[b]),
                        "{be} {name}: cs_w_lane_at, j {j}, {lo}..={hi}, k {k}, b {b}"
                    );
                }
                let mut out = bg;
                cs_range_at_par(&mut out, x, y, j, lo, hi, k);
                assert_eq!(
                    fl_bits(&out),
                    fl_bits(&want),
                    "{be} {name}: cs_range_at_par, j {j}, {lo}..={hi}, k {k}"
                );
                // the weights taken on rayon's workers, where only a split sum's tasks run
                let on_pool = AtomicUsize::new(0);
                let wp = |i: usize| {
                    on_pool.fetch_add(rayon::current_thread_index().is_some() as usize, Ordering::Relaxed);
                    w(i)
                };
                let mut out = bg;
                cs_w_at_par(&mut out, x, y, j, lo, hi, wp, k);
                assert_eq!(
                    fl_bits(&out),
                    fl_bits(&want_w),
                    "{be} {name}: cs_w_at_par, j {j}, {lo}..={hi}, k {k}"
                );
                let splits = hi >= lo && cs_at_splits::<T>(hi - lo + 1, k);
                assert_eq!(
                    on_pool.load(Ordering::Relaxed) > 0,
                    splits,
                    "{be} {name}: cs_w_at_par, j {j}, {lo}..={hi}, k {k}: weights on rayon's workers, the sum splits: \
                     {splits}"
                );
                split += 2 * splits as usize;
                checks += 2 + 2 * B;
                if splits {
                    let mut xs = x.to_vec();
                    xs[lo] = ulp_moved(&xs[lo]);
                    let mut out = bg;
                    cs_range_at_par(&mut out, &xs, y, j, lo, hi, k);
                    controls += 1;
                    caught += (fl_bits(&out) != fl_bits(&want)) as usize;
                }
            }
        }
    }
    assert_eq!(
        split > 0,
        T::NJ > 0,
        "{be} {name}: {split} order-k sums split, a jet lane must split some and another lane none"
    );
    assert_eq!(
        caught, controls,
        "{be} {name}: control: a split order-k sum with a term moved by an ulp has the reference's bits"
    );
    println!(
        "{be} {name}: {checks} order-k lane and split sums matched, {split} of them split, {whole} weighted ones the \
         whole weighted jets'; the control caught {caught} of {controls} terms moved by an ulp"
    );
}

/// A jet of random coefficients (`Gen`) with special values in its lanes. At level 0 each lane of each coefficient has
/// a one in two chance of +0, -0, a value with zero lower parts or one of magnitude about 2^-1000 (whose products
/// underflow); level 1 adds magnitudes about 2^1000 (whose products overflow), and level 2 also +inf, -inf or NaN at
/// about one lane in 64.
fn edge_jet<T: Gen>(r: &mut Rng, level: u8) -> T {
    let mut x = T::gen(r);
    for k in 0..T::NJ {
        let lanes: [OD; 8] = std::array::from_fn(|i| {
            let mut d = x.coef_od(k).lane(i);
            let u = r.next_u64();
            let s = if u & 1 == 0 { 1.0 } else { -1.0 };
            match (u >> 1) % 8 {
                0 => d.x = [0.0; 8],
                1 => d.x = [-0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
                2 => d.x[1..].fill(0.0),
                3 => d = OD::new(d.x.map(|p| p * 2f64.powi(-1000))),
                4 if level >= 1 => d.x.iter_mut().for_each(|p| *p *= 2f64.powi(1000)),
                _ => {}
            }
            if level >= 2 && (u >> 8).is_multiple_of(64) {
                d.x = [
                    [f64::INFINITY * s, f64::NAN, f64::NAN][((u >> 16) % 3) as usize],
                    0.0,
                    0.0,
                    0.0,
                    0.0,
                    0.0,
                    0.0,
                    0.0,
                ];
            }
            d
        });
        x.set_coef_od(k, OV::from_lanes(&lanes));
    }
    x
}

/// the bits of every part of every lane vector of f, each NaN as one word: two NaNs' sign and payload are the hardware's
/// choice of operand, which need not agree between two compilations of the same sum
fn fl_bits_nan<T: Gen>(f: &Fl<T, B>) -> Vec<u64> {
    fl_bits(f)
        .into_iter()
        .map(|w| if f64::from_bits(w).is_nan() { u64::MAX } else { w })
        .collect()
}

/// The split order-k sums against `cs_at`, `cs_range_at` and `cs_w_at`, and `cs_w_at` against the whole weighted jets
/// (`w_whole`), on jets with special values (`edge_jet`), finite and with infinities and NaNs, at every coefficient k and series index `indices(split_terms)` with the ranges 0..=j and
/// j/3..=j - j/4, each written over a destination with special values, at the three levels of `edge_jet`. Control:
/// every split range sum of level 0 with the terms x[lo] and y[j - lo] made regular differs from the reference when
/// x[lo] is moved by one ulp in its leading part (`ulp_moved`). At the other levels a product of 2^1000 or an infinity
/// can absorb the ulp.
#[inline(always)]
fn edge_at_sums<T: Gen>(seed: u64, be: &str, name: &str) {
    let mut r = Rng(seed);
    let w = |i: usize| (2 * i + 1) as f64;
    let (mut checks, mut split, mut nan, mut controls, mut caught, mut whole) = (0, 0, 0, 0, 0, 0);
    for level in 0..3 {
        let field = |r: &mut Rng| Fl::<T, B>(std::array::from_fn(|_| edge_jet::<T>(r, level)));
        let n = split_terms::<T>();
        let x: Vec<Fl<T, B>> = (0..n).map(|_| field(&mut r)).collect();
        let y: Vec<Fl<T, B>> = (0..n).map(|_| field(&mut r)).collect();
        for j in indices(n) {
            for k in 0..T::NJ {
                let bg = field(&mut r);
                for (lo, hi) in [(0, j), (j / 3, j - j / 4)] {
                    let (mut want, mut out) = (bg, bg);
                    cs_range_at(&mut want, &x, &y, j, lo, hi, k);
                    cs_range_at_par(&mut out, &x, &y, j, lo, hi, k);
                    assert_eq!(
                        fl_bits_nan(&out),
                        fl_bits_nan(&want),
                        "{be} {name}: cs_range_at_par, j {j}, {lo}..={hi}, k {k}"
                    );
                    let (mut want_w, mut out) = (bg, bg);
                    cs_w_at(&mut want_w, &x, &y, j, lo, hi, w, k);
                    cs_w_at_par(&mut out, &x, &y, j, lo, hi, w, k);
                    assert_eq!(
                        fl_bits_nan(&out),
                        fl_bits_nan(&want_w),
                        "{be} {name}: cs_w_at_par, j {j}, {lo}..={hi}, k {k}"
                    );
                    assert_eq!(
                        fl_bits_nan(&want_w),
                        fl_bits_nan(&w_whole(&bg, &x, &y, j, lo, hi, w, k)),
                        "{be} {name}: cs_w_at against the whole weighted jets, j {j}, {lo}..={hi}, k {k}"
                    );
                    whole += 1;
                    if lo == 0 {
                        let mut out = bg;
                        cs_at_par(&mut out, &x, &y, j, k);
                        assert_eq!(
                            fl_bits_nan(&out),
                            fl_bits_nan(&want),
                            "{be} {name}: cs_at_par, j {j}, k {k}"
                        );
                        checks += 1;
                    }
                    let splits = cs_at_splits::<T>(hi - lo + 1, k);
                    split += 2 * splits as usize;
                    checks += 2;
                    nan += fl_bits(&want).iter().any(|&w| f64::from_bits(w).is_nan()) as usize;
                    if splits && level == 0 {
                        // a regular term lo, whose product an ulp moves
                        let (mut xs, mut ys) = (x.clone(), y.clone());
                        xs[lo] = Fl(std::array::from_fn(|_| T::gen(&mut r)));
                        ys[j - lo] = Fl(std::array::from_fn(|_| T::gen(&mut r)));
                        let mut want = bg;
                        cs_range_at(&mut want, &xs, &ys, j, lo, hi, k);
                        xs[lo] = ulp_moved(&xs[lo]);
                        let mut out = bg;
                        cs_range_at_par(&mut out, &xs, &ys, j, lo, hi, k);
                        controls += 1;
                        caught += (fl_bits_nan(&out) != fl_bits_nan(&want)) as usize;
                    }
                }
            }
        }
    }
    assert!(
        split > 0 && nan > 0,
        "{be} {name}: {split} sums split, {nan} with NaNs: the inputs miss their purpose"
    );
    assert!(
        controls > 0 && caught == controls,
        "{be} {name}: control: {} of {controls} split sums with a term moved by an ulp have the reference's bits",
        controls - caught
    );
    println!(
        "{be} {name}: {checks} order-k sums of special values matched, {split} of them split, {nan} with NaNs, {whole} \
         weighted ones the whole weighted jets'; the control changed {caught} of {controls} sums"
    );
}

/// `edge_at_sums` for T, compiled with the backend's target features, as `own`
#[inline(never)]
fn edge_own<S: Simd, T: Gen>(seed: u64, name: &str) {
    S::vectorize(
        #[inline(always)]
        || edge_at_sums::<T>(seed, S::NAME, name),
    )
}

/// `split_at_sums_of_special_values` on one backend
#[derive(Clone)]
struct EdgeAtSums;

impl Kernel for EdgeAtSums {
    type Output = ();
    #[inline(always)]
    fn run<S: Simd>(self) {
        edge_own::<S, Jet<S, 5>>(301, "Jet<5>");
        edge_own::<S, QJet<S, 5>>(302, "QJet<5>");
        edge_own::<S, OJet<S, 5>>(303, "OJet<5>");
        edge_own::<S, Counted<OJet<S, 5>>>(304, "Counted<OJet<5>>");
        // optimized builds only, as in every_lane
        if !cfg!(debug_assertions) {
            edge_own::<S, QJet<S, 24>>(305, "QJet<24>");
            edge_own::<S, OJet<S, 24>>(306, "OJet<24>");
        }
    }
}

/// The split order-k sums are the serial ones bit for bit on jets holding signed zeros, zero parts, magnitudes that
/// overflow and underflow, infinities and NaNs, on every backend. Control: a term moved by an ulp changes a split sum.
#[test]
fn split_at_sums_of_special_values() {
    on_every_backend(EdgeAtSums);
}

/// `in_place_sums_are_the_sums` on one backend
#[derive(Clone)]
struct InPlaceSumsAreTheSums;

impl Kernel for InPlaceSumsAreTheSums {
    type Output = ();
    /// the check on the backend S
    #[inline(always)]
    fn run<S: Simd>(self) {
        every_lane::<S>(&mut Sums {
            backend: S::NAME,
            seed: 90,
        });
    }
}

/// The in-place and the split Cauchy sums are the value-returning ones bit for bit, for every lane type on every
/// backend, and the split ones split some sums of each jet lane. Controls: a sum with two terms swapped and a sum
/// without its last term differ.
#[test]
fn in_place_sums_are_the_sums() {
    on_every_backend(InPlaceSumsAreTheSums);
}

/// Control with the crate's built-in breakage: a split order-k sum whose last lane vector is moved by one ulp
/// (`dual::mutate::CS_AT_SPLIT`) differs from the serial sum, on `Jet<5>`, `QJet<5>` and `OJet<5>`, and without the
/// mutation it is the serial sum again.
#[cfg(feature = "mutate")]
#[test]
fn control_split_at_sum_moved_by_an_ulp_is_caught() {
    use multidouble::dual::mutate;
    use multidouble::native;
    fn run<T: Gen>(name: &str) {
        let mut r = Rng(401);
        let field = |r: &mut Rng| Fl::<T, B>(std::array::from_fn(|_| T::gen(r)));
        let n = split_terms::<T>();
        let x: Vec<Fl<T, B>> = (0..n).map(|_| field(&mut r)).collect();
        let y: Vec<Fl<T, B>> = (0..n).map(|_| field(&mut r)).collect();
        let (j, k) = (n - 1, T::NJ - 1);
        assert!(cs_at_splits::<T>(j + 1, k), "{name}: the sum must split");
        let mut want = Fl::zero();
        cs_at(&mut want, &x, &y, j, k);
        let w = |i: usize| (2 * i + 1) as f64;
        let mut want_w = Fl::zero();
        cs_w_at(&mut want_w, &x, &y, j, 0, j, w, k);
        let (mut out, mut out_w) = (Fl::zero(), Fl::zero());
        mutate::set(mutate::CS_AT_SPLIT);
        cs_at_par(&mut out, &x, &y, j, k);
        cs_w_at_par(&mut out_w, &x, &y, j, 0, j, w, k);
        mutate::set(0);
        assert!(
            fl_bits(&out) != fl_bits(&want),
            "{name}: control: the moved split sum has the serial sum's bits"
        );
        assert!(
            fl_bits(&out_w) != fl_bits(&want_w),
            "{name}: control: the moved weighted split sum has its bits"
        );
        cs_at_par(&mut out, &x, &y, j, k);
        assert_eq!(
            fl_bits(&out),
            fl_bits(&want),
            "{name}: the split sum without the mutation"
        );
        println!("{name}: the split order-k sums moved by an ulp differ from the serial ones");
    }
    run::<native::Jet<5>>("Jet<5>");
    run::<native::QJet<5>>("QJet<5>");
    run::<native::OJet<5>>("OJet<5>");
}

/// Control for the weighted order-k sums: with `Lane::mulf_upto` leaving coefficient k unweighted
/// (`dual::mutate::MULF_UPTO`), `cs_w_at` differs from the whole weighted jets (`w_whole`) at every coefficient k of
/// `Jet<5>`, `QJet<5>`, `OJet<5>` and `Counted<OJet<5>>`, and without the mutation it is theirs again. A mutation is
/// selected per thread, which a split sum's tasks do not see, so the control runs the serial sum.
#[cfg(feature = "mutate")]
#[test]
fn control_weighted_sum_upto_k_is_caught() {
    use multidouble::dual::mutate;
    use multidouble::native;
    fn run<T: Gen>(name: &str) {
        let mut r = Rng(402);
        let field = |r: &mut Rng| Fl::<T, B>(std::array::from_fn(|_| T::gen(r)));
        let x: Vec<Fl<T, B>> = (0..ORDERS).map(|_| field(&mut r)).collect();
        let y: Vec<Fl<T, B>> = (0..ORDERS).map(|_| field(&mut r)).collect();
        let w = |i: usize| (2 * i + 1) as f64;
        let j = ORDERS - 1;
        let mut caught = 0;
        for k in 0..T::NJ {
            let bg = field(&mut r);
            let want = w_whole(&bg, &x, &y, j, 0, j, w, k);
            let (mut out, mut again) = (bg, bg);
            mutate::set(mutate::MULF_UPTO);
            cs_w_at(&mut out, &x, &y, j, 0, j, w, k);
            mutate::set(0);
            caught += (fl_bits(&out) != fl_bits(&want)) as usize;
            cs_w_at(&mut again, &x, &y, j, 0, j, w, k);
            assert_eq!(
                fl_bits(&again),
                fl_bits(&want),
                "{name}: k {k}, the weighted sum without the mutation"
            );
        }
        assert_eq!(
            caught,
            T::NJ,
            "{name}: control: {} of {} weighted sums with coefficient k unweighted have the whole weighted jets' bits",
            T::NJ - caught,
            T::NJ
        );
        println!(
            "{name}: the weighted order-k sums with coefficient k unweighted differ at {caught} of {} k",
            T::NJ
        );
    }
    run::<native::Jet<5>>("Jet<5>");
    run::<native::QJet<5>>("QJet<5>");
    run::<native::OJet<5>>("OJet<5>");
    run::<Counted<native::OJet<5>>>("Counted<OJet<5>>");
}
