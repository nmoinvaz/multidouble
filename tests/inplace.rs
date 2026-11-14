//! The in-place accumulation and Cauchy sums against the value-returning ones, bit for bit, on every backend this CPU
//! runs (`simd::for_each_available`), with random inputs in every part of every lane type: `Lane::acc_mut` against
//! `Lane::acc` for the double-double, quad-double and octo-double values, the dual lanes (`Ou` among them) and the
//! f64-tangent lanes, the jets (`QJet<24>` among them, and `OJet<24>` in optimized builds) and the counting lane,
//! `QDotAcc::add_prod_mut` and `ODotAcc::add_prod_mut` against `add_prod`, and `field::cs_into`, `cs_range_into`,
//! `cs_w_into`, `cs_lane_into` and `cs_w_lane_into`, and the split sums `cs_par`, `cs_range_par` and `cs_w_par`,
//! against `cs`, `cs_range` and `cs_w`. Each check has a control that must fail, the same comparison of a sum with two
//! of its terms swapped, and for the field sums also of a sum without its last term.
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::dual::{op, take_counts, Counted, Dc, Dtn, Du, Fu, Fun, Lane, Ou, Qu, F8};
use multidouble::dv::{DotAcc, DV};
use multidouble::field::{
    cs, cs_into, cs_lane_into, cs_par, cs_range, cs_range_into, cs_range_par, cs_splits, cs_w, cs_w_into,
    cs_w_lane_into, cs_w_par, Fl,
};
use multidouble::jet::{Jet, OJet, QJet};
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
fn put_dot<S: Simd>(w: &mut Vec<u64>, a: &DotAcc<S>) {
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
    }
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
