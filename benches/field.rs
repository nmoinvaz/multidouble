// field.rs -- Cauchy sums of jet fields, value-returning (`cs`, `cs_range`, `cs_w`) against in place (`cs_into`,
// `cs_range_into`, `cs_w_into`), one thread on the compile-time backend (`native`)
//
// The workload is one order, k = 146, of a recursion for the power series of an ODE's solution about a regular
// singular point, on Fl<QJet<24>, 4>: thirteen Cauchy sums of up to 147 terms, a matrix product and the field
// operations that combine them, from the orders below k. A QJet<24> lane vector is 6 KB and its accumulator 7.5 KB,
// which the value-returning sums move once per term. Before timing, the two versions' outputs are checked to be the
// same bits. The single sums at the same k show the gain per sum, for QJet<24>, the double-double Jet<24> and QV.

use std::hint::black_box;
use std::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};
use multidouble::dd::DD;
use multidouble::dual::{Lane, Param};
use multidouble::field::{cs, cs_into, cs_range, cs_range_into, cs_w, cs_w_into, Fl};
use multidouble::native::{DMat, Jet, QJet, QV};

const K: usize = 146;
const B: usize = 4;
type T = QJet<24>;
type F = Fl<T, B>;
type P = <T as Lane>::P;

/// xorshift in [-0.5, 0.5)
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> f64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 >> 11) as f64 / (1u64 << 53) as f64 - 0.5
    }
    /// a field of quad-double jets with every coefficient's four parts random (part q scaled by 2^-53q), plus c at
    /// order 0
    fn qjet_field(&mut self, c: f64) -> F {
        let mut f = F::zero();
        for v in f.0.iter_mut() {
            for (i, x) in v.c.iter_mut().enumerate() {
                for q in 0..4 {
                    let s = 2f64.powi(-53 * q as i32);
                    let add = if i == 0 && q == 0 { c } else { 0.0 };
                    let a: [f64; 8] = std::array::from_fn(|_| self.next() * s + add);
                    x.c[q] = multidouble::native::V8::from_array(a);
                }
            }
        }
        f
    }
}

/// the series p, m, a, c of orders 0..=K and the sums a^2 and p^2 + m^2, with the recursion's constants
struct Series {
    pp: Vec<F>,
    mm: Vec<F>,
    aa: Vec<F>,
    cc: Vec<F>,
    q2: Vec<F>,
    a2: Vec<F>,
    invc: F,
    omega: T,
    d: DMat<B>,
}

fn series() -> Series {
    let mut r = Rng(0x2545_f491_4f6c_dd1d);
    let mut v = || (0..=K).map(|_| r.qjet_field(0.0)).collect::<Vec<F>>();
    let (mut pp, mut mm, mut aa, mut cc, q2, a2) = (v(), v(), v(), v(), v(), v());
    // the orders 0 of the recursion: p and m vanish, a is one, c bounded away from zero
    pp[0] = F::zero();
    mm[0] = F::zero();
    aa[0] = F::splat(DD::ONE);
    cc[0] = r.qjet_field(0.0).mul_pwr2(0.125) + F::splat(DD::from_f64(0.6));
    let invc = F::splat(DD::ONE) / cc[0];
    let m = 8 * B;
    let hi: Vec<f64> = (0..m * m).map(|_| r.next()).collect();
    let lo: Vec<f64> = hi.iter().map(|h| h * 1e-17).collect();
    Series {
        pp,
        mm,
        aa,
        cc,
        q2,
        a2,
        invc,
        omega: T::splat(DD::from_f64(1.8)),
        d: DMat::from_rows(&hi, &lo),
    }
}

/// the recursion's parameter constants at order k
struct Consts {
    n: P,
    n1: P,
    nh: P,
    kf: f64,
}

impl Consts {
    fn at(k: usize) -> Self {
        let n = P::var(DD::from_f64(1.7));
        Consts {
            n,
            n1: n - P::one(),
            nh: n.mul_f(0.5),
            kf: k as f64,
        }
    }
}

const SIG: f64 = 0.5;

/// order k from the orders below it, every sum value-returning
#[inline(never)]
fn order_value(s: &mut Series, k: usize) {
    let Consts { n, n1, nh, kf } = Consts::at(k);
    s.pp[k] = F::zero();
    s.mm[k] = F::zero();
    s.aa[k] = F::zero();
    s.q2[k] = cs(&s.pp, &s.pp, k) + cs(&s.mm, &s.mm, k);
    s.a2[k] = cs(&s.aa, &s.aa, k);
    let sq = cs(&s.aa, &s.q2, k);
    let t3 = cs(&s.aa, &s.a2, k);
    s.aa[k] = (sq.mulf(0.5) - t3.mulp(n1.mul_f(0.5))).mulp(P::one() / (P::from_f64(kf) + n1));
    s.a2[k] = cs(&s.aa, &s.aa, k);
    s.cc[k] = cs_range(&s.cc, &s.a2, k, 0, k - 1).mulp(n1 * P::from_f64(1.0 / kf));
    let dp = s.d.apply(&s.pp[k - 1]).mul_t(s.omega).mul_pwr2(SIG);
    let dm = s.d.apply(&s.mm[k - 1]).mul_t(s.omega).mul_pwr2(SIG);
    let s1p = cs_w(&s.cc, &s.pp, k, 1, k - 1, |i| (k - i) as f64);
    let s1m = cs_w(&s.cc, &s.mm, k, 1, k - 1, |i| (k - i) as f64);
    let xpx = s.pp[k - 1].mulf(kf - 1.0).mul_pwr2(SIG) - s1p;
    let xmx = s.mm[k - 1].mulf(kf - 1.0).mul_pwr2(SIG) + s1m;
    let xcxp = cs_w(&s.cc, &s.pp, k, 1, k, |j| j as f64);
    let xcxm = cs_w(&s.cc, &s.mm, k, 1, k, |j| j as f64);
    let cp = cs(&s.cc, &s.pp, k);
    let cm = cs(&s.cc, &s.mm, k);
    finish_order(s, k, [dp, dm, xpx, xmx, xcxp, xcxm, cp, cm], n, nh, kf);
}

/// the scratch fields of `order_in_place`
struct Scratch {
    u: F,
    sq: F,
    t3: F,
    s1p: F,
    s1m: F,
    xcxp: F,
    xcxm: F,
    cp: F,
    cm: F,
}

/// order k from the orders below it, every sum in place, the other operations as in `order_value`
#[inline(never)]
fn order_in_place(s: &mut Series, k: usize, w: &mut Scratch) {
    let Consts { n, n1, nh, kf } = Consts::at(k);
    s.pp[k] = F::zero();
    s.mm[k] = F::zero();
    s.aa[k] = F::zero();
    cs_into(&mut s.q2[k], &s.pp, &s.pp, k);
    cs_into(&mut w.u, &s.mm, &s.mm, k);
    s.q2[k] = s.q2[k] + w.u;
    cs_into(&mut s.a2[k], &s.aa, &s.aa, k);
    cs_into(&mut w.sq, &s.aa, &s.q2, k);
    cs_into(&mut w.t3, &s.aa, &s.a2, k);
    s.aa[k] = (w.sq.mulf(0.5) - w.t3.mulp(n1.mul_f(0.5))).mulp(P::one() / (P::from_f64(kf) + n1));
    cs_into(&mut s.a2[k], &s.aa, &s.aa, k);
    let (below, at) = s.cc.split_at_mut(k);
    cs_range_into(&mut at[0], below, &s.a2, k, 0, k - 1);
    s.cc[k] = s.cc[k].mulp(n1 * P::from_f64(1.0 / kf));
    let dp = s.d.apply(&s.pp[k - 1]).mul_t(s.omega).mul_pwr2(SIG);
    let dm = s.d.apply(&s.mm[k - 1]).mul_t(s.omega).mul_pwr2(SIG);
    cs_w_into(&mut w.s1p, &s.cc, &s.pp, k, 1, k - 1, |i| (k - i) as f64);
    cs_w_into(&mut w.s1m, &s.cc, &s.mm, k, 1, k - 1, |i| (k - i) as f64);
    let xpx = s.pp[k - 1].mulf(kf - 1.0).mul_pwr2(SIG) - w.s1p;
    let xmx = s.mm[k - 1].mulf(kf - 1.0).mul_pwr2(SIG) + w.s1m;
    cs_w_into(&mut w.xcxp, &s.cc, &s.pp, k, 1, k, |j| j as f64);
    cs_w_into(&mut w.xcxm, &s.cc, &s.mm, k, 1, k, |j| j as f64);
    cs_into(&mut w.cp, &s.cc, &s.pp, k);
    cs_into(&mut w.cm, &s.cc, &s.mm, k);
    finish_order(s, k, [dp, dm, xpx, xmx, w.xcxp, w.xcxm, w.cp, w.cm], n, nh, kf);
}

/// p and m of order k from the right-hand sides, the same field operations in both versions
#[inline(always)]
fn finish_order(s: &mut Series, k: usize, r: [F; 8], n: P, nh: P, kf: f64) {
    let [dp, dm, xpx, xmx, xcxp, xcxm, cp, cm] = r;
    let cpm = cp + cm;
    let r3 = (((dp + xpx) - xcxp) + cp) - cpm.mulp(nh);
    let r4 = (((dm + xmx) + xcxm) - cm) + cpm.mulp(nh);
    let mu11 = P::from_f64(1.0 - kf) - nh;
    let mu12 = -nh;
    let mu21 = nh;
    let mu22 = P::from_f64(kf - 1.0) + nh;
    let idel = P::one() / (-(P::from_f64(kf - 1.0) * (P::from_f64(kf - 1.0) + n)));
    s.pp[k] = ((r4.mulp(mu12) - r3.mulp(mu22)) * s.invc).mulp(idel).mul_pwr2(SIG);
    s.mm[k] = ((r3.mulp(mu21) - r4.mulp(mu11)) * s.invc).mulp(idel).mul_pwr2(SIG);
}

/// the bits of the order-k outputs
fn bits(s: &Series, k: usize) -> Vec<u64> {
    [&s.pp, &s.mm, &s.aa, &s.cc, &s.q2, &s.a2]
        .iter()
        .flat_map(|v| v[k].0.iter())
        .flat_map(|j| j.c.iter())
        .flat_map(|q| q.c.iter())
        .flat_map(|x| x.to_array().map(f64::to_bits))
        .collect()
}

fn centre(c: &mut Criterion) {
    let (mut sv, mut si) = (series(), series());
    let z = F::zero();
    let mut w = Scratch {
        u: z,
        sq: z,
        t3: z,
        s1p: z,
        s1m: z,
        xcxp: z,
        xcxm: z,
        cp: z,
        cm: z,
    };
    order_value(&mut sv, K);
    order_in_place(&mut si, K, &mut w);
    let (bv, bi) = (bits(&sv, K), bits(&si, K));
    assert!(bv == bi, "the in-place order differs from the value-returning one");
    assert!(
        bv.iter().all(|&b| f64::from_bits(b).is_finite()),
        "the order is not finite"
    );
    let mut g = c.benchmark_group(format!("centre order {K}, QJet<24>, B = {B}"));
    g.sample_size(10).measurement_time(Duration::from_secs(8));
    g.bench_function("value", |bch| bch.iter(|| order_value(black_box(&mut sv), K)));
    g.bench_function("in place", |bch| {
        bch.iter(|| order_in_place(black_box(&mut si), K, &mut w))
    });
    g.finish();
}

fn sums(c: &mut Criterion) {
    let s = series();
    let (x, y) = (&s.cc, &s.pp);
    let mut g = c.benchmark_group(format!("cauchy sum k = {K}, B = {B}"));
    g.sample_size(20).measurement_time(Duration::from_secs(5));
    let mut o = F::zero();
    g.bench_function("QJet<24> cs", |bch| bch.iter(|| cs(black_box(x), black_box(y), K)));
    g.bench_function("QJet<24> cs_into", |bch| {
        bch.iter(|| cs_into(black_box(&mut o), black_box(x), black_box(y), K))
    });
    g.bench_function("QJet<24> cs_w", |bch| {
        bch.iter(|| cs_w(black_box(x), black_box(y), K, 1, K, |j| j as f64))
    });
    g.bench_function("QJet<24> cs_w_into", |bch| {
        bch.iter(|| cs_w_into(black_box(&mut o), black_box(x), black_box(y), K, 1, K, |j| j as f64))
    });
    // the same values rounded to double-double jets
    let dj = |v: &[F]| -> Vec<Fl<Jet<24>, B>> {
        v.iter()
            .map(|f| Fl(f.0.map(|q| Jet::from_coeffs(q.c.map(|c| c.to_dv())))))
            .collect()
    };
    let (xd, yd) = (dj(x), dj(y));
    let mut od = Fl::<Jet<24>, B>::zero();
    g.bench_function("Jet<24> cs", |bch| bch.iter(|| cs(black_box(&xd), black_box(&yd), K)));
    g.bench_function("Jet<24> cs_into", |bch| {
        bch.iter(|| cs_into(black_box(&mut od), black_box(&xd), black_box(&yd), K))
    });
    // and their values as quad-double lanes
    let qv = |v: &[F]| -> Vec<Fl<QV, B>> { v.iter().map(|f| Fl(f.0.map(|q| q.c[0]))).collect() };
    let (xq, yq) = (qv(x), qv(y));
    let mut oq = Fl::<QV, B>::zero();
    g.bench_function("QV cs", |bch| bch.iter(|| cs(black_box(&xq), black_box(&yq), K)));
    g.bench_function("QV cs_into", |bch| {
        bch.iter(|| cs_into(black_box(&mut oq), black_box(&xq), black_box(&yq), K))
    });
    g.finish();
}

criterion_group!(benches, centre, sums);
criterion_main!(benches);
