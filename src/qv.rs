//! 8 lanes of quad-double: four `V8` registers (structure of arrays, part k of the 8 lanes in `c[k]`), with the
//! algorithms of the scalar `qd::QD` and bitwise the same results lane by lane, on every `v8` backend (AVX-512,
//! 2 x AVX2, portable).
//!
//! The QD library's algorithms branch on the data in two places, and both are run here on all lanes with masks:
//! - the renormalization's second pass skips zero error terms. Written with a per-lane slot index k (the part being
//!   filled), each step is: `(t, e) = quick_two_sum(s[k], c); s[k] = t; s[k+1] = e; k += (e != 0);` with the
//!   five-part version's last step at k = 3 keeping only t (QD's `s3 += c4`). k is held as threshold masks
//!   (k >= 1, k >= 2, k >= 3) and the slots updated by selects; the zero test is the same `!=` as QD's.
//! - the accurate add merges the eight parts by magnitude. Each lane keeps its own read positions i, j (as f64) and
//!   output position k; every step reads `a[i]`, `b[j]` by selects, and lanes that have finished are frozen. The loop
//!   runs at most seven steps and stops early once all eight lanes are done.
//!
//! `QDotAcc` accumulates a sum of quad-double products, in the spirit of `dv::DotAcc`: each product is expanded to
//! its partial products by order (a0b0; a0b1, a1b0 and the error of a0b0; ...; the O(eps^3) products by FMA, the
//! O(eps^4) ones dropped, as in the sloppy multiply), and level l of the accumulator (l = 0..3) sums the order-l
//! terms with error-free two-sums whose errors go to level l + 1; level 4 sums in plain f64 (Ogita-Rump-Oishi SumK,
//! per order). `finish` adds the five levels with qd + f64. The two-sum errors of adding into a running level sum are
//! relative to that sum, not to the terms, so the levels grow (level 3 to about n^1.5 2^-159 sum |a_i b_i|): a first
//! design that summed level 3 in plain f64, with those errors mixed into the per-term ones, gave errors growing
//! like n (72 u at n = 512, u = 2^-209). Here every running-sum error enters the next level by its own two-sum,
//! level 4 is the only plain sum, and the error is that of the dropped O(eps^4) partial products and of `finish`.
//! It costs about a third of a sloppy multiply plus a sloppy add.
use crate::dd::DD;
use crate::dv::{quick_two_sum, two_prod, two_sum, DV};
use crate::qd::{mutate, QD};
use crate::simd::Simd;
use crate::v8::{M8, V8};
use std::ops::{Add, Div, Mul, Neg, Sub};

// Inlining: the hot operations (renormalizations, sloppy add and multiply, times and plus f64, the accumulator) run
// through `Simd::hot`, forced inline on AVX2 and AVX-512 and left to the compiler on the other backends. The other
// large operations are never forced, and run inside `Simd::vectorize`, so that a copy the compiler keeps out of line
// still runs with the backend's instructions.

#[derive(Clone, Copy, Debug)]
pub struct QV<S: Simd> {
    pub c: [V8<S>; 4],
}

#[inline(always)]
fn three_sum<S: Simd>(a: V8<S>, b: V8<S>, c: V8<S>) -> (V8<S>, V8<S>, V8<S>) {
    let (t1, t2) = two_sum(a, b);
    let (a, t3) = two_sum(c, t1);
    let (b, c) = two_sum(t2, t3);
    (a, b, c)
}

#[inline(always)]
fn three_sum2<S: Simd>(a: V8<S>, b: V8<S>, c: V8<S>) -> (V8<S>, V8<S>) {
    let (t1, t2) = two_sum(a, b);
    let (a, t3) = two_sum(c, t1);
    (a, t2.add(t3))
}

#[inline(always)]
fn is_inf<S: Simd>(x: V8<S>) -> M8<S> {
    x.abs().eq(V8::splat(f64::INFINITY))
}

/// QD's renormalization of four parts, all lanes (see the module doc)
#[inline(always)]
pub fn renorm4<S: Simd>(c0: V8<S>, c1: V8<S>, c2: V8<S>, c3: V8<S>) -> [V8<S>; 4] {
    S::hot(
        #[inline(always)]
        || {
            let z = V8::zero();
            let inf = is_inf(c0);
            let (o0, o1, o2, o3) = (c0, c1, c2, c3);
            let (s, c3) = quick_two_sum(c2, c3);
            let (s, c2) = quick_two_sum(c1, s);
            let (c0, c1) = if mutate::on(mutate::RENORM_P1) {
                (c0.add(s), z)
            } else {
                quick_two_sum(c0, s)
            };
            // second pass: slots s0..s3, k >= 1 where c1 != 0
            let (mut s0, mut s1, mut s2, mut s3) = (c0, c1, z, z);
            let k1 = c1.ne(z);
            // step c2 (k in {0, 1})
            let (t, e) = quick_two_sum(k1.sel(s1, s0), c2);
            s0 = k1.sel(s0, t);
            s1 = k1.sel(t, e);
            s2 = k1.sel(e, s2);
            let ne = e.ne(z);
            let (ka, kb) = if mutate::on(mutate::QV_RENORM_MASK) {
                (k1, k1)
            } else {
                (k1.or(ne), k1.and(ne))
            };
            // step c3 (k in {0, 1, 2}): k >= 1 is ka, k >= 2 is kb
            let (t, e) = quick_two_sum(kb.sel(s2, ka.sel(s1, s0)), c3);
            s0 = ka.sel(s0, t);
            s1 = kb.sel(s1, ka.sel(t, e));
            s2 = kb.sel(t, ka.sel(e, s2));
            s3 = kb.sel(e, s3);
            [inf.sel(o0, s0), inf.sel(o1, s1), inf.sel(o2, s2), inf.sel(o3, s3)]
        },
    )
}

/// QD's renormalization of five parts to four, all lanes (see the module doc)
#[inline(always)]
pub fn renorm5<S: Simd>(c0: V8<S>, c1: V8<S>, c2: V8<S>, c3: V8<S>, c4: V8<S>) -> [V8<S>; 4] {
    S::hot(
        #[inline(always)]
        || {
            let z = V8::zero();
            let inf = is_inf(c0);
            let (o0, o1, o2, o3) = (c0, c1, c2, c3);
            let (s, c4) = quick_two_sum(c3, c4);
            let (s, c3) = quick_two_sum(c2, s);
            let (s, c2) = quick_two_sum(c1, s);
            let (c0, c1) = if mutate::on(mutate::RENORM_P1) {
                (c0.add(s), z)
            } else {
                quick_two_sum(c0, s)
            };
            let (mut s0, mut s1, mut s2, mut s3) = (c0, c1, z, z);
            let k1 = c1.ne(z);
            // step c2 (k in {0, 1})
            let (t, e) = quick_two_sum(k1.sel(s1, s0), c2);
            s0 = k1.sel(s0, t);
            s1 = k1.sel(t, e);
            s2 = k1.sel(e, s2);
            let ne = e.ne(z);
            let (ka, kb) = if mutate::on(mutate::QV_RENORM_MASK) {
                (k1, k1)
            } else {
                (k1.or(ne), k1.and(ne))
            };
            // step c3 (k in {0, 1, 2})
            let (t, e) = quick_two_sum(kb.sel(s2, ka.sel(s1, s0)), c3);
            s0 = ka.sel(s0, t);
            s1 = kb.sel(s1, ka.sel(t, e));
            s2 = kb.sel(t, ka.sel(e, s2));
            s3 = kb.sel(e, s3);
            let ne = e.ne(z);
            let (ka, kb, kc) = (ka.or(ne), kb.or(ka.and(ne)), kb.and(ne));
            // step c4 (k in {0..3}; at k = 3 only the sum is kept)
            let (t, e) = quick_two_sum(kc.sel(s3, kb.sel(s2, ka.sel(s1, s0))), c4);
            s0 = ka.sel(s0, t);
            s1 = kb.sel(s1, ka.sel(t, e));
            s2 = kc.sel(s2, kb.sel(t, ka.sel(e, s2)));
            s3 = kc.sel(t, kb.sel(e, s3));
            [inf.sel(o0, s0), inf.sel(o1, s1), inf.sel(o2, s2), inf.sel(o3, s3)]
        },
    )
}

/// arr[idx] per lane for idx in {0, 1, 2, 3} held as f64 (idx 4: arr[3], never used)
#[inline(always)]
fn pick<S: Simd>(arr: &[V8<S>; 4], idx: V8<S>) -> V8<S> {
    let mut h = arr[0];
    h = idx.ge(V8::splat(1.0)).sel(arr[1], h);
    h = idx.ge(V8::splat(2.0)).sel(arr[2], h);
    idx.ge(V8::splat(3.0)).sel(arr[3], h)
}

/// a0 b3 + a1 b2 + a2 b1 + a3 b0 by FMA in QD's order (as qd::eps3)
#[inline(always)]
fn eps3<S: Simd>(a: &[V8<S>; 4], b: &[V8<S>; 4]) -> V8<S> {
    a[3].fma(b[0], a[2].fma(b[1], a[1].fma(b[2], a[0].mul(b[3]))))
}

/// a1 b3 + a2 b2 + a3 b1 by FMA in QD's order (as qd::eps4)
#[inline(always)]
fn eps4<S: Simd>(a: &[V8<S>; 4], b: &[V8<S>; 4]) -> V8<S> {
    a[3].fma(b[1], a[2].fma(b[2], a[1].mul(b[3])))
}

impl<S: Simd> QV<S> {
    #[inline(always)]
    pub fn zero() -> Self {
        QV { c: [V8::zero(); 4] }
    }
    #[inline(always)]
    pub fn splat(x: QD) -> Self {
        QV { c: x.x.map(V8::splat) }
    }
    #[inline(always)]
    pub fn splat_f(x: f64) -> Self {
        let z = V8::zero();
        QV {
            c: [V8::splat(x), z, z, z],
        }
    }
    #[inline(always)]
    pub fn splat_dd(x: DD) -> Self {
        let z = V8::zero();
        QV {
            c: [V8::splat(x.hi), V8::splat(x.lo), z, z],
        }
    }
    /// exact
    #[inline(always)]
    pub fn from_dv(x: DV<S>) -> Self {
        let z = V8::zero();
        QV { c: [x.hi, x.lo, z, z] }
    }
    /// double-double, to about 2^-106 relative (as QD::to_dd)
    #[inline(always)]
    pub fn to_dv(self) -> DV<S> {
        let (h, l) = quick_two_sum(self.c[0], self.c[1].add(self.c[2].add(self.c[3])));
        DV { hi: h, lo: l }
    }
    /// nearest f64 (as QD::to_f64)
    #[inline(always)]
    pub fn to_v8(self) -> V8<S> {
        self.c[0].add(self.c[1].add(self.c[2].add(self.c[3])))
    }
    /// from the four parts' arrays (8 values each)
    #[inline(always)]
    pub fn load(c0: &[f64], c1: &[f64], c2: &[f64], c3: &[f64]) -> Self {
        QV {
            c: [V8::load(c0), V8::load(c1), V8::load(c2), V8::load(c3)],
        }
    }
    #[inline(always)]
    pub fn store(self, c0: &mut [f64], c1: &mut [f64], c2: &mut [f64], c3: &mut [f64]) {
        self.c[0].store(c0);
        self.c[1].store(c1);
        self.c[2].store(c2);
        self.c[3].store(c3);
    }
    pub fn from_lanes(x: &[QD; 8]) -> Self {
        let mut c = [[0.0f64; 8]; 4];
        for (j, q) in x.iter().enumerate() {
            for k in 0..4 {
                c[k][j] = q.x[k];
            }
        }
        QV {
            c: c.map(V8::from_array),
        }
    }
    #[inline(always)]
    pub fn lane(self, j: usize) -> QD {
        QD {
            x: self.c.map(|v| v.to_array()[j]),
        }
    }
    pub fn lanes(self) -> [QD; 8] {
        let a = self.c.map(|v| v.to_array());
        std::array::from_fn(|j| QD {
            x: [a[0][j], a[1][j], a[2][j], a[3][j]],
        })
    }
    /// all lanes = lane j
    #[inline(always)]
    pub fn bcast(self, j: usize) -> Self {
        QV {
            c: self.c.map(|v| v.bcast(j)),
        }
    }
    /// |leading part|
    #[inline(always)]
    pub fn abs_hi(self) -> V8<S> {
        self.c[0].abs()
    }
    #[inline]
    pub fn abs(self) -> Self {
        S::vectorize(
            #[inline(always)]
            || {
                let neg = V8::zero().gt(self.c[0]);
                let n = -self;
                QV {
                    c: [0, 1, 2, 3].map(|k| neg.sel(n.c[k], self.c[k])),
                }
            },
        )
    }
    /// times a power of two b (`dd::is_pwr2`): every part scaled, exact barring overflow and underflow
    #[inline(always)]
    pub fn mul_pwr2(self, b: f64) -> Self {
        debug_assert!(crate::dd::is_pwr2(b), "mul_pwr2: {b} is not a power of two");
        let b = V8::splat(b);
        QV {
            c: self.c.map(|v| v.mul(b)),
        }
    }

    // ---------------------------------------------------------------------------------------------------------
    // additions
    // ---------------------------------------------------------------------------------------------------------

    /// the sloppy add (the default `+`), as QD::sloppy_add
    #[inline(always)]
    pub fn sloppy_add(self, b: Self) -> Self {
        S::hot(
            #[inline(always)]
            || {
                let (a, b) = (self.c, b.c);
                let (s0, t0) = two_sum(a[0], b[0]);
                let t0 = if mutate::on(mutate::SLOPPY_ADD_T0) {
                    V8::zero()
                } else {
                    t0
                };
                let (s1, t1) = two_sum(a[1], b[1]);
                let (s2, t2) = two_sum(a[2], b[2]);
                let (s3, t3) = two_sum(a[3], b[3]);
                let (s1, t0) = two_sum(s1, t0);
                let (s2, t0, t1) = three_sum(s2, t0, t1);
                let (s3, t0) = three_sum2(s3, t0, t2);
                let t0 = t0.add(t1).add(t3);
                QV {
                    c: renorm5(s0, s1, s2, s3, t0),
                }
            },
        )
    }

    /// the accurate merge add, as QD::ieee_add (QD's algorithm with its last part u + v when all parts are read with
    /// three emitted; see the module doc and QD::ieee_add)
    #[inline]
    pub fn ieee_add(self, b: Self) -> Self {
        S::vectorize(
            #[inline(always)]
            || {
                let (a, b) = (self.c, b.c);
                let z = V8::zero();
                let one = V8::splat(1.0);
                let four = V8::splat(4.0);
                let gt = |x: V8<S>, y: V8<S>| {
                    if mutate::on(mutate::IEEE_ADD_ORDER) {
                        y.abs().gt(x.abs())
                    } else {
                        x.abs().gt(y.abs())
                    }
                };
                // the first two parts
                let ta = gt(a[0], b[0]);
                let u = ta.sel(a[0], b[0]);
                let mut i = ta.sel(one, z);
                let mut j = ta.sel(z, one);
                let (ha, hb) = (pick(&a, i), pick(&b, j));
                let ta = gt(ha, hb);
                let v = ta.sel(ha, hb);
                i = i.add(ta.sel(one, z));
                j = j.add(ta.sel(z, one));
                let (mut u, mut v) = quick_two_sum(u, v);
                let mut x = [z; 4];
                let mut k = z;
                let mut done = z.ne(z); // all false
                                        // lanes that read every part with three emitted keep v as a fifth term (renorm5 below), as QD::ieee_add
                let mut fifth = z;
                let mut five = z.ne(z);
                for _ in 0..7 {
                    let ea = i.ge(four);
                    let eb = j.ge(four);
                    // all parts read: x[k] = u, x[k+1] = v (k < 3), or x[3] = u and v as a fifth term (k = 3); stop
                    let fin = done.not().and(ea.and(eb));
                    for m in 0..4 {
                        let at = fin.and(k.eq(V8::splat(m as f64)));
                        if m < 3 {
                            x[m] = at.sel(u, x[m]);
                            x[m + 1] = at.sel(v, x[m + 1]);
                        } else {
                            x[m] = at.sel(u, x[m]);
                            fifth = at.sel(v, fifth);
                            five = five.or(at);
                        }
                    }
                    done = done.or(fin);
                    let act = done.not();
                    // the next part by magnitude
                    let ia = if mutate::on(mutate::QV_IEEE_HEAD) {
                        i.add(one)
                    } else {
                        i
                    };
                    let (ha, hb) = (pick(&a, ia), pick(&b, j));
                    let take_a = ea.not().and(eb.or(gt(ha, hb)));
                    let t = take_a.sel(ha, hb);
                    i = i.add(act.and(take_a).sel(one, z));
                    j = j.add(act.and(take_a.not()).sel(one, z));
                    // quick_three_accum(u, v, t)
                    let (s, bb) = two_sum(v, t);
                    let (s, aa) = two_sum(u, s);
                    let za = aa.ne(z);
                    let zb = bb.ne(z);
                    let both = za.and(zb);
                    u = act.sel(both.sel(aa, s), u);
                    v = act.sel(zb.sel(bb, aa), v);
                    let ret = both.sel(s, z);
                    // a part that does not fit: x[k++] = ret
                    let w = act.and(ret.ne(z));
                    for m in 0..4 {
                        x[m] = w.and(k.eq(V8::splat(m as f64))).sel(ret, x[m]);
                    }
                    k = k.add(w.sel(one, z));
                    done = done.or(k.ge(four));
                    if done.bits() == 0xff {
                        break;
                    }
                }
                // the parts not read go into x[3], a's first, in order
                for kk in 0..4 {
                    x[3] = i.ge(V8::splat(kk as f64 + 1.0)).sel(x[3], x[3].add(a[kk]));
                }
                for kk in 0..4 {
                    x[3] = j.ge(V8::splat(kk as f64 + 1.0)).sel(x[3], x[3].add(b[kk]));
                }
                let r4 = renorm4(x[0], x[1], x[2], x[3]);
                if five.bits() == 0 {
                    return QV { c: r4 };
                }
                let r5 = renorm5(x[0], x[1], x[2], x[3], fifth);
                QV {
                    c: [
                        five.sel(r5[0], r4[0]),
                        five.sel(r5[1], r4[1]),
                        five.sel(r5[2], r4[2]),
                        five.sel(r5[3], r4[3]),
                    ],
                }
            },
        )
    }

    #[inline]
    pub fn ieee_sub(self, b: Self) -> Self {
        self.ieee_add(-b)
    }

    /// qd + exact f64 vector, as QD::add_f
    #[inline(always)]
    pub fn add_v(self, b: V8<S>) -> Self {
        S::hot(
            #[inline(always)]
            || {
                let a = self.c;
                let (c0, e) = two_sum(a[0], b);
                let e = if mutate::on(mutate::ADD_F_E) { V8::zero() } else { e };
                let (c1, e) = two_sum(a[1], e);
                let (c2, e) = two_sum(a[2], e);
                let (c3, e) = two_sum(a[3], e);
                QV {
                    c: renorm5(c0, c1, c2, c3, e),
                }
            },
        )
    }
    #[inline(always)]
    pub fn add_f(self, b: f64) -> Self {
        self.add_v(V8::splat(b))
    }

    /// qd + dd, as QD::add_dd
    #[inline]
    pub fn add_dv(self, b: DV<S>) -> Self {
        S::vectorize(
            #[inline(always)]
            || {
                let a = self.c;
                let (s0, t0) = two_sum(a[0], b.hi);
                let (s1, t1) = two_sum(a[1], b.lo);
                let t1 = if mutate::on(mutate::ADD_DD_T1) { V8::zero() } else { t1 };
                let (s1, t0) = two_sum(s1, t0);
                let (s2, t0, t1) = three_sum(a[2], t0, t1);
                let (s3, t0) = two_sum(t0, a[3]);
                let t0 = t0.add(t1);
                QV {
                    c: renorm5(s0, s1, s2, s3, t0),
                }
            },
        )
    }

    // ---------------------------------------------------------------------------------------------------------
    // multiplications
    // ---------------------------------------------------------------------------------------------------------

    /// times an exact f64 vector, as QD::mul_f
    #[inline(always)]
    pub fn mul_v(self, b: V8<S>) -> Self {
        S::hot(
            #[inline(always)]
            || {
                let a = self.c;
                let (p0, q0) = two_prod(a[0], b);
                let (p1, q1) = two_prod(a[1], b);
                let q1 = if mutate::on(mutate::MUL_F_Q1) { V8::zero() } else { q1 };
                let (p2, q2) = two_prod(a[2], b);
                let p3 = a[3].mul(b);
                let s0 = p0;
                let (s1, s2) = two_sum(q0, p1);
                let (s2, q1, p2) = three_sum(s2, q1, p2);
                let (q1, q2) = three_sum2(q1, q2, p3);
                let s3 = q1;
                let s4 = q2.add(p2);
                QV {
                    c: renorm5(s0, s1, s2, s3, s4),
                }
            },
        )
    }
    #[inline(always)]
    pub fn mul_f(self, b: f64) -> Self {
        self.mul_v(V8::splat(b))
    }

    /// times double-double lanes, as QD::mul_dd
    #[inline]
    pub fn mul_dv(self, b: DV<S>) -> Self {
        S::vectorize(
            #[inline(always)]
            || {
                let a = self.c;
                let (p0, q0) = two_prod(a[0], b.hi);
                let (p1, q1) = two_prod(a[0], b.lo);
                let q1 = if mutate::on(mutate::MUL_DD_Q1) { V8::zero() } else { q1 };
                let (p2, q2) = two_prod(a[1], b.hi);
                let (p3, q3) = two_prod(a[1], b.lo);
                let (p4, q4) = two_prod(a[2], b.hi);
                let (p1, p2, q0) = three_sum(p1, p2, q0);
                let (p2, p3, p4) = three_sum(p2, p3, p4);
                let (q1, q2) = two_sum(q1, q2);
                let (s0, t0) = two_sum(p2, q1);
                let (s1, t1) = two_sum(p3, q2);
                let (s1, t0) = two_sum(s1, t0);
                let s2 = t0.add(t1).add(p4);
                let p2 = s0;
                let p3 = a[3].fma(b.hi, a[2].mul(b.lo)).add(q3).add(q4);
                let (p3, q0) = three_sum2(p3, q0, s1);
                let p4 = q0.add(s2);
                QV {
                    c: renorm5(p0, p1, p2, p3, p4),
                }
            },
        )
    }

    /// the sloppy multiply (the default `*`), as QD::sloppy_mul
    #[inline(always)]
    pub fn sloppy_mul(self, b: Self) -> Self {
        S::hot(
            #[inline(always)]
            || {
                let (a, b) = (self.c, b.c);
                let (p0, q0) = two_prod(a[0], b[0]);
                let q0 = if mutate::on(mutate::SLOPPY_MUL_Q0) {
                    V8::zero()
                } else {
                    q0
                };
                let (p1, q1) = two_prod(a[0], b[1]);
                let (p2, q2) = two_prod(a[1], b[0]);
                let (p3, q3) = two_prod(a[0], b[2]);
                let q3 = if mutate::on(mutate::SLOPPY_MUL_Q3) {
                    V8::zero()
                } else {
                    q3
                };
                let (p4, q4) = two_prod(a[1], b[1]);
                let (p5, q5) = two_prod(a[2], b[0]);
                let (p1, p2, q0) = three_sum(p1, p2, q0);
                let (p2, q1, q2) = three_sum(p2, q1, q2);
                let (p3, p4, p5) = three_sum(p3, p4, p5);
                let (s0, t0) = two_sum(p2, p3);
                let (s1, t1) = two_sum(q1, p4);
                let s2 = q2.add(p5);
                let (s1, t0) = two_sum(s1, t0);
                let s2 = s2.add(t0.add(t1));
                let r = eps3(&a, &b).add(q0).add(q3).add(q4).add(q5);
                let s1 = s1.add(r);
                QV {
                    c: renorm5(p0, p1, s0, s1, s2),
                }
            },
        )
    }

    /// the accurate multiply, as QD::accurate_mul
    #[inline]
    pub fn accurate_mul(self, b: Self) -> Self {
        S::vectorize(
            #[inline(always)]
            || {
                let (a, b) = (self.c, b.c);
                let (p0, q0) = two_prod(a[0], b[0]);
                let (p1, q1) = two_prod(a[0], b[1]);
                let q1 = if mutate::on(mutate::ACCURATE_MUL_Q1) {
                    V8::zero()
                } else {
                    q1
                };
                let (p2, q2) = two_prod(a[1], b[0]);
                let (p3, q3) = two_prod(a[0], b[2]);
                let (p4, q4) = two_prod(a[1], b[1]);
                let (p5, q5) = two_prod(a[2], b[0]);
                let (p1, p2, q0) = three_sum(p1, p2, q0);
                let (p2, q1, q2) = three_sum(p2, q1, q2);
                let (p3, p4, p5) = three_sum(p3, p4, p5);
                let (s0, t0) = two_sum(p2, p3);
                let (s1, t1) = two_sum(q1, p4);
                let s2 = q2.add(p5);
                let (s1, t0) = two_sum(s1, t0);
                let s2 = s2.add(t0.add(t1));
                let (p6, q6) = two_prod(a[0], b[3]);
                let (p7, q7) = two_prod(a[1], b[2]);
                let (p8, q8) = two_prod(a[2], b[1]);
                let (p9, q9) = two_prod(a[3], b[0]);
                let (q0, q3) = two_sum(q0, q3);
                let (q4, q5) = two_sum(q4, q5);
                let (p6, p7) = two_sum(p6, p7);
                let (p8, p9) = two_sum(p8, p9);
                let (t0, t1) = two_sum(q0, q4);
                let t1 = t1.add(q3.add(q5));
                let (r0, r1) = two_sum(p6, p8);
                let r1 = r1.add(p7.add(p9));
                let (q3, q4) = two_sum(t0, r0);
                let q4 = q4.add(t1.add(r1));
                let (t0, t1) = two_sum(q3, s1);
                let t1 = t1.add(q4);
                let r = eps4(&a, &b).add(q6).add(q7).add(q8).add(q9).add(s2);
                let t1 = t1.add(r);
                QV {
                    c: renorm5(p0, p1, s0, t0, t1),
                }
            },
        )
    }

    /// the square, as QD::sqr
    #[inline]
    pub fn sqr(self) -> Self {
        S::vectorize(
            #[inline(always)]
            || {
                let a = self.c;
                let two = V8::splat(2.0);
                let a0x2 = two.mul(a[0]);
                let (p0, q0) = two_prod(a[0], a[0]);
                let (p1, q1) = two_prod(a0x2, a[1]);
                let (p2, q2) = two_prod(a0x2, a[2]);
                let (p3, q3) = two_prod(a[1], a[1]);
                let (p1, q0) = two_sum(q0, p1);
                let (q0, q1) = two_sum(q0, q1);
                let (p2, p3) = two_sum(p2, p3);
                let (s0, t0) = two_sum(q0, p2);
                let (s1, t1) = two_sum(q1, p3);
                let (s1, t0) = two_sum(s1, t0);
                let t0 = t0.add(t1);
                let (s1, t0) = quick_two_sum(s1, t0);
                let (p2, t1) = quick_two_sum(s0, s1);
                let (p3, q0) = quick_two_sum(t1, t0);
                let p4 = a0x2.mul(a[3]);
                let p5 = two.mul(a[1]).mul(a[2]);
                let (p4, p5) = two_sum(p4, p5);
                let (q2, q3) = two_sum(q2, q3);
                let (t0, t1) = two_sum(p4, q2);
                let t1 = t1.add(p5).add(q3);
                let (p3, p4) = two_sum(p3, t0);
                let p4 = p4.add(q0).add(t1);
                QV {
                    c: renorm5(p0, p1, p2, p3, p4),
                }
            },
        )
    }

    // ---------------------------------------------------------------------------------------------------------
    // division, square root
    // ---------------------------------------------------------------------------------------------------------

    /// the sloppy divide (the default `/`), as QD::sloppy_div
    #[inline]
    pub fn sloppy_div(self, b: Self) -> Self {
        S::vectorize(
            #[inline(always)]
            || {
                let q0 = self.c[0].div(b.c[0]);
                let r = self - b.mul_v(q0);
                let q1 = r.c[0].div(b.c[0]);
                let r = r - b.mul_v(q1);
                let q2 = r.c[0].div(b.c[0]);
                let r = if mutate::on(mutate::DIV_R3) { r } else { r - b.mul_v(q2) };
                let q3 = r.c[0].div(b.c[0]);
                QV {
                    c: renorm4(q0, q1, q2, q3),
                }
            },
        )
    }

    /// the accurate divide, as QD::accurate_div
    #[inline]
    pub fn accurate_div(self, b: Self) -> Self {
        S::vectorize(
            #[inline(always)]
            || {
                let q0 = self.c[0].div(b.c[0]);
                let r = self - b.mul_v(q0);
                let q1 = r.c[0].div(b.c[0]);
                let r = r - b.mul_v(q1);
                let q2 = r.c[0].div(b.c[0]);
                let r = if mutate::on(mutate::DIV_R3) { r } else { r - b.mul_v(q2) };
                let q3 = r.c[0].div(b.c[0]);
                let r = r - b.mul_v(q3);
                let q4 = r.c[0].div(b.c[0]);
                QV {
                    c: renorm5(q0, q1, q2, q3, q4),
                }
            },
        )
    }

    #[inline]
    pub fn recip(self) -> Self {
        QV::splat_f(1.0) / self
    }

    /// the square root, as QD::sqrt (scaled by a power of four into [1, 4); zero lanes give zero)
    #[inline]
    pub fn sqrt(self) -> Self {
        S::vectorize(
            #[inline(always)]
            || {
                let z = V8::zero();
                let one = V8::splat(1.0);
                let zero = self.c[0].eq(z);
                let s = self.c[0].sqrt().pow2_floor();
                let inv = one.div(s);
                let a = QV {
                    c: self.c.map(|v| v.mul(inv).mul(inv)),
                };
                let mut r = QV {
                    c: [one.div(a.c[0].sqrt()), z, z, z],
                };
                let h = a.mul_pwr2(0.5);
                let n = if mutate::on(mutate::SQRT_ITER) { 1 } else { 3 };
                for _ in 0..n {
                    r = r + (-(h * r.sqr())).add_f(0.5) * r;
                }
                let r = r * a;
                QV {
                    c: r.c.map(|v| zero.sel(z, v.mul(s))),
                }
            },
        )
    }
}

impl<S: Simd> Neg for QV<S> {
    type Output = Self;
    #[inline(always)]
    fn neg(self) -> Self {
        let z = V8::zero();
        QV {
            c: self.c.map(|v| z.sub(v)),
        }
    }
}

impl<S: Simd> Add for QV<S> {
    type Output = Self;
    #[inline(always)]
    fn add(self, b: Self) -> Self {
        self.sloppy_add(b)
    }
}

impl<S: Simd> Sub for QV<S> {
    type Output = Self;
    #[inline(always)]
    fn sub(self, b: Self) -> Self {
        self.sloppy_add(-b)
    }
}

impl<S: Simd> Mul for QV<S> {
    type Output = Self;
    #[inline(always)]
    fn mul(self, b: Self) -> Self {
        self.sloppy_mul(b)
    }
}

impl<S: Simd> Div for QV<S> {
    type Output = Self;
    #[inline(always)]
    fn div(self, b: Self) -> Self {
        self.sloppy_div(b)
    }
}

/// Accumulator for sums of quad-double products (see the module doc); the 8-lane twin of `qd::QdAcc`.
#[derive(Clone, Copy, Debug)]
pub struct QDotAcc<S: Simd> {
    pub s: [V8<S>; 5],
}

impl<S: Simd> QDotAcc<S> {
    #[inline(always)]
    pub fn zero() -> Self {
        QDotAcc { s: [V8::zero(); 5] }
    }
    /// self + a b
    #[inline(always)]
    pub fn add_prod(self, a: QV<S>, b: QV<S>) -> Self {
        S::hot(
            #[inline(always)]
            || {
                let (a, b) = (a.c, b.c);
                let (p00, e00) = two_prod(a[0], b[0]);
                let (p01, e01) = two_prod(a[0], b[1]);
                let (p10, e10) = two_prod(a[1], b[0]);
                let (p02, e02) = two_prod(a[0], b[2]);
                let (p11, e11) = two_prod(a[1], b[1]);
                let (p20, e20) = two_prod(a[2], b[0]);
                let r3 = eps3(&a, &b);
                let (s0, t0) = two_sum(self.s[0], p00);
                let (x1, y1) = two_sum(p01, p10);
                let (x2, y2) = two_sum(e00, t0);
                let (x3, y3) = two_sum(x1, x2);
                let (s1, y4) = two_sum(self.s[1], x3);
                let (z1, w1) = two_sum(p02, p20);
                let (z2, w2) = two_sum(p11, e01);
                let (z3, w3) = two_sum(e10, y1);
                let (z4, w4) = two_sum(y2, y3);
                let (z5, w5) = two_sum(z1, z2);
                let (z6, w6) = two_sum(z3, z4);
                let (z7, w7) = two_sum(z5, z6);
                let (z8, w8) = two_sum(z7, y4);
                let (s2, w9) = two_sum(self.s[2], z8);
                let (w, w9) = if mutate::on(mutate::ACC_L3) {
                    (V8::zero(), V8::zero())
                } else {
                    (w1.add(w2).add(w3.add(w4)).add(w5.add(w6).add(w7.add(w8))), w9)
                };
                let r = w.add(r3).add(e02.add(e11)).add(e20);
                let (s3, x9) = two_sum(self.s[3], w9);
                let (s3, x10) = two_sum(s3, r);
                QDotAcc {
                    s: [s0, s1, s2, s3, self.s[4].add(x9.add(x10))],
                }
            },
        )
    }
    /// self + a
    #[inline(always)]
    pub fn add(self, a: QV<S>) -> Self {
        S::hot(
            #[inline(always)]
            || {
                let a = a.c;
                let (s0, t0) = two_sum(self.s[0], a[0]);
                let (x1, y1) = two_sum(a[1], t0);
                let (s1, y2) = two_sum(self.s[1], x1);
                let (z1, w1) = two_sum(a[2], y1);
                let (z2, w2) = two_sum(z1, y2);
                let (s2, w3) = two_sum(self.s[2], z2);
                let r = w1.add(w2).add(a[3]);
                let (s3, x3) = two_sum(self.s[3], w3);
                let (s3, x4) = two_sum(s3, r);
                QDotAcc {
                    s: [s0, s1, s2, s3, self.s[4].add(x3.add(x4))],
                }
            },
        )
    }
    #[inline(always)]
    pub fn finish(self) -> QV<S> {
        S::hot(
            #[inline(always)]
            || {
                let z = V8::zero();
                QV {
                    c: [self.s[0], z, z, z],
                }
                .add_v(self.s[1])
                .add_v(self.s[2])
                .add_v(self.s[3])
                .add_v(self.s[4])
            },
        )
    }
}

// ---------------------------------------------------------------------------------------------------------------
// quad-double lanes as a `Lane`
// ---------------------------------------------------------------------------------------------------------------

/// Quad-double values as a `Lane`, so that code generic over `Lane` compiles and runs with quad-double lanes. The
/// trait passes constants and inputs as double-double (`DV`): they enter exactly (`from_dv`) but carry only
/// double-double accuracy, and `val` rounds back to double-double. So this instantiation computes in quad-double with
/// double-double data.
impl<S: Simd> crate::dual::Lane for QV<S> {
    type S = S;
    type Acc = QDotAcc<S>;
    const TANGENT: bool = false;
    #[inline(always)]
    fn zero() -> Self {
        QV::zero()
    }
    #[inline(always)]
    fn cst(c: DV<S>) -> Self {
        QV::from_dv(c)
    }
    #[inline(always)]
    fn mulc(self, c: DV<S>) -> Self {
        self * QV::from_dv(c)
    }
    #[inline(always)]
    fn mulf(self, s: f64) -> Self {
        self.mul_f(s)
    }
    #[inline(always)]
    fn mul_pwr2(self, s: f64) -> Self {
        QV::mul_pwr2(self, s)
    }
    #[inline(always)]
    fn addc(self, c: DV<S>) -> Self {
        self + QV::from_dv(c)
    }
    #[inline(always)]
    fn bcast(self, j: usize) -> Self {
        QV::bcast(self, j)
    }
    #[inline(always)]
    fn val(self) -> DV<S> {
        self.to_dv()
    }
    #[inline(always)]
    fn tan(self) -> DV<S> {
        DV::zero()
    }
    #[inline(always)]
    fn from_vt(v: DV<S>, _t: DV<S>) -> Self {
        QV::from_dv(v)
    }
    #[inline(always)]
    fn acc0() -> QDotAcc<S> {
        QDotAcc::zero()
    }
    #[inline(always)]
    fn acc(a: QDotAcc<S>, x: Self, y: Self) -> QDotAcc<S> {
        a.add_prod(x, y)
    }
    #[inline(always)]
    fn accc(a: QDotAcc<S>, x: Self, c: DV<S>) -> QDotAcc<S> {
        a.add_prod(x, QV::from_dv(c))
    }
    #[inline(always)]
    fn acc1(a: QDotAcc<S>, x: Self) -> QDotAcc<S> {
        a.add(x)
    }
    #[inline(always)]
    fn fin(a: QDotAcc<S>) -> Self {
        a.finish()
    }
}
