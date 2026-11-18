//! A double-double constant meeting octo-double lanes: `mulc`, `addc`, `accc`, `muls`, `mulp` and `addp` of `OV`, `Ou`,
//! `Oun<N>` and `OJet<N>` against the operations they replace, with the constant promoted to octo-double
//! (`OV::from_dv`) and the general product, sum and accumulator applied, as the references below do. Every bit must
//! match, levels of the accumulators included, a NaN equal to any NaN (Rust leaves a NaN result's sign and payload
//! unspecified). The inputs mix random values with every part in use and edge values: zeros of either sign in any
//! part, zero parts between nonzero ones, underflowing and near-overflow values, infinities and NaNs.
//!
//! Control (feature `mutate`): with the new operations' second level one ulp up (`od::mutate::DD_ULP`), every site
//! differs from its reference.
#![allow(clippy::needless_range_loop)]
mod common;
use common::Rng;
use multidouble::dd::DD;
use multidouble::dual::Lane;
use multidouble::native::{ODotAcc, OJet, Ou, Oun, DV, OV};
use multidouble::od::OD;

/// an octo-double h (1 + O(2^-53)) with all eight parts in use
fn od_of(r: &mut Rng, h: f64) -> OD {
    let mut x = [0.0; 8];
    x[0] = h;
    for i in 1..8 {
        x[i] = x[i - 1] * 2f64.powi(-53) * r.sym();
    }
    OD::new(x)
}

/// edge octo-doubles, as given (not renormalized)
fn od_edges() -> Vec<OD> {
    let u = 2f64.powi(-53);
    let o = |x: [f64; 8]| OD { x };
    let f = OD::from_f64;
    vec![
        OD::ZERO,
        f(-0.0),
        o([-0.0; 8]),
        o([0.0, -0.0, 0.0, -0.0, 0.0, -0.0, 0.0, -0.0]),
        OD::ONE,
        f(-1.0),
        f(3.0),
        f(-4503599627370497.0),
        o([1.0, -0.0, -0.0, -0.0, -0.0, -0.0, -0.0, -0.0]),
        o([-1.0, 0.0, u.powi(3), 0.0, 0.0, -u.powi(6), 0.0, 0.0]),
        o([1.5, -u, 0.0, 0.0, 0.0, 0.0, 0.0, u.powi(8)]),
        o([1.0, u, u * u, u.powi(3), u.powi(4), u.powi(5), u.powi(6), u.powi(7)]),
        o([-1e-300, 1e-317, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]),
        o([2f64.powi(-1022), -5e-324, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]),
        f(5e-324),
        o([1e250, 1e233, -1e216, 0.0, 0.0, 0.0, 0.0, 0.0]),
        f(-f64::MAX),
        f(f64::INFINITY),
        f(f64::NAN),
        o([1.0, f64::NAN, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]),
    ]
}

/// edge double-doubles, the low part of either sign or zero
fn dd_edges() -> Vec<DD> {
    let d = |hi: f64, lo: f64| DD { hi, lo };
    let u = 2f64.powi(-53);
    vec![
        d(0.0, 0.0),
        d(-0.0, 0.0),
        d(0.0, -0.0),
        d(-0.0, -0.0),
        d(1.0, 0.0),
        d(-1.0, -0.0),
        d(2.0, 0.0),
        d(3.0, -1.5 * u),
        d(0.1, -5.551115123125783e-18),
        d(-1.0, u / 2.0),
        d(5e-324, 0.0),
        d(-1e-300, 1e-317),
        d(1e300, -1e283),
        d(f64::MAX, 0.0),
        d(f64::NEG_INFINITY, 0.0),
        d(f64::NAN, 0.0),
    ]
}

/// The inputs: octo-double and double-double values, edges one time in four, the rest random at random scales.
struct Pool {
    r: Rng,
    od: Vec<OD>,
    dd: Vec<DD>,
}

impl Pool {
    fn new(seed: u64) -> Pool {
        Pool {
            r: Rng(seed),
            od: od_edges(),
            dd: dd_edges(),
        }
    }
    fn pick(&mut self, n: usize) -> Option<usize> {
        if self.r.next_u64().is_multiple_of(4) {
            Some((self.r.next_u64() % n as u64) as usize)
        } else {
            None
        }
    }
    fn od1(&mut self) -> OD {
        match self.pick(self.od.len()) {
            Some(k) => self.od[k],
            None => {
                let e = (self.r.next_u64() % 61) as i32 - 30;
                let h = self.r.sym() * 2f64.powi(e);
                od_of(&mut self.r, h)
            }
        }
    }
    fn dd1(&mut self) -> DD {
        match self.pick(self.dd.len()) {
            Some(k) => self.dd[k],
            None => {
                let d = self.r.dd(30);
                // an f64 constant one time in four
                if self.r.next_u64().is_multiple_of(4) {
                    DD { hi: d.hi, lo: 0.0 }
                } else {
                    d
                }
            }
        }
    }
    fn ov(&mut self) -> OV {
        let x: [OD; 8] = std::array::from_fn(|_| self.od1());
        OV::from_lanes(&x)
    }
    fn dv(&mut self) -> DV {
        let c: [DD; 8] = std::array::from_fn(|_| self.dd1());
        DV::load(&c.map(|d| d.hi), &c.map(|d| d.lo))
    }
}

/// the bits of the lanes' parts, every NaN as one NaN
fn bits(v: &[OV]) -> Vec<u64> {
    let mut w = Vec::new();
    for x in v {
        for l in x.lanes() {
            w.extend(l.x.map(|p| if p.is_nan() { f64::NAN.to_bits() } else { p.to_bits() }));
        }
    }
    w
}

/// the bits of accumulators' levels and of their sums, every NaN as one NaN
fn acc_bits(a: &[ODotAcc]) -> Vec<u64> {
    let mut w = Vec::new();
    for x in a {
        for l in x.s {
            w.extend(
                l.to_array()
                    .map(|p| if p.is_nan() { f64::NAN.to_bits() } else { p.to_bits() }),
            );
        }
    }
    w.extend(bits(&a.iter().map(|x| x.finish()).collect::<Vec<_>>()));
    w
}

/// An octo-double lane type with its parts as `OV` lane vectors and the operations with a constant as they were
/// before the double-double operations: the constant promoted (`OV::from_dv`), then `*`, `+` and
/// `ODotAcc::add_prod_mut`.
trait Site: Lane<S = multidouble::simd::Native> {
    /// the number of `OV` parts (value, tangents or coefficients)
    const K: usize;
    fn build(v: &[OV]) -> Self;
    fn ovs(&self) -> Vec<OV>;
    fn accs(a: &Self::Acc) -> Vec<ODotAcc>;
    fn ref_mulc(self, c: DV) -> Self;
    fn ref_addc(self, c: DV) -> Self;
    fn ref_accc(a: Self::Acc, x: Self, c: DV) -> Self::Acc;
    /// whether `mulp` and `addp` take a double-double (`Lane::P` = DD)
    const DD_P: bool = true;
}

impl Site for OV {
    const K: usize = 1;
    fn build(v: &[OV]) -> Self {
        v[0]
    }
    fn ovs(&self) -> Vec<OV> {
        vec![*self]
    }
    fn accs(a: &ODotAcc) -> Vec<ODotAcc> {
        vec![*a]
    }
    fn ref_mulc(self, c: DV) -> Self {
        self * OV::from_dv(c)
    }
    fn ref_addc(self, c: DV) -> Self {
        self + OV::from_dv(c)
    }
    fn ref_accc(a: ODotAcc, x: Self, c: DV) -> ODotAcc {
        a.add_prod(x, OV::from_dv(c))
    }
}

impl Site for Ou {
    const K: usize = 2;
    fn build(v: &[OV]) -> Self {
        Ou { v: v[0], d: v[1] }
    }
    fn ovs(&self) -> Vec<OV> {
        vec![self.v, self.d]
    }
    fn accs(a: &Self::Acc) -> Vec<ODotAcc> {
        vec![a.0, a.1]
    }
    fn ref_mulc(self, c: DV) -> Self {
        let c = OV::from_dv(c);
        Ou {
            v: self.v * c,
            d: self.d * c,
        }
    }
    fn ref_addc(self, c: DV) -> Self {
        Ou {
            v: self.v + OV::from_dv(c),
            d: self.d,
        }
    }
    fn ref_accc(a: Self::Acc, x: Self, c: DV) -> Self::Acc {
        let c = OV::from_dv(c);
        let mut a = a;
        a.0.add_prod_mut(&x.v, &c);
        a.1.add_prod_mut(&x.d, &c);
        a
    }
}

impl<const N: usize> Site for Oun<N> {
    const K: usize = 1 + N;
    fn build(v: &[OV]) -> Self {
        Oun {
            v: v[0],
            d: std::array::from_fn(|k| v[1 + k]),
        }
    }
    fn ovs(&self) -> Vec<OV> {
        [&[self.v][..], &self.d[..]].concat()
    }
    fn accs(a: &Self::Acc) -> Vec<ODotAcc> {
        [&[a.0][..], &a.1[..]].concat()
    }
    fn ref_mulc(self, c: DV) -> Self {
        let c = OV::from_dv(c);
        Oun {
            v: self.v * c,
            d: self.d.map(|x| x * c),
        }
    }
    fn ref_addc(self, c: DV) -> Self {
        Oun {
            v: self.v + OV::from_dv(c),
            d: self.d,
        }
    }
    fn ref_accc(a: Self::Acc, x: Self, c: DV) -> Self::Acc {
        let c = OV::from_dv(c);
        let mut a = a;
        a.0.add_prod_mut(&x.v, &c);
        for k in 0..N {
            a.1[k].add_prod_mut(&x.d[k], &c);
        }
        a
    }
}

impl<const N: usize> Site for OJet<N> {
    const K: usize = N;
    const DD_P: bool = false;
    fn build(v: &[OV]) -> Self {
        OJet {
            c: std::array::from_fn(|k| v[k]),
        }
    }
    fn ovs(&self) -> Vec<OV> {
        self.c.to_vec()
    }
    fn accs(a: &Self::Acc) -> Vec<ODotAcc> {
        a.to_vec()
    }
    fn ref_mulc(self, c: DV) -> Self {
        let c = OV::from_dv(c);
        OJet {
            c: self.c.map(|x| x * c),
        }
    }
    fn ref_addc(self, c: DV) -> Self {
        let mut j = self;
        j.c[0] = self.c[0] + OV::from_dv(c);
        j
    }
    fn ref_accc(a: Self::Acc, x: Self, c: DV) -> Self::Acc {
        let c = OV::from_dv(c);
        let mut a = a;
        for k in 0..N {
            a[k].add_prod_mut(&x.c[k], &c);
        }
        a
    }
}

/// `mulp` and `addp` with a double-double parameter, where `Lane::P` is DD (`muls` and `addc` of the splat)
trait DdParam: Site {
    fn mulp_dd(self, p: DD) -> Self;
    fn addp_dd(self, p: DD) -> Self;
}

macro_rules! dd_param_site {
    ($($t:ty),*) => {
        $(impl DdParam for $t {
            fn mulp_dd(self, p: DD) -> Self {
                self.mulp(p)
            }
            fn addp_dd(self, p: DD) -> Self {
                self.addp(p)
            }
        })*
    };
}
dd_param_site!(OV, Ou, Oun<2>, Oun<3>);

impl<const N: usize> DdParam for OJet<N> {
    fn mulp_dd(self, _p: DD) -> Self {
        unreachable!()
    }
    fn addp_dd(self, _p: DD) -> Self {
        unreachable!()
    }
}

/// The mismatches of every site of T against its reference over n random and edge inputs, by site name: `mulc`,
/// `addc`, `muls`, `mulp`, `addp`, and `accc` into an empty accumulator and into one holding a product.
fn mismatches<T: DdParam>(n: usize, seed: u64) -> Vec<(&'static str, usize)> {
    let mut p = Pool::new(seed);
    let mut out = vec![
        ("mulc", 0),
        ("addc", 0),
        ("muls", 0),
        ("mulp", 0),
        ("addp", 0),
        ("accc, empty", 0),
        ("accc, holding a product", 0),
    ];
    let mut add = |site: usize, a: Vec<u64>, b: Vec<u64>| out[site].1 += (a != b) as usize;
    for _ in 0..n {
        let x = T::build(&(0..T::K).map(|_| p.ov()).collect::<Vec<_>>());
        let y = T::build(&(0..T::K).map(|_| p.ov()).collect::<Vec<_>>());
        let c = p.dv();
        let s = p.dd1();
        add(0, bits(&x.mulc(c).ovs()), bits(&x.ref_mulc(c).ovs()));
        add(1, bits(&x.addc(c).ovs()), bits(&x.ref_addc(c).ovs()));
        add(2, bits(&x.muls(s).ovs()), bits(&x.ref_mulc(DV::splat(s)).ovs()));
        if T::DD_P {
            add(3, bits(&x.mulp_dd(s).ovs()), bits(&x.ref_mulc(DV::splat(s)).ovs()));
            add(4, bits(&x.addp_dd(s).ovs()), bits(&x.ref_addc(DV::splat(s)).ovs()));
        }
        for (site, start) in [(5, T::acc0()), (6, T::acc(T::acc0(), y, x))] {
            add(
                site,
                acc_bits(&T::accs(&T::accc(start, x, c))),
                acc_bits(&T::accs(&T::ref_accc(start, x, c))),
            );
        }
    }
    if !T::DD_P {
        out.retain(|(s, _)| *s != "mulp" && *s != "addp");
    }
    out
}

/// every site of every type, as "type site" and its mismatches
fn all_mismatches(n: usize, seed: u64) -> Vec<(String, usize)> {
    let mut out = Vec::new();
    let mut put = |t: &str, m: Vec<(&'static str, usize)>| {
        out.extend(m.into_iter().map(|(s, k)| (format!("{t} {s}"), k)));
    };
    put("OV", mismatches::<OV>(n, seed));
    put("Ou", mismatches::<Ou>(n, seed + 1));
    put("Oun<2>", mismatches::<Oun<2>>(n, seed + 2));
    put("Oun<3>", mismatches::<Oun<3>>(n, seed + 3));
    put("OJet<1>", mismatches::<OJet<1>>(n, seed + 4));
    put("OJet<4>", mismatches::<OJet<4>>(n, seed + 5));
    out
}

/// Pass: at every site of every type, every bit of 1000 random and edge inputs (8 lanes each) matches the reference.
#[test]
fn dd_constant_sites_are_the_promoted_operations() {
    let ms = all_mismatches(1000, 0xdd01);
    let bad: Vec<&(String, usize)> = ms.iter().filter(|(_, k)| *k > 0).collect();
    println!("{} sites checked", ms.len());
    assert!(bad.is_empty(), "sites differing from the promoted operation: {bad:?}");
}

/// Control: with the double-double operations' second level one ulp up, every site differs from its reference on
/// some of 200 inputs.
#[cfg(feature = "mutate")]
#[test]
fn dd_constant_sites_control() {
    use multidouble::od::mutate;
    mutate::set(mutate::DD_ULP);
    let ms = all_mismatches(200, 0xdd02);
    mutate::set(0);
    for (s, k) in &ms {
        println!("{s}: {k} of 200 differ");
    }
    let quiet: Vec<&(String, usize)> = ms.iter().filter(|(_, k)| *k == 0).collect();
    assert!(quiet.is_empty(), "sites the control did not change: {quiet:?}");
}
