//! multidouble side of the comparison with LIB-Dekker-Float (ldf_bench.c, the same method and output format).
//!
//!   md-bench-ldf time DATADIR         timing, one JSON line per (op, mode) on stdout
//!   md-bench-ldf acc  DATADIR OUTDIR  results of every scalar op on the whole input set, raw f64, for acc_eval.py,
//!                                     and the count of lane results that differ from the scalar ones in any bit
//!
//! Throughput: out[i] = op(a[i], b[i]) over N_T independent elements. Latency: x = op(x, b[i]) in one dependent chain
//! (unary ops: blocks of 32 steps, each block's start tied to the previous result by + 0 * x). black_box on the
//! operands before and on the results after every repetition forces each repetition to reload and redo the work.
//! The lane types (DV, QV) run 8 elements per operation; their throughput is per element, their latency per lane
//! operation.

use std::hint::black_box;
use std::time::Instant;

use multidouble::dd::DD;
use multidouble::native::{DV, QV, V8};
use multidouble::qd::QD;

const N_T: usize = 512;
const SAMPLES: usize = 31;
const TARGET_NS: f64 = 300_000.0;
const BLOCK: usize = 32;

fn load(dir: &str, name: &str) -> Vec<f64> {
    let b = std::fs::read(format!("{dir}/{name}.bin")).unwrap_or_else(|e| panic!("{dir}/{name}.bin: {e}"));
    b.chunks_exact(8).map(|c| f64::from_le_bytes(c.try_into().unwrap())).collect()
}

fn save(dir: &str, name: &str, v: &[f64]) {
    let bytes: Vec<u8> = v.iter().flat_map(|x| x.to_le_bytes()).collect();
    std::fs::write(format!("{dir}/md_{name}.bin"), bytes).unwrap();
}

fn dd_of(v: &[f64]) -> Vec<DD> {
    v.chunks_exact(2).map(|c| DD { hi: c[0], lo: c[1] }).collect()
}
fn qd_of(v: &[f64]) -> Vec<QD> {
    v.chunks_exact(4).map(|c| QD { x: [c[0], c[1], c[2], c[3]] }).collect()
}
fn flat_dd(v: &[DD]) -> Vec<f64> {
    v.iter().flat_map(|d| [d.hi, d.lo]).collect()
}
fn flat_qd(v: &[QD]) -> Vec<f64> {
    v.iter().flat_map(|q| q.x).collect()
}

// ---------------------------------------------------------------------------------------------------------------------
// kernels

#[inline(never)]
fn thr<T: Copy, F: Fn(T, T, f64) -> T>(a: &[T], b: &[T], f: &[f64], o: &mut [T], reps: usize, op: F) {
    for _ in 0..reps {
        let (a, b, f) = (black_box(a), black_box(b), black_box(f));
        for ((o, (&x, &y)), &z) in o.iter_mut().zip(a.iter().zip(b)).zip(f) {
            *o = op(x, y, z);
        }
        black_box(&mut *o);
    }
}

#[inline(never)]
fn lat<T: Copy, F: Fn(T, T, f64) -> T>(x0: T, b: &[T], f: &[f64], reps: usize, op: F) -> T {
    let mut x = x0;
    for _ in 0..reps {
        x = x0;
        let (b, f) = (black_box(b), black_box(f));
        for (&y, &z) in b.iter().zip(f) {
            x = op(x, y, z);
        }
        x = black_box(x);
    }
    x
}

#[inline(never)]
fn thr_un<T: Copy, F: Fn(T) -> T>(a: &[T], o: &mut [T], reps: usize, op: F) {
    for _ in 0..reps {
        let a = black_box(a);
        for (o, &x) in o.iter_mut().zip(a) {
            *o = op(x);
        }
        black_box(&mut *o);
    }
}

/// tie(s, x): the block start s made to depend on x (s.hi + 0 x.hi, which is s.hi for finite x)
#[inline(never)]
fn lat_un<T: Copy, F: Fn(T) -> T, G: Fn(T, T) -> T>(a: &[T], reps: usize, op: F, tie: G) -> T {
    let mut x = a[0];
    for _ in 0..reps {
        let a = black_box(a);
        for s in a.iter().step_by(BLOCK) {
            x = tie(*s, x);
            for _ in 0..BLOCK {
                x = op(x);
            }
        }
        x = black_box(x);
    }
    x
}

fn tie_dd(s: DD, x: DD) -> DD {
    DD { hi: s.hi + 0.0 * x.hi, lo: s.lo }
}
fn tie_qd(s: QD, x: QD) -> QD {
    QD { x: [s.x[0] + 0.0 * x.x[0], s.x[1], s.x[2], s.x[3]] }
}

/// lane arrays: part k of element i at parts[k][i]
struct Parts<const P: usize> {
    p: [Vec<f64>; P],
}

impl<const P: usize> Parts<P> {
    fn of(v: &[f64], n: usize) -> Self {
        Parts { p: std::array::from_fn(|k| (0..n).map(|i| v[P * i + k]).collect()) }
    }
    fn zero(n: usize) -> Self {
        Parts { p: std::array::from_fn(|_| vec![0.0; n]) }
    }
}

fn dv_at(x: &Parts<2>, i: usize) -> DV {
    DV::load(&x.p[0][i..], &x.p[1][i..])
}
fn qv_at(x: &Parts<4>, i: usize) -> QV {
    QV::load(&x.p[0][i..], &x.p[1][i..], &x.p[2][i..], &x.p[3][i..])
}

#[inline(never)]
fn thr_dv<F: Fn(DV, DV, V8) -> DV>(a: &Parts<2>, b: &Parts<2>, f: &[f64], o: &mut Parts<2>, reps: usize, op: F) {
    let n = f.len();
    for _ in 0..reps {
        let (a, b, f) = (black_box(a), black_box(b), black_box(f));
        for i in (0..n).step_by(8) {
            let r = op(dv_at(a, i), dv_at(b, i), V8::load(&f[i..]));
            let [h, l] = &mut o.p;
            r.store(&mut h[i..], &mut l[i..]);
        }
        black_box(&mut *o);
    }
}

#[inline(never)]
fn lat_dv<F: Fn(DV, DV, V8) -> DV>(b: &Parts<2>, f: &[f64], reps: usize, op: F) -> DV {
    let n = f.len();
    let x0 = dv_at(b, n - 8);
    let mut x = x0;
    for _ in 0..reps {
        x = x0;
        let (b, f) = (black_box(b), black_box(f));
        for i in (0..n).step_by(8) {
            x = op(x, dv_at(b, i), V8::load(&f[i..]));
        }
        x = black_box(x);
    }
    x
}

#[inline(never)]
fn thr_qv<F: Fn(QV, QV, V8) -> QV>(a: &Parts<4>, b: &Parts<4>, f: &[f64], o: &mut Parts<4>, reps: usize, op: F) {
    let n = f.len();
    for _ in 0..reps {
        let (a, b, f) = (black_box(a), black_box(b), black_box(f));
        for i in (0..n).step_by(8) {
            let r = op(qv_at(a, i), qv_at(b, i), V8::load(&f[i..]));
            let [c0, c1, c2, c3] = &mut o.p;
            r.store(&mut c0[i..], &mut c1[i..], &mut c2[i..], &mut c3[i..]);
        }
        black_box(&mut *o);
    }
}

#[inline(never)]
fn lat_qv<F: Fn(QV, QV, V8) -> QV>(b: &Parts<4>, f: &[f64], reps: usize, op: F) -> QV {
    let n = f.len();
    let x0 = qv_at(b, n - 8);
    let mut x = x0;
    for _ in 0..reps {
        x = x0;
        let (b, f) = (black_box(b), black_box(f));
        for i in (0..n).step_by(8) {
            x = op(x, qv_at(b, i), V8::load(&f[i..]));
        }
        x = black_box(x);
    }
    x
}

#[inline(never)]
fn lat_qv_un<F: Fn(QV) -> QV>(a: &Parts<4>, n: usize, reps: usize, op: F) -> QV {
    let mut x = qv_at(a, 0);
    for _ in 0..reps {
        let a = black_box(a);
        for i in (0..n).step_by(8 * BLOCK) {
            let s = qv_at(a, i);
            // tie the block start to x: c0 + 0 x0
            let mut c = s.c;
            c[0] = c[0].add(V8::splat(0.0).mul(x.c[0]));
            x = QV { c };
            for _ in 0..BLOCK {
                x = op(x);
            }
        }
        x = black_box(x);
    }
    x
}

// ---------------------------------------------------------------------------------------------------------------------
// timing

fn time<F: FnMut(usize)>(op: &str, mode: &str, per_rep: usize, mut call: F, chk: &dyn Fn() -> f64) {
    let t0 = Instant::now();
    call(1);
    let dt = t0.elapsed().as_nanos() as f64;
    let reps = ((TARGET_NS / dt.max(1.0)) as usize).max(1);
    call(reps);
    let mut t = [0.0f64; SAMPLES];
    for s in t.iter_mut() {
        let a0 = Instant::now();
        call(reps);
        *s = a0.elapsed().as_nanos() as f64 / (reps * per_rep) as f64;
    }
    t.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!(
        "{{\"lib\":\"md\",\"op\":\"{op}\",\"mode\":\"{mode}\",\"n\":{per_rep},\"reps\":{reps},\"samples\":{SAMPLES},\
         \"min_ns\":{:.4},\"med_ns\":{:.4},\"max_ns\":{:.4},\"chk\":{:e}}}",
        t[0],
        t[SAMPLES / 2],
        t[SAMPLES - 1],
        chk()
    );
}

macro_rules! dd_ops {
    ($m:ident) => {
        $m!(dd_add, |a: DD, b: DD, _f: f64| a + b);
        $m!(dd_sub, |a: DD, b: DD, _f: f64| a - b);
        $m!(dd_mul, |a: DD, b: DD, _f: f64| a * b);
        $m!(dd_div, |a: DD, b: DD, _f: f64| a / b);
        $m!(dd_mul_f, |a: DD, _b: DD, f: f64| a.mul_f(f));
    };
}
macro_rules! qd_ops {
    ($m:ident) => {
        $m!(qd_add_sloppy, |a: QD, b: QD, _f: f64| a + b);
        $m!(qd_add_ieee, |a: QD, b: QD, _f: f64| a.ieee_add(b));
        $m!(qd_sub_sloppy, |a: QD, b: QD, _f: f64| a - b);
        $m!(qd_sub_ieee, |a: QD, b: QD, _f: f64| a.ieee_sub(b));
        $m!(qd_mul_sloppy, |a: QD, b: QD, _f: f64| a * b);
        $m!(qd_mul_accurate, |a: QD, b: QD, _f: f64| a.accurate_mul(b));
        $m!(qd_div_sloppy, |a: QD, b: QD, _f: f64| a / b);
        $m!(qd_div_accurate, |a: QD, b: QD, _f: f64| a.accurate_div(b));
        $m!(qd_mul_f, |a: QD, _b: QD, f: f64| a.mul_f(f));
        $m!(qd_add_f, |a: QD, _b: QD, f: f64| a.add_f(f));
    };
}
macro_rules! dv_ops {
    ($m:ident) => {
        $m!(dv_add, |a: DV, b: DV, _f: V8| a + b);
        $m!(dv_sub, |a: DV, b: DV, _f: V8| a - b);
        $m!(dv_mul, |a: DV, b: DV, _f: V8| a * b);
        $m!(dv_div, |a: DV, b: DV, _f: V8| a / b);
        $m!(dv_mul_f, |a: DV, _b: DV, f: V8| a.mul_v(f));
    };
}
macro_rules! qv_ops {
    ($m:ident) => {
        $m!(qv_add_sloppy, |a: QV, b: QV, _f: V8| a + b);
        $m!(qv_add_ieee, |a: QV, b: QV, _f: V8| a.ieee_add(b));
        $m!(qv_sub_sloppy, |a: QV, b: QV, _f: V8| a - b);
        $m!(qv_sub_ieee, |a: QV, b: QV, _f: V8| a.ieee_sub(b));
        $m!(qv_mul_sloppy, |a: QV, b: QV, _f: V8| a * b);
        $m!(qv_mul_accurate, |a: QV, b: QV, _f: V8| a.accurate_mul(b));
        $m!(qv_div_sloppy, |a: QV, b: QV, _f: V8| a / b);
        $m!(qv_div_accurate, |a: QV, b: QV, _f: V8| a.accurate_div(b));
        $m!(qv_mul_f, |a: QV, _b: QV, f: V8| a.mul_v(f));
        $m!(qv_add_f, |a: QV, _b: QV, f: V8| a.add_v(f));
    };
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: {} time|acc DATADIR [OUTDIR]", args[0]);
        std::process::exit(2);
    }
    let dir = args[2].as_str();
    let a2 = dd_of(&load(dir, "dd_a"));
    let b2 = dd_of(&load(dir, "dd_b"));
    let ca2 = dd_of(&load(dir, "dd_ca"));
    // the subtractions' cancelling sets take -cb (gen_inputs.py), so that a - b cancels
    let cb2 = dd_of(&load(dir, "dd_cb"));
    let cn2 = dd_of(&load(dir, "dd_cbn"));
    let l2 = dd_of(&load(dir, "lat_dd"));
    let a4 = qd_of(&load(dir, "qd_a"));
    let b4 = qd_of(&load(dir, "qd_b"));
    let ca4 = qd_of(&load(dir, "qd_ca"));
    let cb4 = qd_of(&load(dir, "qd_cb"));
    let cn4 = qd_of(&load(dir, "qd_cbn"));
    let l4 = qd_of(&load(dir, "lat_qd"));
    let fv = load(dir, "f");
    let latf = load(dir, "lat_f");
    let n = fv.len();
    let s4: Vec<QD> = a4.iter().map(|q| q.abs()).collect();
    let mut o2 = vec![DD::ZERO; n];
    let mut o4 = vec![QD::ZERO; n];

    if args[1] == "acc" {
        let out = args.get(3).expect("acc needs OUTDIR").as_str();
        // lane copies of the whole set, for the bitwise check of DV and QV against DD and QD
        let pa2 = Parts::<2>::of(&flat_dd(&a2), n);
        let pb2 = Parts::<2>::of(&flat_dd(&b2), n);
        let pca2 = Parts::<2>::of(&flat_dd(&ca2), n);
        let pcb2 = Parts::<2>::of(&flat_dd(&cb2), n);
        let pa4 = Parts::<4>::of(&flat_qd(&a4), n);
        let pb4 = Parts::<4>::of(&flat_qd(&b4), n);
        let pca4 = Parts::<4>::of(&flat_qd(&ca4), n);
        let pcb4 = Parts::<4>::of(&flat_qd(&cb4), n);
        let ps4 = Parts::<4>::of(&flat_qd(&s4), n);
        let mut po2 = Parts::<2>::zero(n);
        let mut po4 = Parts::<4>::zero(n);
        let mut lane_ops = 0usize;
        let mut lane_bad = 0usize;
        let mut cmp2 = |name: &str, s: &[DD], p: &Parts<2>| {
            let bad = (0..n).filter(|&i| s[i].hi.to_bits() != p.p[0][i].to_bits() || s[i].lo.to_bits() != p.p[1][i].to_bits()).count();
            lane_ops += 1;
            lane_bad += bad;
            if bad > 0 {
                eprintln!("lanes differ: {name} {bad}");
            }
        };
        macro_rules! acc_dd {
            ($name:ident, $op:expr) => {
                thr(&a2, &b2, &fv, &mut o2, 1, $op);
                save(out, stringify!($name), &flat_dd(&o2));
                let cb = if stringify!($name).contains("sub") { &cn2 } else { &cb2 };
                thr(&ca2, cb, &fv, &mut o2, 1, $op);
                save(out, concat!(stringify!($name), "_c"), &flat_dd(&o2));
            };
        }
        dd_ops!(acc_dd);
        macro_rules! acc_dv {
            ($name:ident, $op:expr) => {
                let sname = stringify!($name).replacen("dv", "dd", 1);
                let sop: fn(DD, DD, f64) -> DD = match sname.as_str() {
                    "dd_add" => |a: DD, b: DD, _f: f64| a + b,
                    "dd_sub" => |a: DD, b: DD, _f: f64| a - b,
                    "dd_mul" => |a: DD, b: DD, _f: f64| a * b,
                    "dd_div" => |a: DD, b: DD, _f: f64| a / b,
                    _ => |a: DD, _b: DD, f: f64| a.mul_f(f),
                };
                thr(&a2, &b2, &fv, &mut o2, 1, sop);
                thr_dv(&pa2, &pb2, &fv, &mut po2, 1, $op);
                cmp2(stringify!($name), &o2, &po2);
                thr(&ca2, &cb2, &fv, &mut o2, 1, sop);
                thr_dv(&pca2, &pcb2, &fv, &mut po2, 1, $op);
                cmp2(stringify!($name), &o2, &po2);
            };
        }
        dv_ops!(acc_dv);
        macro_rules! acc_qd {
            ($name:ident, $op:expr) => {
                thr(&a4, &b4, &fv, &mut o4, 1, $op);
                save(out, stringify!($name), &flat_qd(&o4));
                let cb = if stringify!($name).contains("sub") { &cn4 } else { &cb4 };
                thr(&ca4, cb, &fv, &mut o4, 1, $op);
                save(out, concat!(stringify!($name), "_c"), &flat_qd(&o4));
            };
        }
        qd_ops!(acc_qd);
        thr_un(&s4, &mut o4, 1, |a: QD| a.sqrt());
        save(out, "qd_sqrt", &flat_qd(&o4));
        let mut cmp4 = |name: &str, s: &[QD], p: &Parts<4>| {
            let bad = (0..n).filter(|&i| (0..4).any(|k| s[i].x[k].to_bits() != p.p[k][i].to_bits())).count();
            lane_ops += 1;
            lane_bad += bad;
            if bad > 0 {
                eprintln!("lanes differ: {name} {bad}");
            }
        };
        macro_rules! acc_qv {
            ($name:ident, $op:expr) => {
                let sname = stringify!($name).replacen("qv", "qd", 1);
                for (x, y, px, py) in [(&a4, &b4, &pa4, &pb4), (&ca4, &cb4, &pca4, &pcb4)] {
                    let r: Vec<QD> = match sname.as_str() {
                        "qd_add_sloppy" => x.iter().zip(y).map(|(&a, &b)| a + b).collect(),
                        "qd_add_ieee" => x.iter().zip(y).map(|(&a, &b)| a.ieee_add(b)).collect(),
                        "qd_sub_sloppy" => x.iter().zip(y).map(|(&a, &b)| a - b).collect(),
                        "qd_sub_ieee" => x.iter().zip(y).map(|(&a, &b)| a.ieee_sub(b)).collect(),
                        "qd_mul_sloppy" => x.iter().zip(y).map(|(&a, &b)| a * b).collect(),
                        "qd_mul_accurate" => x.iter().zip(y).map(|(&a, &b)| a.accurate_mul(b)).collect(),
                        "qd_div_sloppy" => x.iter().zip(y).map(|(&a, &b)| a / b).collect(),
                        "qd_div_accurate" => x.iter().zip(y).map(|(&a, &b)| a.accurate_div(b)).collect(),
                        "qd_mul_f" => x.iter().zip(&fv).map(|(&a, &f)| a.mul_f(f)).collect(),
                        "qd_add_f" => x.iter().zip(&fv).map(|(&a, &f)| a.add_f(f)).collect(),
                        _ => unreachable!(),
                    };
                    thr_qv(px, py, &fv, &mut po4, 1, $op);
                    cmp4(stringify!($name), &r, &po4);
                }
            };
        }
        qv_ops!(acc_qv);
        {
            let mut ps = Parts::<4>::zero(n);
            for i in (0..n).step_by(8) {
                let [c0, c1, c2, c3] = &mut ps.p;
                qv_at(&ps4, i).sqrt().store(&mut c0[i..], &mut c1[i..], &mut c2[i..], &mut c3[i..]);
            }
            let r: Vec<QD> = s4.iter().map(|q| q.sqrt()).collect();
            cmp4("qv_sqrt", &r, &ps);
        }
        println!("lane checks {lane_ops}, lane results differing from scalar {lane_bad}");
        return;
    }

    if args[1] != "time" {
        eprintln!("unknown mode {}", args[1]);
        std::process::exit(2);
    }
    let sum2 = |v: &[DD]| v[..N_T].iter().map(|d| d.hi + d.lo).sum::<f64>();
    let sum4 = |v: &[QD]| v[..N_T].iter().map(|q| q.x[0] + q.x[1]).sum::<f64>();
    macro_rules! t_dd {
        ($name:ident, $op:expr) => {{
            let o = std::cell::RefCell::new(&mut o2);
            time(
                stringify!($name),
                "thr",
                N_T,
                |r| thr(&a2[..N_T], &b2[..N_T], &fv[..N_T], &mut o.borrow_mut()[..N_T], r, $op),
                &|| sum2(&o.borrow()),
            );
            let x = std::cell::Cell::new(l2[0]);
            time(
                stringify!($name),
                "lat",
                N_T,
                |r| x.set(lat(l2[N_T], &l2[..N_T], &latf[..N_T], r, $op)),
                &|| x.get().hi + x.get().lo,
            );
        }};
    }
    dd_ops!(t_dd);
    macro_rules! t_qd {
        ($name:ident, $op:expr) => {{
            let o = std::cell::RefCell::new(&mut o4);
            time(
                stringify!($name),
                "thr",
                N_T,
                |r| thr(&a4[..N_T], &b4[..N_T], &fv[..N_T], &mut o.borrow_mut()[..N_T], r, $op),
                &|| sum4(&o.borrow()),
            );
            let x = std::cell::Cell::new(l4[0]);
            time(
                stringify!($name),
                "lat",
                N_T,
                |r| x.set(lat(l4[N_T], &l4[..N_T], &latf[..N_T], r, $op)),
                &|| x.get().x[0] + x.get().x[1],
            );
        }};
    }
    qd_ops!(t_qd);
    {
        let o = std::cell::RefCell::new(&mut o4);
        time(
            "qd_sqrt",
            "thr",
            N_T,
            |r| thr_un(&s4[..N_T], &mut o.borrow_mut()[..N_T], r, |a: QD| a.sqrt()),
            &|| sum4(&o.borrow()),
        );
        let x = std::cell::Cell::new(s4[0]);
        time(
            "qd_sqrt",
            "lat",
            N_T,
            |r| x.set(lat_un(&s4[..N_T], r, |a: QD| a.sqrt(), tie_qd)),
            &|| x.get().x[0] + x.get().x[1],
        );
    }
    let _ = tie_dd;

    // lanes: N_T elements as N_T / 8 lane operations
    let pa2 = Parts::<2>::of(&flat_dd(&a2[..N_T]), N_T);
    let pb2 = Parts::<2>::of(&flat_dd(&b2[..N_T]), N_T);
    let pl2 = Parts::<2>::of(&flat_dd(&l2[..N_T]), N_T);
    let pa4 = Parts::<4>::of(&flat_qd(&a4[..N_T]), N_T);
    let pb4 = Parts::<4>::of(&flat_qd(&b4[..N_T]), N_T);
    let pl4 = Parts::<4>::of(&flat_qd(&l4[..N_T]), N_T);
    let ps4 = Parts::<4>::of(&flat_qd(&s4[..N_T]), N_T);
    let po2 = std::cell::RefCell::new(Parts::<2>::zero(N_T));
    let po4 = std::cell::RefCell::new(Parts::<4>::zero(N_T));
    macro_rules! t_dv {
        ($name:ident, $op:expr) => {{
            time(
                stringify!($name),
                "thr",
                N_T,
                |r| thr_dv(&pa2, &pb2, &fv[..N_T], &mut po2.borrow_mut(), r, $op),
                &|| po2.borrow().p[0].iter().sum::<f64>(),
            );
            let x = std::cell::Cell::new(0.0f64);
            time(
                stringify!($name),
                "lat",
                N_T / 8,
                |r| x.set(lat_dv(&pl2, &latf[..N_T], r, $op).lane(0).hi),
                &|| x.get(),
            );
        }};
    }
    dv_ops!(t_dv);
    macro_rules! t_qv {
        ($name:ident, $op:expr) => {{
            time(
                stringify!($name),
                "thr",
                N_T,
                |r| thr_qv(&pa4, &pb4, &fv[..N_T], &mut po4.borrow_mut(), r, $op),
                &|| po4.borrow().p[0].iter().sum::<f64>(),
            );
            let x = std::cell::Cell::new(0.0f64);
            time(
                stringify!($name),
                "lat",
                N_T / 8,
                |r| x.set(lat_qv(&pl4, &latf[..N_T], r, $op).lane(0).x[0]),
                &|| x.get(),
            );
        }};
    }
    qv_ops!(t_qv);
    {
        let zero = Parts::<4>::zero(N_T);
        time(
            "qv_sqrt",
            "thr",
            N_T,
            |r| thr_qv(&ps4, &zero, &fv[..N_T], &mut po4.borrow_mut(), r, |a: QV, _b: QV, _f: V8| a.sqrt()),
            &|| po4.borrow().p[0].iter().sum::<f64>(),
        );
        let x = std::cell::Cell::new(0.0f64);
        time(
            "qv_sqrt",
            "lat",
            N_T / 8,
            |r| x.set(lat_qv_un(&ps4, N_T, r, |a: QV| a.sqrt()).lane(0).x[0]),
            &|| x.get(),
        );
    }
}
