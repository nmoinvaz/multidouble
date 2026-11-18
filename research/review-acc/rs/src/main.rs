//! The referee's driver of multidouble's OdAcc: reads commands on stdin, one per line, f64 parts as 16 hex digits
//! of their bits (big-endian), and prints the accumulator's levels and finish().
//!   X a0..a7          acc.add(a)
//!   P a0..a7 b0..b7   acc.add_prod(a, b)
//!   F                 print "L s0..s8" and "R x0..x7" (finish), the accumulator unchanged
//!   Z                 reset to zero
//!   M a0..a7 b0..b7   print "M x0..x7", a * b
//!   A a0..a7 b        print "A x0..x7", a.add_f(b)
//! With the feature mutate, the first argument selects multidouble's mutation id.
use multidouble::od::{OdAcc, OD};
use std::io::{self, BufRead, Write};

fn f(h: &str) -> f64 {
    f64::from_bits(u64::from_str_radix(h, 16).expect("hex"))
}

fn od(w: &[&str]) -> OD {
    OD { x: std::array::from_fn(|i| f(w[i])) }
}

fn hx(v: &[f64]) -> String {
    v.iter().map(|x| format!("{:016x}", x.to_bits())).collect::<Vec<_>>().join(" ")
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    #[cfg(feature = "mutate")]
    if args.len() > 1 {
        multidouble::od::mutate::set(args[1].parse().unwrap());
    }
    #[cfg(not(feature = "mutate"))]
    assert!(args.len() == 1, "build with --features mutate to select a mutation");
    let stdin = io::stdin();
    let mut out = io::BufWriter::new(io::stdout());
    let mut acc = OdAcc::zero();
    for line in stdin.lock().lines() {
        let line = line.unwrap();
        let w: Vec<&str> = line.split_whitespace().collect();
        if w.is_empty() {
            continue;
        }
        match w[0] {
            "X" => acc = acc.add(od(&w[1..9])),
            "P" => acc = acc.add_prod(od(&w[1..9]), od(&w[9..17])),
            "F" => {
                writeln!(out, "L {}", hx(&acc.s)).unwrap();
                writeln!(out, "R {}", hx(&acc.finish().x)).unwrap();
            }
            "Z" => acc = OdAcc::zero(),
            "M" => writeln!(out, "M {}", hx(&(od(&w[1..9]) * od(&w[9..17])).x)).unwrap(),
            "A" => writeln!(out, "A {}", hx(&od(&w[1..9]).add_f(f(w[9])).x)).unwrap(),
            c => panic!("unknown command {c}"),
        }
    }
}
