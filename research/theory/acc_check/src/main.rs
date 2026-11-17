//! Runs the crate's OdAcc on the terms of a file (one term per line, eight f64 bit patterns in hex) and prints
//! the eight parts of `finish()` as hex bit patterns, for comparison with the emulator (acc_construct.py).
use multidouble::od::{OdAcc, OD};
use std::io::BufRead;

fn main() {
    let path = std::env::args().nth(1).expect("usage: acc_check terms.txt");
    let f = std::io::BufReader::new(std::fs::File::open(path).unwrap());
    let mut acc = OdAcc::zero();
    let mut acc_p = OdAcc::zero();
    let one = OD { x: [1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0] };
    for line in f.lines() {
        let line = line.unwrap();
        let v: Vec<f64> = line.split_whitespace().map(|h| f64::from_bits(u64::from_str_radix(h, 16).unwrap())).collect();
        let a = OD { x: v.try_into().unwrap() };
        acc = acc.add(a);
        acc_p = acc_p.add_prod(a, one);
    }
    for r in [acc.finish(), acc_p.finish()] {
        println!("{}", r.x.iter().map(|x| format!("{:016x}", x.to_bits())).collect::<Vec<_>>().join(" "));
    }
}
