//! Runs multidouble on inputs written by the emulator scripts, and prints results as f64 bit patterns in hex.
//! `acc_check acc terms.txt`: OdAcc over the terms (one per line, eight parts), `finish()` of `add` and of
//! `add_prod(a, 1)`. `acc_check add8 ab.txt` / `add4 ab.txt`: a + b for the two lines a and b (OD or QD).
//! `acc_check sqrt8 xs.txt`: the octo-double square root of each line.
use multidouble::od::{OdAcc, OD};
use multidouble::qd::QD;
use std::io::BufRead;

fn parts(line: &str) -> Vec<f64> {
    line.split_whitespace().map(|h| f64::from_bits(u64::from_str_radix(h, 16).unwrap())).collect()
}

fn hex(x: &[f64]) -> String {
    x.iter().map(|x| format!("{:016x}", x.to_bits())).collect::<Vec<_>>().join(" ")
}

fn main() {
    let mode = std::env::args().nth(1).expect("usage: acc_check acc|add8|add4|sqrt8 file");
    let path = std::env::args().nth(2).expect("usage: acc_check acc|add8|add4|sqrt8 file");
    let lines: Vec<String> = std::io::BufReader::new(std::fs::File::open(path).unwrap()).lines().map(|l| l.unwrap()).collect();
    match mode.as_str() {
        "acc" => {
            let mut acc = OdAcc::zero();
            let mut acc_p = OdAcc::zero();
            let one = OD { x: [1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0] };
            for line in &lines {
                let a = OD { x: parts(line).try_into().unwrap() };
                acc = acc.add(a);
                acc_p = acc_p.add_prod(a, one);
            }
            println!("{}", hex(&acc.finish().x));
            println!("{}", hex(&acc_p.finish().x));
        }
        "add8" => {
            let a = OD { x: parts(&lines[0]).try_into().unwrap() };
            let b = OD { x: parts(&lines[1]).try_into().unwrap() };
            println!("{}", hex(&(a + b).x));
        }
        "add4" => {
            let a = QD { x: parts(&lines[0]).try_into().unwrap() };
            let b = QD { x: parts(&lines[1]).try_into().unwrap() };
            println!("{}", hex(&(a + b).x));
        }
        "sqrt8" => {
            for line in &lines {
                println!("{}", hex(&OD { x: parts(line).try_into().unwrap() }.sqrt().x));
            }
        }
        _ => panic!("unknown mode"),
    }
}
