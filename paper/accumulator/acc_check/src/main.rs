//! Runs multidouble on inputs written by the emulator scripts, and prints results as f64 bit patterns in hex.
//! `acc_check acc terms.txt`: OdAcc over the terms (one per line, eight parts), `finish()` of `add` and of
//! `add_prod(a, 1)`. `acc_check add8 ab.txt` / `add4 ab.txt`: a + b for the two lines a and b (OD or QD).
//! `acc_check sqrt8 xs.txt`: the octo-double square root of each line. `acc_check trig8 xs.txt` / `trig2 xs.txt`: the
//! sine, cosine and tangent of each line (OD or DD), on one line. `acc_check exp8|ln8|expdd|lndd xs.txt`: the
//! octo-double or double-double exp or ln of each line. `acc_check addn8|mul8|div8 ab.txt`: a + b, a b or a / b for each
//! line of sixteen parts, a then b. `acc_check addf8|mulf8 af.txt`: a + f or a f for each line of nine parts, a then f.
use multidouble::dd::DD;
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
    let usage = "usage: acc_check acc|add8|add4|sqrt8|trig8|trig2|exp8|ln8|expdd|lndd|addn8|mul8|div8|addf8|mulf8 file";
    let mode = std::env::args().nth(1).expect(usage);
    let path = std::env::args().nth(2).expect(usage);
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
        "trig8" => {
            for line in &lines {
                let x = OD { x: parts(line).try_into().unwrap() };
                println!("{} {} {}", hex(&x.sin().x), hex(&x.cos().x), hex(&x.tan().x));
            }
        }
        "trig2" => {
            for line in &lines {
                let p = parts(line);
                let x = DD { hi: p[0], lo: p[1] };
                let h = |d: DD| hex(&[d.hi, d.lo]);
                println!("{} {} {}", h(x.sin()), h(x.cos()), h(x.tan()));
            }
        }
        "exp8" | "ln8" => {
            for line in &lines {
                let a = OD { x: parts(line).try_into().unwrap() };
                println!("{}", hex(&if mode == "exp8" { a.exp() } else { a.ln() }.x));
            }
        }
        "expdd" | "lndd" => {
            for line in &lines {
                let p = parts(line);
                let a = DD { hi: p[0], lo: p[1] };
                let y = if mode == "expdd" { a.exp() } else { a.ln() };
                println!("{}", hex(&[y.hi, y.lo]));
            }
        }
        "addn8" | "mul8" | "div8" => {
            for line in &lines {
                let p = parts(line);
                let a = OD { x: p[..8].try_into().unwrap() };
                let b = OD { x: p[8..].try_into().unwrap() };
                let y = match mode.as_str() {
                    "addn8" => a + b,
                    "mul8" => a * b,
                    _ => a / b,
                };
                println!("{}", hex(&y.x));
            }
        }
        "addf8" | "mulf8" => {
            for line in &lines {
                let p = parts(line);
                let a = OD { x: p[..8].try_into().unwrap() };
                let y = if mode == "addf8" { a.add_f(p[8]) } else { a.mul_f(p[8]) };
                println!("{}", hex(&y.x));
            }
        }
        _ => panic!("unknown mode"),
    }
}
