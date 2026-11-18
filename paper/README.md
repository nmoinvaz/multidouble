# Error bounds for quad-double style arithmetic on floating-point expansions of any length

[expansion-error-bounds.pdf](expansion-error-bounds.pdf) proves error bounds for the quad-double style algorithms of
Hida, Li and Bailey carried to any number of parts, the algorithms `src/od.rs` runs at eight. Sums and products err by
at most u^n times the exact result plus a second term, at most 2^-15 of the first at eight parts in binary64. Simple
inputs reach the bound. A sum of K products accumulated in levels, as `OdAcc` does, errs by u^n times the exact sum
plus a term that grows like (Ku)^(n+1), and constructed inputs show the growth. The exponential and the logarithm, built from these
operations with part bounds carried through every step, err by at most 3.661 u^8 e^x + 2^-1071 and 9.926 u^8 |ln x| +
2^-509; the logarithm starts from a binary64 logarithm whose error is proved too.

| File | Contents |
|---|---|
| `expansion-error-bounds.tex`, `expansion-error-bounds-appendix.tex`, `expansion-error-bounds-accumulator.tex`, `expansion-error-bounds-sloppy.tex`, `expansion-error-bounds-trig.tex`, `expansion-error-bounds-explog.tex` | the source; the appendix holds the proofs, the accumulator file those for sums of products, the sloppy file that of the sloppy multiply, the trig file those of the sine, cosine and tangent, and the explog file those of exp and ln |
| `constants.py`, `div_consts.py`, `sqrt_consts.py` | the constants of Theorems 12 and 13, 18, and 21 and 22 in exact rational arithmetic; their outputs are the `.txt` files |
| `trig_consts.py` | the bounds of the sine, cosine and tangent, Theorem 34, in exact rational arithmetic, for the octo-double functions (Lemma 20 at every step, at n = 2, 4, 8 and 12) and the double-double ones (the published double-word bounds); it checks that its series lengths and constants are those of `src/trig/tables.rs`, and `check` adds controls that must raise the bound; its output is `trig_consts.txt` |
| `sloppy_consts.py` | the bound of the opt-in sloppy multiply (`OD::sloppy_mul`) and of sums of its products, Theorem 30, in exact rational arithmetic, with a walk of the algorithm's deposits that checks its two-sum and rounding counts; `check` is its control |
| `sloppy_emu.py` | the sloppy multiply on `fpemu.py`, written from its description: hill climbs against `sloppy_consts.py`'s bound at p = 6 to 53 and n = 3 to 8, the crate's worst found pair bit for bit, and a control that must fire |
| `fpemu.py` | an emulator of the algorithms in exact arithmetic at any precision and number of parts, written from `src/od.rs` and bit for bit with it on 10,000 inputs per operation |
| `example_n3.py` | the worked example of Section IV on `fpemu.py`, with a control that must fail |
| `explog_consts.py` | the bounds of the exponential and the logarithm, Theorems 34 and 36, Lemma 37 and Proposition 38, in exact rational arithmetic: Lemma 20 at every operation of the octo-double ones (any n), the published double-word bounds for the double-double ones, and the bound of the start `ln_f64`; `check` samples the convexity the logarithm's chords use |
| `explog_bits.py` | EXP and LOG on `fpemu.py`, written from the appendix's steps: bit for bit against `OD::exp`, `OD::ln`, `DD::exp` and `DD::ln` and within their bounds against Python's correctly rounded exp and ln, with controls that halve the Taylor degree and move the start; `scan` hooks every product, fused multiply-add and quotient for underflow over every binade, with a control at full Taylor degree |
| `review/` | a reviewer's recomputation of Theorems 34 and 36 from an earlier text of the appendix, sharing no code with `explog_consts.py` (`indep_exp.py`, `indep_log.py`, rationals rounded to nearest at 420 bits): the same largest cases, 3.66006045 u^8, 9.925819 u^8 and 2^-509.17 to nearest, which `explog_consts.txt` gives rounded up as 3.660061 u^8, 9.925819 u^8 and 2^-509.16 |
| `sqrt_bits.py` | `fpemu.py`'s square root against multidouble's `OD::sqrt`, bit for bit, with controls that skip its last step and its two-sum of the leading parts |
| `trig_bits.py` | the sine, cosine and tangent of the trig appendix on `fpemu.py`, at eight parts and with the double-word algorithms at two, against multidouble's `OD` and `DD` functions, bit for bit, with controls that halve the sine series and skip the reduction's correction of k; `a2` scans every bucket of the reduced argument from 2^-212 to 1 for results outside binary64 (Remark 36), with the unscaled steps as its control; its output is `trig_bits_a2.txt` |
| `accumulator/` | the accumulator of Theorems 5 and 27 on `fpemu.py` (`acc.py`), its bound in exact rationals (`acc_bound.py`), the constructed and random inputs (`acc_construct.py`, `acc_greedy.py`), their checks with controls (`acc_check.py`), multidouble's `OdAcc` on the constructed inputs (`acc_check/`) and the error recomputed without the emulator (`acc_crate_err.py`); outputs in `accumulator/out/` |

From this folder:

```sh
python3 constants.py     # prints constants.txt
python3 div_consts.py    # prints div_consts.txt
python3 sqrt_consts.py   # prints sqrt_consts.txt
python3 trig_consts.py   # prints trig_consts.txt (about a minute)
python3 trig_consts.py check   # also the controls, prints PASS
python3 explog_consts.py   # prints explog_consts.txt (about 7 minutes)
python3 explog_consts.py check   # prints PASS
python3 explog_bits.py bits 250   # 998, 1250, 748 and 750 inputs, 0 mismatches, none beyond its bound (about 2 minutes)
python3 explog_bits.py bits 20 1 exp_half   # exp8 and expdd mismatch and break their bounds (control)
python3 explog_bits.py bits 20 1 ln_start   # ln8 and lndd mismatch and break their bounds (control)
python3 explog_bits.py scan 2   # 23870 inputs over every binade, no underflowing product but x_0 Lambda and U (about 6 minutes)
python3 explog_bits.py scan 1 full_degree   # products underflow at full Taylor degree (control)
(cd review && python3 indep_exp.py)   # 3.660060... u^8, Theorem 34
(cd review && python3 indep_log.py)   # k != 0: 9.925819 u^8, Theorem 36 (about 3 minutes)
python3 example_n3.py .  # prints PASS
python3 sqrt_bits.py 2000          # prints 2000 inputs, 0 mismatches
python3 sqrt_bits.py 300 1 accumulator/acc_check/Cargo.toml control   # prints 300 inputs, 300 mismatches (control)
python3 sqrt_bits.py 2000 1 accumulator/acc_check/Cargo.toml control2   # prints 2000 inputs, 30 mismatches (control2)
python3 trig_bits.py      # prints 600 inputs, 0 mismatches, for n = 8 and n = 2
python3 trig_bits.py 300 1 accumulator/acc_check/Cargo.toml control    # most mismatch, exit 0
python3 trig_bits.py 600 1 accumulator/acc_check/Cargo.toml control2   # some mismatch, exit 0
python3 trig_bits.py a2 32  # trig_bits_a2.txt, prints a2: PASS (about a minute and a half)
python3 sloppy_consts.py # Theorem 30, the sloppy multiply's bound, 2^31.9242 u^8 |a_0 b_0| at n = 8
python3 sloppy_consts.py check  # prints PASS
python3 sloppy_emu.py bound     # prints PASS; also bits and control
tectonic -X compile expansion-error-bounds.tex
```

From `accumulator/`:

```sh
python3 acc_bound.py 53 8 2 prod 1 4 8 16 24 32 48 64 128 256 512 1024 2048   # out/acc_bound_n8.txt
python3 acc_bound.py 53 8 2 prod cross 1/8 1   # out/acc_bound_thresholds.txt, with 1 prod and 1 add
python3 acc_check.py                           # out/acc_check.txt, prints PASS
python3 acc_construct.py 53 8 2048 none terms.txt   # out/acc_construct_p53_n8_K2048.txt, the terms and the result
for f in 1 0; do python3 acc_greedy.py 53 8 2048 1 11 err $f | tail -1; done   # out/acc_random_p53_n8_K2048.txt
cargo run --release --manifest-path acc_check/Cargo.toml -- acc out/acc_p53_n8_K2048_terms.txt   # out/acc_crate_result_K2048.txt
python3 acc_crate_err.py out/acc_p53_n8_K2048_terms.txt "$(head -1 out/acc_crate_result_K2048.txt)"   # out/acc_crate_err_K2048.txt
```
