# Error bounds for quad-double style arithmetic on floating-point expansions of any length

[expansion-error-bounds.pdf](expansion-error-bounds.pdf) proves error bounds for a level scheme in the style of Hida, Li
and Bailey's quad-double algorithms, with TwoSum throughout, at any number of parts: the algorithms `src/od.rs` runs at
eight. It is not the QD library's own code at four parts, and Section II of the paper lists the differences. Sums and
products err by at most u^n times the exact result plus a second term of at most 2^-15 u^n times the operands' leading
parts, |a_0| + |b_0| for a sum and |a_0 b_0| for a product, at eight parts in binary64. Simple inputs reach the bound. A
sum of K products accumulated in levels, as `OdAcc` does, errs by u^n times the exact sum plus a term that grows like
(Ku)^(n+1) times the sum of the products' |a_0 b_0|, and constructed inputs show the growth. The sloppy multiply,
without the last level, errs by at most 2^31.93 u^8 |a_0 b_0|. The sine and cosine err by at most 3.17 u^8 and the
tangent by 6.42 u^8 relative, each with a term from the reduction's 1216 bits of pi/2. The exponential and the
logarithm, built from these operations with part bounds carried through every step, err by at most 3.661 u^8 e^x +
2^-1071 and 9.926 u^8 |ln x| + 2^-509; the logarithm starts from a binary64 logarithm whose error is bounded too. Each
constant is computed by a script of this folder from a proved recursion and printed rounded up.

| File | Contents |
|---|---|
| `expansion-error-bounds.tex`, `expansion-error-bounds-appendix.tex`, `expansion-error-bounds-accumulator.tex`, `expansion-error-bounds-sloppy.tex`, `expansion-error-bounds-trig.tex`, `expansion-error-bounds-explog.tex` | the source; the appendix holds the proofs, the accumulator file those for sums of products, the sloppy file that of the sloppy multiply, the trig file those of the sine, cosine and tangent, and the explog file those of exp and ln |
| `constants.py`, `div_consts.py`, `sqrt_consts.py` | the constants of Theorems 14 and 15, 19, and 21 and 22 in exact rational arithmetic; their outputs are the `.txt` files |
| `trig_consts.py` | the bounds of the sine, cosine and tangent, Theorem 35, in exact rational arithmetic, for the octo-double functions (Lemma 13 at every step, at n = 2, 4, 8 and 12) and the double-double ones (the published double-word bounds); it checks that its series lengths and constants are those of `src/trig/tables.rs`, and `check` adds controls that must raise the bound; its output is `trig_consts.txt` |
| `sloppy_consts.py` | the bound of the opt-in sloppy multiply (`OD::sloppy_mul`) and of sums of its products, Theorem 30, in exact rational arithmetic, with a walk of the algorithm's deposits that checks its two-sum and rounding counts; its output is `sloppy_consts.txt`, and `check` is its control |
| `sloppy_emu.py` | the sloppy multiply on `fpemu.py`, written from its description: hill climbs against `sloppy_consts.py`'s bound at p = 6 to 53 and n = 3 to 8, the crate's worst found pair bit for bit, and a control that must fire |
| `rounding.py` | the directed rounding of every printed bound: an upper bound is printed rounded up and a lower bound down, at the digits shown; run alone it checks itself and prints PASS |
| `fpemu.py` | an emulator of the algorithms in exact arithmetic at any precision and number of parts, written from `src/od.rs` |
| `campaign.py` | the tests of Theorems 9, 15 and 19, Corollary 18 and Proposition 24 on `fpemu.py`: `bits` compares ADD, ADDF, MULF, MUL and DIV with multidouble bit for bit on 10,000 inputs each (through `accumulator/acc_check`) and checks each error against its bound; `small` runs Theorem 9 on every tuple of a family of terms at precision 3 and Theorems 15 and 19 on families of ladders at precisions 5 and 7; `sharp` runs the inputs of Proposition 24; each has controls that must fire; its outputs are in `campaign/` |
| `example_n3.py` | the worked example of Section IV on `fpemu.py`, with a control that must fail |
| `explog_consts.py` | the bounds of the exponential and the logarithm, Theorems 40 and 42, Lemma 43 and Proposition 44, in exact rational arithmetic: Lemma 13 at every operation of the octo-double ones (any n), the published double-word bounds for the double-double ones, and the bound of the start `ln_f64`; `check` samples the convexity the logarithm's chords use |
| `explog_bits.py` | EXP and LOG on `fpemu.py`, written from the appendix's steps: bit for bit against `OD::exp`, `OD::ln`, `DD::exp` and `DD::ln` and within their bounds against Python's correctly rounded exp and ln, with controls that halve the Taylor degree and move the start; `scan` hooks every product, fused multiply-add and quotient for underflow over every binade, and records how far the closest product clears the threshold, with a control at full Taylor degree |
| `review/` | a recomputation of the constants from the appendix's text, written before its author read the scripts above and sharing none of their code: Lemmas 11 and 13 and Theorems 14, 19 and 21 (`gop.py`, checked against Table IV, kappa_DIV and the square root's bound), Theorem 30 (`thm30_sloppy.py`), Theorem 35 on every bucket (`thm35_trig.py`), Theorems 40 and 42 (`thm40_exp.py`, `thm42_log.py`, with `explog_common.py`) and Lemma 43 (`lem43_lnb.py`); each compares with the values the paper quotes, prints PASS, and has a control that must print FAIL; outputs in `review/out/` |
| `sqrt_bits.py` | `fpemu.py`'s square root against multidouble's `OD::sqrt`, bit for bit, with controls that skip its last step and its two-sum of the leading parts |
| `trig_bits.py` | the sine, cosine and tangent of the trig appendix on `fpemu.py`, at eight parts and with the double-word algorithms at two, against multidouble's `OD` and `DD` functions, bit for bit, with controls that halve the sine series and skip the reduction's correction of k; `a2` scans every bucket of the reduced argument from 2^-212 to 1 for results outside binary64 (Remark 37), with the unscaled steps as its control; its output is `trig_bits_a2.txt` |
| `table1_inputs.py` | the inputs of Table V for the square root, sine, cosine, tangent, exponential and logarithm: the emulator's results on them, the exact values enclosed by code of its own (an integer square root, fixed-point Taylor series, Python's decimal exp and ln), the errors as multiples of u^8\|Z\|, and multidouble's bits on the same inputs; `ties_away` and `perturb` are its controls |
| `accumulator/` | the accumulator of Theorems 5 and 27 on `fpemu.py` (`acc.py`), its bound in exact rationals (`acc_bound.py`), the constructed and random inputs (`acc_construct.py`, `acc_greedy.py`), their checks with controls (`acc_check.py`), multidouble's `OdAcc` on the constructed inputs (`acc_check/`) and the error recomputed without the emulator (`acc_crate_err.py`); outputs in `accumulator/out/` |
| `lean/` | Assumption 6, the bounds on rounding after it, Lemma 8, Theorem 9, Lemmas 11 to 13, Theorems 14, 15, 17, 19, 21 and 22 (given the published bounds on its double-word start), the accumulator's lemma and Theorem 27, Theorem 30, Lemmas 33, 34, 38 and 39, Theorem 40 for each case, Proposition 24, and Lemma 41 given its range of `x'_0`, proved in Lean 4 on FloatSpec, a port of Flocq; `lake build` fails on a proof left as `sorry`; its README gives the steps |

From this folder:

```sh
python3 rounding.py      # prints PASS
python3 constants.py     # prints constants.txt
python3 div_consts.py    # prints div_consts.txt
python3 sqrt_consts.py   # prints sqrt_consts.txt
python3 trig_consts.py   # prints trig_consts.txt (about a minute)
python3 trig_consts.py check   # also the controls, prints PASS
python3 explog_consts.py   # prints explog_consts.txt (about 7 minutes)
python3 explog_consts.py check   # prints PASS
python3 explog_bits.py bits 250   # 998, 1500, 748 and 750 inputs, 0 mismatches, none beyond its bound (about 2 minutes)
python3 explog_bits.py bits 20 1 exp_half   # exp8 and expdd mismatch and break their bounds (control)
python3 explog_bits.py bits 20 1 ln_start   # ln8 and lndd mismatch and break their bounds (control)
python3 explog_bits.py scan 2   # 23870 inputs over every binade, no underflowing product but x_0 c_r and the U's, the closest clearing the threshold by 48 binades (about 8 minutes)
python3 explog_bits.py scan 1 full_degree   # products underflow at full Taylor degree (control)
python3 campaign.py sharp   # prints campaign/sharp.txt, ending with PASS
python3 campaign.py small   # prints campaign/small.txt (about 10 minutes)
python3 campaign.py bits    # prints campaign/bits.txt (about a minute)
(cd review && python3 gop.py)            # prints out/gop.txt and PASS; `control` prints FAIL
(cd review && python3 thm30_sloppy.py)   # prints out/thm30_sloppy.txt and PASS; `control` prints FAIL
(cd review && python3 thm35_trig.py all) # prints out/thm35_trig.txt and PASS (about a minute); `control` prints FAIL
(cd review && python3 thm40_exp.py)      # prints out/thm40_exp.txt and PASS (about 2 minutes); `control` prints FAIL
(cd review && python3 thm42_log.py)      # prints out/thm42_log.txt and PASS (about 6 minutes); `control` prints FAIL
(cd review && python3 lem43_lnb.py)      # prints out/lem43_lnb.txt and PASS; `control` prints FAIL
python3 example_n3.py .  # prints PASS
python3 sqrt_bits.py 2000          # prints 2000 inputs, 0 mismatches
python3 sqrt_bits.py 300 1 accumulator/acc_check/Cargo.toml control   # prints 300 inputs, 300 mismatches (control)
python3 sqrt_bits.py 2000 1 accumulator/acc_check/Cargo.toml control2   # prints 2000 inputs, 30 mismatches (control2)
python3 trig_bits.py      # prints 600 inputs, 0 mismatches, for n = 8 and n = 2
python3 trig_bits.py 300 1 accumulator/acc_check/Cargo.toml control    # most mismatch, exit 0
python3 trig_bits.py 600 1 accumulator/acc_check/Cargo.toml control2   # some mismatch, exit 0
python3 trig_bits.py a2 32  # trig_bits_a2.txt, prints a2: PASS (about a minute and a half)
python3 sloppy_consts.py # prints sloppy_consts.txt: Theorem 30, the sloppy multiply's bound, 2^31.9242 u^8 |a_0 b_0| at n = 8
python3 sloppy_consts.py check  # prints PASS
python3 sloppy_emu.py bound     # prints PASS; also bits and control
python3 table1_inputs.py        # six inputs, their errors as multiples of u^8|Z|, prints PASS (about 10 seconds)
python3 table1_inputs.py ties_away   # ties rounded away from zero: 6 of 6 below their quoted ratios (control)
python3 table1_inputs.py perturb     # each leading part one ulp up: 6 of 6 below their quoted ratios (control)
(cd lean && lake build)   # Build completed successfully (about 5 minutes the first time); lean/README.md fetches Mathlib
tectonic -X compile expansion-error-bounds.tex
```

From `accumulator/`:

```sh
python3 acc_bound.py 53 8 2 prod 1 4 8 16 24 32 48 64 128 256 512 1024 2048   # out/acc_bound_n8.txt
python3 acc_bound.py 53 8 2 prod cross 1/8 1   # out/acc_bound_thresholds.txt, with the three lines below
python3 acc_bound.py 53 8 1 prod cross 1/8 1
python3 acc_bound.py 53 8 1 add cross 1/8 1
python3 acc_bound.py 53 8 2 add cross 1/8 1
python3 acc_check.py                           # out/acc_check.txt, prints PASS
python3 acc_construct.py 53 8 2048 none terms.txt   # out/acc_construct_p53_n8_K2048.txt, the terms and the result
for f in 1 0; do python3 acc_greedy.py 53 8 2048 1 11 err $f | tail -1; done   # out/acc_random_p53_n8_K2048.txt
cargo run --release --manifest-path acc_check/Cargo.toml -- acc out/acc_p53_n8_K2048_terms.txt   # out/acc_crate_result_K2048.txt
python3 acc_crate_err.py out/acc_p53_n8_K2048_terms.txt "$(head -1 out/acc_crate_result_K2048.txt)"   # out/acc_crate_err_K2048.txt
```
