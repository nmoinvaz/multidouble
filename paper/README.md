# Error bounds for quad-double style arithmetic on floating-point expansions of any length

[expansion-error-bounds.pdf](expansion-error-bounds.pdf) proves error bounds for the quad-double style algorithms of
Hida, Li and Bailey carried to any number of parts, the algorithms `src/od.rs` runs at eight. Sums and products err by
at most u^n times the exact result plus a second term, at most 2^-15 of the first at eight parts in binary64. Simple
inputs reach the bound. A sum of K products accumulated in levels, as `OdAcc` does, errs by u^n times the exact sum
plus a term that grows like (Ku)^(n+1), and constructed inputs show the growth.

| File | Contents |
|---|---|
| `expansion-error-bounds.tex`, `expansion-error-bounds-appendix.tex`, `expansion-error-bounds-accumulator.tex` | the source; the appendix holds the proofs, the last file those for sums of products |
| `constants.py`, `div_consts.py`, `sqrt_consts.py` | the constants of Theorems 12 and 13, 18, and 21 and 22 in exact rational arithmetic; their outputs are the `.txt` files |
| `fpemu.py` | an emulator of the algorithms in exact arithmetic at any precision and number of parts, written from `src/od.rs` and bit for bit with it on 10,000 inputs per operation |
| `example_n3.py` | the worked example of Section IV on `fpemu.py`, with a control that must fail |
| `sqrt_bits.py` | `fpemu.py`'s square root against multidouble's `OD::sqrt`, bit for bit, with controls that skip its last step and its two-sum of the leading parts |
| `accumulator/` | the accumulator of Theorems 5 and 27 on `fpemu.py` (`acc.py`), its bound in exact rationals (`acc_bound.py`), the constructed and random inputs (`acc_construct.py`, `acc_greedy.py`), their checks with controls (`acc_check.py`), multidouble's `OdAcc` on the constructed inputs (`acc_check/`) and the error recomputed without the emulator (`acc_crate_err.py`); outputs in `accumulator/out/` |

From this folder:

```sh
python3 constants.py     # prints constants.txt
python3 div_consts.py    # prints div_consts.txt
python3 sqrt_consts.py   # prints sqrt_consts.txt
python3 example_n3.py .  # prints PASS
python3 sqrt_bits.py 2000          # prints 2000 inputs, 0 mismatches
python3 sqrt_bits.py 300 1 accumulator/acc_check/Cargo.toml control   # prints 300 inputs, 300 mismatches (control)
python3 sqrt_bits.py 2000 1 accumulator/acc_check/Cargo.toml control2   # prints 2000 inputs, 30 mismatches (control2)
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
