# Error bounds for quad-double style arithmetic on floating-point expansions of any length

[expansion-error-bounds.pdf](expansion-error-bounds.pdf) proves error bounds for the quad-double style algorithms of
Hida, Li and Bailey carried to any number of parts, the algorithms `src/od.rs` runs at eight. Sums and products err by
at most u^n times the exact result plus a second term, at most 2^-15 of the first at eight parts in binary64. Simple
inputs reach the bound.

| File | Contents |
|---|---|
| `expansion-error-bounds.tex`, `expansion-error-bounds-appendix.tex` | the source; the appendix holds the proofs |
| `constants.py`, `div_consts.py`, `sqrt_consts.py` | the constants of Theorems 11 and 12, 17, and 19 and 20 in exact rational arithmetic; their outputs are the `.txt` files |
| `fpemu.py` | an emulator of the algorithms in exact arithmetic at any precision and number of parts, written from `src/od.rs` and bit for bit with it on 10,000 inputs per operation |
| `example_n3.py` | the worked example of Section 4 on `fpemu.py`, with a control that must fail |

From this folder:

```sh
python3 constants.py     # prints constants.txt
python3 div_consts.py    # prints div_consts.txt
python3 sqrt_consts.py   # prints sqrt_consts.txt
python3 example_n3.py .  # prints PASS
tectonic -X compile expansion-error-bounds.tex
```
