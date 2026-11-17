"""Bits per octo-double for Blosc-style layouts and filters, simulated with numpy and stdlib codecs, for the size chart
of docs/pack.md (scripts/pack_graphs.py). Input: files of octo-doubles as 8 little-endian f64 parts each. Values
interleaved or as eight part arrays, raw, byte-shuffled (byte k of every element together, Blosc's SHUFFLE) or
bit-shuffled (BITSHUFFLE), each with zlib -9 and lzma -9; and the same after replacing each lower part's exponent
field by its drop below the part above (an exponent-delta filter).

usage: python3 scripts/pack_sizes.py values.bin ..."""
import sys, zlib, lzma
import numpy as np

def parts(f):
    return np.fromfile(f, dtype='<f8').reshape(-1, 8)

def byteshuffle(a):  # a: (m,) uint64 -> bytes grouped by byte position
    return a.view(np.uint8).reshape(-1, 8).T.copy().tobytes()

def bitshuffle(a):
    bits = np.unpackbits(a.view(np.uint8).reshape(-1, 8), axis=1, bitorder='little')  # (m, 64)
    return np.packbits(bits.T.copy(), axis=1, bitorder='little').tobytes()

def delta_exp(P):  # replace lower parts' exponent fields by the drop from the previous part (zero parts kept)
    B = P.view(np.uint64).copy()
    E = (B >> np.uint64(52)) & np.uint64(0x7ff)
    for k in range(7, 0, -1):
        nz = (B[:, k] & np.uint64(0x7fffffffffffffff)) != 0
        d = (E[:, k - 1] - E[:, k]) & np.uint64(0x7ff)
        B[nz, k] = (B[nz, k] & ~(np.uint64(0x7ff) << np.uint64(52))) | (d[nz] << np.uint64(52))
    return B.view(np.float64)

def sizes(P):
    m = len(P)
    out = {}
    for name, Q in (('raw parts', P), ('exponent delta', delta_exp(P))):
        U = Q.view(np.uint64)
        layouts = {
            'interleaved': U.ravel(),
            'part arrays': U.T.ravel(),
        }
        for lname, arr in layouts.items():
            filters = (('none', lambda a: a.tobytes()), ('byte shuffle', byteshuffle), ('bit shuffle', bitshuffle))
            for fname, f in filters:
                if lname == 'part arrays' and fname != 'none':
                    data = b''.join(f(U[:, k].copy()) for k in range(8))
                else:
                    data = f(arr)
                codecs = (lambda d: zlib.compress(d, 9), lambda d: lzma.compress(d, preset=9))
                out[(name, lname, fname)] = tuple(len(c(data)) * 8 / m for c in codecs)
    return out

def varlen(P):
    """bits per value of a variable-length gap code: x0 raw, and per lower part its sign, its fraction and its drop d
    below the part above coded in d - 53 bits (unary), a zero part in 8"""
    ex = np.frexp(P)[1]
    total = 0
    for row, e in zip(P, ex):
        b = 64
        for i in range(1, 8):
            d = int(e[i - 1] - e[i]) if row[i] != 0 and row[i - 1] != 0 else None
            b += 1 + 52 + (d - 53 if d is not None and d >= 54 else 8)
        total += b
    return total / len(P)


for f in sys.argv[1:]:
    P = parts(f)
    print(f"{f}: {len(P)} values; raw 512 bits per value; packed format 463")
    print(f"  variable-length gap code {varlen(P):.1f}")
    for (name, lname, fname), (z, l) in sizes(P).items():
        print(f"  {name:15s} {lname:12s} {fname:13s} zlib {z:6.1f}  lzma {l:6.1f}")
