"""The paper's worked example: MUL of (1, u, 0) and (1, 0, u^2) at n = 3, p = 53, on the emulator fpemu.py.
Exits non-zero if the result is not (1, u, u^2), the levels are not (1, u, u^2, u^3), or the exact split fails."""
import sys
from fractions import Fraction as Q
sys.path.insert(0, sys.argv[1])
import fpemu as F

def val(x):
    m, e = x
    return Q(0) if m == 0 else Q(m) * Q(2) ** e

def run(mutate=None):
    F.set_p(53); F.MUTATE = mutate
    one, u, z = (1, 0), (1, -53), F.PZ
    a, b = [one, u, z], [one, z, (1, -106)]
    lev = F.od_expand(a, b)
    x = F.od_mul(a, b)
    return [val(t) for t in lev], [val(t) for t in x]

u = Q(1, 2**53)
lev, x = run()
Z = (1 + u) * (1 + u * u)
print("levels / u^k:", [t / u**k for k, t in enumerate(lev)])
print("result / u^k:", [t / u**k for k, t in enumerate(x)])
err = Z - sum(x)
print("error / u^3:", err / u**3, " error / (u^3 Z):", float(err / (u**3 * Z)))
ok = lev == [1, u, u**2, u**3] and x == [1, u, u**2] and err == u**3
# an exact three-part split exists: (1 + 2u, -(u - u^2), u^3), each part a binary64 number
alt = [1 + 2 * u, -(u - u * u), u**3]
is_f64 = all(Q(float(t)) == t for t in alt)
print("exact split sums to Z:", sum(alt) == Z, " parts are binary64:", is_f64)
ok = ok and sum(alt) == Z and is_f64
# control: ties away from zero must change the result
_, xc = run('ties_away')
print("control (ties away) result / u^k:", [t / u**k for k, t in enumerate(xc)], " differs:", xc != x)
ok = ok and xc != x
print("PASS" if ok else "FAIL"); sys.exit(0 if ok else 1)
