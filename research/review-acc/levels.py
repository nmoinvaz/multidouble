"""Level growth in a p = 53, n = 8 construction file: per level m, s_{m+1}(K) / (u sum_k s_m(k)) (the remark's 'about
0.6'), s_m(K) / ((Ku)^m / m!), and E_lev / ((Ku)^9 / 9!), all relative to W.
python3 levels.py out/c53_2048.txt
"""
from fractions import Fraction as Fr
from math import factorial
import sys

import construct as C
import reffp as F

F.setp(53)
u = Fr(1, 2 ** 53)
terms = C.load(sys.argv[1])
K = len(terms)
n = 8
st = C.State(n)
cum = [Fr(0)] * (n + 1)
for a in terms:
    for l in range(n):
        st.dep(l, a[l])
    for m in range(n + 1):
        cum[m] += F.frac(st.s[m])
W = sum(abs(F.frac(a[0])) for a in terms)
for m in range(n):
    print(f'm={m}: s_(m+1)(K) / (u sum_k s_m(k)) = {float(F.frac(st.s[m + 1]) / (u * cum[m])):.4f}   '
          f's_(m+1)(K) / ((Ku)^(m+1)/(m+1)! W) = {float(F.frac(st.s[m + 1]) / ((K * u) ** (m + 1) / factorial(m + 1) * W)):.4g}')
print(f'E / (u sum_k s_8(k)) = {float(st.E / (u * cum[8])):.4f}, E / ((Ku)^9/9! W) = '
      f'{float(st.E / ((K * u) ** 9 / factorial(9) * W)):.4g}')
