| multiplication | add/sub | mul | fma | cmp | error on (1,u,u^2,0)x(1,0,0,u^3), units of u^4|Z| |
|---|---|---|---|---|---|
| paper MUL (multidouble od, TwoSum renorm) | 184 | 11 | 12 | 0 | 1.0000 |
| paper MUL, branch + Fast2Sum (multidouble 4.8.2) | 172 | 11 | 12 | 4 | 1.0000 |
| QD 2.3.24 accurate_mul | 157 | 13 | 10 | 0 | 1.0000 |
| QD 2.3.24 sloppy_mul (default) | 102 | 10 | 6 | 0 | 1.0000 |
| libQD3 bf_mul (Kouya Alg. 14, QD_BF) | 90 | 10 | 6 | 0 | 1.0000 |
| CAMPARY baileyMul_renorm | 196 | 11 | 12 | 0 | 1.0000 |

| addition | add/sub | cmp | error on (1,u,u^2,u^3)+(u^4,0,0,0), units of u^4|Z| |
|---|---|---|---|
| paper ADD (multidouble od, TwoSum renorm) | 111 | 0 | 1.0000 |
| QD 2.3.24 sloppy_add (default) | 82 | 0 | 1.0000 |
| QD 2.3.24 ieee_add | 90 | 7 | 1.0000 |
| libQD3 bf_add (Kouya Alg. 13, QD_BF) | 103 | 0 | 1.0000 |
| CAMPARY certifiedAdd | 57 | 7 | 1.0000 |
| CAMPARY baileyAdd_renorm | 124 | 0 | 1.0000 |
