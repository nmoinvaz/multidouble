import ExpansionBounds.Prop28.Run0
import ExpansionBounds.Prop28.Run1
import ExpansionBounds.Prop28.Run2
import ExpansionBounds.Prop28.Run3
import ExpansionBounds.Prop28.Run4
import ExpansionBounds.Prop28.Run5
import ExpansionBounds.Prop28.Run6
import ExpansionBounds.Prop28.Run7
import ExpansionBounds.Kappa8

/-!
# Proposition 28 (`prop:acc-low`): the accumulator's growth is real

The accumulator run by the kernel on the constructed terms of `accumulator/out/acc_p53_n8_K2048_terms.txt`: `1` and
then `2047` positive octo-doubles of size about `u`, each part at most `u` times the one before. At `p = 53` and
`n = 8` the result of FINISH differs from the exact sum `Z` by between `14675797u^8|Z|` and `14675798u^8|Z|`, the
proposition's `1.4676·10^7u^8|Z|`. The terms are cut in chunks of 16, and the kernel checks the levels after each
chunk from those before it (`Prop28/Run0.lean` to `Run7.lean`), then FINISH and the exact sum. This file is written
by `accumulator/acc_lean.py`.
-/

namespace ExpansionBounds

open Finset

/-- the levels after the 2048 terms -/
theorem acc28_run : accRunQ 53 8 (acc28T.map dyFn) (fun _ => 0) = dyFn acc28S128 := by
  have e0 := accRunQ_eq_dyFn 53 8 _ _ (fun _ _ => rfl)
    acc28S1 rfl acc28_c0
  have e1 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S1 (show acc28S1.length ≤ j from hj))
    acc28S2 rfl acc28_c1
  have e2 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S2 (show acc28S2.length ≤ j from hj))
    acc28S3 rfl acc28_c2
  have e3 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S3 (show acc28S3.length ≤ j from hj))
    acc28S4 rfl acc28_c3
  have e4 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S4 (show acc28S4.length ≤ j from hj))
    acc28S5 rfl acc28_c4
  have e5 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S5 (show acc28S5.length ≤ j from hj))
    acc28S6 rfl acc28_c5
  have e6 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S6 (show acc28S6.length ≤ j from hj))
    acc28S7 rfl acc28_c6
  have e7 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S7 (show acc28S7.length ≤ j from hj))
    acc28S8 rfl acc28_c7
  have e8 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S8 (show acc28S8.length ≤ j from hj))
    acc28S9 rfl acc28_c8
  have e9 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S9 (show acc28S9.length ≤ j from hj))
    acc28S10 rfl acc28_c9
  have e10 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S10 (show acc28S10.length ≤ j from hj))
    acc28S11 rfl acc28_c10
  have e11 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S11 (show acc28S11.length ≤ j from hj))
    acc28S12 rfl acc28_c11
  have e12 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S12 (show acc28S12.length ≤ j from hj))
    acc28S13 rfl acc28_c12
  have e13 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S13 (show acc28S13.length ≤ j from hj))
    acc28S14 rfl acc28_c13
  have e14 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S14 (show acc28S14.length ≤ j from hj))
    acc28S15 rfl acc28_c14
  have e15 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S15 (show acc28S15.length ≤ j from hj))
    acc28S16 rfl acc28_c15
  have e16 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S16 (show acc28S16.length ≤ j from hj))
    acc28S17 rfl acc28_c16
  have e17 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S17 (show acc28S17.length ≤ j from hj))
    acc28S18 rfl acc28_c17
  have e18 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S18 (show acc28S18.length ≤ j from hj))
    acc28S19 rfl acc28_c18
  have e19 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S19 (show acc28S19.length ≤ j from hj))
    acc28S20 rfl acc28_c19
  have e20 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S20 (show acc28S20.length ≤ j from hj))
    acc28S21 rfl acc28_c20
  have e21 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S21 (show acc28S21.length ≤ j from hj))
    acc28S22 rfl acc28_c21
  have e22 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S22 (show acc28S22.length ≤ j from hj))
    acc28S23 rfl acc28_c22
  have e23 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S23 (show acc28S23.length ≤ j from hj))
    acc28S24 rfl acc28_c23
  have e24 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S24 (show acc28S24.length ≤ j from hj))
    acc28S25 rfl acc28_c24
  have e25 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S25 (show acc28S25.length ≤ j from hj))
    acc28S26 rfl acc28_c25
  have e26 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S26 (show acc28S26.length ≤ j from hj))
    acc28S27 rfl acc28_c26
  have e27 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S27 (show acc28S27.length ≤ j from hj))
    acc28S28 rfl acc28_c27
  have e28 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S28 (show acc28S28.length ≤ j from hj))
    acc28S29 rfl acc28_c28
  have e29 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S29 (show acc28S29.length ≤ j from hj))
    acc28S30 rfl acc28_c29
  have e30 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S30 (show acc28S30.length ≤ j from hj))
    acc28S31 rfl acc28_c30
  have e31 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S31 (show acc28S31.length ≤ j from hj))
    acc28S32 rfl acc28_c31
  have e32 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S32 (show acc28S32.length ≤ j from hj))
    acc28S33 rfl acc28_c32
  have e33 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S33 (show acc28S33.length ≤ j from hj))
    acc28S34 rfl acc28_c33
  have e34 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S34 (show acc28S34.length ≤ j from hj))
    acc28S35 rfl acc28_c34
  have e35 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S35 (show acc28S35.length ≤ j from hj))
    acc28S36 rfl acc28_c35
  have e36 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S36 (show acc28S36.length ≤ j from hj))
    acc28S37 rfl acc28_c36
  have e37 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S37 (show acc28S37.length ≤ j from hj))
    acc28S38 rfl acc28_c37
  have e38 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S38 (show acc28S38.length ≤ j from hj))
    acc28S39 rfl acc28_c38
  have e39 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S39 (show acc28S39.length ≤ j from hj))
    acc28S40 rfl acc28_c39
  have e40 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S40 (show acc28S40.length ≤ j from hj))
    acc28S41 rfl acc28_c40
  have e41 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S41 (show acc28S41.length ≤ j from hj))
    acc28S42 rfl acc28_c41
  have e42 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S42 (show acc28S42.length ≤ j from hj))
    acc28S43 rfl acc28_c42
  have e43 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S43 (show acc28S43.length ≤ j from hj))
    acc28S44 rfl acc28_c43
  have e44 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S44 (show acc28S44.length ≤ j from hj))
    acc28S45 rfl acc28_c44
  have e45 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S45 (show acc28S45.length ≤ j from hj))
    acc28S46 rfl acc28_c45
  have e46 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S46 (show acc28S46.length ≤ j from hj))
    acc28S47 rfl acc28_c46
  have e47 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S47 (show acc28S47.length ≤ j from hj))
    acc28S48 rfl acc28_c47
  have e48 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S48 (show acc28S48.length ≤ j from hj))
    acc28S49 rfl acc28_c48
  have e49 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S49 (show acc28S49.length ≤ j from hj))
    acc28S50 rfl acc28_c49
  have e50 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S50 (show acc28S50.length ≤ j from hj))
    acc28S51 rfl acc28_c50
  have e51 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S51 (show acc28S51.length ≤ j from hj))
    acc28S52 rfl acc28_c51
  have e52 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S52 (show acc28S52.length ≤ j from hj))
    acc28S53 rfl acc28_c52
  have e53 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S53 (show acc28S53.length ≤ j from hj))
    acc28S54 rfl acc28_c53
  have e54 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S54 (show acc28S54.length ≤ j from hj))
    acc28S55 rfl acc28_c54
  have e55 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S55 (show acc28S55.length ≤ j from hj))
    acc28S56 rfl acc28_c55
  have e56 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S56 (show acc28S56.length ≤ j from hj))
    acc28S57 rfl acc28_c56
  have e57 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S57 (show acc28S57.length ≤ j from hj))
    acc28S58 rfl acc28_c57
  have e58 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S58 (show acc28S58.length ≤ j from hj))
    acc28S59 rfl acc28_c58
  have e59 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S59 (show acc28S59.length ≤ j from hj))
    acc28S60 rfl acc28_c59
  have e60 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S60 (show acc28S60.length ≤ j from hj))
    acc28S61 rfl acc28_c60
  have e61 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S61 (show acc28S61.length ≤ j from hj))
    acc28S62 rfl acc28_c61
  have e62 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S62 (show acc28S62.length ≤ j from hj))
    acc28S63 rfl acc28_c62
  have e63 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S63 (show acc28S63.length ≤ j from hj))
    acc28S64 rfl acc28_c63
  have e64 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S64 (show acc28S64.length ≤ j from hj))
    acc28S65 rfl acc28_c64
  have e65 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S65 (show acc28S65.length ≤ j from hj))
    acc28S66 rfl acc28_c65
  have e66 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S66 (show acc28S66.length ≤ j from hj))
    acc28S67 rfl acc28_c66
  have e67 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S67 (show acc28S67.length ≤ j from hj))
    acc28S68 rfl acc28_c67
  have e68 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S68 (show acc28S68.length ≤ j from hj))
    acc28S69 rfl acc28_c68
  have e69 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S69 (show acc28S69.length ≤ j from hj))
    acc28S70 rfl acc28_c69
  have e70 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S70 (show acc28S70.length ≤ j from hj))
    acc28S71 rfl acc28_c70
  have e71 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S71 (show acc28S71.length ≤ j from hj))
    acc28S72 rfl acc28_c71
  have e72 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S72 (show acc28S72.length ≤ j from hj))
    acc28S73 rfl acc28_c72
  have e73 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S73 (show acc28S73.length ≤ j from hj))
    acc28S74 rfl acc28_c73
  have e74 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S74 (show acc28S74.length ≤ j from hj))
    acc28S75 rfl acc28_c74
  have e75 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S75 (show acc28S75.length ≤ j from hj))
    acc28S76 rfl acc28_c75
  have e76 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S76 (show acc28S76.length ≤ j from hj))
    acc28S77 rfl acc28_c76
  have e77 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S77 (show acc28S77.length ≤ j from hj))
    acc28S78 rfl acc28_c77
  have e78 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S78 (show acc28S78.length ≤ j from hj))
    acc28S79 rfl acc28_c78
  have e79 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S79 (show acc28S79.length ≤ j from hj))
    acc28S80 rfl acc28_c79
  have e80 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S80 (show acc28S80.length ≤ j from hj))
    acc28S81 rfl acc28_c80
  have e81 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S81 (show acc28S81.length ≤ j from hj))
    acc28S82 rfl acc28_c81
  have e82 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S82 (show acc28S82.length ≤ j from hj))
    acc28S83 rfl acc28_c82
  have e83 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S83 (show acc28S83.length ≤ j from hj))
    acc28S84 rfl acc28_c83
  have e84 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S84 (show acc28S84.length ≤ j from hj))
    acc28S85 rfl acc28_c84
  have e85 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S85 (show acc28S85.length ≤ j from hj))
    acc28S86 rfl acc28_c85
  have e86 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S86 (show acc28S86.length ≤ j from hj))
    acc28S87 rfl acc28_c86
  have e87 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S87 (show acc28S87.length ≤ j from hj))
    acc28S88 rfl acc28_c87
  have e88 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S88 (show acc28S88.length ≤ j from hj))
    acc28S89 rfl acc28_c88
  have e89 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S89 (show acc28S89.length ≤ j from hj))
    acc28S90 rfl acc28_c89
  have e90 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S90 (show acc28S90.length ≤ j from hj))
    acc28S91 rfl acc28_c90
  have e91 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S91 (show acc28S91.length ≤ j from hj))
    acc28S92 rfl acc28_c91
  have e92 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S92 (show acc28S92.length ≤ j from hj))
    acc28S93 rfl acc28_c92
  have e93 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S93 (show acc28S93.length ≤ j from hj))
    acc28S94 rfl acc28_c93
  have e94 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S94 (show acc28S94.length ≤ j from hj))
    acc28S95 rfl acc28_c94
  have e95 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S95 (show acc28S95.length ≤ j from hj))
    acc28S96 rfl acc28_c95
  have e96 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S96 (show acc28S96.length ≤ j from hj))
    acc28S97 rfl acc28_c96
  have e97 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S97 (show acc28S97.length ≤ j from hj))
    acc28S98 rfl acc28_c97
  have e98 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S98 (show acc28S98.length ≤ j from hj))
    acc28S99 rfl acc28_c98
  have e99 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S99 (show acc28S99.length ≤ j from hj))
    acc28S100 rfl acc28_c99
  have e100 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S100 (show acc28S100.length ≤ j from hj))
    acc28S101 rfl acc28_c100
  have e101 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S101 (show acc28S101.length ≤ j from hj))
    acc28S102 rfl acc28_c101
  have e102 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S102 (show acc28S102.length ≤ j from hj))
    acc28S103 rfl acc28_c102
  have e103 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S103 (show acc28S103.length ≤ j from hj))
    acc28S104 rfl acc28_c103
  have e104 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S104 (show acc28S104.length ≤ j from hj))
    acc28S105 rfl acc28_c104
  have e105 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S105 (show acc28S105.length ≤ j from hj))
    acc28S106 rfl acc28_c105
  have e106 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S106 (show acc28S106.length ≤ j from hj))
    acc28S107 rfl acc28_c106
  have e107 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S107 (show acc28S107.length ≤ j from hj))
    acc28S108 rfl acc28_c107
  have e108 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S108 (show acc28S108.length ≤ j from hj))
    acc28S109 rfl acc28_c108
  have e109 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S109 (show acc28S109.length ≤ j from hj))
    acc28S110 rfl acc28_c109
  have e110 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S110 (show acc28S110.length ≤ j from hj))
    acc28S111 rfl acc28_c110
  have e111 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S111 (show acc28S111.length ≤ j from hj))
    acc28S112 rfl acc28_c111
  have e112 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S112 (show acc28S112.length ≤ j from hj))
    acc28S113 rfl acc28_c112
  have e113 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S113 (show acc28S113.length ≤ j from hj))
    acc28S114 rfl acc28_c113
  have e114 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S114 (show acc28S114.length ≤ j from hj))
    acc28S115 rfl acc28_c114
  have e115 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S115 (show acc28S115.length ≤ j from hj))
    acc28S116 rfl acc28_c115
  have e116 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S116 (show acc28S116.length ≤ j from hj))
    acc28S117 rfl acc28_c116
  have e117 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S117 (show acc28S117.length ≤ j from hj))
    acc28S118 rfl acc28_c117
  have e118 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S118 (show acc28S118.length ≤ j from hj))
    acc28S119 rfl acc28_c118
  have e119 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S119 (show acc28S119.length ≤ j from hj))
    acc28S120 rfl acc28_c119
  have e120 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S120 (show acc28S120.length ≤ j from hj))
    acc28S121 rfl acc28_c120
  have e121 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S121 (show acc28S121.length ≤ j from hj))
    acc28S122 rfl acc28_c121
  have e122 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S122 (show acc28S122.length ≤ j from hj))
    acc28S123 rfl acc28_c122
  have e123 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S123 (show acc28S123.length ≤ j from hj))
    acc28S124 rfl acc28_c123
  have e124 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S124 (show acc28S124.length ≤ j from hj))
    acc28S125 rfl acc28_c124
  have e125 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S125 (show acc28S125.length ≤ j from hj))
    acc28S126 rfl acc28_c125
  have e126 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S126 (show acc28S126.length ≤ j from hj))
    acc28S127 rfl acc28_c126
  have e127 := accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S127 (show acc28S127.length ≤ j from hj))
    acc28S128 rfl acc28_c127
  rw [acc28T]
  simp only [List.map_append, accRunQ_append]
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24,
    e25, e26, e27, e28, e29, e30, e31, e32, e33, e34, e35, e36, e37, e38, e39, e40, e41, e42, e43, e44, e45, e46, e47,
    e48, e49, e50, e51, e52, e53, e54, e55, e56, e57, e58, e59, e60, e61, e62, e63, e64, e65, e66, e67, e68, e69, e70,
    e71, e72, e73, e74, e75, e76, e77, e78, e79, e80, e81, e82, e83, e84, e85, e86, e87, e88, e89, e90, e91, e92, e93,
    e94, e95, e96, e97, e98, e99, e100, e101, e102, e103, e104, e105, e106, e107, e108, e109, e110, e111, e112, e113,
    e114, e115, e116, e117, e118, e119, e120, e121, e122, e123, e124, e125, e126, e127]

set_option maxHeartbeats 4000000 in
/-- every part of every term is in `F`: `rnQ` leaves it as it is -/
theorem acc28_F : ∀ t ∈ acc28T, ∀ q ∈ t, rnQ 53 (dyQ q) = dyQ q := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- every term has a positive leading part, and each part is at most `u` times the one before -/
theorem acc28_ladder : ∀ t ∈ acc28T,
    0 < dyFn t 0 ∧ ∀ i < 7, |dyFn t (i + 1)| ≤ 1 / 9007199254740992 * |dyFn t i| := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the exact sum of each chunk -/
theorem acc28_sums :
    List.map (fun T => (T.map fun t => ∑ i ∈ range 8, dyFn t i).sum)
        [acc28T0, acc28T1, acc28T2, acc28T3, acc28T4, acc28T5, acc28T6, acc28T7, acc28T8, acc28T9, acc28T10, acc28T11,
          acc28T12, acc28T13, acc28T14, acc28T15, acc28T16, acc28T17, acc28T18, acc28T19, acc28T20, acc28T21, acc28T22,
          acc28T23, acc28T24, acc28T25, acc28T26, acc28T27, acc28T28, acc28T29, acc28T30, acc28T31, acc28T32, acc28T33,
          acc28T34, acc28T35, acc28T36, acc28T37, acc28T38, acc28T39, acc28T40, acc28T41, acc28T42, acc28T43, acc28T44,
          acc28T45, acc28T46, acc28T47, acc28T48, acc28T49, acc28T50, acc28T51, acc28T52, acc28T53, acc28T54, acc28T55,
          acc28T56, acc28T57, acc28T58, acc28T59, acc28T60, acc28T61, acc28T62, acc28T63, acc28T64, acc28T65, acc28T66,
          acc28T67, acc28T68, acc28T69, acc28T70, acc28T71, acc28T72, acc28T73, acc28T74, acc28T75, acc28T76, acc28T77,
          acc28T78, acc28T79, acc28T80, acc28T81, acc28T82, acc28T83, acc28T84, acc28T85, acc28T86, acc28T87, acc28T88,
          acc28T89, acc28T90, acc28T91, acc28T92, acc28T93, acc28T94, acc28T95, acc28T96, acc28T97, acc28T98, acc28T99,
          acc28T100, acc28T101, acc28T102, acc28T103, acc28T104, acc28T105, acc28T106, acc28T107, acc28T108, acc28T109,
          acc28T110, acc28T111, acc28T112, acc28T113, acc28T114, acc28T115, acc28T116, acc28T117, acc28T118, acc28T119,
          acc28T120, acc28T121, acc28T122, acc28T123, acc28T124, acc28T125, acc28T126, acc28T127] =
      acc28ZS.map dyQ := by
  decide +kernel

/-- the exact sum of the terms -/
theorem acc28_sum : (acc28T.map fun t => ∑ i ∈ range 8, dyFn t i).sum = dyQ acc28Z := by
  have hz : (acc28ZS.map dyQ).sum = dyQ acc28Z := by decide +kernel
  rw [← hz, ← acc28_sums, acc28T]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    add_assoc]

set_option maxHeartbeats 4000000 in
/-- FINISH on the levels after the 2048 terms -/
theorem acc28_finish : ∑ i ∈ range 8, finishRQ 53 8 (dyFn acc28S128) 8 i = (acc28X.map dyQ).sum := by
  decide +kernel

/-- the error: between `14675797u^8|Z|` and `14675798u^8|Z|` -/
theorem acc28_err :
    14675797 * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ acc28Z| ≤ |dyQ acc28Z - (acc28X.map dyQ).sum| ∧
      |dyQ acc28Z - (acc28X.map dyQ).sum| ≤ 14675798 * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ acc28Z| := by
  decide +kernel

variable (p : ℤ) [Prec_gt_0 p]

/-- the terms of Proposition 28: term `k` is the `k`-th row of the data -/
noncomputable def acc28 : ℕ → ℕ → ℝ := dyTerms acc28T

/-- Proposition 28 (`prop:acc-low`) at `p = 53` and `n = 8`: the `2048` terms are in `F`, on `H(1)` with positive
leading parts, and the accumulator's result differs from their exact sum `Z` by between `14675797u^8|Z|` and
`14675798u^8|Z|` -/
theorem prop28 (hp : p = 53) :
    (∀ k i, F p (acc28 k i)) ∧ (∀ k ∈ Icc 1 2048, Htheta p 8 1 (acc28 k) ∧ 0 < acc28 k 0) ∧
      14675797 * u p ^ 8 * |∑ k ∈ Icc 1 2048, ∑ i ∈ range 8, acc28 k i| ≤
        |∑ k ∈ Icc 1 2048, ∑ i ∈ range 8, acc28 k i -
          ∑ i ∈ range 8, finishR p 8 (accLevX p 8 acc28 2048) 8 i| ∧
      |∑ k ∈ Icc 1 2048, ∑ i ∈ range 8, acc28 k i -
          ∑ i ∈ range 8, finishR p 8 (accLevX p 8 acc28 2048) 8 i| ≤
        14675798 * u p ^ 8 * |∑ k ∈ Icc 1 2048, ∑ i ∈ range 8, acc28 k i| := by
  subst hp
  have hF := dyF_of_all 53 acc28T acc28_F
  have hlen : acc28T.length = 2048 := by decide +kernel
  obtain ⟨hfin, hZ⟩ := accRun_data 53 8 (by norm_num) acc28T hF
  rw [hlen] at hfin hZ
  obtain ⟨Zq, hZq⟩ : ∃ q, q = dyQ acc28Z := ⟨_, rfl⟩
  obtain ⟨xq, hxq⟩ : ∃ q, q = (acc28X.map dyQ).sum := ⟨_, rfl⟩
  have hx : ∑ i ∈ range 8, finishR 53 8 (accLevX 53 8 acc28 2048) 8 i = (xq : ℝ) := by
    rw [hxq, ← acc28_finish, Rat.cast_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← acc28_run]
    exact hfin i
  have hZ' : ∑ k ∈ Icc 1 2048, ∑ i ∈ range 8, acc28 k i = (Zq : ℝ) := by
    rw [hZq, ← acc28_sum]
    exact hZ
  have hu : u (53 : ℤ) = ((1 / 9007199254740992 : ℚ) : ℝ) := (u_53_rat 53 rfl).symm
  obtain ⟨e1, e2⟩ := acc28_err
  rw [← hZq, ← hxq] at e1 e2
  refine ⟨fun k i => dyTerms_F 53 acc28T hF k i, fun k hk => ?_, ?_, ?_⟩
  · obtain ⟨hk1, hk2⟩ := mem_Icc.mp hk
    have hlt : k - 1 < acc28T.length := by omega
    have hmem : acc28T.getD (k - 1) [] ∈ acc28T := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
      exact List.getElem_mem hlt
    obtain ⟨l1, l2⟩ := acc28_ladder _ hmem
    refine ⟨Htheta_of_steps 53 8 _ fun i hi => ?_, ?_⟩
    · show |((dyFn (acc28T.getD (k - 1) []) (i + 1) : ℚ) : ℝ)| ≤
        u (53 : ℤ) * |((dyFn (acc28T.getD (k - 1) []) i : ℚ) : ℝ)|
      rw [hu, ← Rat.cast_abs, ← Rat.cast_abs, ← Rat.cast_mul, Rat.cast_le]
      exact l2 i (by omega)
    · show (0 : ℝ) < ((dyFn (acc28T.getD (k - 1) []) 0 : ℚ) : ℝ)
      exact_mod_cast l1
  · rw [hZ', hx, hu, ← Rat.cast_sub, ← Rat.cast_abs, ← Rat.cast_abs, ← Rat.cast_pow,
      show (14675797 : ℝ) = ((14675797 : ℚ) : ℝ) by norm_num, ← Rat.cast_mul, ← Rat.cast_mul, Rat.cast_le]
    exact e1
  · rw [hZ', hx, hu, ← Rat.cast_sub, ← Rat.cast_abs, ← Rat.cast_abs, ← Rat.cast_pow,
      show (14675798 : ℝ) = ((14675798 : ℚ) : ℝ) by norm_num, ← Rat.cast_mul, ← Rat.cast_mul, Rat.cast_le]
    exact e2

end ExpansionBounds
