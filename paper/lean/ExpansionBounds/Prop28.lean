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
then `2047` positive octo-doubles of size about `u`, each part at most half an ulp of the one before
(`prop28_terms`). At `p = 53` and `n = 8` the result of FINISH differs from the exact sum `Z` by between
`14675797u^8|Z|` and `14675798u^8|Z|`, the proposition's `1.4676·10^7u^8|Z|` (`prop28`), and `W` lies between
`|Z|(1 - 2^{-96})` and `|Z|` (`prop28_W`). The first `256`, `512` and `1024` terms give errors of `0.10`, `36` and
`1.2·10^4` times `u^8|Z|` (`prop28_256`, `prop28_512`, `prop28_1024`), so doubling the terms from `1024` multiplies
the error by between `1243` and `1244`, about `2^{10.28}`, the proposition's `2^{10.3}`. The terms are cut in chunks
of 16, and the kernel checks the levels after each chunk from those before it (`Prop28/Run0.lean` to `Run7.lean`),
then FINISH and the exact sums. This file is written by `accumulator/acc_lean.py`.
-/

namespace ExpansionBounds

open Finset

/-! ### The levels after each chunk, as functions -/

theorem acc28_e0 : accRunQ 53 8 (acc28T0.map dyFn) (fun _ => 0) = dyFn acc28S1 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun _ _ => rfl)
    acc28S1 rfl acc28_c0

theorem acc28_e1 : accRunQ 53 8 (acc28T1.map dyFn) (dyFn acc28S1) = dyFn acc28S2 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S1 (show acc28S1.length ≤ j from hj))
    acc28S2 rfl acc28_c1

theorem acc28_e2 : accRunQ 53 8 (acc28T2.map dyFn) (dyFn acc28S2) = dyFn acc28S3 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S2 (show acc28S2.length ≤ j from hj))
    acc28S3 rfl acc28_c2

theorem acc28_e3 : accRunQ 53 8 (acc28T3.map dyFn) (dyFn acc28S3) = dyFn acc28S4 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S3 (show acc28S3.length ≤ j from hj))
    acc28S4 rfl acc28_c3

theorem acc28_e4 : accRunQ 53 8 (acc28T4.map dyFn) (dyFn acc28S4) = dyFn acc28S5 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S4 (show acc28S4.length ≤ j from hj))
    acc28S5 rfl acc28_c4

theorem acc28_e5 : accRunQ 53 8 (acc28T5.map dyFn) (dyFn acc28S5) = dyFn acc28S6 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S5 (show acc28S5.length ≤ j from hj))
    acc28S6 rfl acc28_c5

theorem acc28_e6 : accRunQ 53 8 (acc28T6.map dyFn) (dyFn acc28S6) = dyFn acc28S7 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S6 (show acc28S6.length ≤ j from hj))
    acc28S7 rfl acc28_c6

theorem acc28_e7 : accRunQ 53 8 (acc28T7.map dyFn) (dyFn acc28S7) = dyFn acc28S8 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S7 (show acc28S7.length ≤ j from hj))
    acc28S8 rfl acc28_c7

theorem acc28_e8 : accRunQ 53 8 (acc28T8.map dyFn) (dyFn acc28S8) = dyFn acc28S9 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S8 (show acc28S8.length ≤ j from hj))
    acc28S9 rfl acc28_c8

theorem acc28_e9 : accRunQ 53 8 (acc28T9.map dyFn) (dyFn acc28S9) = dyFn acc28S10 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S9 (show acc28S9.length ≤ j from hj))
    acc28S10 rfl acc28_c9

theorem acc28_e10 : accRunQ 53 8 (acc28T10.map dyFn) (dyFn acc28S10) = dyFn acc28S11 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S10 (show acc28S10.length ≤ j from hj))
    acc28S11 rfl acc28_c10

theorem acc28_e11 : accRunQ 53 8 (acc28T11.map dyFn) (dyFn acc28S11) = dyFn acc28S12 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S11 (show acc28S11.length ≤ j from hj))
    acc28S12 rfl acc28_c11

theorem acc28_e12 : accRunQ 53 8 (acc28T12.map dyFn) (dyFn acc28S12) = dyFn acc28S13 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S12 (show acc28S12.length ≤ j from hj))
    acc28S13 rfl acc28_c12

theorem acc28_e13 : accRunQ 53 8 (acc28T13.map dyFn) (dyFn acc28S13) = dyFn acc28S14 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S13 (show acc28S13.length ≤ j from hj))
    acc28S14 rfl acc28_c13

theorem acc28_e14 : accRunQ 53 8 (acc28T14.map dyFn) (dyFn acc28S14) = dyFn acc28S15 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S14 (show acc28S14.length ≤ j from hj))
    acc28S15 rfl acc28_c14

theorem acc28_e15 : accRunQ 53 8 (acc28T15.map dyFn) (dyFn acc28S15) = dyFn acc28S16 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S15 (show acc28S15.length ≤ j from hj))
    acc28S16 rfl acc28_c15

theorem acc28_e16 : accRunQ 53 8 (acc28T16.map dyFn) (dyFn acc28S16) = dyFn acc28S17 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S16 (show acc28S16.length ≤ j from hj))
    acc28S17 rfl acc28_c16

theorem acc28_e17 : accRunQ 53 8 (acc28T17.map dyFn) (dyFn acc28S17) = dyFn acc28S18 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S17 (show acc28S17.length ≤ j from hj))
    acc28S18 rfl acc28_c17

theorem acc28_e18 : accRunQ 53 8 (acc28T18.map dyFn) (dyFn acc28S18) = dyFn acc28S19 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S18 (show acc28S18.length ≤ j from hj))
    acc28S19 rfl acc28_c18

theorem acc28_e19 : accRunQ 53 8 (acc28T19.map dyFn) (dyFn acc28S19) = dyFn acc28S20 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S19 (show acc28S19.length ≤ j from hj))
    acc28S20 rfl acc28_c19

theorem acc28_e20 : accRunQ 53 8 (acc28T20.map dyFn) (dyFn acc28S20) = dyFn acc28S21 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S20 (show acc28S20.length ≤ j from hj))
    acc28S21 rfl acc28_c20

theorem acc28_e21 : accRunQ 53 8 (acc28T21.map dyFn) (dyFn acc28S21) = dyFn acc28S22 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S21 (show acc28S21.length ≤ j from hj))
    acc28S22 rfl acc28_c21

theorem acc28_e22 : accRunQ 53 8 (acc28T22.map dyFn) (dyFn acc28S22) = dyFn acc28S23 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S22 (show acc28S22.length ≤ j from hj))
    acc28S23 rfl acc28_c22

theorem acc28_e23 : accRunQ 53 8 (acc28T23.map dyFn) (dyFn acc28S23) = dyFn acc28S24 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S23 (show acc28S23.length ≤ j from hj))
    acc28S24 rfl acc28_c23

theorem acc28_e24 : accRunQ 53 8 (acc28T24.map dyFn) (dyFn acc28S24) = dyFn acc28S25 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S24 (show acc28S24.length ≤ j from hj))
    acc28S25 rfl acc28_c24

theorem acc28_e25 : accRunQ 53 8 (acc28T25.map dyFn) (dyFn acc28S25) = dyFn acc28S26 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S25 (show acc28S25.length ≤ j from hj))
    acc28S26 rfl acc28_c25

theorem acc28_e26 : accRunQ 53 8 (acc28T26.map dyFn) (dyFn acc28S26) = dyFn acc28S27 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S26 (show acc28S26.length ≤ j from hj))
    acc28S27 rfl acc28_c26

theorem acc28_e27 : accRunQ 53 8 (acc28T27.map dyFn) (dyFn acc28S27) = dyFn acc28S28 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S27 (show acc28S27.length ≤ j from hj))
    acc28S28 rfl acc28_c27

theorem acc28_e28 : accRunQ 53 8 (acc28T28.map dyFn) (dyFn acc28S28) = dyFn acc28S29 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S28 (show acc28S28.length ≤ j from hj))
    acc28S29 rfl acc28_c28

theorem acc28_e29 : accRunQ 53 8 (acc28T29.map dyFn) (dyFn acc28S29) = dyFn acc28S30 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S29 (show acc28S29.length ≤ j from hj))
    acc28S30 rfl acc28_c29

theorem acc28_e30 : accRunQ 53 8 (acc28T30.map dyFn) (dyFn acc28S30) = dyFn acc28S31 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S30 (show acc28S30.length ≤ j from hj))
    acc28S31 rfl acc28_c30

theorem acc28_e31 : accRunQ 53 8 (acc28T31.map dyFn) (dyFn acc28S31) = dyFn acc28S32 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S31 (show acc28S31.length ≤ j from hj))
    acc28S32 rfl acc28_c31

theorem acc28_e32 : accRunQ 53 8 (acc28T32.map dyFn) (dyFn acc28S32) = dyFn acc28S33 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S32 (show acc28S32.length ≤ j from hj))
    acc28S33 rfl acc28_c32

theorem acc28_e33 : accRunQ 53 8 (acc28T33.map dyFn) (dyFn acc28S33) = dyFn acc28S34 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S33 (show acc28S33.length ≤ j from hj))
    acc28S34 rfl acc28_c33

theorem acc28_e34 : accRunQ 53 8 (acc28T34.map dyFn) (dyFn acc28S34) = dyFn acc28S35 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S34 (show acc28S34.length ≤ j from hj))
    acc28S35 rfl acc28_c34

theorem acc28_e35 : accRunQ 53 8 (acc28T35.map dyFn) (dyFn acc28S35) = dyFn acc28S36 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S35 (show acc28S35.length ≤ j from hj))
    acc28S36 rfl acc28_c35

theorem acc28_e36 : accRunQ 53 8 (acc28T36.map dyFn) (dyFn acc28S36) = dyFn acc28S37 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S36 (show acc28S36.length ≤ j from hj))
    acc28S37 rfl acc28_c36

theorem acc28_e37 : accRunQ 53 8 (acc28T37.map dyFn) (dyFn acc28S37) = dyFn acc28S38 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S37 (show acc28S37.length ≤ j from hj))
    acc28S38 rfl acc28_c37

theorem acc28_e38 : accRunQ 53 8 (acc28T38.map dyFn) (dyFn acc28S38) = dyFn acc28S39 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S38 (show acc28S38.length ≤ j from hj))
    acc28S39 rfl acc28_c38

theorem acc28_e39 : accRunQ 53 8 (acc28T39.map dyFn) (dyFn acc28S39) = dyFn acc28S40 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S39 (show acc28S39.length ≤ j from hj))
    acc28S40 rfl acc28_c39

theorem acc28_e40 : accRunQ 53 8 (acc28T40.map dyFn) (dyFn acc28S40) = dyFn acc28S41 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S40 (show acc28S40.length ≤ j from hj))
    acc28S41 rfl acc28_c40

theorem acc28_e41 : accRunQ 53 8 (acc28T41.map dyFn) (dyFn acc28S41) = dyFn acc28S42 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S41 (show acc28S41.length ≤ j from hj))
    acc28S42 rfl acc28_c41

theorem acc28_e42 : accRunQ 53 8 (acc28T42.map dyFn) (dyFn acc28S42) = dyFn acc28S43 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S42 (show acc28S42.length ≤ j from hj))
    acc28S43 rfl acc28_c42

theorem acc28_e43 : accRunQ 53 8 (acc28T43.map dyFn) (dyFn acc28S43) = dyFn acc28S44 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S43 (show acc28S43.length ≤ j from hj))
    acc28S44 rfl acc28_c43

theorem acc28_e44 : accRunQ 53 8 (acc28T44.map dyFn) (dyFn acc28S44) = dyFn acc28S45 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S44 (show acc28S44.length ≤ j from hj))
    acc28S45 rfl acc28_c44

theorem acc28_e45 : accRunQ 53 8 (acc28T45.map dyFn) (dyFn acc28S45) = dyFn acc28S46 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S45 (show acc28S45.length ≤ j from hj))
    acc28S46 rfl acc28_c45

theorem acc28_e46 : accRunQ 53 8 (acc28T46.map dyFn) (dyFn acc28S46) = dyFn acc28S47 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S46 (show acc28S46.length ≤ j from hj))
    acc28S47 rfl acc28_c46

theorem acc28_e47 : accRunQ 53 8 (acc28T47.map dyFn) (dyFn acc28S47) = dyFn acc28S48 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S47 (show acc28S47.length ≤ j from hj))
    acc28S48 rfl acc28_c47

theorem acc28_e48 : accRunQ 53 8 (acc28T48.map dyFn) (dyFn acc28S48) = dyFn acc28S49 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S48 (show acc28S48.length ≤ j from hj))
    acc28S49 rfl acc28_c48

theorem acc28_e49 : accRunQ 53 8 (acc28T49.map dyFn) (dyFn acc28S49) = dyFn acc28S50 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S49 (show acc28S49.length ≤ j from hj))
    acc28S50 rfl acc28_c49

theorem acc28_e50 : accRunQ 53 8 (acc28T50.map dyFn) (dyFn acc28S50) = dyFn acc28S51 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S50 (show acc28S50.length ≤ j from hj))
    acc28S51 rfl acc28_c50

theorem acc28_e51 : accRunQ 53 8 (acc28T51.map dyFn) (dyFn acc28S51) = dyFn acc28S52 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S51 (show acc28S51.length ≤ j from hj))
    acc28S52 rfl acc28_c51

theorem acc28_e52 : accRunQ 53 8 (acc28T52.map dyFn) (dyFn acc28S52) = dyFn acc28S53 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S52 (show acc28S52.length ≤ j from hj))
    acc28S53 rfl acc28_c52

theorem acc28_e53 : accRunQ 53 8 (acc28T53.map dyFn) (dyFn acc28S53) = dyFn acc28S54 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S53 (show acc28S53.length ≤ j from hj))
    acc28S54 rfl acc28_c53

theorem acc28_e54 : accRunQ 53 8 (acc28T54.map dyFn) (dyFn acc28S54) = dyFn acc28S55 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S54 (show acc28S54.length ≤ j from hj))
    acc28S55 rfl acc28_c54

theorem acc28_e55 : accRunQ 53 8 (acc28T55.map dyFn) (dyFn acc28S55) = dyFn acc28S56 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S55 (show acc28S55.length ≤ j from hj))
    acc28S56 rfl acc28_c55

theorem acc28_e56 : accRunQ 53 8 (acc28T56.map dyFn) (dyFn acc28S56) = dyFn acc28S57 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S56 (show acc28S56.length ≤ j from hj))
    acc28S57 rfl acc28_c56

theorem acc28_e57 : accRunQ 53 8 (acc28T57.map dyFn) (dyFn acc28S57) = dyFn acc28S58 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S57 (show acc28S57.length ≤ j from hj))
    acc28S58 rfl acc28_c57

theorem acc28_e58 : accRunQ 53 8 (acc28T58.map dyFn) (dyFn acc28S58) = dyFn acc28S59 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S58 (show acc28S58.length ≤ j from hj))
    acc28S59 rfl acc28_c58

theorem acc28_e59 : accRunQ 53 8 (acc28T59.map dyFn) (dyFn acc28S59) = dyFn acc28S60 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S59 (show acc28S59.length ≤ j from hj))
    acc28S60 rfl acc28_c59

theorem acc28_e60 : accRunQ 53 8 (acc28T60.map dyFn) (dyFn acc28S60) = dyFn acc28S61 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S60 (show acc28S60.length ≤ j from hj))
    acc28S61 rfl acc28_c60

theorem acc28_e61 : accRunQ 53 8 (acc28T61.map dyFn) (dyFn acc28S61) = dyFn acc28S62 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S61 (show acc28S61.length ≤ j from hj))
    acc28S62 rfl acc28_c61

theorem acc28_e62 : accRunQ 53 8 (acc28T62.map dyFn) (dyFn acc28S62) = dyFn acc28S63 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S62 (show acc28S62.length ≤ j from hj))
    acc28S63 rfl acc28_c62

theorem acc28_e63 : accRunQ 53 8 (acc28T63.map dyFn) (dyFn acc28S63) = dyFn acc28S64 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S63 (show acc28S63.length ≤ j from hj))
    acc28S64 rfl acc28_c63

theorem acc28_e64 : accRunQ 53 8 (acc28T64.map dyFn) (dyFn acc28S64) = dyFn acc28S65 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S64 (show acc28S64.length ≤ j from hj))
    acc28S65 rfl acc28_c64

theorem acc28_e65 : accRunQ 53 8 (acc28T65.map dyFn) (dyFn acc28S65) = dyFn acc28S66 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S65 (show acc28S65.length ≤ j from hj))
    acc28S66 rfl acc28_c65

theorem acc28_e66 : accRunQ 53 8 (acc28T66.map dyFn) (dyFn acc28S66) = dyFn acc28S67 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S66 (show acc28S66.length ≤ j from hj))
    acc28S67 rfl acc28_c66

theorem acc28_e67 : accRunQ 53 8 (acc28T67.map dyFn) (dyFn acc28S67) = dyFn acc28S68 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S67 (show acc28S67.length ≤ j from hj))
    acc28S68 rfl acc28_c67

theorem acc28_e68 : accRunQ 53 8 (acc28T68.map dyFn) (dyFn acc28S68) = dyFn acc28S69 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S68 (show acc28S68.length ≤ j from hj))
    acc28S69 rfl acc28_c68

theorem acc28_e69 : accRunQ 53 8 (acc28T69.map dyFn) (dyFn acc28S69) = dyFn acc28S70 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S69 (show acc28S69.length ≤ j from hj))
    acc28S70 rfl acc28_c69

theorem acc28_e70 : accRunQ 53 8 (acc28T70.map dyFn) (dyFn acc28S70) = dyFn acc28S71 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S70 (show acc28S70.length ≤ j from hj))
    acc28S71 rfl acc28_c70

theorem acc28_e71 : accRunQ 53 8 (acc28T71.map dyFn) (dyFn acc28S71) = dyFn acc28S72 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S71 (show acc28S71.length ≤ j from hj))
    acc28S72 rfl acc28_c71

theorem acc28_e72 : accRunQ 53 8 (acc28T72.map dyFn) (dyFn acc28S72) = dyFn acc28S73 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S72 (show acc28S72.length ≤ j from hj))
    acc28S73 rfl acc28_c72

theorem acc28_e73 : accRunQ 53 8 (acc28T73.map dyFn) (dyFn acc28S73) = dyFn acc28S74 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S73 (show acc28S73.length ≤ j from hj))
    acc28S74 rfl acc28_c73

theorem acc28_e74 : accRunQ 53 8 (acc28T74.map dyFn) (dyFn acc28S74) = dyFn acc28S75 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S74 (show acc28S74.length ≤ j from hj))
    acc28S75 rfl acc28_c74

theorem acc28_e75 : accRunQ 53 8 (acc28T75.map dyFn) (dyFn acc28S75) = dyFn acc28S76 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S75 (show acc28S75.length ≤ j from hj))
    acc28S76 rfl acc28_c75

theorem acc28_e76 : accRunQ 53 8 (acc28T76.map dyFn) (dyFn acc28S76) = dyFn acc28S77 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S76 (show acc28S76.length ≤ j from hj))
    acc28S77 rfl acc28_c76

theorem acc28_e77 : accRunQ 53 8 (acc28T77.map dyFn) (dyFn acc28S77) = dyFn acc28S78 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S77 (show acc28S77.length ≤ j from hj))
    acc28S78 rfl acc28_c77

theorem acc28_e78 : accRunQ 53 8 (acc28T78.map dyFn) (dyFn acc28S78) = dyFn acc28S79 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S78 (show acc28S78.length ≤ j from hj))
    acc28S79 rfl acc28_c78

theorem acc28_e79 : accRunQ 53 8 (acc28T79.map dyFn) (dyFn acc28S79) = dyFn acc28S80 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S79 (show acc28S79.length ≤ j from hj))
    acc28S80 rfl acc28_c79

theorem acc28_e80 : accRunQ 53 8 (acc28T80.map dyFn) (dyFn acc28S80) = dyFn acc28S81 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S80 (show acc28S80.length ≤ j from hj))
    acc28S81 rfl acc28_c80

theorem acc28_e81 : accRunQ 53 8 (acc28T81.map dyFn) (dyFn acc28S81) = dyFn acc28S82 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S81 (show acc28S81.length ≤ j from hj))
    acc28S82 rfl acc28_c81

theorem acc28_e82 : accRunQ 53 8 (acc28T82.map dyFn) (dyFn acc28S82) = dyFn acc28S83 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S82 (show acc28S82.length ≤ j from hj))
    acc28S83 rfl acc28_c82

theorem acc28_e83 : accRunQ 53 8 (acc28T83.map dyFn) (dyFn acc28S83) = dyFn acc28S84 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S83 (show acc28S83.length ≤ j from hj))
    acc28S84 rfl acc28_c83

theorem acc28_e84 : accRunQ 53 8 (acc28T84.map dyFn) (dyFn acc28S84) = dyFn acc28S85 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S84 (show acc28S84.length ≤ j from hj))
    acc28S85 rfl acc28_c84

theorem acc28_e85 : accRunQ 53 8 (acc28T85.map dyFn) (dyFn acc28S85) = dyFn acc28S86 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S85 (show acc28S85.length ≤ j from hj))
    acc28S86 rfl acc28_c85

theorem acc28_e86 : accRunQ 53 8 (acc28T86.map dyFn) (dyFn acc28S86) = dyFn acc28S87 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S86 (show acc28S86.length ≤ j from hj))
    acc28S87 rfl acc28_c86

theorem acc28_e87 : accRunQ 53 8 (acc28T87.map dyFn) (dyFn acc28S87) = dyFn acc28S88 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S87 (show acc28S87.length ≤ j from hj))
    acc28S88 rfl acc28_c87

theorem acc28_e88 : accRunQ 53 8 (acc28T88.map dyFn) (dyFn acc28S88) = dyFn acc28S89 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S88 (show acc28S88.length ≤ j from hj))
    acc28S89 rfl acc28_c88

theorem acc28_e89 : accRunQ 53 8 (acc28T89.map dyFn) (dyFn acc28S89) = dyFn acc28S90 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S89 (show acc28S89.length ≤ j from hj))
    acc28S90 rfl acc28_c89

theorem acc28_e90 : accRunQ 53 8 (acc28T90.map dyFn) (dyFn acc28S90) = dyFn acc28S91 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S90 (show acc28S90.length ≤ j from hj))
    acc28S91 rfl acc28_c90

theorem acc28_e91 : accRunQ 53 8 (acc28T91.map dyFn) (dyFn acc28S91) = dyFn acc28S92 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S91 (show acc28S91.length ≤ j from hj))
    acc28S92 rfl acc28_c91

theorem acc28_e92 : accRunQ 53 8 (acc28T92.map dyFn) (dyFn acc28S92) = dyFn acc28S93 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S92 (show acc28S92.length ≤ j from hj))
    acc28S93 rfl acc28_c92

theorem acc28_e93 : accRunQ 53 8 (acc28T93.map dyFn) (dyFn acc28S93) = dyFn acc28S94 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S93 (show acc28S93.length ≤ j from hj))
    acc28S94 rfl acc28_c93

theorem acc28_e94 : accRunQ 53 8 (acc28T94.map dyFn) (dyFn acc28S94) = dyFn acc28S95 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S94 (show acc28S94.length ≤ j from hj))
    acc28S95 rfl acc28_c94

theorem acc28_e95 : accRunQ 53 8 (acc28T95.map dyFn) (dyFn acc28S95) = dyFn acc28S96 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S95 (show acc28S95.length ≤ j from hj))
    acc28S96 rfl acc28_c95

theorem acc28_e96 : accRunQ 53 8 (acc28T96.map dyFn) (dyFn acc28S96) = dyFn acc28S97 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S96 (show acc28S96.length ≤ j from hj))
    acc28S97 rfl acc28_c96

theorem acc28_e97 : accRunQ 53 8 (acc28T97.map dyFn) (dyFn acc28S97) = dyFn acc28S98 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S97 (show acc28S97.length ≤ j from hj))
    acc28S98 rfl acc28_c97

theorem acc28_e98 : accRunQ 53 8 (acc28T98.map dyFn) (dyFn acc28S98) = dyFn acc28S99 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S98 (show acc28S98.length ≤ j from hj))
    acc28S99 rfl acc28_c98

theorem acc28_e99 : accRunQ 53 8 (acc28T99.map dyFn) (dyFn acc28S99) = dyFn acc28S100 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S99 (show acc28S99.length ≤ j from hj))
    acc28S100 rfl acc28_c99

theorem acc28_e100 : accRunQ 53 8 (acc28T100.map dyFn) (dyFn acc28S100) = dyFn acc28S101 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S100 (show acc28S100.length ≤ j from hj))
    acc28S101 rfl acc28_c100

theorem acc28_e101 : accRunQ 53 8 (acc28T101.map dyFn) (dyFn acc28S101) = dyFn acc28S102 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S101 (show acc28S101.length ≤ j from hj))
    acc28S102 rfl acc28_c101

theorem acc28_e102 : accRunQ 53 8 (acc28T102.map dyFn) (dyFn acc28S102) = dyFn acc28S103 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S102 (show acc28S102.length ≤ j from hj))
    acc28S103 rfl acc28_c102

theorem acc28_e103 : accRunQ 53 8 (acc28T103.map dyFn) (dyFn acc28S103) = dyFn acc28S104 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S103 (show acc28S103.length ≤ j from hj))
    acc28S104 rfl acc28_c103

theorem acc28_e104 : accRunQ 53 8 (acc28T104.map dyFn) (dyFn acc28S104) = dyFn acc28S105 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S104 (show acc28S104.length ≤ j from hj))
    acc28S105 rfl acc28_c104

theorem acc28_e105 : accRunQ 53 8 (acc28T105.map dyFn) (dyFn acc28S105) = dyFn acc28S106 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S105 (show acc28S105.length ≤ j from hj))
    acc28S106 rfl acc28_c105

theorem acc28_e106 : accRunQ 53 8 (acc28T106.map dyFn) (dyFn acc28S106) = dyFn acc28S107 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S106 (show acc28S106.length ≤ j from hj))
    acc28S107 rfl acc28_c106

theorem acc28_e107 : accRunQ 53 8 (acc28T107.map dyFn) (dyFn acc28S107) = dyFn acc28S108 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S107 (show acc28S107.length ≤ j from hj))
    acc28S108 rfl acc28_c107

theorem acc28_e108 : accRunQ 53 8 (acc28T108.map dyFn) (dyFn acc28S108) = dyFn acc28S109 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S108 (show acc28S108.length ≤ j from hj))
    acc28S109 rfl acc28_c108

theorem acc28_e109 : accRunQ 53 8 (acc28T109.map dyFn) (dyFn acc28S109) = dyFn acc28S110 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S109 (show acc28S109.length ≤ j from hj))
    acc28S110 rfl acc28_c109

theorem acc28_e110 : accRunQ 53 8 (acc28T110.map dyFn) (dyFn acc28S110) = dyFn acc28S111 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S110 (show acc28S110.length ≤ j from hj))
    acc28S111 rfl acc28_c110

theorem acc28_e111 : accRunQ 53 8 (acc28T111.map dyFn) (dyFn acc28S111) = dyFn acc28S112 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S111 (show acc28S111.length ≤ j from hj))
    acc28S112 rfl acc28_c111

theorem acc28_e112 : accRunQ 53 8 (acc28T112.map dyFn) (dyFn acc28S112) = dyFn acc28S113 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S112 (show acc28S112.length ≤ j from hj))
    acc28S113 rfl acc28_c112

theorem acc28_e113 : accRunQ 53 8 (acc28T113.map dyFn) (dyFn acc28S113) = dyFn acc28S114 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S113 (show acc28S113.length ≤ j from hj))
    acc28S114 rfl acc28_c113

theorem acc28_e114 : accRunQ 53 8 (acc28T114.map dyFn) (dyFn acc28S114) = dyFn acc28S115 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S114 (show acc28S114.length ≤ j from hj))
    acc28S115 rfl acc28_c114

theorem acc28_e115 : accRunQ 53 8 (acc28T115.map dyFn) (dyFn acc28S115) = dyFn acc28S116 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S115 (show acc28S115.length ≤ j from hj))
    acc28S116 rfl acc28_c115

theorem acc28_e116 : accRunQ 53 8 (acc28T116.map dyFn) (dyFn acc28S116) = dyFn acc28S117 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S116 (show acc28S116.length ≤ j from hj))
    acc28S117 rfl acc28_c116

theorem acc28_e117 : accRunQ 53 8 (acc28T117.map dyFn) (dyFn acc28S117) = dyFn acc28S118 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S117 (show acc28S117.length ≤ j from hj))
    acc28S118 rfl acc28_c117

theorem acc28_e118 : accRunQ 53 8 (acc28T118.map dyFn) (dyFn acc28S118) = dyFn acc28S119 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S118 (show acc28S118.length ≤ j from hj))
    acc28S119 rfl acc28_c118

theorem acc28_e119 : accRunQ 53 8 (acc28T119.map dyFn) (dyFn acc28S119) = dyFn acc28S120 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S119 (show acc28S119.length ≤ j from hj))
    acc28S120 rfl acc28_c119

theorem acc28_e120 : accRunQ 53 8 (acc28T120.map dyFn) (dyFn acc28S120) = dyFn acc28S121 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S120 (show acc28S120.length ≤ j from hj))
    acc28S121 rfl acc28_c120

theorem acc28_e121 : accRunQ 53 8 (acc28T121.map dyFn) (dyFn acc28S121) = dyFn acc28S122 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S121 (show acc28S121.length ≤ j from hj))
    acc28S122 rfl acc28_c121

theorem acc28_e122 : accRunQ 53 8 (acc28T122.map dyFn) (dyFn acc28S122) = dyFn acc28S123 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S122 (show acc28S122.length ≤ j from hj))
    acc28S123 rfl acc28_c122

theorem acc28_e123 : accRunQ 53 8 (acc28T123.map dyFn) (dyFn acc28S123) = dyFn acc28S124 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S123 (show acc28S123.length ≤ j from hj))
    acc28S124 rfl acc28_c123

theorem acc28_e124 : accRunQ 53 8 (acc28T124.map dyFn) (dyFn acc28S124) = dyFn acc28S125 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S124 (show acc28S124.length ≤ j from hj))
    acc28S125 rfl acc28_c124

theorem acc28_e125 : accRunQ 53 8 (acc28T125.map dyFn) (dyFn acc28S125) = dyFn acc28S126 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S125 (show acc28S125.length ≤ j from hj))
    acc28S126 rfl acc28_c125

theorem acc28_e126 : accRunQ 53 8 (acc28T126.map dyFn) (dyFn acc28S126) = dyFn acc28S127 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S126 (show acc28S126.length ≤ j from hj))
    acc28S127 rfl acc28_c126

theorem acc28_e127 : accRunQ 53 8 (acc28T127.map dyFn) (dyFn acc28S127) = dyFn acc28S128 :=
  accRunQ_eq_dyFn 53 8 _ _ (fun j hj => dyFn_of_le acc28S127 (show acc28S127.length ≤ j from hj))
    acc28S128 rfl acc28_c127

/-- the levels after the 2048 terms -/
theorem acc28_run : accRunQ 53 8 (acc28T.map dyFn) (fun _ => 0) = dyFn acc28S128 := by
  rw [acc28T]
  simp only [List.map_append, accRunQ_append]
  rw [acc28_e0, acc28_e1, acc28_e2, acc28_e3, acc28_e4, acc28_e5, acc28_e6, acc28_e7, acc28_e8, acc28_e9, acc28_e10,
    acc28_e11, acc28_e12, acc28_e13, acc28_e14, acc28_e15, acc28_e16, acc28_e17, acc28_e18, acc28_e19, acc28_e20,
    acc28_e21, acc28_e22, acc28_e23, acc28_e24, acc28_e25, acc28_e26, acc28_e27, acc28_e28, acc28_e29, acc28_e30,
    acc28_e31, acc28_e32, acc28_e33, acc28_e34, acc28_e35, acc28_e36, acc28_e37, acc28_e38, acc28_e39, acc28_e40,
    acc28_e41, acc28_e42, acc28_e43, acc28_e44, acc28_e45, acc28_e46, acc28_e47, acc28_e48, acc28_e49, acc28_e50,
    acc28_e51, acc28_e52, acc28_e53, acc28_e54, acc28_e55, acc28_e56, acc28_e57, acc28_e58, acc28_e59, acc28_e60,
    acc28_e61, acc28_e62, acc28_e63, acc28_e64, acc28_e65, acc28_e66, acc28_e67, acc28_e68, acc28_e69, acc28_e70,
    acc28_e71, acc28_e72, acc28_e73, acc28_e74, acc28_e75, acc28_e76, acc28_e77, acc28_e78, acc28_e79, acc28_e80,
    acc28_e81, acc28_e82, acc28_e83, acc28_e84, acc28_e85, acc28_e86, acc28_e87, acc28_e88, acc28_e89, acc28_e90,
    acc28_e91, acc28_e92, acc28_e93, acc28_e94, acc28_e95, acc28_e96, acc28_e97, acc28_e98, acc28_e99, acc28_e100,
    acc28_e101, acc28_e102, acc28_e103, acc28_e104, acc28_e105, acc28_e106, acc28_e107, acc28_e108, acc28_e109,
    acc28_e110, acc28_e111, acc28_e112, acc28_e113, acc28_e114, acc28_e115, acc28_e116, acc28_e117, acc28_e118,
    acc28_e119, acc28_e120, acc28_e121, acc28_e122, acc28_e123, acc28_e124, acc28_e125, acc28_e126, acc28_e127]

/-- the first 256 terms, by chunks -/
theorem acc28_take256 : acc28T.take 256 =
    acc28T0 ++ acc28T1 ++ acc28T2 ++ acc28T3 ++ acc28T4 ++ acc28T5 ++ acc28T6 ++ acc28T7 ++ acc28T8 ++ acc28T9 ++
    acc28T10 ++ acc28T11 ++ acc28T12 ++ acc28T13 ++ acc28T14 ++ acc28T15 := by
  decide +kernel

/-- the levels after the first 256 terms -/
theorem acc28_run256 : accRunQ 53 8 ((acc28T.take 256).map dyFn) (fun _ => 0) = dyFn acc28S16 := by
  rw [acc28_take256]
  simp only [List.map_append, accRunQ_append]
  rw [acc28_e0, acc28_e1, acc28_e2, acc28_e3, acc28_e4, acc28_e5, acc28_e6, acc28_e7, acc28_e8, acc28_e9, acc28_e10,
    acc28_e11, acc28_e12, acc28_e13, acc28_e14, acc28_e15]

/-- the first 512 terms, by chunks -/
theorem acc28_take512 : acc28T.take 512 =
    acc28T0 ++ acc28T1 ++ acc28T2 ++ acc28T3 ++ acc28T4 ++ acc28T5 ++ acc28T6 ++ acc28T7 ++ acc28T8 ++ acc28T9 ++
    acc28T10 ++ acc28T11 ++ acc28T12 ++ acc28T13 ++ acc28T14 ++ acc28T15 ++ acc28T16 ++ acc28T17 ++ acc28T18 ++
    acc28T19 ++ acc28T20 ++ acc28T21 ++ acc28T22 ++ acc28T23 ++ acc28T24 ++ acc28T25 ++ acc28T26 ++ acc28T27 ++
    acc28T28 ++ acc28T29 ++ acc28T30 ++ acc28T31 := by
  decide +kernel

/-- the levels after the first 512 terms -/
theorem acc28_run512 : accRunQ 53 8 ((acc28T.take 512).map dyFn) (fun _ => 0) = dyFn acc28S32 := by
  rw [acc28_take512]
  simp only [List.map_append, accRunQ_append]
  rw [acc28_e0, acc28_e1, acc28_e2, acc28_e3, acc28_e4, acc28_e5, acc28_e6, acc28_e7, acc28_e8, acc28_e9, acc28_e10,
    acc28_e11, acc28_e12, acc28_e13, acc28_e14, acc28_e15, acc28_e16, acc28_e17, acc28_e18, acc28_e19, acc28_e20,
    acc28_e21, acc28_e22, acc28_e23, acc28_e24, acc28_e25, acc28_e26, acc28_e27, acc28_e28, acc28_e29, acc28_e30,
    acc28_e31]

/-- the first 1024 terms, by chunks -/
theorem acc28_take1024 : acc28T.take 1024 =
    acc28T0 ++ acc28T1 ++ acc28T2 ++ acc28T3 ++ acc28T4 ++ acc28T5 ++ acc28T6 ++ acc28T7 ++ acc28T8 ++ acc28T9 ++
    acc28T10 ++ acc28T11 ++ acc28T12 ++ acc28T13 ++ acc28T14 ++ acc28T15 ++ acc28T16 ++ acc28T17 ++ acc28T18 ++
    acc28T19 ++ acc28T20 ++ acc28T21 ++ acc28T22 ++ acc28T23 ++ acc28T24 ++ acc28T25 ++ acc28T26 ++ acc28T27 ++
    acc28T28 ++ acc28T29 ++ acc28T30 ++ acc28T31 ++ acc28T32 ++ acc28T33 ++ acc28T34 ++ acc28T35 ++ acc28T36 ++
    acc28T37 ++ acc28T38 ++ acc28T39 ++ acc28T40 ++ acc28T41 ++ acc28T42 ++ acc28T43 ++ acc28T44 ++ acc28T45 ++
    acc28T46 ++ acc28T47 ++ acc28T48 ++ acc28T49 ++ acc28T50 ++ acc28T51 ++ acc28T52 ++ acc28T53 ++ acc28T54 ++
    acc28T55 ++ acc28T56 ++ acc28T57 ++ acc28T58 ++ acc28T59 ++ acc28T60 ++ acc28T61 ++ acc28T62 ++ acc28T63 := by
  decide +kernel

/-- the levels after the first 1024 terms -/
theorem acc28_run1024 : accRunQ 53 8 ((acc28T.take 1024).map dyFn) (fun _ => 0) = dyFn acc28S64 := by
  rw [acc28_take1024]
  simp only [List.map_append, accRunQ_append]
  rw [acc28_e0, acc28_e1, acc28_e2, acc28_e3, acc28_e4, acc28_e5, acc28_e6, acc28_e7, acc28_e8, acc28_e9, acc28_e10,
    acc28_e11, acc28_e12, acc28_e13, acc28_e14, acc28_e15, acc28_e16, acc28_e17, acc28_e18, acc28_e19, acc28_e20,
    acc28_e21, acc28_e22, acc28_e23, acc28_e24, acc28_e25, acc28_e26, acc28_e27, acc28_e28, acc28_e29, acc28_e30,
    acc28_e31, acc28_e32, acc28_e33, acc28_e34, acc28_e35, acc28_e36, acc28_e37, acc28_e38, acc28_e39, acc28_e40,
    acc28_e41, acc28_e42, acc28_e43, acc28_e44, acc28_e45, acc28_e46, acc28_e47, acc28_e48, acc28_e49, acc28_e50,
    acc28_e51, acc28_e52, acc28_e53, acc28_e54, acc28_e55, acc28_e56, acc28_e57, acc28_e58, acc28_e59, acc28_e60,
    acc28_e61, acc28_e62, acc28_e63]

/-- the number of terms -/
theorem acc28_len : acc28T.length = 2048 := by decide +kernel

/-- the first 2048 terms are all of them -/
theorem acc28_take : acc28T.take 2048 = acc28T := List.take_of_length_le (le_of_eq acc28_len)

set_option maxHeartbeats 4000000 in
/-- every part of every term is in `F`: `rnQ` leaves it as it is -/
theorem acc28_F : ∀ t ∈ acc28T, ∀ q ∈ t, rnQ 53 (dyQ q) = dyQ q := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- every term has a positive leading part, and each part is at most `u` times the one before -/
theorem acc28_ladder : ∀ t ∈ acc28T,
    0 < dyFn t 0 ∧ ∀ i < 7, |dyFn t (i + 1)| ≤ 1 / 9007199254740992 * |dyFn t i| := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the first term is `1` -/
theorem acc28_first : dyFn (acc28T.getD 0 []) 0 = 1 ∧ (∀ i < 8, 1 ≤ i → dyFn (acc28T.getD 0 []) i = 0) ∧
    (acc28T.getD 0 []).length ≤ 8 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- the leading parts of the other terms lie in `[(1 - 2^{-42})u, u)` -/
theorem acc28_size : ∀ t ∈ acc28T.tail,
    (1 - 1 / 2 ^ 42) * (1 / 9007199254740992 : ℚ) ≤ dyFn t 0 ∧ dyFn t 0 < 1 / 9007199254740992 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- each part is zero or at most half an ulp of the one before, `2^(e - 54)` for a part in `[2^(e-1), 2^e)` -/
theorem acc28_half : ∀ t ∈ acc28T, ∀ i < 7,
    dyFn t (i + 1) = 0 ∨ dyFn t i ≠ 0 ∧ |dyFn t (i + 1)| ≤ (2 : ℚ) ^ (magQ (dyFn t i) - 53 - 1) := by decide +kernel

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
/-- `W`, the sum of the leading parts, lies between `|Z|(1 - 2^{-96})` and `|Z|`; the kernel sums it by chunks, a sum
down one list of 2048 being too deep for it -/
theorem acc28_W : |dyQ acc28Z| * (1 - 1 / 2 ^ 96) < (acc28T.map fun t => |dyFn t 0|).sum ∧
    (acc28T.map fun t => |dyFn t 0|).sum < |dyQ acc28Z| := by
  rw [acc28T]
  simp only [List.map_append, List.sum_append]
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- FINISH on the levels after the 2048 terms -/
theorem acc28_finish : ∑ i ∈ range 8, finishRQ 53 8 (dyFn acc28S128) 8 i = (acc28X.map dyQ).sum := by
  decide +kernel

/-- the error: between `14675797u^8|Z|` and `14675798u^8|Z|` -/
theorem acc28_err :
    14675797 * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ acc28Z| ≤ |dyQ acc28Z - (acc28X.map dyQ).sum| ∧
      |dyQ acc28Z - (acc28X.map dyQ).sum| ≤ 14675798 * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ acc28Z| := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the exact sum of the first 256 terms, summed by chunks -/
theorem acc28_sum256 : ((acc28T.take 256).map fun t => ∑ i ∈ range 8, dyFn t i).sum = dyQ acc28Z256 := by
  rw [acc28_take256]
  simp only [List.map_append, List.sum_append]
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- FINISH on the levels after the first 256 terms -/
theorem acc28_finish256 : ∑ i ∈ range 8, finishRQ 53 8 (dyFn acc28S16) 8 i = (acc28X256.map dyQ).sum := by
  decide +kernel

/-- the error after the first 256 terms: between `0.1029u^8|Z|` and `0.1030u^8|Z|` -/
theorem acc28_err256 :
    1029 / 10000 * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ acc28Z256| ≤ |dyQ acc28Z256 - (acc28X256.map dyQ).sum| ∧
      |dyQ acc28Z256 - (acc28X256.map dyQ).sum| ≤ 1030 / 10000 * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ acc28Z256| := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the exact sum of the first 512 terms, summed by chunks -/
theorem acc28_sum512 : ((acc28T.take 512).map fun t => ∑ i ∈ range 8, dyFn t i).sum = dyQ acc28Z512 := by
  rw [acc28_take512]
  simp only [List.map_append, List.sum_append]
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- FINISH on the levels after the first 512 terms -/
theorem acc28_finish512 : ∑ i ∈ range 8, finishRQ 53 8 (dyFn acc28S32) 8 i = (acc28X512.map dyQ).sum := by
  decide +kernel

/-- the error after the first 512 terms: between `36.39u^8|Z|` and `36.40u^8|Z|` -/
theorem acc28_err512 :
    3639 / 100 * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ acc28Z512| ≤ |dyQ acc28Z512 - (acc28X512.map dyQ).sum| ∧
      |dyQ acc28Z512 - (acc28X512.map dyQ).sum| ≤ 3640 / 100 * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ acc28Z512| := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- the exact sum of the first 1024 terms, summed by chunks -/
theorem acc28_sum1024 : ((acc28T.take 1024).map fun t => ∑ i ∈ range 8, dyFn t i).sum = dyQ acc28Z1024 := by
  rw [acc28_take1024]
  simp only [List.map_append, List.sum_append]
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- FINISH on the levels after the first 1024 terms -/
theorem acc28_finish1024 : ∑ i ∈ range 8, finishRQ 53 8 (dyFn acc28S64) 8 i = (acc28X1024.map dyQ).sum := by
  decide +kernel

/-- the error after the first 1024 terms: between `11805u^8|Z|` and `11806u^8|Z|` -/
theorem acc28_err1024 :
    11805 * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ acc28Z1024| ≤ |dyQ acc28Z1024 - (acc28X1024.map dyQ).sum| ∧
      |dyQ acc28Z1024 - (acc28X1024.map dyQ).sum| ≤ 11806 * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ acc28Z1024| := by
  decide +kernel

variable (p : ℤ) [Prec_gt_0 p]

/-- the terms of Proposition 28: term `k` is the `k`-th row of the data -/
noncomputable def acc28 : ℕ → ℕ → ℝ := dyTerms acc28T

/-- the error after the first `K` terms, from the kernel's checks of them: the levels `S` after them, FINISH's parts
`X` on those, and the exact sum `Z` -/
theorem acc28_prefix (hp : p = 53) (K : ℕ) (hK : K ≤ 2048) (S X : List (ℤ × ℕ)) (Z : ℤ × ℕ) (lo hi : ℚ)
    (hrun : accRunQ 53 8 ((acc28T.take K).map dyFn) (fun _ => 0) = dyFn S)
    (hsum : ((acc28T.take K).map fun t => ∑ i ∈ range 8, dyFn t i).sum = dyQ Z)
    (hfin : ∑ i ∈ range 8, finishRQ 53 8 (dyFn S) 8 i = (X.map dyQ).sum)
    (herr : lo * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ Z| ≤ |dyQ Z - (X.map dyQ).sum| ∧
      |dyQ Z - (X.map dyQ).sum| ≤ hi * (1 / 9007199254740992 : ℚ) ^ 8 * |dyQ Z|) :
    (lo : ℝ) * u p ^ 8 * |∑ k ∈ Icc 1 K, ∑ i ∈ range 8, acc28 k i| ≤
        |∑ k ∈ Icc 1 K, ∑ i ∈ range 8, acc28 k i -
          ∑ i ∈ range 8, finishR p 8 (accLevX p 8 acc28 K) 8 i| ∧
      |∑ k ∈ Icc 1 K, ∑ i ∈ range 8, acc28 k i -
          ∑ i ∈ range 8, finishR p 8 (accLevX p 8 acc28 K) 8 i| ≤
        (hi : ℝ) * u p ^ 8 * |∑ k ∈ Icc 1 K, ∑ i ∈ range 8, acc28 k i| := by
  subst hp
  obtain ⟨hfin', hZ⟩ := accRun_prefix 53 8 (by norm_num) acc28T (dyF_of_all 53 acc28T acc28_F) (K := K)
    (hK.trans_eq acc28_len.symm)
  have hx : ∑ i ∈ range 8, finishR 53 8 (accLevX 53 8 acc28 K) 8 i = (((X.map dyQ).sum : ℚ) : ℝ) := by
    rw [← hfin, Rat.cast_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← hrun]
    exact hfin' i
  have hZ' : ∑ k ∈ Icc 1 K, ∑ i ∈ range 8, acc28 k i = ((dyQ Z : ℚ) : ℝ) := by
    rw [← hsum]
    exact hZ
  have hu : u (53 : ℤ) = ((1 / 9007199254740992 : ℚ) : ℝ) := (u_53_rat 53 rfl).symm
  obtain ⟨e1, e2⟩ := herr
  constructor
  · rw [hZ', hx, hu, ← Rat.cast_sub, ← Rat.cast_abs, ← Rat.cast_abs, ← Rat.cast_pow, ← Rat.cast_mul, ← Rat.cast_mul,
      Rat.cast_le]
    exact e1
  · rw [hZ', hx, hu, ← Rat.cast_sub, ← Rat.cast_abs, ← Rat.cast_abs, ← Rat.cast_pow, ← Rat.cast_mul, ← Rat.cast_mul,
      Rat.cast_le]
    exact e2

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
  have herr := acc28_prefix p hp 2048 le_rfl acc28S128 acc28X acc28Z 14675797 14675798
    (by rw [acc28_take]; exact acc28_run) (by rw [acc28_take]; exact acc28_sum) acc28_finish acc28_err
  rw [Rat.cast_ofNat, Rat.cast_ofNat] at herr
  subst hp
  have hF := dyF_of_all 53 acc28T acc28_F
  have hu : u (53 : ℤ) = ((1 / 9007199254740992 : ℚ) : ℝ) := (u_53_rat 53 rfl).symm
  refine ⟨fun k i => dyTerms_F 53 acc28T hF k i, fun k hk => ?_, herr⟩
  obtain ⟨hk1, hk2⟩ := mem_Icc.mp hk
  obtain ⟨l1, l2⟩ := acc28_ladder _ (getD_mem acc28T [] (j := k - 1) (by rw [acc28_len]; omega))
  refine ⟨Htheta_of_steps 53 8 _ fun i hi => ?_, ?_⟩
  · show |((dyFn (acc28T.getD (k - 1) []) (i + 1) : ℚ) : ℝ)| ≤
      u (53 : ℤ) * |((dyFn (acc28T.getD (k - 1) []) i : ℚ) : ℝ)|
    rw [hu, ← Rat.cast_abs, ← Rat.cast_abs, ← Rat.cast_mul, Rat.cast_le]
    exact l2 i (by omega)
  · show (0 : ℝ) < ((dyFn (acc28T.getD (k - 1) []) 0 : ℚ) : ℝ)
    exact_mod_cast l1

/-- the terms of Proposition 28: the first is `1`, the leading parts of the others lie in `[(1 - 2^{-42})u, u)`, and
each part is zero or at most half an ulp of the one before, `2^(e - p - 1)` for a part in `[2^(e-1), 2^e)` -/
theorem prop28_terms (hp : p = 53) :
    (acc28 1 0 = 1 ∧ ∀ i, 1 ≤ i → acc28 1 i = 0) ∧
      (∀ k ∈ Icc 2 2048, (1 - (2 : ℝ) ^ (-42 : ℤ)) * u p ≤ acc28 k 0 ∧ acc28 k 0 < u p) ∧
      ∀ k ∈ Icc 1 2048, ∀ i < 7, acc28 k (i + 1) = 0 ∨ ∃ e : ℤ, (2 : ℝ) ^ (e - 1) ≤ |acc28 k i| ∧
        |acc28 k i| < (2 : ℝ) ^ e ∧ |acc28 k (i + 1)| ≤ (2 : ℝ) ^ (e - p - 1) := by
  subst hp
  have hu : u (53 : ℤ) = ((1 / 9007199254740992 : ℚ) : ℝ) := (u_53_rat 53 rfl).symm
  obtain ⟨f0, f1, f2⟩ := acc28_first
  refine ⟨⟨?_, fun i hi => ?_⟩, fun k hk => ?_, fun k hk i hi => ?_⟩
  · show ((dyFn (acc28T.getD 0 []) 0 : ℚ) : ℝ) = 1
    rw [f0, Rat.cast_one]
  · show ((dyFn (acc28T.getD 0 []) i : ℚ) : ℝ) = 0
    rcases Nat.lt_or_ge i 8 with h8 | h8
    · rw [f1 i h8 hi, Rat.cast_zero]
    · rw [dyFn_of_le _ (f2.trans h8), Rat.cast_zero]
  · obtain ⟨hk1, hk2⟩ := mem_Icc.mp hk
    obtain ⟨s1, s2⟩ := acc28_size _ (getD_mem_tail acc28T [] hk1 (hk2.trans_eq acc28_len.symm))
    constructor
    · show (1 - (2 : ℝ) ^ (-42 : ℤ)) * u (53 : ℤ) ≤ ((dyFn (acc28T.getD (k - 1) []) 0 : ℚ) : ℝ)
      rw [hu, show (1 - (2 : ℝ) ^ (-42 : ℤ)) = ((1 - 1 / 2 ^ 42 : ℚ) : ℝ) by norm_num, ← Rat.cast_mul, Rat.cast_le]
      exact s1
    · show ((dyFn (acc28T.getD (k - 1) []) 0 : ℚ) : ℝ) < u (53 : ℤ)
      rw [hu, Rat.cast_lt]
      exact s2
  · obtain ⟨hk1, hk2⟩ := mem_Icc.mp hk
    rcases acc28_half _ (getD_mem acc28T [] (j := k - 1) (by rw [acc28_len]; omega)) i hi with h0 | ⟨hq, hh⟩
    · left
      show ((dyFn (acc28T.getD (k - 1) []) (i + 1) : ℚ) : ℝ) = 0
      rw [h0, Rat.cast_zero]
    · right
      exact half_ulp_cast 53 hq hh

/-- Proposition 28's `W`, the sum of the leading parts' sizes: `|Z|(1 - 2^{-96}) < W < |Z|` -/
theorem prop28_W :
    |∑ k ∈ Icc 1 2048, ∑ i ∈ range 8, acc28 k i| * (1 - (2 : ℝ) ^ (-96 : ℤ)) < ∑ k ∈ Icc 1 2048, |acc28 k 0| ∧
      ∑ k ∈ Icc 1 2048, |acc28 k 0| < |∑ k ∈ Icc 1 2048, ∑ i ∈ range 8, acc28 k i| := by
  have hZ : ∑ k ∈ Icc 1 2048, ∑ i ∈ range 8, acc28 k i = ((dyQ acc28Z : ℚ) : ℝ) := by
    rw [← acc28_sum, ← acc28_len]
    exact dyTerms_sum 8 acc28T
  have hW : ∑ k ∈ Icc 1 2048, |acc28 k 0| = (((acc28T.map fun t => |dyFn t 0|).sum : ℚ) : ℝ) := by
    rw [← acc28_len]
    exact dyTerms_lead_sum acc28T
  obtain ⟨w1, w2⟩ := acc28_W
  rw [hZ, hW, ← Rat.cast_abs, show (1 - (2 : ℝ) ^ (-96 : ℤ)) = ((1 - 1 / 2 ^ 96 : ℚ) : ℝ) by norm_num, ← Rat.cast_mul,
    Rat.cast_lt, Rat.cast_lt]
  exact ⟨w1, w2⟩

/-- the first 256 terms of Proposition 28: the accumulator's result differs from their exact sum `Z` by between
`0.1029u^8|Z|` and `0.1030u^8|Z|` -/
theorem prop28_256 (hp : p = 53) :
    1029 / 10000 * u p ^ 8 * |∑ k ∈ Icc 1 256, ∑ i ∈ range 8, acc28 k i| ≤
        |∑ k ∈ Icc 1 256, ∑ i ∈ range 8, acc28 k i -
          ∑ i ∈ range 8, finishR p 8 (accLevX p 8 acc28 256) 8 i| ∧
      |∑ k ∈ Icc 1 256, ∑ i ∈ range 8, acc28 k i -
          ∑ i ∈ range 8, finishR p 8 (accLevX p 8 acc28 256) 8 i| ≤
        1030 / 10000 * u p ^ 8 * |∑ k ∈ Icc 1 256, ∑ i ∈ range 8, acc28 k i| := by
  have h := acc28_prefix p hp 256 (by norm_num) acc28S16 acc28X256 acc28Z256 (1029 / 10000) (1030 / 10000)
    acc28_run256 acc28_sum256 acc28_finish256 acc28_err256
  push_cast at h
  exact h

/-- the first 512 terms of Proposition 28: the accumulator's result differs from their exact sum `Z` by between
`36.39u^8|Z|` and `36.40u^8|Z|` -/
theorem prop28_512 (hp : p = 53) :
    3639 / 100 * u p ^ 8 * |∑ k ∈ Icc 1 512, ∑ i ∈ range 8, acc28 k i| ≤
        |∑ k ∈ Icc 1 512, ∑ i ∈ range 8, acc28 k i -
          ∑ i ∈ range 8, finishR p 8 (accLevX p 8 acc28 512) 8 i| ∧
      |∑ k ∈ Icc 1 512, ∑ i ∈ range 8, acc28 k i -
          ∑ i ∈ range 8, finishR p 8 (accLevX p 8 acc28 512) 8 i| ≤
        3640 / 100 * u p ^ 8 * |∑ k ∈ Icc 1 512, ∑ i ∈ range 8, acc28 k i| := by
  have h := acc28_prefix p hp 512 (by norm_num) acc28S32 acc28X512 acc28Z512 (3639 / 100) (3640 / 100)
    acc28_run512 acc28_sum512 acc28_finish512 acc28_err512
  push_cast at h
  exact h

/-- the first 1024 terms of Proposition 28: the accumulator's result differs from their exact sum `Z` by between
`11805u^8|Z|` and `11806u^8|Z|` -/
theorem prop28_1024 (hp : p = 53) :
    11805 * u p ^ 8 * |∑ k ∈ Icc 1 1024, ∑ i ∈ range 8, acc28 k i| ≤
        |∑ k ∈ Icc 1 1024, ∑ i ∈ range 8, acc28 k i -
          ∑ i ∈ range 8, finishR p 8 (accLevX p 8 acc28 1024) 8 i| ∧
      |∑ k ∈ Icc 1 1024, ∑ i ∈ range 8, acc28 k i -
          ∑ i ∈ range 8, finishR p 8 (accLevX p 8 acc28 1024) 8 i| ≤
        11806 * u p ^ 8 * |∑ k ∈ Icc 1 1024, ∑ i ∈ range 8, acc28 k i| := by
  have h := acc28_prefix p hp 1024 (by norm_num) acc28S64 acc28X1024 acc28Z1024 (11805) (11806)
    acc28_run1024 acc28_sum1024 acc28_finish1024 acc28_err1024
  push_cast at h
  exact h

end ExpansionBounds
