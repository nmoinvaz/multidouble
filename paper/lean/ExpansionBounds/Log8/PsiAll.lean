import ExpansionBounds.Log8.All
import ExpansionBounds.Log8.Psi

/-!
# Theorem 42 at `n = 8` and `p = 53`: the parts of `t` at the upper end of every case

For each case and sign the kernel checks that the part bounds of the state after the squarings, at the upper end of
the case's interval of `|ln x|`, sum to at most 1 (`Log8Psi`), on the states of `Log8/Run0.lean` to
`Run8.lean`; then `Log8GroupT0` and `Log8GroupT1` of every group. The largest sum is 0.414214. This file is
written by `log_lean.py`.
-/

namespace ExpansionBounds

set_option maxHeartbeats 4000000 in
theorem log8_g0zp0e1_ps :
    Log8Psi true true 5 43 log8_g0zp0e1_v.1 log8_g0zp0e1_v.2.2.2 log8_g0zp0e1_v.2.1 log8_g0zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g0zp0e1_leaf log8_h0_hp log8_g0zp0e1_sq (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g0np0e1_ps :
    Log8Psi false true 5 43 log8_g0np0e1_v.1 log8_g0np0e1_v.2.2.2 log8_g0np0e1_v.2.1 log8_g0np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g0np0e1_leaf log8_h0_hp log8_g0np0e1_sq (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g0zm0e1_ps :
    Log8Psi true false 5 43 log8_g0zm0e1_v.1 log8_g0zm0e1_v.2.2.2 log8_g0zm0e1_v.2.1 log8_g0zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g0zm0e1_leaf log8_h0_hm log8_g0zm0e1_sq (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g0nm0e1_ps :
    Log8Psi false false 5 43 log8_g0nm0e1_v.1 log8_g0nm0e1_v.2.2.2 log8_g0nm0e1_v.2.1 log8_g0nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g0nm0e1_leaf log8_h0_hm log8_g0nm0e1_sq (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g0nm1e1_ps :
    Log8Psi false false 5 43 log8_g0nm1e1_v.1 log8_g0nm1e1_v.2.2.2 log8_g0nm1e1_v.2.1 log8_g0nm1e1_v.2.2.1 :=
  Log8Psi.mk log8_g0nm1e1_leaf log8_h0_hm log8_g0nm1e1_sq (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g0nm2e1_ps :
    Log8Psi false false 5 43 log8_g0nm2e1_v.1 log8_g0nm2e1_v.2.2.2 log8_g0nm2e1_v.2.1 log8_g0nm2e1_v.2.2.1 :=
  Log8Psi.mk log8_g0nm2e1_leaf log8_h0_hm log8_g0nm2e1_sq (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g0nm3e1_ps :
    Log8Psi false false 5 43 log8_g0nm3e1_v.1 log8_g0nm3e1_v.2.2.2 log8_g0nm3e1_v.2.1 log8_g0nm3e1_v.2.2.1 :=
  Log8Psi.mk log8_g0nm3e1_leaf log8_h0_hm log8_g0nm3e1_sq (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g5zp0e1_ps :
    Log8Psi true true 0 43 log8_g5zp0e1_v.1 log8_g5zp0e1_v.2.2.2 log8_g5zp0e1_v.2.1 log8_g5zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g5zp0e1_leaf log8_h6_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g5np0e1_ps :
    Log8Psi false true 0 43 log8_g5np0e1_v.1 log8_g5np0e1_v.2.2.2 log8_g5np0e1_v.2.1 log8_g5np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g5np0e1_leaf log8_h5_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g5zm0e1_ps :
    Log8Psi true false 0 43 log8_g5zm0e1_v.1 log8_g5zm0e1_v.2.2.2 log8_g5zm0e1_v.2.1 log8_g5zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g5zm0e1_leaf log8_h6_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g5nm0e1_ps :
    Log8Psi false false 0 43 log8_g5nm0e1_v.1 log8_g5nm0e1_v.2.2.2 log8_g5nm0e1_v.2.1 log8_g5nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g5nm0e1_leaf log8_h5_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g18zp0e1_ps :
    Log8Psi true true 0 19 log8_g18zp0e1_v.1 log8_g18zp0e1_v.2.2.2 log8_g18zp0e1_v.2.1 log8_g18zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g18zp0e1_leaf log8_h20_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g18np0e1_ps :
    Log8Psi false true 0 19 log8_g18np0e1_v.1 log8_g18np0e1_v.2.2.2 log8_g18np0e1_v.2.1 log8_g18np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g18np0e1_leaf log8_h20_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g18zm0e1_ps :
    Log8Psi true false 0 19 log8_g18zm0e1_v.1 log8_g18zm0e1_v.2.2.2 log8_g18zm0e1_v.2.1 log8_g18zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g18zm0e1_leaf log8_h20_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g18nm0e1_ps :
    Log8Psi false false 0 19 log8_g18nm0e1_v.1 log8_g18nm0e1_v.2.2.2 log8_g18nm0e1_v.2.1 log8_g18nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g18nm0e1_leaf log8_h20_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g23zp0e1_ps :
    Log8Psi true true 0 14 log8_g23zp0e1_v.1 log8_g23zp0e1_v.2.2.2 log8_g23zp0e1_v.2.1 log8_g23zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g23zp0e1_leaf log8_h25_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g23np0e1_ps :
    Log8Psi false true 0 14 log8_g23np0e1_v.1 log8_g23np0e1_v.2.2.2 log8_g23np0e1_v.2.1 log8_g23np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g23np0e1_leaf log8_h25_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g23zm0e1_ps :
    Log8Psi true false 0 14 log8_g23zm0e1_v.1 log8_g23zm0e1_v.2.2.2 log8_g23zm0e1_v.2.1 log8_g23zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g23zm0e1_leaf log8_h25_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g23nm0e1_ps :
    Log8Psi false false 0 14 log8_g23nm0e1_v.1 log8_g23nm0e1_v.2.2.2 log8_g23nm0e1_v.2.1 log8_g23nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g23nm0e1_leaf log8_h25_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g1zp0e1_ps :
    Log8Psi true true 4 43 log8_g1zp0e1_v.1 log8_g1zp0e1_v.2.2.2 log8_g1zp0e1_v.2.1 log8_g1zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g1zp0e1_leaf log8_h1_hp log8_g1zp0e1_sq (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g1np0e1_ps :
    Log8Psi false true 4 43 log8_g1np0e1_v.1 log8_g1np0e1_v.2.2.2 log8_g1np0e1_v.2.1 log8_g1np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g1np0e1_leaf log8_h1_hp log8_g1np0e1_sq (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g1zm0e1_ps :
    Log8Psi true false 4 43 log8_g1zm0e1_v.1 log8_g1zm0e1_v.2.2.2 log8_g1zm0e1_v.2.1 log8_g1zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g1zm0e1_leaf log8_h1_hm log8_g1zm0e1_sq (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g1nm0e1_ps :
    Log8Psi false false 4 43 log8_g1nm0e1_v.1 log8_g1nm0e1_v.2.2.2 log8_g1nm0e1_v.2.1 log8_g1nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g1nm0e1_leaf log8_h1_hm log8_g1nm0e1_sq (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g12zp0e1_ps :
    Log8Psi true true 0 26 log8_g12zp0e1_v.1 log8_g12zp0e1_v.2.2.2 log8_g12zp0e1_v.2.1 log8_g12zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g12zp0e1_leaf log8_h14_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g12np0e1_ps :
    Log8Psi false true 0 26 log8_g12np0e1_v.1 log8_g12np0e1_v.2.2.2 log8_g12np0e1_v.2.1 log8_g12np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g12np0e1_leaf log8_h14_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g12zm0e1_ps :
    Log8Psi true false 0 26 log8_g12zm0e1_v.1 log8_g12zm0e1_v.2.2.2 log8_g12zm0e1_v.2.1 log8_g12zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g12zm0e1_leaf log8_h14_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g12nm0e1_ps :
    Log8Psi false false 0 26 log8_g12nm0e1_v.1 log8_g12nm0e1_v.2.2.2 log8_g12nm0e1_v.2.1 log8_g12nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g12nm0e1_leaf log8_h14_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g17zp0e1_ps :
    Log8Psi true true 0 20 log8_g17zp0e1_v.1 log8_g17zp0e1_v.2.2.2 log8_g17zp0e1_v.2.1 log8_g17zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g17zp0e1_leaf log8_h19_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g17np0e1_ps :
    Log8Psi false true 0 20 log8_g17np0e1_v.1 log8_g17np0e1_v.2.2.2 log8_g17np0e1_v.2.1 log8_g17np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g17np0e1_leaf log8_h19_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g17zm0e1_ps :
    Log8Psi true false 0 20 log8_g17zm0e1_v.1 log8_g17zm0e1_v.2.2.2 log8_g17zm0e1_v.2.1 log8_g17zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g17zm0e1_leaf log8_h19_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g17nm0e1_ps :
    Log8Psi false false 0 20 log8_g17nm0e1_v.1 log8_g17nm0e1_v.2.2.2 log8_g17nm0e1_v.2.1 log8_g17nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g17nm0e1_leaf log8_h19_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g24zp0e1_ps :
    Log8Psi true true 0 13 log8_g24zp0e1_v.1 log8_g24zp0e1_v.2.2.2 log8_g24zp0e1_v.2.1 log8_g24zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g24zp0e1_leaf log8_h26_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g24np0e1_ps :
    Log8Psi false true 0 13 log8_g24np0e1_v.1 log8_g24np0e1_v.2.2.2 log8_g24np0e1_v.2.1 log8_g24np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g24np0e1_leaf log8_h26_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g24zm0e1_ps :
    Log8Psi true false 0 13 log8_g24zm0e1_v.1 log8_g24zm0e1_v.2.2.2 log8_g24zm0e1_v.2.1 log8_g24zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g24zm0e1_leaf log8_h26_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g24nm0e1_ps :
    Log8Psi false false 0 13 log8_g24nm0e1_v.1 log8_g24nm0e1_v.2.2.2 log8_g24nm0e1_v.2.1 log8_g24nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g24nm0e1_leaf log8_h26_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g2zp0e1_ps :
    Log8Psi true true 3 43 log8_g2zp0e1_v.1 log8_g2zp0e1_v.2.2.2 log8_g2zp0e1_v.2.1 log8_g2zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g2zp0e1_leaf log8_h2_hp log8_g2zp0e1_sq (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g2np0e1_ps :
    Log8Psi false true 3 43 log8_g2np0e1_v.1 log8_g2np0e1_v.2.2.2 log8_g2np0e1_v.2.1 log8_g2np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g2np0e1_leaf log8_h2_hp log8_g2np0e1_sq (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g2zm0e1_ps :
    Log8Psi true false 3 43 log8_g2zm0e1_v.1 log8_g2zm0e1_v.2.2.2 log8_g2zm0e1_v.2.1 log8_g2zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g2zm0e1_leaf log8_h2_hm log8_g2zm0e1_sq (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g2nm0e1_ps :
    Log8Psi false false 3 43 log8_g2nm0e1_v.1 log8_g2nm0e1_v.2.2.2 log8_g2nm0e1_v.2.1 log8_g2nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g2nm0e1_leaf log8_h2_hm log8_g2nm0e1_sq (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g28zp0e1_ps :
    Log8Psi true true 0 9 log8_g28zp0e1_v.1 log8_g28zp0e1_v.2.2.2 log8_g28zp0e1_v.2.1 log8_g28zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g28zp0e1_leaf log8_h35_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g28np0e1_ps :
    Log8Psi false true 0 9 log8_g28np0e1_v.1 log8_g28np0e1_v.2.2.2 log8_g28np0e1_v.2.1 log8_g28np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g28np0e1_leaf log8_h34_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g28zm0e1_ps :
    Log8Psi true false 0 9 log8_g28zm0e1_v.1 log8_g28zm0e1_v.2.2.2 log8_g28zm0e1_v.2.1 log8_g28zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g28zm0e1_leaf log8_h35_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g28nm0e1_ps :
    Log8Psi false false 0 9 log8_g28nm0e1_v.1 log8_g28nm0e1_v.2.2.2 log8_g28nm0e1_v.2.1 log8_g28nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g28nm0e1_leaf log8_h34_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g30zp0e1_ps :
    Log8Psi true true 0 7 log8_g30zp0e1_v.1 log8_g30zp0e1_v.2.2.2 log8_g30zp0e1_v.2.1 log8_g30zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g30zp0e1_leaf log8_h41_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g30np0e1_ps :
    Log8Psi false true 0 7 log8_g30np0e1_v.1 log8_g30np0e1_v.2.2.2 log8_g30np0e1_v.2.1 log8_g30np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g30np0e1_leaf log8_h40_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g30zm0e1_ps :
    Log8Psi true false 0 7 log8_g30zm0e1_v.1 log8_g30zm0e1_v.2.2.2 log8_g30zm0e1_v.2.1 log8_g30zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g30zm0e1_leaf log8_h41_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g30nm0e1_ps :
    Log8Psi false false 0 7 log8_g30nm0e1_v.1 log8_g30nm0e1_v.2.2.2 log8_g30nm0e1_v.2.1 log8_g30nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g30nm0e1_leaf log8_h40_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g32zp0e1_ps :
    Log8Psi true true 0 5 log8_g32zp0e1_v.1 log8_g32zp0e1_v.2.2.2 log8_g32zp0e1_v.2.1 log8_g32zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g32zp0e1_leaf log8_h47_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g32np0e1_ps :
    Log8Psi false true 0 5 log8_g32np0e1_v.1 log8_g32np0e1_v.2.2.2 log8_g32np0e1_v.2.1 log8_g32np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g32np0e1_leaf log8_h46_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g32zm0e1_ps :
    Log8Psi true false 0 5 log8_g32zm0e1_v.1 log8_g32zm0e1_v.2.2.2 log8_g32zm0e1_v.2.1 log8_g32zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g32zm0e1_leaf log8_h47_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g32nm0e1_ps :
    Log8Psi false false 0 5 log8_g32nm0e1_v.1 log8_g32nm0e1_v.2.2.2 log8_g32nm0e1_v.2.1 log8_g32nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g32nm0e1_leaf log8_h46_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g3zp0e1_ps :
    Log8Psi true true 2 43 log8_g3zp0e1_v.1 log8_g3zp0e1_v.2.2.2 log8_g3zp0e1_v.2.1 log8_g3zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g3zp0e1_leaf log8_h3_hp log8_g3zp0e1_sq (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g3np0e1_ps :
    Log8Psi false true 2 43 log8_g3np0e1_v.1 log8_g3np0e1_v.2.2.2 log8_g3np0e1_v.2.1 log8_g3np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g3np0e1_leaf log8_h3_hp log8_g3np0e1_sq (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g3zm0e1_ps :
    Log8Psi true false 2 43 log8_g3zm0e1_v.1 log8_g3zm0e1_v.2.2.2 log8_g3zm0e1_v.2.1 log8_g3zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g3zm0e1_leaf log8_h3_hm log8_g3zm0e1_sq (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g3nm0e1_ps :
    Log8Psi false false 2 43 log8_g3nm0e1_v.1 log8_g3nm0e1_v.2.2.2 log8_g3nm0e1_v.2.1 log8_g3nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g3nm0e1_leaf log8_h3_hm log8_g3nm0e1_sq (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g11zp0e1_ps :
    Log8Psi true true 0 28 log8_g11zp0e1_v.1 log8_g11zp0e1_v.2.2.2 log8_g11zp0e1_v.2.1 log8_g11zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g11zp0e1_leaf log8_h13_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g11np0e1_ps :
    Log8Psi false true 0 28 log8_g11np0e1_v.1 log8_g11np0e1_v.2.2.2 log8_g11np0e1_v.2.1 log8_g11np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g11np0e1_leaf log8_h13_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g11zm0e1_ps :
    Log8Psi true false 0 28 log8_g11zm0e1_v.1 log8_g11zm0e1_v.2.2.2 log8_g11zm0e1_v.2.1 log8_g11zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g11zm0e1_leaf log8_h13_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g11nm0e1_ps :
    Log8Psi false false 0 28 log8_g11nm0e1_v.1 log8_g11nm0e1_v.2.2.2 log8_g11nm0e1_v.2.1 log8_g11nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g11nm0e1_leaf log8_h13_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g16zp0e1_ps :
    Log8Psi true true 0 21 log8_g16zp0e1_v.1 log8_g16zp0e1_v.2.2.2 log8_g16zp0e1_v.2.1 log8_g16zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g16zp0e1_leaf log8_h18_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g16np0e1_ps :
    Log8Psi false true 0 21 log8_g16np0e1_v.1 log8_g16np0e1_v.2.2.2 log8_g16np0e1_v.2.1 log8_g16np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g16np0e1_leaf log8_h18_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g16zm0e1_ps :
    Log8Psi true false 0 21 log8_g16zm0e1_v.1 log8_g16zm0e1_v.2.2.2 log8_g16zm0e1_v.2.1 log8_g16zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g16zm0e1_leaf log8_h18_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g16nm0e1_ps :
    Log8Psi false false 0 21 log8_g16nm0e1_v.1 log8_g16nm0e1_v.2.2.2 log8_g16nm0e1_v.2.1 log8_g16nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g16nm0e1_leaf log8_h18_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g22zp0e1_ps :
    Log8Psi true true 0 15 log8_g22zp0e1_v.1 log8_g22zp0e1_v.2.2.2 log8_g22zp0e1_v.2.1 log8_g22zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g22zp0e1_leaf log8_h24_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g22np0e1_ps :
    Log8Psi false true 0 15 log8_g22np0e1_v.1 log8_g22np0e1_v.2.2.2 log8_g22np0e1_v.2.1 log8_g22np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g22np0e1_leaf log8_h24_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g22zm0e1_ps :
    Log8Psi true false 0 15 log8_g22zm0e1_v.1 log8_g22zm0e1_v.2.2.2 log8_g22zm0e1_v.2.1 log8_g22zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g22zm0e1_leaf log8_h24_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g22nm0e1_ps :
    Log8Psi false false 0 15 log8_g22nm0e1_v.1 log8_g22nm0e1_v.2.2.2 log8_g22nm0e1_v.2.1 log8_g22nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g22nm0e1_leaf log8_h24_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g36zp0e1_ps :
    Log8Psi true true 0 1 log8_g36zp0e1_v.1 log8_g36zp0e1_v.2.2.2 log8_g36zp0e1_v.2.1 log8_g36zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g36zp0e1_leaf log8_h56_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g36np0e1_ps :
    Log8Psi false true 0 1 log8_g36np0e1_v.1 log8_g36np0e1_v.2.2.2 log8_g36np0e1_v.2.1 log8_g36np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g36np0e1_leaf log8_h55_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g36zm0e1_ps :
    Log8Psi true false 0 1 log8_g36zm0e1_v.1 log8_g36zm0e1_v.2.2.2 log8_g36zm0e1_v.2.1 log8_g36zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g36zm0e1_leaf log8_h56_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g36nm0e1_ps :
    Log8Psi false false 0 1 log8_g36nm0e1_v.1 log8_g36nm0e1_v.2.2.2 log8_g36nm0e1_v.2.1 log8_g36nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g36nm0e1_leaf log8_h55_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g4zp0e1_ps :
    Log8Psi true true 1 43 log8_g4zp0e1_v.1 log8_g4zp0e1_v.2.2.2 log8_g4zp0e1_v.2.1 log8_g4zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g4zp0e1_leaf log8_h4_hp log8_g4zp0e1_sq (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g4np0e1_ps :
    Log8Psi false true 1 43 log8_g4np0e1_v.1 log8_g4np0e1_v.2.2.2 log8_g4np0e1_v.2.1 log8_g4np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g4np0e1_leaf log8_h4_hp log8_g4np0e1_sq (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g4zm0e1_ps :
    Log8Psi true false 1 43 log8_g4zm0e1_v.1 log8_g4zm0e1_v.2.2.2 log8_g4zm0e1_v.2.1 log8_g4zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g4zm0e1_leaf log8_h4_hm log8_g4zm0e1_sq (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g4nm0e1_ps :
    Log8Psi false false 1 43 log8_g4nm0e1_v.1 log8_g4nm0e1_v.2.2.2 log8_g4nm0e1_v.2.1 log8_g4nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g4nm0e1_leaf log8_h4_hm log8_g4nm0e1_sq (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g15zp0e1_ps :
    Log8Psi true true 0 22 log8_g15zp0e1_v.1 log8_g15zp0e1_v.2.2.2 log8_g15zp0e1_v.2.1 log8_g15zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g15zp0e1_leaf log8_h17_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g15np0e1_ps :
    Log8Psi false true 0 22 log8_g15np0e1_v.1 log8_g15np0e1_v.2.2.2 log8_g15np0e1_v.2.1 log8_g15np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g15np0e1_leaf log8_h17_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g15zm0e1_ps :
    Log8Psi true false 0 22 log8_g15zm0e1_v.1 log8_g15zm0e1_v.2.2.2 log8_g15zm0e1_v.2.1 log8_g15zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g15zm0e1_leaf log8_h17_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g15nm0e1_ps :
    Log8Psi false false 0 22 log8_g15nm0e1_v.1 log8_g15nm0e1_v.2.2.2 log8_g15nm0e1_v.2.1 log8_g15nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g15nm0e1_leaf log8_h17_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g21zp0e1_ps :
    Log8Psi true true 0 16 log8_g21zp0e1_v.1 log8_g21zp0e1_v.2.2.2 log8_g21zp0e1_v.2.1 log8_g21zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g21zp0e1_leaf log8_h23_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g21np0e1_ps :
    Log8Psi false true 0 16 log8_g21np0e1_v.1 log8_g21np0e1_v.2.2.2 log8_g21np0e1_v.2.1 log8_g21np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g21np0e1_leaf log8_h23_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g21zm0e1_ps :
    Log8Psi true false 0 16 log8_g21zm0e1_v.1 log8_g21zm0e1_v.2.2.2 log8_g21zm0e1_v.2.1 log8_g21zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g21zm0e1_leaf log8_h23_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g21nm0e1_ps :
    Log8Psi false false 0 16 log8_g21nm0e1_v.1 log8_g21nm0e1_v.2.2.2 log8_g21nm0e1_v.2.1 log8_g21nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g21nm0e1_leaf log8_h23_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g27zp0e1_ps :
    Log8Psi true true 0 10 log8_g27zp0e1_v.1 log8_g27zp0e1_v.2.2.2 log8_g27zp0e1_v.2.1 log8_g27zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g27zp0e1_leaf log8_h32_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g27np0e1_ps :
    Log8Psi false true 0 10 log8_g27np0e1_v.1 log8_g27np0e1_v.2.2.2 log8_g27np0e1_v.2.1 log8_g27np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g27np0e1_leaf log8_h31_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g27zm0e1_ps :
    Log8Psi true false 0 10 log8_g27zm0e1_v.1 log8_g27zm0e1_v.2.2.2 log8_g27zm0e1_v.2.1 log8_g27zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g27zm0e1_leaf log8_h32_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g27nm0e1_ps :
    Log8Psi false false 0 10 log8_g27nm0e1_v.1 log8_g27nm0e1_v.2.2.2 log8_g27nm0e1_v.2.1 log8_g27nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g27nm0e1_leaf log8_h31_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g35zp0e1_ps :
    Log8Psi true true 0 2 log8_g35zp0e1_v.1 log8_g35zp0e1_v.2.2.2 log8_g35zp0e1_v.2.1 log8_g35zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g35zp0e1_leaf log8_h54_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g35np0e1_ps :
    Log8Psi false true 0 2 log8_g35np0e1_v.1 log8_g35np0e1_v.2.2.2 log8_g35np0e1_v.2.1 log8_g35np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g35np0e1_leaf log8_h53_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g35zm0e1_ps :
    Log8Psi true false 0 2 log8_g35zm0e1_v.1 log8_g35zm0e1_v.2.2.2 log8_g35zm0e1_v.2.1 log8_g35zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g35zm0e1_leaf log8_h54_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g35nm0e1_ps :
    Log8Psi false false 0 2 log8_g35nm0e1_v.1 log8_g35nm0e1_v.2.2.2 log8_g35nm0e1_v.2.1 log8_g35nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g35nm0e1_leaf log8_h53_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g6zp0e1_ps :
    Log8Psi true true 0 40 log8_g6zp0e1_v.1 log8_g6zp0e1_v.2.2.2 log8_g6zp0e1_v.2.1 log8_g6zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g6zp0e1_leaf log8_h8_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g6np0e1_ps :
    Log8Psi false true 0 40 log8_g6np0e1_v.1 log8_g6np0e1_v.2.2.2 log8_g6np0e1_v.2.1 log8_g6np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g6np0e1_leaf log8_h8_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g6zm0e1_ps :
    Log8Psi true false 0 40 log8_g6zm0e1_v.1 log8_g6zm0e1_v.2.2.2 log8_g6zm0e1_v.2.1 log8_g6zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g6zm0e1_leaf log8_h8_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g6nm0e1_ps :
    Log8Psi false false 0 40 log8_g6nm0e1_v.1 log8_g6nm0e1_v.2.2.2 log8_g6nm0e1_v.2.1 log8_g6nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g6nm0e1_leaf log8_h8_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g10zp0e1_ps :
    Log8Psi true true 0 30 log8_g10zp0e1_v.1 log8_g10zp0e1_v.2.2.2 log8_g10zp0e1_v.2.1 log8_g10zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g10zp0e1_leaf log8_h12_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g10np0e1_ps :
    Log8Psi false true 0 30 log8_g10np0e1_v.1 log8_g10np0e1_v.2.2.2 log8_g10np0e1_v.2.1 log8_g10np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g10np0e1_leaf log8_h12_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g10zm0e1_ps :
    Log8Psi true false 0 30 log8_g10zm0e1_v.1 log8_g10zm0e1_v.2.2.2 log8_g10zm0e1_v.2.1 log8_g10zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g10zm0e1_leaf log8_h12_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g10nm0e1_ps :
    Log8Psi false false 0 30 log8_g10nm0e1_v.1 log8_g10nm0e1_v.2.2.2 log8_g10nm0e1_v.2.1 log8_g10nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g10nm0e1_leaf log8_h12_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g14zp0e1_ps :
    Log8Psi true true 0 23 log8_g14zp0e1_v.1 log8_g14zp0e1_v.2.2.2 log8_g14zp0e1_v.2.1 log8_g14zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g14zp0e1_leaf log8_h16_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g14np0e1_ps :
    Log8Psi false true 0 23 log8_g14np0e1_v.1 log8_g14np0e1_v.2.2.2 log8_g14np0e1_v.2.1 log8_g14np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g14np0e1_leaf log8_h16_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g14zm0e1_ps :
    Log8Psi true false 0 23 log8_g14zm0e1_v.1 log8_g14zm0e1_v.2.2.2 log8_g14zm0e1_v.2.1 log8_g14zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g14zm0e1_leaf log8_h16_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g14nm0e1_ps :
    Log8Psi false false 0 23 log8_g14nm0e1_v.1 log8_g14nm0e1_v.2.2.2 log8_g14nm0e1_v.2.1 log8_g14nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g14nm0e1_leaf log8_h16_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g31zp0e1_ps :
    Log8Psi true true 0 6 log8_g31zp0e1_v.1 log8_g31zp0e1_v.2.2.2 log8_g31zp0e1_v.2.1 log8_g31zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g31zp0e1_leaf log8_h44_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g31np0e1_ps :
    Log8Psi false true 0 6 log8_g31np0e1_v.1 log8_g31np0e1_v.2.2.2 log8_g31np0e1_v.2.1 log8_g31np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g31np0e1_leaf log8_h43_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g31zm0e1_ps :
    Log8Psi true false 0 6 log8_g31zm0e1_v.1 log8_g31zm0e1_v.2.2.2 log8_g31zm0e1_v.2.1 log8_g31zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g31zm0e1_leaf log8_h44_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g31nm0e1_ps :
    Log8Psi false false 0 6 log8_g31nm0e1_v.1 log8_g31nm0e1_v.2.2.2 log8_g31nm0e1_v.2.1 log8_g31nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g31nm0e1_leaf log8_h43_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g34zp0e1_ps :
    Log8Psi true true 0 3 log8_g34zp0e1_v.1 log8_g34zp0e1_v.2.2.2 log8_g34zp0e1_v.2.1 log8_g34zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g34zp0e1_leaf log8_h52_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g34np0e1_ps :
    Log8Psi false true 0 3 log8_g34np0e1_v.1 log8_g34np0e1_v.2.2.2 log8_g34np0e1_v.2.1 log8_g34np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g34np0e1_leaf log8_h51_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g34zm0e1_ps :
    Log8Psi true false 0 3 log8_g34zm0e1_v.1 log8_g34zm0e1_v.2.2.2 log8_g34zm0e1_v.2.1 log8_g34zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g34zm0e1_leaf log8_h52_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g34nm0e1_ps :
    Log8Psi false false 0 3 log8_g34nm0e1_v.1 log8_g34nm0e1_v.2.2.2 log8_g34nm0e1_v.2.1 log8_g34nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g34nm0e1_leaf log8_h51_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g7zp0e1_ps :
    Log8Psi true true 0 37 log8_g7zp0e1_v.1 log8_g7zp0e1_v.2.2.2 log8_g7zp0e1_v.2.1 log8_g7zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g7zp0e1_leaf log8_h9_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g7np0e1_ps :
    Log8Psi false true 0 37 log8_g7np0e1_v.1 log8_g7np0e1_v.2.2.2 log8_g7np0e1_v.2.1 log8_g7np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g7np0e1_leaf log8_h9_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g7zm0e1_ps :
    Log8Psi true false 0 37 log8_g7zm0e1_v.1 log8_g7zm0e1_v.2.2.2 log8_g7zm0e1_v.2.1 log8_g7zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g7zm0e1_leaf log8_h9_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g7nm0e1_ps :
    Log8Psi false false 0 37 log8_g7nm0e1_v.1 log8_g7nm0e1_v.2.2.2 log8_g7nm0e1_v.2.1 log8_g7nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g7nm0e1_leaf log8_h9_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g9zp0e1_ps :
    Log8Psi true true 0 32 log8_g9zp0e1_v.1 log8_g9zp0e1_v.2.2.2 log8_g9zp0e1_v.2.1 log8_g9zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g9zp0e1_leaf log8_h11_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g9np0e1_ps :
    Log8Psi false true 0 32 log8_g9np0e1_v.1 log8_g9np0e1_v.2.2.2 log8_g9np0e1_v.2.1 log8_g9np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g9np0e1_leaf log8_h11_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g9zm0e1_ps :
    Log8Psi true false 0 32 log8_g9zm0e1_v.1 log8_g9zm0e1_v.2.2.2 log8_g9zm0e1_v.2.1 log8_g9zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g9zm0e1_leaf log8_h11_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g9nm0e1_ps :
    Log8Psi false false 0 32 log8_g9nm0e1_v.1 log8_g9nm0e1_v.2.2.2 log8_g9nm0e1_v.2.1 log8_g9nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g9nm0e1_leaf log8_h11_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g20zp0e1_ps :
    Log8Psi true true 0 17 log8_g20zp0e1_v.1 log8_g20zp0e1_v.2.2.2 log8_g20zp0e1_v.2.1 log8_g20zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g20zp0e1_leaf log8_h22_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g20np0e1_ps :
    Log8Psi false true 0 17 log8_g20np0e1_v.1 log8_g20np0e1_v.2.2.2 log8_g20np0e1_v.2.1 log8_g20np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g20np0e1_leaf log8_h22_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g20zm0e1_ps :
    Log8Psi true false 0 17 log8_g20zm0e1_v.1 log8_g20zm0e1_v.2.2.2 log8_g20zm0e1_v.2.1 log8_g20zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g20zm0e1_leaf log8_h22_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g20nm0e1_ps :
    Log8Psi false false 0 17 log8_g20nm0e1_v.1 log8_g20nm0e1_v.2.2.2 log8_g20nm0e1_v.2.1 log8_g20nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g20nm0e1_leaf log8_h22_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g25zp0e1_ps :
    Log8Psi true true 0 12 log8_g25zp0e1_v.1 log8_g25zp0e1_v.2.2.2 log8_g25zp0e1_v.2.1 log8_g25zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g25zp0e1_leaf log8_h27_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g25np0e1_ps :
    Log8Psi false true 0 12 log8_g25np0e1_v.1 log8_g25np0e1_v.2.2.2 log8_g25np0e1_v.2.1 log8_g25np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g25np0e1_leaf log8_h27_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g25zm0e1_ps :
    Log8Psi true false 0 12 log8_g25zm0e1_v.1 log8_g25zm0e1_v.2.2.2 log8_g25zm0e1_v.2.1 log8_g25zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g25zm0e1_leaf log8_h27_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g25nm0e1_ps :
    Log8Psi false false 0 12 log8_g25nm0e1_v.1 log8_g25nm0e1_v.2.2.2 log8_g25nm0e1_v.2.1 log8_g25nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g25nm0e1_leaf log8_h27_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g29zp0e1_ps :
    Log8Psi true true 0 8 log8_g29zp0e1_v.1 log8_g29zp0e1_v.2.2.2 log8_g29zp0e1_v.2.1 log8_g29zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g29zp0e1_leaf log8_h38_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g29np0e1_ps :
    Log8Psi false true 0 8 log8_g29np0e1_v.1 log8_g29np0e1_v.2.2.2 log8_g29np0e1_v.2.1 log8_g29np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g29np0e1_leaf log8_h37_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g29zm0e1_ps :
    Log8Psi true false 0 8 log8_g29zm0e1_v.1 log8_g29zm0e1_v.2.2.2 log8_g29zm0e1_v.2.1 log8_g29zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g29zm0e1_leaf log8_h38_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g29nm0e1_ps :
    Log8Psi false false 0 8 log8_g29nm0e1_v.1 log8_g29nm0e1_v.2.2.2 log8_g29nm0e1_v.2.1 log8_g29nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g29nm0e1_leaf log8_h37_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g8zp0e1_ps :
    Log8Psi true true 0 34 log8_g8zp0e1_v.1 log8_g8zp0e1_v.2.2.2 log8_g8zp0e1_v.2.1 log8_g8zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g8zp0e1_leaf log8_h10_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g8np0e1_ps :
    Log8Psi false true 0 34 log8_g8np0e1_v.1 log8_g8np0e1_v.2.2.2 log8_g8np0e1_v.2.1 log8_g8np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g8np0e1_leaf log8_h10_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g8zm0e1_ps :
    Log8Psi true false 0 34 log8_g8zm0e1_v.1 log8_g8zm0e1_v.2.2.2 log8_g8zm0e1_v.2.1 log8_g8zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g8zm0e1_leaf log8_h10_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g8nm0e1_ps :
    Log8Psi false false 0 34 log8_g8nm0e1_v.1 log8_g8nm0e1_v.2.2.2 log8_g8nm0e1_v.2.1 log8_g8nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g8nm0e1_leaf log8_h10_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g13zp0e1_ps :
    Log8Psi true true 0 25 log8_g13zp0e1_v.1 log8_g13zp0e1_v.2.2.2 log8_g13zp0e1_v.2.1 log8_g13zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g13zp0e1_leaf log8_h15_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g13np0e1_ps :
    Log8Psi false true 0 25 log8_g13np0e1_v.1 log8_g13np0e1_v.2.2.2 log8_g13np0e1_v.2.1 log8_g13np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g13np0e1_leaf log8_h15_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g13zm0e1_ps :
    Log8Psi true false 0 25 log8_g13zm0e1_v.1 log8_g13zm0e1_v.2.2.2 log8_g13zm0e1_v.2.1 log8_g13zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g13zm0e1_leaf log8_h15_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g13nm0e1_ps :
    Log8Psi false false 0 25 log8_g13nm0e1_v.1 log8_g13nm0e1_v.2.2.2 log8_g13nm0e1_v.2.1 log8_g13nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g13nm0e1_leaf log8_h15_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g19zp0e1_ps :
    Log8Psi true true 0 18 log8_g19zp0e1_v.1 log8_g19zp0e1_v.2.2.2 log8_g19zp0e1_v.2.1 log8_g19zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g19zp0e1_leaf log8_h21_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g19np0e1_ps :
    Log8Psi false true 0 18 log8_g19np0e1_v.1 log8_g19np0e1_v.2.2.2 log8_g19np0e1_v.2.1 log8_g19np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g19np0e1_leaf log8_h21_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g19zm0e1_ps :
    Log8Psi true false 0 18 log8_g19zm0e1_v.1 log8_g19zm0e1_v.2.2.2 log8_g19zm0e1_v.2.1 log8_g19zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g19zm0e1_leaf log8_h21_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g19nm0e1_ps :
    Log8Psi false false 0 18 log8_g19nm0e1_v.1 log8_g19nm0e1_v.2.2.2 log8_g19nm0e1_v.2.1 log8_g19nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g19nm0e1_leaf log8_h21_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g26zp0e1_ps :
    Log8Psi true true 0 11 log8_g26zp0e1_v.1 log8_g26zp0e1_v.2.2.2 log8_g26zp0e1_v.2.1 log8_g26zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g26zp0e1_leaf log8_h29_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g26np0e1_ps :
    Log8Psi false true 0 11 log8_g26np0e1_v.1 log8_g26np0e1_v.2.2.2 log8_g26np0e1_v.2.1 log8_g26np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g26np0e1_leaf log8_h28_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g26zm0e1_ps :
    Log8Psi true false 0 11 log8_g26zm0e1_v.1 log8_g26zm0e1_v.2.2.2 log8_g26zm0e1_v.2.1 log8_g26zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g26zm0e1_leaf log8_h29_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g26nm0e1_ps :
    Log8Psi false false 0 11 log8_g26nm0e1_v.1 log8_g26nm0e1_v.2.2.2 log8_g26nm0e1_v.2.1 log8_g26nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g26nm0e1_leaf log8_h28_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g33zp0e1_ps :
    Log8Psi true true 0 4 log8_g33zp0e1_v.1 log8_g33zp0e1_v.2.2.2 log8_g33zp0e1_v.2.1 log8_g33zp0e1_v.2.2.1 :=
  Log8Psi.mk log8_g33zp0e1_leaf log8_h50_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g33np0e1_ps :
    Log8Psi false true 0 4 log8_g33np0e1_v.1 log8_g33np0e1_v.2.2.2 log8_g33np0e1_v.2.1 log8_g33np0e1_v.2.2.1 :=
  Log8Psi.mk log8_g33np0e1_leaf log8_h49_hp rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g33zm0e1_ps :
    Log8Psi true false 0 4 log8_g33zm0e1_v.1 log8_g33zm0e1_v.2.2.2 log8_g33zm0e1_v.2.1 log8_g33zm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g33zm0e1_leaf log8_h50_hm rfl (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem log8_g33nm0e1_ps :
    Log8Psi false false 0 4 log8_g33nm0e1_v.1 log8_g33nm0e1_v.2.2.2 log8_g33nm0e1_v.2.1 log8_g33nm0e1_v.2.2.1 :=
  Log8Psi.mk log8_g33nm0e1_leaf log8_h49_hm rfl (by decide +kernel)

theorem log8_psi0 : ∀ g ∈ log8Grp0, Log8GroupT0 g := by
  intro g hg
  simp only [log8Grp0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    intro pos
    cases pos
    · exact log8_g0zm0e1_ps
    · exact log8_g0zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g1zm0e1_ps
    · exact log8_g1zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g2zm0e1_ps
    · exact log8_g2zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g3zm0e1_ps
    · exact log8_g3zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g4zm0e1_ps
    · exact log8_g4zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g5zm0e1_ps
    · exact log8_g5zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g6zm0e1_ps
    · exact log8_g6zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g7zm0e1_ps
    · exact log8_g7zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g8zm0e1_ps
    · exact log8_g8zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g9zm0e1_ps
    · exact log8_g9zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g10zm0e1_ps
    · exact log8_g10zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g11zm0e1_ps
    · exact log8_g11zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g12zm0e1_ps
    · exact log8_g12zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g13zm0e1_ps
    · exact log8_g13zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g14zm0e1_ps
    · exact log8_g14zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g15zm0e1_ps
    · exact log8_g15zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g16zm0e1_ps
    · exact log8_g16zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g17zm0e1_ps
    · exact log8_g17zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g18zm0e1_ps
    · exact log8_g18zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g19zm0e1_ps
    · exact log8_g19zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g20zm0e1_ps
    · exact log8_g20zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g21zm0e1_ps
    · exact log8_g21zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g22zm0e1_ps
    · exact log8_g22zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g23zm0e1_ps
    · exact log8_g23zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g24zm0e1_ps
    · exact log8_g24zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g25zm0e1_ps
    · exact log8_g25zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g26zm0e1_ps
    · exact log8_g26zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g27zm0e1_ps
    · exact log8_g27zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g28zm0e1_ps
    · exact log8_g28zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g29zm0e1_ps
    · exact log8_g29zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g30zm0e1_ps
    · exact log8_g30zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g31zm0e1_ps
    · exact log8_g31zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g32zm0e1_ps
    · exact log8_g32zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g33zm0e1_ps
    · exact log8_g33zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g34zm0e1_ps
    · exact log8_g34zp0e1_ps
  ·
    intro pos
    cases pos
    · exact log8_g35zm0e1_ps
    · exact log8_g35zp0e1_ps

theorem log8_psi_last0 : Log8GroupT0 log8Last0 := by
  intro pos
  cases pos
  · exact log8_g36zm0e1_ps
  · exact log8_g36zp0e1_ps

theorem log8_psi1 : ∀ g ∈ log8Grp1, Log8GroupT1 g := by
  intro g hg
  simp only [log8Grp1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g0np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl
      · exact log8_g0nm0e1_ps
      · exact log8_g0nm1e1_ps
      · exact log8_g0nm2e1_ps
      · exact log8_g0nm3e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g1np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g1nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g2np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g2nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g3np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g3nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g4np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g4nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g5np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g5nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g6np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g6nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g7np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g7nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g8np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g8nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g9np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g9nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g10np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g10nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g11np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g11nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g12np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g12nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g13np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g13nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g14np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g14nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g15np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g15nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g16np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g16nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g17np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g17nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g18np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g18nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g19np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g19nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g20np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g20nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g21np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g21nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g22np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g22nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g23np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g23nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g24np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g24nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g25np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g25nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g26np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g26nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g27np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g27nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g28np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g28nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g29np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g29nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g30np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g30nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g31np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g31nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g32np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g32nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g33np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g33nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g34np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g34nm0e1_ps
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g35np0e1_ps
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact log8_g35nm0e1_ps

theorem log8_psi_last1 : Log8GroupT1 log8Last1 := by
  refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
  · simp only [log8Last1, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl
    · exact log8_g36np0e1_ps
  · simp only [log8Last1, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl
    · exact log8_g36nm0e1_ps

end ExpansionBounds
