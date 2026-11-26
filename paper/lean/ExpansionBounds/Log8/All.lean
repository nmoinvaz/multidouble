import ExpansionBounds.Log8.Run0
import ExpansionBounds.Log8.Run1
import ExpansionBounds.Log8.Run2
import ExpansionBounds.Log8.Run3
import ExpansionBounds.Log8.Run4
import ExpansionBounds.Log8.Run5
import ExpansionBounds.Log8.Run6
import ExpansionBounds.Log8.Run7
import ExpansionBounds.Log8.Run8
import ExpansionBounds.Log8.Table

/-!
# Theorem 42 at `n = 8` and `p = 53`: every state and every evaluation

The kernel's checks of `Log8/Run0.lean` to `Run8.lean` joined: `Log8Head` for each state of a group and each sign,
from the pieces of Horner's run, the two products and the sum; and `Log8Eval` for each case, sign and end, from its
rational bounds, its state, the squarings, the two pieces of step (4) and the bound. This file is written by
`log_lean.py`.
-/

namespace ExpansionBounds

theorem log8_h0_q : ∀ q ∈ log8_h0_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h0_r : log8Run log8_h0_pq log8_h0_bp 43 0 41 (hornerInitL 8 exp8F exp8Phi 43) =
    dySt log8_h0_s41 :=
  log8Run_cut log8_h0_pq log8_h0_bp 43 _ 2 39 log8_h0_r0_2
    (log8Run_cut log8_h0_pq log8_h0_bp 43 _ 2 37 log8_h0_r2_4
    (log8Run_cut log8_h0_pq log8_h0_bp 43 _ 2 35 log8_h0_r4_6
    (log8Run_cut log8_h0_pq log8_h0_bp 43 _ 2 33 log8_h0_r6_8
    (log8Run_cut log8_h0_pq log8_h0_bp 43 _ 2 31 log8_h0_r8_10
    (log8Run_cut log8_h0_pq log8_h0_bp 43 _ 2 29 log8_h0_r10_12
    (log8Run_cut log8_h0_pq log8_h0_bp 43 _ 2 27 log8_h0_r12_14
    (log8Run_cut log8_h0_pq log8_h0_bp 43 _ 2 25 log8_h0_r14_16
    (log8Run_cut log8_h0_pq log8_h0_bp 43 _ 2 23 log8_h0_r16_18
    (log8Run_cut log8_h0_pq log8_h0_bp 43 _ 2 21 log8_h0_r18_20
    (log8Run_cut log8_h0_pq log8_h0_bp 43 _ 2 19 log8_h0_r20_22
    (log8Run_cut log8_h0_pq log8_h0_bp 43 _ 2 17 log8_h0_r22_24
    (log8Run_cut log8_h0_pq log8_h0_bp 43 _ 2 15 log8_h0_r24_26
    (log8Run_cut log8_h0_pq log8_h0_bp 43 _ 2 13 log8_h0_r26_28
    (log8Run_cut log8_h0_pq log8_h0_bp 43 _ 2 11 log8_h0_r28_30
    (log8Run_cut log8_h0_pq log8_h0_bp 43 _ 2 9 log8_h0_r30_32
    (log8Run_cut log8_h0_pq log8_h0_bp 43 _ 2 7 log8_h0_r32_34
    (log8Run_cut log8_h0_pq log8_h0_bp 43 _ 2 5 log8_h0_r34_36
    (log8Run_cut log8_h0_pq log8_h0_bp 43 _ 2 3 log8_h0_r36_38
    (log8Run_cut log8_h0_pq log8_h0_bp 43 _ 2 1 log8_h0_r38_40
    (log8_h0_r40_41))))))))))))))))))))

theorem log8_h0_hp : Log8Head true 5 43 log8_h0_pq log8_h0_bp (dySt log8_h0_tp) :=
  Log8Head.mk_ne (by decide) log8_h0_q log8_h0_r log8_h0_wt log8_h0_yt log8_h0_tpt

theorem log8_h0_hm : Log8Head false 5 43 log8_h0_pq log8_h0_bp (dySt log8_h0_tm) :=
  Log8Head.mk_ne (by decide) log8_h0_q log8_h0_r log8_h0_wt log8_h0_yt log8_h0_tmt

theorem log8_g0zp0e0_sq :
    log8SqRun true 5 log8_g0zp0e0_v.1 log8_g0zp0e0_v.2.1 5 (dySt log8_h0_tp) =
      dySt log8_g0zp0e0_s5 := by
  show log8Sq true 5 log8_g0zp0e0_v.1 log8_g0zp0e0_v.2.1 4
      (log8Sq true 5 log8_g0zp0e0_v.1 log8_g0zp0e0_v.2.1 3
      (log8Sq true 5 log8_g0zp0e0_v.1 log8_g0zp0e0_v.2.1 2
      (log8Sq true 5 log8_g0zp0e0_v.1 log8_g0zp0e0_v.2.1 1
      (log8Sq true 5 log8_g0zp0e0_v.1 log8_g0zp0e0_v.2.1 0
      (dySt log8_h0_tp))))) = _
  rw [log8_g0zp0e0_q0_2, log8_g0zp0e0_q2_4, log8_g0zp0e0_q4_5]

theorem log8_g0zp0e0_ev :
    Log8Eval true true 5 43 log8_g0zp0e0_v.1 log8_g0zp0e0_v.2.2.2 false log8_g0zp0e0_v.2.1 log8_g0zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g0zp0e0_leaf log8_h0_hp log8_g0zp0e0_sq log8_g0zp0e0_a log8_g0zp0e0_b log8_g0zp0e0_end

theorem log8_g0zp0e1_sq :
    log8SqRun true 5 log8_g0zp0e1_v.1 log8_g0zp0e1_v.2.1 5 (dySt log8_h0_tp) =
      dySt log8_g0zp0e1_s5 := by
  show log8Sq true 5 log8_g0zp0e1_v.1 log8_g0zp0e1_v.2.1 4
      (log8Sq true 5 log8_g0zp0e1_v.1 log8_g0zp0e1_v.2.1 3
      (log8Sq true 5 log8_g0zp0e1_v.1 log8_g0zp0e1_v.2.1 2
      (log8Sq true 5 log8_g0zp0e1_v.1 log8_g0zp0e1_v.2.1 1
      (log8Sq true 5 log8_g0zp0e1_v.1 log8_g0zp0e1_v.2.1 0
      (dySt log8_h0_tp))))) = _
  rw [log8_g0zp0e1_q0_2, log8_g0zp0e1_q2_4, log8_g0zp0e1_q4_5]

theorem log8_g0zp0e1_ev :
    Log8Eval true true 5 43 log8_g0zp0e1_v.1 log8_g0zp0e1_v.2.2.2 false log8_g0zp0e1_v.2.1 log8_g0zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g0zp0e1_leaf log8_h0_hp log8_g0zp0e1_sq log8_g0zp0e1_a log8_g0zp0e1_b log8_g0zp0e1_end

theorem log8_g0np0e0_sq :
    log8SqRun true 5 log8_g0np0e0_v.1 log8_g0np0e0_v.2.1 5 (dySt log8_h0_tp) =
      dySt log8_g0np0e0_s5 := by
  show log8Sq true 5 log8_g0np0e0_v.1 log8_g0np0e0_v.2.1 4
      (log8Sq true 5 log8_g0np0e0_v.1 log8_g0np0e0_v.2.1 3
      (log8Sq true 5 log8_g0np0e0_v.1 log8_g0np0e0_v.2.1 2
      (log8Sq true 5 log8_g0np0e0_v.1 log8_g0np0e0_v.2.1 1
      (log8Sq true 5 log8_g0np0e0_v.1 log8_g0np0e0_v.2.1 0
      (dySt log8_h0_tp))))) = _
  rw [log8_g0np0e0_q0_2, log8_g0np0e0_q2_4, log8_g0np0e0_q4_5]

theorem log8_g0np0e0_ev :
    Log8Eval false true 5 43 log8_g0np0e0_v.1 log8_g0np0e0_v.2.2.2 false log8_g0np0e0_v.2.1 log8_g0np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g0np0e0_leaf log8_h0_hp log8_g0np0e0_sq log8_g0np0e0_a log8_g0np0e0_b log8_g0np0e0_end

theorem log8_g0np0e1_sq :
    log8SqRun true 5 log8_g0np0e1_v.1 log8_g0np0e1_v.2.1 5 (dySt log8_h0_tp) =
      dySt log8_g0np0e1_s5 := by
  show log8Sq true 5 log8_g0np0e1_v.1 log8_g0np0e1_v.2.1 4
      (log8Sq true 5 log8_g0np0e1_v.1 log8_g0np0e1_v.2.1 3
      (log8Sq true 5 log8_g0np0e1_v.1 log8_g0np0e1_v.2.1 2
      (log8Sq true 5 log8_g0np0e1_v.1 log8_g0np0e1_v.2.1 1
      (log8Sq true 5 log8_g0np0e1_v.1 log8_g0np0e1_v.2.1 0
      (dySt log8_h0_tp))))) = _
  rw [log8_g0np0e1_q0_2, log8_g0np0e1_q2_4, log8_g0np0e1_q4_5]

theorem log8_g0np0e1_ev :
    Log8Eval false true 5 43 log8_g0np0e1_v.1 log8_g0np0e1_v.2.2.2 false log8_g0np0e1_v.2.1 log8_g0np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g0np0e1_leaf log8_h0_hp log8_g0np0e1_sq log8_g0np0e1_a log8_g0np0e1_b log8_g0np0e1_end

theorem log8_g0zm0e0_sq :
    log8SqRun false 5 log8_g0zm0e0_v.1 log8_g0zm0e0_v.2.1 5 (dySt log8_h0_tm) =
      dySt log8_g0zm0e0_s5 := by
  show log8Sq false 5 log8_g0zm0e0_v.1 log8_g0zm0e0_v.2.1 4
      (log8Sq false 5 log8_g0zm0e0_v.1 log8_g0zm0e0_v.2.1 3
      (log8Sq false 5 log8_g0zm0e0_v.1 log8_g0zm0e0_v.2.1 2
      (log8Sq false 5 log8_g0zm0e0_v.1 log8_g0zm0e0_v.2.1 1
      (log8Sq false 5 log8_g0zm0e0_v.1 log8_g0zm0e0_v.2.1 0
      (dySt log8_h0_tm))))) = _
  rw [log8_g0zm0e0_q0_2, log8_g0zm0e0_q2_4, log8_g0zm0e0_q4_5]

theorem log8_g0zm0e0_ev :
    Log8Eval true false 5 43 log8_g0zm0e0_v.1 log8_g0zm0e0_v.2.2.2 false log8_g0zm0e0_v.2.1 log8_g0zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g0zm0e0_leaf log8_h0_hm log8_g0zm0e0_sq log8_g0zm0e0_a log8_g0zm0e0_b log8_g0zm0e0_end

theorem log8_g0zm0e1_sq :
    log8SqRun false 5 log8_g0zm0e1_v.1 log8_g0zm0e1_v.2.1 5 (dySt log8_h0_tm) =
      dySt log8_g0zm0e1_s5 := by
  show log8Sq false 5 log8_g0zm0e1_v.1 log8_g0zm0e1_v.2.1 4
      (log8Sq false 5 log8_g0zm0e1_v.1 log8_g0zm0e1_v.2.1 3
      (log8Sq false 5 log8_g0zm0e1_v.1 log8_g0zm0e1_v.2.1 2
      (log8Sq false 5 log8_g0zm0e1_v.1 log8_g0zm0e1_v.2.1 1
      (log8Sq false 5 log8_g0zm0e1_v.1 log8_g0zm0e1_v.2.1 0
      (dySt log8_h0_tm))))) = _
  rw [log8_g0zm0e1_q0_2, log8_g0zm0e1_q2_4, log8_g0zm0e1_q4_5]

theorem log8_g0zm0e1_ev :
    Log8Eval true false 5 43 log8_g0zm0e1_v.1 log8_g0zm0e1_v.2.2.2 false log8_g0zm0e1_v.2.1 log8_g0zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g0zm0e1_leaf log8_h0_hm log8_g0zm0e1_sq log8_g0zm0e1_a log8_g0zm0e1_b log8_g0zm0e1_end

theorem log8_g0nm0e0_sq :
    log8SqRun false 5 log8_g0nm0e0_v.1 log8_g0nm0e0_v.2.1 5 (dySt log8_h0_tm) =
      dySt log8_g0nm0e0_s5 := by
  show log8Sq false 5 log8_g0nm0e0_v.1 log8_g0nm0e0_v.2.1 4
      (log8Sq false 5 log8_g0nm0e0_v.1 log8_g0nm0e0_v.2.1 3
      (log8Sq false 5 log8_g0nm0e0_v.1 log8_g0nm0e0_v.2.1 2
      (log8Sq false 5 log8_g0nm0e0_v.1 log8_g0nm0e0_v.2.1 1
      (log8Sq false 5 log8_g0nm0e0_v.1 log8_g0nm0e0_v.2.1 0
      (dySt log8_h0_tm))))) = _
  rw [log8_g0nm0e0_q0_2, log8_g0nm0e0_q2_4, log8_g0nm0e0_q4_5]

theorem log8_g0nm0e0_ev :
    Log8Eval false false 5 43 log8_g0nm0e0_v.1 log8_g0nm0e0_v.2.2.2 false log8_g0nm0e0_v.2.1 log8_g0nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g0nm0e0_leaf log8_h0_hm log8_g0nm0e0_sq log8_g0nm0e0_a log8_g0nm0e0_b log8_g0nm0e0_end

theorem log8_g0nm0e1_sq :
    log8SqRun false 5 log8_g0nm0e1_v.1 log8_g0nm0e1_v.2.1 5 (dySt log8_h0_tm) =
      dySt log8_g0nm0e1_s5 := by
  show log8Sq false 5 log8_g0nm0e1_v.1 log8_g0nm0e1_v.2.1 4
      (log8Sq false 5 log8_g0nm0e1_v.1 log8_g0nm0e1_v.2.1 3
      (log8Sq false 5 log8_g0nm0e1_v.1 log8_g0nm0e1_v.2.1 2
      (log8Sq false 5 log8_g0nm0e1_v.1 log8_g0nm0e1_v.2.1 1
      (log8Sq false 5 log8_g0nm0e1_v.1 log8_g0nm0e1_v.2.1 0
      (dySt log8_h0_tm))))) = _
  rw [log8_g0nm0e1_q0_2, log8_g0nm0e1_q2_4, log8_g0nm0e1_q4_5]

theorem log8_g0nm0e1_ev :
    Log8Eval false false 5 43 log8_g0nm0e1_v.1 log8_g0nm0e1_v.2.2.2 false log8_g0nm0e1_v.2.1 log8_g0nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g0nm0e1_leaf log8_h0_hm log8_g0nm0e1_sq log8_g0nm0e1_a log8_g0nm0e1_b log8_g0nm0e1_end

theorem log8_g0nm1e0_sq :
    log8SqRun false 5 log8_g0nm1e0_v.1 log8_g0nm1e0_v.2.1 5 (dySt log8_h0_tm) =
      dySt log8_g0nm1e0_s5 := by
  show log8Sq false 5 log8_g0nm1e0_v.1 log8_g0nm1e0_v.2.1 4
      (log8Sq false 5 log8_g0nm1e0_v.1 log8_g0nm1e0_v.2.1 3
      (log8Sq false 5 log8_g0nm1e0_v.1 log8_g0nm1e0_v.2.1 2
      (log8Sq false 5 log8_g0nm1e0_v.1 log8_g0nm1e0_v.2.1 1
      (log8Sq false 5 log8_g0nm1e0_v.1 log8_g0nm1e0_v.2.1 0
      (dySt log8_h0_tm))))) = _
  rw [log8_g0nm1e0_q0_2, log8_g0nm1e0_q2_4, log8_g0nm1e0_q4_5]

theorem log8_g0nm1e0_ev :
    Log8Eval false false 5 43 log8_g0nm1e0_v.1 log8_g0nm1e0_v.2.2.2 false log8_g0nm1e0_v.2.1 log8_g0nm1e0_v.2.2.1 :=
  Log8Eval.mk log8_g0nm1e0_leaf log8_h0_hm log8_g0nm1e0_sq log8_g0nm1e0_a log8_g0nm1e0_b log8_g0nm1e0_end

theorem log8_g0nm1e1_sq :
    log8SqRun false 5 log8_g0nm1e1_v.1 log8_g0nm1e1_v.2.1 5 (dySt log8_h0_tm) =
      dySt log8_g0nm1e1_s5 := by
  show log8Sq false 5 log8_g0nm1e1_v.1 log8_g0nm1e1_v.2.1 4
      (log8Sq false 5 log8_g0nm1e1_v.1 log8_g0nm1e1_v.2.1 3
      (log8Sq false 5 log8_g0nm1e1_v.1 log8_g0nm1e1_v.2.1 2
      (log8Sq false 5 log8_g0nm1e1_v.1 log8_g0nm1e1_v.2.1 1
      (log8Sq false 5 log8_g0nm1e1_v.1 log8_g0nm1e1_v.2.1 0
      (dySt log8_h0_tm))))) = _
  rw [log8_g0nm1e1_q0_2, log8_g0nm1e1_q2_4, log8_g0nm1e1_q4_5]

theorem log8_g0nm1e1_ev :
    Log8Eval false false 5 43 log8_g0nm1e1_v.1 log8_g0nm1e1_v.2.2.2 false log8_g0nm1e1_v.2.1 log8_g0nm1e1_v.2.2.1 :=
  Log8Eval.mk log8_g0nm1e1_leaf log8_h0_hm log8_g0nm1e1_sq log8_g0nm1e1_a log8_g0nm1e1_b log8_g0nm1e1_end

theorem log8_g0nm2e0_sq :
    log8SqRun false 5 log8_g0nm2e0_v.1 log8_g0nm2e0_v.2.1 5 (dySt log8_h0_tm) =
      dySt log8_g0nm2e0_s5 := by
  show log8Sq false 5 log8_g0nm2e0_v.1 log8_g0nm2e0_v.2.1 4
      (log8Sq false 5 log8_g0nm2e0_v.1 log8_g0nm2e0_v.2.1 3
      (log8Sq false 5 log8_g0nm2e0_v.1 log8_g0nm2e0_v.2.1 2
      (log8Sq false 5 log8_g0nm2e0_v.1 log8_g0nm2e0_v.2.1 1
      (log8Sq false 5 log8_g0nm2e0_v.1 log8_g0nm2e0_v.2.1 0
      (dySt log8_h0_tm))))) = _
  rw [log8_g0nm2e0_q0_2, log8_g0nm2e0_q2_4, log8_g0nm2e0_q4_5]

theorem log8_g0nm2e0_ev :
    Log8Eval false false 5 43 log8_g0nm2e0_v.1 log8_g0nm2e0_v.2.2.2 false log8_g0nm2e0_v.2.1 log8_g0nm2e0_v.2.2.1 :=
  Log8Eval.mk log8_g0nm2e0_leaf log8_h0_hm log8_g0nm2e0_sq log8_g0nm2e0_a log8_g0nm2e0_b log8_g0nm2e0_end

theorem log8_g0nm2e1_sq :
    log8SqRun false 5 log8_g0nm2e1_v.1 log8_g0nm2e1_v.2.1 5 (dySt log8_h0_tm) =
      dySt log8_g0nm2e1_s5 := by
  show log8Sq false 5 log8_g0nm2e1_v.1 log8_g0nm2e1_v.2.1 4
      (log8Sq false 5 log8_g0nm2e1_v.1 log8_g0nm2e1_v.2.1 3
      (log8Sq false 5 log8_g0nm2e1_v.1 log8_g0nm2e1_v.2.1 2
      (log8Sq false 5 log8_g0nm2e1_v.1 log8_g0nm2e1_v.2.1 1
      (log8Sq false 5 log8_g0nm2e1_v.1 log8_g0nm2e1_v.2.1 0
      (dySt log8_h0_tm))))) = _
  rw [log8_g0nm2e1_q0_2, log8_g0nm2e1_q2_4, log8_g0nm2e1_q4_5]

theorem log8_g0nm2e1_ev :
    Log8Eval false false 5 43 log8_g0nm2e1_v.1 log8_g0nm2e1_v.2.2.2 false log8_g0nm2e1_v.2.1 log8_g0nm2e1_v.2.2.1 :=
  Log8Eval.mk log8_g0nm2e1_leaf log8_h0_hm log8_g0nm2e1_sq log8_g0nm2e1_a log8_g0nm2e1_b log8_g0nm2e1_end

theorem log8_g0nm3e0_sq :
    log8SqRun false 5 log8_g0nm3e0_v.1 log8_g0nm3e0_v.2.1 5 (dySt log8_h0_tm) =
      dySt log8_g0nm3e0_s5 := by
  show log8Sq false 5 log8_g0nm3e0_v.1 log8_g0nm3e0_v.2.1 4
      (log8Sq false 5 log8_g0nm3e0_v.1 log8_g0nm3e0_v.2.1 3
      (log8Sq false 5 log8_g0nm3e0_v.1 log8_g0nm3e0_v.2.1 2
      (log8Sq false 5 log8_g0nm3e0_v.1 log8_g0nm3e0_v.2.1 1
      (log8Sq false 5 log8_g0nm3e0_v.1 log8_g0nm3e0_v.2.1 0
      (dySt log8_h0_tm))))) = _
  rw [log8_g0nm3e0_q0_2, log8_g0nm3e0_q2_4, log8_g0nm3e0_q4_5]

theorem log8_g0nm3e0_ev :
    Log8Eval false false 5 43 log8_g0nm3e0_v.1 log8_g0nm3e0_v.2.2.2 false log8_g0nm3e0_v.2.1 log8_g0nm3e0_v.2.2.1 :=
  Log8Eval.mk log8_g0nm3e0_leaf log8_h0_hm log8_g0nm3e0_sq log8_g0nm3e0_a log8_g0nm3e0_b log8_g0nm3e0_end

theorem log8_g0nm3e1_sq :
    log8SqRun false 5 log8_g0nm3e1_v.1 log8_g0nm3e1_v.2.1 5 (dySt log8_h0_tm) =
      dySt log8_g0nm3e1_s5 := by
  show log8Sq false 5 log8_g0nm3e1_v.1 log8_g0nm3e1_v.2.1 4
      (log8Sq false 5 log8_g0nm3e1_v.1 log8_g0nm3e1_v.2.1 3
      (log8Sq false 5 log8_g0nm3e1_v.1 log8_g0nm3e1_v.2.1 2
      (log8Sq false 5 log8_g0nm3e1_v.1 log8_g0nm3e1_v.2.1 1
      (log8Sq false 5 log8_g0nm3e1_v.1 log8_g0nm3e1_v.2.1 0
      (dySt log8_h0_tm))))) = _
  rw [log8_g0nm3e1_q0_2, log8_g0nm3e1_q2_4, log8_g0nm3e1_q4_5]

theorem log8_g0nm3e1_ev :
    Log8Eval false false 5 43 log8_g0nm3e1_v.1 log8_g0nm3e1_v.2.2.2 false log8_g0nm3e1_v.2.1 log8_g0nm3e1_v.2.2.1 :=
  Log8Eval.mk log8_g0nm3e1_leaf log8_h0_hm log8_g0nm3e1_sq log8_g0nm3e1_a log8_g0nm3e1_b log8_g0nm3e1_end

theorem log8_h5_q : ∀ q ∈ log8_h5_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h5_r : log8Run log8_h5_pq log8_h5_bp 43 0 41 (hornerInitL 8 exp8F exp8Phi 43) =
    dySt log8_h5_s41 :=
  log8Run_cut log8_h5_pq log8_h5_bp 43 _ 2 39 log8_h5_r0_2
    (log8Run_cut log8_h5_pq log8_h5_bp 43 _ 2 37 log8_h5_r2_4
    (log8Run_cut log8_h5_pq log8_h5_bp 43 _ 2 35 log8_h5_r4_6
    (log8Run_cut log8_h5_pq log8_h5_bp 43 _ 2 33 log8_h5_r6_8
    (log8Run_cut log8_h5_pq log8_h5_bp 43 _ 2 31 log8_h5_r8_10
    (log8Run_cut log8_h5_pq log8_h5_bp 43 _ 2 29 log8_h5_r10_12
    (log8Run_cut log8_h5_pq log8_h5_bp 43 _ 2 27 log8_h5_r12_14
    (log8Run_cut log8_h5_pq log8_h5_bp 43 _ 2 25 log8_h5_r14_16
    (log8Run_cut log8_h5_pq log8_h5_bp 43 _ 2 23 log8_h5_r16_18
    (log8Run_cut log8_h5_pq log8_h5_bp 43 _ 2 21 log8_h5_r18_20
    (log8Run_cut log8_h5_pq log8_h5_bp 43 _ 2 19 log8_h5_r20_22
    (log8Run_cut log8_h5_pq log8_h5_bp 43 _ 2 17 log8_h5_r22_24
    (log8Run_cut log8_h5_pq log8_h5_bp 43 _ 2 15 log8_h5_r24_26
    (log8Run_cut log8_h5_pq log8_h5_bp 43 _ 2 13 log8_h5_r26_28
    (log8Run_cut log8_h5_pq log8_h5_bp 43 _ 2 11 log8_h5_r28_30
    (log8Run_cut log8_h5_pq log8_h5_bp 43 _ 2 9 log8_h5_r30_32
    (log8Run_cut log8_h5_pq log8_h5_bp 43 _ 2 7 log8_h5_r32_34
    (log8Run_cut log8_h5_pq log8_h5_bp 43 _ 2 5 log8_h5_r34_36
    (log8Run_cut log8_h5_pq log8_h5_bp 43 _ 2 3 log8_h5_r36_38
    (log8Run_cut log8_h5_pq log8_h5_bp 43 _ 2 1 log8_h5_r38_40
    (log8_h5_r40_41))))))))))))))))))))

theorem log8_h5_hp : Log8Head true 0 43 log8_h5_pq log8_h5_bp (dySt log8_h5_tp) :=
  Log8Head.mk_ne (by decide) log8_h5_q log8_h5_r log8_h5_wt log8_h5_yt log8_h5_tpt

theorem log8_h5_hm : Log8Head false 0 43 log8_h5_pq log8_h5_bp (dySt log8_h5_tm) :=
  Log8Head.mk_ne (by decide) log8_h5_q log8_h5_r log8_h5_wt log8_h5_yt log8_h5_tmt

theorem log8_h6_q : ∀ q ∈ log8_h6_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h6_r : log8Run log8_h6_pq log8_h6_bp 43 0 41 (hornerInitL 8 exp8F exp8Phi 43) =
    dySt log8_h6_s41 :=
  log8Run_cut log8_h6_pq log8_h6_bp 43 _ 2 39 log8_h6_r0_2
    (log8Run_cut log8_h6_pq log8_h6_bp 43 _ 2 37 log8_h6_r2_4
    (log8Run_cut log8_h6_pq log8_h6_bp 43 _ 2 35 log8_h6_r4_6
    (log8Run_cut log8_h6_pq log8_h6_bp 43 _ 2 33 log8_h6_r6_8
    (log8Run_cut log8_h6_pq log8_h6_bp 43 _ 2 31 log8_h6_r8_10
    (log8Run_cut log8_h6_pq log8_h6_bp 43 _ 2 29 log8_h6_r10_12
    (log8Run_cut log8_h6_pq log8_h6_bp 43 _ 2 27 log8_h6_r12_14
    (log8Run_cut log8_h6_pq log8_h6_bp 43 _ 2 25 log8_h6_r14_16
    (log8Run_cut log8_h6_pq log8_h6_bp 43 _ 2 23 log8_h6_r16_18
    (log8Run_cut log8_h6_pq log8_h6_bp 43 _ 2 21 log8_h6_r18_20
    (log8Run_cut log8_h6_pq log8_h6_bp 43 _ 2 19 log8_h6_r20_22
    (log8Run_cut log8_h6_pq log8_h6_bp 43 _ 2 17 log8_h6_r22_24
    (log8Run_cut log8_h6_pq log8_h6_bp 43 _ 2 15 log8_h6_r24_26
    (log8Run_cut log8_h6_pq log8_h6_bp 43 _ 2 13 log8_h6_r26_28
    (log8Run_cut log8_h6_pq log8_h6_bp 43 _ 2 11 log8_h6_r28_30
    (log8Run_cut log8_h6_pq log8_h6_bp 43 _ 2 9 log8_h6_r30_32
    (log8Run_cut log8_h6_pq log8_h6_bp 43 _ 2 7 log8_h6_r32_34
    (log8Run_cut log8_h6_pq log8_h6_bp 43 _ 2 5 log8_h6_r34_36
    (log8Run_cut log8_h6_pq log8_h6_bp 43 _ 2 3 log8_h6_r36_38
    (log8Run_cut log8_h6_pq log8_h6_bp 43 _ 2 1 log8_h6_r38_40
    (log8_h6_r40_41))))))))))))))))))))

theorem log8_h6_hp : Log8Head true 0 43 log8_h6_pq log8_h6_bp (dySt log8_h6_tp) :=
  Log8Head.mk_ne (by decide) log8_h6_q log8_h6_r log8_h6_wt log8_h6_yt log8_h6_tpt

theorem log8_h6_hm : Log8Head false 0 43 log8_h6_pq log8_h6_bp (dySt log8_h6_tm) :=
  Log8Head.mk_ne (by decide) log8_h6_q log8_h6_r log8_h6_wt log8_h6_yt log8_h6_tmt

theorem log8_h7_q : ∀ q ∈ log8_h7_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h7_r : log8Run log8_h7_pq log8_h7_bp 43 0 41 (hornerInitL 8 exp8F exp8Phi 43) =
    dySt log8_h7_s41 :=
  log8Run_cut log8_h7_pq log8_h7_bp 43 _ 2 39 log8_h7_r0_2
    (log8Run_cut log8_h7_pq log8_h7_bp 43 _ 2 37 log8_h7_r2_4
    (log8Run_cut log8_h7_pq log8_h7_bp 43 _ 2 35 log8_h7_r4_6
    (log8Run_cut log8_h7_pq log8_h7_bp 43 _ 2 33 log8_h7_r6_8
    (log8Run_cut log8_h7_pq log8_h7_bp 43 _ 2 31 log8_h7_r8_10
    (log8Run_cut log8_h7_pq log8_h7_bp 43 _ 2 29 log8_h7_r10_12
    (log8Run_cut log8_h7_pq log8_h7_bp 43 _ 2 27 log8_h7_r12_14
    (log8Run_cut log8_h7_pq log8_h7_bp 43 _ 2 25 log8_h7_r14_16
    (log8Run_cut log8_h7_pq log8_h7_bp 43 _ 2 23 log8_h7_r16_18
    (log8Run_cut log8_h7_pq log8_h7_bp 43 _ 2 21 log8_h7_r18_20
    (log8Run_cut log8_h7_pq log8_h7_bp 43 _ 2 19 log8_h7_r20_22
    (log8Run_cut log8_h7_pq log8_h7_bp 43 _ 2 17 log8_h7_r22_24
    (log8Run_cut log8_h7_pq log8_h7_bp 43 _ 2 15 log8_h7_r24_26
    (log8Run_cut log8_h7_pq log8_h7_bp 43 _ 2 13 log8_h7_r26_28
    (log8Run_cut log8_h7_pq log8_h7_bp 43 _ 2 11 log8_h7_r28_30
    (log8Run_cut log8_h7_pq log8_h7_bp 43 _ 2 9 log8_h7_r30_32
    (log8Run_cut log8_h7_pq log8_h7_bp 43 _ 2 7 log8_h7_r32_34
    (log8Run_cut log8_h7_pq log8_h7_bp 43 _ 2 5 log8_h7_r34_36
    (log8Run_cut log8_h7_pq log8_h7_bp 43 _ 2 3 log8_h7_r36_38
    (log8Run_cut log8_h7_pq log8_h7_bp 43 _ 2 1 log8_h7_r38_40
    (log8_h7_r40_41))))))))))))))))))))

theorem log8_h7_hp : Log8Head true 0 43 log8_h7_pq log8_h7_bp (dySt log8_h7_tp) :=
  Log8Head.mk_ne (by decide) log8_h7_q log8_h7_r log8_h7_wt log8_h7_yt log8_h7_tpt

theorem log8_h7_hm : Log8Head false 0 43 log8_h7_pq log8_h7_bp (dySt log8_h7_tm) :=
  Log8Head.mk_ne (by decide) log8_h7_q log8_h7_r log8_h7_wt log8_h7_yt log8_h7_tmt

theorem log8_g5zp0e0_ev :
    Log8Eval true true 0 43 log8_g5zp0e0_v.1 log8_g5zp0e0_v.2.2.2 false log8_g5zp0e0_v.2.1 log8_g5zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g5zp0e0_leaf log8_h7_hp rfl log8_g5zp0e0_a log8_g5zp0e0_b log8_g5zp0e0_end

theorem log8_g5zp0e1_ev :
    Log8Eval true true 0 43 log8_g5zp0e1_v.1 log8_g5zp0e1_v.2.2.2 false log8_g5zp0e1_v.2.1 log8_g5zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g5zp0e1_leaf log8_h6_hp rfl log8_g5zp0e1_a log8_g5zp0e1_b log8_g5zp0e1_end

theorem log8_g5np0e0_ev :
    Log8Eval false true 0 43 log8_g5np0e0_v.1 log8_g5np0e0_v.2.2.2 false log8_g5np0e0_v.2.1 log8_g5np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g5np0e0_leaf log8_h5_hp rfl log8_g5np0e0_a log8_g5np0e0_b log8_g5np0e0_end

theorem log8_g5np0e1_ev :
    Log8Eval false true 0 43 log8_g5np0e1_v.1 log8_g5np0e1_v.2.2.2 false log8_g5np0e1_v.2.1 log8_g5np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g5np0e1_leaf log8_h5_hp rfl log8_g5np0e1_a log8_g5np0e1_b log8_g5np0e1_end

theorem log8_g5zm0e0_ev :
    Log8Eval true false 0 43 log8_g5zm0e0_v.1 log8_g5zm0e0_v.2.2.2 false log8_g5zm0e0_v.2.1 log8_g5zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g5zm0e0_leaf log8_h7_hm rfl log8_g5zm0e0_a log8_g5zm0e0_b log8_g5zm0e0_end

theorem log8_g5zm0e1_ev :
    Log8Eval true false 0 43 log8_g5zm0e1_v.1 log8_g5zm0e1_v.2.2.2 false log8_g5zm0e1_v.2.1 log8_g5zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g5zm0e1_leaf log8_h6_hm rfl log8_g5zm0e1_a log8_g5zm0e1_b log8_g5zm0e1_end

theorem log8_g5nm0e0_ev :
    Log8Eval false false 0 43 log8_g5nm0e0_v.1 log8_g5nm0e0_v.2.2.2 false log8_g5nm0e0_v.2.1 log8_g5nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g5nm0e0_leaf log8_h5_hm rfl log8_g5nm0e0_a log8_g5nm0e0_b log8_g5nm0e0_end

theorem log8_g5nm0e1_ev :
    Log8Eval false false 0 43 log8_g5nm0e1_v.1 log8_g5nm0e1_v.2.2.2 false log8_g5nm0e1_v.2.1 log8_g5nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g5nm0e1_leaf log8_h5_hm rfl log8_g5nm0e1_a log8_g5nm0e1_b log8_g5nm0e1_end

theorem log8_h20_q : ∀ q ∈ log8_h20_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h20_r : log8Run log8_h20_pq log8_h20_bp 19 0 17 (hornerInitL 8 exp8F exp8Phi 19) =
    dySt log8_h20_s17 :=
  log8Run_cut log8_h20_pq log8_h20_bp 19 _ 2 15 log8_h20_r0_2
    (log8Run_cut log8_h20_pq log8_h20_bp 19 _ 2 13 log8_h20_r2_4
    (log8Run_cut log8_h20_pq log8_h20_bp 19 _ 2 11 log8_h20_r4_6
    (log8Run_cut log8_h20_pq log8_h20_bp 19 _ 2 9 log8_h20_r6_8
    (log8Run_cut log8_h20_pq log8_h20_bp 19 _ 2 7 log8_h20_r8_10
    (log8Run_cut log8_h20_pq log8_h20_bp 19 _ 2 5 log8_h20_r10_12
    (log8Run_cut log8_h20_pq log8_h20_bp 19 _ 2 3 log8_h20_r12_14
    (log8Run_cut log8_h20_pq log8_h20_bp 19 _ 2 1 log8_h20_r14_16
    (log8_h20_r16_17))))))))

theorem log8_h20_hp : Log8Head true 0 19 log8_h20_pq log8_h20_bp (dySt log8_h20_tp) :=
  Log8Head.mk_ne (by decide) log8_h20_q log8_h20_r log8_h20_wt log8_h20_yt log8_h20_tpt

theorem log8_h20_hm : Log8Head false 0 19 log8_h20_pq log8_h20_bp (dySt log8_h20_tm) :=
  Log8Head.mk_ne (by decide) log8_h20_q log8_h20_r log8_h20_wt log8_h20_yt log8_h20_tmt

theorem log8_g18zp0e0_ev :
    Log8Eval true true 0 19 log8_g18zp0e0_v.1 log8_g18zp0e0_v.2.2.2 false log8_g18zp0e0_v.2.1 log8_g18zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g18zp0e0_leaf log8_h20_hp rfl log8_g18zp0e0_a log8_g18zp0e0_b log8_g18zp0e0_end

theorem log8_g18zp0e1_ev :
    Log8Eval true true 0 19 log8_g18zp0e1_v.1 log8_g18zp0e1_v.2.2.2 false log8_g18zp0e1_v.2.1 log8_g18zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g18zp0e1_leaf log8_h20_hp rfl log8_g18zp0e1_a log8_g18zp0e1_b log8_g18zp0e1_end

theorem log8_g18np0e0_ev :
    Log8Eval false true 0 19 log8_g18np0e0_v.1 log8_g18np0e0_v.2.2.2 false log8_g18np0e0_v.2.1 log8_g18np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g18np0e0_leaf log8_h20_hp rfl log8_g18np0e0_a log8_g18np0e0_b log8_g18np0e0_end

theorem log8_g18np0e1_ev :
    Log8Eval false true 0 19 log8_g18np0e1_v.1 log8_g18np0e1_v.2.2.2 false log8_g18np0e1_v.2.1 log8_g18np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g18np0e1_leaf log8_h20_hp rfl log8_g18np0e1_a log8_g18np0e1_b log8_g18np0e1_end

theorem log8_g18zm0e0_ev :
    Log8Eval true false 0 19 log8_g18zm0e0_v.1 log8_g18zm0e0_v.2.2.2 false log8_g18zm0e0_v.2.1 log8_g18zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g18zm0e0_leaf log8_h20_hm rfl log8_g18zm0e0_a log8_g18zm0e0_b log8_g18zm0e0_end

theorem log8_g18zm0e1_ev :
    Log8Eval true false 0 19 log8_g18zm0e1_v.1 log8_g18zm0e1_v.2.2.2 false log8_g18zm0e1_v.2.1 log8_g18zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g18zm0e1_leaf log8_h20_hm rfl log8_g18zm0e1_a log8_g18zm0e1_b log8_g18zm0e1_end

theorem log8_g18nm0e0_ev :
    Log8Eval false false 0 19 log8_g18nm0e0_v.1 log8_g18nm0e0_v.2.2.2 false log8_g18nm0e0_v.2.1 log8_g18nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g18nm0e0_leaf log8_h20_hm rfl log8_g18nm0e0_a log8_g18nm0e0_b log8_g18nm0e0_end

theorem log8_g18nm0e1_ev :
    Log8Eval false false 0 19 log8_g18nm0e1_v.1 log8_g18nm0e1_v.2.2.2 false log8_g18nm0e1_v.2.1 log8_g18nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g18nm0e1_leaf log8_h20_hm rfl log8_g18nm0e1_a log8_g18nm0e1_b log8_g18nm0e1_end

theorem log8_h25_q : ∀ q ∈ log8_h25_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h25_r : log8Run log8_h25_pq log8_h25_bp 14 0 12 (hornerInitL 8 exp8F exp8Phi 14) =
    dySt log8_h25_s12 :=
  log8Run_cut log8_h25_pq log8_h25_bp 14 _ 2 10 log8_h25_r0_2
    (log8Run_cut log8_h25_pq log8_h25_bp 14 _ 2 8 log8_h25_r2_4
    (log8Run_cut log8_h25_pq log8_h25_bp 14 _ 2 6 log8_h25_r4_6
    (log8Run_cut log8_h25_pq log8_h25_bp 14 _ 2 4 log8_h25_r6_8
    (log8Run_cut log8_h25_pq log8_h25_bp 14 _ 2 2 log8_h25_r8_10
    (log8_h25_r10_12)))))

theorem log8_h25_hp : Log8Head true 0 14 log8_h25_pq log8_h25_bp (dySt log8_h25_tp) :=
  Log8Head.mk_ne (by decide) log8_h25_q log8_h25_r log8_h25_wt log8_h25_yt log8_h25_tpt

theorem log8_h25_hm : Log8Head false 0 14 log8_h25_pq log8_h25_bp (dySt log8_h25_tm) :=
  Log8Head.mk_ne (by decide) log8_h25_q log8_h25_r log8_h25_wt log8_h25_yt log8_h25_tmt

theorem log8_g23zp0e0_ev :
    Log8Eval true true 0 14 log8_g23zp0e0_v.1 log8_g23zp0e0_v.2.2.2 false log8_g23zp0e0_v.2.1 log8_g23zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g23zp0e0_leaf log8_h25_hp rfl log8_g23zp0e0_a log8_g23zp0e0_b log8_g23zp0e0_end

theorem log8_g23zp0e1_ev :
    Log8Eval true true 0 14 log8_g23zp0e1_v.1 log8_g23zp0e1_v.2.2.2 false log8_g23zp0e1_v.2.1 log8_g23zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g23zp0e1_leaf log8_h25_hp rfl log8_g23zp0e1_a log8_g23zp0e1_b log8_g23zp0e1_end

theorem log8_g23np0e0_ev :
    Log8Eval false true 0 14 log8_g23np0e0_v.1 log8_g23np0e0_v.2.2.2 false log8_g23np0e0_v.2.1 log8_g23np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g23np0e0_leaf log8_h25_hp rfl log8_g23np0e0_a log8_g23np0e0_b log8_g23np0e0_end

theorem log8_g23np0e1_ev :
    Log8Eval false true 0 14 log8_g23np0e1_v.1 log8_g23np0e1_v.2.2.2 false log8_g23np0e1_v.2.1 log8_g23np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g23np0e1_leaf log8_h25_hp rfl log8_g23np0e1_a log8_g23np0e1_b log8_g23np0e1_end

theorem log8_g23zm0e0_ev :
    Log8Eval true false 0 14 log8_g23zm0e0_v.1 log8_g23zm0e0_v.2.2.2 false log8_g23zm0e0_v.2.1 log8_g23zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g23zm0e0_leaf log8_h25_hm rfl log8_g23zm0e0_a log8_g23zm0e0_b log8_g23zm0e0_end

theorem log8_g23zm0e1_ev :
    Log8Eval true false 0 14 log8_g23zm0e1_v.1 log8_g23zm0e1_v.2.2.2 false log8_g23zm0e1_v.2.1 log8_g23zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g23zm0e1_leaf log8_h25_hm rfl log8_g23zm0e1_a log8_g23zm0e1_b log8_g23zm0e1_end

theorem log8_g23nm0e0_ev :
    Log8Eval false false 0 14 log8_g23nm0e0_v.1 log8_g23nm0e0_v.2.2.2 false log8_g23nm0e0_v.2.1 log8_g23nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g23nm0e0_leaf log8_h25_hm rfl log8_g23nm0e0_a log8_g23nm0e0_b log8_g23nm0e0_end

theorem log8_g23nm0e1_ev :
    Log8Eval false false 0 14 log8_g23nm0e1_v.1 log8_g23nm0e1_v.2.2.2 false log8_g23nm0e1_v.2.1 log8_g23nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g23nm0e1_leaf log8_h25_hm rfl log8_g23nm0e1_a log8_g23nm0e1_b log8_g23nm0e1_end

theorem log8_h1_q : ∀ q ∈ log8_h1_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h1_r : log8Run log8_h1_pq log8_h1_bp 43 0 41 (hornerInitL 8 exp8F exp8Phi 43) =
    dySt log8_h1_s41 :=
  log8Run_cut log8_h1_pq log8_h1_bp 43 _ 2 39 log8_h1_r0_2
    (log8Run_cut log8_h1_pq log8_h1_bp 43 _ 2 37 log8_h1_r2_4
    (log8Run_cut log8_h1_pq log8_h1_bp 43 _ 2 35 log8_h1_r4_6
    (log8Run_cut log8_h1_pq log8_h1_bp 43 _ 2 33 log8_h1_r6_8
    (log8Run_cut log8_h1_pq log8_h1_bp 43 _ 2 31 log8_h1_r8_10
    (log8Run_cut log8_h1_pq log8_h1_bp 43 _ 2 29 log8_h1_r10_12
    (log8Run_cut log8_h1_pq log8_h1_bp 43 _ 2 27 log8_h1_r12_14
    (log8Run_cut log8_h1_pq log8_h1_bp 43 _ 2 25 log8_h1_r14_16
    (log8Run_cut log8_h1_pq log8_h1_bp 43 _ 2 23 log8_h1_r16_18
    (log8Run_cut log8_h1_pq log8_h1_bp 43 _ 2 21 log8_h1_r18_20
    (log8Run_cut log8_h1_pq log8_h1_bp 43 _ 2 19 log8_h1_r20_22
    (log8Run_cut log8_h1_pq log8_h1_bp 43 _ 2 17 log8_h1_r22_24
    (log8Run_cut log8_h1_pq log8_h1_bp 43 _ 2 15 log8_h1_r24_26
    (log8Run_cut log8_h1_pq log8_h1_bp 43 _ 2 13 log8_h1_r26_28
    (log8Run_cut log8_h1_pq log8_h1_bp 43 _ 2 11 log8_h1_r28_30
    (log8Run_cut log8_h1_pq log8_h1_bp 43 _ 2 9 log8_h1_r30_32
    (log8Run_cut log8_h1_pq log8_h1_bp 43 _ 2 7 log8_h1_r32_34
    (log8Run_cut log8_h1_pq log8_h1_bp 43 _ 2 5 log8_h1_r34_36
    (log8Run_cut log8_h1_pq log8_h1_bp 43 _ 2 3 log8_h1_r36_38
    (log8Run_cut log8_h1_pq log8_h1_bp 43 _ 2 1 log8_h1_r38_40
    (log8_h1_r40_41))))))))))))))))))))

theorem log8_h1_hp : Log8Head true 4 43 log8_h1_pq log8_h1_bp (dySt log8_h1_tp) :=
  Log8Head.mk_ne (by decide) log8_h1_q log8_h1_r log8_h1_wt log8_h1_yt log8_h1_tpt

theorem log8_h1_hm : Log8Head false 4 43 log8_h1_pq log8_h1_bp (dySt log8_h1_tm) :=
  Log8Head.mk_ne (by decide) log8_h1_q log8_h1_r log8_h1_wt log8_h1_yt log8_h1_tmt

theorem log8_g1zp0e0_sq :
    log8SqRun true 4 log8_g1zp0e0_v.1 log8_g1zp0e0_v.2.1 4 (dySt log8_h1_tp) =
      dySt log8_g1zp0e0_s4 := by
  show log8Sq true 4 log8_g1zp0e0_v.1 log8_g1zp0e0_v.2.1 3
      (log8Sq true 4 log8_g1zp0e0_v.1 log8_g1zp0e0_v.2.1 2
      (log8Sq true 4 log8_g1zp0e0_v.1 log8_g1zp0e0_v.2.1 1
      (log8Sq true 4 log8_g1zp0e0_v.1 log8_g1zp0e0_v.2.1 0
      (dySt log8_h1_tp)))) = _
  rw [log8_g1zp0e0_q0_2, log8_g1zp0e0_q2_4]

theorem log8_g1zp0e0_ev :
    Log8Eval true true 4 43 log8_g1zp0e0_v.1 log8_g1zp0e0_v.2.2.2 false log8_g1zp0e0_v.2.1 log8_g1zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g1zp0e0_leaf log8_h1_hp log8_g1zp0e0_sq log8_g1zp0e0_a log8_g1zp0e0_b log8_g1zp0e0_end

theorem log8_g1zp0e1_sq :
    log8SqRun true 4 log8_g1zp0e1_v.1 log8_g1zp0e1_v.2.1 4 (dySt log8_h1_tp) =
      dySt log8_g1zp0e1_s4 := by
  show log8Sq true 4 log8_g1zp0e1_v.1 log8_g1zp0e1_v.2.1 3
      (log8Sq true 4 log8_g1zp0e1_v.1 log8_g1zp0e1_v.2.1 2
      (log8Sq true 4 log8_g1zp0e1_v.1 log8_g1zp0e1_v.2.1 1
      (log8Sq true 4 log8_g1zp0e1_v.1 log8_g1zp0e1_v.2.1 0
      (dySt log8_h1_tp)))) = _
  rw [log8_g1zp0e1_q0_2, log8_g1zp0e1_q2_4]

theorem log8_g1zp0e1_ev :
    Log8Eval true true 4 43 log8_g1zp0e1_v.1 log8_g1zp0e1_v.2.2.2 false log8_g1zp0e1_v.2.1 log8_g1zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g1zp0e1_leaf log8_h1_hp log8_g1zp0e1_sq log8_g1zp0e1_a log8_g1zp0e1_b log8_g1zp0e1_end

theorem log8_g1np0e0_sq :
    log8SqRun true 4 log8_g1np0e0_v.1 log8_g1np0e0_v.2.1 4 (dySt log8_h1_tp) =
      dySt log8_g1np0e0_s4 := by
  show log8Sq true 4 log8_g1np0e0_v.1 log8_g1np0e0_v.2.1 3
      (log8Sq true 4 log8_g1np0e0_v.1 log8_g1np0e0_v.2.1 2
      (log8Sq true 4 log8_g1np0e0_v.1 log8_g1np0e0_v.2.1 1
      (log8Sq true 4 log8_g1np0e0_v.1 log8_g1np0e0_v.2.1 0
      (dySt log8_h1_tp)))) = _
  rw [log8_g1np0e0_q0_2, log8_g1np0e0_q2_4]

theorem log8_g1np0e0_ev :
    Log8Eval false true 4 43 log8_g1np0e0_v.1 log8_g1np0e0_v.2.2.2 false log8_g1np0e0_v.2.1 log8_g1np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g1np0e0_leaf log8_h1_hp log8_g1np0e0_sq log8_g1np0e0_a log8_g1np0e0_b log8_g1np0e0_end

theorem log8_g1np0e1_sq :
    log8SqRun true 4 log8_g1np0e1_v.1 log8_g1np0e1_v.2.1 4 (dySt log8_h1_tp) =
      dySt log8_g1np0e1_s4 := by
  show log8Sq true 4 log8_g1np0e1_v.1 log8_g1np0e1_v.2.1 3
      (log8Sq true 4 log8_g1np0e1_v.1 log8_g1np0e1_v.2.1 2
      (log8Sq true 4 log8_g1np0e1_v.1 log8_g1np0e1_v.2.1 1
      (log8Sq true 4 log8_g1np0e1_v.1 log8_g1np0e1_v.2.1 0
      (dySt log8_h1_tp)))) = _
  rw [log8_g1np0e1_q0_2, log8_g1np0e1_q2_4]

theorem log8_g1np0e1_ev :
    Log8Eval false true 4 43 log8_g1np0e1_v.1 log8_g1np0e1_v.2.2.2 false log8_g1np0e1_v.2.1 log8_g1np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g1np0e1_leaf log8_h1_hp log8_g1np0e1_sq log8_g1np0e1_a log8_g1np0e1_b log8_g1np0e1_end

theorem log8_g1zm0e0_sq :
    log8SqRun false 4 log8_g1zm0e0_v.1 log8_g1zm0e0_v.2.1 4 (dySt log8_h1_tm) =
      dySt log8_g1zm0e0_s4 := by
  show log8Sq false 4 log8_g1zm0e0_v.1 log8_g1zm0e0_v.2.1 3
      (log8Sq false 4 log8_g1zm0e0_v.1 log8_g1zm0e0_v.2.1 2
      (log8Sq false 4 log8_g1zm0e0_v.1 log8_g1zm0e0_v.2.1 1
      (log8Sq false 4 log8_g1zm0e0_v.1 log8_g1zm0e0_v.2.1 0
      (dySt log8_h1_tm)))) = _
  rw [log8_g1zm0e0_q0_2, log8_g1zm0e0_q2_4]

theorem log8_g1zm0e0_ev :
    Log8Eval true false 4 43 log8_g1zm0e0_v.1 log8_g1zm0e0_v.2.2.2 false log8_g1zm0e0_v.2.1 log8_g1zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g1zm0e0_leaf log8_h1_hm log8_g1zm0e0_sq log8_g1zm0e0_a log8_g1zm0e0_b log8_g1zm0e0_end

theorem log8_g1zm0e1_sq :
    log8SqRun false 4 log8_g1zm0e1_v.1 log8_g1zm0e1_v.2.1 4 (dySt log8_h1_tm) =
      dySt log8_g1zm0e1_s4 := by
  show log8Sq false 4 log8_g1zm0e1_v.1 log8_g1zm0e1_v.2.1 3
      (log8Sq false 4 log8_g1zm0e1_v.1 log8_g1zm0e1_v.2.1 2
      (log8Sq false 4 log8_g1zm0e1_v.1 log8_g1zm0e1_v.2.1 1
      (log8Sq false 4 log8_g1zm0e1_v.1 log8_g1zm0e1_v.2.1 0
      (dySt log8_h1_tm)))) = _
  rw [log8_g1zm0e1_q0_2, log8_g1zm0e1_q2_4]

theorem log8_g1zm0e1_ev :
    Log8Eval true false 4 43 log8_g1zm0e1_v.1 log8_g1zm0e1_v.2.2.2 false log8_g1zm0e1_v.2.1 log8_g1zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g1zm0e1_leaf log8_h1_hm log8_g1zm0e1_sq log8_g1zm0e1_a log8_g1zm0e1_b log8_g1zm0e1_end

theorem log8_g1nm0e0_sq :
    log8SqRun false 4 log8_g1nm0e0_v.1 log8_g1nm0e0_v.2.1 4 (dySt log8_h1_tm) =
      dySt log8_g1nm0e0_s4 := by
  show log8Sq false 4 log8_g1nm0e0_v.1 log8_g1nm0e0_v.2.1 3
      (log8Sq false 4 log8_g1nm0e0_v.1 log8_g1nm0e0_v.2.1 2
      (log8Sq false 4 log8_g1nm0e0_v.1 log8_g1nm0e0_v.2.1 1
      (log8Sq false 4 log8_g1nm0e0_v.1 log8_g1nm0e0_v.2.1 0
      (dySt log8_h1_tm)))) = _
  rw [log8_g1nm0e0_q0_2, log8_g1nm0e0_q2_4]

theorem log8_g1nm0e0_ev :
    Log8Eval false false 4 43 log8_g1nm0e0_v.1 log8_g1nm0e0_v.2.2.2 false log8_g1nm0e0_v.2.1 log8_g1nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g1nm0e0_leaf log8_h1_hm log8_g1nm0e0_sq log8_g1nm0e0_a log8_g1nm0e0_b log8_g1nm0e0_end

theorem log8_g1nm0e1_sq :
    log8SqRun false 4 log8_g1nm0e1_v.1 log8_g1nm0e1_v.2.1 4 (dySt log8_h1_tm) =
      dySt log8_g1nm0e1_s4 := by
  show log8Sq false 4 log8_g1nm0e1_v.1 log8_g1nm0e1_v.2.1 3
      (log8Sq false 4 log8_g1nm0e1_v.1 log8_g1nm0e1_v.2.1 2
      (log8Sq false 4 log8_g1nm0e1_v.1 log8_g1nm0e1_v.2.1 1
      (log8Sq false 4 log8_g1nm0e1_v.1 log8_g1nm0e1_v.2.1 0
      (dySt log8_h1_tm)))) = _
  rw [log8_g1nm0e1_q0_2, log8_g1nm0e1_q2_4]

theorem log8_g1nm0e1_ev :
    Log8Eval false false 4 43 log8_g1nm0e1_v.1 log8_g1nm0e1_v.2.2.2 false log8_g1nm0e1_v.2.1 log8_g1nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g1nm0e1_leaf log8_h1_hm log8_g1nm0e1_sq log8_g1nm0e1_a log8_g1nm0e1_b log8_g1nm0e1_end

theorem log8_h14_q : ∀ q ∈ log8_h14_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h14_r : log8Run log8_h14_pq log8_h14_bp 26 0 24 (hornerInitL 8 exp8F exp8Phi 26) =
    dySt log8_h14_s24 :=
  log8Run_cut log8_h14_pq log8_h14_bp 26 _ 2 22 log8_h14_r0_2
    (log8Run_cut log8_h14_pq log8_h14_bp 26 _ 2 20 log8_h14_r2_4
    (log8Run_cut log8_h14_pq log8_h14_bp 26 _ 2 18 log8_h14_r4_6
    (log8Run_cut log8_h14_pq log8_h14_bp 26 _ 2 16 log8_h14_r6_8
    (log8Run_cut log8_h14_pq log8_h14_bp 26 _ 2 14 log8_h14_r8_10
    (log8Run_cut log8_h14_pq log8_h14_bp 26 _ 2 12 log8_h14_r10_12
    (log8Run_cut log8_h14_pq log8_h14_bp 26 _ 2 10 log8_h14_r12_14
    (log8Run_cut log8_h14_pq log8_h14_bp 26 _ 2 8 log8_h14_r14_16
    (log8Run_cut log8_h14_pq log8_h14_bp 26 _ 2 6 log8_h14_r16_18
    (log8Run_cut log8_h14_pq log8_h14_bp 26 _ 2 4 log8_h14_r18_20
    (log8Run_cut log8_h14_pq log8_h14_bp 26 _ 2 2 log8_h14_r20_22
    (log8_h14_r22_24)))))))))))

theorem log8_h14_hp : Log8Head true 0 26 log8_h14_pq log8_h14_bp (dySt log8_h14_tp) :=
  Log8Head.mk_ne (by decide) log8_h14_q log8_h14_r log8_h14_wt log8_h14_yt log8_h14_tpt

theorem log8_h14_hm : Log8Head false 0 26 log8_h14_pq log8_h14_bp (dySt log8_h14_tm) :=
  Log8Head.mk_ne (by decide) log8_h14_q log8_h14_r log8_h14_wt log8_h14_yt log8_h14_tmt

theorem log8_g12zp0e0_ev :
    Log8Eval true true 0 26 log8_g12zp0e0_v.1 log8_g12zp0e0_v.2.2.2 false log8_g12zp0e0_v.2.1 log8_g12zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g12zp0e0_leaf log8_h14_hp rfl log8_g12zp0e0_a log8_g12zp0e0_b log8_g12zp0e0_end

theorem log8_g12zp0e1_ev :
    Log8Eval true true 0 26 log8_g12zp0e1_v.1 log8_g12zp0e1_v.2.2.2 false log8_g12zp0e1_v.2.1 log8_g12zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g12zp0e1_leaf log8_h14_hp rfl log8_g12zp0e1_a log8_g12zp0e1_b log8_g12zp0e1_end

theorem log8_g12np0e0_ev :
    Log8Eval false true 0 26 log8_g12np0e0_v.1 log8_g12np0e0_v.2.2.2 false log8_g12np0e0_v.2.1 log8_g12np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g12np0e0_leaf log8_h14_hp rfl log8_g12np0e0_a log8_g12np0e0_b log8_g12np0e0_end

theorem log8_g12np0e1_ev :
    Log8Eval false true 0 26 log8_g12np0e1_v.1 log8_g12np0e1_v.2.2.2 false log8_g12np0e1_v.2.1 log8_g12np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g12np0e1_leaf log8_h14_hp rfl log8_g12np0e1_a log8_g12np0e1_b log8_g12np0e1_end

theorem log8_g12zm0e0_ev :
    Log8Eval true false 0 26 log8_g12zm0e0_v.1 log8_g12zm0e0_v.2.2.2 false log8_g12zm0e0_v.2.1 log8_g12zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g12zm0e0_leaf log8_h14_hm rfl log8_g12zm0e0_a log8_g12zm0e0_b log8_g12zm0e0_end

theorem log8_g12zm0e1_ev :
    Log8Eval true false 0 26 log8_g12zm0e1_v.1 log8_g12zm0e1_v.2.2.2 false log8_g12zm0e1_v.2.1 log8_g12zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g12zm0e1_leaf log8_h14_hm rfl log8_g12zm0e1_a log8_g12zm0e1_b log8_g12zm0e1_end

theorem log8_g12nm0e0_ev :
    Log8Eval false false 0 26 log8_g12nm0e0_v.1 log8_g12nm0e0_v.2.2.2 false log8_g12nm0e0_v.2.1 log8_g12nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g12nm0e0_leaf log8_h14_hm rfl log8_g12nm0e0_a log8_g12nm0e0_b log8_g12nm0e0_end

theorem log8_g12nm0e1_ev :
    Log8Eval false false 0 26 log8_g12nm0e1_v.1 log8_g12nm0e1_v.2.2.2 false log8_g12nm0e1_v.2.1 log8_g12nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g12nm0e1_leaf log8_h14_hm rfl log8_g12nm0e1_a log8_g12nm0e1_b log8_g12nm0e1_end

theorem log8_h19_q : ∀ q ∈ log8_h19_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h19_r : log8Run log8_h19_pq log8_h19_bp 20 0 18 (hornerInitL 8 exp8F exp8Phi 20) =
    dySt log8_h19_s18 :=
  log8Run_cut log8_h19_pq log8_h19_bp 20 _ 2 16 log8_h19_r0_2
    (log8Run_cut log8_h19_pq log8_h19_bp 20 _ 2 14 log8_h19_r2_4
    (log8Run_cut log8_h19_pq log8_h19_bp 20 _ 2 12 log8_h19_r4_6
    (log8Run_cut log8_h19_pq log8_h19_bp 20 _ 2 10 log8_h19_r6_8
    (log8Run_cut log8_h19_pq log8_h19_bp 20 _ 2 8 log8_h19_r8_10
    (log8Run_cut log8_h19_pq log8_h19_bp 20 _ 2 6 log8_h19_r10_12
    (log8Run_cut log8_h19_pq log8_h19_bp 20 _ 2 4 log8_h19_r12_14
    (log8Run_cut log8_h19_pq log8_h19_bp 20 _ 2 2 log8_h19_r14_16
    (log8_h19_r16_18))))))))

theorem log8_h19_hp : Log8Head true 0 20 log8_h19_pq log8_h19_bp (dySt log8_h19_tp) :=
  Log8Head.mk_ne (by decide) log8_h19_q log8_h19_r log8_h19_wt log8_h19_yt log8_h19_tpt

theorem log8_h19_hm : Log8Head false 0 20 log8_h19_pq log8_h19_bp (dySt log8_h19_tm) :=
  Log8Head.mk_ne (by decide) log8_h19_q log8_h19_r log8_h19_wt log8_h19_yt log8_h19_tmt

theorem log8_g17zp0e0_ev :
    Log8Eval true true 0 20 log8_g17zp0e0_v.1 log8_g17zp0e0_v.2.2.2 false log8_g17zp0e0_v.2.1 log8_g17zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g17zp0e0_leaf log8_h19_hp rfl log8_g17zp0e0_a log8_g17zp0e0_b log8_g17zp0e0_end

theorem log8_g17zp0e1_ev :
    Log8Eval true true 0 20 log8_g17zp0e1_v.1 log8_g17zp0e1_v.2.2.2 false log8_g17zp0e1_v.2.1 log8_g17zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g17zp0e1_leaf log8_h19_hp rfl log8_g17zp0e1_a log8_g17zp0e1_b log8_g17zp0e1_end

theorem log8_g17np0e0_ev :
    Log8Eval false true 0 20 log8_g17np0e0_v.1 log8_g17np0e0_v.2.2.2 false log8_g17np0e0_v.2.1 log8_g17np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g17np0e0_leaf log8_h19_hp rfl log8_g17np0e0_a log8_g17np0e0_b log8_g17np0e0_end

theorem log8_g17np0e1_ev :
    Log8Eval false true 0 20 log8_g17np0e1_v.1 log8_g17np0e1_v.2.2.2 false log8_g17np0e1_v.2.1 log8_g17np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g17np0e1_leaf log8_h19_hp rfl log8_g17np0e1_a log8_g17np0e1_b log8_g17np0e1_end

theorem log8_g17zm0e0_ev :
    Log8Eval true false 0 20 log8_g17zm0e0_v.1 log8_g17zm0e0_v.2.2.2 false log8_g17zm0e0_v.2.1 log8_g17zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g17zm0e0_leaf log8_h19_hm rfl log8_g17zm0e0_a log8_g17zm0e0_b log8_g17zm0e0_end

theorem log8_g17zm0e1_ev :
    Log8Eval true false 0 20 log8_g17zm0e1_v.1 log8_g17zm0e1_v.2.2.2 false log8_g17zm0e1_v.2.1 log8_g17zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g17zm0e1_leaf log8_h19_hm rfl log8_g17zm0e1_a log8_g17zm0e1_b log8_g17zm0e1_end

theorem log8_g17nm0e0_ev :
    Log8Eval false false 0 20 log8_g17nm0e0_v.1 log8_g17nm0e0_v.2.2.2 false log8_g17nm0e0_v.2.1 log8_g17nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g17nm0e0_leaf log8_h19_hm rfl log8_g17nm0e0_a log8_g17nm0e0_b log8_g17nm0e0_end

theorem log8_g17nm0e1_ev :
    Log8Eval false false 0 20 log8_g17nm0e1_v.1 log8_g17nm0e1_v.2.2.2 false log8_g17nm0e1_v.2.1 log8_g17nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g17nm0e1_leaf log8_h19_hm rfl log8_g17nm0e1_a log8_g17nm0e1_b log8_g17nm0e1_end

theorem log8_h26_q : ∀ q ∈ log8_h26_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h26_r : log8Run log8_h26_pq log8_h26_bp 13 0 11 (hornerInitL 8 exp8F exp8Phi 13) =
    dySt log8_h26_s11 :=
  log8Run_cut log8_h26_pq log8_h26_bp 13 _ 2 9 log8_h26_r0_2
    (log8Run_cut log8_h26_pq log8_h26_bp 13 _ 2 7 log8_h26_r2_4
    (log8Run_cut log8_h26_pq log8_h26_bp 13 _ 2 5 log8_h26_r4_6
    (log8Run_cut log8_h26_pq log8_h26_bp 13 _ 2 3 log8_h26_r6_8
    (log8Run_cut log8_h26_pq log8_h26_bp 13 _ 2 1 log8_h26_r8_10
    (log8_h26_r10_11)))))

theorem log8_h26_hp : Log8Head true 0 13 log8_h26_pq log8_h26_bp (dySt log8_h26_tp) :=
  Log8Head.mk_ne (by decide) log8_h26_q log8_h26_r log8_h26_wt log8_h26_yt log8_h26_tpt

theorem log8_h26_hm : Log8Head false 0 13 log8_h26_pq log8_h26_bp (dySt log8_h26_tm) :=
  Log8Head.mk_ne (by decide) log8_h26_q log8_h26_r log8_h26_wt log8_h26_yt log8_h26_tmt

theorem log8_g24zp0e0_ev :
    Log8Eval true true 0 13 log8_g24zp0e0_v.1 log8_g24zp0e0_v.2.2.2 false log8_g24zp0e0_v.2.1 log8_g24zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g24zp0e0_leaf log8_h26_hp rfl log8_g24zp0e0_a log8_g24zp0e0_b log8_g24zp0e0_end

theorem log8_g24zp0e1_ev :
    Log8Eval true true 0 13 log8_g24zp0e1_v.1 log8_g24zp0e1_v.2.2.2 false log8_g24zp0e1_v.2.1 log8_g24zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g24zp0e1_leaf log8_h26_hp rfl log8_g24zp0e1_a log8_g24zp0e1_b log8_g24zp0e1_end

theorem log8_g24np0e0_ev :
    Log8Eval false true 0 13 log8_g24np0e0_v.1 log8_g24np0e0_v.2.2.2 false log8_g24np0e0_v.2.1 log8_g24np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g24np0e0_leaf log8_h26_hp rfl log8_g24np0e0_a log8_g24np0e0_b log8_g24np0e0_end

theorem log8_g24np0e1_ev :
    Log8Eval false true 0 13 log8_g24np0e1_v.1 log8_g24np0e1_v.2.2.2 false log8_g24np0e1_v.2.1 log8_g24np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g24np0e1_leaf log8_h26_hp rfl log8_g24np0e1_a log8_g24np0e1_b log8_g24np0e1_end

theorem log8_g24zm0e0_ev :
    Log8Eval true false 0 13 log8_g24zm0e0_v.1 log8_g24zm0e0_v.2.2.2 false log8_g24zm0e0_v.2.1 log8_g24zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g24zm0e0_leaf log8_h26_hm rfl log8_g24zm0e0_a log8_g24zm0e0_b log8_g24zm0e0_end

theorem log8_g24zm0e1_ev :
    Log8Eval true false 0 13 log8_g24zm0e1_v.1 log8_g24zm0e1_v.2.2.2 false log8_g24zm0e1_v.2.1 log8_g24zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g24zm0e1_leaf log8_h26_hm rfl log8_g24zm0e1_a log8_g24zm0e1_b log8_g24zm0e1_end

theorem log8_g24nm0e0_ev :
    Log8Eval false false 0 13 log8_g24nm0e0_v.1 log8_g24nm0e0_v.2.2.2 false log8_g24nm0e0_v.2.1 log8_g24nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g24nm0e0_leaf log8_h26_hm rfl log8_g24nm0e0_a log8_g24nm0e0_b log8_g24nm0e0_end

theorem log8_g24nm0e1_ev :
    Log8Eval false false 0 13 log8_g24nm0e1_v.1 log8_g24nm0e1_v.2.2.2 false log8_g24nm0e1_v.2.1 log8_g24nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g24nm0e1_leaf log8_h26_hm rfl log8_g24nm0e1_a log8_g24nm0e1_b log8_g24nm0e1_end

theorem log8_h2_q : ∀ q ∈ log8_h2_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h2_r : log8Run log8_h2_pq log8_h2_bp 43 0 41 (hornerInitL 8 exp8F exp8Phi 43) =
    dySt log8_h2_s41 :=
  log8Run_cut log8_h2_pq log8_h2_bp 43 _ 2 39 log8_h2_r0_2
    (log8Run_cut log8_h2_pq log8_h2_bp 43 _ 2 37 log8_h2_r2_4
    (log8Run_cut log8_h2_pq log8_h2_bp 43 _ 2 35 log8_h2_r4_6
    (log8Run_cut log8_h2_pq log8_h2_bp 43 _ 2 33 log8_h2_r6_8
    (log8Run_cut log8_h2_pq log8_h2_bp 43 _ 2 31 log8_h2_r8_10
    (log8Run_cut log8_h2_pq log8_h2_bp 43 _ 2 29 log8_h2_r10_12
    (log8Run_cut log8_h2_pq log8_h2_bp 43 _ 2 27 log8_h2_r12_14
    (log8Run_cut log8_h2_pq log8_h2_bp 43 _ 2 25 log8_h2_r14_16
    (log8Run_cut log8_h2_pq log8_h2_bp 43 _ 2 23 log8_h2_r16_18
    (log8Run_cut log8_h2_pq log8_h2_bp 43 _ 2 21 log8_h2_r18_20
    (log8Run_cut log8_h2_pq log8_h2_bp 43 _ 2 19 log8_h2_r20_22
    (log8Run_cut log8_h2_pq log8_h2_bp 43 _ 2 17 log8_h2_r22_24
    (log8Run_cut log8_h2_pq log8_h2_bp 43 _ 2 15 log8_h2_r24_26
    (log8Run_cut log8_h2_pq log8_h2_bp 43 _ 2 13 log8_h2_r26_28
    (log8Run_cut log8_h2_pq log8_h2_bp 43 _ 2 11 log8_h2_r28_30
    (log8Run_cut log8_h2_pq log8_h2_bp 43 _ 2 9 log8_h2_r30_32
    (log8Run_cut log8_h2_pq log8_h2_bp 43 _ 2 7 log8_h2_r32_34
    (log8Run_cut log8_h2_pq log8_h2_bp 43 _ 2 5 log8_h2_r34_36
    (log8Run_cut log8_h2_pq log8_h2_bp 43 _ 2 3 log8_h2_r36_38
    (log8Run_cut log8_h2_pq log8_h2_bp 43 _ 2 1 log8_h2_r38_40
    (log8_h2_r40_41))))))))))))))))))))

theorem log8_h2_hp : Log8Head true 3 43 log8_h2_pq log8_h2_bp (dySt log8_h2_tp) :=
  Log8Head.mk_ne (by decide) log8_h2_q log8_h2_r log8_h2_wt log8_h2_yt log8_h2_tpt

theorem log8_h2_hm : Log8Head false 3 43 log8_h2_pq log8_h2_bp (dySt log8_h2_tm) :=
  Log8Head.mk_ne (by decide) log8_h2_q log8_h2_r log8_h2_wt log8_h2_yt log8_h2_tmt

theorem log8_g2zp0e0_sq :
    log8SqRun true 3 log8_g2zp0e0_v.1 log8_g2zp0e0_v.2.1 3 (dySt log8_h2_tp) =
      dySt log8_g2zp0e0_s3 := by
  show log8Sq true 3 log8_g2zp0e0_v.1 log8_g2zp0e0_v.2.1 2
      (log8Sq true 3 log8_g2zp0e0_v.1 log8_g2zp0e0_v.2.1 1
      (log8Sq true 3 log8_g2zp0e0_v.1 log8_g2zp0e0_v.2.1 0
      (dySt log8_h2_tp))) = _
  rw [log8_g2zp0e0_q0_2, log8_g2zp0e0_q2_3]

theorem log8_g2zp0e0_ev :
    Log8Eval true true 3 43 log8_g2zp0e0_v.1 log8_g2zp0e0_v.2.2.2 false log8_g2zp0e0_v.2.1 log8_g2zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g2zp0e0_leaf log8_h2_hp log8_g2zp0e0_sq log8_g2zp0e0_a log8_g2zp0e0_b log8_g2zp0e0_end

theorem log8_g2zp0e1_sq :
    log8SqRun true 3 log8_g2zp0e1_v.1 log8_g2zp0e1_v.2.1 3 (dySt log8_h2_tp) =
      dySt log8_g2zp0e1_s3 := by
  show log8Sq true 3 log8_g2zp0e1_v.1 log8_g2zp0e1_v.2.1 2
      (log8Sq true 3 log8_g2zp0e1_v.1 log8_g2zp0e1_v.2.1 1
      (log8Sq true 3 log8_g2zp0e1_v.1 log8_g2zp0e1_v.2.1 0
      (dySt log8_h2_tp))) = _
  rw [log8_g2zp0e1_q0_2, log8_g2zp0e1_q2_3]

theorem log8_g2zp0e1_ev :
    Log8Eval true true 3 43 log8_g2zp0e1_v.1 log8_g2zp0e1_v.2.2.2 false log8_g2zp0e1_v.2.1 log8_g2zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g2zp0e1_leaf log8_h2_hp log8_g2zp0e1_sq log8_g2zp0e1_a log8_g2zp0e1_b log8_g2zp0e1_end

theorem log8_g2np0e0_sq :
    log8SqRun true 3 log8_g2np0e0_v.1 log8_g2np0e0_v.2.1 3 (dySt log8_h2_tp) =
      dySt log8_g2np0e0_s3 := by
  show log8Sq true 3 log8_g2np0e0_v.1 log8_g2np0e0_v.2.1 2
      (log8Sq true 3 log8_g2np0e0_v.1 log8_g2np0e0_v.2.1 1
      (log8Sq true 3 log8_g2np0e0_v.1 log8_g2np0e0_v.2.1 0
      (dySt log8_h2_tp))) = _
  rw [log8_g2np0e0_q0_2, log8_g2np0e0_q2_3]

theorem log8_g2np0e0_ev :
    Log8Eval false true 3 43 log8_g2np0e0_v.1 log8_g2np0e0_v.2.2.2 false log8_g2np0e0_v.2.1 log8_g2np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g2np0e0_leaf log8_h2_hp log8_g2np0e0_sq log8_g2np0e0_a log8_g2np0e0_b log8_g2np0e0_end

theorem log8_g2np0e1_sq :
    log8SqRun true 3 log8_g2np0e1_v.1 log8_g2np0e1_v.2.1 3 (dySt log8_h2_tp) =
      dySt log8_g2np0e1_s3 := by
  show log8Sq true 3 log8_g2np0e1_v.1 log8_g2np0e1_v.2.1 2
      (log8Sq true 3 log8_g2np0e1_v.1 log8_g2np0e1_v.2.1 1
      (log8Sq true 3 log8_g2np0e1_v.1 log8_g2np0e1_v.2.1 0
      (dySt log8_h2_tp))) = _
  rw [log8_g2np0e1_q0_2, log8_g2np0e1_q2_3]

theorem log8_g2np0e1_ev :
    Log8Eval false true 3 43 log8_g2np0e1_v.1 log8_g2np0e1_v.2.2.2 false log8_g2np0e1_v.2.1 log8_g2np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g2np0e1_leaf log8_h2_hp log8_g2np0e1_sq log8_g2np0e1_a log8_g2np0e1_b log8_g2np0e1_end

theorem log8_g2zm0e0_sq :
    log8SqRun false 3 log8_g2zm0e0_v.1 log8_g2zm0e0_v.2.1 3 (dySt log8_h2_tm) =
      dySt log8_g2zm0e0_s3 := by
  show log8Sq false 3 log8_g2zm0e0_v.1 log8_g2zm0e0_v.2.1 2
      (log8Sq false 3 log8_g2zm0e0_v.1 log8_g2zm0e0_v.2.1 1
      (log8Sq false 3 log8_g2zm0e0_v.1 log8_g2zm0e0_v.2.1 0
      (dySt log8_h2_tm))) = _
  rw [log8_g2zm0e0_q0_2, log8_g2zm0e0_q2_3]

theorem log8_g2zm0e0_ev :
    Log8Eval true false 3 43 log8_g2zm0e0_v.1 log8_g2zm0e0_v.2.2.2 false log8_g2zm0e0_v.2.1 log8_g2zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g2zm0e0_leaf log8_h2_hm log8_g2zm0e0_sq log8_g2zm0e0_a log8_g2zm0e0_b log8_g2zm0e0_end

theorem log8_g2zm0e1_sq :
    log8SqRun false 3 log8_g2zm0e1_v.1 log8_g2zm0e1_v.2.1 3 (dySt log8_h2_tm) =
      dySt log8_g2zm0e1_s3 := by
  show log8Sq false 3 log8_g2zm0e1_v.1 log8_g2zm0e1_v.2.1 2
      (log8Sq false 3 log8_g2zm0e1_v.1 log8_g2zm0e1_v.2.1 1
      (log8Sq false 3 log8_g2zm0e1_v.1 log8_g2zm0e1_v.2.1 0
      (dySt log8_h2_tm))) = _
  rw [log8_g2zm0e1_q0_2, log8_g2zm0e1_q2_3]

theorem log8_g2zm0e1_ev :
    Log8Eval true false 3 43 log8_g2zm0e1_v.1 log8_g2zm0e1_v.2.2.2 false log8_g2zm0e1_v.2.1 log8_g2zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g2zm0e1_leaf log8_h2_hm log8_g2zm0e1_sq log8_g2zm0e1_a log8_g2zm0e1_b log8_g2zm0e1_end

theorem log8_g2nm0e0_sq :
    log8SqRun false 3 log8_g2nm0e0_v.1 log8_g2nm0e0_v.2.1 3 (dySt log8_h2_tm) =
      dySt log8_g2nm0e0_s3 := by
  show log8Sq false 3 log8_g2nm0e0_v.1 log8_g2nm0e0_v.2.1 2
      (log8Sq false 3 log8_g2nm0e0_v.1 log8_g2nm0e0_v.2.1 1
      (log8Sq false 3 log8_g2nm0e0_v.1 log8_g2nm0e0_v.2.1 0
      (dySt log8_h2_tm))) = _
  rw [log8_g2nm0e0_q0_2, log8_g2nm0e0_q2_3]

theorem log8_g2nm0e0_ev :
    Log8Eval false false 3 43 log8_g2nm0e0_v.1 log8_g2nm0e0_v.2.2.2 false log8_g2nm0e0_v.2.1 log8_g2nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g2nm0e0_leaf log8_h2_hm log8_g2nm0e0_sq log8_g2nm0e0_a log8_g2nm0e0_b log8_g2nm0e0_end

theorem log8_g2nm0e1_sq :
    log8SqRun false 3 log8_g2nm0e1_v.1 log8_g2nm0e1_v.2.1 3 (dySt log8_h2_tm) =
      dySt log8_g2nm0e1_s3 := by
  show log8Sq false 3 log8_g2nm0e1_v.1 log8_g2nm0e1_v.2.1 2
      (log8Sq false 3 log8_g2nm0e1_v.1 log8_g2nm0e1_v.2.1 1
      (log8Sq false 3 log8_g2nm0e1_v.1 log8_g2nm0e1_v.2.1 0
      (dySt log8_h2_tm))) = _
  rw [log8_g2nm0e1_q0_2, log8_g2nm0e1_q2_3]

theorem log8_g2nm0e1_ev :
    Log8Eval false false 3 43 log8_g2nm0e1_v.1 log8_g2nm0e1_v.2.2.2 false log8_g2nm0e1_v.2.1 log8_g2nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g2nm0e1_leaf log8_h2_hm log8_g2nm0e1_sq log8_g2nm0e1_a log8_g2nm0e1_b log8_g2nm0e1_end

theorem log8_h34_q : ∀ q ∈ log8_h34_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h34_r : log8Run log8_h34_pq log8_h34_bp 9 0 7 (hornerInitL 8 exp8F exp8Phi 9) =
    dySt log8_h34_s7 :=
  log8Run_cut log8_h34_pq log8_h34_bp 9 _ 2 5 log8_h34_r0_2
    (log8Run_cut log8_h34_pq log8_h34_bp 9 _ 2 3 log8_h34_r2_4
    (log8Run_cut log8_h34_pq log8_h34_bp 9 _ 2 1 log8_h34_r4_6
    (log8_h34_r6_7)))

theorem log8_h34_hp : Log8Head true 0 9 log8_h34_pq log8_h34_bp (dySt log8_h34_tp) :=
  Log8Head.mk_ne (by decide) log8_h34_q log8_h34_r log8_h34_wt log8_h34_yt log8_h34_tpt

theorem log8_h34_hm : Log8Head false 0 9 log8_h34_pq log8_h34_bp (dySt log8_h34_tm) :=
  Log8Head.mk_ne (by decide) log8_h34_q log8_h34_r log8_h34_wt log8_h34_yt log8_h34_tmt

theorem log8_h35_q : ∀ q ∈ log8_h35_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h35_r : log8Run log8_h35_pq log8_h35_bp 9 0 7 (hornerInitL 8 exp8F exp8Phi 9) =
    dySt log8_h35_s7 :=
  log8Run_cut log8_h35_pq log8_h35_bp 9 _ 2 5 log8_h35_r0_2
    (log8Run_cut log8_h35_pq log8_h35_bp 9 _ 2 3 log8_h35_r2_4
    (log8Run_cut log8_h35_pq log8_h35_bp 9 _ 2 1 log8_h35_r4_6
    (log8_h35_r6_7)))

theorem log8_h35_hp : Log8Head true 0 9 log8_h35_pq log8_h35_bp (dySt log8_h35_tp) :=
  Log8Head.mk_ne (by decide) log8_h35_q log8_h35_r log8_h35_wt log8_h35_yt log8_h35_tpt

theorem log8_h35_hm : Log8Head false 0 9 log8_h35_pq log8_h35_bp (dySt log8_h35_tm) :=
  Log8Head.mk_ne (by decide) log8_h35_q log8_h35_r log8_h35_wt log8_h35_yt log8_h35_tmt

theorem log8_h36_q : ∀ q ∈ log8_h36_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h36_r : log8Run log8_h36_pq log8_h36_bp 9 0 7 (hornerInitL 8 exp8F exp8Phi 9) =
    dySt log8_h36_s7 :=
  log8Run_cut log8_h36_pq log8_h36_bp 9 _ 2 5 log8_h36_r0_2
    (log8Run_cut log8_h36_pq log8_h36_bp 9 _ 2 3 log8_h36_r2_4
    (log8Run_cut log8_h36_pq log8_h36_bp 9 _ 2 1 log8_h36_r4_6
    (log8_h36_r6_7)))

theorem log8_h36_hp : Log8Head true 0 9 log8_h36_pq log8_h36_bp (dySt log8_h36_tp) :=
  Log8Head.mk_ne (by decide) log8_h36_q log8_h36_r log8_h36_wt log8_h36_yt log8_h36_tpt

theorem log8_h36_hm : Log8Head false 0 9 log8_h36_pq log8_h36_bp (dySt log8_h36_tm) :=
  Log8Head.mk_ne (by decide) log8_h36_q log8_h36_r log8_h36_wt log8_h36_yt log8_h36_tmt

theorem log8_g28zp0e0_ev :
    Log8Eval true true 0 9 log8_g28zp0e0_v.1 log8_g28zp0e0_v.2.2.2 false log8_g28zp0e0_v.2.1 log8_g28zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g28zp0e0_leaf log8_h36_hp rfl log8_g28zp0e0_a log8_g28zp0e0_b log8_g28zp0e0_end

theorem log8_g28zp0e1_ev :
    Log8Eval true true 0 9 log8_g28zp0e1_v.1 log8_g28zp0e1_v.2.2.2 false log8_g28zp0e1_v.2.1 log8_g28zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g28zp0e1_leaf log8_h35_hp rfl log8_g28zp0e1_a log8_g28zp0e1_b log8_g28zp0e1_end

theorem log8_g28np0e0_ev :
    Log8Eval false true 0 9 log8_g28np0e0_v.1 log8_g28np0e0_v.2.2.2 false log8_g28np0e0_v.2.1 log8_g28np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g28np0e0_leaf log8_h34_hp rfl log8_g28np0e0_a log8_g28np0e0_b log8_g28np0e0_end

theorem log8_g28np0e1_ev :
    Log8Eval false true 0 9 log8_g28np0e1_v.1 log8_g28np0e1_v.2.2.2 false log8_g28np0e1_v.2.1 log8_g28np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g28np0e1_leaf log8_h34_hp rfl log8_g28np0e1_a log8_g28np0e1_b log8_g28np0e1_end

theorem log8_g28zm0e0_ev :
    Log8Eval true false 0 9 log8_g28zm0e0_v.1 log8_g28zm0e0_v.2.2.2 false log8_g28zm0e0_v.2.1 log8_g28zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g28zm0e0_leaf log8_h36_hm rfl log8_g28zm0e0_a log8_g28zm0e0_b log8_g28zm0e0_end

theorem log8_g28zm0e1_ev :
    Log8Eval true false 0 9 log8_g28zm0e1_v.1 log8_g28zm0e1_v.2.2.2 false log8_g28zm0e1_v.2.1 log8_g28zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g28zm0e1_leaf log8_h35_hm rfl log8_g28zm0e1_a log8_g28zm0e1_b log8_g28zm0e1_end

theorem log8_g28nm0e0_ev :
    Log8Eval false false 0 9 log8_g28nm0e0_v.1 log8_g28nm0e0_v.2.2.2 false log8_g28nm0e0_v.2.1 log8_g28nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g28nm0e0_leaf log8_h34_hm rfl log8_g28nm0e0_a log8_g28nm0e0_b log8_g28nm0e0_end

theorem log8_g28nm0e1_ev :
    Log8Eval false false 0 9 log8_g28nm0e1_v.1 log8_g28nm0e1_v.2.2.2 false log8_g28nm0e1_v.2.1 log8_g28nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g28nm0e1_leaf log8_h34_hm rfl log8_g28nm0e1_a log8_g28nm0e1_b log8_g28nm0e1_end

theorem log8_h40_q : ∀ q ∈ log8_h40_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h40_r : log8Run log8_h40_pq log8_h40_bp 7 0 5 (hornerInitL 8 exp8F exp8Phi 7) =
    dySt log8_h40_s5 :=
  log8Run_cut log8_h40_pq log8_h40_bp 7 _ 2 3 log8_h40_r0_2
    (log8Run_cut log8_h40_pq log8_h40_bp 7 _ 2 1 log8_h40_r2_4
    (log8_h40_r4_5))

theorem log8_h40_hp : Log8Head true 0 7 log8_h40_pq log8_h40_bp (dySt log8_h40_tp) :=
  Log8Head.mk_ne (by decide) log8_h40_q log8_h40_r log8_h40_wt log8_h40_yt log8_h40_tpt

theorem log8_h40_hm : Log8Head false 0 7 log8_h40_pq log8_h40_bp (dySt log8_h40_tm) :=
  Log8Head.mk_ne (by decide) log8_h40_q log8_h40_r log8_h40_wt log8_h40_yt log8_h40_tmt

theorem log8_h41_q : ∀ q ∈ log8_h41_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h41_r : log8Run log8_h41_pq log8_h41_bp 7 0 5 (hornerInitL 8 exp8F exp8Phi 7) =
    dySt log8_h41_s5 :=
  log8Run_cut log8_h41_pq log8_h41_bp 7 _ 2 3 log8_h41_r0_2
    (log8Run_cut log8_h41_pq log8_h41_bp 7 _ 2 1 log8_h41_r2_4
    (log8_h41_r4_5))

theorem log8_h41_hp : Log8Head true 0 7 log8_h41_pq log8_h41_bp (dySt log8_h41_tp) :=
  Log8Head.mk_ne (by decide) log8_h41_q log8_h41_r log8_h41_wt log8_h41_yt log8_h41_tpt

theorem log8_h41_hm : Log8Head false 0 7 log8_h41_pq log8_h41_bp (dySt log8_h41_tm) :=
  Log8Head.mk_ne (by decide) log8_h41_q log8_h41_r log8_h41_wt log8_h41_yt log8_h41_tmt

theorem log8_h42_q : ∀ q ∈ log8_h42_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h42_r : log8Run log8_h42_pq log8_h42_bp 7 0 5 (hornerInitL 8 exp8F exp8Phi 7) =
    dySt log8_h42_s5 :=
  log8Run_cut log8_h42_pq log8_h42_bp 7 _ 2 3 log8_h42_r0_2
    (log8Run_cut log8_h42_pq log8_h42_bp 7 _ 2 1 log8_h42_r2_4
    (log8_h42_r4_5))

theorem log8_h42_hp : Log8Head true 0 7 log8_h42_pq log8_h42_bp (dySt log8_h42_tp) :=
  Log8Head.mk_ne (by decide) log8_h42_q log8_h42_r log8_h42_wt log8_h42_yt log8_h42_tpt

theorem log8_h42_hm : Log8Head false 0 7 log8_h42_pq log8_h42_bp (dySt log8_h42_tm) :=
  Log8Head.mk_ne (by decide) log8_h42_q log8_h42_r log8_h42_wt log8_h42_yt log8_h42_tmt

theorem log8_g30zp0e0_ev :
    Log8Eval true true 0 7 log8_g30zp0e0_v.1 log8_g30zp0e0_v.2.2.2 true log8_g30zp0e0_v.2.1 log8_g30zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g30zp0e0_leaf log8_h42_hp rfl log8_g30zp0e0_a log8_g30zp0e0_b log8_g30zp0e0_end

theorem log8_g30zp0e1_ev :
    Log8Eval true true 0 7 log8_g30zp0e1_v.1 log8_g30zp0e1_v.2.2.2 true log8_g30zp0e1_v.2.1 log8_g30zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g30zp0e1_leaf log8_h41_hp rfl log8_g30zp0e1_a log8_g30zp0e1_b log8_g30zp0e1_end

theorem log8_g30np0e0_ev :
    Log8Eval false true 0 7 log8_g30np0e0_v.1 log8_g30np0e0_v.2.2.2 false log8_g30np0e0_v.2.1 log8_g30np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g30np0e0_leaf log8_h40_hp rfl log8_g30np0e0_a log8_g30np0e0_b log8_g30np0e0_end

theorem log8_g30np0e1_ev :
    Log8Eval false true 0 7 log8_g30np0e1_v.1 log8_g30np0e1_v.2.2.2 false log8_g30np0e1_v.2.1 log8_g30np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g30np0e1_leaf log8_h40_hp rfl log8_g30np0e1_a log8_g30np0e1_b log8_g30np0e1_end

theorem log8_g30zm0e0_ev :
    Log8Eval true false 0 7 log8_g30zm0e0_v.1 log8_g30zm0e0_v.2.2.2 true log8_g30zm0e0_v.2.1 log8_g30zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g30zm0e0_leaf log8_h42_hm rfl log8_g30zm0e0_a log8_g30zm0e0_b log8_g30zm0e0_end

theorem log8_g30zm0e1_ev :
    Log8Eval true false 0 7 log8_g30zm0e1_v.1 log8_g30zm0e1_v.2.2.2 true log8_g30zm0e1_v.2.1 log8_g30zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g30zm0e1_leaf log8_h41_hm rfl log8_g30zm0e1_a log8_g30zm0e1_b log8_g30zm0e1_end

theorem log8_g30nm0e0_ev :
    Log8Eval false false 0 7 log8_g30nm0e0_v.1 log8_g30nm0e0_v.2.2.2 false log8_g30nm0e0_v.2.1 log8_g30nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g30nm0e0_leaf log8_h40_hm rfl log8_g30nm0e0_a log8_g30nm0e0_b log8_g30nm0e0_end

theorem log8_g30nm0e1_ev :
    Log8Eval false false 0 7 log8_g30nm0e1_v.1 log8_g30nm0e1_v.2.2.2 false log8_g30nm0e1_v.2.1 log8_g30nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g30nm0e1_leaf log8_h40_hm rfl log8_g30nm0e1_a log8_g30nm0e1_b log8_g30nm0e1_end

theorem log8_h46_q : ∀ q ∈ log8_h46_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h46_r : log8Run log8_h46_pq log8_h46_bp 5 0 3 (hornerInitL 8 exp8F exp8Phi 5) =
    dySt log8_h46_s3 :=
  log8Run_cut log8_h46_pq log8_h46_bp 5 _ 2 1 log8_h46_r0_2
    (log8_h46_r2_3)

theorem log8_h46_hp : Log8Head true 0 5 log8_h46_pq log8_h46_bp (dySt log8_h46_tp) :=
  Log8Head.mk_ne (by decide) log8_h46_q log8_h46_r log8_h46_wt log8_h46_yt log8_h46_tpt

theorem log8_h46_hm : Log8Head false 0 5 log8_h46_pq log8_h46_bp (dySt log8_h46_tm) :=
  Log8Head.mk_ne (by decide) log8_h46_q log8_h46_r log8_h46_wt log8_h46_yt log8_h46_tmt

theorem log8_h47_q : ∀ q ∈ log8_h47_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h47_r : log8Run log8_h47_pq log8_h47_bp 5 0 3 (hornerInitL 8 exp8F exp8Phi 5) =
    dySt log8_h47_s3 :=
  log8Run_cut log8_h47_pq log8_h47_bp 5 _ 2 1 log8_h47_r0_2
    (log8_h47_r2_3)

theorem log8_h47_hp : Log8Head true 0 5 log8_h47_pq log8_h47_bp (dySt log8_h47_tp) :=
  Log8Head.mk_ne (by decide) log8_h47_q log8_h47_r log8_h47_wt log8_h47_yt log8_h47_tpt

theorem log8_h47_hm : Log8Head false 0 5 log8_h47_pq log8_h47_bp (dySt log8_h47_tm) :=
  Log8Head.mk_ne (by decide) log8_h47_q log8_h47_r log8_h47_wt log8_h47_yt log8_h47_tmt

theorem log8_h48_q : ∀ q ∈ log8_h48_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h48_r : log8Run log8_h48_pq log8_h48_bp 5 0 3 (hornerInitL 8 exp8F exp8Phi 5) =
    dySt log8_h48_s3 :=
  log8Run_cut log8_h48_pq log8_h48_bp 5 _ 2 1 log8_h48_r0_2
    (log8_h48_r2_3)

theorem log8_h48_hp : Log8Head true 0 5 log8_h48_pq log8_h48_bp (dySt log8_h48_tp) :=
  Log8Head.mk_ne (by decide) log8_h48_q log8_h48_r log8_h48_wt log8_h48_yt log8_h48_tpt

theorem log8_h48_hm : Log8Head false 0 5 log8_h48_pq log8_h48_bp (dySt log8_h48_tm) :=
  Log8Head.mk_ne (by decide) log8_h48_q log8_h48_r log8_h48_wt log8_h48_yt log8_h48_tmt

theorem log8_g32zp0e0_ev :
    Log8Eval true true 0 5 log8_g32zp0e0_v.1 log8_g32zp0e0_v.2.2.2 true log8_g32zp0e0_v.2.1 log8_g32zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g32zp0e0_leaf log8_h48_hp rfl log8_g32zp0e0_a log8_g32zp0e0_b log8_g32zp0e0_end

theorem log8_g32zp0e1_ev :
    Log8Eval true true 0 5 log8_g32zp0e1_v.1 log8_g32zp0e1_v.2.2.2 true log8_g32zp0e1_v.2.1 log8_g32zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g32zp0e1_leaf log8_h47_hp rfl log8_g32zp0e1_a log8_g32zp0e1_b log8_g32zp0e1_end

theorem log8_g32np0e0_ev :
    Log8Eval false true 0 5 log8_g32np0e0_v.1 log8_g32np0e0_v.2.2.2 false log8_g32np0e0_v.2.1 log8_g32np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g32np0e0_leaf log8_h46_hp rfl log8_g32np0e0_a log8_g32np0e0_b log8_g32np0e0_end

theorem log8_g32np0e1_ev :
    Log8Eval false true 0 5 log8_g32np0e1_v.1 log8_g32np0e1_v.2.2.2 false log8_g32np0e1_v.2.1 log8_g32np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g32np0e1_leaf log8_h46_hp rfl log8_g32np0e1_a log8_g32np0e1_b log8_g32np0e1_end

theorem log8_g32zm0e0_ev :
    Log8Eval true false 0 5 log8_g32zm0e0_v.1 log8_g32zm0e0_v.2.2.2 true log8_g32zm0e0_v.2.1 log8_g32zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g32zm0e0_leaf log8_h48_hm rfl log8_g32zm0e0_a log8_g32zm0e0_b log8_g32zm0e0_end

theorem log8_g32zm0e1_ev :
    Log8Eval true false 0 5 log8_g32zm0e1_v.1 log8_g32zm0e1_v.2.2.2 true log8_g32zm0e1_v.2.1 log8_g32zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g32zm0e1_leaf log8_h47_hm rfl log8_g32zm0e1_a log8_g32zm0e1_b log8_g32zm0e1_end

theorem log8_g32nm0e0_ev :
    Log8Eval false false 0 5 log8_g32nm0e0_v.1 log8_g32nm0e0_v.2.2.2 false log8_g32nm0e0_v.2.1 log8_g32nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g32nm0e0_leaf log8_h46_hm rfl log8_g32nm0e0_a log8_g32nm0e0_b log8_g32nm0e0_end

theorem log8_g32nm0e1_ev :
    Log8Eval false false 0 5 log8_g32nm0e1_v.1 log8_g32nm0e1_v.2.2.2 false log8_g32nm0e1_v.2.1 log8_g32nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g32nm0e1_leaf log8_h46_hm rfl log8_g32nm0e1_a log8_g32nm0e1_b log8_g32nm0e1_end

theorem log8_h3_q : ∀ q ∈ log8_h3_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h3_r : log8Run log8_h3_pq log8_h3_bp 43 0 41 (hornerInitL 8 exp8F exp8Phi 43) =
    dySt log8_h3_s41 :=
  log8Run_cut log8_h3_pq log8_h3_bp 43 _ 2 39 log8_h3_r0_2
    (log8Run_cut log8_h3_pq log8_h3_bp 43 _ 2 37 log8_h3_r2_4
    (log8Run_cut log8_h3_pq log8_h3_bp 43 _ 2 35 log8_h3_r4_6
    (log8Run_cut log8_h3_pq log8_h3_bp 43 _ 2 33 log8_h3_r6_8
    (log8Run_cut log8_h3_pq log8_h3_bp 43 _ 2 31 log8_h3_r8_10
    (log8Run_cut log8_h3_pq log8_h3_bp 43 _ 2 29 log8_h3_r10_12
    (log8Run_cut log8_h3_pq log8_h3_bp 43 _ 2 27 log8_h3_r12_14
    (log8Run_cut log8_h3_pq log8_h3_bp 43 _ 2 25 log8_h3_r14_16
    (log8Run_cut log8_h3_pq log8_h3_bp 43 _ 2 23 log8_h3_r16_18
    (log8Run_cut log8_h3_pq log8_h3_bp 43 _ 2 21 log8_h3_r18_20
    (log8Run_cut log8_h3_pq log8_h3_bp 43 _ 2 19 log8_h3_r20_22
    (log8Run_cut log8_h3_pq log8_h3_bp 43 _ 2 17 log8_h3_r22_24
    (log8Run_cut log8_h3_pq log8_h3_bp 43 _ 2 15 log8_h3_r24_26
    (log8Run_cut log8_h3_pq log8_h3_bp 43 _ 2 13 log8_h3_r26_28
    (log8Run_cut log8_h3_pq log8_h3_bp 43 _ 2 11 log8_h3_r28_30
    (log8Run_cut log8_h3_pq log8_h3_bp 43 _ 2 9 log8_h3_r30_32
    (log8Run_cut log8_h3_pq log8_h3_bp 43 _ 2 7 log8_h3_r32_34
    (log8Run_cut log8_h3_pq log8_h3_bp 43 _ 2 5 log8_h3_r34_36
    (log8Run_cut log8_h3_pq log8_h3_bp 43 _ 2 3 log8_h3_r36_38
    (log8Run_cut log8_h3_pq log8_h3_bp 43 _ 2 1 log8_h3_r38_40
    (log8_h3_r40_41))))))))))))))))))))

theorem log8_h3_hp : Log8Head true 2 43 log8_h3_pq log8_h3_bp (dySt log8_h3_tp) :=
  Log8Head.mk_ne (by decide) log8_h3_q log8_h3_r log8_h3_wt log8_h3_yt log8_h3_tpt

theorem log8_h3_hm : Log8Head false 2 43 log8_h3_pq log8_h3_bp (dySt log8_h3_tm) :=
  Log8Head.mk_ne (by decide) log8_h3_q log8_h3_r log8_h3_wt log8_h3_yt log8_h3_tmt

theorem log8_g3zp0e0_sq :
    log8SqRun true 2 log8_g3zp0e0_v.1 log8_g3zp0e0_v.2.1 2 (dySt log8_h3_tp) =
      dySt log8_g3zp0e0_s2 := by
  show log8Sq true 2 log8_g3zp0e0_v.1 log8_g3zp0e0_v.2.1 1
      (log8Sq true 2 log8_g3zp0e0_v.1 log8_g3zp0e0_v.2.1 0
      (dySt log8_h3_tp)) = _
  rw [log8_g3zp0e0_q0_2]

theorem log8_g3zp0e0_ev :
    Log8Eval true true 2 43 log8_g3zp0e0_v.1 log8_g3zp0e0_v.2.2.2 false log8_g3zp0e0_v.2.1 log8_g3zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g3zp0e0_leaf log8_h3_hp log8_g3zp0e0_sq log8_g3zp0e0_a log8_g3zp0e0_b log8_g3zp0e0_end

theorem log8_g3zp0e1_sq :
    log8SqRun true 2 log8_g3zp0e1_v.1 log8_g3zp0e1_v.2.1 2 (dySt log8_h3_tp) =
      dySt log8_g3zp0e1_s2 := by
  show log8Sq true 2 log8_g3zp0e1_v.1 log8_g3zp0e1_v.2.1 1
      (log8Sq true 2 log8_g3zp0e1_v.1 log8_g3zp0e1_v.2.1 0
      (dySt log8_h3_tp)) = _
  rw [log8_g3zp0e1_q0_2]

theorem log8_g3zp0e1_ev :
    Log8Eval true true 2 43 log8_g3zp0e1_v.1 log8_g3zp0e1_v.2.2.2 false log8_g3zp0e1_v.2.1 log8_g3zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g3zp0e1_leaf log8_h3_hp log8_g3zp0e1_sq log8_g3zp0e1_a log8_g3zp0e1_b log8_g3zp0e1_end

theorem log8_g3np0e0_sq :
    log8SqRun true 2 log8_g3np0e0_v.1 log8_g3np0e0_v.2.1 2 (dySt log8_h3_tp) =
      dySt log8_g3np0e0_s2 := by
  show log8Sq true 2 log8_g3np0e0_v.1 log8_g3np0e0_v.2.1 1
      (log8Sq true 2 log8_g3np0e0_v.1 log8_g3np0e0_v.2.1 0
      (dySt log8_h3_tp)) = _
  rw [log8_g3np0e0_q0_2]

theorem log8_g3np0e0_ev :
    Log8Eval false true 2 43 log8_g3np0e0_v.1 log8_g3np0e0_v.2.2.2 false log8_g3np0e0_v.2.1 log8_g3np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g3np0e0_leaf log8_h3_hp log8_g3np0e0_sq log8_g3np0e0_a log8_g3np0e0_b log8_g3np0e0_end

theorem log8_g3np0e1_sq :
    log8SqRun true 2 log8_g3np0e1_v.1 log8_g3np0e1_v.2.1 2 (dySt log8_h3_tp) =
      dySt log8_g3np0e1_s2 := by
  show log8Sq true 2 log8_g3np0e1_v.1 log8_g3np0e1_v.2.1 1
      (log8Sq true 2 log8_g3np0e1_v.1 log8_g3np0e1_v.2.1 0
      (dySt log8_h3_tp)) = _
  rw [log8_g3np0e1_q0_2]

theorem log8_g3np0e1_ev :
    Log8Eval false true 2 43 log8_g3np0e1_v.1 log8_g3np0e1_v.2.2.2 false log8_g3np0e1_v.2.1 log8_g3np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g3np0e1_leaf log8_h3_hp log8_g3np0e1_sq log8_g3np0e1_a log8_g3np0e1_b log8_g3np0e1_end

theorem log8_g3zm0e0_sq :
    log8SqRun false 2 log8_g3zm0e0_v.1 log8_g3zm0e0_v.2.1 2 (dySt log8_h3_tm) =
      dySt log8_g3zm0e0_s2 := by
  show log8Sq false 2 log8_g3zm0e0_v.1 log8_g3zm0e0_v.2.1 1
      (log8Sq false 2 log8_g3zm0e0_v.1 log8_g3zm0e0_v.2.1 0
      (dySt log8_h3_tm)) = _
  rw [log8_g3zm0e0_q0_2]

theorem log8_g3zm0e0_ev :
    Log8Eval true false 2 43 log8_g3zm0e0_v.1 log8_g3zm0e0_v.2.2.2 false log8_g3zm0e0_v.2.1 log8_g3zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g3zm0e0_leaf log8_h3_hm log8_g3zm0e0_sq log8_g3zm0e0_a log8_g3zm0e0_b log8_g3zm0e0_end

theorem log8_g3zm0e1_sq :
    log8SqRun false 2 log8_g3zm0e1_v.1 log8_g3zm0e1_v.2.1 2 (dySt log8_h3_tm) =
      dySt log8_g3zm0e1_s2 := by
  show log8Sq false 2 log8_g3zm0e1_v.1 log8_g3zm0e1_v.2.1 1
      (log8Sq false 2 log8_g3zm0e1_v.1 log8_g3zm0e1_v.2.1 0
      (dySt log8_h3_tm)) = _
  rw [log8_g3zm0e1_q0_2]

theorem log8_g3zm0e1_ev :
    Log8Eval true false 2 43 log8_g3zm0e1_v.1 log8_g3zm0e1_v.2.2.2 false log8_g3zm0e1_v.2.1 log8_g3zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g3zm0e1_leaf log8_h3_hm log8_g3zm0e1_sq log8_g3zm0e1_a log8_g3zm0e1_b log8_g3zm0e1_end

theorem log8_g3nm0e0_sq :
    log8SqRun false 2 log8_g3nm0e0_v.1 log8_g3nm0e0_v.2.1 2 (dySt log8_h3_tm) =
      dySt log8_g3nm0e0_s2 := by
  show log8Sq false 2 log8_g3nm0e0_v.1 log8_g3nm0e0_v.2.1 1
      (log8Sq false 2 log8_g3nm0e0_v.1 log8_g3nm0e0_v.2.1 0
      (dySt log8_h3_tm)) = _
  rw [log8_g3nm0e0_q0_2]

theorem log8_g3nm0e0_ev :
    Log8Eval false false 2 43 log8_g3nm0e0_v.1 log8_g3nm0e0_v.2.2.2 false log8_g3nm0e0_v.2.1 log8_g3nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g3nm0e0_leaf log8_h3_hm log8_g3nm0e0_sq log8_g3nm0e0_a log8_g3nm0e0_b log8_g3nm0e0_end

theorem log8_g3nm0e1_sq :
    log8SqRun false 2 log8_g3nm0e1_v.1 log8_g3nm0e1_v.2.1 2 (dySt log8_h3_tm) =
      dySt log8_g3nm0e1_s2 := by
  show log8Sq false 2 log8_g3nm0e1_v.1 log8_g3nm0e1_v.2.1 1
      (log8Sq false 2 log8_g3nm0e1_v.1 log8_g3nm0e1_v.2.1 0
      (dySt log8_h3_tm)) = _
  rw [log8_g3nm0e1_q0_2]

theorem log8_g3nm0e1_ev :
    Log8Eval false false 2 43 log8_g3nm0e1_v.1 log8_g3nm0e1_v.2.2.2 false log8_g3nm0e1_v.2.1 log8_g3nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g3nm0e1_leaf log8_h3_hm log8_g3nm0e1_sq log8_g3nm0e1_a log8_g3nm0e1_b log8_g3nm0e1_end

theorem log8_h13_q : ∀ q ∈ log8_h13_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h13_r : log8Run log8_h13_pq log8_h13_bp 28 0 26 (hornerInitL 8 exp8F exp8Phi 28) =
    dySt log8_h13_s26 :=
  log8Run_cut log8_h13_pq log8_h13_bp 28 _ 2 24 log8_h13_r0_2
    (log8Run_cut log8_h13_pq log8_h13_bp 28 _ 2 22 log8_h13_r2_4
    (log8Run_cut log8_h13_pq log8_h13_bp 28 _ 2 20 log8_h13_r4_6
    (log8Run_cut log8_h13_pq log8_h13_bp 28 _ 2 18 log8_h13_r6_8
    (log8Run_cut log8_h13_pq log8_h13_bp 28 _ 2 16 log8_h13_r8_10
    (log8Run_cut log8_h13_pq log8_h13_bp 28 _ 2 14 log8_h13_r10_12
    (log8Run_cut log8_h13_pq log8_h13_bp 28 _ 2 12 log8_h13_r12_14
    (log8Run_cut log8_h13_pq log8_h13_bp 28 _ 2 10 log8_h13_r14_16
    (log8Run_cut log8_h13_pq log8_h13_bp 28 _ 2 8 log8_h13_r16_18
    (log8Run_cut log8_h13_pq log8_h13_bp 28 _ 2 6 log8_h13_r18_20
    (log8Run_cut log8_h13_pq log8_h13_bp 28 _ 2 4 log8_h13_r20_22
    (log8Run_cut log8_h13_pq log8_h13_bp 28 _ 2 2 log8_h13_r22_24
    (log8_h13_r24_26))))))))))))

theorem log8_h13_hp : Log8Head true 0 28 log8_h13_pq log8_h13_bp (dySt log8_h13_tp) :=
  Log8Head.mk_ne (by decide) log8_h13_q log8_h13_r log8_h13_wt log8_h13_yt log8_h13_tpt

theorem log8_h13_hm : Log8Head false 0 28 log8_h13_pq log8_h13_bp (dySt log8_h13_tm) :=
  Log8Head.mk_ne (by decide) log8_h13_q log8_h13_r log8_h13_wt log8_h13_yt log8_h13_tmt

theorem log8_g11zp0e0_ev :
    Log8Eval true true 0 28 log8_g11zp0e0_v.1 log8_g11zp0e0_v.2.2.2 false log8_g11zp0e0_v.2.1 log8_g11zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g11zp0e0_leaf log8_h13_hp rfl log8_g11zp0e0_a log8_g11zp0e0_b log8_g11zp0e0_end

theorem log8_g11zp0e1_ev :
    Log8Eval true true 0 28 log8_g11zp0e1_v.1 log8_g11zp0e1_v.2.2.2 false log8_g11zp0e1_v.2.1 log8_g11zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g11zp0e1_leaf log8_h13_hp rfl log8_g11zp0e1_a log8_g11zp0e1_b log8_g11zp0e1_end

theorem log8_g11np0e0_ev :
    Log8Eval false true 0 28 log8_g11np0e0_v.1 log8_g11np0e0_v.2.2.2 false log8_g11np0e0_v.2.1 log8_g11np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g11np0e0_leaf log8_h13_hp rfl log8_g11np0e0_a log8_g11np0e0_b log8_g11np0e0_end

theorem log8_g11np0e1_ev :
    Log8Eval false true 0 28 log8_g11np0e1_v.1 log8_g11np0e1_v.2.2.2 false log8_g11np0e1_v.2.1 log8_g11np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g11np0e1_leaf log8_h13_hp rfl log8_g11np0e1_a log8_g11np0e1_b log8_g11np0e1_end

theorem log8_g11zm0e0_ev :
    Log8Eval true false 0 28 log8_g11zm0e0_v.1 log8_g11zm0e0_v.2.2.2 false log8_g11zm0e0_v.2.1 log8_g11zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g11zm0e0_leaf log8_h13_hm rfl log8_g11zm0e0_a log8_g11zm0e0_b log8_g11zm0e0_end

theorem log8_g11zm0e1_ev :
    Log8Eval true false 0 28 log8_g11zm0e1_v.1 log8_g11zm0e1_v.2.2.2 false log8_g11zm0e1_v.2.1 log8_g11zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g11zm0e1_leaf log8_h13_hm rfl log8_g11zm0e1_a log8_g11zm0e1_b log8_g11zm0e1_end

theorem log8_g11nm0e0_ev :
    Log8Eval false false 0 28 log8_g11nm0e0_v.1 log8_g11nm0e0_v.2.2.2 false log8_g11nm0e0_v.2.1 log8_g11nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g11nm0e0_leaf log8_h13_hm rfl log8_g11nm0e0_a log8_g11nm0e0_b log8_g11nm0e0_end

theorem log8_g11nm0e1_ev :
    Log8Eval false false 0 28 log8_g11nm0e1_v.1 log8_g11nm0e1_v.2.2.2 false log8_g11nm0e1_v.2.1 log8_g11nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g11nm0e1_leaf log8_h13_hm rfl log8_g11nm0e1_a log8_g11nm0e1_b log8_g11nm0e1_end

theorem log8_h18_q : ∀ q ∈ log8_h18_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h18_r : log8Run log8_h18_pq log8_h18_bp 21 0 19 (hornerInitL 8 exp8F exp8Phi 21) =
    dySt log8_h18_s19 :=
  log8Run_cut log8_h18_pq log8_h18_bp 21 _ 2 17 log8_h18_r0_2
    (log8Run_cut log8_h18_pq log8_h18_bp 21 _ 2 15 log8_h18_r2_4
    (log8Run_cut log8_h18_pq log8_h18_bp 21 _ 2 13 log8_h18_r4_6
    (log8Run_cut log8_h18_pq log8_h18_bp 21 _ 2 11 log8_h18_r6_8
    (log8Run_cut log8_h18_pq log8_h18_bp 21 _ 2 9 log8_h18_r8_10
    (log8Run_cut log8_h18_pq log8_h18_bp 21 _ 2 7 log8_h18_r10_12
    (log8Run_cut log8_h18_pq log8_h18_bp 21 _ 2 5 log8_h18_r12_14
    (log8Run_cut log8_h18_pq log8_h18_bp 21 _ 2 3 log8_h18_r14_16
    (log8Run_cut log8_h18_pq log8_h18_bp 21 _ 2 1 log8_h18_r16_18
    (log8_h18_r18_19)))))))))

theorem log8_h18_hp : Log8Head true 0 21 log8_h18_pq log8_h18_bp (dySt log8_h18_tp) :=
  Log8Head.mk_ne (by decide) log8_h18_q log8_h18_r log8_h18_wt log8_h18_yt log8_h18_tpt

theorem log8_h18_hm : Log8Head false 0 21 log8_h18_pq log8_h18_bp (dySt log8_h18_tm) :=
  Log8Head.mk_ne (by decide) log8_h18_q log8_h18_r log8_h18_wt log8_h18_yt log8_h18_tmt

theorem log8_g16zp0e0_ev :
    Log8Eval true true 0 21 log8_g16zp0e0_v.1 log8_g16zp0e0_v.2.2.2 false log8_g16zp0e0_v.2.1 log8_g16zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g16zp0e0_leaf log8_h18_hp rfl log8_g16zp0e0_a log8_g16zp0e0_b log8_g16zp0e0_end

theorem log8_g16zp0e1_ev :
    Log8Eval true true 0 21 log8_g16zp0e1_v.1 log8_g16zp0e1_v.2.2.2 false log8_g16zp0e1_v.2.1 log8_g16zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g16zp0e1_leaf log8_h18_hp rfl log8_g16zp0e1_a log8_g16zp0e1_b log8_g16zp0e1_end

theorem log8_g16np0e0_ev :
    Log8Eval false true 0 21 log8_g16np0e0_v.1 log8_g16np0e0_v.2.2.2 false log8_g16np0e0_v.2.1 log8_g16np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g16np0e0_leaf log8_h18_hp rfl log8_g16np0e0_a log8_g16np0e0_b log8_g16np0e0_end

theorem log8_g16np0e1_ev :
    Log8Eval false true 0 21 log8_g16np0e1_v.1 log8_g16np0e1_v.2.2.2 false log8_g16np0e1_v.2.1 log8_g16np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g16np0e1_leaf log8_h18_hp rfl log8_g16np0e1_a log8_g16np0e1_b log8_g16np0e1_end

theorem log8_g16zm0e0_ev :
    Log8Eval true false 0 21 log8_g16zm0e0_v.1 log8_g16zm0e0_v.2.2.2 false log8_g16zm0e0_v.2.1 log8_g16zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g16zm0e0_leaf log8_h18_hm rfl log8_g16zm0e0_a log8_g16zm0e0_b log8_g16zm0e0_end

theorem log8_g16zm0e1_ev :
    Log8Eval true false 0 21 log8_g16zm0e1_v.1 log8_g16zm0e1_v.2.2.2 false log8_g16zm0e1_v.2.1 log8_g16zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g16zm0e1_leaf log8_h18_hm rfl log8_g16zm0e1_a log8_g16zm0e1_b log8_g16zm0e1_end

theorem log8_g16nm0e0_ev :
    Log8Eval false false 0 21 log8_g16nm0e0_v.1 log8_g16nm0e0_v.2.2.2 false log8_g16nm0e0_v.2.1 log8_g16nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g16nm0e0_leaf log8_h18_hm rfl log8_g16nm0e0_a log8_g16nm0e0_b log8_g16nm0e0_end

theorem log8_g16nm0e1_ev :
    Log8Eval false false 0 21 log8_g16nm0e1_v.1 log8_g16nm0e1_v.2.2.2 false log8_g16nm0e1_v.2.1 log8_g16nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g16nm0e1_leaf log8_h18_hm rfl log8_g16nm0e1_a log8_g16nm0e1_b log8_g16nm0e1_end

theorem log8_h24_q : ∀ q ∈ log8_h24_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h24_r : log8Run log8_h24_pq log8_h24_bp 15 0 13 (hornerInitL 8 exp8F exp8Phi 15) =
    dySt log8_h24_s13 :=
  log8Run_cut log8_h24_pq log8_h24_bp 15 _ 2 11 log8_h24_r0_2
    (log8Run_cut log8_h24_pq log8_h24_bp 15 _ 2 9 log8_h24_r2_4
    (log8Run_cut log8_h24_pq log8_h24_bp 15 _ 2 7 log8_h24_r4_6
    (log8Run_cut log8_h24_pq log8_h24_bp 15 _ 2 5 log8_h24_r6_8
    (log8Run_cut log8_h24_pq log8_h24_bp 15 _ 2 3 log8_h24_r8_10
    (log8Run_cut log8_h24_pq log8_h24_bp 15 _ 2 1 log8_h24_r10_12
    (log8_h24_r12_13))))))

theorem log8_h24_hp : Log8Head true 0 15 log8_h24_pq log8_h24_bp (dySt log8_h24_tp) :=
  Log8Head.mk_ne (by decide) log8_h24_q log8_h24_r log8_h24_wt log8_h24_yt log8_h24_tpt

theorem log8_h24_hm : Log8Head false 0 15 log8_h24_pq log8_h24_bp (dySt log8_h24_tm) :=
  Log8Head.mk_ne (by decide) log8_h24_q log8_h24_r log8_h24_wt log8_h24_yt log8_h24_tmt

theorem log8_g22zp0e0_ev :
    Log8Eval true true 0 15 log8_g22zp0e0_v.1 log8_g22zp0e0_v.2.2.2 false log8_g22zp0e0_v.2.1 log8_g22zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g22zp0e0_leaf log8_h24_hp rfl log8_g22zp0e0_a log8_g22zp0e0_b log8_g22zp0e0_end

theorem log8_g22zp0e1_ev :
    Log8Eval true true 0 15 log8_g22zp0e1_v.1 log8_g22zp0e1_v.2.2.2 false log8_g22zp0e1_v.2.1 log8_g22zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g22zp0e1_leaf log8_h24_hp rfl log8_g22zp0e1_a log8_g22zp0e1_b log8_g22zp0e1_end

theorem log8_g22np0e0_ev :
    Log8Eval false true 0 15 log8_g22np0e0_v.1 log8_g22np0e0_v.2.2.2 false log8_g22np0e0_v.2.1 log8_g22np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g22np0e0_leaf log8_h24_hp rfl log8_g22np0e0_a log8_g22np0e0_b log8_g22np0e0_end

theorem log8_g22np0e1_ev :
    Log8Eval false true 0 15 log8_g22np0e1_v.1 log8_g22np0e1_v.2.2.2 false log8_g22np0e1_v.2.1 log8_g22np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g22np0e1_leaf log8_h24_hp rfl log8_g22np0e1_a log8_g22np0e1_b log8_g22np0e1_end

theorem log8_g22zm0e0_ev :
    Log8Eval true false 0 15 log8_g22zm0e0_v.1 log8_g22zm0e0_v.2.2.2 false log8_g22zm0e0_v.2.1 log8_g22zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g22zm0e0_leaf log8_h24_hm rfl log8_g22zm0e0_a log8_g22zm0e0_b log8_g22zm0e0_end

theorem log8_g22zm0e1_ev :
    Log8Eval true false 0 15 log8_g22zm0e1_v.1 log8_g22zm0e1_v.2.2.2 false log8_g22zm0e1_v.2.1 log8_g22zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g22zm0e1_leaf log8_h24_hm rfl log8_g22zm0e1_a log8_g22zm0e1_b log8_g22zm0e1_end

theorem log8_g22nm0e0_ev :
    Log8Eval false false 0 15 log8_g22nm0e0_v.1 log8_g22nm0e0_v.2.2.2 false log8_g22nm0e0_v.2.1 log8_g22nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g22nm0e0_leaf log8_h24_hm rfl log8_g22nm0e0_a log8_g22nm0e0_b log8_g22nm0e0_end

theorem log8_g22nm0e1_ev :
    Log8Eval false false 0 15 log8_g22nm0e1_v.1 log8_g22nm0e1_v.2.2.2 false log8_g22nm0e1_v.2.1 log8_g22nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g22nm0e1_leaf log8_h24_hm rfl log8_g22nm0e1_a log8_g22nm0e1_b log8_g22nm0e1_end

theorem log8_h55_q : ∀ q ∈ log8_h55_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h55_hp : Log8Head true 0 1 log8_h55_pq log8_h55_bp
    (upQ 200 (eTrQ log8_h55_bp 1 + 2 * ((8 : ℕ) : ℚ) * exp8Eta1 0), log8_h55_pq) :=
  Log8Head.mk_one true 0 log8_h55_bp log8_h55_q

theorem log8_h55_hm : Log8Head false 0 1 log8_h55_pq log8_h55_bp
    (upQ 200 (eTrQ log8_h55_bp 1 + 2 * ((8 : ℕ) : ℚ) * exp8Eta1 0), log8_h55_pq) :=
  Log8Head.mk_one false 0 log8_h55_bp log8_h55_q

theorem log8_h56_q : ∀ q ∈ log8_h56_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h56_hp : Log8Head true 0 1 log8_h56_pq log8_h56_bp
    (upQ 200 (eTrQ log8_h56_bp 1 + 2 * ((8 : ℕ) : ℚ) * exp8Eta1 0), log8_h56_pq) :=
  Log8Head.mk_one true 0 log8_h56_bp log8_h56_q

theorem log8_h56_hm : Log8Head false 0 1 log8_h56_pq log8_h56_bp
    (upQ 200 (eTrQ log8_h56_bp 1 + 2 * ((8 : ℕ) : ℚ) * exp8Eta1 0), log8_h56_pq) :=
  Log8Head.mk_one false 0 log8_h56_bp log8_h56_q

theorem log8_g36zp0e0_ev :
    Log8Eval true true 0 1 log8_g36zp0e0_v.1 log8_g36zp0e0_v.2.2.2 true log8_g36zp0e0_v.2.1 log8_g36zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g36zp0e0_leaf log8_h56_hp rfl log8_g36zp0e0_a log8_g36zp0e0_b log8_g36zp0e0_end

theorem log8_g36zp0e1_ev :
    Log8Eval true true 0 1 log8_g36zp0e1_v.1 log8_g36zp0e1_v.2.2.2 true log8_g36zp0e1_v.2.1 log8_g36zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g36zp0e1_leaf log8_h56_hp rfl log8_g36zp0e1_a log8_g36zp0e1_b log8_g36zp0e1_end

theorem log8_g36np0e0_ev :
    Log8Eval false true 0 1 log8_g36np0e0_v.1 log8_g36np0e0_v.2.2.2 false log8_g36np0e0_v.2.1 log8_g36np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g36np0e0_leaf log8_h55_hp rfl log8_g36np0e0_a log8_g36np0e0_b log8_g36np0e0_end

theorem log8_g36np0e1_ev :
    Log8Eval false true 0 1 log8_g36np0e1_v.1 log8_g36np0e1_v.2.2.2 false log8_g36np0e1_v.2.1 log8_g36np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g36np0e1_leaf log8_h55_hp rfl log8_g36np0e1_a log8_g36np0e1_b log8_g36np0e1_end

theorem log8_g36zm0e0_ev :
    Log8Eval true false 0 1 log8_g36zm0e0_v.1 log8_g36zm0e0_v.2.2.2 true log8_g36zm0e0_v.2.1 log8_g36zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g36zm0e0_leaf log8_h56_hm rfl log8_g36zm0e0_a log8_g36zm0e0_b log8_g36zm0e0_end

theorem log8_g36zm0e1_ev :
    Log8Eval true false 0 1 log8_g36zm0e1_v.1 log8_g36zm0e1_v.2.2.2 true log8_g36zm0e1_v.2.1 log8_g36zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g36zm0e1_leaf log8_h56_hm rfl log8_g36zm0e1_a log8_g36zm0e1_b log8_g36zm0e1_end

theorem log8_g36nm0e0_ev :
    Log8Eval false false 0 1 log8_g36nm0e0_v.1 log8_g36nm0e0_v.2.2.2 false log8_g36nm0e0_v.2.1 log8_g36nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g36nm0e0_leaf log8_h55_hm rfl log8_g36nm0e0_a log8_g36nm0e0_b log8_g36nm0e0_end

theorem log8_g36nm0e1_ev :
    Log8Eval false false 0 1 log8_g36nm0e1_v.1 log8_g36nm0e1_v.2.2.2 false log8_g36nm0e1_v.2.1 log8_g36nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g36nm0e1_leaf log8_h55_hm rfl log8_g36nm0e1_a log8_g36nm0e1_b log8_g36nm0e1_end

theorem log8_h4_q : ∀ q ∈ log8_h4_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h4_r : log8Run log8_h4_pq log8_h4_bp 43 0 41 (hornerInitL 8 exp8F exp8Phi 43) =
    dySt log8_h4_s41 :=
  log8Run_cut log8_h4_pq log8_h4_bp 43 _ 2 39 log8_h4_r0_2
    (log8Run_cut log8_h4_pq log8_h4_bp 43 _ 2 37 log8_h4_r2_4
    (log8Run_cut log8_h4_pq log8_h4_bp 43 _ 2 35 log8_h4_r4_6
    (log8Run_cut log8_h4_pq log8_h4_bp 43 _ 2 33 log8_h4_r6_8
    (log8Run_cut log8_h4_pq log8_h4_bp 43 _ 2 31 log8_h4_r8_10
    (log8Run_cut log8_h4_pq log8_h4_bp 43 _ 2 29 log8_h4_r10_12
    (log8Run_cut log8_h4_pq log8_h4_bp 43 _ 2 27 log8_h4_r12_14
    (log8Run_cut log8_h4_pq log8_h4_bp 43 _ 2 25 log8_h4_r14_16
    (log8Run_cut log8_h4_pq log8_h4_bp 43 _ 2 23 log8_h4_r16_18
    (log8Run_cut log8_h4_pq log8_h4_bp 43 _ 2 21 log8_h4_r18_20
    (log8Run_cut log8_h4_pq log8_h4_bp 43 _ 2 19 log8_h4_r20_22
    (log8Run_cut log8_h4_pq log8_h4_bp 43 _ 2 17 log8_h4_r22_24
    (log8Run_cut log8_h4_pq log8_h4_bp 43 _ 2 15 log8_h4_r24_26
    (log8Run_cut log8_h4_pq log8_h4_bp 43 _ 2 13 log8_h4_r26_28
    (log8Run_cut log8_h4_pq log8_h4_bp 43 _ 2 11 log8_h4_r28_30
    (log8Run_cut log8_h4_pq log8_h4_bp 43 _ 2 9 log8_h4_r30_32
    (log8Run_cut log8_h4_pq log8_h4_bp 43 _ 2 7 log8_h4_r32_34
    (log8Run_cut log8_h4_pq log8_h4_bp 43 _ 2 5 log8_h4_r34_36
    (log8Run_cut log8_h4_pq log8_h4_bp 43 _ 2 3 log8_h4_r36_38
    (log8Run_cut log8_h4_pq log8_h4_bp 43 _ 2 1 log8_h4_r38_40
    (log8_h4_r40_41))))))))))))))))))))

theorem log8_h4_hp : Log8Head true 1 43 log8_h4_pq log8_h4_bp (dySt log8_h4_tp) :=
  Log8Head.mk_ne (by decide) log8_h4_q log8_h4_r log8_h4_wt log8_h4_yt log8_h4_tpt

theorem log8_h4_hm : Log8Head false 1 43 log8_h4_pq log8_h4_bp (dySt log8_h4_tm) :=
  Log8Head.mk_ne (by decide) log8_h4_q log8_h4_r log8_h4_wt log8_h4_yt log8_h4_tmt

theorem log8_g4zp0e0_sq :
    log8SqRun true 1 log8_g4zp0e0_v.1 log8_g4zp0e0_v.2.1 1 (dySt log8_h4_tp) =
      dySt log8_g4zp0e0_s1 := by
  show log8Sq true 1 log8_g4zp0e0_v.1 log8_g4zp0e0_v.2.1 0
      (dySt log8_h4_tp) = _
  rw [log8_g4zp0e0_q0_1]

theorem log8_g4zp0e0_ev :
    Log8Eval true true 1 43 log8_g4zp0e0_v.1 log8_g4zp0e0_v.2.2.2 false log8_g4zp0e0_v.2.1 log8_g4zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g4zp0e0_leaf log8_h4_hp log8_g4zp0e0_sq log8_g4zp0e0_a log8_g4zp0e0_b log8_g4zp0e0_end

theorem log8_g4zp0e1_sq :
    log8SqRun true 1 log8_g4zp0e1_v.1 log8_g4zp0e1_v.2.1 1 (dySt log8_h4_tp) =
      dySt log8_g4zp0e1_s1 := by
  show log8Sq true 1 log8_g4zp0e1_v.1 log8_g4zp0e1_v.2.1 0
      (dySt log8_h4_tp) = _
  rw [log8_g4zp0e1_q0_1]

theorem log8_g4zp0e1_ev :
    Log8Eval true true 1 43 log8_g4zp0e1_v.1 log8_g4zp0e1_v.2.2.2 false log8_g4zp0e1_v.2.1 log8_g4zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g4zp0e1_leaf log8_h4_hp log8_g4zp0e1_sq log8_g4zp0e1_a log8_g4zp0e1_b log8_g4zp0e1_end

theorem log8_g4np0e0_sq :
    log8SqRun true 1 log8_g4np0e0_v.1 log8_g4np0e0_v.2.1 1 (dySt log8_h4_tp) =
      dySt log8_g4np0e0_s1 := by
  show log8Sq true 1 log8_g4np0e0_v.1 log8_g4np0e0_v.2.1 0
      (dySt log8_h4_tp) = _
  rw [log8_g4np0e0_q0_1]

theorem log8_g4np0e0_ev :
    Log8Eval false true 1 43 log8_g4np0e0_v.1 log8_g4np0e0_v.2.2.2 false log8_g4np0e0_v.2.1 log8_g4np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g4np0e0_leaf log8_h4_hp log8_g4np0e0_sq log8_g4np0e0_a log8_g4np0e0_b log8_g4np0e0_end

theorem log8_g4np0e1_sq :
    log8SqRun true 1 log8_g4np0e1_v.1 log8_g4np0e1_v.2.1 1 (dySt log8_h4_tp) =
      dySt log8_g4np0e1_s1 := by
  show log8Sq true 1 log8_g4np0e1_v.1 log8_g4np0e1_v.2.1 0
      (dySt log8_h4_tp) = _
  rw [log8_g4np0e1_q0_1]

theorem log8_g4np0e1_ev :
    Log8Eval false true 1 43 log8_g4np0e1_v.1 log8_g4np0e1_v.2.2.2 false log8_g4np0e1_v.2.1 log8_g4np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g4np0e1_leaf log8_h4_hp log8_g4np0e1_sq log8_g4np0e1_a log8_g4np0e1_b log8_g4np0e1_end

theorem log8_g4zm0e0_sq :
    log8SqRun false 1 log8_g4zm0e0_v.1 log8_g4zm0e0_v.2.1 1 (dySt log8_h4_tm) =
      dySt log8_g4zm0e0_s1 := by
  show log8Sq false 1 log8_g4zm0e0_v.1 log8_g4zm0e0_v.2.1 0
      (dySt log8_h4_tm) = _
  rw [log8_g4zm0e0_q0_1]

theorem log8_g4zm0e0_ev :
    Log8Eval true false 1 43 log8_g4zm0e0_v.1 log8_g4zm0e0_v.2.2.2 false log8_g4zm0e0_v.2.1 log8_g4zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g4zm0e0_leaf log8_h4_hm log8_g4zm0e0_sq log8_g4zm0e0_a log8_g4zm0e0_b log8_g4zm0e0_end

theorem log8_g4zm0e1_sq :
    log8SqRun false 1 log8_g4zm0e1_v.1 log8_g4zm0e1_v.2.1 1 (dySt log8_h4_tm) =
      dySt log8_g4zm0e1_s1 := by
  show log8Sq false 1 log8_g4zm0e1_v.1 log8_g4zm0e1_v.2.1 0
      (dySt log8_h4_tm) = _
  rw [log8_g4zm0e1_q0_1]

theorem log8_g4zm0e1_ev :
    Log8Eval true false 1 43 log8_g4zm0e1_v.1 log8_g4zm0e1_v.2.2.2 false log8_g4zm0e1_v.2.1 log8_g4zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g4zm0e1_leaf log8_h4_hm log8_g4zm0e1_sq log8_g4zm0e1_a log8_g4zm0e1_b log8_g4zm0e1_end

theorem log8_g4nm0e0_sq :
    log8SqRun false 1 log8_g4nm0e0_v.1 log8_g4nm0e0_v.2.1 1 (dySt log8_h4_tm) =
      dySt log8_g4nm0e0_s1 := by
  show log8Sq false 1 log8_g4nm0e0_v.1 log8_g4nm0e0_v.2.1 0
      (dySt log8_h4_tm) = _
  rw [log8_g4nm0e0_q0_1]

theorem log8_g4nm0e0_ev :
    Log8Eval false false 1 43 log8_g4nm0e0_v.1 log8_g4nm0e0_v.2.2.2 false log8_g4nm0e0_v.2.1 log8_g4nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g4nm0e0_leaf log8_h4_hm log8_g4nm0e0_sq log8_g4nm0e0_a log8_g4nm0e0_b log8_g4nm0e0_end

theorem log8_g4nm0e1_sq :
    log8SqRun false 1 log8_g4nm0e1_v.1 log8_g4nm0e1_v.2.1 1 (dySt log8_h4_tm) =
      dySt log8_g4nm0e1_s1 := by
  show log8Sq false 1 log8_g4nm0e1_v.1 log8_g4nm0e1_v.2.1 0
      (dySt log8_h4_tm) = _
  rw [log8_g4nm0e1_q0_1]

theorem log8_g4nm0e1_ev :
    Log8Eval false false 1 43 log8_g4nm0e1_v.1 log8_g4nm0e1_v.2.2.2 false log8_g4nm0e1_v.2.1 log8_g4nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g4nm0e1_leaf log8_h4_hm log8_g4nm0e1_sq log8_g4nm0e1_a log8_g4nm0e1_b log8_g4nm0e1_end

theorem log8_h17_q : ∀ q ∈ log8_h17_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h17_r : log8Run log8_h17_pq log8_h17_bp 22 0 20 (hornerInitL 8 exp8F exp8Phi 22) =
    dySt log8_h17_s20 :=
  log8Run_cut log8_h17_pq log8_h17_bp 22 _ 2 18 log8_h17_r0_2
    (log8Run_cut log8_h17_pq log8_h17_bp 22 _ 2 16 log8_h17_r2_4
    (log8Run_cut log8_h17_pq log8_h17_bp 22 _ 2 14 log8_h17_r4_6
    (log8Run_cut log8_h17_pq log8_h17_bp 22 _ 2 12 log8_h17_r6_8
    (log8Run_cut log8_h17_pq log8_h17_bp 22 _ 2 10 log8_h17_r8_10
    (log8Run_cut log8_h17_pq log8_h17_bp 22 _ 2 8 log8_h17_r10_12
    (log8Run_cut log8_h17_pq log8_h17_bp 22 _ 2 6 log8_h17_r12_14
    (log8Run_cut log8_h17_pq log8_h17_bp 22 _ 2 4 log8_h17_r14_16
    (log8Run_cut log8_h17_pq log8_h17_bp 22 _ 2 2 log8_h17_r16_18
    (log8_h17_r18_20)))))))))

theorem log8_h17_hp : Log8Head true 0 22 log8_h17_pq log8_h17_bp (dySt log8_h17_tp) :=
  Log8Head.mk_ne (by decide) log8_h17_q log8_h17_r log8_h17_wt log8_h17_yt log8_h17_tpt

theorem log8_h17_hm : Log8Head false 0 22 log8_h17_pq log8_h17_bp (dySt log8_h17_tm) :=
  Log8Head.mk_ne (by decide) log8_h17_q log8_h17_r log8_h17_wt log8_h17_yt log8_h17_tmt

theorem log8_g15zp0e0_ev :
    Log8Eval true true 0 22 log8_g15zp0e0_v.1 log8_g15zp0e0_v.2.2.2 false log8_g15zp0e0_v.2.1 log8_g15zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g15zp0e0_leaf log8_h17_hp rfl log8_g15zp0e0_a log8_g15zp0e0_b log8_g15zp0e0_end

theorem log8_g15zp0e1_ev :
    Log8Eval true true 0 22 log8_g15zp0e1_v.1 log8_g15zp0e1_v.2.2.2 false log8_g15zp0e1_v.2.1 log8_g15zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g15zp0e1_leaf log8_h17_hp rfl log8_g15zp0e1_a log8_g15zp0e1_b log8_g15zp0e1_end

theorem log8_g15np0e0_ev :
    Log8Eval false true 0 22 log8_g15np0e0_v.1 log8_g15np0e0_v.2.2.2 false log8_g15np0e0_v.2.1 log8_g15np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g15np0e0_leaf log8_h17_hp rfl log8_g15np0e0_a log8_g15np0e0_b log8_g15np0e0_end

theorem log8_g15np0e1_ev :
    Log8Eval false true 0 22 log8_g15np0e1_v.1 log8_g15np0e1_v.2.2.2 false log8_g15np0e1_v.2.1 log8_g15np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g15np0e1_leaf log8_h17_hp rfl log8_g15np0e1_a log8_g15np0e1_b log8_g15np0e1_end

theorem log8_g15zm0e0_ev :
    Log8Eval true false 0 22 log8_g15zm0e0_v.1 log8_g15zm0e0_v.2.2.2 false log8_g15zm0e0_v.2.1 log8_g15zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g15zm0e0_leaf log8_h17_hm rfl log8_g15zm0e0_a log8_g15zm0e0_b log8_g15zm0e0_end

theorem log8_g15zm0e1_ev :
    Log8Eval true false 0 22 log8_g15zm0e1_v.1 log8_g15zm0e1_v.2.2.2 false log8_g15zm0e1_v.2.1 log8_g15zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g15zm0e1_leaf log8_h17_hm rfl log8_g15zm0e1_a log8_g15zm0e1_b log8_g15zm0e1_end

theorem log8_g15nm0e0_ev :
    Log8Eval false false 0 22 log8_g15nm0e0_v.1 log8_g15nm0e0_v.2.2.2 false log8_g15nm0e0_v.2.1 log8_g15nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g15nm0e0_leaf log8_h17_hm rfl log8_g15nm0e0_a log8_g15nm0e0_b log8_g15nm0e0_end

theorem log8_g15nm0e1_ev :
    Log8Eval false false 0 22 log8_g15nm0e1_v.1 log8_g15nm0e1_v.2.2.2 false log8_g15nm0e1_v.2.1 log8_g15nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g15nm0e1_leaf log8_h17_hm rfl log8_g15nm0e1_a log8_g15nm0e1_b log8_g15nm0e1_end

theorem log8_h23_q : ∀ q ∈ log8_h23_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h23_r : log8Run log8_h23_pq log8_h23_bp 16 0 14 (hornerInitL 8 exp8F exp8Phi 16) =
    dySt log8_h23_s14 :=
  log8Run_cut log8_h23_pq log8_h23_bp 16 _ 2 12 log8_h23_r0_2
    (log8Run_cut log8_h23_pq log8_h23_bp 16 _ 2 10 log8_h23_r2_4
    (log8Run_cut log8_h23_pq log8_h23_bp 16 _ 2 8 log8_h23_r4_6
    (log8Run_cut log8_h23_pq log8_h23_bp 16 _ 2 6 log8_h23_r6_8
    (log8Run_cut log8_h23_pq log8_h23_bp 16 _ 2 4 log8_h23_r8_10
    (log8Run_cut log8_h23_pq log8_h23_bp 16 _ 2 2 log8_h23_r10_12
    (log8_h23_r12_14))))))

theorem log8_h23_hp : Log8Head true 0 16 log8_h23_pq log8_h23_bp (dySt log8_h23_tp) :=
  Log8Head.mk_ne (by decide) log8_h23_q log8_h23_r log8_h23_wt log8_h23_yt log8_h23_tpt

theorem log8_h23_hm : Log8Head false 0 16 log8_h23_pq log8_h23_bp (dySt log8_h23_tm) :=
  Log8Head.mk_ne (by decide) log8_h23_q log8_h23_r log8_h23_wt log8_h23_yt log8_h23_tmt

theorem log8_g21zp0e0_ev :
    Log8Eval true true 0 16 log8_g21zp0e0_v.1 log8_g21zp0e0_v.2.2.2 false log8_g21zp0e0_v.2.1 log8_g21zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g21zp0e0_leaf log8_h23_hp rfl log8_g21zp0e0_a log8_g21zp0e0_b log8_g21zp0e0_end

theorem log8_g21zp0e1_ev :
    Log8Eval true true 0 16 log8_g21zp0e1_v.1 log8_g21zp0e1_v.2.2.2 false log8_g21zp0e1_v.2.1 log8_g21zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g21zp0e1_leaf log8_h23_hp rfl log8_g21zp0e1_a log8_g21zp0e1_b log8_g21zp0e1_end

theorem log8_g21np0e0_ev :
    Log8Eval false true 0 16 log8_g21np0e0_v.1 log8_g21np0e0_v.2.2.2 false log8_g21np0e0_v.2.1 log8_g21np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g21np0e0_leaf log8_h23_hp rfl log8_g21np0e0_a log8_g21np0e0_b log8_g21np0e0_end

theorem log8_g21np0e1_ev :
    Log8Eval false true 0 16 log8_g21np0e1_v.1 log8_g21np0e1_v.2.2.2 false log8_g21np0e1_v.2.1 log8_g21np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g21np0e1_leaf log8_h23_hp rfl log8_g21np0e1_a log8_g21np0e1_b log8_g21np0e1_end

theorem log8_g21zm0e0_ev :
    Log8Eval true false 0 16 log8_g21zm0e0_v.1 log8_g21zm0e0_v.2.2.2 false log8_g21zm0e0_v.2.1 log8_g21zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g21zm0e0_leaf log8_h23_hm rfl log8_g21zm0e0_a log8_g21zm0e0_b log8_g21zm0e0_end

theorem log8_g21zm0e1_ev :
    Log8Eval true false 0 16 log8_g21zm0e1_v.1 log8_g21zm0e1_v.2.2.2 false log8_g21zm0e1_v.2.1 log8_g21zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g21zm0e1_leaf log8_h23_hm rfl log8_g21zm0e1_a log8_g21zm0e1_b log8_g21zm0e1_end

theorem log8_g21nm0e0_ev :
    Log8Eval false false 0 16 log8_g21nm0e0_v.1 log8_g21nm0e0_v.2.2.2 false log8_g21nm0e0_v.2.1 log8_g21nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g21nm0e0_leaf log8_h23_hm rfl log8_g21nm0e0_a log8_g21nm0e0_b log8_g21nm0e0_end

theorem log8_g21nm0e1_ev :
    Log8Eval false false 0 16 log8_g21nm0e1_v.1 log8_g21nm0e1_v.2.2.2 false log8_g21nm0e1_v.2.1 log8_g21nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g21nm0e1_leaf log8_h23_hm rfl log8_g21nm0e1_a log8_g21nm0e1_b log8_g21nm0e1_end

theorem log8_h31_q : ∀ q ∈ log8_h31_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h31_r : log8Run log8_h31_pq log8_h31_bp 10 0 8 (hornerInitL 8 exp8F exp8Phi 10) =
    dySt log8_h31_s8 :=
  log8Run_cut log8_h31_pq log8_h31_bp 10 _ 2 6 log8_h31_r0_2
    (log8Run_cut log8_h31_pq log8_h31_bp 10 _ 2 4 log8_h31_r2_4
    (log8Run_cut log8_h31_pq log8_h31_bp 10 _ 2 2 log8_h31_r4_6
    (log8_h31_r6_8)))

theorem log8_h31_hp : Log8Head true 0 10 log8_h31_pq log8_h31_bp (dySt log8_h31_tp) :=
  Log8Head.mk_ne (by decide) log8_h31_q log8_h31_r log8_h31_wt log8_h31_yt log8_h31_tpt

theorem log8_h31_hm : Log8Head false 0 10 log8_h31_pq log8_h31_bp (dySt log8_h31_tm) :=
  Log8Head.mk_ne (by decide) log8_h31_q log8_h31_r log8_h31_wt log8_h31_yt log8_h31_tmt

theorem log8_h32_q : ∀ q ∈ log8_h32_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h32_r : log8Run log8_h32_pq log8_h32_bp 10 0 8 (hornerInitL 8 exp8F exp8Phi 10) =
    dySt log8_h32_s8 :=
  log8Run_cut log8_h32_pq log8_h32_bp 10 _ 2 6 log8_h32_r0_2
    (log8Run_cut log8_h32_pq log8_h32_bp 10 _ 2 4 log8_h32_r2_4
    (log8Run_cut log8_h32_pq log8_h32_bp 10 _ 2 2 log8_h32_r4_6
    (log8_h32_r6_8)))

theorem log8_h32_hp : Log8Head true 0 10 log8_h32_pq log8_h32_bp (dySt log8_h32_tp) :=
  Log8Head.mk_ne (by decide) log8_h32_q log8_h32_r log8_h32_wt log8_h32_yt log8_h32_tpt

theorem log8_h32_hm : Log8Head false 0 10 log8_h32_pq log8_h32_bp (dySt log8_h32_tm) :=
  Log8Head.mk_ne (by decide) log8_h32_q log8_h32_r log8_h32_wt log8_h32_yt log8_h32_tmt

theorem log8_h33_q : ∀ q ∈ log8_h33_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h33_r : log8Run log8_h33_pq log8_h33_bp 10 0 8 (hornerInitL 8 exp8F exp8Phi 10) =
    dySt log8_h33_s8 :=
  log8Run_cut log8_h33_pq log8_h33_bp 10 _ 2 6 log8_h33_r0_2
    (log8Run_cut log8_h33_pq log8_h33_bp 10 _ 2 4 log8_h33_r2_4
    (log8Run_cut log8_h33_pq log8_h33_bp 10 _ 2 2 log8_h33_r4_6
    (log8_h33_r6_8)))

theorem log8_h33_hp : Log8Head true 0 10 log8_h33_pq log8_h33_bp (dySt log8_h33_tp) :=
  Log8Head.mk_ne (by decide) log8_h33_q log8_h33_r log8_h33_wt log8_h33_yt log8_h33_tpt

theorem log8_h33_hm : Log8Head false 0 10 log8_h33_pq log8_h33_bp (dySt log8_h33_tm) :=
  Log8Head.mk_ne (by decide) log8_h33_q log8_h33_r log8_h33_wt log8_h33_yt log8_h33_tmt

theorem log8_g27zp0e0_ev :
    Log8Eval true true 0 10 log8_g27zp0e0_v.1 log8_g27zp0e0_v.2.2.2 false log8_g27zp0e0_v.2.1 log8_g27zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g27zp0e0_leaf log8_h33_hp rfl log8_g27zp0e0_a log8_g27zp0e0_b log8_g27zp0e0_end

theorem log8_g27zp0e1_ev :
    Log8Eval true true 0 10 log8_g27zp0e1_v.1 log8_g27zp0e1_v.2.2.2 false log8_g27zp0e1_v.2.1 log8_g27zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g27zp0e1_leaf log8_h32_hp rfl log8_g27zp0e1_a log8_g27zp0e1_b log8_g27zp0e1_end

theorem log8_g27np0e0_ev :
    Log8Eval false true 0 10 log8_g27np0e0_v.1 log8_g27np0e0_v.2.2.2 false log8_g27np0e0_v.2.1 log8_g27np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g27np0e0_leaf log8_h31_hp rfl log8_g27np0e0_a log8_g27np0e0_b log8_g27np0e0_end

theorem log8_g27np0e1_ev :
    Log8Eval false true 0 10 log8_g27np0e1_v.1 log8_g27np0e1_v.2.2.2 false log8_g27np0e1_v.2.1 log8_g27np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g27np0e1_leaf log8_h31_hp rfl log8_g27np0e1_a log8_g27np0e1_b log8_g27np0e1_end

theorem log8_g27zm0e0_ev :
    Log8Eval true false 0 10 log8_g27zm0e0_v.1 log8_g27zm0e0_v.2.2.2 false log8_g27zm0e0_v.2.1 log8_g27zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g27zm0e0_leaf log8_h33_hm rfl log8_g27zm0e0_a log8_g27zm0e0_b log8_g27zm0e0_end

theorem log8_g27zm0e1_ev :
    Log8Eval true false 0 10 log8_g27zm0e1_v.1 log8_g27zm0e1_v.2.2.2 false log8_g27zm0e1_v.2.1 log8_g27zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g27zm0e1_leaf log8_h32_hm rfl log8_g27zm0e1_a log8_g27zm0e1_b log8_g27zm0e1_end

theorem log8_g27nm0e0_ev :
    Log8Eval false false 0 10 log8_g27nm0e0_v.1 log8_g27nm0e0_v.2.2.2 false log8_g27nm0e0_v.2.1 log8_g27nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g27nm0e0_leaf log8_h31_hm rfl log8_g27nm0e0_a log8_g27nm0e0_b log8_g27nm0e0_end

theorem log8_g27nm0e1_ev :
    Log8Eval false false 0 10 log8_g27nm0e1_v.1 log8_g27nm0e1_v.2.2.2 false log8_g27nm0e1_v.2.1 log8_g27nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g27nm0e1_leaf log8_h31_hm rfl log8_g27nm0e1_a log8_g27nm0e1_b log8_g27nm0e1_end

theorem log8_h53_q : ∀ q ∈ log8_h53_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h53_r : log8Run log8_h53_pq log8_h53_bp 2 0 0 (hornerInitL 8 exp8F exp8Phi 2) =
    (hornerInitL 8 exp8F exp8Phi 2) := rfl

theorem log8_h53_hp : Log8Head true 0 2 log8_h53_pq log8_h53_bp (dySt log8_h53_tp) :=
  Log8Head.mk_ne (by decide) log8_h53_q log8_h53_r log8_h53_wt log8_h53_yt log8_h53_tpt

theorem log8_h53_hm : Log8Head false 0 2 log8_h53_pq log8_h53_bp (dySt log8_h53_tm) :=
  Log8Head.mk_ne (by decide) log8_h53_q log8_h53_r log8_h53_wt log8_h53_yt log8_h53_tmt

theorem log8_h54_q : ∀ q ∈ log8_h54_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h54_r : log8Run log8_h54_pq log8_h54_bp 2 0 0 (hornerInitL 8 exp8F exp8Phi 2) =
    (hornerInitL 8 exp8F exp8Phi 2) := rfl

theorem log8_h54_hp : Log8Head true 0 2 log8_h54_pq log8_h54_bp (dySt log8_h54_tp) :=
  Log8Head.mk_ne (by decide) log8_h54_q log8_h54_r log8_h54_wt log8_h54_yt log8_h54_tpt

theorem log8_h54_hm : Log8Head false 0 2 log8_h54_pq log8_h54_bp (dySt log8_h54_tm) :=
  Log8Head.mk_ne (by decide) log8_h54_q log8_h54_r log8_h54_wt log8_h54_yt log8_h54_tmt

theorem log8_g35zp0e0_ev :
    Log8Eval true true 0 2 log8_g35zp0e0_v.1 log8_g35zp0e0_v.2.2.2 true log8_g35zp0e0_v.2.1 log8_g35zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g35zp0e0_leaf log8_h54_hp rfl log8_g35zp0e0_a log8_g35zp0e0_b log8_g35zp0e0_end

theorem log8_g35zp0e1_ev :
    Log8Eval true true 0 2 log8_g35zp0e1_v.1 log8_g35zp0e1_v.2.2.2 true log8_g35zp0e1_v.2.1 log8_g35zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g35zp0e1_leaf log8_h54_hp rfl log8_g35zp0e1_a log8_g35zp0e1_b log8_g35zp0e1_end

theorem log8_g35np0e0_ev :
    Log8Eval false true 0 2 log8_g35np0e0_v.1 log8_g35np0e0_v.2.2.2 false log8_g35np0e0_v.2.1 log8_g35np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g35np0e0_leaf log8_h53_hp rfl log8_g35np0e0_a log8_g35np0e0_b log8_g35np0e0_end

theorem log8_g35np0e1_ev :
    Log8Eval false true 0 2 log8_g35np0e1_v.1 log8_g35np0e1_v.2.2.2 false log8_g35np0e1_v.2.1 log8_g35np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g35np0e1_leaf log8_h53_hp rfl log8_g35np0e1_a log8_g35np0e1_b log8_g35np0e1_end

theorem log8_g35zm0e0_ev :
    Log8Eval true false 0 2 log8_g35zm0e0_v.1 log8_g35zm0e0_v.2.2.2 true log8_g35zm0e0_v.2.1 log8_g35zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g35zm0e0_leaf log8_h54_hm rfl log8_g35zm0e0_a log8_g35zm0e0_b log8_g35zm0e0_end

theorem log8_g35zm0e1_ev :
    Log8Eval true false 0 2 log8_g35zm0e1_v.1 log8_g35zm0e1_v.2.2.2 true log8_g35zm0e1_v.2.1 log8_g35zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g35zm0e1_leaf log8_h54_hm rfl log8_g35zm0e1_a log8_g35zm0e1_b log8_g35zm0e1_end

theorem log8_g35nm0e0_ev :
    Log8Eval false false 0 2 log8_g35nm0e0_v.1 log8_g35nm0e0_v.2.2.2 false log8_g35nm0e0_v.2.1 log8_g35nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g35nm0e0_leaf log8_h53_hm rfl log8_g35nm0e0_a log8_g35nm0e0_b log8_g35nm0e0_end

theorem log8_g35nm0e1_ev :
    Log8Eval false false 0 2 log8_g35nm0e1_v.1 log8_g35nm0e1_v.2.2.2 false log8_g35nm0e1_v.2.1 log8_g35nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g35nm0e1_leaf log8_h53_hm rfl log8_g35nm0e1_a log8_g35nm0e1_b log8_g35nm0e1_end

theorem log8_h8_q : ∀ q ∈ log8_h8_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h8_r : log8Run log8_h8_pq log8_h8_bp 40 0 38 (hornerInitL 8 exp8F exp8Phi 40) =
    dySt log8_h8_s38 :=
  log8Run_cut log8_h8_pq log8_h8_bp 40 _ 2 36 log8_h8_r0_2
    (log8Run_cut log8_h8_pq log8_h8_bp 40 _ 2 34 log8_h8_r2_4
    (log8Run_cut log8_h8_pq log8_h8_bp 40 _ 2 32 log8_h8_r4_6
    (log8Run_cut log8_h8_pq log8_h8_bp 40 _ 2 30 log8_h8_r6_8
    (log8Run_cut log8_h8_pq log8_h8_bp 40 _ 2 28 log8_h8_r8_10
    (log8Run_cut log8_h8_pq log8_h8_bp 40 _ 2 26 log8_h8_r10_12
    (log8Run_cut log8_h8_pq log8_h8_bp 40 _ 2 24 log8_h8_r12_14
    (log8Run_cut log8_h8_pq log8_h8_bp 40 _ 2 22 log8_h8_r14_16
    (log8Run_cut log8_h8_pq log8_h8_bp 40 _ 2 20 log8_h8_r16_18
    (log8Run_cut log8_h8_pq log8_h8_bp 40 _ 2 18 log8_h8_r18_20
    (log8Run_cut log8_h8_pq log8_h8_bp 40 _ 2 16 log8_h8_r20_22
    (log8Run_cut log8_h8_pq log8_h8_bp 40 _ 2 14 log8_h8_r22_24
    (log8Run_cut log8_h8_pq log8_h8_bp 40 _ 2 12 log8_h8_r24_26
    (log8Run_cut log8_h8_pq log8_h8_bp 40 _ 2 10 log8_h8_r26_28
    (log8Run_cut log8_h8_pq log8_h8_bp 40 _ 2 8 log8_h8_r28_30
    (log8Run_cut log8_h8_pq log8_h8_bp 40 _ 2 6 log8_h8_r30_32
    (log8Run_cut log8_h8_pq log8_h8_bp 40 _ 2 4 log8_h8_r32_34
    (log8Run_cut log8_h8_pq log8_h8_bp 40 _ 2 2 log8_h8_r34_36
    (log8_h8_r36_38))))))))))))))))))

theorem log8_h8_hp : Log8Head true 0 40 log8_h8_pq log8_h8_bp (dySt log8_h8_tp) :=
  Log8Head.mk_ne (by decide) log8_h8_q log8_h8_r log8_h8_wt log8_h8_yt log8_h8_tpt

theorem log8_h8_hm : Log8Head false 0 40 log8_h8_pq log8_h8_bp (dySt log8_h8_tm) :=
  Log8Head.mk_ne (by decide) log8_h8_q log8_h8_r log8_h8_wt log8_h8_yt log8_h8_tmt

theorem log8_g6zp0e0_ev :
    Log8Eval true true 0 40 log8_g6zp0e0_v.1 log8_g6zp0e0_v.2.2.2 false log8_g6zp0e0_v.2.1 log8_g6zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g6zp0e0_leaf log8_h8_hp rfl log8_g6zp0e0_a log8_g6zp0e0_b log8_g6zp0e0_end

theorem log8_g6zp0e1_ev :
    Log8Eval true true 0 40 log8_g6zp0e1_v.1 log8_g6zp0e1_v.2.2.2 false log8_g6zp0e1_v.2.1 log8_g6zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g6zp0e1_leaf log8_h8_hp rfl log8_g6zp0e1_a log8_g6zp0e1_b log8_g6zp0e1_end

theorem log8_g6np0e0_ev :
    Log8Eval false true 0 40 log8_g6np0e0_v.1 log8_g6np0e0_v.2.2.2 false log8_g6np0e0_v.2.1 log8_g6np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g6np0e0_leaf log8_h8_hp rfl log8_g6np0e0_a log8_g6np0e0_b log8_g6np0e0_end

theorem log8_g6np0e1_ev :
    Log8Eval false true 0 40 log8_g6np0e1_v.1 log8_g6np0e1_v.2.2.2 false log8_g6np0e1_v.2.1 log8_g6np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g6np0e1_leaf log8_h8_hp rfl log8_g6np0e1_a log8_g6np0e1_b log8_g6np0e1_end

theorem log8_g6zm0e0_ev :
    Log8Eval true false 0 40 log8_g6zm0e0_v.1 log8_g6zm0e0_v.2.2.2 false log8_g6zm0e0_v.2.1 log8_g6zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g6zm0e0_leaf log8_h8_hm rfl log8_g6zm0e0_a log8_g6zm0e0_b log8_g6zm0e0_end

theorem log8_g6zm0e1_ev :
    Log8Eval true false 0 40 log8_g6zm0e1_v.1 log8_g6zm0e1_v.2.2.2 false log8_g6zm0e1_v.2.1 log8_g6zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g6zm0e1_leaf log8_h8_hm rfl log8_g6zm0e1_a log8_g6zm0e1_b log8_g6zm0e1_end

theorem log8_g6nm0e0_ev :
    Log8Eval false false 0 40 log8_g6nm0e0_v.1 log8_g6nm0e0_v.2.2.2 false log8_g6nm0e0_v.2.1 log8_g6nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g6nm0e0_leaf log8_h8_hm rfl log8_g6nm0e0_a log8_g6nm0e0_b log8_g6nm0e0_end

theorem log8_g6nm0e1_ev :
    Log8Eval false false 0 40 log8_g6nm0e1_v.1 log8_g6nm0e1_v.2.2.2 false log8_g6nm0e1_v.2.1 log8_g6nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g6nm0e1_leaf log8_h8_hm rfl log8_g6nm0e1_a log8_g6nm0e1_b log8_g6nm0e1_end

theorem log8_h12_q : ∀ q ∈ log8_h12_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h12_r : log8Run log8_h12_pq log8_h12_bp 30 0 28 (hornerInitL 8 exp8F exp8Phi 30) =
    dySt log8_h12_s28 :=
  log8Run_cut log8_h12_pq log8_h12_bp 30 _ 2 26 log8_h12_r0_2
    (log8Run_cut log8_h12_pq log8_h12_bp 30 _ 2 24 log8_h12_r2_4
    (log8Run_cut log8_h12_pq log8_h12_bp 30 _ 2 22 log8_h12_r4_6
    (log8Run_cut log8_h12_pq log8_h12_bp 30 _ 2 20 log8_h12_r6_8
    (log8Run_cut log8_h12_pq log8_h12_bp 30 _ 2 18 log8_h12_r8_10
    (log8Run_cut log8_h12_pq log8_h12_bp 30 _ 2 16 log8_h12_r10_12
    (log8Run_cut log8_h12_pq log8_h12_bp 30 _ 2 14 log8_h12_r12_14
    (log8Run_cut log8_h12_pq log8_h12_bp 30 _ 2 12 log8_h12_r14_16
    (log8Run_cut log8_h12_pq log8_h12_bp 30 _ 2 10 log8_h12_r16_18
    (log8Run_cut log8_h12_pq log8_h12_bp 30 _ 2 8 log8_h12_r18_20
    (log8Run_cut log8_h12_pq log8_h12_bp 30 _ 2 6 log8_h12_r20_22
    (log8Run_cut log8_h12_pq log8_h12_bp 30 _ 2 4 log8_h12_r22_24
    (log8Run_cut log8_h12_pq log8_h12_bp 30 _ 2 2 log8_h12_r24_26
    (log8_h12_r26_28)))))))))))))

theorem log8_h12_hp : Log8Head true 0 30 log8_h12_pq log8_h12_bp (dySt log8_h12_tp) :=
  Log8Head.mk_ne (by decide) log8_h12_q log8_h12_r log8_h12_wt log8_h12_yt log8_h12_tpt

theorem log8_h12_hm : Log8Head false 0 30 log8_h12_pq log8_h12_bp (dySt log8_h12_tm) :=
  Log8Head.mk_ne (by decide) log8_h12_q log8_h12_r log8_h12_wt log8_h12_yt log8_h12_tmt

theorem log8_g10zp0e0_ev :
    Log8Eval true true 0 30 log8_g10zp0e0_v.1 log8_g10zp0e0_v.2.2.2 false log8_g10zp0e0_v.2.1 log8_g10zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g10zp0e0_leaf log8_h12_hp rfl log8_g10zp0e0_a log8_g10zp0e0_b log8_g10zp0e0_end

theorem log8_g10zp0e1_ev :
    Log8Eval true true 0 30 log8_g10zp0e1_v.1 log8_g10zp0e1_v.2.2.2 false log8_g10zp0e1_v.2.1 log8_g10zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g10zp0e1_leaf log8_h12_hp rfl log8_g10zp0e1_a log8_g10zp0e1_b log8_g10zp0e1_end

theorem log8_g10np0e0_ev :
    Log8Eval false true 0 30 log8_g10np0e0_v.1 log8_g10np0e0_v.2.2.2 false log8_g10np0e0_v.2.1 log8_g10np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g10np0e0_leaf log8_h12_hp rfl log8_g10np0e0_a log8_g10np0e0_b log8_g10np0e0_end

theorem log8_g10np0e1_ev :
    Log8Eval false true 0 30 log8_g10np0e1_v.1 log8_g10np0e1_v.2.2.2 false log8_g10np0e1_v.2.1 log8_g10np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g10np0e1_leaf log8_h12_hp rfl log8_g10np0e1_a log8_g10np0e1_b log8_g10np0e1_end

theorem log8_g10zm0e0_ev :
    Log8Eval true false 0 30 log8_g10zm0e0_v.1 log8_g10zm0e0_v.2.2.2 false log8_g10zm0e0_v.2.1 log8_g10zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g10zm0e0_leaf log8_h12_hm rfl log8_g10zm0e0_a log8_g10zm0e0_b log8_g10zm0e0_end

theorem log8_g10zm0e1_ev :
    Log8Eval true false 0 30 log8_g10zm0e1_v.1 log8_g10zm0e1_v.2.2.2 false log8_g10zm0e1_v.2.1 log8_g10zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g10zm0e1_leaf log8_h12_hm rfl log8_g10zm0e1_a log8_g10zm0e1_b log8_g10zm0e1_end

theorem log8_g10nm0e0_ev :
    Log8Eval false false 0 30 log8_g10nm0e0_v.1 log8_g10nm0e0_v.2.2.2 false log8_g10nm0e0_v.2.1 log8_g10nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g10nm0e0_leaf log8_h12_hm rfl log8_g10nm0e0_a log8_g10nm0e0_b log8_g10nm0e0_end

theorem log8_g10nm0e1_ev :
    Log8Eval false false 0 30 log8_g10nm0e1_v.1 log8_g10nm0e1_v.2.2.2 false log8_g10nm0e1_v.2.1 log8_g10nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g10nm0e1_leaf log8_h12_hm rfl log8_g10nm0e1_a log8_g10nm0e1_b log8_g10nm0e1_end

theorem log8_h16_q : ∀ q ∈ log8_h16_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h16_r : log8Run log8_h16_pq log8_h16_bp 23 0 21 (hornerInitL 8 exp8F exp8Phi 23) =
    dySt log8_h16_s21 :=
  log8Run_cut log8_h16_pq log8_h16_bp 23 _ 2 19 log8_h16_r0_2
    (log8Run_cut log8_h16_pq log8_h16_bp 23 _ 2 17 log8_h16_r2_4
    (log8Run_cut log8_h16_pq log8_h16_bp 23 _ 2 15 log8_h16_r4_6
    (log8Run_cut log8_h16_pq log8_h16_bp 23 _ 2 13 log8_h16_r6_8
    (log8Run_cut log8_h16_pq log8_h16_bp 23 _ 2 11 log8_h16_r8_10
    (log8Run_cut log8_h16_pq log8_h16_bp 23 _ 2 9 log8_h16_r10_12
    (log8Run_cut log8_h16_pq log8_h16_bp 23 _ 2 7 log8_h16_r12_14
    (log8Run_cut log8_h16_pq log8_h16_bp 23 _ 2 5 log8_h16_r14_16
    (log8Run_cut log8_h16_pq log8_h16_bp 23 _ 2 3 log8_h16_r16_18
    (log8Run_cut log8_h16_pq log8_h16_bp 23 _ 2 1 log8_h16_r18_20
    (log8_h16_r20_21))))))))))

theorem log8_h16_hp : Log8Head true 0 23 log8_h16_pq log8_h16_bp (dySt log8_h16_tp) :=
  Log8Head.mk_ne (by decide) log8_h16_q log8_h16_r log8_h16_wt log8_h16_yt log8_h16_tpt

theorem log8_h16_hm : Log8Head false 0 23 log8_h16_pq log8_h16_bp (dySt log8_h16_tm) :=
  Log8Head.mk_ne (by decide) log8_h16_q log8_h16_r log8_h16_wt log8_h16_yt log8_h16_tmt

theorem log8_g14zp0e0_ev :
    Log8Eval true true 0 23 log8_g14zp0e0_v.1 log8_g14zp0e0_v.2.2.2 false log8_g14zp0e0_v.2.1 log8_g14zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g14zp0e0_leaf log8_h16_hp rfl log8_g14zp0e0_a log8_g14zp0e0_b log8_g14zp0e0_end

theorem log8_g14zp0e1_ev :
    Log8Eval true true 0 23 log8_g14zp0e1_v.1 log8_g14zp0e1_v.2.2.2 false log8_g14zp0e1_v.2.1 log8_g14zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g14zp0e1_leaf log8_h16_hp rfl log8_g14zp0e1_a log8_g14zp0e1_b log8_g14zp0e1_end

theorem log8_g14np0e0_ev :
    Log8Eval false true 0 23 log8_g14np0e0_v.1 log8_g14np0e0_v.2.2.2 false log8_g14np0e0_v.2.1 log8_g14np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g14np0e0_leaf log8_h16_hp rfl log8_g14np0e0_a log8_g14np0e0_b log8_g14np0e0_end

theorem log8_g14np0e1_ev :
    Log8Eval false true 0 23 log8_g14np0e1_v.1 log8_g14np0e1_v.2.2.2 false log8_g14np0e1_v.2.1 log8_g14np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g14np0e1_leaf log8_h16_hp rfl log8_g14np0e1_a log8_g14np0e1_b log8_g14np0e1_end

theorem log8_g14zm0e0_ev :
    Log8Eval true false 0 23 log8_g14zm0e0_v.1 log8_g14zm0e0_v.2.2.2 false log8_g14zm0e0_v.2.1 log8_g14zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g14zm0e0_leaf log8_h16_hm rfl log8_g14zm0e0_a log8_g14zm0e0_b log8_g14zm0e0_end

theorem log8_g14zm0e1_ev :
    Log8Eval true false 0 23 log8_g14zm0e1_v.1 log8_g14zm0e1_v.2.2.2 false log8_g14zm0e1_v.2.1 log8_g14zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g14zm0e1_leaf log8_h16_hm rfl log8_g14zm0e1_a log8_g14zm0e1_b log8_g14zm0e1_end

theorem log8_g14nm0e0_ev :
    Log8Eval false false 0 23 log8_g14nm0e0_v.1 log8_g14nm0e0_v.2.2.2 false log8_g14nm0e0_v.2.1 log8_g14nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g14nm0e0_leaf log8_h16_hm rfl log8_g14nm0e0_a log8_g14nm0e0_b log8_g14nm0e0_end

theorem log8_g14nm0e1_ev :
    Log8Eval false false 0 23 log8_g14nm0e1_v.1 log8_g14nm0e1_v.2.2.2 false log8_g14nm0e1_v.2.1 log8_g14nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g14nm0e1_leaf log8_h16_hm rfl log8_g14nm0e1_a log8_g14nm0e1_b log8_g14nm0e1_end

theorem log8_h43_q : ∀ q ∈ log8_h43_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h43_r : log8Run log8_h43_pq log8_h43_bp 6 0 4 (hornerInitL 8 exp8F exp8Phi 6) =
    dySt log8_h43_s4 :=
  log8Run_cut log8_h43_pq log8_h43_bp 6 _ 2 2 log8_h43_r0_2
    (log8_h43_r2_4)

theorem log8_h43_hp : Log8Head true 0 6 log8_h43_pq log8_h43_bp (dySt log8_h43_tp) :=
  Log8Head.mk_ne (by decide) log8_h43_q log8_h43_r log8_h43_wt log8_h43_yt log8_h43_tpt

theorem log8_h43_hm : Log8Head false 0 6 log8_h43_pq log8_h43_bp (dySt log8_h43_tm) :=
  Log8Head.mk_ne (by decide) log8_h43_q log8_h43_r log8_h43_wt log8_h43_yt log8_h43_tmt

theorem log8_h44_q : ∀ q ∈ log8_h44_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h44_r : log8Run log8_h44_pq log8_h44_bp 6 0 4 (hornerInitL 8 exp8F exp8Phi 6) =
    dySt log8_h44_s4 :=
  log8Run_cut log8_h44_pq log8_h44_bp 6 _ 2 2 log8_h44_r0_2
    (log8_h44_r2_4)

theorem log8_h44_hp : Log8Head true 0 6 log8_h44_pq log8_h44_bp (dySt log8_h44_tp) :=
  Log8Head.mk_ne (by decide) log8_h44_q log8_h44_r log8_h44_wt log8_h44_yt log8_h44_tpt

theorem log8_h44_hm : Log8Head false 0 6 log8_h44_pq log8_h44_bp (dySt log8_h44_tm) :=
  Log8Head.mk_ne (by decide) log8_h44_q log8_h44_r log8_h44_wt log8_h44_yt log8_h44_tmt

theorem log8_h45_q : ∀ q ∈ log8_h45_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h45_r : log8Run log8_h45_pq log8_h45_bp 6 0 4 (hornerInitL 8 exp8F exp8Phi 6) =
    dySt log8_h45_s4 :=
  log8Run_cut log8_h45_pq log8_h45_bp 6 _ 2 2 log8_h45_r0_2
    (log8_h45_r2_4)

theorem log8_h45_hp : Log8Head true 0 6 log8_h45_pq log8_h45_bp (dySt log8_h45_tp) :=
  Log8Head.mk_ne (by decide) log8_h45_q log8_h45_r log8_h45_wt log8_h45_yt log8_h45_tpt

theorem log8_h45_hm : Log8Head false 0 6 log8_h45_pq log8_h45_bp (dySt log8_h45_tm) :=
  Log8Head.mk_ne (by decide) log8_h45_q log8_h45_r log8_h45_wt log8_h45_yt log8_h45_tmt

theorem log8_g31zp0e0_ev :
    Log8Eval true true 0 6 log8_g31zp0e0_v.1 log8_g31zp0e0_v.2.2.2 true log8_g31zp0e0_v.2.1 log8_g31zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g31zp0e0_leaf log8_h45_hp rfl log8_g31zp0e0_a log8_g31zp0e0_b log8_g31zp0e0_end

theorem log8_g31zp0e1_ev :
    Log8Eval true true 0 6 log8_g31zp0e1_v.1 log8_g31zp0e1_v.2.2.2 true log8_g31zp0e1_v.2.1 log8_g31zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g31zp0e1_leaf log8_h44_hp rfl log8_g31zp0e1_a log8_g31zp0e1_b log8_g31zp0e1_end

theorem log8_g31np0e0_ev :
    Log8Eval false true 0 6 log8_g31np0e0_v.1 log8_g31np0e0_v.2.2.2 false log8_g31np0e0_v.2.1 log8_g31np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g31np0e0_leaf log8_h43_hp rfl log8_g31np0e0_a log8_g31np0e0_b log8_g31np0e0_end

theorem log8_g31np0e1_ev :
    Log8Eval false true 0 6 log8_g31np0e1_v.1 log8_g31np0e1_v.2.2.2 false log8_g31np0e1_v.2.1 log8_g31np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g31np0e1_leaf log8_h43_hp rfl log8_g31np0e1_a log8_g31np0e1_b log8_g31np0e1_end

theorem log8_g31zm0e0_ev :
    Log8Eval true false 0 6 log8_g31zm0e0_v.1 log8_g31zm0e0_v.2.2.2 true log8_g31zm0e0_v.2.1 log8_g31zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g31zm0e0_leaf log8_h45_hm rfl log8_g31zm0e0_a log8_g31zm0e0_b log8_g31zm0e0_end

theorem log8_g31zm0e1_ev :
    Log8Eval true false 0 6 log8_g31zm0e1_v.1 log8_g31zm0e1_v.2.2.2 true log8_g31zm0e1_v.2.1 log8_g31zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g31zm0e1_leaf log8_h44_hm rfl log8_g31zm0e1_a log8_g31zm0e1_b log8_g31zm0e1_end

theorem log8_g31nm0e0_ev :
    Log8Eval false false 0 6 log8_g31nm0e0_v.1 log8_g31nm0e0_v.2.2.2 false log8_g31nm0e0_v.2.1 log8_g31nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g31nm0e0_leaf log8_h43_hm rfl log8_g31nm0e0_a log8_g31nm0e0_b log8_g31nm0e0_end

theorem log8_g31nm0e1_ev :
    Log8Eval false false 0 6 log8_g31nm0e1_v.1 log8_g31nm0e1_v.2.2.2 false log8_g31nm0e1_v.2.1 log8_g31nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g31nm0e1_leaf log8_h43_hm rfl log8_g31nm0e1_a log8_g31nm0e1_b log8_g31nm0e1_end

theorem log8_h51_q : ∀ q ∈ log8_h51_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h51_r : log8Run log8_h51_pq log8_h51_bp 3 0 1 (hornerInitL 8 exp8F exp8Phi 3) =
    dySt log8_h51_s1 :=
  log8_h51_r0_1

theorem log8_h51_hp : Log8Head true 0 3 log8_h51_pq log8_h51_bp (dySt log8_h51_tp) :=
  Log8Head.mk_ne (by decide) log8_h51_q log8_h51_r log8_h51_wt log8_h51_yt log8_h51_tpt

theorem log8_h51_hm : Log8Head false 0 3 log8_h51_pq log8_h51_bp (dySt log8_h51_tm) :=
  Log8Head.mk_ne (by decide) log8_h51_q log8_h51_r log8_h51_wt log8_h51_yt log8_h51_tmt

theorem log8_h52_q : ∀ q ∈ log8_h52_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h52_r : log8Run log8_h52_pq log8_h52_bp 3 0 1 (hornerInitL 8 exp8F exp8Phi 3) =
    dySt log8_h52_s1 :=
  log8_h52_r0_1

theorem log8_h52_hp : Log8Head true 0 3 log8_h52_pq log8_h52_bp (dySt log8_h52_tp) :=
  Log8Head.mk_ne (by decide) log8_h52_q log8_h52_r log8_h52_wt log8_h52_yt log8_h52_tpt

theorem log8_h52_hm : Log8Head false 0 3 log8_h52_pq log8_h52_bp (dySt log8_h52_tm) :=
  Log8Head.mk_ne (by decide) log8_h52_q log8_h52_r log8_h52_wt log8_h52_yt log8_h52_tmt

theorem log8_g34zp0e0_ev :
    Log8Eval true true 0 3 log8_g34zp0e0_v.1 log8_g34zp0e0_v.2.2.2 true log8_g34zp0e0_v.2.1 log8_g34zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g34zp0e0_leaf log8_h52_hp rfl log8_g34zp0e0_a log8_g34zp0e0_b log8_g34zp0e0_end

theorem log8_g34zp0e1_ev :
    Log8Eval true true 0 3 log8_g34zp0e1_v.1 log8_g34zp0e1_v.2.2.2 true log8_g34zp0e1_v.2.1 log8_g34zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g34zp0e1_leaf log8_h52_hp rfl log8_g34zp0e1_a log8_g34zp0e1_b log8_g34zp0e1_end

theorem log8_g34np0e0_ev :
    Log8Eval false true 0 3 log8_g34np0e0_v.1 log8_g34np0e0_v.2.2.2 false log8_g34np0e0_v.2.1 log8_g34np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g34np0e0_leaf log8_h51_hp rfl log8_g34np0e0_a log8_g34np0e0_b log8_g34np0e0_end

theorem log8_g34np0e1_ev :
    Log8Eval false true 0 3 log8_g34np0e1_v.1 log8_g34np0e1_v.2.2.2 false log8_g34np0e1_v.2.1 log8_g34np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g34np0e1_leaf log8_h51_hp rfl log8_g34np0e1_a log8_g34np0e1_b log8_g34np0e1_end

theorem log8_g34zm0e0_ev :
    Log8Eval true false 0 3 log8_g34zm0e0_v.1 log8_g34zm0e0_v.2.2.2 true log8_g34zm0e0_v.2.1 log8_g34zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g34zm0e0_leaf log8_h52_hm rfl log8_g34zm0e0_a log8_g34zm0e0_b log8_g34zm0e0_end

theorem log8_g34zm0e1_ev :
    Log8Eval true false 0 3 log8_g34zm0e1_v.1 log8_g34zm0e1_v.2.2.2 true log8_g34zm0e1_v.2.1 log8_g34zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g34zm0e1_leaf log8_h52_hm rfl log8_g34zm0e1_a log8_g34zm0e1_b log8_g34zm0e1_end

theorem log8_g34nm0e0_ev :
    Log8Eval false false 0 3 log8_g34nm0e0_v.1 log8_g34nm0e0_v.2.2.2 false log8_g34nm0e0_v.2.1 log8_g34nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g34nm0e0_leaf log8_h51_hm rfl log8_g34nm0e0_a log8_g34nm0e0_b log8_g34nm0e0_end

theorem log8_g34nm0e1_ev :
    Log8Eval false false 0 3 log8_g34nm0e1_v.1 log8_g34nm0e1_v.2.2.2 false log8_g34nm0e1_v.2.1 log8_g34nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g34nm0e1_leaf log8_h51_hm rfl log8_g34nm0e1_a log8_g34nm0e1_b log8_g34nm0e1_end

theorem log8_h9_q : ∀ q ∈ log8_h9_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h9_r : log8Run log8_h9_pq log8_h9_bp 37 0 35 (hornerInitL 8 exp8F exp8Phi 37) =
    dySt log8_h9_s35 :=
  log8Run_cut log8_h9_pq log8_h9_bp 37 _ 2 33 log8_h9_r0_2
    (log8Run_cut log8_h9_pq log8_h9_bp 37 _ 2 31 log8_h9_r2_4
    (log8Run_cut log8_h9_pq log8_h9_bp 37 _ 2 29 log8_h9_r4_6
    (log8Run_cut log8_h9_pq log8_h9_bp 37 _ 2 27 log8_h9_r6_8
    (log8Run_cut log8_h9_pq log8_h9_bp 37 _ 2 25 log8_h9_r8_10
    (log8Run_cut log8_h9_pq log8_h9_bp 37 _ 2 23 log8_h9_r10_12
    (log8Run_cut log8_h9_pq log8_h9_bp 37 _ 2 21 log8_h9_r12_14
    (log8Run_cut log8_h9_pq log8_h9_bp 37 _ 2 19 log8_h9_r14_16
    (log8Run_cut log8_h9_pq log8_h9_bp 37 _ 2 17 log8_h9_r16_18
    (log8Run_cut log8_h9_pq log8_h9_bp 37 _ 2 15 log8_h9_r18_20
    (log8Run_cut log8_h9_pq log8_h9_bp 37 _ 2 13 log8_h9_r20_22
    (log8Run_cut log8_h9_pq log8_h9_bp 37 _ 2 11 log8_h9_r22_24
    (log8Run_cut log8_h9_pq log8_h9_bp 37 _ 2 9 log8_h9_r24_26
    (log8Run_cut log8_h9_pq log8_h9_bp 37 _ 2 7 log8_h9_r26_28
    (log8Run_cut log8_h9_pq log8_h9_bp 37 _ 2 5 log8_h9_r28_30
    (log8Run_cut log8_h9_pq log8_h9_bp 37 _ 2 3 log8_h9_r30_32
    (log8Run_cut log8_h9_pq log8_h9_bp 37 _ 2 1 log8_h9_r32_34
    (log8_h9_r34_35)))))))))))))))))

theorem log8_h9_hp : Log8Head true 0 37 log8_h9_pq log8_h9_bp (dySt log8_h9_tp) :=
  Log8Head.mk_ne (by decide) log8_h9_q log8_h9_r log8_h9_wt log8_h9_yt log8_h9_tpt

theorem log8_h9_hm : Log8Head false 0 37 log8_h9_pq log8_h9_bp (dySt log8_h9_tm) :=
  Log8Head.mk_ne (by decide) log8_h9_q log8_h9_r log8_h9_wt log8_h9_yt log8_h9_tmt

theorem log8_g7zp0e0_ev :
    Log8Eval true true 0 37 log8_g7zp0e0_v.1 log8_g7zp0e0_v.2.2.2 false log8_g7zp0e0_v.2.1 log8_g7zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g7zp0e0_leaf log8_h9_hp rfl log8_g7zp0e0_a log8_g7zp0e0_b log8_g7zp0e0_end

theorem log8_g7zp0e1_ev :
    Log8Eval true true 0 37 log8_g7zp0e1_v.1 log8_g7zp0e1_v.2.2.2 false log8_g7zp0e1_v.2.1 log8_g7zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g7zp0e1_leaf log8_h9_hp rfl log8_g7zp0e1_a log8_g7zp0e1_b log8_g7zp0e1_end

theorem log8_g7np0e0_ev :
    Log8Eval false true 0 37 log8_g7np0e0_v.1 log8_g7np0e0_v.2.2.2 false log8_g7np0e0_v.2.1 log8_g7np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g7np0e0_leaf log8_h9_hp rfl log8_g7np0e0_a log8_g7np0e0_b log8_g7np0e0_end

theorem log8_g7np0e1_ev :
    Log8Eval false true 0 37 log8_g7np0e1_v.1 log8_g7np0e1_v.2.2.2 false log8_g7np0e1_v.2.1 log8_g7np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g7np0e1_leaf log8_h9_hp rfl log8_g7np0e1_a log8_g7np0e1_b log8_g7np0e1_end

theorem log8_g7zm0e0_ev :
    Log8Eval true false 0 37 log8_g7zm0e0_v.1 log8_g7zm0e0_v.2.2.2 false log8_g7zm0e0_v.2.1 log8_g7zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g7zm0e0_leaf log8_h9_hm rfl log8_g7zm0e0_a log8_g7zm0e0_b log8_g7zm0e0_end

theorem log8_g7zm0e1_ev :
    Log8Eval true false 0 37 log8_g7zm0e1_v.1 log8_g7zm0e1_v.2.2.2 false log8_g7zm0e1_v.2.1 log8_g7zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g7zm0e1_leaf log8_h9_hm rfl log8_g7zm0e1_a log8_g7zm0e1_b log8_g7zm0e1_end

theorem log8_g7nm0e0_ev :
    Log8Eval false false 0 37 log8_g7nm0e0_v.1 log8_g7nm0e0_v.2.2.2 false log8_g7nm0e0_v.2.1 log8_g7nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g7nm0e0_leaf log8_h9_hm rfl log8_g7nm0e0_a log8_g7nm0e0_b log8_g7nm0e0_end

theorem log8_g7nm0e1_ev :
    Log8Eval false false 0 37 log8_g7nm0e1_v.1 log8_g7nm0e1_v.2.2.2 false log8_g7nm0e1_v.2.1 log8_g7nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g7nm0e1_leaf log8_h9_hm rfl log8_g7nm0e1_a log8_g7nm0e1_b log8_g7nm0e1_end

theorem log8_h11_q : ∀ q ∈ log8_h11_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h11_r : log8Run log8_h11_pq log8_h11_bp 32 0 30 (hornerInitL 8 exp8F exp8Phi 32) =
    dySt log8_h11_s30 :=
  log8Run_cut log8_h11_pq log8_h11_bp 32 _ 2 28 log8_h11_r0_2
    (log8Run_cut log8_h11_pq log8_h11_bp 32 _ 2 26 log8_h11_r2_4
    (log8Run_cut log8_h11_pq log8_h11_bp 32 _ 2 24 log8_h11_r4_6
    (log8Run_cut log8_h11_pq log8_h11_bp 32 _ 2 22 log8_h11_r6_8
    (log8Run_cut log8_h11_pq log8_h11_bp 32 _ 2 20 log8_h11_r8_10
    (log8Run_cut log8_h11_pq log8_h11_bp 32 _ 2 18 log8_h11_r10_12
    (log8Run_cut log8_h11_pq log8_h11_bp 32 _ 2 16 log8_h11_r12_14
    (log8Run_cut log8_h11_pq log8_h11_bp 32 _ 2 14 log8_h11_r14_16
    (log8Run_cut log8_h11_pq log8_h11_bp 32 _ 2 12 log8_h11_r16_18
    (log8Run_cut log8_h11_pq log8_h11_bp 32 _ 2 10 log8_h11_r18_20
    (log8Run_cut log8_h11_pq log8_h11_bp 32 _ 2 8 log8_h11_r20_22
    (log8Run_cut log8_h11_pq log8_h11_bp 32 _ 2 6 log8_h11_r22_24
    (log8Run_cut log8_h11_pq log8_h11_bp 32 _ 2 4 log8_h11_r24_26
    (log8Run_cut log8_h11_pq log8_h11_bp 32 _ 2 2 log8_h11_r26_28
    (log8_h11_r28_30))))))))))))))

theorem log8_h11_hp : Log8Head true 0 32 log8_h11_pq log8_h11_bp (dySt log8_h11_tp) :=
  Log8Head.mk_ne (by decide) log8_h11_q log8_h11_r log8_h11_wt log8_h11_yt log8_h11_tpt

theorem log8_h11_hm : Log8Head false 0 32 log8_h11_pq log8_h11_bp (dySt log8_h11_tm) :=
  Log8Head.mk_ne (by decide) log8_h11_q log8_h11_r log8_h11_wt log8_h11_yt log8_h11_tmt

theorem log8_g9zp0e0_ev :
    Log8Eval true true 0 32 log8_g9zp0e0_v.1 log8_g9zp0e0_v.2.2.2 false log8_g9zp0e0_v.2.1 log8_g9zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g9zp0e0_leaf log8_h11_hp rfl log8_g9zp0e0_a log8_g9zp0e0_b log8_g9zp0e0_end

theorem log8_g9zp0e1_ev :
    Log8Eval true true 0 32 log8_g9zp0e1_v.1 log8_g9zp0e1_v.2.2.2 false log8_g9zp0e1_v.2.1 log8_g9zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g9zp0e1_leaf log8_h11_hp rfl log8_g9zp0e1_a log8_g9zp0e1_b log8_g9zp0e1_end

theorem log8_g9np0e0_ev :
    Log8Eval false true 0 32 log8_g9np0e0_v.1 log8_g9np0e0_v.2.2.2 false log8_g9np0e0_v.2.1 log8_g9np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g9np0e0_leaf log8_h11_hp rfl log8_g9np0e0_a log8_g9np0e0_b log8_g9np0e0_end

theorem log8_g9np0e1_ev :
    Log8Eval false true 0 32 log8_g9np0e1_v.1 log8_g9np0e1_v.2.2.2 false log8_g9np0e1_v.2.1 log8_g9np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g9np0e1_leaf log8_h11_hp rfl log8_g9np0e1_a log8_g9np0e1_b log8_g9np0e1_end

theorem log8_g9zm0e0_ev :
    Log8Eval true false 0 32 log8_g9zm0e0_v.1 log8_g9zm0e0_v.2.2.2 false log8_g9zm0e0_v.2.1 log8_g9zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g9zm0e0_leaf log8_h11_hm rfl log8_g9zm0e0_a log8_g9zm0e0_b log8_g9zm0e0_end

theorem log8_g9zm0e1_ev :
    Log8Eval true false 0 32 log8_g9zm0e1_v.1 log8_g9zm0e1_v.2.2.2 false log8_g9zm0e1_v.2.1 log8_g9zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g9zm0e1_leaf log8_h11_hm rfl log8_g9zm0e1_a log8_g9zm0e1_b log8_g9zm0e1_end

theorem log8_g9nm0e0_ev :
    Log8Eval false false 0 32 log8_g9nm0e0_v.1 log8_g9nm0e0_v.2.2.2 false log8_g9nm0e0_v.2.1 log8_g9nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g9nm0e0_leaf log8_h11_hm rfl log8_g9nm0e0_a log8_g9nm0e0_b log8_g9nm0e0_end

theorem log8_g9nm0e1_ev :
    Log8Eval false false 0 32 log8_g9nm0e1_v.1 log8_g9nm0e1_v.2.2.2 false log8_g9nm0e1_v.2.1 log8_g9nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g9nm0e1_leaf log8_h11_hm rfl log8_g9nm0e1_a log8_g9nm0e1_b log8_g9nm0e1_end

theorem log8_h22_q : ∀ q ∈ log8_h22_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h22_r : log8Run log8_h22_pq log8_h22_bp 17 0 15 (hornerInitL 8 exp8F exp8Phi 17) =
    dySt log8_h22_s15 :=
  log8Run_cut log8_h22_pq log8_h22_bp 17 _ 2 13 log8_h22_r0_2
    (log8Run_cut log8_h22_pq log8_h22_bp 17 _ 2 11 log8_h22_r2_4
    (log8Run_cut log8_h22_pq log8_h22_bp 17 _ 2 9 log8_h22_r4_6
    (log8Run_cut log8_h22_pq log8_h22_bp 17 _ 2 7 log8_h22_r6_8
    (log8Run_cut log8_h22_pq log8_h22_bp 17 _ 2 5 log8_h22_r8_10
    (log8Run_cut log8_h22_pq log8_h22_bp 17 _ 2 3 log8_h22_r10_12
    (log8Run_cut log8_h22_pq log8_h22_bp 17 _ 2 1 log8_h22_r12_14
    (log8_h22_r14_15)))))))

theorem log8_h22_hp : Log8Head true 0 17 log8_h22_pq log8_h22_bp (dySt log8_h22_tp) :=
  Log8Head.mk_ne (by decide) log8_h22_q log8_h22_r log8_h22_wt log8_h22_yt log8_h22_tpt

theorem log8_h22_hm : Log8Head false 0 17 log8_h22_pq log8_h22_bp (dySt log8_h22_tm) :=
  Log8Head.mk_ne (by decide) log8_h22_q log8_h22_r log8_h22_wt log8_h22_yt log8_h22_tmt

theorem log8_g20zp0e0_ev :
    Log8Eval true true 0 17 log8_g20zp0e0_v.1 log8_g20zp0e0_v.2.2.2 false log8_g20zp0e0_v.2.1 log8_g20zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g20zp0e0_leaf log8_h22_hp rfl log8_g20zp0e0_a log8_g20zp0e0_b log8_g20zp0e0_end

theorem log8_g20zp0e1_ev :
    Log8Eval true true 0 17 log8_g20zp0e1_v.1 log8_g20zp0e1_v.2.2.2 false log8_g20zp0e1_v.2.1 log8_g20zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g20zp0e1_leaf log8_h22_hp rfl log8_g20zp0e1_a log8_g20zp0e1_b log8_g20zp0e1_end

theorem log8_g20np0e0_ev :
    Log8Eval false true 0 17 log8_g20np0e0_v.1 log8_g20np0e0_v.2.2.2 false log8_g20np0e0_v.2.1 log8_g20np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g20np0e0_leaf log8_h22_hp rfl log8_g20np0e0_a log8_g20np0e0_b log8_g20np0e0_end

theorem log8_g20np0e1_ev :
    Log8Eval false true 0 17 log8_g20np0e1_v.1 log8_g20np0e1_v.2.2.2 false log8_g20np0e1_v.2.1 log8_g20np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g20np0e1_leaf log8_h22_hp rfl log8_g20np0e1_a log8_g20np0e1_b log8_g20np0e1_end

theorem log8_g20zm0e0_ev :
    Log8Eval true false 0 17 log8_g20zm0e0_v.1 log8_g20zm0e0_v.2.2.2 false log8_g20zm0e0_v.2.1 log8_g20zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g20zm0e0_leaf log8_h22_hm rfl log8_g20zm0e0_a log8_g20zm0e0_b log8_g20zm0e0_end

theorem log8_g20zm0e1_ev :
    Log8Eval true false 0 17 log8_g20zm0e1_v.1 log8_g20zm0e1_v.2.2.2 false log8_g20zm0e1_v.2.1 log8_g20zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g20zm0e1_leaf log8_h22_hm rfl log8_g20zm0e1_a log8_g20zm0e1_b log8_g20zm0e1_end

theorem log8_g20nm0e0_ev :
    Log8Eval false false 0 17 log8_g20nm0e0_v.1 log8_g20nm0e0_v.2.2.2 false log8_g20nm0e0_v.2.1 log8_g20nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g20nm0e0_leaf log8_h22_hm rfl log8_g20nm0e0_a log8_g20nm0e0_b log8_g20nm0e0_end

theorem log8_g20nm0e1_ev :
    Log8Eval false false 0 17 log8_g20nm0e1_v.1 log8_g20nm0e1_v.2.2.2 false log8_g20nm0e1_v.2.1 log8_g20nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g20nm0e1_leaf log8_h22_hm rfl log8_g20nm0e1_a log8_g20nm0e1_b log8_g20nm0e1_end

theorem log8_h27_q : ∀ q ∈ log8_h27_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h27_r : log8Run log8_h27_pq log8_h27_bp 12 0 10 (hornerInitL 8 exp8F exp8Phi 12) =
    dySt log8_h27_s10 :=
  log8Run_cut log8_h27_pq log8_h27_bp 12 _ 2 8 log8_h27_r0_2
    (log8Run_cut log8_h27_pq log8_h27_bp 12 _ 2 6 log8_h27_r2_4
    (log8Run_cut log8_h27_pq log8_h27_bp 12 _ 2 4 log8_h27_r4_6
    (log8Run_cut log8_h27_pq log8_h27_bp 12 _ 2 2 log8_h27_r6_8
    (log8_h27_r8_10))))

theorem log8_h27_hp : Log8Head true 0 12 log8_h27_pq log8_h27_bp (dySt log8_h27_tp) :=
  Log8Head.mk_ne (by decide) log8_h27_q log8_h27_r log8_h27_wt log8_h27_yt log8_h27_tpt

theorem log8_h27_hm : Log8Head false 0 12 log8_h27_pq log8_h27_bp (dySt log8_h27_tm) :=
  Log8Head.mk_ne (by decide) log8_h27_q log8_h27_r log8_h27_wt log8_h27_yt log8_h27_tmt

theorem log8_g25zp0e0_ev :
    Log8Eval true true 0 12 log8_g25zp0e0_v.1 log8_g25zp0e0_v.2.2.2 false log8_g25zp0e0_v.2.1 log8_g25zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g25zp0e0_leaf log8_h27_hp rfl log8_g25zp0e0_a log8_g25zp0e0_b log8_g25zp0e0_end

theorem log8_g25zp0e1_ev :
    Log8Eval true true 0 12 log8_g25zp0e1_v.1 log8_g25zp0e1_v.2.2.2 false log8_g25zp0e1_v.2.1 log8_g25zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g25zp0e1_leaf log8_h27_hp rfl log8_g25zp0e1_a log8_g25zp0e1_b log8_g25zp0e1_end

theorem log8_g25np0e0_ev :
    Log8Eval false true 0 12 log8_g25np0e0_v.1 log8_g25np0e0_v.2.2.2 false log8_g25np0e0_v.2.1 log8_g25np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g25np0e0_leaf log8_h27_hp rfl log8_g25np0e0_a log8_g25np0e0_b log8_g25np0e0_end

theorem log8_g25np0e1_ev :
    Log8Eval false true 0 12 log8_g25np0e1_v.1 log8_g25np0e1_v.2.2.2 false log8_g25np0e1_v.2.1 log8_g25np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g25np0e1_leaf log8_h27_hp rfl log8_g25np0e1_a log8_g25np0e1_b log8_g25np0e1_end

theorem log8_g25zm0e0_ev :
    Log8Eval true false 0 12 log8_g25zm0e0_v.1 log8_g25zm0e0_v.2.2.2 false log8_g25zm0e0_v.2.1 log8_g25zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g25zm0e0_leaf log8_h27_hm rfl log8_g25zm0e0_a log8_g25zm0e0_b log8_g25zm0e0_end

theorem log8_g25zm0e1_ev :
    Log8Eval true false 0 12 log8_g25zm0e1_v.1 log8_g25zm0e1_v.2.2.2 false log8_g25zm0e1_v.2.1 log8_g25zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g25zm0e1_leaf log8_h27_hm rfl log8_g25zm0e1_a log8_g25zm0e1_b log8_g25zm0e1_end

theorem log8_g25nm0e0_ev :
    Log8Eval false false 0 12 log8_g25nm0e0_v.1 log8_g25nm0e0_v.2.2.2 false log8_g25nm0e0_v.2.1 log8_g25nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g25nm0e0_leaf log8_h27_hm rfl log8_g25nm0e0_a log8_g25nm0e0_b log8_g25nm0e0_end

theorem log8_g25nm0e1_ev :
    Log8Eval false false 0 12 log8_g25nm0e1_v.1 log8_g25nm0e1_v.2.2.2 false log8_g25nm0e1_v.2.1 log8_g25nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g25nm0e1_leaf log8_h27_hm rfl log8_g25nm0e1_a log8_g25nm0e1_b log8_g25nm0e1_end

theorem log8_h37_q : ∀ q ∈ log8_h37_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h37_r : log8Run log8_h37_pq log8_h37_bp 8 0 6 (hornerInitL 8 exp8F exp8Phi 8) =
    dySt log8_h37_s6 :=
  log8Run_cut log8_h37_pq log8_h37_bp 8 _ 2 4 log8_h37_r0_2
    (log8Run_cut log8_h37_pq log8_h37_bp 8 _ 2 2 log8_h37_r2_4
    (log8_h37_r4_6))

theorem log8_h37_hp : Log8Head true 0 8 log8_h37_pq log8_h37_bp (dySt log8_h37_tp) :=
  Log8Head.mk_ne (by decide) log8_h37_q log8_h37_r log8_h37_wt log8_h37_yt log8_h37_tpt

theorem log8_h37_hm : Log8Head false 0 8 log8_h37_pq log8_h37_bp (dySt log8_h37_tm) :=
  Log8Head.mk_ne (by decide) log8_h37_q log8_h37_r log8_h37_wt log8_h37_yt log8_h37_tmt

theorem log8_h38_q : ∀ q ∈ log8_h38_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h38_r : log8Run log8_h38_pq log8_h38_bp 8 0 6 (hornerInitL 8 exp8F exp8Phi 8) =
    dySt log8_h38_s6 :=
  log8Run_cut log8_h38_pq log8_h38_bp 8 _ 2 4 log8_h38_r0_2
    (log8Run_cut log8_h38_pq log8_h38_bp 8 _ 2 2 log8_h38_r2_4
    (log8_h38_r4_6))

theorem log8_h38_hp : Log8Head true 0 8 log8_h38_pq log8_h38_bp (dySt log8_h38_tp) :=
  Log8Head.mk_ne (by decide) log8_h38_q log8_h38_r log8_h38_wt log8_h38_yt log8_h38_tpt

theorem log8_h38_hm : Log8Head false 0 8 log8_h38_pq log8_h38_bp (dySt log8_h38_tm) :=
  Log8Head.mk_ne (by decide) log8_h38_q log8_h38_r log8_h38_wt log8_h38_yt log8_h38_tmt

theorem log8_h39_q : ∀ q ∈ log8_h39_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h39_r : log8Run log8_h39_pq log8_h39_bp 8 0 6 (hornerInitL 8 exp8F exp8Phi 8) =
    dySt log8_h39_s6 :=
  log8Run_cut log8_h39_pq log8_h39_bp 8 _ 2 4 log8_h39_r0_2
    (log8Run_cut log8_h39_pq log8_h39_bp 8 _ 2 2 log8_h39_r2_4
    (log8_h39_r4_6))

theorem log8_h39_hp : Log8Head true 0 8 log8_h39_pq log8_h39_bp (dySt log8_h39_tp) :=
  Log8Head.mk_ne (by decide) log8_h39_q log8_h39_r log8_h39_wt log8_h39_yt log8_h39_tpt

theorem log8_h39_hm : Log8Head false 0 8 log8_h39_pq log8_h39_bp (dySt log8_h39_tm) :=
  Log8Head.mk_ne (by decide) log8_h39_q log8_h39_r log8_h39_wt log8_h39_yt log8_h39_tmt

theorem log8_g29zp0e0_ev :
    Log8Eval true true 0 8 log8_g29zp0e0_v.1 log8_g29zp0e0_v.2.2.2 true log8_g29zp0e0_v.2.1 log8_g29zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g29zp0e0_leaf log8_h39_hp rfl log8_g29zp0e0_a log8_g29zp0e0_b log8_g29zp0e0_end

theorem log8_g29zp0e1_ev :
    Log8Eval true true 0 8 log8_g29zp0e1_v.1 log8_g29zp0e1_v.2.2.2 true log8_g29zp0e1_v.2.1 log8_g29zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g29zp0e1_leaf log8_h38_hp rfl log8_g29zp0e1_a log8_g29zp0e1_b log8_g29zp0e1_end

theorem log8_g29np0e0_ev :
    Log8Eval false true 0 8 log8_g29np0e0_v.1 log8_g29np0e0_v.2.2.2 false log8_g29np0e0_v.2.1 log8_g29np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g29np0e0_leaf log8_h37_hp rfl log8_g29np0e0_a log8_g29np0e0_b log8_g29np0e0_end

theorem log8_g29np0e1_ev :
    Log8Eval false true 0 8 log8_g29np0e1_v.1 log8_g29np0e1_v.2.2.2 false log8_g29np0e1_v.2.1 log8_g29np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g29np0e1_leaf log8_h37_hp rfl log8_g29np0e1_a log8_g29np0e1_b log8_g29np0e1_end

theorem log8_g29zm0e0_ev :
    Log8Eval true false 0 8 log8_g29zm0e0_v.1 log8_g29zm0e0_v.2.2.2 true log8_g29zm0e0_v.2.1 log8_g29zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g29zm0e0_leaf log8_h39_hm rfl log8_g29zm0e0_a log8_g29zm0e0_b log8_g29zm0e0_end

theorem log8_g29zm0e1_ev :
    Log8Eval true false 0 8 log8_g29zm0e1_v.1 log8_g29zm0e1_v.2.2.2 true log8_g29zm0e1_v.2.1 log8_g29zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g29zm0e1_leaf log8_h38_hm rfl log8_g29zm0e1_a log8_g29zm0e1_b log8_g29zm0e1_end

theorem log8_g29nm0e0_ev :
    Log8Eval false false 0 8 log8_g29nm0e0_v.1 log8_g29nm0e0_v.2.2.2 false log8_g29nm0e0_v.2.1 log8_g29nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g29nm0e0_leaf log8_h37_hm rfl log8_g29nm0e0_a log8_g29nm0e0_b log8_g29nm0e0_end

theorem log8_g29nm0e1_ev :
    Log8Eval false false 0 8 log8_g29nm0e1_v.1 log8_g29nm0e1_v.2.2.2 false log8_g29nm0e1_v.2.1 log8_g29nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g29nm0e1_leaf log8_h37_hm rfl log8_g29nm0e1_a log8_g29nm0e1_b log8_g29nm0e1_end

theorem log8_h10_q : ∀ q ∈ log8_h10_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h10_r : log8Run log8_h10_pq log8_h10_bp 34 0 32 (hornerInitL 8 exp8F exp8Phi 34) =
    dySt log8_h10_s32 :=
  log8Run_cut log8_h10_pq log8_h10_bp 34 _ 2 30 log8_h10_r0_2
    (log8Run_cut log8_h10_pq log8_h10_bp 34 _ 2 28 log8_h10_r2_4
    (log8Run_cut log8_h10_pq log8_h10_bp 34 _ 2 26 log8_h10_r4_6
    (log8Run_cut log8_h10_pq log8_h10_bp 34 _ 2 24 log8_h10_r6_8
    (log8Run_cut log8_h10_pq log8_h10_bp 34 _ 2 22 log8_h10_r8_10
    (log8Run_cut log8_h10_pq log8_h10_bp 34 _ 2 20 log8_h10_r10_12
    (log8Run_cut log8_h10_pq log8_h10_bp 34 _ 2 18 log8_h10_r12_14
    (log8Run_cut log8_h10_pq log8_h10_bp 34 _ 2 16 log8_h10_r14_16
    (log8Run_cut log8_h10_pq log8_h10_bp 34 _ 2 14 log8_h10_r16_18
    (log8Run_cut log8_h10_pq log8_h10_bp 34 _ 2 12 log8_h10_r18_20
    (log8Run_cut log8_h10_pq log8_h10_bp 34 _ 2 10 log8_h10_r20_22
    (log8Run_cut log8_h10_pq log8_h10_bp 34 _ 2 8 log8_h10_r22_24
    (log8Run_cut log8_h10_pq log8_h10_bp 34 _ 2 6 log8_h10_r24_26
    (log8Run_cut log8_h10_pq log8_h10_bp 34 _ 2 4 log8_h10_r26_28
    (log8Run_cut log8_h10_pq log8_h10_bp 34 _ 2 2 log8_h10_r28_30
    (log8_h10_r30_32)))))))))))))))

theorem log8_h10_hp : Log8Head true 0 34 log8_h10_pq log8_h10_bp (dySt log8_h10_tp) :=
  Log8Head.mk_ne (by decide) log8_h10_q log8_h10_r log8_h10_wt log8_h10_yt log8_h10_tpt

theorem log8_h10_hm : Log8Head false 0 34 log8_h10_pq log8_h10_bp (dySt log8_h10_tm) :=
  Log8Head.mk_ne (by decide) log8_h10_q log8_h10_r log8_h10_wt log8_h10_yt log8_h10_tmt

theorem log8_g8zp0e0_ev :
    Log8Eval true true 0 34 log8_g8zp0e0_v.1 log8_g8zp0e0_v.2.2.2 false log8_g8zp0e0_v.2.1 log8_g8zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g8zp0e0_leaf log8_h10_hp rfl log8_g8zp0e0_a log8_g8zp0e0_b log8_g8zp0e0_end

theorem log8_g8zp0e1_ev :
    Log8Eval true true 0 34 log8_g8zp0e1_v.1 log8_g8zp0e1_v.2.2.2 false log8_g8zp0e1_v.2.1 log8_g8zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g8zp0e1_leaf log8_h10_hp rfl log8_g8zp0e1_a log8_g8zp0e1_b log8_g8zp0e1_end

theorem log8_g8np0e0_ev :
    Log8Eval false true 0 34 log8_g8np0e0_v.1 log8_g8np0e0_v.2.2.2 false log8_g8np0e0_v.2.1 log8_g8np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g8np0e0_leaf log8_h10_hp rfl log8_g8np0e0_a log8_g8np0e0_b log8_g8np0e0_end

theorem log8_g8np0e1_ev :
    Log8Eval false true 0 34 log8_g8np0e1_v.1 log8_g8np0e1_v.2.2.2 false log8_g8np0e1_v.2.1 log8_g8np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g8np0e1_leaf log8_h10_hp rfl log8_g8np0e1_a log8_g8np0e1_b log8_g8np0e1_end

theorem log8_g8zm0e0_ev :
    Log8Eval true false 0 34 log8_g8zm0e0_v.1 log8_g8zm0e0_v.2.2.2 false log8_g8zm0e0_v.2.1 log8_g8zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g8zm0e0_leaf log8_h10_hm rfl log8_g8zm0e0_a log8_g8zm0e0_b log8_g8zm0e0_end

theorem log8_g8zm0e1_ev :
    Log8Eval true false 0 34 log8_g8zm0e1_v.1 log8_g8zm0e1_v.2.2.2 false log8_g8zm0e1_v.2.1 log8_g8zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g8zm0e1_leaf log8_h10_hm rfl log8_g8zm0e1_a log8_g8zm0e1_b log8_g8zm0e1_end

theorem log8_g8nm0e0_ev :
    Log8Eval false false 0 34 log8_g8nm0e0_v.1 log8_g8nm0e0_v.2.2.2 false log8_g8nm0e0_v.2.1 log8_g8nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g8nm0e0_leaf log8_h10_hm rfl log8_g8nm0e0_a log8_g8nm0e0_b log8_g8nm0e0_end

theorem log8_g8nm0e1_ev :
    Log8Eval false false 0 34 log8_g8nm0e1_v.1 log8_g8nm0e1_v.2.2.2 false log8_g8nm0e1_v.2.1 log8_g8nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g8nm0e1_leaf log8_h10_hm rfl log8_g8nm0e1_a log8_g8nm0e1_b log8_g8nm0e1_end

theorem log8_h15_q : ∀ q ∈ log8_h15_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h15_r : log8Run log8_h15_pq log8_h15_bp 25 0 23 (hornerInitL 8 exp8F exp8Phi 25) =
    dySt log8_h15_s23 :=
  log8Run_cut log8_h15_pq log8_h15_bp 25 _ 2 21 log8_h15_r0_2
    (log8Run_cut log8_h15_pq log8_h15_bp 25 _ 2 19 log8_h15_r2_4
    (log8Run_cut log8_h15_pq log8_h15_bp 25 _ 2 17 log8_h15_r4_6
    (log8Run_cut log8_h15_pq log8_h15_bp 25 _ 2 15 log8_h15_r6_8
    (log8Run_cut log8_h15_pq log8_h15_bp 25 _ 2 13 log8_h15_r8_10
    (log8Run_cut log8_h15_pq log8_h15_bp 25 _ 2 11 log8_h15_r10_12
    (log8Run_cut log8_h15_pq log8_h15_bp 25 _ 2 9 log8_h15_r12_14
    (log8Run_cut log8_h15_pq log8_h15_bp 25 _ 2 7 log8_h15_r14_16
    (log8Run_cut log8_h15_pq log8_h15_bp 25 _ 2 5 log8_h15_r16_18
    (log8Run_cut log8_h15_pq log8_h15_bp 25 _ 2 3 log8_h15_r18_20
    (log8Run_cut log8_h15_pq log8_h15_bp 25 _ 2 1 log8_h15_r20_22
    (log8_h15_r22_23)))))))))))

theorem log8_h15_hp : Log8Head true 0 25 log8_h15_pq log8_h15_bp (dySt log8_h15_tp) :=
  Log8Head.mk_ne (by decide) log8_h15_q log8_h15_r log8_h15_wt log8_h15_yt log8_h15_tpt

theorem log8_h15_hm : Log8Head false 0 25 log8_h15_pq log8_h15_bp (dySt log8_h15_tm) :=
  Log8Head.mk_ne (by decide) log8_h15_q log8_h15_r log8_h15_wt log8_h15_yt log8_h15_tmt

theorem log8_g13zp0e0_ev :
    Log8Eval true true 0 25 log8_g13zp0e0_v.1 log8_g13zp0e0_v.2.2.2 false log8_g13zp0e0_v.2.1 log8_g13zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g13zp0e0_leaf log8_h15_hp rfl log8_g13zp0e0_a log8_g13zp0e0_b log8_g13zp0e0_end

theorem log8_g13zp0e1_ev :
    Log8Eval true true 0 25 log8_g13zp0e1_v.1 log8_g13zp0e1_v.2.2.2 false log8_g13zp0e1_v.2.1 log8_g13zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g13zp0e1_leaf log8_h15_hp rfl log8_g13zp0e1_a log8_g13zp0e1_b log8_g13zp0e1_end

theorem log8_g13np0e0_ev :
    Log8Eval false true 0 25 log8_g13np0e0_v.1 log8_g13np0e0_v.2.2.2 false log8_g13np0e0_v.2.1 log8_g13np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g13np0e0_leaf log8_h15_hp rfl log8_g13np0e0_a log8_g13np0e0_b log8_g13np0e0_end

theorem log8_g13np0e1_ev :
    Log8Eval false true 0 25 log8_g13np0e1_v.1 log8_g13np0e1_v.2.2.2 false log8_g13np0e1_v.2.1 log8_g13np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g13np0e1_leaf log8_h15_hp rfl log8_g13np0e1_a log8_g13np0e1_b log8_g13np0e1_end

theorem log8_g13zm0e0_ev :
    Log8Eval true false 0 25 log8_g13zm0e0_v.1 log8_g13zm0e0_v.2.2.2 false log8_g13zm0e0_v.2.1 log8_g13zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g13zm0e0_leaf log8_h15_hm rfl log8_g13zm0e0_a log8_g13zm0e0_b log8_g13zm0e0_end

theorem log8_g13zm0e1_ev :
    Log8Eval true false 0 25 log8_g13zm0e1_v.1 log8_g13zm0e1_v.2.2.2 false log8_g13zm0e1_v.2.1 log8_g13zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g13zm0e1_leaf log8_h15_hm rfl log8_g13zm0e1_a log8_g13zm0e1_b log8_g13zm0e1_end

theorem log8_g13nm0e0_ev :
    Log8Eval false false 0 25 log8_g13nm0e0_v.1 log8_g13nm0e0_v.2.2.2 false log8_g13nm0e0_v.2.1 log8_g13nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g13nm0e0_leaf log8_h15_hm rfl log8_g13nm0e0_a log8_g13nm0e0_b log8_g13nm0e0_end

theorem log8_g13nm0e1_ev :
    Log8Eval false false 0 25 log8_g13nm0e1_v.1 log8_g13nm0e1_v.2.2.2 false log8_g13nm0e1_v.2.1 log8_g13nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g13nm0e1_leaf log8_h15_hm rfl log8_g13nm0e1_a log8_g13nm0e1_b log8_g13nm0e1_end

theorem log8_h21_q : ∀ q ∈ log8_h21_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h21_r : log8Run log8_h21_pq log8_h21_bp 18 0 16 (hornerInitL 8 exp8F exp8Phi 18) =
    dySt log8_h21_s16 :=
  log8Run_cut log8_h21_pq log8_h21_bp 18 _ 2 14 log8_h21_r0_2
    (log8Run_cut log8_h21_pq log8_h21_bp 18 _ 2 12 log8_h21_r2_4
    (log8Run_cut log8_h21_pq log8_h21_bp 18 _ 2 10 log8_h21_r4_6
    (log8Run_cut log8_h21_pq log8_h21_bp 18 _ 2 8 log8_h21_r6_8
    (log8Run_cut log8_h21_pq log8_h21_bp 18 _ 2 6 log8_h21_r8_10
    (log8Run_cut log8_h21_pq log8_h21_bp 18 _ 2 4 log8_h21_r10_12
    (log8Run_cut log8_h21_pq log8_h21_bp 18 _ 2 2 log8_h21_r12_14
    (log8_h21_r14_16)))))))

theorem log8_h21_hp : Log8Head true 0 18 log8_h21_pq log8_h21_bp (dySt log8_h21_tp) :=
  Log8Head.mk_ne (by decide) log8_h21_q log8_h21_r log8_h21_wt log8_h21_yt log8_h21_tpt

theorem log8_h21_hm : Log8Head false 0 18 log8_h21_pq log8_h21_bp (dySt log8_h21_tm) :=
  Log8Head.mk_ne (by decide) log8_h21_q log8_h21_r log8_h21_wt log8_h21_yt log8_h21_tmt

theorem log8_g19zp0e0_ev :
    Log8Eval true true 0 18 log8_g19zp0e0_v.1 log8_g19zp0e0_v.2.2.2 false log8_g19zp0e0_v.2.1 log8_g19zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g19zp0e0_leaf log8_h21_hp rfl log8_g19zp0e0_a log8_g19zp0e0_b log8_g19zp0e0_end

theorem log8_g19zp0e1_ev :
    Log8Eval true true 0 18 log8_g19zp0e1_v.1 log8_g19zp0e1_v.2.2.2 false log8_g19zp0e1_v.2.1 log8_g19zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g19zp0e1_leaf log8_h21_hp rfl log8_g19zp0e1_a log8_g19zp0e1_b log8_g19zp0e1_end

theorem log8_g19np0e0_ev :
    Log8Eval false true 0 18 log8_g19np0e0_v.1 log8_g19np0e0_v.2.2.2 false log8_g19np0e0_v.2.1 log8_g19np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g19np0e0_leaf log8_h21_hp rfl log8_g19np0e0_a log8_g19np0e0_b log8_g19np0e0_end

theorem log8_g19np0e1_ev :
    Log8Eval false true 0 18 log8_g19np0e1_v.1 log8_g19np0e1_v.2.2.2 false log8_g19np0e1_v.2.1 log8_g19np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g19np0e1_leaf log8_h21_hp rfl log8_g19np0e1_a log8_g19np0e1_b log8_g19np0e1_end

theorem log8_g19zm0e0_ev :
    Log8Eval true false 0 18 log8_g19zm0e0_v.1 log8_g19zm0e0_v.2.2.2 false log8_g19zm0e0_v.2.1 log8_g19zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g19zm0e0_leaf log8_h21_hm rfl log8_g19zm0e0_a log8_g19zm0e0_b log8_g19zm0e0_end

theorem log8_g19zm0e1_ev :
    Log8Eval true false 0 18 log8_g19zm0e1_v.1 log8_g19zm0e1_v.2.2.2 false log8_g19zm0e1_v.2.1 log8_g19zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g19zm0e1_leaf log8_h21_hm rfl log8_g19zm0e1_a log8_g19zm0e1_b log8_g19zm0e1_end

theorem log8_g19nm0e0_ev :
    Log8Eval false false 0 18 log8_g19nm0e0_v.1 log8_g19nm0e0_v.2.2.2 false log8_g19nm0e0_v.2.1 log8_g19nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g19nm0e0_leaf log8_h21_hm rfl log8_g19nm0e0_a log8_g19nm0e0_b log8_g19nm0e0_end

theorem log8_g19nm0e1_ev :
    Log8Eval false false 0 18 log8_g19nm0e1_v.1 log8_g19nm0e1_v.2.2.2 false log8_g19nm0e1_v.2.1 log8_g19nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g19nm0e1_leaf log8_h21_hm rfl log8_g19nm0e1_a log8_g19nm0e1_b log8_g19nm0e1_end

theorem log8_h28_q : ∀ q ∈ log8_h28_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h28_r : log8Run log8_h28_pq log8_h28_bp 11 0 9 (hornerInitL 8 exp8F exp8Phi 11) =
    dySt log8_h28_s9 :=
  log8Run_cut log8_h28_pq log8_h28_bp 11 _ 2 7 log8_h28_r0_2
    (log8Run_cut log8_h28_pq log8_h28_bp 11 _ 2 5 log8_h28_r2_4
    (log8Run_cut log8_h28_pq log8_h28_bp 11 _ 2 3 log8_h28_r4_6
    (log8Run_cut log8_h28_pq log8_h28_bp 11 _ 2 1 log8_h28_r6_8
    (log8_h28_r8_9))))

theorem log8_h28_hp : Log8Head true 0 11 log8_h28_pq log8_h28_bp (dySt log8_h28_tp) :=
  Log8Head.mk_ne (by decide) log8_h28_q log8_h28_r log8_h28_wt log8_h28_yt log8_h28_tpt

theorem log8_h28_hm : Log8Head false 0 11 log8_h28_pq log8_h28_bp (dySt log8_h28_tm) :=
  Log8Head.mk_ne (by decide) log8_h28_q log8_h28_r log8_h28_wt log8_h28_yt log8_h28_tmt

theorem log8_h29_q : ∀ q ∈ log8_h29_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h29_r : log8Run log8_h29_pq log8_h29_bp 11 0 9 (hornerInitL 8 exp8F exp8Phi 11) =
    dySt log8_h29_s9 :=
  log8Run_cut log8_h29_pq log8_h29_bp 11 _ 2 7 log8_h29_r0_2
    (log8Run_cut log8_h29_pq log8_h29_bp 11 _ 2 5 log8_h29_r2_4
    (log8Run_cut log8_h29_pq log8_h29_bp 11 _ 2 3 log8_h29_r4_6
    (log8Run_cut log8_h29_pq log8_h29_bp 11 _ 2 1 log8_h29_r6_8
    (log8_h29_r8_9))))

theorem log8_h29_hp : Log8Head true 0 11 log8_h29_pq log8_h29_bp (dySt log8_h29_tp) :=
  Log8Head.mk_ne (by decide) log8_h29_q log8_h29_r log8_h29_wt log8_h29_yt log8_h29_tpt

theorem log8_h29_hm : Log8Head false 0 11 log8_h29_pq log8_h29_bp (dySt log8_h29_tm) :=
  Log8Head.mk_ne (by decide) log8_h29_q log8_h29_r log8_h29_wt log8_h29_yt log8_h29_tmt

theorem log8_h30_q : ∀ q ∈ log8_h30_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h30_r : log8Run log8_h30_pq log8_h30_bp 11 0 9 (hornerInitL 8 exp8F exp8Phi 11) =
    dySt log8_h30_s9 :=
  log8Run_cut log8_h30_pq log8_h30_bp 11 _ 2 7 log8_h30_r0_2
    (log8Run_cut log8_h30_pq log8_h30_bp 11 _ 2 5 log8_h30_r2_4
    (log8Run_cut log8_h30_pq log8_h30_bp 11 _ 2 3 log8_h30_r4_6
    (log8Run_cut log8_h30_pq log8_h30_bp 11 _ 2 1 log8_h30_r6_8
    (log8_h30_r8_9))))

theorem log8_h30_hp : Log8Head true 0 11 log8_h30_pq log8_h30_bp (dySt log8_h30_tp) :=
  Log8Head.mk_ne (by decide) log8_h30_q log8_h30_r log8_h30_wt log8_h30_yt log8_h30_tpt

theorem log8_h30_hm : Log8Head false 0 11 log8_h30_pq log8_h30_bp (dySt log8_h30_tm) :=
  Log8Head.mk_ne (by decide) log8_h30_q log8_h30_r log8_h30_wt log8_h30_yt log8_h30_tmt

theorem log8_g26zp0e0_ev :
    Log8Eval true true 0 11 log8_g26zp0e0_v.1 log8_g26zp0e0_v.2.2.2 false log8_g26zp0e0_v.2.1 log8_g26zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g26zp0e0_leaf log8_h30_hp rfl log8_g26zp0e0_a log8_g26zp0e0_b log8_g26zp0e0_end

theorem log8_g26zp0e1_ev :
    Log8Eval true true 0 11 log8_g26zp0e1_v.1 log8_g26zp0e1_v.2.2.2 false log8_g26zp0e1_v.2.1 log8_g26zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g26zp0e1_leaf log8_h29_hp rfl log8_g26zp0e1_a log8_g26zp0e1_b log8_g26zp0e1_end

theorem log8_g26np0e0_ev :
    Log8Eval false true 0 11 log8_g26np0e0_v.1 log8_g26np0e0_v.2.2.2 false log8_g26np0e0_v.2.1 log8_g26np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g26np0e0_leaf log8_h28_hp rfl log8_g26np0e0_a log8_g26np0e0_b log8_g26np0e0_end

theorem log8_g26np0e1_ev :
    Log8Eval false true 0 11 log8_g26np0e1_v.1 log8_g26np0e1_v.2.2.2 false log8_g26np0e1_v.2.1 log8_g26np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g26np0e1_leaf log8_h28_hp rfl log8_g26np0e1_a log8_g26np0e1_b log8_g26np0e1_end

theorem log8_g26zm0e0_ev :
    Log8Eval true false 0 11 log8_g26zm0e0_v.1 log8_g26zm0e0_v.2.2.2 false log8_g26zm0e0_v.2.1 log8_g26zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g26zm0e0_leaf log8_h30_hm rfl log8_g26zm0e0_a log8_g26zm0e0_b log8_g26zm0e0_end

theorem log8_g26zm0e1_ev :
    Log8Eval true false 0 11 log8_g26zm0e1_v.1 log8_g26zm0e1_v.2.2.2 false log8_g26zm0e1_v.2.1 log8_g26zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g26zm0e1_leaf log8_h29_hm rfl log8_g26zm0e1_a log8_g26zm0e1_b log8_g26zm0e1_end

theorem log8_g26nm0e0_ev :
    Log8Eval false false 0 11 log8_g26nm0e0_v.1 log8_g26nm0e0_v.2.2.2 false log8_g26nm0e0_v.2.1 log8_g26nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g26nm0e0_leaf log8_h28_hm rfl log8_g26nm0e0_a log8_g26nm0e0_b log8_g26nm0e0_end

theorem log8_g26nm0e1_ev :
    Log8Eval false false 0 11 log8_g26nm0e1_v.1 log8_g26nm0e1_v.2.2.2 false log8_g26nm0e1_v.2.1 log8_g26nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g26nm0e1_leaf log8_h28_hm rfl log8_g26nm0e1_a log8_g26nm0e1_b log8_g26nm0e1_end

theorem log8_h49_q : ∀ q ∈ log8_h49_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h49_r : log8Run log8_h49_pq log8_h49_bp 4 0 2 (hornerInitL 8 exp8F exp8Phi 4) =
    dySt log8_h49_s2 :=
  log8_h49_r0_2

theorem log8_h49_hp : Log8Head true 0 4 log8_h49_pq log8_h49_bp (dySt log8_h49_tp) :=
  Log8Head.mk_ne (by decide) log8_h49_q log8_h49_r log8_h49_wt log8_h49_yt log8_h49_tpt

theorem log8_h49_hm : Log8Head false 0 4 log8_h49_pq log8_h49_bp (dySt log8_h49_tm) :=
  Log8Head.mk_ne (by decide) log8_h49_q log8_h49_r log8_h49_wt log8_h49_yt log8_h49_tmt

theorem log8_h50_q : ∀ q ∈ log8_h50_pq, 0 ≤ q := by
  decide +kernel

theorem log8_h50_r : log8Run log8_h50_pq log8_h50_bp 4 0 2 (hornerInitL 8 exp8F exp8Phi 4) =
    dySt log8_h50_s2 :=
  log8_h50_r0_2

theorem log8_h50_hp : Log8Head true 0 4 log8_h50_pq log8_h50_bp (dySt log8_h50_tp) :=
  Log8Head.mk_ne (by decide) log8_h50_q log8_h50_r log8_h50_wt log8_h50_yt log8_h50_tpt

theorem log8_h50_hm : Log8Head false 0 4 log8_h50_pq log8_h50_bp (dySt log8_h50_tm) :=
  Log8Head.mk_ne (by decide) log8_h50_q log8_h50_r log8_h50_wt log8_h50_yt log8_h50_tmt

theorem log8_g33zp0e0_ev :
    Log8Eval true true 0 4 log8_g33zp0e0_v.1 log8_g33zp0e0_v.2.2.2 true log8_g33zp0e0_v.2.1 log8_g33zp0e0_v.2.2.1 :=
  Log8Eval.mk log8_g33zp0e0_leaf log8_h50_hp rfl log8_g33zp0e0_a log8_g33zp0e0_b log8_g33zp0e0_end

theorem log8_g33zp0e1_ev :
    Log8Eval true true 0 4 log8_g33zp0e1_v.1 log8_g33zp0e1_v.2.2.2 true log8_g33zp0e1_v.2.1 log8_g33zp0e1_v.2.2.1 :=
  Log8Eval.mk log8_g33zp0e1_leaf log8_h50_hp rfl log8_g33zp0e1_a log8_g33zp0e1_b log8_g33zp0e1_end

theorem log8_g33np0e0_ev :
    Log8Eval false true 0 4 log8_g33np0e0_v.1 log8_g33np0e0_v.2.2.2 false log8_g33np0e0_v.2.1 log8_g33np0e0_v.2.2.1 :=
  Log8Eval.mk log8_g33np0e0_leaf log8_h49_hp rfl log8_g33np0e0_a log8_g33np0e0_b log8_g33np0e0_end

theorem log8_g33np0e1_ev :
    Log8Eval false true 0 4 log8_g33np0e1_v.1 log8_g33np0e1_v.2.2.2 false log8_g33np0e1_v.2.1 log8_g33np0e1_v.2.2.1 :=
  Log8Eval.mk log8_g33np0e1_leaf log8_h49_hp rfl log8_g33np0e1_a log8_g33np0e1_b log8_g33np0e1_end

theorem log8_g33zm0e0_ev :
    Log8Eval true false 0 4 log8_g33zm0e0_v.1 log8_g33zm0e0_v.2.2.2 true log8_g33zm0e0_v.2.1 log8_g33zm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g33zm0e0_leaf log8_h50_hm rfl log8_g33zm0e0_a log8_g33zm0e0_b log8_g33zm0e0_end

theorem log8_g33zm0e1_ev :
    Log8Eval true false 0 4 log8_g33zm0e1_v.1 log8_g33zm0e1_v.2.2.2 true log8_g33zm0e1_v.2.1 log8_g33zm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g33zm0e1_leaf log8_h50_hm rfl log8_g33zm0e1_a log8_g33zm0e1_b log8_g33zm0e1_end

theorem log8_g33nm0e0_ev :
    Log8Eval false false 0 4 log8_g33nm0e0_v.1 log8_g33nm0e0_v.2.2.2 false log8_g33nm0e0_v.2.1 log8_g33nm0e0_v.2.2.1 :=
  Log8Eval.mk log8_g33nm0e0_leaf log8_h49_hm rfl log8_g33nm0e0_a log8_g33nm0e0_b log8_g33nm0e0_end

theorem log8_g33nm0e1_ev :
    Log8Eval false false 0 4 log8_g33nm0e1_v.1 log8_g33nm0e1_v.2.2.2 false log8_g33nm0e1_v.2.1 log8_g33nm0e1_v.2.2.1 :=
  Log8Eval.mk log8_g33nm0e1_leaf log8_h49_hm rfl log8_g33nm0e1_a log8_g33nm0e1_b log8_g33nm0e1_end

theorem log8_all0 : ∀ g ∈ log8Grp0, Log8Group0 g := by
  intro g hg
  simp only [log8Grp0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    intro pos
    cases pos
    · exact ⟨log8_g0zm0e0_ev, log8_g0zm0e1_ev⟩
    · exact ⟨log8_g0zp0e0_ev, log8_g0zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g1zm0e0_ev, log8_g1zm0e1_ev⟩
    · exact ⟨log8_g1zp0e0_ev, log8_g1zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g2zm0e0_ev, log8_g2zm0e1_ev⟩
    · exact ⟨log8_g2zp0e0_ev, log8_g2zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g3zm0e0_ev, log8_g3zm0e1_ev⟩
    · exact ⟨log8_g3zp0e0_ev, log8_g3zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g4zm0e0_ev, log8_g4zm0e1_ev⟩
    · exact ⟨log8_g4zp0e0_ev, log8_g4zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g5zm0e0_ev, log8_g5zm0e1_ev⟩
    · exact ⟨log8_g5zp0e0_ev, log8_g5zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g6zm0e0_ev, log8_g6zm0e1_ev⟩
    · exact ⟨log8_g6zp0e0_ev, log8_g6zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g7zm0e0_ev, log8_g7zm0e1_ev⟩
    · exact ⟨log8_g7zp0e0_ev, log8_g7zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g8zm0e0_ev, log8_g8zm0e1_ev⟩
    · exact ⟨log8_g8zp0e0_ev, log8_g8zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g9zm0e0_ev, log8_g9zm0e1_ev⟩
    · exact ⟨log8_g9zp0e0_ev, log8_g9zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g10zm0e0_ev, log8_g10zm0e1_ev⟩
    · exact ⟨log8_g10zp0e0_ev, log8_g10zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g11zm0e0_ev, log8_g11zm0e1_ev⟩
    · exact ⟨log8_g11zp0e0_ev, log8_g11zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g12zm0e0_ev, log8_g12zm0e1_ev⟩
    · exact ⟨log8_g12zp0e0_ev, log8_g12zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g13zm0e0_ev, log8_g13zm0e1_ev⟩
    · exact ⟨log8_g13zp0e0_ev, log8_g13zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g14zm0e0_ev, log8_g14zm0e1_ev⟩
    · exact ⟨log8_g14zp0e0_ev, log8_g14zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g15zm0e0_ev, log8_g15zm0e1_ev⟩
    · exact ⟨log8_g15zp0e0_ev, log8_g15zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g16zm0e0_ev, log8_g16zm0e1_ev⟩
    · exact ⟨log8_g16zp0e0_ev, log8_g16zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g17zm0e0_ev, log8_g17zm0e1_ev⟩
    · exact ⟨log8_g17zp0e0_ev, log8_g17zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g18zm0e0_ev, log8_g18zm0e1_ev⟩
    · exact ⟨log8_g18zp0e0_ev, log8_g18zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g19zm0e0_ev, log8_g19zm0e1_ev⟩
    · exact ⟨log8_g19zp0e0_ev, log8_g19zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g20zm0e0_ev, log8_g20zm0e1_ev⟩
    · exact ⟨log8_g20zp0e0_ev, log8_g20zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g21zm0e0_ev, log8_g21zm0e1_ev⟩
    · exact ⟨log8_g21zp0e0_ev, log8_g21zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g22zm0e0_ev, log8_g22zm0e1_ev⟩
    · exact ⟨log8_g22zp0e0_ev, log8_g22zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g23zm0e0_ev, log8_g23zm0e1_ev⟩
    · exact ⟨log8_g23zp0e0_ev, log8_g23zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g24zm0e0_ev, log8_g24zm0e1_ev⟩
    · exact ⟨log8_g24zp0e0_ev, log8_g24zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g25zm0e0_ev, log8_g25zm0e1_ev⟩
    · exact ⟨log8_g25zp0e0_ev, log8_g25zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g26zm0e0_ev, log8_g26zm0e1_ev⟩
    · exact ⟨log8_g26zp0e0_ev, log8_g26zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g27zm0e0_ev, log8_g27zm0e1_ev⟩
    · exact ⟨log8_g27zp0e0_ev, log8_g27zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g28zm0e0_ev, log8_g28zm0e1_ev⟩
    · exact ⟨log8_g28zp0e0_ev, log8_g28zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g29zm0e0_ev, log8_g29zm0e1_ev⟩
    · exact ⟨log8_g29zp0e0_ev, log8_g29zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g30zm0e0_ev, log8_g30zm0e1_ev⟩
    · exact ⟨log8_g30zp0e0_ev, log8_g30zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g31zm0e0_ev, log8_g31zm0e1_ev⟩
    · exact ⟨log8_g31zp0e0_ev, log8_g31zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g32zm0e0_ev, log8_g32zm0e1_ev⟩
    · exact ⟨log8_g32zp0e0_ev, log8_g32zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g33zm0e0_ev, log8_g33zm0e1_ev⟩
    · exact ⟨log8_g33zp0e0_ev, log8_g33zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g34zm0e0_ev, log8_g34zm0e1_ev⟩
    · exact ⟨log8_g34zp0e0_ev, log8_g34zp0e1_ev⟩
  ·
    intro pos
    cases pos
    · exact ⟨log8_g35zm0e0_ev, log8_g35zm0e1_ev⟩
    · exact ⟨log8_g35zp0e0_ev, log8_g35zp0e1_ev⟩

theorem log8_last0 : Log8Group0 log8Last0 := by
  intro pos
  cases pos
  · exact ⟨log8_g36zm0e0_ev, log8_g36zm0e1_ev⟩
  · exact ⟨log8_g36zp0e0_ev, log8_g36zp0e1_ev⟩

theorem log8_all1 : ∀ g ∈ log8Grp1, Log8Group1 log8Lk g := by
  intro g hg
  simp only [log8Grp1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g0np0e0_ev, log8_g0np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl
      · exact ⟨log8_g0nm0e0_ev, log8_g0nm0e1_ev⟩
      · exact ⟨log8_g0nm1e0_ev, log8_g0nm1e1_ev⟩
      · exact ⟨log8_g0nm2e0_ev, log8_g0nm2e1_ev⟩
      · exact ⟨log8_g0nm3e0_ev, log8_g0nm3e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g1np0e0_ev, log8_g1np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g1nm0e0_ev, log8_g1nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g2np0e0_ev, log8_g2np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g2nm0e0_ev, log8_g2nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g3np0e0_ev, log8_g3np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g3nm0e0_ev, log8_g3nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g4np0e0_ev, log8_g4np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g4nm0e0_ev, log8_g4nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g5np0e0_ev, log8_g5np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g5nm0e0_ev, log8_g5nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g6np0e0_ev, log8_g6np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g6nm0e0_ev, log8_g6nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g7np0e0_ev, log8_g7np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g7nm0e0_ev, log8_g7nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g8np0e0_ev, log8_g8np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g8nm0e0_ev, log8_g8nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g9np0e0_ev, log8_g9np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g9nm0e0_ev, log8_g9nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g10np0e0_ev, log8_g10np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g10nm0e0_ev, log8_g10nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g11np0e0_ev, log8_g11np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g11nm0e0_ev, log8_g11nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g12np0e0_ev, log8_g12np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g12nm0e0_ev, log8_g12nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g13np0e0_ev, log8_g13np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g13nm0e0_ev, log8_g13nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g14np0e0_ev, log8_g14np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g14nm0e0_ev, log8_g14nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g15np0e0_ev, log8_g15np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g15nm0e0_ev, log8_g15nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g16np0e0_ev, log8_g16np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g16nm0e0_ev, log8_g16nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g17np0e0_ev, log8_g17np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g17nm0e0_ev, log8_g17nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g18np0e0_ev, log8_g18np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g18nm0e0_ev, log8_g18nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g19np0e0_ev, log8_g19np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g19nm0e0_ev, log8_g19nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g20np0e0_ev, log8_g20np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g20nm0e0_ev, log8_g20nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g21np0e0_ev, log8_g21np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g21nm0e0_ev, log8_g21nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g22np0e0_ev, log8_g22np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g22nm0e0_ev, log8_g22nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g23np0e0_ev, log8_g23np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g23nm0e0_ev, log8_g23nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g24np0e0_ev, log8_g24np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g24nm0e0_ev, log8_g24nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g25np0e0_ev, log8_g25np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g25nm0e0_ev, log8_g25nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g26np0e0_ev, log8_g26np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g26nm0e0_ev, log8_g26nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g27np0e0_ev, log8_g27np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g27nm0e0_ev, log8_g27nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g28np0e0_ev, log8_g28np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g28nm0e0_ev, log8_g28nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g29np0e0_ev, log8_g29np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g29nm0e0_ev, log8_g29nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g30np0e0_ev, log8_g30np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g30nm0e0_ev, log8_g30nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g31np0e0_ev, log8_g31np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g31nm0e0_ev, log8_g31nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g32np0e0_ev, log8_g32np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g32nm0e0_ev, log8_g32nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g33np0e0_ev, log8_g33np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g33nm0e0_ev, log8_g33nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g34np0e0_ev, log8_g34np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g34nm0e0_ev, log8_g34nm0e1_ev⟩
  ·
    refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g35np0e0_ev, log8_g35np0e1_ev⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl
      · exact ⟨log8_g35nm0e0_ev, log8_g35nm0e1_ev⟩

theorem log8_last1 : Log8Group1 log8Lk log8Last1 := by
  refine ⟨fun bn hb => ?_, fun bn hb => ?_⟩
  · simp only [log8Last1, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl
    · exact ⟨log8_g36np0e0_ev, log8_g36np0e1_ev⟩
  · simp only [log8Last1, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl
    · exact ⟨log8_g36nm0e0_ev, log8_g36nm0e1_ev⟩

end ExpansionBounds
