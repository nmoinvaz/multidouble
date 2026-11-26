import ExpansionBounds.Trig12
import Controls.Axioms

/-!
# Controls of the remark after Theorem 35: the bounds at `n = 12`

Each claim below is one of the kernel's checks of `Trig12.lean` with a bound one unit lower in its
last digit, in the run of buckets where it is largest, or with a bound on `κ_DIV` one unit lower, and the kernel
proves its negation. The table is outside the default build, so the audit of
`Controls/Axioms.lean` is repeated here with its modules. This file is written by `trig_lean.py`.
-/

namespace ExpansionBounds

open Finset

set_option maxHeartbeats 4000000 in
/-- at `n = 12`, `C` in bucket 0 is not below `3582.787310u^12` -/
example : ¬ trigCQ trig8U 12 (sinDeltaL trig8U 12 (upQ 200) trig8Ab (trig8Rb 0) 56 (dySt trig12_s0_54))
    (cosDeltaL trig8U 12 (upQ 200) trig8Ab (trig8Rb 0) 57 (dySt trig12_c0_55)) (trig8Rb 0) ≤
      3582787310 / 1000000 * trig8U ^ 12 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- at `n = 12`, the tangent's check in bucket 0 fails with `4929.367334u^12` -/
example : ¬ trig12Tab.TanOk (4929367334 / 1000000) trig12Kd0 trig12Kd3 0 56 57 (dySt trig12_s0_54)
    (dySt trig12_c0_55) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- at `n = 12`, `κ_DIV(1.4143u)` is not within `18515926076196` -/
example : ¬ trig12Tab.KdivOk 18515926076196 trig12Kd3 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- at `n = 12`, `κ_DIV(3u)` is not within `72548256175783` -/
example : ¬ trig12Tab.KdivOk trig12Kd0 72548256175783 := by
  decide +kernel

end ExpansionBounds

open Lean Elab Command in
run_cmd liftCoreM do
  let decls ← Controls.proofDecls
  unless decls.contains ``ExpansionBounds.thm35_sincos_12 && decls.contains ``ExpansionBounds.thm35_tan_12 do
    throwError "the theorems at n = 12 are not among the declarations read"
  let mut bad : Array (Name × Array Name) := #[]
  for c in decls do
    let ax ← Controls.otherAxioms c
    unless ax.isEmpty do bad := bad.push (c, ax)
  unless bad.isEmpty do
    throwError "declarations with other axioms: {bad}"
  logInfo m!"{decls.size} declarations with Trig12: no axiom other than propext, Classical.choice and Quot.sound"
