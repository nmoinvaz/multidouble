import ExpansionBounds

/-!
# The axioms of every declaration

No declaration of the modules `ExpansionBounds.*` depends on an axiom other than `propext`, `Classical.choice` and
`Quot.sound`. Lean records the axioms of each declaration when its module is built; this file reads them for every
declaration and fails the build on any other. So no proof rests on `sorry` or on `native_decide`. The control is a
theorem proved from an axiom declared here, which the same test must report.
-/

open Lean Elab Command

namespace Controls

/-- the axioms of `c` other than Lean's three -/
def otherAxioms (c : Name) : CoreM (Array Name) :=
  return (← collectAxioms c).filter fun a => a ∉ [``propext, ``Classical.choice, ``Quot.sound]

/-- the declarations of the modules `ExpansionBounds.*`, the generated ones included -/
def proofDecls : CoreM (Array Name) := do
  let env ← getEnv
  -- `moduleNames` builds its array at each call
  let mods := env.header.moduleNames
  return env.constants.fold (init := #[]) fun acc c _ =>
    match env.getModuleIdxFor? c with
    | some i => if (`ExpansionBounds).isPrefixOf mods[i.toNat]! then acc.push c else acc
    | none => acc

/-- an axiom for the control: it states nothing new -/
axiom controlAxiom : (0 : Nat) = 0

/-- a theorem that rests on it -/
theorem controlTheorem : (0 : Nat) = 0 := controlAxiom

run_cmd liftCoreM do
  unless (← otherAxioms ``controlTheorem) == #[``controlAxiom] do
    throwError "the control failed: the axiom under controlTheorem is not reported"
  let decls ← proofDecls
  let mut bad : Array (Name × Array Name) := #[]
  for c in decls do
    let ax ← otherAxioms c
    unless ax.isEmpty do bad := bad.push (c, ax)
  unless bad.isEmpty do
    throwError "declarations with other axioms: {bad}"
  if decls.size < 1000 then
    throwError "only {decls.size} declarations found"
  logInfo m!"{decls.size} declarations of ExpansionBounds: no axiom other than propext, Classical.choice and Quot.sound"

end Controls
