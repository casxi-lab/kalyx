import Kalyx
set_option pp.privateNames true

example : Kalyx.Statements.Counter.S := Kalyx.Proofs.Counter.t
example : Kalyx.Proofs.Other.P := Kalyx.Proofs.Other.v
example : Kalyx.Statements.Counter.Missing := Kalyx.Proofs.Counter.s
example : Kalyx.Statements.Counter.W := Kalyx.Proofs.Coerced.c

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleOf : Name → Name := fun n =>
    ((env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!)).getD .anonymous
  let planned : Array Name := #[`Kalyx.Proofs.Other.u]
  let own : Array Name := #[`Kalyx.HB.Fixture, `Kalyx.Proofs.Coerced, `Kalyx.Proofs.Counter, `Kalyx.Proofs.Other, `Kalyx.Qualification.Arithmetic, `Kalyx.Qualification.Checked, `Kalyx.Qualification.Models.Arc, `Kalyx.Qualification.Models.FromStr, `Kalyx.Qualification.SingleLoop, `Kalyx.Spec.Counter, `Kalyx.Statements.Counter]
  for (module, data) in env.header.moduleNames.zip env.header.moduleData do
    unless own.contains module do continue
    logInfo m!"kalyx-audit module {module}"
    for decl in data.constNames do
      let some (.thmInfo _) := env.find? decl | continue
      unless isPrivateName decl || decl.isInternalDetail || planned.contains decl do
        elabCommand (← `(#print axioms $(mkIdent decl)))
        for ax in ← collectAxioms decl do
          if ax.components.contains `_native then
            logInfo m!"kalyx-audit native {ax} {moduleOf ax}"
      if let some ranges ← findDeclarationRanges? decl then
        logInfo m!"kalyx-audit range {decl} {ranges.range.pos.line}"
  for (statement, thm) in (#[(`Kalyx.Statements.Counter.S, `Kalyx.Proofs.Counter.t), (`Kalyx.Proofs.Other.P, `Kalyx.Proofs.Other.v), (`Kalyx.Statements.Counter.Missing, `Kalyx.Proofs.Counter.s), (`Kalyx.Statements.Counter.W, `Kalyx.Proofs.Coerced.c)] : Array (Name × Name)) do
    let exact := (env.find? thm).any fun c => c.isTheorem && c.type == mkConst statement
    logInfo m!"kalyx-audit statement {statement} {moduleOf statement} {exact}"
