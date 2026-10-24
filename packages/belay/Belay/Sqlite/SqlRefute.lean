import Lean.Elab.Tactic.Basic
import Belay.Sqlite.CounterexampleWitness

set_option doc.verso true

namespace Belay.Sqlite

open Lean Elab Tactic Meta

/-- Refute a universal claim with a supplied database and optional named inputs.
For example, {lit}`sql_refute (db := Database.empty)` refutes a claim that every
database contains a row in a named table. An input {lit}`(env := environment)` supplies
an execution environment; other names match the claim's quantified binders.
Every precondition and the final refutation are checked, rather than assumed. -/
syntax (name := sqlRefuteWitness) "sql_refute" "(" ident ":=" term ")"
  ("(" ident ":=" term ")")* : tactic

/-- Elaborate witness inputs without Lean's error-to-sorry recovery. The certification
boundary checks the resulting terms again, including dependencies of named constants. -/
private def witnessInput (stx : Syntax) (expected : Option Expr := none) : TacticM Expr :=
  Term.withoutErrToSorry do
    let value ← Term.elabTerm stx expected
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars value

/-- Apply the explicit witness selector to a negated proposition and assign only its
certified proof. Incorrect inputs leave the original goal unproved. -/
@[tactic sqlRefuteWitness]
def elabSqlRefuteWitness : Tactic := fun stx => do
  let `(tactic| sql_refute ($databaseName:ident := $database) $[($names:ident := $values:term)]*) := stx
    | throwUnsupportedSyntax
  unless databaseName.getId == `db do
    throwErrorAt databaseName "the first sql_refute input must be (db := database)"
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let some proposition := target.not? | throwError "sql_refute expects a goal of the form ¬ P"
    let mut witness : Check.Witness := { database := ← witnessInput database (some (mkConst ``Database)) }
    for name in names, value in values do
      if name.getId == `env then
        witness := { witness with environment := ← witnessInput value (some (mkConst ``Env)) }
      else
        witness := { witness with named := witness.named.push (name.getId, ← witnessInput value) }
    let proof ← Check.refuteWitness proposition witness
    goal.assign proof
  replaceMainGoal []

end Belay.Sqlite
