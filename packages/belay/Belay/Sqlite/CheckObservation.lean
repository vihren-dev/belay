import Belay.Sqlite.CheckReplayData
import Belay.Sqlite.CheckClaim

set_option doc.verso true

/-! The failing observation of a refuted claim about programs: which run of the program fails the claim,
or how the runs of two programs differ. The text comes from the model's run at the witness. The checker
has already certified the refutation, so this text explains the witness and proves nothing. -/

namespace Belay.Sqlite

/-- What a report shows of a run: whether the program returned a value, and the outputs of its statements. -/
def Sql.runSummary {α : Type} (program : Sql α) (state : ExecutionContext) : Bool × List Output :=
  let run := program.runFrom state.clock state.index state.connection
  (run.value.isSome, run.outputs)

/-- The check of a program at one run: the actual run of the program from the context must return a value that
satisfies the postcondition at the context that the run reaches. This is the check of {name}`Sql.check`
restricted to the actual branch, so a failure here is a failure of that check. -/
def Sql.checkActual {α : Type} (program : Sql α) (post : α → ExecutionContext → Prop)
    (state : ExecutionContext) : Prop :=
  match (program.runFrom state.clock state.index state.connection).value with
  | none => False
  | some value => post value (state.finish (program.runFrom state.clock state.index state.connection))

/-- The check of the actual run is decidable when the postcondition is. -/
instance Sql.decidableCheckActual {α : Type} (program : Sql α) (post : α → ExecutionContext → Prop)
    [∀ value state, Decidable (post value state)] (state : ExecutionContext) :
    Decidable (program.checkActual post state) := by
  unfold Sql.checkActual
  split <;> infer_instance

end Belay.Sqlite

namespace Belay.Sqlite.Check
open Lean Meta Elab Term

/-- Text for the outputs and the result of one run. -/
private def runText (summary : Bool × List Output) : String :=
  s!"{if summary.1 then "returns a value" else "returns no value"}; outputs {reprStr summary.2}"

/-- Decode the summary of the run of a program at a context. -/
private def summaryOf (program state : Expr) (excluded : Array Name) (excludedLocals : Array FVarId) :
    TermElabM (Bool × List Output) := do
  let _ := outputExprInstance
  let type ← inferType program
  let α := type.appArg!
  dataValue (Bool × List Output) (mkApp3 (mkConst ``Sql.runSummary) α program state) excluded excludedLocals

/-- A line that names the initial database of the run, when the claim fixes a database other than the one of
the witness. A claim about one named context, such as an initial context of a named database, ignores the
database of the witness, so the line says where the runs start. -/
private def initialLine (state witnessDatabase : Expr) : MetaM String := do
  let some database ← initialDatabase? (← instantiateMVars state) | return ""
  if database == witnessDatabase then return ""
  return s!"Initial database of the run: {(← ppExpr database).pretty}.\n"

/-- Say which run of a program fails its check. The actual run is decided in the kernel. When the actual run
satisfies the postcondition, the check fails on another branch, which exists only for a statement whose output is
a choice among results. None when the postcondition has no decision procedure. -/
private def checkText (program post state witnessDatabase : Expr) (excluded : Array Name)
    (excludedLocals : Array FVarId) : TermElabM (Option String) := do
  let α := (← inferType program).appArg!
  let actual := mkApp4 (mkConst ``Sql.checkActual) α program post state
  let summary ← summaryOf program state excluded excludedLocals
  let shown := s!"{← initialLine state witnessDatabase}Run of the program: {runText summary}."
  if (← attempt (decideCertified (mkNot actual) excluded excludedLocals)).isSome then
    return some s!"The check fails on the actual run of the program.\n{shown}"
  if (← attempt (decideCertified actual excluded excludedLocals)).isSome then
    return some s!"The check holds on the actual run of the program and fails on another branch. A branch other than the actual run exists when a statement has an output that is a choice among results.\n{shown}"
  return some s!"The postcondition has no decision procedure, so the failing branch is not shown.\n{shown}"

/-- Say how the actual runs of two programs differ. When the value and the outputs are equal, the runs differ
in the connection that they leave, and the text says so. The model decides this difference, and a replay in
SQLite shows only the outputs. -/
private def relationText (first second state witnessDatabase : Expr) (excluded : Array Name)
    (excludedLocals : Array FVarId) : TermElabM String := do
  let one ← summaryOf first state excluded excludedLocals
  let other ← summaryOf second state excluded excludedLocals
  let shown := s!"{← initialLine state witnessDatabase}First program: {runText one}.\nSecond program: {runText other}."
  if one == other then
    return s!"The actual runs of the two programs differ at this context in the connection that they leave: they return the same value and the same outputs.\n{shown}"
  return s!"The actual runs of the two programs differ at this context.\n{shown}"

/-- Apply the claim to the witness and describe the failing observation of the conclusion: the run that fails
a check, or the runs that differ. None when the conclusion is neither. -/
def failingObservation (proposition : Expr) (witness : Witness) (excluded : Array Name := #[])
    (excludedLocals : Array FVarId := #[]) (fuel : Nat := 64) : TermElabM (Option String) :=
  visit fuel proposition
where
  /-- Strip premises and fill the other binders from the witness, unfolding named claims, down to a conclusion. -/
  visit : Nat → Expr → TermElabM (Option String)
    | 0, _ => pure none
    | fuel + 1, claim => do
      checkSystem "SQL failing observation"
      match claim with
      | .mdata _ body => visit fuel body
      | .letE _ _ value body _ => visit fuel (body.instantiate1 value)
      | .forallE name domain body _ =>
        if ← isProp domain then
          withLocalDeclD name domain fun input => visit fuel (body.instantiate1 input)
        else visit fuel (body.instantiate1 (← witness.choose name domain))
      | _ =>
        let head := claim.getAppFn
        let arguments := claim.getAppArgs
        if head.isConstOf ``Sql.check && arguments.size == 4 then
          return ← checkText arguments[1]! arguments[2]! arguments[3]! witness.database excluded excludedLocals
        if programRelationNames.any head.isConstOf && arguments.size ≥ 4 then
          return some (← relationText arguments[1]! arguments[2]! arguments.back! witness.database excluded excludedLocals)
        if head.isLambda then return ← visit fuel (head.beta arguments)
        let .const name levels := head | return none
        let some info := (← getEnv).find? name | return none
        let some body := info.value? | return none
        if ← isProp claim then
          visit fuel ((body.instantiateLevelParams info.levelParams levels).beta arguments)
        else return none

/-- The text for a refuted claim, when the claim and the budget allow it. The text may use the budget that is
left, and a failure to make it leaves the refutation as it is. -/
def observeFailure (proposition : Expr) (witness : Witness) (excluded : Array Name := #[])
    (excludedLocals : Array FVarId := #[]) : TermElabM (Option String) := do
  let shown ← withinBudget ((← remainingUnits)) <|
    attempt (failingObservation proposition witness excluded excludedLocals)
  return (shown.bind id).bind id

end Belay.Sqlite.Check
