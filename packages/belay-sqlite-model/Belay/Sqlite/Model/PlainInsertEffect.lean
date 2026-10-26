import Belay.Sqlite.Model.SuccessfulScriptEffects
import Belay.Sqlite.Model.StatementRun
import Belay.Sqlite.Model.LiteralData
import Belay.Sqlite.Model.KeysUniqueWrites
import Belay.Sqlite.Model.ScriptRun

set_option doc.verso true

/-!
The effect of one plain INSERT of the model (ADR 0017, S6). A plain INSERT is a resolved insert
without a RETURNING clause, subqueries or trigger and foreign-key rules. The module shows what the
model's run of such a statement stores. A universal claim about an INSERT then needs only the rows
that the statement adds to the table, not the engine.
-/

namespace Belay.Sqlite.Model

/-- For every database, target, keys, table, supplied rows and result table: if the write of
the result succeeds, it gives the database with the rows of the result stored at the target.
Proof sketch: split the data-domain check and the checked write; each failing branch is an error,
and the successful branch stores the rows. -/
theorem insertOutcome_ok {database : Model.Database} {target : Nat} {keys : List UniqueKey}
    {table : Table} {rows : List (List Value)} {result : Table} {after : Model.Database}
    (ok : insertOutcome database target keys table rows result = .ok after) :
    after = database.setRows target result.rows := by
  unfold insertOutcome at ok
  split at ok
  · dsimp only at ok
    split at ok <;> cases ok
  · unfold checkedWrite at ok
    split at ok
    · cases ok; rfl
    · cases ok

/-- For every connection, plain insert and error-free step that continues: the next connection
has the database with the rows that {lit}`LiteralData.inserted` gives, stored at the target. The
statement context is that of the clock value of the step. Proof sketch:
{name}`runScriptStep_effect` gives the effect of the run, and {name}`insertOutcome_ok` reads it. -/
theorem plainInsert_database {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {target : Nat} {cells : List (List Resolved.Cell)} {after : ResolveState} {table : Table}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.insert target cells [] [] none, after))
    (present : connection.state.database.table target = some table)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (noError : output.isError = false) :
    ∃ value : Int, statementClock clock index (.insert target cells [] [] none) = some value ∧
      next.state.database = connection.state.database.setRows target
        (LiteralData.inserted table (Resolved.rowsAt (Resolved.statementContext value
          (connection.state.counters.view (Resolved.Statement.insert target cells [] [] none).counterReads)
          parameters connection.state.database []) table.shape.columns cells)).rows := by
  obtain ⟨value, database, timed, effect, nextEq⟩ :=
    runScriptStep_effect found (by simp [Resolved.Statement.isControl]) step noError
  refine ⟨value, timed, ?_⟩
  simp only [SqlState.statementRun, runStatement, present, StatementRun.withKeys, Option.map_none] at effect
  rw [nextEq, insertOutcome_ok effect]

/-- For every clock, statement values, state, run, transition, target and rule fields: the
output of a step of an insert is never a choice between results. Only a query step gives one.
Proof sketch: unfold the output and split on the halt reason; every remaining case gives rows,
a done count, an error or an unmodeled stop. -/
theorem Output.ofStep_insert_ne_oneOf (clock : Int) (parameters : List Value) (before : SqlState)
    (run : StatementRun) (transition : SqlTransition) (target : Nat) (rows returning subqueries rules)
    (alternatives : List (List (List Value))) :
    Output.ofStep clock parameters (.insert target rows returning subqueries rules) before run transition ≠
      .oneOf alternatives := by
  unfold Output.ofStep
  rcases haltError transition with _ | failure
  · dsimp only
    split
    · split <;> simp
    · simp
  · cases failure <;> simp

/-- Whether a step of a statement continues the run. The Boolean form lets a closed check compute it
for every clock and every counter, which an existence statement does not. -/
def RunStep.continues : RunStep → Bool
  | .continued .. => true
  | .ended _ => false

/-- For every step, it continues exactly when some output, next connection and list of further
executions give it. Proof sketch:
case split on the step. -/
theorem RunStep.continues_iff {step : RunStep} :
    step.continues = true ↔ ∃ output next others, step = .continued output next others := by
  cases step <;> simp [RunStep.continues]

/-- For every connection, statement that resolves to an insert, and step that continues: the output
of the step is not a choice between results. Proof sketch: {name}`runScriptStep_ran` gives the output
as {name}`Output.ofStep` of the resolved statement, which {name}`Output.ofStep_insert_ne_oneOf`
treats. -/
theorem runScriptStep_insert_ne_oneOf {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution} {target : Nat}
    {cells : List (List Resolved.Cell)} {returning subqueries rules} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.insert target cells returning subqueries rules, after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (alternatives : List (List (List Value))) : output ≠ .oneOf alternatives := by
  obtain ⟨resolved, later, value, same, -, -, -, outputEq, -⟩ := runScriptStep_ran step
  rw [found] at same
  cases same
  rw [outputEq]
  exact Output.ofStep_insert_ne_oneOf _ _ _ _ _ _ _ _ _ _ alternatives

end Belay.Sqlite.Model
