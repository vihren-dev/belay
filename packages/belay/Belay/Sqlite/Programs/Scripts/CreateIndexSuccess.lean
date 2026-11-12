import Belay.Sqlite.Programs.Scripts.ScriptSuccess

set_option doc.verso true

namespace Belay.Sqlite

open Belay.Sqlite Belay.Sqlite.Model

/-- For every one-statement CREATE INDEX script, with or without {lit}`IF NOT EXISTS`
({lit}`ifNotExists`), database and environment, its public run has neither an error nor an
ending output exactly when one of these holds:

* the clause is present and the statement is a no-op ({name}`createIndexKept`: the table
  exists, no name is reserved, and an index has the name);
* the table and name checks, term and filter resolution, and required uniqueness all hold
  ({name}`CreateIndexConditions`). A nonunique index requires no uniqueness of rows.

Without the clause only the second item can hold. Proof sketch: validity aligns the row
lists with the catalog; the shared model step law gives the only output of this script. -/
theorem Script.createIndex_allOk_iff {script : Script} {name tableName : Identifier}
    {unique : Bool} {terms : List Syntax.OrderTerm} {filter : Option Syntax.Expr} {ifNotExists : Bool}
    {parameters : List Value}
    (head : script.statements = [(.createIndex name unique tableName terms filter ifNotExists, parameters)])
    (db : Database) (env : Env) :
    (db.run script env).outputs.allOk = true ↔
      (ifNotExists = true ∧ createIndexKept db.raw.catalog name tableName = true) ∨
        CreateIndexConditions runContext db.raw name unique tableName terms filter := by
  rw [Script.run_outputs, head]
  have output := runScriptStep_createIndex_ok_iff runContext env.clock 0
    (db.raw.connection env.counters) parameters name tableName unique terms filter ifNotExists
    db.valid.admitted.rowsShaped.1
  change _ ↔ (ifNotExists = true ∧ createIndexKept db.raw.catalog name tableName = true) ∨
    CreateIndexConditions runContext db.raw name unique tableName terms filter at output
  cases step : runScriptStep runContext env.clock 0 (db.raw.connection env.counters)
      (.createIndex name unique tableName terms filter ifNotExists) parameters <;>
    simpa [runScriptFrom, step, RunStep.output, List.allOk, Output.isError, Output.endsRun] using output

/-- For every one-statement CREATE INDEX script, with or without {lit}`IF NOT EXISTS`, and
database predicate, the script succeeds exactly when every database satisfying the predicate
has a no-op statement (the clause is present and {name}`createIndexKept` holds) or meets
{name}`CreateIndexConditions`. Both sides hold when no database satisfies the predicate. Proof sketch: the preceding
output equivalence holds in every environment; one complete environment supplies the
necessary direction, and the same conditions supply every environment for the converse. -/
theorem Succeeds.iff_createIndex {script : Script} {name tableName : Identifier}
    {unique : Bool} {terms : List Syntax.OrderTerm} {filter : Option Syntax.Expr} {ifNotExists : Bool}
    {parameters : List Value}
    (head : script.statements = [(.createIndex name unique tableName terms filter ifNotExists, parameters)])
    (predicate : Database → Prop) :
    Succeeds script predicate ↔ ∀ db, predicate db →
      (ifNotExists = true ∧ createIndexKept db.raw.catalog name tableName = true) ∨
        CreateIndexConditions runContext db.raw name unique tableName terms filter := by
  rw [Succeeds.script_iff script predicate (by simp [head, Syntax.Statement.isInsertSelect])]
  simp only [Script.createIndex_allOk_iff head]
  constructor
  · intro success db holds
    exact success db holds { Env.atTime 0 with counters := Counters.newConnection } ⟨rfl, rfl, rfl, rfl⟩
  · intro conditions db holds _ _
    exact conditions db holds

end Belay.Sqlite
