import Belay.Sqlite.Model.ScriptRun
import Belay.Sqlite.Model.Resolution.Examples

set_option doc.verso true

/-! Examples of {name}`Belay.Sqlite.Model.runScriptFrom`, checked by {lit}`#guard` when the
package builds. They check that the run goes on after an error, as SQLite does: a failed INSERT
and a later query, an error in a transaction and a later COMMIT, {lit}`OR ROLLBACK`, which ends
the transaction, a query of a dropped table, which SQLite refuses to prepare, a failed
{lit}`ADD COLUMN`, which leaves the catalog as it was, the results of {lit}`LIMIT 1` without
{lit}`ORDER BY`, a statement that reads the clock or random values, which ends the run, and
statements that read the values bound to their parameters. -/

namespace Belay.Sqlite.Model.ScriptRunExamples

open Belay.Sqlite.Model Syntax Resolution.Examples

/-- A run of the statements from the empty database, with the default profile; statement
{lit}`i` gets item {lit}`i` of {lit}`values` ({name}`bindValues`). -/
def outputs (script : List Syntax.Statement) (values : List (List Value) := []) : List Output :=
  (runScriptFrom { profile := defaults, mode := .execution } 0 { state := { database := {} } }
    (bindValues script values)).outputs

/-- {lit}`CREATE TABLE t(id INTEGER PRIMARY KEY, name TEXT)`. -/
def createT : Syntax.Statement :=
  .createTable (name! "t")
    [{ name := name! "id", declaredType := some "INTEGER", constraints := [.primaryKey false] },
      column (name! "name")] []

/-- {lit}`INSERT INTO t VALUES (id, name)`, with the algorithm of {lit}`INSERT OR algorithm`. -/
def insertT (id : String) (text : String) (algorithm : Option ConflictAlgorithm := none) : Syntax.Statement :=
  .insert (name! "t") none [[.numeric id, .string text.toUTF8.toList]] [] algorithm

/-- {lit}`SELECT name FROM t`. -/
def selectNames : Syntax.Statement :=
  .select [.expression (.identifier (name! "name") .none) none ""] (some { table := name! "t", alias := none })
    [] none [] [] none none

/-- A text value. -/
def textValue (text : String) : Value := .text text.toUTF8.toList

-- A failed INSERT gives error 19 (SQLITE_CONSTRAINT); the query after it runs.
#guard outputs [createT, insertT "1" "a", insertT "1" "b", selectNames] ==
  [.done 0, .done 1, .error 19, .rows [[textValue "a"]]]

-- Each statement reads its own values: the INSERT stores ?2 of its list, and the query's ?1 of
-- its list; a number without an item is NULL. A trigger body reads none.
#guard outputs [createT, .insert (name! "t") none [[.parameter 1, .parameter 2]] [],
    .select [.expression (.parameter 1) none "", .expression (.parameter 2) none ""] none [] none [] [] none none,
    selectNames]
    [[], [.integer 1, textValue "a"], [.integer 7]] ==
  [.done 0, .done 1, .rows [[.integer 7, .null]], .rows [[textValue "a"]]]

-- A bound NaN REAL is NULL, as SQLite binds it.
#guard outputs [.select [.expression (.parameter 1) none ""] none [] none [] [] none none]
    [[.real 0x7FF8000000000000]] == [.rows [[.null]]]

-- An error in a transaction keeps the transaction open: COMMIT succeeds and keeps the first row.
#guard outputs [createT, .begin, insertT "1" "a", insertT "1" "b", .commit, selectNames] ==
  [.done 0, .done 0, .done 1, .error 19, .done 0, .rows [[textValue "a"]]]

-- OR ROLLBACK rolls back the transaction: COMMIT fails with error 1, and no row is left.
#guard outputs [createT, .begin, insertT "1" "a", insertT "1" "b" (some .rollback), .commit, selectNames] ==
  [.done 0, .done 0, .done 1, .error 19, .error 1, .rows []]

-- A query of a dropped table: SQLite refuses to prepare it, with error 1.
#guard outputs [createT, .dropTable (name! "t") false, selectNames] == [.done 0, .done 0, .error 1]

-- A statement that reads the clock ends the run; the statements after it do not run.
#guard outputs [.select [.expression (.currentTime "CURRENT_TIMESTAMP") none ""] none [] none [] [] none none,
  selectNames] == [.unmodeled clockUnmodeled]

-- random() is a restriction of the model: the run ends at it with the restriction's reason.
#guard match outputs [.select [.expression (.call "random" []) none ""] none [] none [] [] none none, selectNames] with
  | [.unmodeled _] => true
  | _ => false

-- A failed ADD COLUMN leaves the catalog as it was: a later query of the new column is a
-- prepare error (error 1), because the run resolves it against the database's catalog.
#guard outputs [createT, insertT "1" "a",
  .addColumn (name! "t") { name := name! "c", declaredType := some "INTEGER", constraints := [.notNull] },
  .select [.expression (.identifier (name! "c") .none) none ""] (some { table := name! "t", alias := none })
    [] none [] [] none none] == [.done 0, .done 1, .error 1, .error 1]

/-- {lit}`SELECT expression FROM t LIMIT 1`. -/
def firstOf (expression : Expr) : Syntax.Statement :=
  .select [.expression expression none ""] (some { table := name! "t", alias := none }) [] none [] []
    (some (.numeric "1")) none

-- LIMIT 1 without ORDER BY: SQLite may give either row, so the output is oneOf.
#guard outputs [createT, insertT "1" "b", insertT "2" "a", firstOf (.identifier (name! "name") .none)] ==
  [.done 0, .done 1, .done 1, .oneOf [[[textValue "a"]], [[textValue "b"]]]]

-- When every possible result is the same, the output is rows.
#guard outputs [createT, insertT "1" "b", insertT "2" "a", firstOf (.numeric "1")] ==
  [.done 0, .done 1, .done 1, .rows [[.integer 1]]]

-- Equal results count once, the results are sorted, and no result is unmodeled.
#guard Output.ofResults [[[.integer 1]], [[.integer 1]]] == .rows [[.integer 1]]
#guard Output.ofResults [[[.integer 2]], [[.integer 1]], [[.integer 2]]] == .oneOf [[[.integer 1]], [[.integer 2]]]
#guard Output.ofResults [] == .unmodeled "the model gives no result for this query"

end Belay.Sqlite.Model.ScriptRunExamples
