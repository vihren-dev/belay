import Belay.Sqlite.Model.ScriptRun
import Belay.Sqlite.Model.Resolution.Examples

set_option doc.verso true

/-! Examples of {name}`Belay.Sqlite.Model.runScriptFrom`, checked by {lit}`#guard` when the
package builds. They check that the run goes on after an error, as SQLite does: a failed INSERT
and a later query, an error in a transaction and a later COMMIT, {lit}`OR ROLLBACK`, which ends
the transaction, a query of a dropped table, which SQLite refuses to prepare, and a statement
that reads the clock or random values, which ends the run. -/

namespace Belay.Sqlite.Model.ScriptRunExamples

open Belay.Sqlite.Model Syntax Resolution.Examples

/-- A run of the statements from the empty database, with the default profile. -/
def outputs (script : List Syntax.Statement) : List Output :=
  (runScriptFrom { profile := defaults, mode := .execution } 0 { state := { database := {} } } script).outputs

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

end Belay.Sqlite.Model.ScriptRunExamples
