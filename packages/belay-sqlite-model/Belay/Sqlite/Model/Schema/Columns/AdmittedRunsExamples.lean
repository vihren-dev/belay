import Belay.Sqlite.Model.Schema.Rows.ScriptRunValid
import Belay.Sqlite.Model.Schema.Ddl.AdmittedAtomsSchemaExamples
import Belay.Sqlite.Model.Schema.Rows.AdmittedAtomsCounterExamples
import Belay.Sqlite.Model.Queries.Preparation.ForeignKeyExamples
import Belay.Sqlite.Model.Schema.ForeignKeys.ForeignKeyExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.AdmittedRunsExamples

open Belay.Sqlite.Model Syntax
open Belay.Sqlite.Model.ForeignKeyExamples (keysOn deleteOne)
open Belay.Sqlite.Model.AdmittedAtomsSchemaExamples (createT term triggerOnT)

/-- {lit}`CREATE UNIQUE INDEX ia ON t(a)`. -/
def uniqueIndex : Syntax.Statement := .createIndex (name! "ia") true (name! "t") [term (name! "a")] none

/-- {lit}`ALTER TABLE t ADD COLUMN c INTEGER DEFAULT 5`. -/
def addFive : Syntax.Statement :=
  .addColumn (name! "t") { name := name! "c", declaredType := some "INTEGER", constraints := [.default (.numeric "5") "5"] }

/-- With foreign keys on: the tables {lit}`p` and {lit}`c` of {lit}`ForeignKeyExamples` with their rows
({lit}`ON DELETE CASCADE`), then {lit}`CREATE TABLE t(a INTEGER, b TEXT)`, one row of {lit}`t`, a unique index
and a trigger on {lit}`t`, ADD COLUMN, {lit}`BEGIN`, the DELETE of the row 1 of {lit}`p`, which deletes the row
of {lit}`c`, {lit}`DROP TABLE t` (with its index and its trigger), and {lit}`ROLLBACK`. -/
def mixedSyntax : List Syntax.Statement :=
  ForeignKeyExamples.schema .cascade .noAction ++
    [createT, .insert (name! "t") none [[.numeric "1", .numeric "2"]] [], uniqueIndex, triggerOnT, addFive,
      .begin, deleteOne, .dropTable (name! "t") false, .rollback]

/-- The context of the run: the profile with foreign keys on, in execution mode. -/
def mixedContext : ResolveContext := { profile := keysOn, mode := .execution }

end Belay.Sqlite.Model.AdmittedRunsExamples
