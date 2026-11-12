import Belay.Sqlite.Model.Schema.Writes.CounterExamples
import Belay.Sqlite.Model.Schema.Triggers.TriggerRunExamples
import Belay.Sqlite.Model.Queries.Preparation.ForeignKeyExamples
import Belay.Sqlite.Model.Schema.ForeignKeys.ForeignKeyExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.CounterRowExamples

open Belay.Sqlite.Model Syntax Resolution.Examples TriggerRunExamples

/-- {lit}`INSERT INTO log VALUES (0), (0), (0)`: the table {lit}`log` has the rowids 1 to 3. -/
def logThree : Syntax.Statement := .insert (name! "log") none [[.numeric "0"], [.numeric "0"], [.numeric "0"]] []

/-- {lit}`INSERT INTO t VALUES (NULL, 7)`. -/
def insertSeven : Syntax.Statement := insertT [[.null, .numeric "7"]]

/-- The trigger of {lit}`t` that runs the body after each INSERT, if {lit}`new.v = 8` when the flag is set. -/
def afterInsert (body : List BodyStatement) (onlyEight : Bool := false) : Syntax.Statement :=
  trigger "a" .after .insert body (if onlyEight then some (.compare .eq (column "new" "v") (.numeric "8")) else none)

/-- {lit}`CREATE TABLE p(id PRIMARY KEY)`, {lit}`CREATE TABLE c(x REFERENCES p)`, the rows 1 and 2 of
{lit}`p` and the row 1 of {lit}`c`: the schema of {name}`ForeignKeyExamples.schema` without actions. -/
def plainSchema : List Syntax.Statement := ForeignKeyExamples.schema .noAction .noAction

/-- {lit}`INSERT INTO c VALUES (value), ...`. -/
def insertChildren (values : List String) : Syntax.Statement :=
  .insert (name! "c") none (values.map fun value => [.numeric value]) []

/-- {lit}`PRAGMA recursive_triggers = ON`: the DELETE of a REPLACE fires its triggers. -/
def recursiveOn : Profile := { defaults with recursiveTriggers := true }

/-- {lit}`INSERT OR REPLACE INTO t VALUES (1, 'b')` after the row {lit}`(1, 'a')`, and the trigger
{lit}`AFTER DELETE ON t` with the body. -/
def replaceWithDeleteTrigger (body : List BodyStatement) : List Syntax.Statement :=
  tables ++ [insertT [[.numeric "1", text "a"]], trigger "d" .after .delete body,
    insertT [[.numeric "1", text "b"]] (some .replace)]

end Belay.Sqlite.Model.CounterRowExamples
