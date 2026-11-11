import Belay.Sqlite.Model.Shared.Execution.SqlExecution
import Belay.Sqlite.Model.Schema.Dispatch.Examples

set_option doc.verso true

/-! Examples of trigger definitions (ADR 0018, D5), checked when the package builds: CREATE
TRIGGER and its prepare errors, the namespace of trigger names, {lit}`IF NOT EXISTS`, DROP
TRIGGER, the triggers that DROP TABLE drops and {lit}`RAISE` outside a trigger. The authored corpus of
the slice checks the same rules against native SQLite; {lit}`TriggerRunExamples.lean` runs the
triggers. -/

namespace Belay.Sqlite.Model.TriggerExamples

open Belay.Sqlite.Model Syntax Resolution.Examples

/-- A column without a type and without constraints. -/
def plain (text : String) : ColumnDefinition := { name := Identifier.ofString text, declaredType := none, constraints := [] }

/-- {lit}`CREATE TABLE t(a)`. -/
def tableT : Syntax.Statement := .createTable (name! "t") [plain "a"] []

/-- {lit}`CREATE TRIGGER [IF NOT EXISTS] name AFTER INSERT ON table BEGIN DELETE FROM t; END`. -/
def trigger (name : String) (table : String := "t") (ifNotExists : Bool := false) : Syntax.Statement :=
  .createTrigger (Identifier.ofString name) ifNotExists .after .insert (Identifier.ofString table) none
    [.delete (name! "t") none]

/-- The names of the triggers of the catalog after the script, in catalog order. -/
def triggerNames (script : List Syntax.Statement) : List Identifier :=
  ((catalogOf (migration [] script)).filter (·.isTrigger)).map (·.name)

/-- The last resolved statement of the script. -/
def last (script : List Syntax.Statement) : Option Resolved.Statement := (statements (migration [] script)).getLast?

-- A trigger joins the catalog; its name may be the name of a table.
#guard triggerNames [tableT, trigger "r"] == [name! "r"]
#guard triggerNames [tableT, trigger "t"] == [name! "t"]
-- The prepare errors, in SQLite's order.
#guard last [trigger "r"] == some (.prepareError (.noSuchReferencedTable (name! "t")))
#guard last [tableT, trigger "sqlite_r"] == some (.prepareError (.expression (.reservedName (name! "sqlite_r"))))
#guard last [tableT, trigger "r", trigger "r"] == some (.prepareError (.triggerExists (name! "r")))
#guard last [tableT, trigger "r" "sqlite_master"] == some (.prepareError (.expression .triggerOnSystemTable))

-- IF NOT EXISTS of an existing trigger does nothing.
#guard last [tableT, trigger "r", trigger "r" (ifNotExists := true)] == some (.drop [])
#guard triggerNames [tableT, trigger "r", trigger "r" (ifNotExists := true)] == [name! "r"]

-- DROP TRIGGER removes the trigger; a missing one is an error, or nothing with IF EXISTS.
#guard triggerNames [tableT, trigger "r", .dropTrigger (name! "r") false] == []
#guard last [tableT, .dropTrigger (name! "r") false] == some (.prepareError (.noSuchTrigger (name! "r")))
#guard last [tableT, .dropTrigger (name! "r") true] == some (.drop [])

-- DROP TABLE drops the triggers of its table.
#guard catalogOf (migration [] [tableT, trigger "r", .dropTable (name! "t") false]) == []

-- RAISE outside a trigger is a prepare error.
#guard last [.select [.expression (.raise .ignore none) none "RAISE(IGNORE)"] none [] none [] [] none none] ==
  some (.prepareError (.expression .raiseOutsideTrigger))

end Belay.Sqlite.Model.TriggerExamples
