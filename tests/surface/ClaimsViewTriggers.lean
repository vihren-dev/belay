import ViewsSupport

set_option doc.verso true
set_option maxRecDepth 8000
set_option maxHeartbeats 800000

/-! Stored views can see trigger NEW/OLD rows. The resolver and expression
context must retain their offsets after an UPDATE/DELETE target's columns.
These checks do not claim that keyReady admits nested writes with subqueries. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open ViewExamples

namespace ViewTriggerExamples

/-- A three-column target makes a displaced trigger cell observable. -/
def base : Database := db! r"
  CREATE TABLE log(a,b,c); INSERT INTO log VALUES(900,800,700);
  CREATE TABLE source(x); INSERT INTO source VALUES(7);"

/-- View bodies use trigger names only at their eventual use sites. -/
def database : Database := ⟨withViews base [
  (name! "new_row", definition (sql r"SELECT new.x AS value")),
  (name! "old_row", definition (sql r"SELECT old.x AS value")),
  (name! "total", definition (sql r"SELECT new.x+old.x AS value")),
  (name! "closed", definition (sql r"SELECT x FROM source"))], by decide +kernel⟩

/-- The trigger source has one column; the event chooses the available pseudo-rows. -/
def trigger (new old : Bool) : TriggerRow :=
  {columns := [{name := name! "x", declaredType := none}], new, old}

/-- Prepare a SELECT body and run its indexed queries on the supplied trigger
cells. The result includes fault and ending checks through exact equality. -/
def readRows (script : Script) (row : TriggerRow) (cells : List Value) :
    Option (List (List Value) × Resolved.Fault × Resolved.RunEnd) :=
  let view := definition script
  match bodyStep (resolveBodySelect runContext database.catalog row view.query view.subqueries) with
  | .ok (.ok (.query query subqueries)) =>
    let context := Resolved.statementContext 0 {} [] database.raw subqueries
    let result := query.subqueryRun context database.raw cells
    some (result.rows, result.fault, result.ending)
  | .error _ | .ok (.error _) | .ok (.ok (.insert ..)) | .ok (.ok (.update ..))
  | .ok (.ok (.delete ..)) | .ok (.ok (.raise ..)) => none

/-- A stored NEW reference resolves and reads the INSERT row. -/
example : readRows (sql r"SELECT value FROM new_row") (trigger true false) [.integer 100] =
    some ([[.integer 100]], .none, .done) := by decide +kernel

/-- A short supplied outer row retains the evaluator's NULL-padding contract. -/
example : readRows (sql r"SELECT value FROM new_row") (trigger true false) [] =
    some ([[.null]], .none, .done) := by decide +kernel

/-- A stored OLD reference reads the UPDATE event's second pseudo-row. -/
example : readRows (sql r"SELECT value FROM old_row") (trigger true true) [.integer 100,.integer 7] =
    some ([[.integer 7]], .none, .done) := by decide +kernel

/-- A normal view source keeps local cells after the trigger prefix. -/
example : readRows (sql r"SELECT x FROM closed") (trigger true false) [.integer 100] =
    some ([[.integer 7]], .none, .done) := by decide +kernel

/-- Convert only UPDATE/DELETE fixtures to their trigger-body syntax. Other
statement families return none and cannot make the value assertions pass. -/
def writeBody (script : Script) : Option Syntax.BodyStatement := do
  let (statement, _) ← script.statements.head?
  match statement with
  | .update table assignments filter _ subqueries => some (.update table assignments filter subqueries)
  | .delete table filter _ subqueries => some (.delete table filter subqueries)
  | .select .. | .createTable .. | .createIndex .. | .addColumn .. | .dropTable ..
  | .dropIndex .. | .begin | .commit | .rollback | .insert .. | .pragma ..
  | .createTrigger .. | .dropTrigger .. => none

/-- Read a resolved assignment or DELETE filter using the actual target-plus-trigger
cell layout. This checks preparation and expressions without broadening nested-write execution. -/
def writeValue (script : Script) (row : TriggerRow) (cells : List Value) : Option Value := do
  let body ← writeBody script
  match resolveBodyStatement runContext database.catalog row body with
  | .ok (.ok (.update _ assignments _ subqueries)) =>
    let (_, expression) ← assignments.head?
    some (expression.eval (Resolved.statementContext 0 {} [] database.raw subqueries) cells)
  | .ok (.ok (.delete _ filter subqueries)) =>
    let expression ← filter
    some (expression.eval (Resolved.statementContext 0 {} [] database.raw subqueries) cells)
  | .error _ | .ok (.error _) | .ok (.ok (.insert ..)) | .ok (.ok (.query ..))
  | .ok (.ok (.raise ..)) => none

/-- Hiding target names keeps NEW at cell three and OLD at cell four. -/
example : writeValue (sql r"UPDATE log SET c=(SELECT value FROM total)") (trigger true true)
    [.integer 900,.integer 800,.integer 700,.integer 100,.integer 7] = some (.integer 107) := by decide +kernel

/-- A DELETE body keeps OLD after its three target columns. -/
example : writeValue (sql r"DELETE FROM log WHERE c=(SELECT value FROM old_row)") (trigger false true)
    [.integer 900,.integer 800,.integer 7,.integer 7] = some (.integer 1) := by decide +kernel

/-- The same filter rejects a different target value. -/
example : writeValue (sql r"DELETE FROM log WHERE c=(SELECT value FROM old_row)") (trigger false true)
    [.integer 900,.integer 800,.integer 8,.integer 7] = some (.integer 0) := by decide +kernel

end ViewTriggerExamples
