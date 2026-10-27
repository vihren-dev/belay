import Belay.Sqlite.Model.Resolution.RenameEdits
import Belay.Sqlite.Model.Resolution.RewriteExamples
import Belay.Sqlite.Model.Resolution.TriggerTraceExamples

set_option doc.verso true

/-! Examples of the edits that a rename makes in a stored view or trigger, checked by {lit}`#guard` when
the package builds. The catalog is {lit}`RewriteExamples.tables`: {lit}`t(a, b)`, {lit}`u(x)` and
{lit}`log(x)` at the positions 0, 1 and 2. -/

namespace Belay.Sqlite.Model.Resolution.RenameEditExamples

open Belay.Sqlite.Model Syntax Resolution.RewriteExamples

/-- The rename of the column {lit}`t.a` to {lit}`z`, written without a quote. -/
def columnA : RenameRequest := { target := .column 0 0, new := name! "z", style := .column false }

/-- The rename of the table {lit}`t` to {lit}`w`. -/
def tableT : RenameRequest := { target := .table 0, new := name! "w", style := .table }

/-- The query and subqueries of a view after the rename, or none when the rename is a restriction or cannot be
applied. -/
def renamedView (request : RenameRequest) (query : Subquery) (subqueries : List Subquery := []) :
    Option (Subquery × List Subquery) :=
  match request.edits false (resolveSelectTraced context tables query subqueries).trace with
  | .ok edits => (CatalogView.renameAll { query, subqueries } edits).map fun view => (view.query, view.subqueries)
  | .error _ => none

/-- The trigger after the rename, when {lit}`triggerOn` tells that its table is the renamed table. -/
def renamedTrigger (request : RenameRequest) (triggerOn : Bool) (trigger : CatalogTrigger) : Option CatalogTrigger :=
  match request.edits triggerOn (resolveProgramTraced context tables 3 trigger).trace with
  | .ok edits => trigger.renameAll edits
  | .error _ => none

/-- {lit}`SELECT t.a, b FROM t WHERE t.a > 0 ORDER BY b`, with the column {lit}`t.a` named {lit}`column`. -/
def viewQuery (column : String) : Subquery :=
  selectOf [dotted "t" column, ident "b"] (filter := some (.compare .gt (dotted "t" column) (.numeric "0")))
    (orderBy := [{ expression := ident "b", descending := false }])

-- A column rename changes every name that is bound to the column, and no other.
#guard renamedView columnA (viewQuery "a") == some (viewQuery "z", [])
-- A subquery over another table has its own column x; the correlated name of the outer table is renamed.
#guard renamedView columnA (selectOf [ident "a"] (filter := some (.inQuery (ident "a") 0 false)))
    [{ columns := [.expression (ident "x") none ""], source := some { table := name! "u", alias := none }, joins := [],
       filter := some (.compare .eq (ident "x") (dotted "t" "a")), groupBy := [], orderBy := [], limit := none,
       offset := none, parent := none }] ==
  some (selectOf [ident "z"] (filter := some (.inQuery (ident "z") 0 false)),
    [{ columns := [.expression (ident "x") none ""], source := some { table := name! "u", alias := none }, joins := [],
       filter := some (.compare .eq (ident "x") (dotted "t" "z")), groupBy := [], orderBy := [], limit := none,
       offset := none, parent := none }])
-- A rename of a column of another table changes nothing.
#guard renamedView { columnA with target := .column 1 0 } (viewQuery "a") == some (viewQuery "a", [])
/-- {lit}`SELECT w.a, b FROM w WHERE w.a > 0 ORDER BY b`: the view after a rename of {lit}`t` to {lit}`w`. -/
def viewOfW : Subquery :=
  { (viewQuery "a") with
    columns := [.expression (dotted "w" "a") none "", .expression (ident "b") none ""],
    source := some { table := name! "w", alias := none },
    filter := some (.compare .gt (dotted "w" "a") (.numeric "0")) }

-- A table rename changes the table and the qualifiers that name it.
#guard renamedView tableT (viewQuery "a") == some (viewOfW, [])
-- A qualifier that names an alias stays; only the table behind it is renamed.
#guard renamedView tableT { (viewQuery "a") with source := some { table := name! "t", alias := some (name! "t") } } ==
  some ({ (viewQuery "a") with source := some { table := name! "w", alias := some (name! "t") } }, [])

-- The rows of a trigger belong to its table: NEW.a and OLD.a of the WHEN condition are renamed when the trigger
-- is on the renamed table, and keep their names when it is on another table. The names of the table t itself in
-- its body are renamed in both cases.
#guard (renamedTrigger columnA true TriggerTraceExamples.trigger).map (·.condition) ==
  some (some (.compare .gt (dotted "new" "z") (dotted "old" "z")))
#guard (renamedTrigger columnA false TriggerTraceExamples.trigger).map (·.condition) ==
  some TriggerTraceExamples.trigger.condition
#guard (renamedTrigger columnA false TriggerTraceExamples.trigger).map (·.body.getLast?) ==
  some (some (.select [.expression (ident "z") none "a"] (some { table := name! "t", alias := none }) []
    (some (.compare .eq (ident "b") (dotted "new" "b"))) [] [] none none))
end Belay.Sqlite.Model.Resolution.RenameEditExamples
