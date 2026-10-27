import Belay.Sqlite.Model.Resolution.RenameCatalogExamples

set_option doc.verso true

/-! Examples of the failures of {lit}`renameCatalog`, checked by {lit}`#guard` when the package builds, with the
messages of SQLite 3.51.0 that the task probed natively: a view or trigger that does not resolve before the rename
({lit}`error in view v: ...`), a catalog that does not resolve after it ({lit}`error in view v after rename: ...`,
{lit}`error in table t after rename: duplicate column name: b`), and a trigger whose body fails only when it runs,
which SQLite renames without error and the model does not describe (a restriction, never an error of the rename). -/

namespace Belay.Sqlite.Model.Resolution.RenameFailureExamples

open Belay.Sqlite.Model Syntax Resolution.Examples Resolution.RewriteExamples Resolution.RenameCatalogExamples

/-- The tables {lit}`t(a, b)` and {lit}`u(x)` and the object that the example adds. -/
def withObject (statement : Syntax.Statement) : Catalog :=
  catalogOf (schema [.createTable (name! "t") [column (name! "a"), column (name! "b")] [],
    .createTable (name! "u") [column (name! "x")] [], statement])

/-- A trigger on {lit}`t` after an insert, with the statements as its body. -/
def triggerOf (body : List BodyStatement) : Syntax.Statement :=
  .createTrigger (name! "g") false .after .insert (name! "t") none body

/-- The rename of the column {lit}`u.x` to {lit}`a`. -/
def uxToA : RenameRequest := { target := .column 1 0, new := name! "a", style := .column false }

/-- {lit}`JOIN u ON 1`. -/
def joinU : Join where
  operator := []
  source := { table := name! "u", alias := none }
  condition := some (.numeric "1")
  usingColumns := none

/-- Whether the rename is a restriction of the model. -/
def restrictedBy (catalog : Catalog) (request : RenameRequest) (oldTable oldColumn : String) : Bool :=
  match renameCatalog context catalog request (Identifier.ofString oldTable) (Identifier.ofString oldColumn) with
  | .error (.restricted _) => true
  | .error (.prepare _) | .ok _ => false

-- A view that does not resolve is the error of the first pass, also when it does not read the renamed table.
#guard errorBy (withObject (.createView (name! "vbad") false none (selectOf [ident "zz"]))) tableToW "t" "t" ==
  some (.dependentObject .view (name! "vbad") .current (.expression (.noSuchColumn (name! "zz"))))
#guard errorBy (withObject (.createView (name! "vbad") false none (selectOf [ident "zz"]))) uxToA "u" "x" ==
  some (.dependentObject .view (name! "vbad") .current (.expression (.noSuchColumn (name! "zz"))))
-- A trigger whose WHERE clause names a missing column is the error of the first pass.
#guard errorBy (withObject (triggerOf [.update (name! "t") [(name! "b", .numeric "1")]
    (some (.compare .eq (ident "zz") (.numeric "1")))])) tableToW "t" "t" ==
  some (.dependentObject .trigger (name! "g") .current (.expression (.noSuchColumn (name! "zz"))))
-- A rewritten catalog that does not resolve is the error of the second pass: an ambiguous name, a duplicate column.
#guard errorBy (withObject (.createView (name! "vj") false none
    (selectOf [ident "a"] (joins := [joinU])))) uxToA "u" "x" ==
  some (.dependentObject .view (name! "vj") .afterRename (.expression (.ambiguousColumn (name! "a"))))
#guard errorBy (withObject (.createView (name! "w") false none (selectOf [ident "a"])))
    { columnToZ with new := name! "b" } "t" "a" ==
  some (.dependentObject .table (name! "t") .afterRename (.expression (.duplicateColumn (name! "b"))))
-- A trigger that fails only when it runs is renamed by SQLite (the INSERT has too few values). The model has no
-- complete trace of the names of such a trigger, so it is a restriction and never an error.
#guard restrictedBy (withObject (triggerOf [.insert (name! "t") none [[.numeric "1"]] []])) tableToW "t" "t"
#guard errorBy (withObject (triggerOf [.insert (name! "t") none [[.numeric "1"]] []])) tableToW "t" "t" == none

-- A CHECK text with a double quote that no name covers is rewritten by SQLite at every column rename
-- ({lit}`renameQuotefix`); the model does not write that into the text, so the column rename is a restriction.
-- A table rename leaves the text as written.
#guard restrictedBy (catalogOf (schema [.createTable (name! "t")
    [{ name := name! "a", declaredType := some "TEXT",
       constraints := [.check (.numeric "1") "\"x\" = 1" { text := "\"x\" = 1", tokens := [] }] }] []]))
  columnToZ "t" "a"
#guard (renamedBy (catalogOf (schema [.createTable (name! "t")
    [{ name := name! "a", declaredType := some "TEXT",
       constraints := [.check (.numeric "1") "\"x\" = 1" { text := "\"x\" = 1", tokens := [] }] }] []]))
  tableToW "t" "t").isSome

-- SQLite reports the errors of dependent objects while the statement runs, and every other prepare error in prepare.
#guard (PrepareError.dependentObject .view (name! "v") .current (.expression (.noSuchColumn (name! "zz")))).reportedWhileRunning
#guard !(PrepareError.noSuchTable (name! "t")).reportedWhileRunning
#guard !(PrepareError.renameTargetTaken (name! "t")).reportedWhileRunning

end Belay.Sqlite.Model.Resolution.RenameFailureExamples
