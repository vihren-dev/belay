import Belay.Sqlite.Model.Queries.Select.AddColumn
import Belay.Sqlite.Model.Queries.Preparation.Upserts
import Belay.Sqlite.Model.Queries.Evaluation.InsertCells
import Belay.Sqlite.Model.Queries.Preparation.WriteStages

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The name of a view as the catalog spells it, or the name as written when there is none. -/
def viewCatalogName (catalog : Catalog) (view : Identifier) : Identifier :=
  (((catalog.findView view).bind fun (position, _) => catalog[position]?.map (·.name))).getD view

/-- The resolution of a write (INSERT, UPDATE or DELETE) whose target is a view: SQLite refuses it
with {lit}`cannot modify %s because it is a view`, because the model holds no INSTEAD OF trigger.
The name keeps the catalog's spelling. Before that, SQLite reads the columns of the view
({lit}`resolveViewTarget`). -/
def resolveViewModify (catalog : Catalog) (view : Identifier) : StatementResolution :=
  prepareError catalog (.viewModify (viewCatalogName catalog view))

/-- The table column positions of an INSERT column list from the name at {lit}`index`, or
{lit}`table %S has no column named %s` for the first unknown name, or
{lit}`cannot INSERT into generated column "%s"` for a generated column. Each name is recorded at
{lit}`[index]`, as the column of the table that it names, with the columns of the table as candidates
when it names none; {lit}`scope` is the scope of the table. -/
def insertPositionsFrom (tableName : Identifier) (columns : List CatalogColumn) (scope : Scope) :
    Nat → List Identifier → Traced ExprError (List Nat)
  | _, [] => pure []
  | index, name :: rest => do
    let located := columnPosition columns name
    Traced.record (columnTargetOccurrence scope [index] name located .error)
    match located with
    | some position =>
      if (columns[position]?.bind (·.generated)).isSome then throw (.insertGenerated name)
      else do
        let positions ← insertPositionsFrom tableName columns scope (index + 1) rest
        pure (position :: positions)
    | none => throw (.tableHasNoColumn tableName name)

/-- Whether the column list of an INSERT is stopped by a rowid name: the first name that is no
usable column (an unknown name, or a generated column) is {lit}`rowid`, {lit}`_rowid_` or {lit}`oid`
and the table has a rowid. SQLite stores the value in the rowid, which the model does not describe for
a column list ({name}`RestrictionKind.rowidName`); the first name decides, so that an error of an earlier
name stays an error. -/
def insertRowidTarget (table : CatalogTable) : Option (List Identifier) → Bool
  | none => false
  | some written =>
    match written.find? fun name => match columnPosition table.columns name with
      | none => true
      | some position => (table.columns[position]?.bind (·.generated)).isSome with
    | some name => !table.withoutRowid && (columnPosition table.columns name).isNone && rowidName name
    | none => false

/-- The positions that an INSERT without a column list fills: every column that is not
generated, in table order (ADR 0014, slice 5). -/
def writablePositions (columns : List CatalogColumn) : List Nat :=
  (List.range columns.length).filter fun position => (columns[position]?.bind (·.generated)).isNone

/-- The positions of the cells that an INSERT fills: those of its column list, or without a list every
column that is not generated ({name}`writablePositions`). The column list is at child 1. -/
def insertPositionsTraced (tableName : Identifier) (columns : List CatalogColumn) (scope : Scope) :
    Option (List Identifier) → Traced ExprError (List Nat)
  | some written => insertPositionsFrom tableName columns scope 0 written
  | none => pure (writablePositions columns)

/-- The resolved {lit}`WHERE` filter of an UPDATE or DELETE, a condition over {lit}`scope`, or none
when there is no filter. -/
def resolveWriteFilterTraced (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) :
    Option Syntax.Expr → Traced ValueIssue (Option Resolved.Expr)
  | none => pure none
  | some term => Traced.map some (Traced.condition [] (resolveOperandTraced dqs scope shapes true term))

end Belay.Sqlite.Model
