import Belay.Sqlite.Model.Queries.Select.TableChecks

set_option doc.verso true

/-! The CHECK constraints of CREATE TABLE and ADD COLUMN (ADR 0014, D2), resolved as
SQLite's {lit}`sqlite3EndTable` resolves them: after every other check of the definition,
in written order, as {lit}`WHERE` conditions over the table alone, with aggregates as
misuse and under the profile's {lit}`DQS_DDL`. Checked natively with 3.51.0. -/

namespace Belay.Sqlite.Model

/-- The CHECK constraints of one column definition, in written order; the path of an issue
of constraint {lit}`item` is {lit}`[2, item, 0]` within the definition. -/
def columnChecks (dqs : Bool) (scope : Scope) (definition : Syntax.ColumnDefinition) :
    Except ValueIssue (List CheckConstraint) :=
  definition.constraints.zipIdx.filterMapM fun (constraint, item) => match constraint with
    | .check condition label text => some <$> (resolveCheck dqs scope condition label text).mapError
      (·.under [2, item, 0])
    | .notNull _ | .primaryKey .. | .unique _ | .default .. | .collate _ | .references .. | .generated .. | .deferral _ => .ok none

/-- The table with the CHECK constraints of its definitions and of its table constraints
resolved over the scope, in written order: each column's in {name}`CatalogColumn.checks`
(issue path {lit}`[1, column, 2, item, 0]`), then the table constraints' in
{name}`CatalogTable.checks` (issue path {lit}`[2, item, 0]`). -/
def resolveTableChecks (dqs : Bool) (scope : Scope) (table : CatalogTable)
    (definitions : List Syntax.ColumnDefinition) (constraints : List Syntax.TableConstraint) :
    Except ValueIssue CatalogTable := do
  let checked ← (table.columns.zip definitions).zipIdx.mapM fun ((column, definition), position) =>
    (fun checks => { column with checks }) <$> (columnChecks dqs scope definition).mapError (·.under [1, position])
  let tableChecks ← constraints.zipIdx.filterMapM fun (constraint, item) => match constraint with
    | .check condition label text => some <$> (resolveCheck dqs scope condition label text).mapError
      (·.under [2, item, 0])
    | .primaryKey .. | .unique .. | .foreignKey .. | .deferral _ => .ok none
  .ok { table with columns := checked ++ table.columns.drop definitions.length, checks := tableChecks }

end Belay.Sqlite.Model
