import Belay.Sqlite.Schema.Columns.DerivedColumnSiteCheck
import Belay.Sqlite.Schema.Columns.DerivedColumnReads
import Belay.Sqlite.Model

set_option doc.verso true

/-! A computed check of a read that the derived-column migration keeps ({lit}`Site.ReadPreserved`). The
read is a one-table {lit}`SELECT` without a join, a subquery, grouping, ordering or a limit. Its
resolution depends on the catalog only, so the check resolves it once on the catalog before the
migration and once on the catalog after it, and requires the same query. -/

namespace Belay.Sqlite.DerivedColumnMigration
open Belay.Sqlite.Model

/-- Whether the read is a query of the table at the position that the migration keeps: {name}`readParts`
gives the same query, at the position, on the catalog before the migration and on the catalog with the
column added; the filter and the result columns read only the old columns; and every expression of them
passes {name}`Resolved.Expr.calmCheck`. For example, {lit}`SELECT id FROM customers WHERE email = ?1` passes, and
{lit}`SELECT * FROM customers` fails, because after the migration its result columns include the new
column. -/
def readCheck (catalog : Catalog) (position width : Nat) (column : CatalogColumn) (statement : Syntax.Statement) :
    Bool :=
  match readParts runContext catalog statement, readParts runContext (catalog.addColumn position column) statement with
  | some (before, filter, columns), some (after, filterAfter, columnsAfter) =>
    before == position && after == position && filter == filterAfter && columns == columnsAfter &&
      filter.all (·.readsBelow width) && columns.all (·.readsBelow width) &&
      filter.all Resolved.Expr.calmCheck && (columns.flatMap Resolved.Output.scalars).all Resolved.Expr.calmCheck
  | _, _ => false

/-- For every site of the migration without triggers, the catalog of the database that it reaches is the
catalog of the database with the column of the site added. Proof sketch: the definitions. -/
theorem Site.reached_nil_catalog {database : Database.Raw} {tableName : Identifier}
    {definition : Syntax.ColumnDefinition} {value : Syntax.Expr} (site : Site database tableName definition value) :
    (site.reached []).catalog = database.catalog.addColumn site.position site.column :=
  rfl

/-- The {name}`Site.ReadPreserved` of a read at a site of the migration without triggers, when the read
passes {name}`readCheck` on the catalog of the database. Proof sketch: {name}`readParts` gives the same
filter and result columns on the catalog before the migration and on the catalog with the column added
({name}`Site.reached_nil_catalog`); {name}`readParts_resolves` turns each into the resolution of the
statement on every state with that catalog. The checks of {name}`readCheck` give the bounds of the filter
and the columns, and {name}`Resolved.Expr.calm_of_calmCheck` gives the calm query. -/
def Site.ReadPreserved.ofCheck {database : Database.Raw} {tableName : Identifier}
    {definition : Syntax.ColumnDefinition} {value : Syntax.Expr} (site : Site database tableName definition value)
    {statement : Syntax.Statement}
    (checked : readCheck database.catalog site.position site.table.shape.columns.length site.column statement = true) :
    site.ReadPreserved [] statement :=
  match before : readParts runContext database.catalog statement,
      after : readParts runContext (database.catalog.addColumn site.position site.column) statement, checked with
  | some (beforePosition, filter, columns), some (afterPosition, filterAfter, columnsAfter), checked => by
    simp only [readCheck, before, after, Bool.and_eq_true, beq_iff_eq] at checked
    obtain ⟨⟨⟨⟨⟨⟨⟨atBefore, atAfter⟩, sameFilter⟩, sameColumns⟩, filterBelow⟩, columnsBelow⟩, filterCalm⟩,
      columnsCalm⟩ := checked
    subst atBefore atAfter sameFilter sameColumns
    refine ⟨filter, columns, ?_, List.all_eq_true.mp columnsBelow, ?_, ?_, ?_⟩
    · intro condition member
      simp only [Option.mem_def] at member
      subst member
      simpa using filterBelow
    · intro state same
      obtain ⟨names, resolves⟩ := readParts_resolves (state := state) (same ▸ before)
      exact ⟨names, state, resolves⟩
    · intro state same
      rw [Site.reached_nil_catalog] at same
      obtain ⟨names, resolves⟩ := readParts_resolves (state := state) (same ▸ after)
      exact ⟨names, state, resolves⟩
    · exact fun names => Resolved.Statement.simpleTable_calm _ filter columns names
        (by
          intro expression member
          simp only [List.mem_append] at member
          rcases member with member | member
          · cases filter with
            | none => cases member
            | some condition =>
              simp only [Option.toList_some, List.mem_singleton] at member
              subst member
              exact Resolved.Expr.calm_of_calmCheck (by simpa using filterCalm)
          · exact Resolved.Expr.calm_of_calmCheck (List.all_eq_true.mp columnsCalm expression member))
        (fun output member => Resolved.Output.operands_of_readsBelow (List.all_eq_true.mp columnsBelow output member))
  | none, _, checked => absurd checked (by simp [readCheck, before])
  | some _, none, checked => absurd checked (by simp [readCheck, before, after])

end Belay.Sqlite.DerivedColumnMigration
