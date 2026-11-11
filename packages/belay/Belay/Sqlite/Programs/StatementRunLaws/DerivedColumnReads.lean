import Belay.Sqlite.Programs.StatementRunLaws.DerivedColumnMigration
import Belay.Sqlite.Schema.Columns.DerivedColumnReads

set_option doc.verso true

/-! The reads that a migration which adds a column, backfills it from an expression and registers triggers
moves or keeps (ADR 0017, S6). {lit}`Site.LookupMove` states what moves a read from the expression to the
stored column, and {lit}`Site.ReadPreserved` states what keeps a read as it is. For each, a theorem gives the
equal outputs of the steps before and after the migration. -/

namespace Belay.Sqlite.DerivedColumnMigration
open Belay.Sqlite.Model

/-- For every site, move of a read, connection on the site's database and connection on the migrated
database, with an aligned table of wide aliased rows, the steps of the original and replacement statements
have equal outputs, at any clocks and statement indexes. Proof sketch:
{name}`Model.derivedColumn_lookup_outputs` with the resolutions, calm facts and agreement of the move. -/
theorem Site.LookupMove.outputs {database : Database.Raw} {tableName : Identifier}
    {definition : Syntax.ColumnDefinition} {value : Syntax.Expr} {site : Site database tableName definition value}
    {triggers : List (Identifier × CatalogTrigger)} {original replacement : Syntax.Statement}
    {parameters : List Value} (lookup : site.LookupMove triggers original replacement parameters)
    (clock : Option Clock) (before after : Nat) {connection migrated : Connection}
    (same : connection.state.database = database) (aligned : site.position < database.rows.length)
    (reached : migrated.state.database = site.reached triggers)
    (wide : site.table.RowsWide) (aliased : site.table.RowsAliased) :
    (runScriptStep runContext clock before connection original parameters).output =
      (runScriptStep runContext clock after migrated replacement parameters).output := by
  obtain ⟨names, beforeState, resolvedBefore⟩ := lookup.resolvesBefore connection.resolveState
    (by simp [Connection.resolveState, same])
  obtain ⟨afterNames, afterState, resolvedAfter⟩ := lookup.resolvesAfter migrated.resolveState
    (by simp [Connection.resolveState, reached])
  refine derivedColumn_lookup_outputs runContext clock before after connection migrated original replacement
    parameters site.position site.table site.column site.assigned triggers lookup.beforeFilter lookup.afterFilter
    lookup.columns names afterNames (by rw [same]; exact site.present) (by rw [same]; exact aligned)
    (by rw [reached, same]; rfl) wide aliased (assignedExpression_readsBelow site.below) site.keysInside site.plain
    (by simp [Site.column, definedColumn]) resolvedBefore resolvedAfter (lookup.calmBefore names)
    (lookup.calmAfter afterNames) lookup.columnsBelow (lookup.agree wide)

/-- For the premises of {name}`Site.LookupMove.outputs`, the original statement's step on the first
connection has the rows of some result as its output, and the replacement statement's step on the migrated
connection has the same rows. Plain words: a moved read returns rows, and the same rows before and after.
Proof sketch: the output of a calm read of one table is the normal form of the query result
({name}`Model.runScriptStep_simpleTable_output`), and {name}`Site.LookupMove.outputs` equates the two. -/
theorem Site.LookupMove.rows {database : Database.Raw} {tableName : Identifier}
    {definition : Syntax.ColumnDefinition} {value : Syntax.Expr} {site : Site database tableName definition value}
    {triggers : List (Identifier × CatalogTrigger)} {original replacement : Syntax.Statement}
    {parameters : List Value} (lookup : site.LookupMove triggers original replacement parameters)
    (clock : Option Clock) (before after : Nat) {connection migrated : Connection}
    (same : connection.state.database = database) (aligned : site.position < database.rows.length)
    (reached : migrated.state.database = site.reached triggers)
    (wide : site.table.RowsWide) (aliased : site.table.RowsAliased) :
    ∃ rows, (runScriptStep runContext clock before connection original parameters).output = .rows rows ∧
      (runScriptStep runContext clock after migrated replacement parameters).output = .rows rows := by
  obtain ⟨names, beforeState, resolvedBefore⟩ := lookup.resolvesBefore connection.resolveState
    (by simp [Connection.resolveState, same])
  refine ⟨_, runScriptStep_simpleTable_output runContext clock before connection original parameters site.position
    site.table lookup.beforeFilter lookup.columns names resolvedBefore (by rw [same]; exact site.present)
    (lookup.calmBefore names), ?_⟩
  rw [← lookup.outputs clock before after same aligned reached wide aliased]
  exact runScriptStep_simpleTable_output runContext clock before connection original parameters site.position
    site.table lookup.beforeFilter lookup.columns names resolvedBefore (by rw [same]; exact site.present)
    (lookup.calmBefore names)

/-- For every site, read kept by {name}`Site.ReadPreserved`, connection on the site's database and connection
on the migrated database, with an aligned table of wide aliased rows, the steps of the statement on the two
connections have equal outputs, at any clocks and statement indexes. Proof sketch:
{name}`Model.derivedColumn_preserved_outputs` with the resolutions and calm facts of the read. -/
theorem Site.ReadPreserved.outputs {database : Database.Raw} {tableName : Identifier}
    {definition : Syntax.ColumnDefinition} {value : Syntax.Expr} {site : Site database tableName definition value}
    {triggers : List (Identifier × CatalogTrigger)} {statement : Syntax.Statement}
    (read : site.ReadPreserved triggers statement) (parameters : List Value)
    (clock : Option Clock) (before after : Nat) {connection migrated : Connection}
    (same : connection.state.database = database) (aligned : site.position < database.rows.length)
    (reached : migrated.state.database = site.reached triggers)
    (wide : site.table.RowsWide) (aliased : site.table.RowsAliased) :
    (runScriptStep runContext clock before connection statement parameters).output =
      (runScriptStep runContext clock after migrated statement parameters).output := by
  obtain ⟨names, beforeState, resolvedBefore⟩ := read.resolvesBefore connection.resolveState
    (by simp [Connection.resolveState, same])
  obtain ⟨afterNames, afterState, resolvedAfter⟩ := read.resolvesAfter migrated.resolveState
    (by simp [Connection.resolveState, reached])
  exact derivedColumn_preserved_outputs runContext clock before after connection migrated statement parameters
    site.position site.table site.column site.assigned triggers read.filter read.columns names afterNames
    (by rw [same]; exact site.present) (by rw [same]; exact aligned) (by rw [reached, same]; rfl) wide aliased
    (assignedExpression_readsBelow site.below) site.keysInside site.plain (by simp [Site.column, definedColumn])
    resolvedBefore resolvedAfter (read.calm names) read.filterBelow read.columnsBelow

end Belay.Sqlite.DerivedColumnMigration
