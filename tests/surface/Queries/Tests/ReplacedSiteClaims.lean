import ReplacedSiteCertificates

/-! Original claims for moving and preserving reads across the derived-column migration. -/

namespace Belay.Sqlite.DerivedColumnMigration
open Belay.Sqlite.Model

/-- The earlier resolution witnesses imply this application claim through the two scan certificates. -/
theorem Site.OriginalLookupMove.outputs {database : Database.Raw} {tableName : Identifier}
    {definition : Syntax.ColumnDefinition} {value : Syntax.Expr} {site : Site database tableName definition value}
    {triggers : List (Identifier × CatalogTrigger)} {original replacement : Syntax.Statement}
    {parameters : List Value} (lookup : site.OriginalLookupMove triggers original replacement parameters)
    (clock : Option Clock) (before after : Nat) {connection migrated : Connection}
    (same : connection.state.database = database) (aligned : site.position < database.rows.length)
    (reached : migrated.state.database = site.reached triggers)
    (wide : site.table.RowsWide) (aliased : site.table.RowsAliased) :
    (runScriptStep runContext clock before connection original parameters).output =
      (runScriptStep runContext clock after migrated replacement parameters).output :=
  lookup.semantic.outputs clock before after same aligned reached wide aliased

/-- The earlier resolution witnesses imply this application claim through the two scan certificates. -/
theorem Site.OriginalLookupMove.rows {database : Database.Raw} {tableName : Identifier}
    {definition : Syntax.ColumnDefinition} {value : Syntax.Expr} {site : Site database tableName definition value}
    {triggers : List (Identifier × CatalogTrigger)} {original replacement : Syntax.Statement}
    {parameters : List Value} (lookup : site.OriginalLookupMove triggers original replacement parameters)
    (clock : Option Clock) (before after : Nat) {connection migrated : Connection}
    (same : connection.state.database = database) (aligned : site.position < database.rows.length)
    (reached : migrated.state.database = site.reached triggers)
    (wide : site.table.RowsWide) (aliased : site.table.RowsAliased) :
    ∃ rows, (runScriptStep runContext clock before connection original parameters).output = .rows rows ∧
      (runScriptStep runContext clock after migrated replacement parameters).output = .rows rows :=
  lookup.semantic.rows clock before after same aligned reached wide aliased

/-- The earlier resolution witnesses imply this application claim through the two scan certificates. -/
theorem Site.OriginalReadPreserved.outputs {database : Database.Raw} {tableName : Identifier}
    {definition : Syntax.ColumnDefinition} {value : Syntax.Expr} {site : Site database tableName definition value}
    {triggers : List (Identifier × CatalogTrigger)} {statement : Syntax.Statement}
    (read : site.OriginalReadPreserved triggers statement) (parameters : List Value)
    (clock : Option Clock) (before after : Nat) {connection migrated : Connection}
    (same : connection.state.database = database) (aligned : site.position < database.rows.length)
    (reached : migrated.state.database = site.reached triggers)
    (wide : site.table.RowsWide) (aliased : site.table.RowsAliased) :
    (runScriptStep runContext clock before connection statement parameters).output =
      (runScriptStep runContext clock after migrated statement parameters).output :=
  read.semantic.outputs parameters clock before after same aligned reached wide aliased

/-- The earlier resolution witnesses imply this application claim through the two scan certificates. -/
theorem original_queryTranslates (tableName : Identifier) (definition : Syntax.ColumnDefinition) (value : Syntax.Expr)
    (addValues updateValues : List Value) (triggers : List ((Identifier × CatalogTrigger) × List Value))
    (original replacement : Syntax.Statement) (parameters : List Value)
    (originalReads : original.readsOnly = true) (replacementReads : replacement.readsOnly = true)
    (originalSingle : original.isInsertSelect = false) (replacementSingle : replacement.isInsertSelect = false)
    (domain : Database → Prop) (siteOf : ∀ db, domain db → Site db.raw tableName definition value)
    (move : ∀ (db : Database) (inside : domain db),
      (siteOf db inside).OriginalLookupMove (triggers.map (·.1)) original replacement parameters) :
    Migration.QueryTranslates
      (send (migration tableName definition value addValues updateValues triggers))
      ⟨[(original, parameters)]⟩ ⟨[(replacement, parameters)]⟩ domain
      (by simp [Script.isQuery, originalReads]) (by simp [Script.isQuery, replacementReads]) :=
  queryTranslates tableName definition value addValues updateValues triggers
    original replacement parameters originalReads replacementReads originalSingle replacementSingle domain siteOf fun db inside => (move db inside).semantic

/-- The earlier resolution witnesses imply this application claim through the two scan certificates. -/
theorem original_queryPreserves (tableName : Identifier) (definition : Syntax.ColumnDefinition) (value : Syntax.Expr)
    (addValues updateValues : List Value) (triggers : List ((Identifier × CatalogTrigger) × List Value))
    (statement : Syntax.Statement) (parameters : List Value) (reads : statement.readsOnly = true)
    (single : statement.isInsertSelect = false)
    (domain : Database → Prop) (siteOf : ∀ db, domain db → Site db.raw tableName definition value)
    (kept : ∀ (db : Database) (inside : domain db), (siteOf db inside).OriginalReadPreserved (triggers.map (·.1)) statement) :
    Migration.QueryPreserves
      (send (migration tableName definition value addValues updateValues triggers))
      ⟨[(statement, parameters)]⟩ domain (by simp [Script.isQuery, reads]) :=
  queryPreserves tableName definition value addValues updateValues triggers
    statement parameters reads single domain siteOf fun db inside => (kept db inside).semantic

#print axioms Site.OriginalLookupMove.outputs
#print axioms Site.OriginalLookupMove.rows
#print axioms Site.OriginalReadPreserved.outputs
#print axioms original_queryTranslates
#print axioms original_queryPreserves

end Belay.Sqlite.DerivedColumnMigration
