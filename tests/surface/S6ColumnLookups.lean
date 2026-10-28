import LowercaseQueries

set_option doc.verso true

/-! Lookups of a plain column across the lowercase-field migration (ADR 0017, S6). The lookup
{lit}`SELECT id FROM t WHERE name = ?n` reads no column that the migration adds, so it resolves to the same
simple query before and after it. This module states the lookup as syntax, its resolution for a compared column
of any declared type and collation, and the description {lit}`columnPreserved` that the general derived-column
laws need to keep the lookup across the migration of a {lit}`LowercaseSite`. -/

namespace S6RulesQuerySites
open Belay.Sqlite Belay.Sqlite.Model Belay.Sqlite.Model.Resolved LowercaseFixture

/-- The lookup {lit}`SELECT id FROM t WHERE name = ?n` as syntax: the table reference, the returned column and
its result text, the compared column and the one-based parameter number. -/
def columnLookup (reference : Syntax.TableReference) (idName columnName : Identifier) (text : String)
    (number : Nat) : Syntax.Statement :=
  .select [.expression (.identifier idName .none) none text] (some reference) []
    (some (.compare .eq (.identifier columnName .none) (.parameter number)))
    [] [] none none [] none false none

/-- The resolved filter {lit}`column = ?n`: the comparison takes the affinity and the collation of the
column, because a parameter has neither. -/
def columnFilter (position number : Nat) (column : CatalogColumn) : Expr :=
  .compare .eq (some column.affinity) (.column position) (.parameter number) column.collation

/-- For every column of any affinity and collation, in the scope of one table, the written filter
{lit}`name = ?n` resolves to {name}`columnFilter`. Proof sketch: the comparison law resolves the column with
its own affinity and the parameter with none, and a comparison with one affinity takes it. -/
theorem resolve_column_filter_at {dqs : Bool} {position : Option Nat} {tableName name : Identifier}
    {columns : List CatalogColumn} {rowid aliased : Bool} {index : Nat} {column : CatalogColumn}
    (found : columnPosition columns name = some index) (atIndex : columns[index]? = some column) (number : Nat) :
    resolveOperand dqs (Scope.singleAt position tableName columns rowid aliased) {} true
      (.compare .eq (.identifier name .none) (.parameter number)) =
      .ok (columnFilter index number column, none) := by
  have resolved : (Scope.singleAt position tableName columns rowid aliased).resolveName name =
      .found index [index] := resolveName_one_source_at found
  rw [resolveOperand_compare _ _ (by decide) (by decide)]
  simp only [resolveOperand_identifier_singleAt found, resolveOperand_parameter, atIndex, Except.mapError, bind,
    Except.bind]
  simp [comparisonAffinity, comparisonCollation, Syntax.Expr.explicitCollation, Syntax.Expr.columnCollation, resolved, Scope.columns_singleAt, atIndex, columnFilter]

/-- For a table that has the id column and the compared column, the lookup resolves to the simple query of the
table with {name}`columnFilter` and the id column. Proof sketch:
{name}`resolveStatement_select_column` with {name}`resolve_column_filter_at`. -/
theorem resolve_column_lookup (context : ResolveContext) (state : ResolveState)
    (reference : Syntax.TableReference) (position : Nat) (table : CatalogTable)
    (idName columnName : Identifier) (text : String) (number : Nat) {idPosition index : Nat} {column : CatalogColumn}
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none)
    (found : state.catalog.findTable reference.table = some (position, table))
    (idFound : columnPosition table.columns idName = some idPosition)
    (columnFound : columnPosition table.columns columnName = some index) (atIndex : table.columns[index]? = some column) :
    ∃ names, resolveStatement context state (columnLookup reference idName columnName text number) =
      .ok (.query (Resolved.Query.simple [Resolved.QuerySource.first position]
        (some (columnFilter index number column)) [.scalar (.column idPosition)] names) [], state) :=
  resolveStatement_select_column context state reference _ position table _ idName text namedSource current arguments
    found idFound (FilterResolves.of_term (result := (columnFilter index number column, none))
      (by simp [namesAlias]) (resolve_column_filter_at columnFound atIndex number))

/-- The filter {name}`columnFilter` is calm: it has no fallible call, clock read or counter call. -/
theorem columnFilter_calm (position number : Nat) (column : CatalogColumn) : (columnFilter position number column).Calm := by
  simp [columnFilter, Expr.Calm, Expr.any, Expr.isFallibleCall, Expr.readsClockHere, Expr.readsCounterHere]

/-- For every site of the lowercase migration, every alias of the table, id and compared columns of the
site, text and parameter number, and list of triggers, the lookup {lit}`SELECT id FROM t WHERE source = ?n`
is kept as it is: it resolves to the same simple query before and after the migration, it reads only old
columns, and it is calm. The compared column may have any declared type and collation. Proof sketch:
{name}`resolve_column_lookup` on the table before and after, where the compared column keeps its position
and its metadata when a column is appended. -/
def columnPreserved {database : Database.Raw} {tableName idName sourceName storedName : Identifier}
    (site : LowercaseSite database tableName idName sourceName storedName) (alias : Option Identifier)
    (text : String) (number : Nat) (triggers : List (Identifier × CatalogTrigger)) :
    site.toSite.ReadPreserved triggers (columnLookup (tableReference tableName alias) idName sourceName text number) :=
  have idInside := columnPosition_lt site.idFound
  have sourceInside := columnPosition_lt site.sourceFound
  have atSource : site.table.shape.columns[site.source]? = some (site.table.shape.columns[site.source]'sourceInside) :=
    List.getElem?_eq_getElem sourceInside
  { filter := some (columnFilter site.source number (site.table.shape.columns[site.source]'sourceInside))
    columns := [.scalar (.column site.id)]
    filterBelow := by
      intro condition member
      cases Option.mem_some_iff.mp member
      simp [columnFilter, Expr.readsBelow, Expr.any, Expr.isColumnFrom]
      exact sourceInside
    columnsBelow := by
      intro output member
      cases List.mem_singleton.mp member
      simp [Output.readsBelow, Expr.readsBelow, Expr.any, Expr.isColumnFrom]
      exact idInside
    resolvesBefore := fun state same => by
      obtain ⟨names, resolved⟩ := resolve_column_lookup runContext state (tableReference tableName alias)
        site.position site.table.shape idName sourceName text number rfl rfl rfl (by rw [same]; exact site.found)
        site.idFound site.sourceFound atSource
      exact ⟨names, state, resolved⟩
    resolvesAfter := fun state same => by
      have extended : state.catalog.findTable tableName = some (site.position,
          { site.table.shape with
            columns := site.table.shape.columns ++ [textColumn storedName site.table.shape.strict] }) := by
        rw [same]
        have := Database.findTable_addDerivedColumn (site.toSite.column) site.toSite.assigned triggers site.found
        simpa [DerivedColumnMigration.Site.reached, DerivedColumnMigration.Site.column, LowercaseSite.toSite,
          Table.addDerivedColumn, definedColumn_text] using this
      obtain ⟨names, resolved⟩ := resolve_column_lookup runContext state (tableReference tableName alias)
        site.position _ idName sourceName text number rfl rfl rfl extended
        (columnPosition_append site.idFound _) (columnPosition_append site.sourceFound _)
        (by rw [List.getElem?_append_left sourceInside]; exact atSource)
      exact ⟨names, state, resolved⟩
    calm := fun names => simpleColumn_calm _ _ _ names (columnFilter_calm _ _ _) }

end S6RulesQuerySites
