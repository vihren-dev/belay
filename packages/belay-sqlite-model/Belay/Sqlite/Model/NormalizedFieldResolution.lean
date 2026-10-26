import Belay.Sqlite.Model.ExprResolutionLaws
import Belay.Sqlite.Model.ModelProjectionLaws
import Belay.Sqlite.Model.CatalogValidSet

set_option doc.verso true

/-! Resolution facts needed by a lowercase-field expansion: the plain TEXT
column, its position, and the original named column's lowercase expression. -/

namespace Belay.Sqlite.Model.NormalizedField

/-- The written declaration of a plain TEXT column, without a default or other
constraint. ADD COLUMN initializes its existing rows with NULL. -/
def textDefinition (name : Identifier) : Syntax.ColumnDefinition :=
  { name, declaredType := some "TEXT", constraints := [] }

/-- The metadata of the plain TEXT declaration, retaining the table's strict
typing mode. The field has BINARY collation and no generated expression. -/
def textColumn (name : Identifier) (strict : Bool) : CatalogColumn :=
  { name, declaredType := some "TEXT", strictType := if strict then some .text else none }

/-- A plain TEXT addition to a present table either gives a prepare error or
adds precisely the declared column at that table's position. A model restriction
cannot satisfy the successful-resolution premise. The column has no {lit}`REFERENCES`, so the
statement does not refuse a populated table, whatever {lit}`enforced` is. Proof sketch: reduce the
empty constraint list, then split the remaining name and width checks. -/
theorem addColumn_resolution_cases {context : ResolveContext} {enforced : Bool} {catalog : Catalog}
    {tableName name : Identifier} {position : Nat} {table : CatalogTable}
    {resolved : Resolved.Statement} {next : Catalog}
    (found : catalog.findTable tableName = some (position, table))
    (ok : resolveAddColumn context catalog enforced tableName (textDefinition name) = .ok (resolved, next)) :
    (∃ error, resolved = .prepareError error ∧ next = catalog) ∨
      (resolved = .addColumn position (textColumn name table.strict) false ∧
        next = catalog.addColumn position (textColumn name table.strict)) := by
  have metadata : addedColumn table.strict (textDefinition name) = some (textColumn name table.strict) := by
    cases table.strict <;> rfl
  have restriction : addColumnRestriction table (textDefinition name) = none := by
    change (if table.strict && false then some RestrictionKind.addColumnStrictType else none) = none
    simp
  have fits : strictDefaultFits (textColumn name table.strict) = true := by
    cases table.strict <;> rfl
  simp only [resolveAddColumn, found] at ok
  simp only [metadata, restriction, fits] at ok
  simp only [textDefinition, List.findSome?_nil, List.any_nil, Bool.false_and,
    Bool.false_eq_true, Bool.not_true, ↓reduceIte, columnChecks, List.zipIdx_nil,
    List.filterMapM_nil, addedForeignKeys, List.foldl_nil, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact .inl ⟨_, rfl, rfl⟩)
    | (cases ok; exact .inr ⟨by simp [textColumn], rfl⟩)
    | cases ok

/-- Appending columns keeps every already resolved column position. The first
matching original name still precedes the appended columns. Proof sketch:
recover the successful search and apply its append law. -/
theorem columnPosition_append {columns : List CatalogColumn} {name : Identifier} {position : Nat}
    (found : columnPosition columns name = some position) (extra : List CatalogColumn) :
    columnPosition (columns ++ extra) name = some position := by
  obtain ⟨pair, located, equal⟩ := Option.map_eq_some_iff.mp found
  simp only [columnPosition, findPosition_append extra located, Option.map_some, equal]

/-- If no original column has the plain TEXT field's name, that field is found
at the original width after appending it. Proof sketch: the absent prefix and
the matching final name satisfy the first-match search. -/
theorem columnPosition_new {columns : List CatalogColumn} {name : Identifier}
    (fresh : columnPosition columns name = none) (strict : Bool) :
    columnPosition (columns ++ [textColumn name strict]) name = some columns.length := by
  have absent : findPosition (fun column => column.name.sameName name) columns = none := by
    simpa only [columnPosition, Option.map_eq_none_iff] using fresh
  simp [columnPosition, findPosition_append_none (item := textColumn name strict) absent
    (by simp [textColumn])]

/-- Adding a column to the named table keeps its exact name lookup and position,
with the column appended to its shape. Other catalog objects are unrestricted.
Proof sketch: replacing the table keeps the first matching name, and lookup at
that unchanged position identifies the replacement. -/
theorem findTable_addColumn {catalog : Catalog} {tableName : Identifier}
    {position : Nat} {table : CatalogTable} (column : CatalogColumn)
    (found : catalog.findTable tableName = some (position, table)) :
    (catalog.addColumn position column).findTable tableName =
      some (position, { table with columns := table.columns ++ [column] }) := by
  unfold Catalog.findTable at found
  split at found <;> try contradiction
  rename_i oldPosition name oldTable located
  cases found
  have atPosition := ((findPosition_eq_some_iff _ _ _ _).mp located).1
  have bound := (List.getElem?_eq_some_iff.mp atPosition).1
  let replacement : CatalogObject :=
    { name, entry := .table { table with columns := table.columns ++ [column] } }
  obtain ⟨other, searched, _⟩ := Catalog.find_set
    (replacement := replacement) atPosition rfl rfl located
  have atOther := ((findPosition_eq_some_iff _ _ _ _).mp searched).1
  rw [List.getElem?_set_self bound] at atOther
  cases atOther
  dsimp only [replacement] at searched
  simp only [Catalog.addColumn, atPosition, Catalog.findTable, searched]

/-- In the scope of one table read from the catalog, lowercase of a found column resolves to that
column's lowercase expression with no comparison affinity. The column's own affinity and collation do
not change a function result's metadata. Proof sketch: resolve its one argument with the column lookup
law, then reduce the known call. -/
theorem resolve_lower_column_at {dqs : Bool} {position : Option Nat} {tableName name : Identifier}
    {columns : List CatalogColumn} {rowid : Bool} {source : Nat}
    (found : columnPosition columns name = some source) :
    resolveOperand dqs (Scope.singleAt position tableName columns rowid) {} true
      (.call "lower" [.identifier name .none]) =
      .ok (.scalar .lower (.cons (.column source) .nil), none) := by
  rw [resolveOperand_arm_call, resolveArguments_arm_cons, resolveArguments_arm_nil,
    resolveOperand_identifier_singleAt found]
  rfl

/-- In the single table scope, lowercase of a found column resolves to that
column's lowercase expression with no comparison affinity. The column's own
affinity and collation do not change a function result's metadata. Proof sketch:
this is {name}`resolve_lower_column_at` for a table that has no catalog position. -/
theorem resolve_lower_column {dqs : Bool} {tableName name : Identifier}
    {columns : List CatalogColumn} {rowid : Bool} {source : Nat}
    (found : columnPosition columns name = some source) :
    resolveOperand dqs (Scope.single tableName columns rowid) {} true
      (.call "lower" [.identifier name .none]) =
      .ok (.scalar .lower (.cons (.column source) .nil), none) :=
  resolve_lower_column_at (position := none) found

end Belay.Sqlite.Model.NormalizedField
