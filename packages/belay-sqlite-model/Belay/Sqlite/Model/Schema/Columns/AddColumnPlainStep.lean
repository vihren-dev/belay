import Belay.Sqlite.Model.Schema.Ddl.StatementArms
import Belay.Sqlite.Model.Schema.Dispatch.StatementArms
import Belay.Sqlite.Model.Schema.Ddl.CatalogAddColumnSearch
import Belay.Sqlite.Model.Queries.Select.ExprResolutionLaws

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every resolution context, catalog, table name, table at a catalog position and column definition without
constraints: if the table's strictness admits the declared type ({name}`addColumnRestriction`), then a
successful resolution of ADD COLUMN gives a prepare error with the catalog unchanged, or the addition of
{name}`definedColumn` at the position of the table with the catalog that holds the column. A model
restriction cannot satisfy the success premise. The column has no {lit}`REFERENCES`, so the statement
does not refuse a populated table, whatever {lit}`enforced` is. Proof sketch: reduce the empty
constraint list, then split the remaining name and width checks. -/
theorem addColumn_resolution_cases {context : ResolveContext} {enforced : Bool} {catalog : Catalog}
    {tableName : Identifier} {definition : Syntax.ColumnDefinition} {position : Nat} {table : CatalogTable}
    {resolved : Resolved.Statement} {next : Catalog}
    (plain : definition.constraints = [])
    (admitted : addColumnRestriction table definition = none)
    (found : catalog.findTable tableName = some (position, table))
    (ok : resolveAddColumn context catalog enforced tableName definition = .ok (resolved, next)) :
    (∃ error, resolved = .prepareError error ∧ next = catalog) ∨
      (resolved = .addColumn position (definedColumn table.strict definition) false ∧
        next = catalog.addColumn position (definedColumn table.strict definition)) := by
  have metadata : addedColumn table.strict definition = some (definedColumn table.strict definition) := by
    simp [addedColumn, plain]
  have read : readDefaultValue (definedColumn table.strict definition) = .ok .null := rfl
  have fits : strictDefaultFits (definedColumn table.strict definition) = true := by
    unfold strictDefaultFits
    rw [read]
    cases (definedColumn table.strict definition).strictType with
    | none => rfl
    | some strictType => cases strictType <;> rfl
  simp only [resolveAddColumn, found] at ok
  simp only [plain, admitted, metadata, fits] at ok
  simp only [plain, List.findSome?_nil, List.any_nil, Bool.false_and,
    Bool.false_eq_true, Bool.not_true, ↓reduceIte, columnChecks, List.zipIdx_nil,
    List.filterMapM_nil, addedForeignKeys, List.foldl_nil, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact .inl ⟨_, rfl, rfl⟩)
    | (cases ok; exact .inr ⟨by simp [definedColumn], rfl⟩)
    | cases ok

end Belay.Sqlite.Model
