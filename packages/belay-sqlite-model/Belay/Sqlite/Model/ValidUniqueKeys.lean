import Belay.Sqlite.Model.PartialUniqueCount
import Belay.Sqlite.Model.PartialUniqueKeptRows
import Belay.Sqlite.Model.DatabaseConstraints

set_option doc.verso true

/-!
The unique keys of a valid database (ADR 0017, S6). A database that SQLite writes with its statements is
valid, and a valid database keeps the unique keys of its catalog: the primary key, the UNIQUE constraints
and the unique indexes, with their filters. This module states the two facts about rows that the proofs of
claims about a unique index need (the pairwise fact about kept rows and the bound of a lookup), for any
valid database and any key of its catalog, so that a proof about a database that a plain insert reaches
needs only the validity of the reached database.
-/

namespace Belay.Sqlite.Model

/-- For every catalog, position, catalog table and index of the catalog that is on the position and is
unique: the key of the index is one of the unique keys of the table at the position
({name}`Catalog.uniqueKeys`). Proof sketch: the unique indexes of the catalog on the position are the last part of
the list, and the index is one of them. -/
theorem CatalogIndex.uniqueKey_mem_uniqueKeys {catalog : Catalog} {name : Identifier} {index : CatalogIndex}
    (indexed : ({ name, entry := .index index } : CatalogObject) ∈ catalog) (position : Nat) (table : CatalogTable)
    (indexTable : index.table = position) (indexUnique : index.unique = true) :
    index.uniqueKey ∈ catalog.uniqueKeys position table :=
  List.mem_append_right _ (List.mem_filterMap.2 ⟨_, indexed, by simp [indexTable, indexUnique]⟩)

/-- For every valid database, table at a position, key of the unique keys of the catalog for that table, and
column of the table at an index: assume that the key has one term, which is the column at the index under a
collation, that the column is declared NOT NULL, and that the guard implies the filter of the key (a missing
guard is true, a missing filter is true, and the filter is read with the plain context). Then no two rows that
the guard keeps ({name}`Resolved.keptRows` of {name}`Resolved.sourceRows`, in scan order) have values at the index
that compare equal under the collation. Plain words: a valid database keeps its unique index, so a query that
looks for two kept rows with one value finds none. Proof sketch: the validity gives {name}`Table.KeysUnique`,
{name}`Table.RowsWide` and {name}`Table.NotNull` for the table, and
{name}`Table.KeysUnique.keptRows_pairwise` gives the claim. -/
theorem Database.Valid.keptRows_pairwise {database : Database} {profile : Profile} (valid : database.Valid profile)
    {position : Nat} {table : Table} (present : database.table position = some table)
    {key : UniqueKey} (member : key ∈ database.catalog.uniqueKeys position table.shape)
    {index : Nat} {descending : Bool} {collation : Collation}
    (oneTerm : key.terms = [{ term := .column index, descending, collation }])
    {column : CatalogColumn} (columnAt : table.shape.columns[index]? = some column)
    (declaredNotNull : column.notNull = true) (context : Resolved.EvalContext) (guard : Option Resolved.Expr)
    (restricts : ∀ row : List Value, (guard.all fun condition => Resolved.truthy (condition.eval context row)) = true →
      (key.filter.all fun filter => Resolved.truthy (filter.eval (.plain 0) row)) = true) :
    (Resolved.keptRows context guard (Resolved.sourceRows table)).Pairwise fun earlier later =>
      collation.compare (later.getD index .null) (earlier.getD index .null) ≠ .eq :=
  Table.KeysUnique.keptRows_pairwise (valid.unique position table present)
    (valid.admitted.rowsWide position table present) (valid.notNull position table present)
    member oneTerm columnAt declaredNotNull context guard restricts

/-- For every valid database, table at a position, key of the unique keys of the catalog for that table with
a filter and one term, and condition: assume that the term is the column at an index under a collation, that
the condition implies the filter of the key, and that the comparison {lit}`cell = value` has the affinity of
the column and the collation of the key term, with a right operand that depends on no row. Then at most one
row of the table makes {lit}`guard AND cell = value` true: {name}`Resolved.countMatching` of the conjunction is
at most one. Plain words: a valid database keeps its partial unique index, so at most one row that the guard
accepts has a given value. Proof sketch: the validity gives {name}`Table.KeysUnique` and
{name}`Table.RowsStored` for the table, and {name}`Table.KeysUnique.countMatching_partial_le_one` gives
the claim. -/
theorem Database.Valid.countMatching_partial_le_one {database : Database} {profile : Profile}
    (valid : database.Valid profile) {position : Nat} {table : Table} (present : database.table position = some table)
    {key : UniqueKey} (member : key ∈ database.catalog.uniqueKeys position table.shape)
    {index : Nat} {descending : Bool} {collation : Collation} {column : CatalogColumn}
    (columnAt : table.shape.columns[index]? = some column) {filter : Resolved.Expr}
    (filtered : key.filter = some filter)
    (oneTerm : key.terms = [{ term := .column index, descending, collation }])
    (context : Resolved.EvalContext) (guard value : Resolved.Expr) (cell : Value)
    (restricts : ∀ row : List Value, Resolved.truthy (guard.eval context row) = true →
      Resolved.truthy (filter.eval (.plain 0) row) = true)
    (constant : ∀ row : List Value, value.eval context row = cell) :
    Resolved.countMatching context
      (some (.and guard (.compare .eq (some column.affinity) (.column index) value collation))) table ≤ 1 :=
  Table.KeysUnique.countMatching_partial_le_one (valid.unique position table present)
    (valid.admitted.rowsStored position table present) member columnAt filtered oneTerm context guard value cell
    restricts constant

end Belay.Sqlite.Model
