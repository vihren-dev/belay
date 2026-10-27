import Belay.Sqlite.Model.Resolution.Sources
import Belay.Sqlite.Model.Resolution.SourceRecords

set_option doc.verso true

/-! Resolution of the table of a table reference against the catalog, with the name trace. -/

namespace Belay.Sqlite.Model

/-- A table that the model does not read: the table of {lit}`path` is recorded as refused, and the
resolution fails with the restriction {lit}`kind`. -/
def refuseTable (path : List Nat) (table : Identifier) (kind : RestrictionKind) : Traced SourceIssue α := do
  Traced.record (tableOccurrence path table (.unreached .refused))
  throw (.value (.restriction path kind))

/-- The source of one table reference at {lit}`path`: the table's catalog position and the
source with its name (the alias, else the table name as declared, as SQLite names it in
messages), of kind {lit}`role`, which is {name}`SourceKind.baseTable` unless the catalog is the
catalog of the initial database. {lit}`index` is the position of the source in its {lit}`FROM`. A missing
table is SQLite's {lit}`no such table: %s` and lists the tables and views of the catalog as
candidates; one of SQLite's own tables is a model restriction, as in a
query of one table, and so is a name of an eponymous table-valued function
({name}`eponymousName`), which SQLite reads without arguments. A view requires indexed
query expansion and is {name}`RestrictionKind.subqueryHere` at this physical-table boundary.
The table is recorded where the resolver looks it up. -/
def resolveTableReferenceTraced (catalog : Catalog) (path : List Nat) (reference : Syntax.TableReference)
    (index : Nat := 0) (role : SourceKind := .baseTable) : Traced SourceIssue (Nat × ScopeSource) :=
  match catalog.findTable reference.table with
  | some (position, table) =>
    let declared := (catalog[position]?.map (·.name)).getD reference.table
    let source : ScopeSource :=
      { name := reference.alias.getD declared, columns := table.columns, hasRowid := !table.withoutRowid,
        role := role, catalogPosition := some position, aliased := reference.alias.isSome }
    do
      Traced.record (tableOccurrence path reference.table (.source (source.reference index)))
      pure (position, source)
  | none =>
    if (catalog.findView reference.table).isSome then refuseTable path reference.table .subqueryHere
    else if reservedName reference.table then refuseTable path reference.table .systemTable
    else if eponymousName reference.table then refuseTable path reference.table .tableFunction
    else do
      Traced.record (tableOccurrence path reference.table (.missing .error catalog.referenceCandidates))
      throw (.noSuchTable reference.table)

/-- The source of one table reference at {lit}`path`: {name}`resolveTableReferenceTraced` without its
trace. -/
def resolveTableReference (catalog : Catalog) (path : List Nat) (reference : Syntax.TableReference) :
    Except SourceIssue (Nat × ScopeSource) :=
  (resolveTableReferenceTraced catalog path reference).drop

/-- For every position of the source in its {lit}`FROM`: the position changes only the trace of a table
lookup, not its result. Proof sketch: split on the cases of the lookup; the position is in the records only. -/
@[traced_drop] theorem drop_resolveTableReferenceTraced_index (catalog : Catalog) (path : List Nat)
    (reference : Syntax.TableReference) (index : Nat) (role : SourceKind) :
    (resolveTableReferenceTraced catalog path reference index role).drop =
      (resolveTableReferenceTraced catalog path reference 0 role).drop := by
  unfold resolveTableReferenceTraced
  split
  · simp [traced_drop]
  · rfl

end Belay.Sqlite.Model
