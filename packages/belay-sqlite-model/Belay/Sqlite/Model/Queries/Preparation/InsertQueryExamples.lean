import Belay.Sqlite.Model.Queries.Preparation.NameTraceStatementExamples
import Belay.Sqlite.Model.Shared.Resolved.ResolveState

set_option doc.verso true

namespace Belay.Sqlite.Model.InsertQueryExamples

open NameTraceStatementExamples (name column from_)

/-- The catalog: {lit}`t(a, b, g)` with the generated column {lit}`g`, the view {lit}`v` of {lit}`t`, and
{lit}`s(x, y, z)`. -/
def catalog : Catalog :=
  let tableT : CatalogTable :=
    { columns := [
        { name := name "a", declaredType := some "INTEGER" },
        { name := name "b", declaredType := some "TEXT" },
        { name := name "g", declaredType := some "INTEGER",
          generated := some { expression := .literal .null, stored := false } }],
      primaryKey := [0], uniqueKeys := [[1]] }
  let tableS : CatalogTable :=
    { columns := [
        { name := name "x", declaredType := some "TEXT" },
        { name := name "y", declaredType := some "TEXT" },
        { name := name "z", declaredType := some "TEXT" }] }
  [{ name := name "t", entry := .table tableT },
   { name := name "v", entry := .view { query := NameTraceStatementExamples.query "t" } },
   { name := name "s", entry := .table tableS }]

/-- A query body of the given result columns from the table {lit}`s`, with the optional filter. -/
def body (results : List String) (source : String := "s") : Syntax.SelectBody :=
  { columns := results.map fun text => .expression (column text) none text, source := from_ source, joins := [],
    filter := none, groupBy := [], orderBy := [], limit := none, offset := none }

/-- The prepare error of a resolution, if it is one. -/
def prepared : Except NodeRestriction (Resolved.Statement × ResolveState) → Option PrepareError
  | .ok (.prepareError error, _) => some error
  | .ok (.createView .., _) | .ok (.createTable .., _) | .ok (.createIndex .., _) | .ok (.createTrigger .., _)
  | .ok (.addColumn .., _) | .ok (.rewrite _, _) | .ok (.dropColumn .., _) | .ok (.drop .., _) | .ok (.begin, _) | .ok (.commit, _) | .ok (.rollback, _) | .ok (.insert .., _)
  | .ok (.upsert .., _) | .ok (.insertSelect .., _) | .ok (.update .., _) | .ok (.delete .., _) | .ok (.query .., _) | .ok (.setting .., _)
  | .error _ => none

/-- The restriction of a resolution with its path, if it is one. -/
def refused : Except NodeRestriction (Resolved.Statement × ResolveState) → Option (List Nat × RestrictionKind)
  | .error restriction => some (restriction.path, restriction.kind)
  | .ok _ => none

/-- The cells of the resolved INSERT from a query, if the resolution is one. -/
def cellsOf : Except NodeRestriction (Resolved.Statement × ResolveState) → Option (List Resolved.SourceCell)
  | .ok (.insertSelect _ cells .., _) => some cells
  | .ok (.prepareError _, _) | .ok (.createView .., _) | .ok (.createTable .., _) | .ok (.createIndex .., _)
  | .ok (.createTrigger .., _) | .ok (.addColumn .., _) | .ok (.rewrite _, _) | .ok (.dropColumn .., _) | .ok (.drop .., _) | .ok (.begin, _) | .ok (.commit, _)
  | .ok (.rollback, _) | .ok (.insert .., _) | .ok (.upsert .., _) | .ok (.update .., _) | .ok (.delete .., _)
  | .ok (.query .., _) | .ok (.setting .., _) | .error _ => none

end Belay.Sqlite.Model.InsertQueryExamples
