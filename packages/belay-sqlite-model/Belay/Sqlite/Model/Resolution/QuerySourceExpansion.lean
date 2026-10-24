import Belay.Sqlite.Model.Resolution.CommonTableExpansion

set_option doc.verso true

/-! The statement boundary for per-use CTE and stored-view query expansion.
Ordinary table queries keep their syntax and indexed query identities. -/

namespace Belay.Sqlite.Model

/-- A statement's queries after per-use CTE and stored-view expansion. The syntax root retains
the statement's clauses; the mapping translates the direct query references of a write. -/
structure CommonTableExpansion where
  /-- The rewritten query clauses of a SELECT, or the empty root used for a write. -/
  query : Syntax.Subquery
  /-- The complete executable query list, original paths and explicit source names. -/
  copies : CommonTableCopies
  /-- Old and new indexes of the statement's ordinary direct subqueries. -/
  rootIndexes : List (Nat × Nat)

/-- Expand used WITH and view definitions for one statement. Unused definitions are not prepared;
duplicates and malformed parent links are checked before the used definitions are copied.
The caller's fast path keeps syntax without used views or WITH definitions unchanged. -/
def expandCommonTables (catalog : Catalog) (field : Nat) (query : Syntax.Subquery)
    (written : List Syntax.Subquery) : Except SourceIssue CommonTableExpansion := do
  checkCommonTableSyntax field written
  let ((query, rootIndexes), copies) ←
    (copyCommonTableQuery catalog field written (querySourceDepth catalog written) none none [] [] query [] none).run {}
  if copies.filled.length != copies.queries.size then throw (.value (.restriction [field] .subqueryHere))
  return { query, copies, rootIndexes }

/-- Keep ordinary query syntax unchanged, or expand its WITH definitions and used views.
The identity branch preserves the existing query indexes and needs no new copies. -/
def prepareQuerySources (catalog : Catalog) (field : Nat) (query : Syntax.Subquery)
    (written : List Syntax.Subquery) : Except SourceIssue CommonTableExpansion :=
  if querySourceCopiesNeeded catalog query written then expandCommonTables catalog field query written else
    .ok {
      query
      rootIndexes := (List.range written.length).map fun index => (index, index)
      copies := { queries := written.toArray, origins := (List.range written.length).toArray } }

end Belay.Sqlite.Model
