import Belay.Sqlite.Model.Resolution.CommonTableScope
import Belay.Sqlite.Model.Resolution.SourceExpansion

set_option doc.verso true

/-! Storage for per-use copies of CTE queries. Every copied query retains its original
syntax index for diagnostics, and an explicit CTE column list changes source metadata only. -/

namespace Belay.Sqlite.Model

/-- An empty query used while reserving indexes before their bodies are copied.
Resolution receives the list only after every reservation has been filled. -/
def commonTablePlaceholder : Syntax.Subquery :=
  { columns := [], source := none, joins := [], filter := none, groupBy := [],
    orderBy := [], limit := none, offset := none, parent := none }

/-- The copied queries of one statement and the data needed by source resolution.
Use the empty default before expanding the statement. -/
structure CommonTableCopies where
  /-- The new indexed query list, with parents reserved before children. -/
  queries : Array Syntax.Subquery := #[]
  /-- The original syntax index of each copied query, for restriction spans. -/
  origins : Array Nat := #[]
  /-- Filled reservations; an unfilled slot must never reach resolution. -/
  filled : List Nat := []
  /-- Explicit output names for the copied CTE uses that declare them. -/
  columnNames : List (Nat × List Identifier) := []
  /-- Recursive CTE copies and their recursive arms, retained only for preparation. -/
  recursive : List (Nat × List Nat) := []

/-- The expansion computation: pure state updates with the existing source errors. -/
abbrev CommonTableCopyM := StateT CommonTableCopies (Except SourceIssue)

/-- Reserve a query index before copying its descendants and retain its written origin. -/
def reserveCommonTableQuery (origin : Nat) : CommonTableCopyM Nat := do
  let state ← get
  let index := state.queries.size
  set { state with
    queries := state.queries.push commonTablePlaceholder
    origins := state.origins.push origin }
  return index

/-- Fill one reserved query with its copied body. -/
def fillCommonTableQuery (index : Nat) (query : Syntax.Subquery) : CommonTableCopyM Unit :=
  modify fun state => { state with
    queries := state.queries.set! index query
    filled := index :: state.filled }

/-- Map an expanded query's restriction path back to the written definition.
Paths outside the indexed query list are unchanged. -/
def CommonTableCopies.originalPath (copies : CommonTableCopies) (field : Nat) : List Nat → List Nat
  | first :: index :: rest =>
    if first == field then
      first :: copies.origins[index]?.getD index :: rest
    else first :: index :: rest
  | path => path

/-- Restore written query indexes in source restrictions. SQL errors retain their names. -/
def CommonTableCopies.originalIssue (copies : CommonTableCopies) (field : Nat) : SourceIssue → SourceIssue
  | .value (.restriction path kind) => .value (.restriction (copies.originalPath field path) kind)
  | .value (.prepare error) => .value (.prepare error)
  | .noSuchTable name => .noSuchTable name

/-- Inspect the names produced by a completed query copy, using the ordinary source
expander and any already completed explicit CTE column lists. -/
def commonTableOutput (catalog : Catalog) (field index : Nat) :
    CommonTableCopyM (Scope × List Syntax.ResultColumn × List String) := do
  let copies ← get
  liftM ((expandQuerySources catalog field copies.queries.toList copies.columnNames
    (copies.queries.size + 1) index).mapError (copies.originalIssue field))

/-- Check an explicit CTE column count after its body expands, and retain its names.
An absent column list keeps the query's ordinary derived-column names. -/
def nameCommonTableCopy (catalog : Catalog) (field index : Nat)
    (definition : Syntax.CommonTable) : CommonTableCopyM Unit := do
  let (_, _, names) ← commonTableOutput catalog field index
  if let some columns := definition.columns then
    if names.length != columns.length then
      throw (.value (.prepare (.commonTable (.columns definition.name names.length columns.length))))
    modify fun state => { state with columnNames := (index, columns) :: state.columnNames }

/-- Refuse a prepared recursive definition after ordinary name and column-count checks.
A recursive aggregate is SQLite's preparation error. Otherwise no copied recursive source
can reach evaluation: its source-name placeholders exist only for these checks. -/
def CommonTableCopies.recursionIssue (copies : CommonTableCopies) (field : Nat)
    (queries : List Resolved.Query) : Option ValueIssue := do
  let (index, arms) ← copies.recursive.head?
  if arms.any (fun arm => (queries[arm]?).any (·.aggregate)) then
    return .prepare (.commonTable (.recursiveAggregate))
  return .restriction [field, index] .recursiveCommonTable

/-- Rewrite clause indexes using a parent query's copies. A reference outside that
parent's ordinary children is malformed syntax and remains a model restriction. -/
def reindexCommonTableQuery (field : Nat) (owner : Option Nat) (mapping : List (Nat × Nat))
    (query : Syntax.Subquery) : Except SourceIssue Syntax.Subquery :=
  ({ query with parent := none, commonTable := none }).reindexM fun index =>
    match mapping.lookup index with
    | some copied => pure copied
    | none => .error (.value (.restriction ([field] ++ owner.toList) .subqueryHere))

end Belay.Sqlite.Model
