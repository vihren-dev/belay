import Belay.Sqlite.SampleHints
import Belay.Sqlite.SampleDatabases

set_option doc.verso true

/-! Candidate schemas from query clauses. Keeping this heuristic separate from
certification lets callers replace it with explicit schemas or arbitrary generators. -/

namespace Belay.Sqlite.Sampling

open Belay.Sqlite.Model

/-- Search hints for one or more SQL statements. Named sources suggest physical tables;
expressions suggest their columns and row values. Explicit schemas remain available when
SQL alone cannot identify a database, for example a view or a table's declared constraints. -/
structure SchemaHints where
  /-- Named table references, retaining aliases for qualified column hints. -/
  sources : List Syntax.TableReference := []
  /-- Columns and literals from the query clauses. -/
  expressions : Hints := {}

/-- Keep hints in their SQL traversal order. This order makes repeated seeded searches
reproducible and can be replaced by a caller's explicit candidate sequence. -/
def SchemaHints.append (first second : SchemaHints) : SchemaHints :=
  { sources := first.sources ++ second.sources
    expressions := first.expressions.append second.expressions }

/-- Collect a SELECT's clauses, including join conditions and USING columns. Derived sources
and table-valued functions contribute expressions, but do not invent a physical table with
the function or subquery's name. Indexed subqueries are collected separately. -/
def queryHints (columns : List Syntax.ResultColumn) (source : Option Syntax.TableReference)
    (joins : List Syntax.Join) (filter : Option Syntax.Expr) (groupBy : List Syntax.Expr)
    (orderBy : List Syntax.OrderTerm) (limit offset having : Option Syntax.Expr) : SchemaHints :=
  let references := source.toList ++ joins.map (·.source)
  let clauses := filter.toList ++ groupBy ++ orderBy.map (·.expression) ++ limit.toList ++
    offset.toList ++ having.toList ++ joins.flatMap (·.condition.toList) ++
    references.flatMap (fun reference => reference.arguments.getD [])
  let usingColumns := joins.flatMap fun join =>
    (join.usingColumns.getD []).map fun name => (none, name)
  { sources := references.filter fun reference => reference.query.isNone && reference.arguments.isNone
    expressions := ((resultHints columns).append (expressionListHints clauses)).append
      { columns := usingColumns } }

/-- Collect one indexed subquery through the same clause traversal as a top-level SELECT. -/
def subqueryHints (query : Syntax.Subquery) : SchemaHints :=
  queryHints query.columns query.source query.joins query.filter query.groupBy query.orderBy
    query.limit query.offset query.having

/-- Nullable, unconstrained schema candidates suggested by named sources and column reads.
Unqualified columns are offered on each named source; qualified columns match its table or
alias. A star-only table gets column {lit}`a`. These are finite guesses, never assumptions;
the original claim and any precondition must still be certified at a selected database. -/
def SchemaHints.schema (hints : SchemaHints) : Option Database :=
  let tableNames := hints.sources.foldl (fun names source =>
    if names.any (·.sameName source.table) then names else names ++ [source.table]) []
  let tables := tableNames.map fun table =>
    let references := hints.sources.filter (·.table.sameName table)
    let names := hints.expressions.columns.filterMap fun (qualifier, column) =>
      if qualifier.all (fun name => references.any fun reference =>
        reference.table.sameName name || reference.alias.any (·.sameName name)) then some column else none
    let names := names.foldl (fun names name =>
      if names.any (·.sameName name) then names else names ++ [name]) []
    (table.text, (if names.isEmpty then [Identifier.ofString "a"] else names).map Identifier.text)
  Sampling.schema tables

end Belay.Sqlite.Sampling
