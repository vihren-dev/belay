import Belay.Sqlite.Model.Resolution.ResultColumnTraced
import Belay.Sqlite.Model.Resolution.ScopeOwn

set_option doc.verso true

/-! Resolution of the clauses of a query with the name trace (ADR 0012, slice 1, and amendment 2
for joins), the statement's query or a subquery (ADR 0018, D1). The steps follow SQLite's resolver:
the tables of {lit}`FROM` ({lit}`Sources`), the result columns, {lit}`WHERE`, the {lit}`ON`
conditions, {lit}`GROUP BY`, {lit}`ORDER BY`, then {lit}`LIMIT` and {lit}`OFFSET`. The paths
of a restriction and of an occurrence use the child positions of {lit}`Syntax.Statement.select` and of
{lit}`Syntax.Subquery`: 0 the columns, 1 the first table, 2 the joins, 3 the filter, 4 the
grouping terms, 5 the ordering terms, 6 the limit, 7 the offset and 9 {lit}`HAVING`. A
grouping term is a column name, also under one {lit}`COLLATE` ({name}`Belay.Sqlite.Model.Syntax.Expr.collatedColumn`),
or a result column; each grouping and ordering term compares under its collation
(ADR 0014, slice 3). -/

namespace Belay.Sqlite.Model

/-- The path of the first aggregate call that is the same as {lit}`call` in the result columns,
{lit}`HAVING` or {lit}`ORDER BY` of a query, in that order; the empty path if there is none. A
call that is a whole result column is not listed, so it is not found there. -/
def Syntax.Subquery.callLocation (query : Syntax.Subquery) (call : Syntax.Expr) : List Nat :=
  let inColumns := query.columns.zipIdx.findSome? fun (column, index) => match column with
    | .expression value _ _ => if aggregateCall value then none else (value.callPath? call).map ([0, index, 0] ++ ·)
    | .star | .sourceStar _ => none
  (inColumns <|> (query.having.bind (·.callPath? call)).map ([9] ++ ·)
    <|> query.orderBy.zipIdx.findSome? fun (term, index) => (term.expression.callPath? call).map ([5, index, 0] ++ ·)).getD []

/-- The operand of a term of {lit}`ORDER BY`: a name that no column has lists the aliases of the
result columns among its candidates, because the term could have named one. -/
def orderOperandTraced (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (misuse : Bool)
    (aliases : List (Option Identifier)) : Syntax.Expr → Traced ValueIssue Operand
  | .identifier name quote => identifierTraced dqs scope name quote (aliasCandidates aliases)
  | term@(.null) | term@(.numeric _) | term@(.string _) | term@(.blob _) | term@(.parameter _)
  | term@(.currentTime _) | term@(.qualified ..) | term@(.negate _) | term@(.positive _)
  | term@(.compare ..) | term@(.and ..) | term@(.or ..) | term@(.not _) | term@(.isNull ..)
  | term@(.callStar _) | term@(.call ..) | term@(.arithmetic ..) | term@(.cast ..) | term@(.collate ..)
  | term@(.exists _) | term@(.inQuery ..) | term@(.subquery _) | term@(.inList ..) | term@(.between ..)
  | term@(.caseOf ..) | term@(.concatenate ..) | term@(.raise ..) =>
    resolveOperandTraced dqs scope shapes misuse term

/-- The position of the first join whose {lit}`ON` condition names one of the result column aliases
{lit}`visibleAliases`, if there is one. -/
def aliasJoinItem? (scope : Scope) (visibleAliases : List Identifier) (joins : List Syntax.Join) : Option Nat :=
  (joins.zipIdx.find? fun (join, _) => join.condition.any (namesAlias scope visibleAliases)).map (·.2)

/-- Resolve {lit}`ORDER BY` term {lit}`item` of a query whose result columns are {lit}`outputs`, with
the aliases {lit}`aliases` of its result columns, the aliases {lit}`visibleAliases` that its clauses
may name, the collations {lit}`collations` of its result columns, its grouping terms {lit}`grouped`, and
the flags of an aggregate query and of {lit}`SELECT DISTINCT`. A term that names a result column by
number or alias sorts by that column, and an alias is recorded as the result column that it names.
Any other term is an expression over the scope: in an aggregate query it must read only grouping
terms and aggregates, and under {lit}`DISTINCT` it must be a result column. -/
def resolveOrderTermTraced (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes)
    (aliases : List (Option Identifier)) (visibleAliases : List Identifier)
    (outputs : List (Resolved.Output × String × Option Affinity)) (collations : List Collation)
    (grouped : List Resolved.Expr) (aggregate distinct : Bool) (item : Nat) (term : Syntax.OrderTerm) :
    Traced ValueIssue Resolved.SortTerm :=
  match namedResult aliases term.expression with
  | some (.ok column) => do
    if let .identifier name quote := term.expression then
      Traced.record { aliasUseOccurrence name quote column with path := [5, item, 0] }
    pure { key := .output column, descending := term.descending, collation := collations.getD column .binary }
  | some (.error ()) => throw (.prepare (.orderByOutOfRange (item + 1) outputs.length))
  | none =>
    if namesAlias scope visibleAliases term.expression then throw (aliasInExpression.under [5, item, 0])
    else do
      let (e, _) ← (orderOperandTraced dqs scope shapes (!aggregate) aliases term.expression).under [5, item, 0]
      if aggregate && !e.grouped grouped then throw (.restriction [5, item] .aggregateOrderBy)
      else if distinct && !outputs.any (·.1 == .scalar e) then throw (.restriction [5, item] .distinctOrderBy)
      else pure { key := .expression e, descending := term.descending, collation := term.expression.collationIn scope }

/-- Resolve the clauses of a query over its scope ({lit}`resolveSources`, enclosed by the
scopes of the queries around it), with the shapes of the subqueries that its expressions name
and the aliases of the queries around it, which a name in {lit}`WHERE` can name: the resolved
query and the affinity of its first result column, with the occurrences that the resolution
decided. See the module documentation for the steps.
A scalar subquery is no grouping term, so it is a bare column of an aggregate query. The
query is an aggregate query when it has {lit}`GROUP BY` or an aggregate in a result column, and
then the aggregate calls of its result columns, {lit}`HAVING` and {lit}`ORDER BY` are its
aggregates (ADR 0018, D3); {lit}`HAVING` in another query is SQLite's {lit}`HAVING clause on a
non-aggregate query`, and an aggregate in its {lit}`ORDER BY` SQLite's misuse. {lit}`HAVING` and
{lit}`ORDER BY` expressions
must read only grouping terms and aggregates ({name}`Resolved.Expr.grouped`). A fallible call
over an aggregate is {name}`RestrictionKind.aggregateInExpression`, because the model's fault scan
does not read aggregate values; an {lit}`ORDER BY` expression of {lit}`SELECT DISTINCT` that is no
result column is {name}`RestrictionKind.distinctOrderBy`. The names inside the aggregate calls
are recorded where the expression that holds the call resolves; the pass that lists the calls
shows them only when it is the one that fails. -/
def resolveQueryBodyTraced (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (outerAliases : List Identifier)
    (pending : List PendingSource) (query : Syntax.Subquery) :
    Traced ValueIssue (Resolved.Query × Option Affinity) := do
  let aggregate := !query.groupBy.isEmpty || query.columns.any fun
    | .expression value _ _ => !value.aggregateCalls.isEmpty
    | .star | .sourceStar _ => false
  let calls := (query.columns.flatMap (fun
      | .expression value _ _ => if aggregateCall value then [] else value.aggregateCalls
      | .star | .sourceStar _ => []) ++
    (if aggregate then query.having.toList.flatMap Syntax.Expr.aggregateCalls ++
      query.orderBy.flatMap (·.expression.aggregateCalls) else [])) |> Syntax.Expr.distinctList
  let shapes := { shapes with aggregates := calls }
  let aggregates ← (resolveAllTraced (fun _ call =>
    (resolveAggregateCallTraced dqs scope shapes call).underTrace (query.callLocation call)) calls).keepOnFailure
  let outputs := (← resolveAllTraced (resolveResultColumnTraced dqs scope shapes) query.columns).flatten
  -- SQLite resolves the result columns before it checks HAVING.
  if query.having.isSome && !aggregate then throw (.prepare .havingNonAggregate)
  let aliases := resultAliases scope query.columns
  let visibleAliases := aliases.filterMap id ++ outerAliases
  let condition ← match query.filter with
    | none => pure none
    | some term =>
      if namesAlias scope visibleAliases term then throw (aliasInExpression.under [3])
      else do pure (some (← Traced.condition [3] (resolveOperandTraced dqs scope shapes true term)))
  -- SQLite resolves a result column alias in an ON condition as it does in WHERE.
  if h : (aliasJoinItem? scope visibleAliases query.joins).isSome then
    throw (aliasInExpression.under [2, (aliasJoinItem? scope visibleAliases query.joins).get h, 2])
  let sources ← resolvePendingSourcesTraced dqs scope pending
  let collations := resultCollations scope query.columns
  let terms ← resolveAllTraced (resolveGroupTermTraced dqs scope.ownSources shapes aliases outputs collations) query.groupBy
  if aggregate && !outputs.all (groupedOutput (terms.map Prod.fst) ·.1) then
    throw (.restriction [0] .bareColumn)
  let having ← match query.having with
    | none => pure none
    | some term =>
      if namesAlias scope visibleAliases term then throw (aliasInExpression.under [9])
      else
        let resolved ← Traced.condition [9] (resolveOperandTraced dqs scope shapes false term)
        if resolved.grouped (terms.map Prod.fst) then pure (some resolved) else throw (.restriction [9] .bareColumn)
  let order ← resolveAllTraced (resolveOrderTermTraced dqs scope.ownSources shapes aliases visibleAliases outputs collations
    (terms.map Prod.fst) aggregate query.distinct) query.orderBy
  let feedsCall := fun (expression : Resolved.Expr) =>
    expression.any fun node => node.isFallibleCall && node.any (· matches .aggregateValue _)
  let scalars := outputs.filterMap fun (output, _) => match output with
    | .scalar expression => some expression
    | .aggregate _ => none
  let sorted := order.filterMap fun term => match term.key with
    | .expression expression => some expression
    | .output _ => none
  if (scalars ++ having.toList ++ sorted).any feedsCall then
    throw (.restriction [] .aggregateInExpression)
  let (limitValue, limitParameter) ← windowValue [6] query.limit
  let (offsetValue, offsetParameter) ← windowValue [7] query.offset
  if offsetValue.any (· < 0) then throw (.restriction [7] .negativeOffset)
  if windowSkipsFailure query.groupBy query.limit query.offset (outputs.map (·.1) ++ aggregates.map .aggregate) then
    throw (.restriction [6] .windowedGroupSum)
  return ({ sources, filter := condition, aggregate, groupBy := terms,
            columns := outputs.map (·.1), names := outputs.map (·.2.1), orderBy := order,
            offset := (offsetValue.getD 0).toNat,
            limit := limitValue.bind fun value => if value < 0 then none else some value.toNat,
            limitParameter, offsetParameter,
            outer := shapes.outer, aggregates, having,
            distinct := if query.distinct then some collations else none }, (outputs.head?.bind (·.2.2)))

end Belay.Sqlite.Model
