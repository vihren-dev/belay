import Belay.Sqlite.Resolution.StatementCatalog
import Belay.Sqlite.Resolution.SourceList
import Belay.Sqlite.Resolution.QueryTerms

set_option doc.verso true

/-! Resolution of the clauses of a query (ADR 0012, slice 1, and amendment 2 for joins),
the statement's query or a subquery (ADR 0018, D1). The steps follow SQLite's resolver: the
tables of {lit}`FROM` ({lit}`Sources`), the result columns, {lit}`WHERE`, the {lit}`ON`
conditions, {lit}`GROUP BY`, {lit}`ORDER BY`, then {lit}`LIMIT` and {lit}`OFFSET`. The paths
of a restriction use the child positions of {lit}`Syntax.Statement.select` and of
{lit}`Syntax.Subquery`: 0 the columns, 1 the first table, 2 the joins, 3 the filter, 4 the
grouping terms, 5 the ordering terms, 6 the limit and 7 the offset. A
grouping term is a column name, also under one {lit}`COLLATE` ({name}`Belay.Sqlite.Syntax.Expr.collatedColumn`),
or a result column; each grouping and ordering term compares under its collation
(ADR 0014, slice 3). -/

namespace Belay.Sqlite

/-- One resolved result column with its names and the affinity of each: {lit}`*` gives every
column of every source of the query's own sources that is not merged ({name}`Scope.visible`)
under its defined name, a merged pair as its unqualified name ({name}`Scope.starOperand`),
{lit}`x.*` every column of source {lit}`x` ({name}`sourceStarColumns`); an aggregate is a whole
result column, without affinity; any other expression is a scalar with the affinity of its
operand. A name is the {lit}`AS` alias, else the defined name of a referenced column
({name}`definedName`), else the source text as written. -/
def resolveResultColumn (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (column : Nat) :
    Syntax.ResultColumn → Except ValueIssue (List (Resolved.Output × String × Option Affinity))
  | .star => if scope.inner.isEmpty then .error (.prepare .noTablesSpecified) else
      scope.visible.mapM fun (position, defined) =>
        (fun (operand : Operand) => (.scalar operand.1, defined.name.text, operand.2)) <$> scope.starOperand position defined
  | .sourceStar source => (sourceStarColumns scope source).map fun columns =>
      columns.map fun ((expression, affinity), name) => (.scalar expression, name, affinity)
  | .expression value alias text => do
    let named := fun (output : Resolved.Output) (defined : Option String) (affinity : Option Affinity) =>
      [(output, (alias.map (·.text)).getD (defined.getD text), affinity)]
    let outerAggregate := fun (operand : Resolved.Expr) =>
      if operand.readsUnder shapes shapes.outer then throw ((ValueIssue.restriction [] .outerAggregate).under [0, column, 0])
      else pure ()
    match value with
    | .callStar name =>
      if normalizeIdentifier name == "count" then .ok (named (.aggregate .countRows) none none)
      else throw ((starCallIssue name).under [0, column, 0])
    | .call name [] =>
      if normalizeIdentifier name == "count" then .ok (named (.aggregate .countRows) none none)
      else do
        let (resolved, affinity) ← (resolveOperand dqs scope shapes false value).mapError (·.under [0, column, 0])
        .ok (named (.scalar resolved) none affinity)
    | .call name [operand] => match aggregateNamed name with
      | some aggregate =>
        let (resolved, _) ← (resolveOperand dqs scope shapes true operand).mapError (·.under [0, column, 0, 1, 0])
        outerAggregate resolved
        if (aggregate resolved).writesJson && resolved.subtypeUndescribed then
          throw ((ValueIssue.restriction [] .jsonSubtype).under [0, column, 0, 1, 0])
        .ok (named (.aggregate ((aggregate resolved).withCollation (operand.collationIn scope))) none none)
      | none => do
        let (resolved, affinity) ← (resolveOperand dqs scope shapes false value).mapError (·.under [0, column, 0])
        .ok (named (.scalar resolved) none affinity)
    | .call name [first, second] => match pairAggregateNamed name with
      | some aggregate =>
        let (label, _) ← (resolveOperand dqs scope shapes true first).mapError (·.under [0, column, 0, 1, 0])
        let (operand, _) ← (resolveOperand dqs scope shapes true second).mapError (·.under [0, column, 0, 1, 1])
        outerAggregate (.coalesce label operand)
        if operand.subtypeUndescribed then throw ((ValueIssue.restriction [] .jsonSubtype).under [0, column, 0, 1, 1])
        .ok (named (.aggregate (aggregate label operand)) none none)
      | none => do
        let (resolved, affinity) ← (resolveOperand dqs scope shapes false value).mapError (·.under [0, column, 0])
        .ok (named (.scalar resolved) none affinity)
    | .call _ (_ :: _ :: _ :: _) | .null | .numeric _ | .string _ | .blob _ | .currentTime _
    | .identifier .. | .qualified .. | .negate _ | .positive _ | .compare .. | .and .. | .or .. | .not _
    | .isNull .. | .arithmetic .. | .cast .. | .collate .. | .exists _ | .inQuery .. | .subquery _ =>
      let (resolved, affinity) ← (resolveOperand dqs scope shapes false value).mapError (·.under [0, column, 0])
      .ok (named (.scalar resolved) (definedName scope value) affinity)

/-- The aliases of the result columns as written, one for each output: none for each column
of {lit}`*` and {lit}`x.*`. -/
def resultAliases (scope : Scope) (results : List Syntax.ResultColumn) : List (Option Identifier) :=
  results.flatMap fun
    | .star => scope.visible.map fun _ => none
    | .sourceStar name => ((scope.starColumns? name).map (·.map fun _ => none)).getD []
    | .expression _ alias _ => [alias]

/-- The explicit collation and the column collation of the first result column, as
{name}`inCollation` needs them for a subquery: those of its expression, or the collation of
the first column of {lit}`*` or {lit}`x.*`. -/
def firstCollations (scope : Scope) : List Syntax.ResultColumn → Option Collation × Option Collation
  | .expression value _ _ :: _ => (value.explicitCollation, value.columnCollation scope)
  | .star :: _ => (none, (scope.visible.head?.map (·.2.collation)))
  | .sourceStar name :: _ => (none, ((scope.starColumns? name).bind (·.head?)).map (·.2.collation))
  | [] => (none, none)

/-- Resolve the clauses of a query over its scope ({lit}`resolveSources`, enclosed by the
scopes of the queries around it), with the shapes of the subqueries that its expressions name
and the aliases of the queries around it, which a name in {lit}`WHERE` can name: the resolved
query and the affinity of its first result column. See the module documentation for the steps.
A scalar subquery is no grouping term, so it is a bare column of an aggregate query. -/
def resolveQueryBody (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (outerAliases : List Identifier)
    (pending : List PendingSource) (query : Syntax.Subquery) : Except ValueIssue (Resolved.Query × Option Affinity) := do
  let outputs := (← resolveAll (resolveResultColumn dqs scope shapes) query.columns).flatten
  let aliases := resultAliases scope query.columns
  let visibleAliases := aliases.filterMap id ++ outerAliases
  let condition ← match query.filter with
    | none => pure none
    | some term =>
      if namesAlias scope visibleAliases term then throw (aliasInExpression.under [3])
      else some <$> condition [3] (resolveOperand dqs scope shapes true term)
  let sources ← resolvePendingSources dqs scope pending
  let aggregate := !query.groupBy.isEmpty || outputs.any fun (output, _) => match output with
    | .aggregate _ => true
    | .scalar _ => false
  let collations := resultCollations scope query.columns
  let grouped := fun (column : Nat) => match outputs[column]? with
    | some (.scalar expression, _) => .ok (expression, collations.getD column .binary)
    | some (.aggregate _, _) | none => .error (.prepare .aggregateInGroupBy)
  let terms ← resolveAll (fun item term => match term with
    | .identifier name _ => match scope.resolveName name, aliasIndex aliases name with
      | .found _ reads, _ => .ok ((scope.nameOperand reads).1, term.collationIn scope)
      | .missing, some column => grouped column
      | .missing, none | .ambiguous, _ =>
        (resolveOperand dqs scope shapes true term).map (·.1, term.collationIn scope) |>.mapError (·.under [4, item])
    | .callStar name | .call name [] | .call name [_] =>
      .error (if aggregateCall term then .prepare .aggregateInGroupBy else (callIssue name).under [4, item])
    | .numeric _ | .negate _ => match namedResult aliases term with
      | some (.ok column) => grouped column
      | some (.error ()) => .error (.prepare (.groupByOutOfRange (item + 1) outputs.length))
      | none => .error (.restriction [4, item] .groupByTerm)
    | .qualified .. =>
      (resolveOperand dqs scope shapes true term).map (·.1, term.collationIn scope) |>.mapError (·.under [4, item])
    | .collate .. =>
      if term.collatedColumn scope then
        (resolveOperand dqs scope shapes true term).map (·.1, term.collationIn scope) |>.mapError (·.under [4, item])
      else .error (.restriction [4, item] .groupByTerm)
    | .call _ (_ :: _ :: _) | .null | .string _ | .blob _ | .currentTime _ | .positive _ | .compare ..
    | .and .. | .or .. | .not _ | .isNull .. | .arithmetic .. | .cast .. | .exists _ | .inQuery .. | .subquery _ =>
      .error (.restriction [4, item] .groupByTerm)) query.groupBy
  if aggregate && !outputs.all (groupedOutput (terms.map Prod.fst) ·.1) then
    throw (.restriction [0] .bareColumn)
  let order ← resolveAll (fun item (term : Syntax.OrderTerm) => match namedResult aliases term.expression with
    | some (.ok column) =>
      .ok { key := .output column, descending := term.descending, collation := collations.getD column .binary }
    | some (.error ()) => .error (.prepare (.orderByOutOfRange (item + 1) outputs.length))
    | none =>
      if aggregate then .error (.restriction [5, item] .aggregateOrderBy)
      else if namesAlias scope visibleAliases term.expression then
        .error (aliasInExpression.under [5, item, 0])
      else (resolveOperand dqs scope shapes false term.expression).map (fun (e, _) =>
          ({ key := .expression e, descending := term.descending, collation := term.expression.collationIn scope }
            : Resolved.SortTerm))
        |>.mapError (·.under [5, item, 0])) query.orderBy
  let limitValue ← windowValue [6] query.limit
  let offsetValue ← windowValue [7] query.offset
  if offsetValue.any (· < 0) then throw (.restriction [7] .negativeOffset)
  if windowSkipsFailure query.groupBy query.limit query.offset (outputs.map (·.1)) then
    throw (.restriction [6] .windowedGroupSum)
  return ({ sources, filter := condition, aggregate, groupBy := terms,
            columns := outputs.map (·.1), names := outputs.map (·.2.1), orderBy := order,
            offset := (offsetValue.getD 0).toNat,
            limit := limitValue.bind fun value => if value < 0 then none else some value.toNat,
            outer := shapes.outer }, (outputs.head?.bind (·.2.2)))

end Belay.Sqlite
