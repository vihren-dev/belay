import Belay.Sqlite.Resolution.StatementCatalog
import Belay.Sqlite.Resolution.SourceList
import Belay.Sqlite.Resolution.QueryTerms

set_option doc.verso true

/-! Resolution of a {lit}`SELECT` (ADR 0012, slice 1, and amendment 2 for joins). The
steps follow SQLite's resolver: the tables of {lit}`FROM` ({lit}`Sources`), the result
columns, {lit}`WHERE`, the {lit}`ON` conditions, {lit}`GROUP BY`, {lit}`ORDER BY`, then
{lit}`LIMIT` and {lit}`OFFSET`. The paths of a restriction use the child positions of
{lit}`Syntax.Statement.select`: 0 the columns, 1 the first table, 2 the joins, 3 the
filter, 4 the grouping terms, 5 the ordering terms, 6 the limit and 7 the offset. A
grouping term is a column name, also under one {lit}`COLLATE` ({name}`Belay.Sqlite.Syntax.Expr.collatedColumn`),
or a result column; each grouping and ordering term compares under its collation
(ADR 0014, slice 3). -/

namespace Belay.Sqlite

/-- One resolved result column with its names: {lit}`*` gives every column of every
source that is not merged ({name}`Scope.visible`) under its defined name, a merged pair as
its unqualified name ({name}`Scope.starOperand`), {lit}`x.*` every column of source
{lit}`x` ({name}`sourceStarColumns`); an aggregate is a whole result column; any other expression
is a scalar. A name is the {lit}`AS` alias, else the defined name of a referenced column
({name}`definedName`), else the source text as written. -/
def resolveResultColumn (dqs : Bool) (scope : Scope) (column : Nat) :
    Syntax.ResultColumn → Except ValueIssue (List (Resolved.Output × String))
  | .star => if scope.isEmpty then .error (.prepare .noTablesSpecified) else
      scope.visible.mapM fun (position, defined) => (.scalar ·.1, defined.name.text) <$> scope.starOperand position defined
  | .sourceStar source => (sourceStarColumns scope source).map fun columns =>
      columns.map fun (expression, name) => (.scalar expression, name)
  | .expression value alias text => do
    let named := fun (output : Resolved.Output) (defined : Option String) => [(output, (alias.map (·.text)).getD (defined.getD text))]
    match value with
    | .callStar name =>
      if normalizeIdentifier name == "count" then .ok (named (.aggregate .countRows) none)
      else throw ((starCallIssue name).under [0, column, 0])
    | .call name [] =>
      if normalizeIdentifier name == "count" then .ok (named (.aggregate .countRows) none)
      else do
        let (resolved, _) ← (resolveOperand dqs scope false value).mapError (·.under [0, column, 0])
        .ok (named (.scalar resolved) none)
    | .call name [operand] => match aggregateNamed name with
      | some aggregate =>
        let (resolved, _) ← (resolveOperand dqs scope true operand).mapError (·.under [0, column, 0, 1, 0])
        .ok (named (.aggregate ((aggregate resolved).withCollation (operand.collationIn scope))) none)
      | none => do
        let (resolved, _) ← (resolveOperand dqs scope false value).mapError (·.under [0, column, 0])
        .ok (named (.scalar resolved) none)
    | .call _ (_ :: _ :: _) | .null | .numeric _ | .string _ | .blob _ | .currentTime _
    | .identifier .. | .qualified .. | .negate _ | .positive _ | .compare .. | .and .. | .or .. | .not _
    | .isNull .. | .arithmetic .. | .cast .. | .collate .. =>
      let (resolved, _) ← (resolveOperand dqs scope false value).mapError (·.under [0, column, 0])
      .ok (named (.scalar resolved) (definedName scope value))

/-- Resolve a {lit}`SELECT`; see the module documentation for the steps. -/
def resolveSelect (context : ResolveContext) (catalog : Catalog) (index : Nat)
    (results : List Syntax.ResultColumn) (source : Option Syntax.TableReference) (joins : List Syntax.Join)
    (filter : Option Syntax.Expr) (groupBy : List Syntax.Expr) (orderBy : List Syntax.OrderTerm)
    (limit offset : Option Syntax.Expr) : StatementResolution :=
  let dqs := context.profile.dqsDml
  match resolveSources catalog source joins with
  | .error (.noSuchTable name) => prepareError catalog (.noSuchTable name)
  | .error (.value issue) => issueResolution catalog index [] issue
  | .ok (pending, scope) =>
  let resolved : Except ValueIssue Resolved.Query := do
    let outputs := (← resolveAll (resolveResultColumn dqs scope) results).flatten
    let aliases := results.flatMap fun
      | .star => scope.visible.map fun _ => none
      | .sourceStar name => ((scope.starColumns? name).map (·.map fun _ => none)).getD []
      | .expression _ alias _ => [alias]
    let condition ← match filter with
      | none => pure none
      | some term =>
        if namesAlias scope (aliases.filterMap id) term then throw (aliasInExpression.under [3])
        else some <$> condition [3] (resolveOperand dqs scope true term)
    let sources ← resolvePendingSources dqs scope pending
    let aggregate := !groupBy.isEmpty || outputs.any fun (output, _) => match output with
      | .aggregate _ => true
      | .scalar _ => false
    let collations := resultCollations scope results
    let grouped := fun (column : Nat) => match outputs[column]? with
      | some (.scalar expression, _) => .ok (expression, collations.getD column .binary)
      | some (.aggregate _, _) | none => .error (.prepare .aggregateInGroupBy)
    let terms ← resolveAll (fun item term => match term with
      | .identifier name _ => match scope.resolveName name, aliasIndex aliases name with
        | .found _ reads, _ => .ok ((scope.nameOperand reads).1, term.collationIn scope)
        | .missing, some column => grouped column
        | .missing, none | .ambiguous, _ =>
          (resolveOperand dqs scope true term).map (·.1, term.collationIn scope) |>.mapError (·.under [4, item])
      | .callStar name | .call name [] | .call name [_] =>
        .error (if aggregateCall term then .prepare .aggregateInGroupBy else (callIssue name).under [4, item])
      | .numeric _ | .negate _ => match namedResult aliases term with
        | some (.ok column) => grouped column
        | some (.error ()) => .error (.prepare (.groupByOutOfRange (item + 1) outputs.length))
        | none => .error (.restriction [4, item] .groupByTerm)
      | .qualified .. =>
        (resolveOperand dqs scope true term).map (·.1, term.collationIn scope) |>.mapError (·.under [4, item])
      | .collate .. =>
        if term.collatedColumn scope then
          (resolveOperand dqs scope true term).map (·.1, term.collationIn scope) |>.mapError (·.under [4, item])
        else .error (.restriction [4, item] .groupByTerm)
      | .call _ (_ :: _ :: _) | .null | .string _ | .blob _ | .currentTime _ | .positive _ | .compare ..
      | .and .. | .or .. | .not _ | .isNull .. | .arithmetic .. | .cast .. =>
        .error (.restriction [4, item] .groupByTerm)) groupBy
    if aggregate && !outputs.all (groupedOutput (terms.map Prod.fst) ·.1) then
      throw (.restriction [0] .bareColumn)
    let order ← resolveAll (fun item (term : Syntax.OrderTerm) => match namedResult aliases term.expression with
      | some (.ok column) =>
        .ok { key := .output column, descending := term.descending, collation := collations.getD column .binary }
      | some (.error ()) => .error (.prepare (.orderByOutOfRange (item + 1) outputs.length))
      | none =>
        if aggregate then .error (.restriction [5, item] .aggregateOrderBy)
        else if namesAlias scope (aliases.filterMap id) term.expression then
          .error (aliasInExpression.under [5, item, 0])
        else (resolveOperand dqs scope false term.expression).map (fun (e, _) =>
            ({ key := .expression e, descending := term.descending, collation := term.expression.collationIn scope }
              : Resolved.SortTerm))
          |>.mapError (·.under [5, item, 0])) orderBy
    let limitValue ← windowValue [6] limit
    let offsetValue ← windowValue [7] offset
    if offsetValue.any (· < 0) then throw (.restriction [7] .negativeOffset)
    if windowSkipsFailure groupBy limit offset (outputs.map (·.1)) then
      throw (.restriction [6] .windowedGroupSum)
    return { sources, filter := condition, aggregate, groupBy := terms,
             columns := outputs.map (·.1), names := outputs.map (·.2), orderBy := order,
             offset := (offsetValue.getD 0).toNat,
             limit := limitValue.bind fun value => if value < 0 then none else some value.toNat }
  match resolved with
  | .ok query => .ok (.query query, catalog)
  | .error issue => issueResolution catalog index [] issue

/-- For every successful resolution of a {lit}`SELECT`, the catalog is unchanged and the
resolved statement applied to the input catalog gives the input catalog again
({lit}`Resolved.Statement.applyCatalog`); the statement is not transaction control.
Proof sketch: every branch of the resolver returns the input catalog and a query or a
prepare error. -/
theorem resolveSelect_same (context : ResolveContext) (catalog after : Catalog) (index : Nat)
    (results : List Syntax.ResultColumn) (source : Option Syntax.TableReference) (joins : List Syntax.Join)
    (filter : Option Syntax.Expr) (groupBy : List Syntax.Expr) (orderBy : List Syntax.OrderTerm)
    (limit offset : Option Syntax.Expr) (statement : Resolved.Statement)
    (ok : resolveSelect context catalog index results source joins filter groupBy orderBy limit offset =
      .ok (statement, after)) :
    after = catalog ∧ statement.applyCatalog catalog = catalog ∧ statement.isControl = false := by
  unfold resolveSelect at ok
  simp only [prepareError, issueResolution] at ok
  repeat' split at ok
  all_goals first | (cases ok; exact ⟨rfl, rfl, rfl⟩) | (cases ok)

end Belay.Sqlite
